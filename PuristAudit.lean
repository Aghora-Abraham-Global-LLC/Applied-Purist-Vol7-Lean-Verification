import Lean

open Lean

def isPuristDecl (n : Name) : Bool :=
  match n.components with
  | `PuristSiliconCore :: _ =>
    let s := n.toString
    !(n.isInternalDetail) &&
    !(s.endsWith ".mk.inj") &&
    !(s.endsWith ".mk.injEq") &&
    !(s.endsWith ".mk.sizeOf_spec")
  | _ => false

def main (args : List String) : IO UInt32 := do
  let outPath := args.headD "./proof-manifest.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `PuristSiliconCore }] {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<purist-audit>", fileMap := default }
  let st : Core.State := { env := env }

  let mut entries : Array (String × Json) := #[]
  let mut sorryCount : Nat := 0
  let mut kernelOnlyCount : Nat := 0
  let mut satCertCount : Nat := 0
  let mut thmCount : Nat := 0

  for (name, cinfo) in env.constants.toList do
    if isPuristDecl name then
      if let ConstantInfo.thmInfo _ := cinfo then
        thmCount := thmCount + 1
        let (axioms, _) ← Core.CoreM.toIO (Lean.collectAxioms name) ctx st
        let axiomStrs : Array String := axioms.map (·.toString)
        let hasSorry : Bool := axiomStrs.contains "sorryAx"
        let usesSatCert : Bool :=
          axiomStrs.contains "Lean.ofReduceBool" || axiomStrs.contains "Lean.trustCompiler"
        if hasSorry then
          sorryCount := sorryCount + 1
        else if usesSatCert then
          satCertCount := satCertCount + 1
        else
          kernelOnlyCount := kernelOnlyCount + 1
        let tier :=
          if hasSorry then "SORRY_FAIL"
          else if usesSatCert then "SAT_LRAT_CERT"
          else "KERNEL_ONLY"
        let recJson := Json.mkObj [
          ("name", Json.str name.toString),
          ("tier", Json.str tier),
          ("axioms", Json.arr (axiomStrs.map Json.str)),
          ("sorryFree", Json.bool (!hasSorry))
        ]
        entries := entries.push (name.toString, recJson)

  let sortedRecords := (entries.qsort (fun a b => a.1 < b.1)).map (·.2)

  let manifest := Json.mkObj [
    ("directorate", Json.str "Purist Lean Proof Foundry"),
    ("documentCode", Json.str "TMD-12-PURIST-APPLIED-VOL-VII-STRONG-FIELD-CHRONOMETRY-2026"),
    ("preprintDoi", Json.str "10.5281/zenodo.24417929"),
    ("verifiedVolumes", Json.arr #[
      Json.str "APPLIED_VOL_6 (10.5281/zenodo.24392562)",
      Json.str "APPLIED_VOL_7 (10.5281/zenodo.24417929)"
    ]),
    ("leanVersion", Json.str Lean.versionString),
    ("module", Json.str "PuristSiliconCore"),
    ("theoremCount", Json.num thmCount),
    ("kernelOnlyCount", Json.num kernelOnlyCount),
    ("satCertCount", Json.num satCertCount),
    ("sorryCount", Json.num sorryCount),
    ("status", Json.str (if sorryCount == 0 && thmCount > 0 then "GREEN" else "FAILED_SORRY")),
    ("theorems", Json.arr sortedRecords)
  ]

  IO.FS.writeFile outPath (manifest.pretty ++ "\n")
  IO.println s!"[PuristAudit] Theorems: {thmCount} | KernelOnly: {kernelOnlyCount} | SatCert: {satCertCount} | Sorry: {sorryCount} | Wrote: {outPath}"
  return if sorryCount == 0 && thmCount > 0 then 0 else 1
