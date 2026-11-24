import PuristSiliconCore.Anchor
import PuristSiliconCore.SolinasFields
import PuristSiliconCore.D106AndBitwise

namespace PuristSiliconCore

/-- Canonical Listing 7.1 64-byte SolinasIvcState64 WGSL ABI (4 x vec4<u32>). -/
structure SolinasIvcState64 where
  u0Lo : BitVec 32
  u0Hi : BitVec 32
  u1Lo : BitVec 32
  u1Hi : BitVec 32
  dciChLo : BitVec 32
  dciChHi : BitVec 32
  bitlenLo : BitVec 32
  ccsdsFlags : BitVec 32
  ivcStep : BitVec 32
  pqHornerLo : BitVec 32
  pqHornerHi : BitVec 32
  mldsaFlags : BitVec 32
  tmdW0 : BitVec 32
  tmdW1 : BitVec 32
  morton30RoTag : BitVec 32
  statusZeroize : BitVec 32

structure TelemetryIngressPacket64 where
  posMortonW : BitVec 32
  wireTailMetaY : BitVec 32

def readMorton30BV (raw : BitVec 32) : BitVec 32 :=
  raw &&& 0x3fffffff#32

theorem readMorton30BV_lt (raw : BitVec 32) : (readMorton30BV raw).toNat < 2^30 := by
  unfold readMorton30BV
  rw [BitVec.toNat_and]
  have hle : raw.toNat &&& (0x3fffffff#32).toNat ≤ (0x3fffffff#32).toNat := Nat.and_le_right
  have hlt : (0x3fffffff#32).toNat < 2^30 := by decide
  omega

theorem readMorton30BV_matches_u32 (raw : BitVec 32) :
    (readMorton30FtzSafe ⟨raw⟩).toBitVec = readMorton30BV raw := rfl

def stepSolinasIvc64 (st : SolinasIvcState64) (ing : TelemetryIngressPacket64)
    (domainTag zeroizeOn : BitVec 32) : SolinasIvcState64 :=
  let m30Ro : BitVec 32 :=
    readMorton30BV ing.posMortonW |||
    readMorton30BV ing.wireTailMetaY |||
    (st.morton30RoTag &&& 0x3fffffff#32)
  let stepMask : Nat := (domainTag ^^^ m30Ro).toNat
  let cur64 : Nat := st.u0Lo.toNat + 2^32 * st.u0Hi.toNat
  let next64 : Nat := addModP64Ct cur64 stepMask
  let canonLo : BitVec 32 := BitVec.ofNat 32 (next64 % 2^32)
  let canonHi : BitVec 32 := BitVec.ofNat 32 (next64 / 2^32)
  let zmask : BitVec 32 := if zeroizeOn == 1#32 then 0#32 else BitVec.allOnes 32
  {
    u0Lo := canonLo &&& zmask
    u0Hi := canonHi &&& zmask
    u1Lo := st.u1Lo &&& zmask
    u1Hi := st.u1Hi &&& zmask
    dciChLo := st.dciChLo &&& zmask
    dciChHi := st.dciChHi &&& zmask
    bitlenLo := st.bitlenLo &&& zmask
    ccsdsFlags := st.ccsdsFlags &&& zmask
    ivcStep := st.ivcStep &&& zmask
    pqHornerLo := st.pqHornerLo &&& zmask
    pqHornerHi := st.pqHornerHi &&& zmask
    mldsaFlags := st.mldsaFlags &&& zmask
    tmdW0 := (st.tmdW0 ^^^ canonLo) &&& zmask
    tmdW1 := (st.tmdW1 ^^^ canonHi) &&& zmask
    morton30RoTag := m30Ro
    statusZeroize := if zeroizeOn == 1#32 then 0#32 else 1#32
  }

/-- THM-DILATON-APP6-03 & HW-APP6-01: NIST SP 800-88 wipe clears all 14 secret lanes to 0 while keeping read-only Morton-30 immutable. -/
theorem solinasIvc64_sp800_88_wipe_total (st : SolinasIvcState64) (ing : TelemetryIngressPacket64)
    (domainTag : BitVec 32) :
    let out := stepSolinasIvc64 st ing domainTag 1#32
    out.u0Lo = 0#32 ∧ out.u0Hi = 0#32 ∧ out.u1Lo = 0#32 ∧ out.u1Hi = 0#32 ∧
    out.dciChLo = 0#32 ∧ out.dciChHi = 0#32 ∧ out.bitlenLo = 0#32 ∧ out.ccsdsFlags = 0#32 ∧
    out.ivcStep = 0#32 ∧ out.pqHornerLo = 0#32 ∧ out.pqHornerHi = 0#32 ∧ out.mldsaFlags = 0#32 ∧
    out.tmdW0 = 0#32 ∧ out.tmdW1 = 0#32 ∧ out.statusZeroize = 0#32 ∧
    out.morton30RoTag.toNat < 2^30 := by
  intro out
  have hz1 : ((1#32 : BitVec 32) == 1#32) = true := rfl
  have hm : out.morton30RoTag.toNat < 2^30 := by
    change (readMorton30BV ing.posMortonW ||| readMorton30BV ing.wireTailMetaY |||
      (st.morton30RoTag &&& 0x3fffffff#32)).toNat < 2^30
    have ha := readMorton30BV_lt ing.posMortonW
    have hb := readMorton30BV_lt ing.wireTailMetaY
    have hc : (st.morton30RoTag &&& 0x3fffffff#32).toNat < 2^30 := by
      rw [BitVec.toNat_and]
      have hle : st.morton30RoTag.toNat &&& (0x3fffffff#32).toNat ≤ (0x3fffffff#32).toNat := Nat.and_le_right
      have hlt : (0x3fffffff#32).toNat < 2^30 := by decide
      omega
    rw [BitVec.toNat_or, BitVec.toNat_or]
    have h1 := Nat.or_lt_two_pow ha hb
    exact Nat.or_lt_two_pow h1 hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩ <;>
    simp [out, stepSolinasIvc64]

/-- HW-APP6-01: Non-wiped step produces canonical < p64 primary limb and statusZeroize = 1. -/
theorem solinasIvc64_active_step_canonical (st : SolinasIvcState64) (ing : TelemetryIngressPacket64)
    (domainTag : BitVec 32) :
    let out := stepSolinasIvc64 st ing domainTag 0#32
    out.u0Lo.toNat + 2^32 * out.u0Hi.toNat < p64 ∧ out.statusZeroize = 1#32 := by
  intro out
  have hz0 : ((0#32 : BitVec 32) == 1#32) = false := rfl
  have hcur : st.u0Lo.toNat + 2^32 * st.u0Hi.toNat < 2^64 := by
    have h0 := st.u0Lo.isLt
    have h1 := st.u0Hi.isLt
    omega
  let m30 := readMorton30BV ing.posMortonW ||| readMorton30BV ing.wireTailMetaY |||
    (st.morton30RoTag &&& 0x3fffffff#32)
  have hmask : (domainTag ^^^ m30).toNat < 2^64 := by
    have h := (domainTag ^^^ m30).isLt
    omega
  let next64 := addModP64Ct (st.u0Lo.toNat + 2^32 * st.u0Hi.toNat) (domainTag ^^^ m30).toNat
  have hadd : next64 < p64 := (addModP64Ct_correct _ _ hcur hmask).2
  have hp64_lt : p64 < 2^64 := by decide
  have hnext_u64 : next64 < 2^64 := Nat.lt_trans hadd hp64_lt
  have hlo : (BitVec.ofNat 32 (next64 % 2^32)).toNat = next64 % 2^32 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  have hhi : (BitVec.ofNat 32 (next64 / 2^32)).toNat = next64 / 2^32 := by
    rw [BitVec.toNat_ofNat]
    have hdiv_lt : next64 / 2^32 < 2^32 := by omega
    exact Nat.mod_eq_of_lt hdiv_lt
  constructor
  · have h_all : ∀ v : BitVec 32, v &&& (4294967295#32 : BitVec 32) = v := by
      intro v
      have : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [this, BitVec.and_allOnes]
    have h_u0lo : out.u0Lo = BitVec.ofNat 32 (next64 % 2^32) := by
      simp [out, stepSolinasIvc64, m30, next64, hz0, h_all]
    have h_u0hi : out.u0Hi = BitVec.ofNat 32 (next64 / 2^32) := by
      simp [out, stepSolinasIvc64, m30, next64, hz0, h_all]
    rw [h_u0lo, h_u0hi, hlo, hhi]
    have hdm : next64 % 2^32 + 2^32 * (next64 / 2^32) = next64 := by
      have := Nat.div_add_mod next64 (2^32)
      omega
    rw [hdm]
    exact hadd
  · simp [out, stepSolinasIvc64, hz0]

end PuristSiliconCore
