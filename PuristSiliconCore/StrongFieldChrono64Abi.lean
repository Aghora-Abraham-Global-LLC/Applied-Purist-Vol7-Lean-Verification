import PuristSiliconCore.Anchor
import PuristSiliconCore.D106AndBitwise
import PuristSiliconCore.SolinasIvc64Abi

namespace PuristSiliconCore

/-- Canonical Vol. VII Listing 7.1 / Vol. VIII SovereignQuadKernel64 64-byte f32 packet (4 x vec4<f32>). -/
structure StrongFieldChronoState64 where
  hBmsPlus         : BitVec 32 -- +00 B (.x)
  hBmsCross        : BitVec 32 -- +04 B (.y)
  qnmOmegaRe       : BitVec 32 -- +08 B (.z)
  morton30Local    : BitVec 32 -- +12 B (.w) STRICTLY READ-ONLY Morton-30
  tailI5Norm       : BitVec 32 -- +16 B (.x)
  tailPhaseRad     : BitVec 32 -- +20 B (.y)
  nhekCftMatch     : BitVec 32 -- +24 B (.z)
  drayUnitarityDef : BitVec 32 -- +28 B (.w)
  tauEpochHi       : BitVec 32 -- +32 B (.x)
  tauEpochLo       : BitVec 32 -- +36 B (.y)
  sagnacLoopNs     : BitVec 32 -- +40 B (.z)
  geopotWRes       : BitVec 32 -- +44 B (.w)
  d106ErrNorm      : BitVec 32 -- +48 B (.x)
  morton30Wire     : BitVec 32 -- +52 B (.y) STRICTLY READ-ONLY Morton-30 wire mirror
  lTclRate         : BitVec 32 -- +56 B (.z) Wiped under zeroize_flag == 1u
  abiStatusParity  : BitVec 32 -- +60 B (.w) Pure f32 status parity (1.0f32 active / 0.0f32 wiped)

/-- Companion integer attestation buffer (attest_seals : array<vec4<u32>>; zero f32 integer transits). -/
structure AttestSealVec4 where
  bbTag    : BitVec 32 -- .x: priorTag ^ m30Bound or 0xdead0000u wipe sentinel
  m30Bound : BitVec 32 -- .y: m30Local ^ m30Wire (< 2^30)
  wiped    : BitVec 32 -- .z: 1u if wiped else 0u
  reserved : BitVec 32 -- .w: 0u

/-- Vol. VIII Unified SovereignQuadKernel64 dual-buffer ABI envelope (64B SoA + 16B u32 companion seal). -/
structure SovereignQuadKernel64 where
  state      : StrongFieldChronoState64
  attestSeal : AttestSealVec4

def chrono64AllOffsets : List Nat :=
  [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]

def chrono64ReadOnlyMortonOffsets : List Nat := [12, 52]

def chrono64NonMortonWipeOffsets : List Nat :=
  [0, 4, 8, 16, 20, 24, 28, 32, 36, 40, 44, 48, 56, 60]

/-- IVV-APP7-06 / IVV-APP8-01: All 16 lanes fit in 64B, are 4B-aligned, pairwise distinct, and 14/14 wipe lanes are disjoint from +12B/.w & +52B/.y. -/
theorem chrono64_lane_offsets_distinct_and_aligned :
    chrono64AllOffsets.length = 16 ∧
    chrono64ReadOnlyMortonOffsets.length = 2 ∧
    chrono64NonMortonWipeOffsets.length = 14 ∧
    chrono64AllOffsets.all (fun o => o < 64 && o % 4 == 0) = true ∧
    chrono64AllOffsets.Nodup ∧
    chrono64NonMortonWipeOffsets.all (fun o => !chrono64ReadOnlyMortonOffsets.contains o) = true := by
  decide

/-- IEEE-754 f32 1.0 parity sentinel (0x3f800000) and SP 800-88 wipe sentinel (0xdead0000). -/
def f32OneBits : BitVec 32 := 0x3f800000#32
def sp80088SentinelU32 : BitVec 32 := 0xdead0000#32

/-- Executable model of Vol. VII Listing 7.1 (non-copied RO Morton-30, 14/14 non-Morton wipe, companion u32 seal). -/
def stepStrongFieldChrono64 (st : StrongFieldChronoState64) (sealIn : AttestSealVec4)
    (nextQnmF32 nextEpochF32 lTclSecularF32 : BitVec 32)
    (zeroizeFlag : BitVec 32) : SovereignQuadKernel64 :=
  let m30Local := readMorton30BV st.morton30Local
  let m30Wire  := readMorton30BV st.morton30Wire
  let m30Bound := m30Local ^^^ m30Wire
  let priorTag := sealIn.bbTag
  let wipeOn   := zeroizeFlag == 1#32
  let selFloat := fun (activeVal : BitVec 32) => if wipeOn then 0#32 else activeVal
  {
    state := {
      hBmsPlus         := selFloat st.hBmsPlus
      hBmsCross        := selFloat st.hBmsCross
      qnmOmegaRe       := selFloat nextQnmF32
      morton30Local    := st.morton30Local
      tailI5Norm       := selFloat st.tailI5Norm
      tailPhaseRad     := selFloat st.tailPhaseRad
      nhekCftMatch     := selFloat st.nhekCftMatch
      drayUnitarityDef := selFloat st.drayUnitarityDef
      tauEpochHi       := selFloat st.tauEpochHi
      tauEpochLo       := selFloat nextEpochF32
      sagnacLoopNs     := selFloat st.sagnacLoopNs
      geopotWRes       := selFloat st.geopotWRes
      d106ErrNorm      := selFloat st.d106ErrNorm
      morton30Wire     := st.morton30Wire
      lTclRate         := selFloat lTclSecularF32
      abiStatusParity  := selFloat f32OneBits
    }
    attestSeal := {
      bbTag    := if wipeOn then sp80088SentinelU32 else (priorTag ^^^ m30Bound)
      m30Bound := m30Bound
      wiped    := if wipeOn then 1#32 else 0#32
      reserved := 0#32
    }
  }

/-- Morton-30 lanes at +12B/.w and +52B/.y are strictly immutable and m30Bound < 2^30 for every zeroizeFlag. -/
theorem strongFieldChrono64_morton30_immutable_always
    (st : StrongFieldChronoState64) (sealIn : AttestSealVec4)
    (nextQnmF32 nextEpochF32 lTclSecularF32 zeroizeFlag : BitVec 32) :
    let out := stepStrongFieldChrono64 st sealIn nextQnmF32 nextEpochF32 lTclSecularF32 zeroizeFlag
    out.state.morton30Local = st.morton30Local ∧
    out.state.morton30Wire = st.morton30Wire ∧
    out.attestSeal.m30Bound.toNat < 2^30 := by
  intro out
  have ha := readMorton30BV_lt st.morton30Local
  have hb := readMorton30BV_lt st.morton30Wire
  refine ⟨rfl, rfl, ?_⟩
  change (readMorton30BV st.morton30Local ^^^ readMorton30BV st.morton30Wire).toNat < 2^30
  rw [BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow ha hb

/-- Under zeroizeFlag == 1u, ALL 14/14 non-Morton f32 lanes (including .z/.w) wipe to 0 while Morton lanes stay untouched. -/
theorem strongFieldChrono64_14_of_14_wipe_total
    (st : StrongFieldChronoState64) (sealIn : AttestSealVec4)
    (nextQnmF32 nextEpochF32 lTclSecularF32 : BitVec 32) :
    let out := stepStrongFieldChrono64 st sealIn nextQnmF32 nextEpochF32 lTclSecularF32 1#32
    out.state.hBmsPlus = 0#32 ∧ out.state.hBmsCross = 0#32 ∧ out.state.qnmOmegaRe = 0#32 ∧
    out.state.tailI5Norm = 0#32 ∧ out.state.tailPhaseRad = 0#32 ∧ out.state.nhekCftMatch = 0#32 ∧
    out.state.drayUnitarityDef = 0#32 ∧ out.state.tauEpochHi = 0#32 ∧ out.state.tauEpochLo = 0#32 ∧
    out.state.sagnacLoopNs = 0#32 ∧ out.state.geopotWRes = 0#32 ∧ out.state.d106ErrNorm = 0#32 ∧
    out.state.lTclRate = 0#32 ∧ out.state.abiStatusParity = 0#32 ∧
    out.state.morton30Local = st.morton30Local ∧ out.state.morton30Wire = st.morton30Wire ∧
    out.attestSeal.bbTag = sp80088SentinelU32 ∧ out.attestSeal.wiped = 1#32 := by
  intro out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩ <;>
    simp [out, stepStrongFieldChrono64]

/-- Under zeroizeFlag == 0u, wire_tcl_seal.z holds lTclSecularF32, .w holds pure f32 1.0, and attest_seals holds u32 tag. -/
theorem strongFieldChrono64_active_parity_and_zero_f32_transit
    (st : StrongFieldChronoState64) (sealIn : AttestSealVec4)
    (nextQnmF32 nextEpochF32 lTclSecularF32 : BitVec 32) :
    let out := stepStrongFieldChrono64 st sealIn nextQnmF32 nextEpochF32 lTclSecularF32 0#32
    out.state.qnmOmegaRe = nextQnmF32 ∧
    out.state.tauEpochLo = nextEpochF32 ∧
    out.state.lTclRate = lTclSecularF32 ∧
    out.state.abiStatusParity = f32OneBits ∧
    out.attestSeal.bbTag = (sealIn.bbTag ^^^ (readMorton30BV st.morton30Local ^^^ readMorton30BV st.morton30Wire)) ∧
    out.attestSeal.wiped = 0#32 ∧
    out.state.abiStatusParity ≠ sp80088SentinelU32 := by
  intro out
  have hneq : f32OneBits ≠ sp80088SentinelU32 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [out, stepStrongFieldChrono64] <;>
    exact hneq

end PuristSiliconCore
