import Mathlib
import Submission.Work.SynFFT.mrgBlkHelper
import Submission.Work.SynFFT.mrgBlkZip
import Submission.Work.SynFFT.mrgBlkRestore

/-!
# `Work.SynFFT.hasMrgBlk`

The interleave ("merge") block pass of the synthetic FFT: one `StackLang` word mapping the `2s`
coefficient vectors of a block, together with the parameters `s r p`, to the block reordered by
the scale-`s` interleave `mrgN`: position `2j + ε` receives what was at `j + ε*s`.

The word is the composition of three phases, each proved in its own module:

* `mrgBlk_splitW` (`mrgBlkHelper`) — split `ofList (cvecs ws)` into its two halves
  `cvecs (ws.drop s)` (on top) and `cvecs (ws.take s)`;
* `mrgBlk_zipW` (`mrgBlkZip`) — zip the two halves into the two-element lists
  `ofList [ws_i, ws_{i+s}]` and flatten, producing `cvecs (mrgBlkL s ws)`;
* `mrgBlk_restoreW` (`mrgBlkRestore`) — recompute `s` as `length / 2` and push it back below
  the list.

The mathematical content (that `mrgBlkL s ws` is the interleave, with the same error bound and
all coefficients in the disc) is `mrgBlk_facts` (`mrgBlkHelper`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

theorem hasMrgBlk (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib) : Work.SynFFT.HasMrgBlk := by
  obtain ⟨P1, K1, hP1⟩ := mrgBlk_splitW hk hl
  obtain ⟨P2, K2, hP2⟩ := mrgBlk_zipW hk hl
  obtain ⟨P3, K3, hP3⟩ := mrgBlk_restoreW hk hi hl
  refine ⟨((P1 ;;; P2) ;;; P3), 1000 * (K1 + K2 + K3 + 1), ?_⟩
  intro main p r s ws u e rest hs hlen hdisc happ
  set Kx : ℕ := K1 + K2 + K3 + 1 with hKx
  set U : ℕ := s * (r + 1) * (p + 1) with hU
  set B : ℕ := 100 * Kx * U with hB
  have hU1 : 1 ≤ U := by rw [hU]; exact one_le_sX hs
  have hK1 : K1 ≤ Kx := by rw [hKx]; omega
  have hK2 : K2 ≤ Kx := by rw [hKx]; omega
  have hK3 : K3 ≤ Kx := by rw [hKx]; omega
  -- the pure mathematical content
  obtain ⟨hlen', hdisc', happ'⟩ := mrgBlk_facts p r s ws u e hs hlen hdisc happ
  have hsz : vsz (ofList (cvecs (mrgBlkL s ws))) ≤ 40 * U := by
    rw [hU]
    refine vsz_cvecs_le40 hs ?_ hdisc'
    rw [hlen']
  have hhalf : ((cvecs (mrgBlkL s ws)).length / 2 : ℕ) = s := by
    rw [show (cvecs (mrgBlkL s ws)).length = (mrgBlkL s ws).length from by simp [cvecs],
      mrgBlkL_length]
    exact Nat.mul_div_cancel_left s (by norm_num)
  -- phase 1: split
  have e1 : WordR main P1
      (fun vs => vs = ofList (cvecs ws) :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (cvecs (ws.drop s)) :: ofList (cvecs (ws.take s)) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => B) := by
    refine MrgKit.WordR_weaken (hP1 main s ws r p rest hs hlen hdisc) (fun vs hvs => hvs)
      (fun vs out _ hq => hq) (fun vs _ => ?_)
    have h1 : K1 * s * (r + 1) * (p + 1) = K1 * U := by rw [hU]; ring
    have h2 : K1 ≤ K1 * U := by
      have hh := Nat.mul_le_mul_left K1 hU1
      simpa using hh
    rw [hB, h1]
    nlinarith [h2, hK1, Nat.zero_le Kx]
  -- phase 2: zip and flatten
  have e2 : WordR main P2
      (fun vs => vs = ofList (cvecs (ws.drop s)) :: ofList (cvecs (ws.take s)) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (cvecs (mrgBlkL s ws)) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => B) := by
    refine MrgKit.WordR_weaken (hP2 main s ws r p rest hs hlen hdisc) (fun vs hvs => hvs)
      (fun vs out _ hq => hq) (fun vs _ => ?_)
    have h1 : K2 * s * (r + 1) * (p + 1) = K2 * U := by rw [hU]; ring
    have h2 : K2 ≤ K2 * U := by
      have hh := Nat.mul_le_mul_left K2 hU1
      simpa using hh
    rw [hB, h1]
    nlinarith [h2, hK2, Nat.zero_le Kx]
  -- phase 3: restore `s = length / 2`
  have e3 : WordR main P3
      (fun vs => vs = ofList (cvecs (mrgBlkL s ws)) ::
        .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (cvecs (mrgBlkL s ws)) ::
        .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => B) := by
    have h := hP3 main (cvecs (mrgBlkL s ws)) (.int (r : ℤ) :: .int (p : ℤ) :: rest)
    rw [hhalf] at h
    refine MrgKit.WordR_weaken h (fun vs hvs => hvs) (fun vs out _ hq => hq) (fun vs _ => ?_)
    have h1 : K3 * (vsz (ofList (cvecs (mrgBlkL s ws))) + 1) ≤ K3 * (40 * U + 1) :=
      Nat.mul_le_mul_left K3 (by omega)
    have h2 : K3 ≤ K3 * U := by
      have hh := Nat.mul_le_mul_left K3 hU1
      simpa using hh
    rw [hB]
    nlinarith [h1, h2, hK3, hU1, Nat.zero_le Kx]
  -- assembly
  have e12 := MrgKit.WordR_seqC e1 e2
  have e123 := MrgKit.WordR_seqC e12 e3
  refine MrgKit.WordR_weaken e123 (fun vs hvs => hvs) ?_ (fun vs _ => ?_)
  · intro vs out hvs hQ
    exact ⟨mrgBlkL s ws, hQ, hlen', hdisc', happ'⟩
  · have h5 : (B + B) + B ≤ 1000 * Kx * U := by
      rw [hB]
      have h6 : (100 * Kx * U + 100 * Kx * U) + 100 * Kx * U = 300 * Kx * U := by ring
      rw [h6]
      exact Nat.mul_le_mul_right U (by omega)
    have h7 : 1000 * Kx * U = 1000 * Kx * s * (r + 1) * (p + 1) := by rw [hU]; ring
    rw [h7] at h5
    exact le_trans h5 (Nat.le_add_right _ _)

end Work.SynFFT
