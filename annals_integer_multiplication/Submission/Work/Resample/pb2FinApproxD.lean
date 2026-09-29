import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.axisIter_getD_fxTensorRec
import Submission.Work.Resample.fxTensorErrMixed
import Submission.Work.Resample.tensorMapLin
import Submission.Work.Resample.resAopNorm

/-! Guidance from the project lead (the requester):

LEAD (endgame: Resample's B half is the LAST open piece of the whole problem — speed matters). This statement is the
MIRROR of the already PROVED `Work.Resample.paFinApproxD` (Submission/Work/Resample/). Start by COPYING that file's proof and
adapting it; do not design anything new. Mirror dictionary (definitions in Submission/Work/Resample/pb2Defs.lean):
PAVec/PAInv/PAMid/PABr/PAIterBrF ↦ PB2Vec/PB2Inv/PB2Mid/PB2Br/PB2IterBrF; the array flows from shape ts (input,
ts.prod entries) to shape ss (output); list iteration is `axisIter ts ss Φ` with Φ j : (Fin t_j → ℤ×ℤ) → (Fin s_j → ℤ×ℤ);
applyAlong arguments per axis j are A = (ss.take j).prod, m = t_j, n = s_j, B = (ts.drop (j+1)).prod; stack 2 holds the
remaining INPUT dims (ts.drop j), stack 3 the remaining OUTPUT dims (ss.drop j), stack 6 (ss.take j).prod, stack 7 s_j;
SliceSpecAtA Kb p α s t prep q Φ P ↦ SliceSpecAt prep q Kb p α s t Φ P (argument order differs; its q cost has the extra
Kb(t+1)(p+1)² term, already in PB2Br); resAop/rA ↦ resBop/rB. Size bounds keep ts.prod (sᵢ < tᵢ, so every intermediate
array has ≤ ts.prod entries: (ss.take j).prod ≤ (ts.take j).prod). NEVER import pbSetupF, pbRoundF, pbIterGo*, pbIterF*
(obsolete route; pbSetupF needs 17 GB). Split into children only where the A-side proof was split.
-/

namespace Work.Resample

open HvdH

/-! ## Two small helpers (reproved here, mirroring the private helpers of `paFinApproxD`) -/

/-- `matOf` of the unbundled entries of a matrix is the matrix. -/
private lemma pbMatOf_unb (s t : ℕ) (M : Matrix (Fin s) (Fin t) ℂ) : matOf s t (unb s t M) = M := by
  funext i j
  simp [matOf, unb, i.isLt, j.isLt]

/-- Sum of a constant function over `List.range n`. -/
private lemma pbSumRangeConst (c : ℝ) (n : ℕ) :
    ((List.range n).map (fun _ => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp
    ring

/-- Mirror of paFinApproxD for the B half: the D-fold axis iteration approximates resBop within D p^2. -/
theorem pb2FinApproxD (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ))
    (hpar : HvdH.ResParams p α ss ts)
    (hΦ : ∀ j < HvdH.D, ∃ (prep q : HvdH.Cmd) (Kb : ℕ) (Pj : List HvdH.Val),
        Work.Resample.SliceSpecAt prep q Kb p α (ss.getD j 0) (ts.getD j 0) (Φ j) Pj)
    (hRM : HvdH.ResMath1DProp)
    (hz : HvdH.InDiscVec p ts.prod zs0) :
    HvdH.Approx p (Work.Resample.axisIter ts ss Φ HvdH.D zs0)
      (Work.Resample.resBop ss ts α (HvdH.fxVec p ts.prod zs0)) (HvdH.D * p ^ 2 : ℕ) := by
  obtain ⟨hssD, htsD, -, hα2, hαp, hdim⟩ := hpar
  have hlen : ss.length = ts.length := by rw [hssD, htsD]
  have hne : ts ≠ [] := by
    intro h
    rw [h] at htsD
    simp [HvdH.D] at htsD
  -- the list length of the input
  have hlen0 : zs0.length = (ts.take HvdH.D).prod * (ts.drop HvdH.D).prod := by
    rw [hz.1, ← List.prod_append, List.take_append_drop]
  -- positivity of the dimensions
  have hssPos : ∀ j < ss.length, 0 < ss.getD j 0 := fun j hj => by
    obtain ⟨h1, h2, -⟩ := hdim j (by rwa [hssD] at hj)
    omega
  have htsPos : ∀ j < ss.length, 0 < ts.getD j 0 := fun j hj => by
    obtain ⟨h1, h2, -⟩ := hdim j (by rwa [hssD] at hj)
    omega
  have htsPosD : ∀ j < ts.length, 0 < ts.getD j 0 :=
    fun j hj => htsPos j (hlen.symm ▸ hj)
  have hssPosD : ∀ j < ts.length, 0 < ss.getD j 0 :=
    fun j hj => hssPos j (hlen.symm ▸ hj)
  -- the per-axis disc preservation and the one-dimensional error bound
  have hdiscF : ∀ j < HvdH.D, ∀ w : Fin (ts.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ss.getD j 0), HvdH.inDisc p (Φ j w k) := by
    intro j hj w hw k
    obtain ⟨prep, q, Kb, Pj, hspec⟩ := hΦ j hj
    exact hspec.2.2.1 w hw k
  have herrF : ∀ j < HvdH.D, ∀ w : Fin (ts.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ss.getD j 0),
      ‖HvdH.fxC p (Φ j w k) - (HvdH.resB (ss.getD j 0) (ts.getD j 0) α).mulVec
        (fun i => HvdH.fxC p (w i)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2 := by
    intro j hj w hw k
    obtain ⟨prep, q, Kb, Pj, hspec⟩ := hΦ j hj
    exact hspec.2.2.2 w hw k
  have hdiscS : ∀ j < ts.length, ∀ w : Fin (ts.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ss.getD j 0), HvdH.inDisc p (Φ j w k) :=
    fun j hj w hw k => hdiscF j (by rwa [htsD] at hj) w hw k
  have herrS : ∀ j < ts.length, ∀ w : Fin (ts.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ss.getD j 0),
      ‖HvdH.fxC p (Φ j w k) - (HvdH.resB (ss.getD j 0) (ts.getD j 0) α).mulVec
        (fun i => HvdH.fxC p (w i)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2 :=
    fun j hj w hw k => herrF j (by rwa [htsD] at hj) w hw k
  -- the input as a `Fin`-indexed vector
  let u : Fin ts.prod → ℤ × ℤ := fun j => zs0.getD (j : ℕ) (0, 0)
  have hu : ∀ j, HvdH.inDisc p (u j) := fun j =>
    getD_forall (inDisc_default p) hz.2 (j : ℕ)
  -- the `getD` bridge to the `Fin`-indexed recursion
  have hget : ∀ J : Fin ss.prod,
      (Work.Resample.axisIter ts ss Φ HvdH.D zs0).getD (J : ℕ) (0, 0)
        = Work.Resample.fxTensorRec ts ss Φ u J := by
    intro J
    rw [← htsD]
    exact axisIter_getD_fxTensorRec ts ss hlen htsPosD hssPosD Φ zs0 hz.1 (J : ℕ) J.isLt
  -- length and disc preservation of the resulting array
  have hAlen : (Work.Resample.axisIter ts ss Φ HvdH.D zs0).length = ss.prod := by
    have h := axisIter_length ts ss hlen HvdH.D (by rw [htsD]) (fun j hj => by
      obtain ⟨h1, h2, -⟩ := hdim j hj
      omega) Φ zs0 hlen0
    rw [h, List.take_of_length_le (by rw [hssD]), List.drop_eq_nil_of_le (by rw [htsD])]
    simp
  have hAdisc : ∀ z ∈ Work.Resample.axisIter ts ss Φ HvdH.D zs0, HvdH.inDisc p z :=
    axisIter_disc ts ss hlen HvdH.D (by rw [htsD]) p Φ hdiscS zs0 hlen0 hz.2
  -- linearity and contraction of the one-dimensional factors
  have hAdd : ∀ i < ts.length, ∀ x y : Fin (ts.getD i 0) → ℂ,
      (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec (x + y)
        = (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec x
          + (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec y :=
    fun i _ x y => Matrix.mulVec_add _ x y
  have hNorm : ∀ i < ts.length, ∀ z : Fin (ts.getD i 0) → ℂ,
      ‖(HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec z‖ ≤ ‖z‖ := by
    intro i hi z
    obtain ⟨h1, h2, -, h4, h5⟩ := hdim i (by rwa [htsD] at hi)
    have hb := (hRM (ss.getD i 0) (ts.getD i 0) α p h1 h2 h4 hα2 hαp h5).2.2.2.2.2.2.2 z
    exact hb
  -- the accumulated error estimate
  have hv : ∀ j : Fin ts.prod,
      ‖HvdH.fxC p (u j) - HvdH.fxVec p ts.prod zs0 j‖ * (2 : ℝ) ^ p ≤ 0 := by
    intro j
    have h : HvdH.fxC p (u j) = HvdH.fxVec p ts.prod zs0 j := rfl
    rw [h, sub_self, norm_zero, zero_mul]
  have herr := fxTensorErrMixed ts ss hlen p
    (fun i => (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec)
    (fun i => Φ i) (fun _ => (p : ℝ) ^ 2) 0 (le_refl 0) hne
    hssPosD hAdd hNorm (fun i hi w hw k => hdiscS i hi w hw k)
    (fun i hi w hw k => herrS i hi w hw k)
    u hu (HvdH.fxVec p ts.prod zs0) hv
  -- the accumulated sum is `D p²`
  have hsum : ((List.range ts.length).map (fun _ : ℕ => (p : ℝ) ^ 2)).sum
      = ((HvdH.D * p ^ 2 : ℕ) : ℝ) := by
    rw [pbSumRangeConst, htsD]
    push_cast
    ring
  -- `tensorMapRec` is `resBop`
  have hmatFam : (fun i => (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec)
      = matFam ts ss (fun i j k => rB (ss.getD i 0) (ts.getD i 0) α j k) := by
    funext i
    simp only [matFam, rB, pbMatOf_unb]
  have hid : ∀ v : Fin ts.prod → ℂ,
      tensorMapRec ts ss (fun i => (HvdH.resB (ss.getD i 0) (ts.getD i 0) α).mulVec) v
        = resBop ss ts α v := by
    intro v
    rw [hmatFam, tensorMapLin ts ss hlen (fun i j k => rB (ss.getD i 0) (ts.getD i 0) α j k) v]
    rfl
  refine ⟨⟨hAlen, hAdisc⟩, ?_⟩
  intro i
  have h1 := herr i
  rw [zero_add, hsum] at h1
  rw [hget i, ← hid (HvdH.fxVec p ts.prod zs0)]
  exact lt_of_eq_of_lt (mul_comm ((2 : ℝ) ^ p) _) h1

end Work.Resample
