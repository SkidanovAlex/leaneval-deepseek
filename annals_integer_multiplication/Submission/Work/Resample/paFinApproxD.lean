import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paProofs1
import Submission.Work.Resample.axisIter_getD_fxTensorRec
import Submission.Work.Resample.fxTensorErrMixed
import Submission.Work.Resample.tensorMapLin
import Submission.Work.Resample.resAopNorm

namespace Work.Resample

open HvdH

/-! ## Two small helpers (reproved here: `pbFinal` may not be imported) -/

/-- `matOf` of the unbundled entries of a matrix is the matrix. -/
private lemma paMatOf_unb (s t : ℕ) (M : Matrix (Fin s) (Fin t) ℂ) : matOf s t (unb s t M) = M := by
  funext i j
  simp [matOf, unb, i.isLt, j.isLt]

/-- Sum of a constant function over `List.range n`. -/
private lemma paSumRangeConst (c : ℝ) (n : ℕ) :
    ((List.range n).map (fun _ => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp
    ring

/-- **The analytic end of the `Ã` program** (paper Theorem 4.1, `A` half).  If every axis map `Φ j`
satisfies the one-dimensional `SliceSpecAtA` specification (disc preservation + error `< p²`) and
`resA` is contractive (`ResMath1DProp`), then the `D`-fold axis composition of the `Φ j` applied to
an in-disc input vector approximates the tensor product `resAop ss ts α` with error `< D p²`.

Proof route: mirror `Work.Resample.pbFinApproxCore` (`Submission/Work/Resample/pbFinal.lean`; do NOT
import that module — it contains a `sorry`), then adapt to the `axisIter` orientation: identify
`axisIter ss ts Φ D zs0` with `List.ofFn (fxTensorRec ss ts Φ u)` using
`Work.Resample.axisIter_getD_fxTensorRec` plus the lemma `paGlueC` of
`Submission.Work.Resample.paProofs1` (`w = List.ofFn f` from `getD`-agreement), then apply
`Work.Resample.fxTensorErrMixed` with `δ = 0`, `ε i := p²`,
`A i := (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec` (using `Work.Resample.unb_apply` to
identify `matFam` with `resA`), the contraction from `Work.Resample.resAopNorm`/`ResMath1DProp`, and
finally `Work.Resample.tensorMapLin` to rewrite `tensorMapRec` as `resAop`.  The `InDiscVec` part of
`Approx` comes from `Work.Resample.axisIter_disc` and `Work.Resample.axisIter_length`.  The
hypothesis `hΦ` supplies, for each axis, the `SliceSpecAtA` data (the `∃ s t` witnesses are forced to
`ss.getD j 0`, `ts.getD j 0`, which is why the two equalities are required). -/
theorem paFinApproxD (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ))
    (hpar : HvdH.ResParams p α ss ts)
    (hΦ : ∀ j < HvdH.D, ∃ (s t : ℕ) (prep q : HvdH.Cmd) (Kb : ℕ)
        (Pj : List HvdH.Val), s = ss.getD j 0 ∧ t = ts.getD j 0 ∧
        Work.Resample.SliceSpecAtA Kb p α (ss.getD j 0) (ts.getD j 0) prep q (Φ j) Pj)
    (hRM : HvdH.ResMath1DProp)
    (hz : HvdH.InDiscVec p ss.prod zs0) :
    HvdH.Approx p (Work.Resample.axisIter ss ts Φ HvdH.D zs0)
      (Work.Resample.resAop ss ts α (HvdH.fxVec p ss.prod zs0)) (HvdH.D * p ^ 2 : ℕ) := by
  obtain ⟨hssD, htsD, -, hα2, hαp, hdim⟩ := hpar
  have hlen : ts.length = ss.length := by rw [hssD, htsD]
  have hne : ss ≠ [] := by
    intro h
    rw [h] at hssD
    simp [HvdH.D] at hssD
  -- the list length of the input
  have hlen0 : zs0.length = (ss.take HvdH.D).prod * (ss.drop HvdH.D).prod := by
    rw [hz.1, ← List.prod_append, List.take_append_drop]
  -- positivity of the dimensions
  have hssPos : ∀ j < ss.length, 0 < ss.getD j 0 := fun j hj => by
    obtain ⟨h1, h2, -⟩ := hdim j (by rwa [hssD] at hj)
    omega
  have htsPos : ∀ j < ss.length, 0 < ts.getD j 0 := fun j hj => by
    obtain ⟨h1, h2, -⟩ := hdim j (by rwa [hssD] at hj)
    omega
  have htsPosD : ∀ j < ts.length, 0 < ts.getD j 0 :=
    fun j hj => htsPos j (by rwa [hlen] at hj)
  -- the per-axis disc preservation and the one-dimensional error bound
  have hdiscF : ∀ j < HvdH.D, ∀ w : Fin (ss.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ts.getD j 0), HvdH.inDisc p (Φ j w k) := by
    intro j hj w hw k
    obtain ⟨s, t, prep, q, Kb, Pj, -, -, hspec⟩ := hΦ j hj
    exact hspec.2.2.1 w hw k
  have herrF : ∀ j < HvdH.D, ∀ w : Fin (ss.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ts.getD j 0),
      ‖HvdH.fxC p (Φ j w k) - (HvdH.resA (ss.getD j 0) (ts.getD j 0) α).mulVec
        (fun i => HvdH.fxC p (w i)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2 := by
    intro j hj w hw k
    obtain ⟨s, t, prep, q, Kb, Pj, -, -, hspec⟩ := hΦ j hj
    exact hspec.2.2.2 w hw k
  have hdiscS : ∀ j < ss.length, ∀ w : Fin (ss.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ts.getD j 0), HvdH.inDisc p (Φ j w k) :=
    fun j hj w hw k => hdiscF j (by rwa [hssD] at hj) w hw k
  have herrS : ∀ j < ss.length, ∀ w : Fin (ss.getD j 0) → ℤ × ℤ,
      (∀ i, HvdH.inDisc p (w i)) → ∀ k : Fin (ts.getD j 0),
      ‖HvdH.fxC p (Φ j w k) - (HvdH.resA (ss.getD j 0) (ts.getD j 0) α).mulVec
        (fun i => HvdH.fxC p (w i)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2 :=
    fun j hj w hw k => herrF j (by rwa [hssD] at hj) w hw k
  -- the input as a `Fin`-indexed vector
  let u : Fin ss.prod → ℤ × ℤ := fun j => zs0.getD (j : ℕ) (0, 0)
  have hu : ∀ j, HvdH.inDisc p (u j) := fun j =>
    getD_forall (inDisc_default p) hz.2 (j : ℕ)
  -- the `getD` bridge to the `Fin`-indexed recursion
  have hget : ∀ J : Fin ts.prod,
      (Work.Resample.axisIter ss ts Φ HvdH.D zs0).getD (J : ℕ) (0, 0)
        = Work.Resample.fxTensorRec ss ts Φ u J := by
    intro J
    rw [← hssD]
    exact axisIter_getD_fxTensorRec ss ts hlen hssPos htsPos Φ zs0 hz.1 (J : ℕ) J.isLt
  -- length and disc preservation of the resulting array
  have hAlen : (Work.Resample.axisIter ss ts Φ HvdH.D zs0).length = ts.prod := by
    have h := axisIter_length ss ts hlen HvdH.D (by rw [hssD]) (fun j hj => by
      obtain ⟨h1, h2, -⟩ := hdim j hj
      omega) Φ zs0 hlen0
    rw [h, List.take_of_length_le (by rw [htsD]), List.drop_eq_nil_of_le (by rw [hssD])]
    simp
  have hAdisc : ∀ z ∈ Work.Resample.axisIter ss ts Φ HvdH.D zs0, HvdH.inDisc p z :=
    axisIter_disc ss ts hlen HvdH.D (by rw [hssD]) p Φ hdiscS zs0 hlen0 hz.2
  -- linearity and contraction of the one-dimensional factors
  have hAdd : ∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ,
      (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec (x + y)
        = (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec x
          + (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec y :=
    fun i _ x y => Matrix.mulVec_add _ x y
  have hNorm : ∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ,
      ‖(HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec z‖ ≤ ‖z‖ := by
    intro i hi z
    obtain ⟨h1, h2, -, h4, h5⟩ := hdim i (by rwa [hssD] at hi)
    have hb := (hRM (ss.getD i 0) (ts.getD i 0) α p h1 h2 h4 hα2 hαp h5).2.1 z
    exact le_trans hb (by nlinarith [norm_nonneg z])
  -- the accumulated error estimate
  have hv : ∀ j : Fin ss.prod,
      ‖HvdH.fxC p (u j) - HvdH.fxVec p ss.prod zs0 j‖ * (2 : ℝ) ^ p ≤ 0 := by
    intro j
    have h : HvdH.fxC p (u j) = HvdH.fxVec p ss.prod zs0 j := rfl
    rw [h, sub_self, norm_zero, zero_mul]
  have herr := fxTensorErrMixed ss ts hlen p
    (fun i => (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec)
    (fun i => Φ i) (fun _ => (p : ℝ) ^ 2) 0 (le_refl 0) hne
    htsPos hAdd hNorm (fun i hi w hw k => hdiscS i hi w hw k)
    (fun i hi w hw k => herrS i hi w hw k)
    u hu (HvdH.fxVec p ss.prod zs0) hv
  -- the accumulated sum is `D p²`
  have hsum : ((List.range ss.length).map (fun _ : ℕ => (p : ℝ) ^ 2)).sum
      = ((HvdH.D * p ^ 2 : ℕ) : ℝ) := by
    rw [paSumRangeConst, hssD]
    push_cast
    ring
  -- `tensorMapRec` is `resAop`
  have hmatFam : (fun i => (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec)
      = matFam ss ts (fun i j k => rA (ss.getD i 0) (ts.getD i 0) α j k) := by
    funext i
    simp only [matFam, rA, paMatOf_unb]
  have hid : ∀ v : Fin ss.prod → ℂ,
      tensorMapRec ss ts (fun i => (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec) v
        = resAop ss ts α v := by
    intro v
    rw [hmatFam, tensorMapLin ss ts hlen (fun i j k => rA (ss.getD i 0) (ts.getD i 0) α j k) v]
    rfl
  refine ⟨⟨hAlen, hAdisc⟩, ?_⟩
  intro i
  have h1 := herr i
  rw [zero_add, hsum] at h1
  rw [hget i, ← hid (HvdH.fxVec p ss.prod zs0)]
  exact lt_of_eq_of_lt (mul_comm ((2 : ℝ) ^ p) _) h1

end Work.Resample
