import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter

/-! # The iterated partial derivatives of a finite sum

`Work.Diff.STE.pdRList l f` is the iterated partial derivative of `f : (Fin d → ℝ) → ℝ` along the
list of coordinate directions `l`.  This module proves that it is **additive** on finite sums of
functions that are `C²` at the base point: for `l.length ≤ 2` the function `f ↦ pdRList l f z` is
linear, so that the derivatives of `∑ i ∈ s, φ i` are the sums of the derivatives of the `φ i`.
The constant in the resulting estimate is `1`. -/

/-- If `f` is `C²` at `z`, then every partial derivative of `f` of order `≤ 1` is differentiable in
a neighbourhood of `z`. -/
lemma pdRList_eventually_differentiableAt {d : ℕ} {f : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (h : ContDiffAt ℝ 2 f z) (l : List (Fin d)) (hl : l.length ≤ 1) :
    ∀ᶠ y in nhds z, DifferentiableAt ℝ (Work.Diff.STE.pdRList l f) y := by
  cases l with
  | nil =>
    exact (h.eventually (by norm_num)).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  | cons b t =>
    cases t with
    | nil =>
      change ∀ᶠ y in nhds z, DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) y
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
      have h2 : ContDiffAt ℝ 1 (fun y => (fderiv ℝ f) y (Pi.single b 1)) z :=
        h1.clm_apply contDiffAt_const
      exact (h2.eventually (by norm_num)).mono
        (fun y hy => hy.differentiableAt (by norm_num))
    | cons c t =>
      simp only [List.length_cons] at hl
      omega

/-- The derivative of a finite sum of functions that are differentiable near `z`. -/
lemma fderiv_finset_sum_eventuallyEq {d : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → (Fin d → ℝ) → ℝ) {z : Fin d → ℝ}
    (h : ∀ᶠ y in nhds z, ∀ i ∈ s, DifferentiableAt ℝ (A i) y) :
    fderiv ℝ (fun y => ∑ i ∈ s, A i y) =ᶠ[nhds z]
      fun y => ∑ i ∈ s, fderiv ℝ (A i) y := by
  filter_upwards [h] with y hy
  exact fderiv_fun_sum hy

/-- **Linearity of `pdRList` on finite sums.**  If every `φ i` (`i ∈ s`) is `C²` at `z` and
`l.length ≤ 2`, then `pdRList l (∑ i ∈ s, φ i)` agrees near `z` with `∑ i ∈ s, pdRList l (φ i)`. -/
lemma pdRList_finset_sum_eventuallyEq {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (φ : ι → (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) :
    ∀ l : List (Fin d), l.length ≤ 2 →
      (∀ i ∈ s, ContDiffAt ℝ 2 (φ i) z) →
      Work.Diff.STE.pdRList l (fun y => ∑ i ∈ s, φ i y)
        =ᶠ[nhds z] fun y => ∑ i ∈ s, Work.Diff.STE.pdRList l (φ i) y := by
  intro l
  induction l with
  | nil => intro hl h; exact Filter.EventuallyEq.rfl
  | cons a l' ih =>
    intro hl h
    have hl2 : l'.length ≤ 2 := by simp only [List.length_cons] at hl; omega
    have hl1 : l'.length ≤ 1 := by simp only [List.length_cons] at hl; omega
    have hIH := ih hl2 h
    have hfd : fderiv ℝ (Work.Diff.STE.pdRList l' (fun y => ∑ i ∈ s, φ i y))
        =ᶠ[nhds z] fderiv ℝ (fun y => ∑ i ∈ s, Work.Diff.STE.pdRList l' (φ i) y) :=
      hIH.fderiv
    have e1 : (fun y => fderiv ℝ (Work.Diff.STE.pdRList l' (fun y => ∑ i ∈ s, φ i y)) y
          (Pi.single a 1))
        =ᶠ[nhds z]
        (fun y => fderiv ℝ (fun y => ∑ i ∈ s, Work.Diff.STE.pdRList l' (φ i) y) y
          (Pi.single a 1)) := by
      filter_upwards [hfd] with y hy
      exact congrArg (fun (L : (Fin d → ℝ) →L[ℝ] ℝ) => L (Pi.single a 1)) hy
    have e2 : (fun y => fderiv ℝ (fun y => ∑ i ∈ s, Work.Diff.STE.pdRList l' (φ i) y) y
          (Pi.single a 1))
        =ᶠ[nhds z]
        (fun y => ∑ i ∈ s, fderiv ℝ (Work.Diff.STE.pdRList l' (φ i)) y (Pi.single a 1)) := by
      have hdiff : ∀ᶠ y in nhds z, ∀ i ∈ s,
          DifferentiableAt ℝ (Work.Diff.STE.pdRList l' (φ i)) y := by
        rw [eventually_all_finset]
        exact fun i hi => pdRList_eventually_differentiableAt (h i hi) l' hl1
      filter_upwards [fderiv_finset_sum_eventuallyEq s (fun i => Work.Diff.STE.pdRList l' (φ i))
        hdiff] with y hy
      rw [hy]
      exact map_sum (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1))
        (fun i => fderiv ℝ (Work.Diff.STE.pdRList l' (φ i)) y) s
    exact e1.trans e2

/-- Linearity of `pdRList` on a finite sum, in pointwise form. -/
lemma pdRList_finset_sum_eq {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (φ : ι → (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) (l : List (Fin d))
    (hl : l.length ≤ 2) (h : ∀ i ∈ s, ContDiffAt ℝ 2 (φ i) z) :
    Work.Diff.STE.pdRList l (fun y => ∑ i ∈ s, φ i y) z
      = ∑ i ∈ s, Work.Diff.STE.pdRList l (φ i) z :=
  (pdRList_finset_sum_eventuallyEq s φ z l hl h).eq_of_nhds

theorem pdRList_finset_sum_le {d : ℕ} {ι : Type*} [DecidableEq ι] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : Finset ι) (φ : ι → (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) (K : ℝ),
        0 ≤ K → (∀ i ∈ s, ContDiffAt ℝ 2 (φ i) z) →
        (∀ i ∈ s, ∀ l : List (Fin d), l.length ≤ 2 → |Work.Diff.STE.pdRList l (φ i) z| ≤ K) →
        ∀ l : List (Fin d), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (fun y => ∑ i ∈ s, φ i y) z| ≤ C * (s.card : ℝ) * K := by
  refine ⟨1, by norm_num, ?_⟩
  intro s φ z K hK hcd hbnd l hl
  rw [pdRList_finset_sum_eq s φ z l hl hcd]
  have h1 : |∑ i ∈ s, Work.Diff.STE.pdRList l (φ i) z|
      ≤ ∑ i ∈ s, |Work.Diff.STE.pdRList l (φ i) z| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i ∈ s, |Work.Diff.STE.pdRList l (φ i) z| ≤ ∑ i ∈ s, K :=
    Finset.sum_le_sum (fun i hi => hbnd i hi l hl)
  calc |∑ i ∈ s, Work.Diff.STE.pdRList l (φ i) z| ≤ ∑ i ∈ s, K := le_trans h1 h2
    _ = (s.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 1 * (s.card : ℝ) * K := by ring

end Work.Diff.STE.Lead
