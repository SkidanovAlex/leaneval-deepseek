import Submission.Work.Core.Defs
import Submission.Work.Core.Reduction

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- The standard complex structure on `E n` transported by a real-linear isomorphism
`T : E n ≃ F n`: the linear map `T⁻¹ ∘ (multiplication by i) ∘ T`. -/
noncomputable def stdOf (T : E n ≃L[ℝ] F n) : E n → E n →L[ℝ] E n :=
  fun _ => (T.symm : F n →L[ℝ] E n).comp
    ((Complex.I • (1 : F n →L[ℝ] F n)).comp (T : E n →L[ℝ] F n))

lemma stdOf_apply (T : E n ≃L[ℝ] F n) (y v : E n) :
    stdOf T y v = (T.symm : F n →L[ℝ] E n) (Complex.I • (T : E n →L[ℝ] F n) v) := rfl

lemma stdOf_sq (T : E n ≃L[ℝ] F n) (y v : E n) : stdOf T y (stdOf T y v) = -v := by
  simp [stdOf_apply, smul_smul]

lemma stdOf_intertwine' (T : E n ≃L[ℝ] F n) (y v : E n) :
    (T : E n →L[ℝ] F n) (stdOf T y v) = Complex.I • ((T : E n →L[ℝ] F n) v) := by
  simp [stdOf_apply]

lemma stdOf_intertwine (T : E n ≃L[ℝ] F n) (y v : E n) : T (stdOf T y v) = Complex.I • T v := by
  simpa using stdOf_intertwine' T y v

lemma isAlmostComplexOn_stdOf (T : E n ≃L[ℝ] F n) (U : Set (E n)) :
    IsAlmostComplexOn (stdOf T) U :=
  ⟨contDiffOn_const, fun y _ v => stdOf_sq T y v⟩

/-- **Linearisation of `∂̄`.**  For any field of endomorphisms `J` and any `T : E n ≃ F n`,
the `∂̄`-operator of `J` differs from that of the standard structure `stdOf T` by the first order
operator `u ↦ du ∘ (J - stdOf T)`.  This identity turns the equation `∂̄_J u = 0` for a chart
into a *linear* equation in `u`. -/
lemma dbar_linearization (T : E n ≃L[ℝ] F n) (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (y : E n) :
    dbar J u y = dbar (stdOf T) u y
      + (Complex.I / 2) • ((fderiv ℝ u y).comp (J y - stdOf T y)) := by
  ext v
  simp only [dbar, ContinuousLinearMap.comp_apply, Complex.real_smul, smul_apply, add_apply,
    sub_apply, map_sub]
  push_cast
  ring

/-- The `j`-th standard coordinate function associated with `T`. -/
noncomputable def zcoord (T : E n ≃L[ℝ] F n) (j : Fin n) : E n → ℂ :=
  fun y => ecInvL n (T y) j

lemma zcoord_apply (T : E n ≃L[ℝ] F n) (j : Fin n) (y : E n) :
    zcoord T j y = ((ec n).symm (T y)) j := rfl

lemma fderiv_ecInvL_T (T : E n ≃L[ℝ] F n) (y : E n) :
    fderiv ℝ (fun y : E n => ecInvL n (T y)) y
      = (ecInvL n).comp (T : E n →L[ℝ] F n) :=
  ((ContinuousLinearMap.hasFDerivAt (ecInvL n)).comp y
    (ContinuousLinearMap.hasFDerivAt (T : E n →L[ℝ] F n))).fderiv

lemma hasFDerivAt_zcoord (T : E n ≃L[ℝ] F n) (j : Fin n) (y : E n) :
    HasFDerivAt (zcoord T j)
      ((ContinuousLinearMap.proj j).comp ((ecInvL n).comp (T : E n →L[ℝ] F n))) y := by
  have h1 := (ContinuousLinearMap.hasFDerivAt (ecInvL n)).comp y
    (ContinuousLinearMap.hasFDerivAt (T : E n →L[ℝ] F n))
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj j)).comp y h1

lemma fderiv_zcoord (T : E n ≃L[ℝ] F n) (j : Fin n) (y : E n) :
    fderiv ℝ (zcoord T j) y
      = (ContinuousLinearMap.proj j).comp ((ecInvL n).comp (T : E n →L[ℝ] F n)) :=
  (hasFDerivAt_zcoord T j y).fderiv

/-- The standard coordinate functions are `J`-holomorphic for the standard structure of `T`. -/
lemma zcoord_hol (T : E n ≃L[ℝ] F n) (j : Fin n) (y v : E n) :
    fderiv ℝ (zcoord T j) y (stdOf T y v) = Complex.I * fderiv ℝ (zcoord T j) y v := by
  rw [fderiv_zcoord]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [stdOf_intertwine', ecInvL_smul]
  simp [Pi.smul_apply, smul_eq_mul]

/-- The tuple of standard coordinates is `T` followed by the identification with `ℂⁿ`. -/
lemma zcoord_tuple_eq (T : E n ≃L[ℝ] F n) :
    (fun y : E n => fun j => zcoord T j y) = fun y => ecInvL n (T y) := by
  funext y j
  rfl

lemma bijective_fderiv_zcoord_tuple (T : E n ≃L[ℝ] F n) (y : E n) :
    Function.Bijective (fderiv ℝ (fun y : E n => fun j => zcoord T j y) y) := by
  rw [zcoord_tuple_eq, fderiv_ecInvL_T]
  exact ((ecInv n).bijective).comp (T.bijective)

lemma contDiff_zcoord (T : E n ≃L[ℝ] F n) (j : Fin n) : ContDiff ℝ ∞ (zcoord T j) := by
  have h1 : ContDiff ℝ ∞ (fun y : E n => ecInvL n (T y)) :=
    (ContinuousLinearMap.contDiff (n := ∞) (ecInvL n)).comp
      (ContinuousLinearMap.contDiff (n := ∞) (T : E n →L[ℝ] F n))
  have h2 : ContDiff ℝ ∞ (fun y : E n => ecInvL n (T y) j) := by
    have := (ContinuousLinearMap.contDiff (n := ∞) (ContinuousLinearMap.proj j)).comp h1
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using this
  exact h2

lemma isJHolomorphicOn_zcoord (T : E n ≃L[ℝ] F n) (j : Fin n) (U : Set (E n)) :
    IsJHolomorphicOn (stdOf T) (zcoord T j) U :=
  fun y _ v => zcoord_hol T j y v

/-- **The flat case of Newlander–Nirenberg.**  For the standard structure `stdOf T` transported
by a linear isomorphism `T`, the coordinate functions of `T` are holomorphic with invertible
differentials, so the reduction lemma produces the required chart. -/
theorem newlander_nirenberg_std {U : Set (E n)} (hU : IsOpen U) (T : E n ≃L[ℝ] F n)
    {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (F n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → F n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F n → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → F n) y (stdOf T y v) = Complex.I • fderiv ℝ (φ : E n → F n) y v :=
  exists_chart_of_holomorphic hU (subset_refl U) (stdOf T) hx (zcoord T)
    (fun j => (contDiff_zcoord T j).contDiffOn)
    (fun j y _ v => zcoord_hol T j y v)
    (fun y _ => bijective_fderiv_zcoord_tuple T y)

end Submission
