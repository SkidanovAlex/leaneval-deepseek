import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evX

/-!
# The Leibniz rule for the symmetrized reaction `(A, B) ↦ rmSym (A ·) (B ·)`

`Work.Diff.EXT.rmSym X Y` is the *polarization* of the quadratic reaction map `Q = reactionMap`
(namely `(rmPair X Y + rmPair Y X)/2`); it is a bilinear form on curvature arrays and
`rmSym X X = reactionMap X`.  This file proves the Leibniz rule for the `(0,4)`-tensor field
`y ↦ rmSym (A y) (B y)`:

`d (y ↦ rmSym (A y) (B y))_x v = rmSym (dA) (B x) + rmSym (A x) (dB)`,

componentwise (the target `mvfderiv_rmSymV`) as well as at the level of the `Curv4 n`-valued
functions themselves.

## Strategy

* `rmSym` is bilinear in its two array arguments (`rmSym_add_left/smul_left/add_right/smul_right`),
  hence (finite dimensionality) a bounded bilinear map `Curv4 n × Curv4 n → Curv4 n`; its Fréchet
  derivative at `(A x, B x)` is `(U, W) ↦ rmSym U (B x) + rmSym (A x) W` (Mathlib's
  `IsBoundedBilinearMap.deriv_apply`).
* The manifold chain rule (`HasMFDerivAt.comp` together with `HasMFDerivAt.prodMk`) applied to
  `y ↦ (A y, B y)` gives the array-level statement `mvfderiv_bilin_pair`.
* `mdifferentiableAt_curv4_of_components` (the components of a `Curv4 n`-valued map determine its
  differentiability) provides `MDifferentiableAt` for `A`, `B` and for the composite;
  `mvfderiv_pi_apply_aux` / `mvfderiv_curv4_apply_aux` identify the derivative of a `Π`-valued
  (resp. `Curv4`-valued) map componentwise with the components of its derivative, which converts the
  array-level statement into the componentwise one.

The bookkeeping of `mfderiv` goes through the identification `TangentSpace (self W) w ≡ W`, which
holds definitionally but only at full transparency; the auxiliary section below therefore runs with
`backward.isDefEq.respectTransparency false` (an elaboration-only option, reset at the end of the
section, so that the statement of the target theorem is elaborated in the default environment).
-/

section Aux

open Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Bilinearity of `rmPair` and `rmSym` -/

/-- `ricF` is linear: `ricF (c • X) = c * ricF X` (componentwise). -/
theorem ricF_smul' {n : ℕ} (c : ℝ) (X : Curv4 n) (i p : Fin n) :
    Work.Diff.GE.ricF (c • X) i p = c * Work.Diff.GE.ricF X i p := by
  simp only [Work.Diff.GE.ricF, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

/-- `rmPair` is linear in its first argument. -/
theorem rmPair_smul_left {n : ℕ} (c : ℝ) (X Y : Curv4 n) :
    rmPair (c • X) Y = c • rmPair X Y := by
  funext i j k l
  simp only [rmPair, Work.Diff.GE.ricF, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

/-- `rmPair` is linear in its second argument. -/
theorem rmPair_smul_right {n : ℕ} (c : ℝ) (X Y : Curv4 n) :
    rmPair X (c • Y) = c • rmPair X Y := by
  funext i j k l
  simp only [rmPair, Work.Diff.GE.ricF, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

/-- `rmSym` is additive in its first argument. -/
theorem rmSym_add_left {n : ℕ} (X₁ X₂ Y : Curv4 n) :
    rmSym (X₁ + X₂) Y = rmSym X₁ Y + rmSym X₂ Y := by
  funext i j k l
  simp only [rmSym, rmPair_add_left, rmPair_add_right, Pi.add_apply]
  ring

/-- `rmSym` is homogeneous in its first argument. -/
theorem rmSym_smul_left {n : ℕ} (c : ℝ) (X Y : Curv4 n) :
    rmSym (c • X) Y = c • rmSym X Y := by
  funext i j k l
  simp only [rmSym, rmPair_smul_left, rmPair_smul_right, Pi.smul_apply, smul_eq_mul]
  ring

/-- `rmSym` is additive in its second argument. -/
theorem rmSym_add_right {n : ℕ} (X Y₁ Y₂ : Curv4 n) :
    rmSym X (Y₁ + Y₂) = rmSym X Y₁ + rmSym X Y₂ := by
  funext i j k l
  simp only [rmSym, rmPair_add_right, rmPair_add_left, Pi.add_apply]
  ring

/-- `rmSym` is homogeneous in its second argument. -/
theorem rmSym_smul_right {n : ℕ} (c : ℝ) (X Y : Curv4 n) :
    rmSym X (c • Y) = c • rmSym X Y := by
  funext i j k l
  simp only [rmSym, rmPair_smul_right, rmPair_smul_left, Pi.smul_apply, smul_eq_mul]
  ring

/-- `rmSym` is a bilinear form on curvature arrays. -/
theorem rmSym_isBilinearMap (n : ℕ) :
    IsBilinearMap ℝ (fun X Y : Curv4 n => rmSym X Y) where
  add_left X₁ X₂ Y := rmSym_add_left X₁ X₂ Y
  smul_left c X Y := rmSym_smul_left c X Y
  add_right X Y₁ Y₂ := rmSym_add_right X Y₁ Y₂
  smul_right c X Y := rmSym_smul_right c X Y

/-- `rmSym`, as a curried continuous bilinear map (using finite dimensionality of `Curv4 n`). -/
noncomputable def rmSymCLM (n : ℕ) : Curv4 n →L[ℝ] Curv4 n →L[ℝ] Curv4 n :=
  (rmSym_isBilinearMap n).toContinuousBilinearMap

@[simp]
theorem rmSymCLM_apply {n : ℕ} (X Y : Curv4 n) : rmSymCLM n X Y = rmSym X Y := rfl

/-- `rmSym` is a bounded (hence differentiable) bilinear map. -/
theorem rmSym_isBoundedBilinearMap (n : ℕ) :
    IsBoundedBilinearMap ℝ (fun p : Curv4 n × Curv4 n => rmSym p.1 p.2) := by
  have h := ContinuousLinearMap.isBoundedBilinearMap (rmSymCLM n)
  simpa only [rmSymCLM_apply] using h

/-! ## The bilinear chain rule -/

/-- **The Leibniz rule for a bounded bilinear map applied to two `M → V` maps.**  If `b : V × V → V`
is a bounded bilinear map and `A B : M → V` are differentiable at `x`, then
`d (y ↦ b (A y, B y))_x v = b (dA_x v, B x) + b (A x, dB_x v)`. -/
theorem mvfderiv_bilin_pair
    (b : V × V → V) (hbb : IsBoundedBilinearMap ℝ b)
    {A B : M → V} {x : M} (v : TangentSpace I x)
    (hA : MDifferentiableAt I (modelWithCornersSelf ℝ V) A x)
    (hB : MDifferentiableAt I (modelWithCornersSelf ℝ V) B x) :
    mvfderiv I (fun y => b (A y, B y)) x v
      = b (mvfderiv I A x v, B x) + b (A x, mvfderiv I B x v) := by
  have hα : HasFDerivAt b (hbb.deriv (A x, B x)) (A x, B x) := hbb.hasFDerivAt (A x, B x)
  have hLg : HasMFDerivAt (modelWithCornersSelf ℝ (V × V)) (modelWithCornersSelf ℝ V)
      b (A x, B x) (hbb.deriv (A x, B x)) := hα.hasMFDerivAt
  have hmfA : mfderiv I (modelWithCornersSelf ℝ V) A x = mvfderiv I A x := by
    ext w; rfl
  have hmfB : mfderiv I (modelWithCornersSelf ℝ V) B x = mvfderiv I B x := by
    ext w; rfl
  have hpair : HasMFDerivAt I (modelWithCornersSelf ℝ (V × V)) (fun y => (A y, B y)) x
      ((mfderiv I (modelWithCornersSelf ℝ V) A x).prod
        (mfderiv I (modelWithCornersSelf ℝ V) B x)) :=
    HasMFDerivAt.prodMk hA.hasMFDerivAt hB.hasMFDerivAt
  have hcomp := hLg.comp x hpair
  have h1 : mvfderiv I (fun y => b (A y, B y)) x
      = mfderiv I (modelWithCornersSelf ℝ V) (b ∘ fun y => (A y, B y)) x := by
    ext w; rfl
  have hmv : mvfderiv I (fun y => b (A y, B y)) x v
      = (hbb.deriv (A x, B x))
          (((mfderiv I (modelWithCornersSelf ℝ V) A x).prod
            (mfderiv I (modelWithCornersSelf ℝ V) B x)) v) := by
    rw [h1, hcomp.mfderiv]
    rfl
  rw [hmv, ContinuousLinearMap.prod_apply, hbb.deriv_apply]
  rw [hmfA, hmfB]
  ac_rfl

/-- **Differentiability of a bounded bilinear map applied to two differentiable maps.** -/
theorem mdifferentiableAt_bilin_pair
    (b : V × V → V) (hbb : IsBoundedBilinearMap ℝ b)
    {A B : M → V} {x : M}
    (hA : MDifferentiableAt I (modelWithCornersSelf ℝ V) A x)
    (hB : MDifferentiableAt I (modelWithCornersSelf ℝ V) B x) :
    MDifferentiableAt I (modelWithCornersSelf ℝ V) (fun y => b (A y, B y)) x := by
  have hα : HasFDerivAt b (hbb.deriv (A x, B x)) (A x, B x) := hbb.hasFDerivAt (A x, B x)
  have hLg : HasMFDerivAt (modelWithCornersSelf ℝ (V × V)) (modelWithCornersSelf ℝ V)
      b (A x, B x) (hbb.deriv (A x, B x)) := hα.hasMFDerivAt
  have hpair : HasMFDerivAt I (modelWithCornersSelf ℝ (V × V)) (fun y => (A y, B y)) x
      ((mfderiv I (modelWithCornersSelf ℝ V) A x).prod
        (mfderiv I (modelWithCornersSelf ℝ V) B x)) :=
    HasMFDerivAt.prodMk hA.hasMFDerivAt hB.hasMFDerivAt
  exact (hLg.comp x hpair).mdifferentiableAt

end Aux

/-! ## Componentwise differentiability and derivatives of `Π`-valued maps -/

section Comp

open Submission.Diff.Alg

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M]

/-- **Componentwise differentiability of a `Curv4`-valued map.**  A map `A : M → Curv4 n` is
differentiable at `x` as soon as all of its components are. -/
theorem mdifferentiableAt_curv4_of_components {n : ℕ} {A : M → Curv4 n} {x : M}
    (hA : ∀ i j k l, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y => A y i j k l) x) :
    MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n)) A x := by
  rw [mdifferentiableAt_iff]
  refine ⟨?_, ?_⟩
  · exact continuousAt_pi' (fun i => continuousAt_pi' (fun j => continuousAt_pi' (fun k =>
      continuousAt_pi' (fun l => (hA i j k l).continuousAt))))
  · have hΦ : writtenInExtChartAt I (modelWithCornersSelf ℝ (Curv4 n)) x A
        = fun z => A ((extChartAt I x).symm z) := by
      funext z
      simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [hΦ]
    simp only [differentiableWithinAt_pi]
    intro i j k l
    have hmap : writtenInExtChartAt I (modelWithCornersSelf ℝ ℝ) x (fun y => A y i j k l)
        = fun z => A ((extChartAt I x).symm z) i j k l := by
      funext z
      simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    simpa only [hmap] using (hA i j k l).differentiableWithinAt_writtenInExtChartAt

/-- **The components of the derivative of a `Π`-valued map.**  For `θ : M → Π i, Fi i`
differentiable at `x`, the `i`-th component of `dθ_x` is the derivative of the `i`-th component. -/
theorem mvfderiv_pi_apply_aux
    {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
    [∀ i, NormedSpace ℝ (Fi i)]
    (θ : M → Π i, Fi i) (x : M) (v : TangentSpace I x) (i : ι)
    (hθ : MDifferentiableAt I (modelWithCornersSelf ℝ (Π i, Fi i)) θ x) :
    mvfderiv I (fun y : M => θ y i) x v = mvfderiv I θ x v i := by
  have hproj : MDifferentiableAt (modelWithCornersSelf ℝ (Π i, Fi i))
      (modelWithCornersSelf ℝ (Fi i)) (fun w : Π i, Fi i => w i) (θ x) :=
    (differentiableAt_apply (𝕜 := ℝ) i (θ x)).mdifferentiableAt
  have hL : MDifferentiableAt I (modelWithCornersSelf ℝ (Fi i)) (fun y : M => θ y i) x :=
    hproj.comp x hθ
  have h1 := hθ.mvfderiv
  have h2 := hL.mvfderiv
  have hΦ : DifferentiableWithinAt ℝ
      (writtenInExtChartAt I (modelWithCornersSelf ℝ (Π i, Fi i)) x θ)
      (Set.range I) ((extChartAt I x) x) := by
    have h := hθ.mdifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
      (I' := modelWithCornersSelf ℝ (Π i, Fi i)) (s := Set.univ)
    simpa only [Set.preimage_univ, Set.univ_inter] using h
  have hs : UniqueDiffWithinAt ℝ (Set.range I) ((extChartAt I x) x) := by
    have h := UniqueMDiffOn.uniqueDiffWithinAt_range_inter (I := I) (s := Set.univ)
      (uniqueMDiffOn_univ) x ((extChartAt I x) x)
      ⟨(extChartAt I x).map_source (mem_extChartAt_source x), trivial⟩
    simpa only [Set.preimage_univ, Set.inter_univ] using h
  rw [h2, h1]
  have hΨ : writtenInExtChartAt I (modelWithCornersSelf ℝ (Fi i)) x (fun y : M => θ y i)
      = fun z => writtenInExtChartAt I (modelWithCornersSelf ℝ (Π i, Fi i)) x θ z i := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
  rw [hΨ, fderivWithin_apply hΦ hs i]
  rfl

/-- **The components of the derivative of a `Curv4`-valued map.** -/
theorem mvfderiv_curv4_apply_aux {n : ℕ} (f : M → Curv4 n) (x : M) (v : TangentSpace I x)
    (hm : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n)) f x) :
    mvfderiv I f x v = fun i j k l => mvfderiv I (fun y : M => f y i j k l) x v := by
  funext i j k l
  have hd1 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → Fin n → Fin n → ℝ))
      (fun y : M => f y i) x :=
    ((differentiableAt_apply (𝕜 := ℝ) i (f x)).mdifferentiableAt).comp x hm
  have hd2 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → Fin n → ℝ))
      (fun y : M => f y i j) x :=
    ((differentiableAt_apply (𝕜 := ℝ) j (f x i)).mdifferentiableAt).comp x hd1
  have hd3 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → ℝ))
      (fun y : M => f y i j k) x :=
    ((differentiableAt_apply (𝕜 := ℝ) k (f x i j)).mdifferentiableAt).comp x hd2
  rw [← mvfderiv_pi_apply_aux (θ := f) x v i hm]
  rw [← mvfderiv_pi_apply_aux (θ := fun y : M => f y i) x v j hd1]
  rw [← mvfderiv_pi_apply_aux (θ := fun y : M => (fun y : M => f y i) y j) x v k hd2]
  rw [← mvfderiv_pi_apply_aux
    (θ := fun y : M => (fun y : M => (fun y : M => f y i) y j) y k) x v l hd3]

end Comp

theorem mvfderiv_rmSymV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (n : ℕ) (A B : M → Submission.Diff.Alg.Curv4 n)
    (x : M) (v : TangentSpace I x)
    (hA : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun y => A y p q r s) x)
    (hB : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun y => B y p q r s) x)
    (i j k l : Fin n) :
    mvfderiv I (fun y => Work.Diff.EXT.rmSym (A y) (B y) i j k l) x v
      = Work.Diff.EXT.rmSym
          (fun p q r s => mvfderiv I (fun y => A y p q r s) x v) (B x) i j k l
        + Work.Diff.EXT.rmSym
          (A x) (fun p q r s => mvfderiv I (fun y => B y p q r s) x v) i j k l := by
  have hA' : MDifferentiableAt I (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 n)) A x :=
    mdifferentiableAt_curv4_of_components hA
  have hB' : MDifferentiableAt I (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 n)) B x :=
    mdifferentiableAt_curv4_of_components hB
  have hFmd : MDifferentiableAt I (modelWithCornersSelf ℝ (Submission.Diff.Alg.Curv4 n))
      (fun y => Work.Diff.EXT.rmSym (A y) (B y)) x :=
    mdifferentiableAt_bilin_pair
      (fun p : Submission.Diff.Alg.Curv4 n × Submission.Diff.Alg.Curv4 n =>
        Work.Diff.EXT.rmSym p.1 p.2)
      (rmSym_isBoundedBilinearMap n) hA' hB'
  have hchain := mvfderiv_bilin_pair
      (fun p : Submission.Diff.Alg.Curv4 n × Submission.Diff.Alg.Curv4 n =>
        Work.Diff.EXT.rmSym p.1 p.2)
      (rmSym_isBoundedBilinearMap n) v hA' hB'
  have hsplit := mvfderiv_curv4_apply_aux
      (f := fun y => Work.Diff.EXT.rmSym (A y) (B y)) x v hFmd
  have hkey : (fun i j k l =>
        mvfderiv I (fun y => Work.Diff.EXT.rmSym (A y) (B y) i j k l) x v)
      = Work.Diff.EXT.rmSym (mvfderiv I A x v) (B x)
        + Work.Diff.EXT.rmSym (A x) (mvfderiv I B x v) := by
    rw [← hsplit, hchain]
  have hcomp := congrFun (congrFun (congrFun (congrFun hkey i) j) k) l
  rw [mvfderiv_curv4_apply_aux (f := A) x v hA',
    mvfderiv_curv4_apply_aux (f := B) x v hB'] at hcomp
  simpa only [Pi.add_apply] using hcomp

end Work.Diff.EXT.evX
