import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.LWP.CurlFree

/-- A `C¹` curl-free vector field on `ℝ³` is the gradient of a scalar potential.  This is the
Poincaré lemma on the simply connected domain `ℝ³`: the `1`-form `z ↦ ⟪F z, ·⟫` is closed
because its derivative `innerSL ℝ ∘ D F` is symmetric (here the vanishing of `vorticity F` is
used), and Mathlib's Poincaré lemma for convex sets produces a primitive. -/
theorem curlFree_isGradient (F : R3 → R3) (hF : ContDiff ℝ 1 F)
    (hcurl : ∀ x, FiniteTimeSingularity.vorticity F x = 0) :
    ∃ P : R3 → ℝ, ∀ x, ∀ y : R3, fderiv ℝ P x y = inner ℝ (F x) y := by
  -- The `1`-form `ω z = ⟪F z, ·⟫`, a continuous linear functional at each point.
  let ω : R3 → (R3 →L[ℝ] ℝ) := fun z => innerSL ℝ (F z)
  -- `ω` is differentiable, being `innerSL ℝ` composed with the `C¹` map `F`.
  have hω : DifferentiableOn ℝ ω Set.univ := by
    apply Differentiable.differentiableOn
    exact (ContinuousLinearMap.differentiable (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ))).comp
      hF.differentiable_one
  -- Its derivative is `innerSL ℝ ∘ D F`.
  have hfderivω : ∀ a, fderiv ℝ ω a =
      (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ)).comp (fderiv ℝ F a) := by
    intro a
    have hF' : HasFDerivAt F (fderiv ℝ F a) a := (hF.differentiable_one a).hasFDerivAt
    exact ((ContinuousLinearMap.hasFDerivAt (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ))
      (x := F a)).comp a hF').fderiv
  -- The derivative of `ω` is symmetric; this is exactly the curl-free condition.
  have hsymm : ∀ a ∈ Set.univ, ∀ x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x := by
    intro a _ x y
    rw [hfderivω a, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, innerSL_apply_apply]
    -- Goal: `⟪DF a x, y⟫ = ⟪DF a y, x⟫`.  Write `L := DF a` and show `L` is symmetric: its
    -- matrix in the standard basis is symmetric because the curl
    -- `∑ i, e i ⨯₃ L (e i)` vanishes.
    set L := fderiv ℝ F a with hLdef
    have hS : (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i))) = 0 := by
      have hh := hcurl a
      unfold FiniteTimeSingularity.vorticity at hh
      rw [← WithLp.toLp_zero] at hh
      exact WithLp.toLp_injective 2 hh
    have heq : ∀ k : Fin 3,
        (∑ i, (FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i))) k) = 0 := by
      intro k
      have hk := congrFun hS k
      rwa [Finset.sum_apply, Pi.zero_apply] at hk
    have h0 : (L (FiniteTimeSingularity.e 1)) 2 = (L (FiniteTimeSingularity.e 2)) 1 := by
      have hk := heq 0
      simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero] at hk
      simp only [FiniteTimeSingularity.e, Pi.single_apply] at hk
      norm_num at hk
      change (L (PiLp.single 2 1 1)).ofLp 2 = (L (PiLp.single 2 2 1)).ofLp 1
      linarith
    have h1 : (L (FiniteTimeSingularity.e 2)) 0 = (L (FiniteTimeSingularity.e 0)) 2 := by
      have hk := heq 1
      simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hk
      simp only [FiniteTimeSingularity.e, Pi.single_apply] at hk
      norm_num at hk
      change (L (PiLp.single 2 2 1)).ofLp 0 = (L (PiLp.single 2 0 1)).ofLp 2
      linarith
    have h2 : (L (FiniteTimeSingularity.e 0)) 1 = (L (FiniteTimeSingularity.e 1)) 0 := by
      have hk := heq 2
      simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_two] at hk
      simp only [FiniteTimeSingularity.e, Pi.single_apply] at hk
      norm_num at hk
      change (L (PiLp.single 2 0 1)).ofLp 1 = (L (PiLp.single 2 1 1)).ofLp 0
      linarith
    have hM : ∀ i j : Fin 3,
        (L (FiniteTimeSingularity.e i)) j = (L (FiniteTimeSingularity.e j)) i := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp_all
    -- Expand an arbitrary vector in the standard orthonormal basis.
    have hxexpand : ∀ u : R3, (∑ i, u i • FiniteTimeSingularity.e i : R3) = u := by
      intro u
      trans (∑ i, ((EuclideanSpace.basisFun (Fin 3) ℝ).repr u).ofLp i
          • (EuclideanSpace.basisFun (Fin 3) ℝ) i : R3)
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]; rfl
      · exact OrthonormalBasis.sum_repr _ u
    have hLsum : ∀ u : R3, L u = ∑ j, u j • L (FiniteTimeSingularity.e j) := by
      intro u
      have h1 : L u = L (∑ i, u i • FiniteTimeSingularity.e i) :=
        congrArg L (hxexpand u).symm
      rw [h1]; simp [map_sum, map_smul]
    have hinner : ∀ u v : R3, inner ℝ u v = ∑ i, v i * u i := by
      intro u v; rw [PiLp.inner_apply]; simp [mul_comm]
    have hcomp : ∀ (c : Fin 3 → ℝ) (i : Fin 3),
        ((∑ j, c j • L (FiniteTimeSingularity.e j) : R3)) i
          = ∑ j, c j * (L (FiniteTimeSingularity.e j)) i := by
      intro c i; simp [Finset.sum_apply, Pi.smul_apply]
    rw [hLsum x, hLsum y]
    simp only [hinner]
    simp only [hcomp]
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM i j]
    ring
  -- The Poincaré lemma for the convex set `ℝ³`.
  obtain ⟨P, hP⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    (𝕜 := ℝ) (E := R3) (F := ℝ) convex_univ isOpen_univ hω hsymm
  refine ⟨P, fun x y => ?_⟩
  rw [(hP x (Set.mem_univ x)).fderiv]
  exact innerSL_apply_apply ℝ (F x) y

end Work.LWP.CurlFree
