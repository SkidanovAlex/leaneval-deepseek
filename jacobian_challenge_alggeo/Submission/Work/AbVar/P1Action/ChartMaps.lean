/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — chart-level maps and ring identities.

This file collects the ring-theoretic computations underlying the two properties of the scaling
action `scalingAct k : ℙ¹ ⊗ 𝔾_m ⟶ ℙ¹` that are not immediate from the gluing construction:

* the equivariance of the orbit map `gmToP1 : 𝔾_m ⟶ ℙ¹` (`T ↦ [T : 1]`) for the action, and
* the fact that `∞ = [1 : 0]` is a fixed point.

In both cases the geometric statement reduces to an identity of ring maps out of the chart rings
`chartRing k i = Away 𝒜 (Xᵢ)` of `ℙ¹`:

* `psi0 ∘ thetaRing k 0 = psi0 ∘ includeLeft`, where
  `psi0 : chartRing k 0 ⊗[k] k[T;T⁻¹] →ₐ[k] k[T;T⁻¹]` is `a ⊗ b ↦ chartEvalZero a * b`
  (the chart-`D₊(X₀)` coordinate description of the graph of `∞`), and
* `map (chartEvalT) id ∘ thetaRing k 1 = comul ∘ chartEvalT`.

Both are proved by testing against the surjection `polyToAway i (other i) : k[X] → chartRing k i`
and reducing to `Polynomial.aeval` computations.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.Points
import Submission.Work.AbVar.ProjectiveLine.polyToAwaySurjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-- The `k`-algebra map `chartRing k 0 ⊗[k] k[T;T⁻¹] → k[T;T⁻¹]`, `a ⊗ b ↦ chartEvalZero a * b`.
This is the chart-`D₊(X₀)` coordinate description of the graph of the point `∞ = [1 : 0]`. -/
noncomputable def psi0 : srcChartRing k 0 →ₐ[k] L k :=
  Algebra.TensorProduct.lift (R := k) (S := k) (A := chartRing k 0) (B := L k) (C := L k)
    ((Algebra.ofId k (L k)).comp (chartEvalZeroAlgHom k) : chartRing k 0 →ₐ[k] L k)
    (AlgHom.id k (L k)) (fun _ _ => Commute.all _ _)

lemma psi0_tmul (a : chartRing k 0) (b : L k) :
    psi0 k (a ⊗ₜ[k] b) = algebraMap k (L k) (chartEvalZero k a) * b := by
  simp [psi0]

@[simp]
lemma psi0_includeLeft (a : chartRing k 0) :
    psi0 k (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k 0) (B := L k) a)
      = algebraMap k (L k) (chartEvalZero k a) := by
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, psi0_tmul]
  simp

@[simp]
lemma psi0_includeRight (b : L k) :
    psi0 k (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 0) (B := L k) b) = b := by
  rw [Algebra.TensorProduct.includeRight_apply, psi0_tmul]
  simp

lemma psi0_algebraMap (c : k) :
    psi0 k (algebraMap k (srcChartRing k 0) c) = algebraMap k (L k) c := by
  rw [show algebraMap k (srcChartRing k 0) c
        = Algebra.TensorProduct.includeLeftRingHom (R := k) (A := chartRing k 0) (B := L k)
            (algebraMap k (chartRing k 0) c) from rfl,
    psi0_includeLeft, chartEvalZero_algebraMap]

/-- `comulAlgHom` of `T 1` in `k[T;T⁻¹]` is `T 1 ⊗ T 1`: the element `T` is group-like. -/
lemma comulAlgHom_T_one :
    Bialgebra.comulAlgHom k (L k) (LaurentPolynomial.T 1)
      = LaurentPolynomial.T 1 ⊗ₜ[k] LaurentPolynomial.T 1 := by
  have h : Coalgebra.comul (LaurentPolynomial.T (1 : ℤ) : L k)
      = LaurentPolynomial.T (1 : ℤ) ⊗ₜ[k] (LaurentPolynomial.T (1 : ℤ) : L k) := by
    simpa using LaurentPolynomial.comul_C_mul_T_self (R := k) (1 : k) 1
  simpa using h

/-- The `k`-algebra hom `chartEvalT k ⊗ id` sends `X₀/X₁ ⊗ T` to `T ⊗ T`. -/
lemma map_chartEvalT_awayU_tensor_T :
    Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))
        (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k] LaurentPolynomial.T 1)
      = LaurentPolynomial.T 1 ⊗ₜ[k] LaurentPolynomial.T 1 := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, chartEvalTAlgHom_apply, chartEvalT_awayU]

/-- The chart coordinate `X₁/X₀ ⊗ T⁻¹` is killed by `psi0`. -/
lemma psi0_awayU_tensor :
    psi0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k]
        LaurentPolynomial.T (thetaExp 0)) = 0 := by
  rw [psi0_tmul, chartEvalZero_awayU, map_zero, zero_mul]

/-- `thetaRing k i` applied to `polyToAway` is `aeval` at the scaled generator. -/
lemma thetaRing_polyToAway (i : Fin 2) (p : Polynomial k) :
    thetaRing k i (Work.AbVar.ProjectiveLine.polyToAway (R := k) i (other i) p)
      = Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) i (other i) ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp i)) p := by
  rw [thetaRing, RingHom.comp_apply,
    Work.AbVar.ProjectiveLine.awayToPoly_polyToAway (R := k)
      (Work.AbVar.P1Action.other_ne i)]
  rfl

/-- **Ring identity (fixed point).**  The chart-`D₊(X₀)` description of the action of `𝔾_m` on
`ℙ¹` fixes the point `∞ = [1 : 0]`: the ring map `psi0` of the graph of `∞` intertwines the
scaled chart ring map `thetaRing k 0` with the inclusion of the chart ring. -/
theorem psi0_thetaRing_zero (x : chartRing k 0) :
    psi0 k (thetaRing k 0 x) = algebraMap k (L k) (chartEvalZero k x) := by
  obtain ⟨p, rfl⟩ := Work.AbVar.ProjectiveLine.polyToAwaySurjective (R := k) (i := 0) (j := 1)
    (by decide) x
  have hz : thetaRing k 0 (Work.AbVar.ProjectiveLine.polyToAway (R := k) 0 1 p)
      = Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp 0)) p := by
    have h := thetaRing_polyToAway k 0 p
    rwa [other_zero] at h
  calc psi0 k (thetaRing k 0 (Work.AbVar.ProjectiveLine.polyToAway (R := k) 0 1 p))
      = psi0 k (Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp 0)) p) := by rw [hz]
    _ = Polynomial.aeval (psi0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp 0))) p :=
        (Polynomial.aeval_algHom_apply (psi0 k) _ p).symm
    _ = Polynomial.aeval (0 : L k) p := by rw [psi0_awayU_tensor]
    _ = algebraMap k (L k) (Polynomial.eval₂ (RingHom.id k) 0 p) := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.eval_zero_map,
          ← Polynomial.eval₂_id]
    _ = algebraMap k (L k)
          (chartEvalZero k (Work.AbVar.ProjectiveLine.polyToAway (R := k) 0 1 p)) := by
        rw [chartEvalZero_polyToAway]

/-- **Ring identity (equivariance).**  The chart-`D₊(X₁)` description of the action of `𝔾_m` on
`ℙ¹` is compatible with the orbit map `T ↦ [T : 1]` and the group law of `𝔾_m`:
`map (chartEvalT) id ∘ thetaRing k 1 = comul ∘ chartEvalT`. -/
theorem map_thetaRing_one (x : chartRing k 1) :
    Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k)) (thetaRing k 1 x)
      = Bialgebra.comulAlgHom k (L k) (chartEvalT k x) := by
  obtain ⟨p, rfl⟩ := Work.AbVar.ProjectiveLine.polyToAwaySurjective (R := k) (i := 1) (j := 0)
    (by decide) x
  have hz : thetaRing k 1 (Work.AbVar.ProjectiveLine.polyToAway (R := k) 1 0 p)
      = Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k]
          LaurentPolynomial.T (thetaExp 1)) p := by
    have h := thetaRing_polyToAway k 1 p
    rwa [other_one] at h
  have hz1 : Work.AbVar.ProjectiveLine.awayU (R := k) 1 0
        ⊗ₜ[k] (LaurentPolynomial.T (thetaExp 1) : L k)
      = Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k] (LaurentPolynomial.T 1 : L k) := by
    rw [thetaExp_one]
  calc Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))
        (thetaRing k 1 (Work.AbVar.ProjectiveLine.polyToAway (R := k) 1 0 p))
      = Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))
          (Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k]
            LaurentPolynomial.T (thetaExp 1)) p) := by rw [hz]
    _ = Polynomial.aeval (Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))
          (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k]
            LaurentPolynomial.T (thetaExp 1))) p :=
        (Polynomial.aeval_algHom_apply
          (Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k)))
          (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k]
            LaurentPolynomial.T (thetaExp 1)) p).symm
    _ = Polynomial.aeval (Algebra.TensorProduct.map (chartEvalTAlgHom k) (AlgHom.id k (L k))
          (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k] LaurentPolynomial.T 1)) p := by
        rw [hz1]
    _ = Polynomial.aeval (LaurentPolynomial.T 1 ⊗ₜ[k] LaurentPolynomial.T 1) p := by
        rw [map_chartEvalT_awayU_tensor_T]
    _ = Bialgebra.comulAlgHom k (L k) (Polynomial.aeval (LaurentPolynomial.T 1) p) := by
        rw [← Polynomial.aeval_algHom_apply (Bialgebra.comulAlgHom k (L k))
          (LaurentPolynomial.T 1) p, comulAlgHom_T_one]
    _ = Bialgebra.comulAlgHom k (L k)
          (chartEvalT k (Work.AbVar.ProjectiveLine.polyToAway (R := k) 1 0 p)) := by
        rw [chartEvalT_polyToAway]

end

end Work.AbVar.P1Action
