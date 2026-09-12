import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix

namespace Commons.Probability.RandomMatrix

namespace MeasurableOpNormClm

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev X (n : ℕ) := Fin n → Fin n → ℝ

/-- The continuous-linear-map-valued function on the (plain) matrix space
`X n = Fin n → Fin n → ℝ`, viewed as a linear equivalence. -/
noncomputable def clmEquiv (n : ℕ) : X n ≃ₗ[ℝ] E n →L[ℝ] E n := by
  exact ((LinearEquiv.refl ℝ (X n)).trans (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n))).trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E n) (F' := E n))

/-- The map sending a matrix (as a plain function) to its continuous linear operator
is continuous, since the domain is finite-dimensional. -/
lemma clm_continuous (n : ℕ) : Continuous (clmEquiv n : X n → E n →L[ℝ] E n) := by
  have hfin : FiniteDimensional ℝ (X n) := inferInstance
  have ht2 : T2Space (X n) := inferInstance
  exact (clmEquiv n).toLinearMap.continuous_of_finiteDimensional

/-- The operator norm is continuous in the matrix entries. -/
lemma norm_clm_continuous (n : ℕ) :
    Continuous (fun v : X n => ‖clmEquiv n v‖) := by
  exact continuous_norm.comp (clm_continuous n)

/-- Hence it is measurable w.r.t. the product measurable space on the entries. -/
lemma norm_clm_measurable (n : ℕ) :
    Measurable (fun v : X n => ‖clmEquiv n v‖) :=
  (norm_clm_continuous n).measurable

/-- Unfolding statement for `clmEquiv`. -/
lemma clmEquiv_apply (n : ℕ) (v : X n) :
    clmEquiv n v = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (v : Matrix (Fin n) (Fin n) ℝ)) := by
  rfl

end MeasurableOpNormClm

open MeasurableOpNormClm

theorem measurable_opNorm_clm {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j)) :
    Measurable (fun ω => ‖((B ω).toEuclideanLin).toContinuousLinearMap‖) := by
  let Bx : Ω → X n := fun ω i j => B ω i j
  have hBx : Measurable Bx := by
    dsimp [Bx]
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    change Measurable (fun ω : Ω => B ω i j)
    exact hmeas i j
  have hm : Measurable (fun ω : Ω => ‖clmEquiv n (Bx ω)‖) :=
    (norm_clm_measurable n).comp hBx
  have hEq : (fun ω : Ω => ‖((B ω).toEuclideanLin).toContinuousLinearMap‖)
      = fun ω : Ω => ‖clmEquiv n (Bx ω)‖ := by
    funext ω
    congr 1
  rw [hEq]
  exact hm

end Commons.Probability.RandomMatrix
