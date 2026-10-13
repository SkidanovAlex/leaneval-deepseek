import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.ConstructionInstance

/-! ## Reflection equivariance of `biotSavart` under the flip `x₁ ↦ -x₁`

The same argument as `Work.LWP.BiotSavart.biotSavart_reflZ`, run with the reflection
`flip1 = (x₀, x₁, x₃) ↦ (x₀, -x₁, x₃)` (as the linear isometry equivalence `flip1LE`).
Every point of the computation is already available: `flip1LE` is an isometry
(`flip1_norm`), the parity hypothesis `ω (flip1 x) = - flip1 (ω x)` says the integrand is
`flip1`-equivariant, and `flip1Coord_cross` (the reflection reverses the cross product,
`det = -1`) supplies the sign change that makes the two cancel. -/

/-- `(-a) ⨯₃ b = -(a ⨯₃ b)` for coordinate vectors of `ℝ³`. -/
private lemma cross_neg_left (a b : Fin 3 → ℝ) : (-a) ⨯₃ b = - (a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- `flip1LE` on a coordinate vector, in coordinates. -/
private lemma flip1LE_toLp (w : Fin 3 → ℝ) :
    flip1LE (WithLp.toLp 2 w) = WithLp.toLp 2 (flip1Coord w) := rfl

/-- `flip1LE` in coordinates, on `ofLp`. -/
private lemma flip1LE_ofLp (x : R3) : (flip1LE x).ofLp = flip1Coord x.ofLp := by
  rw [flip1LE_apply, flip1_ofLp]

/-- **The Biot–Savart integrand is equivariant under the flip `flip1`.**  If
`ω (flip1 x) = - flip1 (ω x)`, then the integrand of `biotSavart ω` at the reflected pair
`(flip1LE x, flip1LE z)` is `flip1LE` applied to the integrand at `(x, z)`. -/
private lemma biotSavart_integrand_flip1 {ω : R3 → R3}
    (h : ∀ x : R3, ω (flip1 x) = - flip1 (ω x)) (x z : R3) :
    WithLp.toLp 2 ((‖flip1LE x - flip1LE z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z)))
      = flip1LE (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖flip1LE x - flip1LE z‖ = ‖x - z‖ := by
    rw [← LinearIsometryEquiv.map_sub]
    exact flip1LE.norm_map (x - z)
  have hz : ω (flip1LE z) = - flip1LE (ω z) := by
    rw [flip1LE_apply]
    exact h z
  have e1 : (ω (flip1LE z)).ofLp = - flip1Coord ((ω z).ofLp) := by
    rw [hz, WithLp.ofLp_neg, flip1LE_ofLp]
  have e2 : (flip1LE x).ofLp - (flip1LE z).ofLp = flip1Coord (x.ofLp - z.ofLp) := by
    rw [flip1LE_ofLp, flip1LE_ofLp, ← flip1Coord_sub]
  have hkey : ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z))
      = flip1Coord ((ω z) ⨯₃ (x - z)) := by
    rw [e1, e2, cross_neg_left, flip1Coord_cross, neg_neg]
  rw [h1, hkey, flip1LE_toLp, flip1Coord_smul]

/-- **`biotSavart` commutes with the linear isometry `flip1LE`** for a vorticity of parity
`ω ∘ flip1 = - flip1 ∘ ω`. -/
private lemma biotSavart_flip1LE {ω : R3 → R3}
    (h : ∀ x : R3, ω (flip1 x) = - flip1 (ω x)) (x : R3) :
    Work.LWP.biotSavart ω (flip1LE x) = flip1LE (Work.LWP.biotSavart ω x) := by
  rw [Work.LWP.biotSavart, Work.LWP.biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖flip1LE x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (flip1LE x - z)))
      = ∫ z, WithLp.toLp 2 ((‖flip1LE x - flip1LE z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z))) := by
        exact (MeasureTheory.integral_comp flip1LE (fun z => WithLp.toLp 2
          ((‖flip1LE x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (flip1LE x - z))))).symm
    _ = ∫ z, flip1LE (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_flip1 h x z
    _ = flip1LE (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm flip1LE.toLinearIsometry _

theorem biotSavart_flip1 {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    (hω : ∀ x : Work.ConstructionInstance.R3,
      ω (Work.ConstructionInstance.flip1 x) = - Work.ConstructionInstance.flip1 (ω x))
    (x : Work.ConstructionInstance.R3) :
    Work.LWP.biotSavart ω (Work.ConstructionInstance.flip1 x)
      = Work.ConstructionInstance.flip1 (Work.LWP.biotSavart ω x) :=
  biotSavart_flip1LE hω x

end Work.ConstructionInstance
