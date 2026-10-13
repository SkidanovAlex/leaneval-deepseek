/-
# Rotation equivariance of the Biot–Savart operator

We prove, directly from the Newtonian-potential form of `Work.LWP.biotSavart`, that the
Biot–Savart operator commutes with the rotations `rotLE φ` about the `x₃`-axis: for every
vorticity `ω` that is *equivariant* under `rotLE φ` (i.e. `ω (rotLE φ x) = rotLE φ (ω x)`,
which is exactly the axisymmetry of `ω` on each orbit of the rotation group),

  `biotSavart ω (rotLE φ x) = rotLE φ (biotSavart ω x)`.

## The argument

Let `R = rotLE φ`, viewed as the linear isometry equivalence of `ℝ³` given by the coordinate
rotation `rotCoord φ` (this is `Work.ConstructionInstance.rotLE`, and its coordinate action is
the `rfl`-lemma `rotLE_apply`).  Since `R` is an orthogonal transformation it preserves Lebesgue
measure, so we may substitute `y ↦ R y` in the Biot–Savart integral
(`MeasureTheory.integral_comp`).  Writing

  `bs(ω) x = (4π)⁻¹ • ∫ y, (‖x-y‖³)⁻¹ • (ω y ⨯₃ (x-y))`,

this gives

  `bs(ω) (R x) = (4π)⁻¹ • ∫ y, (‖R x - R y‖³)⁻¹ • (ω (R y) ⨯₃ (R x - R y))`.

Now `‖R x - R y‖ = ‖x - y‖` (`R` is an isometry), `ω (R y) = R (ω y)` (the equivariance
hypothesis), and `R` is *linear*, so `R x - R y = R (x - y)` and the cross product is natural:
`rotCoord_cross` (`R a ⨯₃ R b = R (a ⨯₃ b)`) — the rotation has determinant `+1`, so unlike the
reflection of `Work.LWP.BiotSavart.biotSavart_reflZ` there is no sign.  Hence the substituted
integrand is `R` applied to the original integrand, and `R` commutes with the Bochner integral
(`LinearIsometry.integral_comp_comm`) and with the scalar `(4π)⁻¹`, giving the identity.

Nothing here needs `ω` to be integrable: if the Biot–Savart integral diverges, both sides are the
junk value `0`, and the interchange steps above are stated for the Bochner integral without
integrability hypotheses.
-/
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

/-! ## Two elementary rewrites for `rotLE` and `rotCoord` -/

/-- The coordinate form of `rotLE φ` on a vector written in coordinates: `rotLE` acts by
`rotCoord φ`. -/
lemma rotLE_toLp (φ : ℝ) (v : Fin 3 → ℝ) :
    rotLE φ (WithLp.toLp 2 v) = WithLp.toLp 2 (rotCoord φ v) := by
  rw [rotLE_apply, WithLp.ofLp_toLp]

/-- `rotCoord φ` is additive for differences as well: it is the coordinate action of the linear
map `rotLE φ` (see `rotCoord_add`, `rotCoord_smul`). -/
lemma rotLE_rotCoord_sub (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ (a - b) = rotCoord φ a - rotCoord φ b := by
  have h := map_sub (rotLE φ) (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  rw [← WithLp.toLp_sub, rotLE_toLp] at h
  rw [← WithLp.toLp_sub, rotLE_toLp, rotLE_toLp] at h
  exact WithLp.toLp_injective 2 h

/-- **The rotation is natural for the cross product** (the rotation has determinant `+1`, so
there is no sign; this is the coordinate identity `rotCoord_cross` transported through
`WithLp.toLp`). -/
lemma rotLE_cross (φ : ℝ) (a b : R3) :
    rotLE φ a ⨯₃ rotLE φ b = rotCoord φ (a.ofLp ⨯₃ b.ofLp) := by
  rw [rotLE_ofLp, rotLE_ofLp, ← rotCoord_cross]

/-! ## The pointwise identity for the Biot–Savart integrand -/

/-- **The Biot–Savart integrand is equivariant under the rotation.**  For `ω` equivariant under
`rotLE φ`, the integrand of `biotSavart ω` at the rotated pair `(R x, R z)` is `R` applied to the
integrand at `(x, z)`. -/
lemma biotSavart_integrand_rotLE {ω : R3 → R3}
    (hω : ∀ (φ : ℝ) (x : R3), ω (rotLE φ x) = rotLE φ (ω x)) (φ : ℝ) (x z : R3) :
    WithLp.toLp 2 ((‖rotLE φ x - rotLE φ z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (rotLE φ z)) ⨯₃ (rotLE φ x - rotLE φ z)))
      = rotLE φ (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖rotLE φ x - rotLE φ z‖ = ‖x - z‖ := by
    rw [← map_sub (rotLE φ) x z]
    exact (rotLE φ).norm_map (x - z)
  have hz : ω (rotLE φ z) = rotLE φ (ω z) := hω φ z
  rw [h1, hz]
  simp only [rotLE_ofLp]
  rw [rotLE_toLp]
  congr 1
  rw [rotCoord_smul, ← rotLE_rotCoord_sub, rotCoord_cross]

/-! ## Rotation equivariance of the Biot–Savart operator -/

/-- **`biotSavart` commutes with the rotations `rotLE φ` about the `x₃`-axis** for a vorticity `ω`
that is equivariant under those rotations.  This is the axisymmetry of the Biot–Savart map
(`Work.Cyl.IsAxiNoSwirl` is stated for the *differential* symmetry
`ω = f(radial, axial) • e_θ`; `Work.ConstructionInstance.isAxiNoSwirl_biotSavart` reduces it to
this equivariance through `eTheta_rotLE` and `radial_rotLE`/`axial_rotLE`).

Proved directly from the defining integral, with no Schauder input and no integrability
hypothesis on `ω`. -/
theorem biotSavart_rotLE {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    (hω : ∀ (φ : ℝ) (x : Work.ConstructionInstance.R3),
      ω (Work.ConstructionInstance.rotLE φ x) = Work.ConstructionInstance.rotLE φ (ω x))
    (φ : ℝ) (x : Work.ConstructionInstance.R3) :
    Work.LWP.biotSavart ω (Work.ConstructionInstance.rotLE φ x)
      = Work.ConstructionInstance.rotLE φ (Work.LWP.biotSavart ω x) := by
  rw [Work.LWP.biotSavart, Work.LWP.biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖rotLE φ x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (rotLE φ x - z)))
      = ∫ z, WithLp.toLp 2 ((‖rotLE φ x - rotLE φ z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (rotLE φ z)) ⨯₃ (rotLE φ x - rotLE φ z))) :=
        (MeasureTheory.integral_comp (rotLE φ) (fun z => WithLp.toLp 2
          ((‖rotLE φ x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (rotLE φ x - z))))).symm
    _ = ∫ z, rotLE φ (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_rotLE hω φ x z
    _ = rotLE φ (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm (rotLE φ).toLinearIsometry _

end Work.ConstructionInstance
