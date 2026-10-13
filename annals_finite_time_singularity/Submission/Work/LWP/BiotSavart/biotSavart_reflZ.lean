/-
# Reflection equivariance of the Biot–Savart operator (`biotSavart_reflZ`)

We prove, directly from the defining integral of `Work.LWP.biotSavart`, that the Biot–Savart
operator commutes with the reflection `σ : x ↦ (x₀, x₁, -x₃)` of `ℝ³` in the plane `x₃ = 0`:

  `biotSavart ω (σ x) = σ (biotSavart ω x)`   for every `ω` with `IsOddVorticity ω`,

i.e. `Work.LWP.Inputs.BiotSavartReflection`, but *unconditionally* (the input of the LWP chapter
asks for it as a hypothesis; here it is a theorem).  Note that on the nose

  `Work.LWP.reflZ x = Work.LWP.flipZ x = WithLp.toLp 2 ![x 0, x 1, - x 2]`,

so the statement reads `biotSavart ω (reflZ x) = flipZ (biotSavart ω x)`.

## The argument

Let `σ` be the reflection, viewed as the linear isometry equivalence
`PiLp 2 (fun _ : Fin 3 => ℝ) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin 3 => ℝ)` that flips the last coordinate
(`reflZEquiv`; its underlying function is `reflZ = flipZ`).  Since `σ` is an involution of `ℝ³`
by orthogonal transformations it preserves Lebesgue measure, so we may substitute `y ↦ σ y` in
the Biot–Savart integral (`MeasureTheory.integral_comp`).  Writing
`bs(ω) x = (4π)⁻¹ • ∫ y, (‖x-y‖³)⁻¹ • (ω y ⨯₃ (x-y))`, this gives

  `bs(ω) (σ x) = (4π)⁻¹ • ∫ y, (‖σ x - σ y‖³)⁻¹ • (ω (σ y) ⨯₃ (σ x - σ y))`.

Now `‖σ x - σ y‖ = ‖x - y‖` (`σ` is an isometry), `ω (σ y) = - σ (ω y)` (this is exactly
`IsOddVorticity`, note `flipZ = σ`), and `σ` acts on the vector arguments of the cross product by
the coordinate flip `flipCoord v = (v₀, v₁, -v₃)`; the elementary identity

  `flipCoord a ⨯₃ flipCoord b = - flipCoord (a ⨯₃ b)`

(determinant `-1` of the reflection) turns the integrand into `σ` applied to the original
integrand.  Finally `σ` commutes with the Bochner integral (`LinearIsometry.integral_comp_comm`,
which is unconditional because a linear isometry is norm preserving) and with the scalar
`(4π)⁻¹`, giving `bs(ω) (σ x) = σ (bs(ω) x)`.

Nothing here needs `ω` to be integrable: if the Biot–Savart integral diverges, both sides of the
identity are the junk value `0`, and the interchange steps above are stated for the Bochner
integral without integrability hypotheses.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.LWP.BiotSavart

/-! ## The reflection as a linear isometry equivalence of `ℝ³` -/

/-- The coordinate flip `v ↦ (v₀, v₁, -v₃)` as a linear isometry equivalence of `ℝ`, applied to
the `i`-th coordinate. -/
private noncomputable def coordFlip (i : Fin 3) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i = 2 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- **The reflection `σ : x ↦ (x₀, x₁, -x₃)` of `ℝ³`, as a linear isometry equivalence.**  Its
underlying function is `Work.LWP.reflZ = Work.LWP.flipZ`. -/
private noncomputable def reflZEquiv : R3 ≃ₗᵢ[ℝ] R3 :=
  LinearIsometryEquiv.piLpCongrRight 2 coordFlip

/-- The action of `reflZEquiv` on coordinates, as a self-map of `Fin 3 → ℝ`. -/
private noncomputable def flipCoord : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v i => coordFlip i (v i)

private lemma reflZEquiv_toLp (v : Fin 3 → ℝ) :
    reflZEquiv (WithLp.toLp 2 v) = WithLp.toLp 2 (flipCoord v) := rfl

private lemma ofLp_reflZEquiv (x : R3) : (reflZEquiv x).ofLp = flipCoord x.ofLp := by
  rw [← WithLp.toLp_ofLp 2 x, reflZEquiv_toLp]

private lemma reflZEquiv_eq_reflZ (x : R3) : reflZEquiv x = reflZ x := by
  rw [← WithLp.toLp_ofLp 2 x, reflZEquiv_toLp]
  congr 1
  funext i
  fin_cases i <;> simp [flipCoord, coordFlip]

private lemma reflZEquiv_eq_flipZ (x : R3) : reflZEquiv x = flipZ x := by
  rw [reflZEquiv_eq_reflZ]; rfl

/-! ## The coordinate flip -/

private lemma flipCoord_smul (c : ℝ) (a : Fin 3 → ℝ) : flipCoord (c • a) = c • flipCoord a := by
  funext i; fin_cases i <;> simp [flipCoord, coordFlip]

private lemma flipCoord_sub (a b : Fin 3 → ℝ) :
    flipCoord (a - b) = flipCoord a - flipCoord b := by
  funext i; fin_cases i <;> (simp [flipCoord, coordFlip] <;> ring)

private lemma flipCoord_cross (a b : Fin 3 → ℝ) :
    flipCoord a ⨯₃ flipCoord b = - flipCoord (a ⨯₃ b) := by
  ext i
  fin_cases i <;> (simp [flipCoord, coordFlip, cross_apply] <;> ring)

private lemma cross_neg_left (a b : Fin 3 → ℝ) : (-a) ⨯₃ b = - (a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-! ## The pointwise identity for the Biot–Savart integrand -/

/-- **The Biot–Savart integrand is equivariant under the reflection.**  For `ω` of parity
`IsOddVorticity` (i.e. `ω (reflZ x) = - flipZ (ω x)`), the integrand of `biotSavart ω` at the
reflected pair `(σ x, σ z)` is the reflection `σ` of the integrand at `(x, z)`. -/
private lemma biotSavart_integrand_reflZ {ω : R3 → R3} (h : IsOddVorticity ω) (x z : R3) :
    WithLp.toLp 2 ((‖reflZEquiv x - reflZEquiv z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z)))
      = reflZEquiv (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖reflZEquiv x - reflZEquiv z‖ = ‖x - z‖ := by
    rw [← LinearIsometryEquiv.map_sub]
    exact reflZEquiv.norm_map (x - z)
  have hz : ω (reflZEquiv z) = - reflZEquiv (ω z) := by
    rw [reflZEquiv_eq_reflZ, reflZEquiv_eq_flipZ]
    exact h z
  have e1 : (ω (reflZEquiv z)).ofLp = - flipCoord ((ω z).ofLp) := by
    rw [hz, WithLp.ofLp_neg, ofLp_reflZEquiv]
  have e2 : (reflZEquiv x).ofLp - (reflZEquiv z).ofLp = flipCoord (x.ofLp - z.ofLp) := by
    rw [ofLp_reflZEquiv, ofLp_reflZEquiv, ← flipCoord_sub]
  have hkey : ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z))
      = flipCoord ((ω z) ⨯₃ (x - z)) := by
    rw [e1, e2, cross_neg_left, flipCoord_cross, neg_neg]
  rw [h1, hkey, reflZEquiv_toLp, flipCoord_smul]

/-! ## Reflection equivariance of the Biot–Savart operator -/

/-- **`biotSavart` commutes with the reflection `σ = reflZ = flipZ`** for a vorticity of parity
`IsOddVorticity`.  This is the algebraic content of `biotSavart_reflZ`. -/
private lemma biotSavart_reflZEquiv {ω : R3 → R3} (h : IsOddVorticity ω) (x : R3) :
    biotSavart ω (reflZEquiv x) = reflZEquiv (biotSavart ω x) := by
  rw [biotSavart, biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖reflZEquiv x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (reflZEquiv x - z)))
      = ∫ z, WithLp.toLp 2 ((‖reflZEquiv x - reflZEquiv z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (reflZEquiv z)) ⨯₃ (reflZEquiv x - reflZEquiv z))) := by
        exact (MeasureTheory.integral_comp reflZEquiv (fun z => WithLp.toLp 2
          ((‖reflZEquiv x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (reflZEquiv x - z))))).symm
    _ = ∫ z, reflZEquiv (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_reflZ h x z
    _ = reflZEquiv (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm reflZEquiv.toLinearIsometry _

/-- **Reflection equivariance of the Biot–Savart operator**: a vorticity in the parity class
`IsOddVorticity` produces a velocity field `biotSavart ω` that is reflection invariant, i.e.
`biotSavart ω (reflZ x) = flipZ (biotSavart ω x)`.  This is the "odd" clause of the
Lichtenstein–Gunther class at the level of the Biot–Savart map, proved here directly from the
Newtonian-potential form of `biotSavart` (no Schauder input, no integrability of `ω` needed). -/
theorem biotSavart_reflZ {ω : R3 → R3} (h : IsOddVorticity ω) (x : R3) :
    biotSavart ω (reflZ x) = flipZ (biotSavart ω x) := by
  rw [← reflZEquiv_eq_reflZ x, biotSavart_reflZEquiv h x, reflZEquiv_eq_flipZ]

end Work.LWP.BiotSavart
