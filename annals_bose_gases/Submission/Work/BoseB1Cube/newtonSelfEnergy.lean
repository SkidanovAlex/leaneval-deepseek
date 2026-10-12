import ChallengeDeps
import Submission.Work.QDecompSimpler
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.newtonSelfEnergy`

The **Newtonian self-energy identity of `g₀`** — the quantitative heart of the extremal
comparison in `FINDING_cubeMDeltaPortArb_session8.md` §1.4:

    ‖g₀‖²_{H^{-1}}  :=  (4π)⁻¹ ∬ g₀(x)g₀(y)‖x−y‖⁻¹  =  2·∫g₀·ω  =  2·g0w0Mass .

It is an immediate consequence of the on-disk

* `Submission.BoseGases.scattering_newton_double_eq`
  (`∫∫ g(x)g(y)‖x−y‖⁻¹ = 8π∫ g(x)w(x)`, `g = v(1−w)`) — the Tonelli form of the a.e. Newton
  representation `Submission.BoseGases.scattering_newton_representation` (`ω = newtonPotential g₀`);

and it is exactly the input that makes the pairing-deficit comparison
`⟨w̃₁,(Θ_1+Θ_2+κ)^{-1}w̃₁⟩ ≤ C·Ξ·D` (FINDING §1.4) a *quantitative* statement about a fixed `v`
rather than an unknown analytic object.

Nothing here is new mathematics — it is the bookkeeping that puts the on-disk theorem in the shape
the `MΔ`-lane consumes.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology

namespace Work.BoseB1Cube

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The Newtonian self-energy of `g₀` against itself**: `∬ g₀(x)g₀(y)‖x−y‖⁻¹ = 8π·g0w0Mass`.
This is `scattering_newton_double_eq` at the chosen scattering solution `ω = Classical.choose h`. -/
theorem g0_newton_double_eq {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    (∫ x : ℝ³, ∫ y : ℝ³, Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y
        * (‖x - y‖ : ℝ)⁻¹)
      = 8 * Real.pi * Submission.BoseGases.g0w0Mass h := by
  have hspec := h
  obtain ⟨hrad, hw⟩ := (Classical.choose_spec h)
  have hmain := Submission.BoseGases.scattering_newton_double_eq (v := v)
    (w := Classical.choose h) hR hvrad hv_supp hrad hw
  simpa [Submission.BoseGases.g0, Submission.BoseGases.g0w0Mass] using hmain

/-- **The `H^{-1}`-reading**: `‖g₀‖²_{H^{-1}} = 2·g0w0Mass`, i.e. the Newtonian self-energy of the
scattering numerator `g₀ = v(1−ω)` is exactly twice its `g₀ω`-mass. -/
theorem g0_Hminus1_eq_two_g0w0Mass {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    (4 * Real.pi)⁻¹ * (∫ x : ℝ³, ∫ y : ℝ³,
        Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y * (‖x - y‖ : ℝ)⁻¹)
      = 2 * Submission.BoseGases.g0w0Mass h := by
  have hmain := g0_newton_double_eq (v := v) (R := R) hR hvrad hv_supp h
  have hpi : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [hmain]
  field_simp
  ring

/-- **The `g₀ω`-mass is nonnegative** (`g₀ ≥ 0` a.e. and `0 ≤ ω` a.e.). -/
theorem g0w0Mass_nonneg {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    0 ≤ Submission.BoseGases.g0w0Mass h := by
  obtain ⟨hrad, hw⟩ := (Classical.choose_spec h)
  have hb := Submission.BoseGases.scat_gomega_integral_bounds (v := v)
    (w := Classical.choose h) hR hv hvrad hv_supp hrad hw
  simpa [Submission.BoseGases.g0w0Mass, Submission.BoseGases.g0] using hb.1

/-- **The `g₀ω`-mass is at most `∫g₀ = 8π·(a v)`** (`0 ≤ ω ≤ 1` a.e.). -/
theorem g0w0Mass_le_eight_pi_mul_a {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    Submission.BoseGases.g0w0Mass h ≤ 8 * Real.pi * _root_.BoseGases.a v := by
  obtain ⟨hrad, hw⟩ := (Classical.choose_spec h)
  have hb := Submission.BoseGases.scat_gomega_integral_bounds (v := v)
    (w := Classical.choose h) hR hv hvrad hv_supp hrad hw
  have hg : (∫ x : ℝ³, v x * (1 - Classical.choose h x))
      = 8 * Real.pi * _root_.BoseGases.a v :=
    Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h
  have hb2 := hb.2
  rw [hg] at hb2
  simpa [Submission.BoseGases.g0w0Mass, Submission.BoseGases.g0] using hb2

/-- **The self-energy is bounded by `16π·(a v)`**: the extremal comparison needs only that the
Newtonian self-energy of `g₀` is controlled by the scattering length. -/
theorem g0_selfEnergy_le {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (h : Work.UBB.ScatSol v) :
    (4 * Real.pi)⁻¹ * (∫ x : ℝ³, ∫ y : ℝ³,
        Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y * (‖x - y‖ : ℝ)⁻¹)
      ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  rw [g0_Hminus1_eq_two_g0w0Mass (v := v) (R := R) hR hvrad hv_supp h]
  have hle := g0w0Mass_le_eight_pi_mul_a (v := v) (R := R) hR hv hvrad hv_supp h
  linarith

end Work.BoseB1Cube
