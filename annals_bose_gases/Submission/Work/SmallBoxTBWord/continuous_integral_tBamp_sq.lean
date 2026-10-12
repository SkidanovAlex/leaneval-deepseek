import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the `p`-diagonal amplitude integral

The windowed exponential amplitude

    tBamp χ p Φ i x = ∫_z χ(z) e^{−i⟪p,z⟫} Φ(x_{i←z}) dz

is an integral over `ℝ³` of a function supported in the compact set `tsupport χ`
(the window is compactly supported).  Writing the integral over that compact set
makes the parameter dependence explicit and continuous: the integrand is jointly
continuous in `(p, x, z)`, and a parametric integral over a *compact* set of a
jointly continuous function is continuous
(`continuous_parametric_integral_of_continuous`).  Composing with `‖·‖²` and
integrating once more over the (compact) ambient box `abox N a` — again by the
compact parametric-integral lemma — gives the stated continuity.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real
open Submission.BoseGases

namespace Work.SmallBoxTBWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `tBamp` is the integral over the *compact* set `tsupport χ` of its (jointly
continuous) integrand, since `χ` vanishes off `tsupport χ`. -/
theorem tBamp_eq_setIntegral_tsupport {N : ℕ} {χ : ℝ³ → ℝ} {Φ : X N → ℝ} (i : Fin N)
    (p : ℝ³) (x : X N) :
    tBamp χ p Φ i x
      = ∫ z in tsupport χ, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (Φ (Function.update x i z) : ℂ) := by
  rw [tBamp]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    simp [image_eq_zero_of_notMem_tsupport hz])).symm

/-- The amplitude `(p, x) ↦ tBamp χ p Φ i x` is jointly continuous. -/
theorem continuous_tBamp_pair {N : ℕ} {χ : ℝ³ → ℝ} (hχ : Continuous χ)
    (hcs : HasCompactSupport χ) {Φ : X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    Continuous (fun q : ℝ³ × X N => tBamp χ q.1 Φ i q.2) := by
  have hcont_int : Continuous (fun q : ℝ³ × X N =>
      ∫ z in tsupport χ, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ)))
        * (Φ (Function.update q.2 i z) : ℂ)) := by
    refine continuous_parametric_integral_of_continuous (μ := volume) ?_ hcs
    rw [show Function.uncurry (fun q : ℝ³ × X N => fun z : ℝ³ =>
        (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ)))
          * (Φ (Function.update q.2 i z) : ℂ))
      = fun r : (ℝ³ × X N) × ℝ³ =>
        (χ r.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ r.1.1 r.2 : ℂ)))
          * (Φ (Function.update r.1.2 i r.2) : ℂ) from by
        funext r; rfl]
    fun_prop
  exact hcont_int.congr (fun q => (tBamp_eq_setIntegral_tsupport i q.1 q.2).symm)

/-- **Continuity of `p ↦ ∫_{abox} ‖tBamp χ p Φ i‖²`.**  The integrand is jointly
continuous in `(p, x)` (`continuous_tBamp_pair`), and `abox N a` is compact, so the
parametric-integral lemma applies. -/
theorem continuous_integral_tBamp_sq {N : ℕ} {a : ℝ} (ha : 0 < a) {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ) (hcs : HasCompactSupport χ) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => ∫ x in Submission.BoseGases.abox N a, ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
  have hF : Continuous (Function.uncurry (fun p : ℝ³ => fun x : X N => ‖tBamp χ p Φ i x‖ ^ 2)) := by
    rw [show Function.uncurry (fun p : ℝ³ => fun x : X N => ‖tBamp χ p Φ i x‖ ^ 2)
      = fun r : ℝ³ × X N => ‖tBamp χ r.1 Φ i r.2‖ ^ 2 from by funext r; rfl]
    exact (continuous_tBamp_pair hχ hcs hΦ i).norm.pow 2
  exact continuous_parametric_integral_of_continuous (μ := volume) hF (abox_compact N ha)

end Work.SmallBoxTBWord
