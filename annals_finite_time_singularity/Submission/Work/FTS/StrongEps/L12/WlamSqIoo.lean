import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `WlamSqIoo`.
The near-zero part of the squared radial weight: `Wlam s = s/(1+s)² ≤ s` for `s > 0`, hence
`∫_{s ∈ Ioo 0 δ} (Wlam s)² ≤ δ³` (dominate by the constant `δ²` on a set of measure `δ`; the
integral is `0` in the non-integrable case, and `0 ≤ δ³` by the hypothesis). -/
theorem WlamSqIoo (δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ s in Set.Ioo 0 δ, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ δ ^ 3 := by
  -- the interval `(0, δ)` is a null-or-finite measure set, so constants are integrable on it
  have hvol : volume (Set.Ioo 0 δ) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn (fun _ : ℝ => δ ^ 2) (Set.Ioo 0 δ) :=
    integrableOn_const hvol (by simp)
  -- pointwise domination of the integrand by the constant `δ²`
  have hpt : ∀ s ∈ Set.Ioo 0 δ, Work.FTS.GalBasis.cc.Wlam s ^ 2 ≤ δ ^ 2 := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hden : (1 : ℝ) ≤ (1 + s) ^ 2 := by nlinarith [hs0]
    have hWle : Work.FTS.GalBasis.cc.Wlam s ≤ s := by
      rw [Work.FTS.GalBasis.cc.Wlam, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
      nlinarith [hs0, hden]
    have hW0 : 0 ≤ Work.FTS.GalBasis.cc.Wlam s := Work.FTS.GalBasis.cc.Wlam_nonneg hs0
    exact (pow_le_pow_left₀ hW0 hWle 2).trans (pow_le_pow_left₀ hs0 hs.2.le 2)
  have hmono := MeasureTheory.setIntegral_mono_of_nonneg
    (f := fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (g := fun _ : ℝ => δ ^ 2)
    (fun s _ => sq_nonneg _) hpt hint
  -- the integral of the constant is `δ² · vol (0, δ) = δ³`
  have hconst : ∫ s in Set.Ioo 0 δ, δ ^ 2 = δ ^ 3 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hδ), smul_eq_mul]
    ring
  rw [hconst] at hmono
  exact hmono

end Work.FTS.StrongEps.L12
