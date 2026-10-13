/-
# `Work.FTS.ClassC.rgG2_near_bound` — the near-`0` bound on the growing branch `g₂`

The growing indicial branch of the radial Green function is

  `rgG2 α m c z = z^{p} · rgB α m c z`,   `rgB α m c z = ∫_t∈(z,∞) rgF2 α m c t`,
  `rgF2 α m c t = c t · t^{-p-1}`,        `p = rgP α m = 2m/α`.

The lemma below bounds it, uniformly in `α`, `m`, `c`, by the *total mass of the tail
integrand*: for every `z > 0`,

  `|rgG2 α m c z| ≤ (∫_t∈(0,∞) ‖rgF2 α m c t‖) · z^{p}`,

provided the tail integrand is integrable on `(0,∞)`.

The proof is the elementary chain

  `|z^p · ∫_z^∞ f| = z^p · |∫_z^∞ f| ≤ z^p · ∫_z^∞ |f| ≤ z^p · ∫_0^∞ |f|`,

the last inequality being monotonicity of the set integral over `(z,∞) ⊆ (0,∞)` (valid for
`z > 0`).  The hypothesis is only needed to make those integral comparisons legitimate: it
supplies the integrability of `‖rgF2‖` on `(0,∞)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

theorem rgG2_near_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (h2 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      |Work.FTS.EllExist.rgG2 α m c z|
        ≤ (∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖)
          * z ^ (Work.FTS.EllExist.rgP α m) := by
  intro z hz
  -- `z ^ p > 0`
  have hzp : 0 < z ^ (Work.FTS.EllExist.rgP α m) := Real.rpow_pos_of_pos hz _
  -- `(z,∞) ⊆ (0,∞)` as an a.e. inclusion, since `z > 0`
  have hle : Set.Ioi z ≤ᵐ[volume] Set.Ioi 0 :=
    ae_of_all _ (fun x hx => lt_trans hz hx)
  -- the triangle inequality for the Bochner integral
  have hint1 : ‖∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
    norm_integral_le_integral_norm _
  -- monotonicity of the set integral: enlarging `(z,∞)` to `(0,∞)`
  have hint2 : ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
    setIntegral_mono_set h2.norm (ae_of_all _ (fun t => norm_nonneg _)) hle
  calc |Work.FTS.EllExist.rgG2 α m c z|
      = z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z| := by
        rw [Work.FTS.EllExist.rgG2, abs_mul, abs_of_pos hzp]
    _ = z ^ (Work.FTS.EllExist.rgP α m)
          * ‖∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ z ^ (Work.FTS.EllExist.rgP α m)
          * ∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
        mul_le_mul_of_nonneg_left (le_trans hint1 hint2) (le_of_lt hzp)
    _ = (∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖)
          * z ^ (Work.FTS.EllExist.rgP α m) := by ring

end Work.FTS.ClassC
