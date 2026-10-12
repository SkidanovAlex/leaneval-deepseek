import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `G · w(xᵢ,xⱼ)` over the centred box

`integrableOn_cont_mul_pairComp`: for a continuous `G : X N → ℝ` and a pair kernel
`w : ℝ³ × ℝ³ → ℝ` which is integrable on `acube ℓ ×ˢ acube ℓ`, the function
`x ↦ G x * w (x i, x j)` (`i ≠ j`) is integrable over the centred `N`-particle box
`abox N ℓ`.

The proof is the bounded-factor argument, with the unbounded factor supplied by
`Submission.BoseGases.integrableOn_pair_comp_ae` (the `AeValue` layer, which
handles a merely-integrable kernel through an a.e.-measurable representative and
the measure-preserving double insertion `ins2_flat_mp`).  The cases `N ≤ 1` are
vacuous because there are no distinct `i j : Fin N`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

theorem integrableOn_cont_mul_pairComp {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {G : Submission.BoseGases.X N → ℝ} (hG : Continuous G)
    {w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : MeasureTheory.IntegrableOn w
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => G x * w (x i, x j))
      (Submission.BoseGases.abox N ℓ) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
      cases n with
      | zero =>
          have hij' : i = j := by
            refine Fin.ext ?_
            have hi := i.isLt
            have hj := j.isLt
            omega
          exact absurd hij' hij
      | succ p =>
          have hwcomp : IntegrableOn (fun x : Submission.BoseGases.X (p + 2) => w (x i, x j))
              (Submission.BoseGases.abox (p + 2) ℓ) volume :=
            Submission.BoseGases.integrableOn_pair_comp_ae (p := p) hℓ i j hij hw
          obtain ⟨B, hB⟩ :=
            (Submission.BoseGases.abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
              (s := Submission.BoseGases.abox (p + 2) ℓ) (f := G) hG.continuousOn
          have hwabs : Integrable (fun x : Submission.BoseGases.X (p + 2) => |w (x i, x j)|)
              (volume.restrict (Submission.BoseGases.abox (p + 2) ℓ)) := by
            have h := hwcomp.abs
            simpa [Real.norm_eq_abs] using h
          have hbnd : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (p + 2) ℓ)),
              ‖G x * w (x i, x j)‖ ≤ B * |w (x i, x j)| := by
            rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (p + 2) ℓ)]
            apply ae_of_all
            intro x hx
            have hle : |G x| ≤ B := by
              have hb' := hB x hx
              simpa [Real.norm_eq_abs] using hb'
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          have hmeas : AEStronglyMeasurable
              (fun x : Submission.BoseGases.X (p + 2) => G x * w (x i, x j))
              (volume.restrict (Submission.BoseGases.abox (p + 2) ℓ)) :=
            hG.measurable.aestronglyMeasurable.mul hwcomp.aestronglyMeasurable
          exact Integrable.mono' (hwabs.const_mul B) hmeas hbnd

end Work.BoseFixB1S
