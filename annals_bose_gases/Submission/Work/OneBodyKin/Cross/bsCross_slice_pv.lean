import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.CrossDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.Cross.bsCross_slice_pv`

The `(p,v,s)`-slice integrability of the four-fold integrand of the cross term, with the `p`-factor
`bsLf ℓ F p v` frozen:

    `(v,s) ↦ bsLf ℓ F p v · ψ(ℓ(v+u)) · ψ(ℓ(u+s))`  is integrable on
    `volume.prod (volume.restrict (acube 1))`.

This is the Fubini input for the `(v,s)`-exchange in `bsCross_expand_mean`/`bsCross_subst`: the
`u`-integral is frozen at the point `u` (so the `s`-variable ranges over the unit cube only) and
the momentum `p` is a fixed parameter, hence no integrability hypothesis on `F` is needed beyond
the (unused, but statement-faithful) global one.

The proof is pure domination.  By `Work.OneBodyKin.abs_bsLf_le`,

    `|bsLf ℓ F p v| ≤ (∫|χ|)·|F ‖p‖|·|χ v|`,

which is an `L¹` function of `v` because `χ` is continuous with compact support
(`BoseGases.chi_continuous`, `BoseGases.chi_hasCompactSupport`), while `ψ` is bounded
(`Work.OneBodyKin.exists_bound_of_contDiff_hasCompactSupport`).  Hence the integrand is dominated
by the constant `(∫|χ|)·|F ‖p‖|·Cψ²` times `|χ w.1|`, an integrable function on the product by
`Integrable.mul_prod` (the `s`-factor being the constant `1` on the finite measure
`volume.restrict (acube 1)`, `BoseGases.acube_lt_top`).  A.e. strong measurability comes from
continuity of the integrand.  Integrability of `p ↦ F ‖p‖` and positivity of `ℓ` are not needed
for this slice.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Real

namespace Work.OneBodyKin.Cross

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

lemma bsCross_slice_pv {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (u p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.OneBodyKin.bsLf ℓ F p w.1 * ψ (ℓ • (w.1 + u)) * ψ (ℓ • (u + w.2)))
      (MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1))) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  have hχI : MeasureTheory.Integrable (fun v : ℝ³ => |Submission.BoseGases.chi v|) :=
    (Submission.BoseGases.chi_continuous.integrable_of_hasCompactSupport
      Submission.BoseGases.chi_hasCompactSupport).abs
  -- The dominating function: a constant times `|χ w.1|`.
  have hmaj : MeasureTheory.Integrable
      (fun w : ℝ³ × ℝ³ =>
        ((∫ z : ℝ³, |Submission.BoseGases.chi z|) * |F ‖p‖| * Cψ * Cψ) *
          |Submission.BoseGases.chi w.1|)
      (MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1))) := by
    have h1 : MeasureTheory.Integrable
        (fun v : ℝ³ => ((∫ z : ℝ³, |Submission.BoseGases.chi z|) * |F ‖p‖| * Cψ * Cψ) *
          |Submission.BoseGases.chi v|) MeasureTheory.volume := hχI.const_mul _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ³ => (1 : ℝ))
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1)) :=
      MeasureTheory.integrableOn_const
        (ne_of_lt (Submission.BoseGases.acube_lt_top 1 (by norm_num)))
    simpa using h1.mul_prod h2
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · have hψc : Continuous ψ := hψ.continuous
    have hchi : Continuous Submission.BoseGases.chi := Submission.BoseGases.chi_continuous
    have hcont : Continuous (fun w : ℝ³ × ℝ³ =>
        Work.OneBodyKin.bsLf ℓ F p w.1 * ψ (ℓ • (w.1 + u)) * ψ (ℓ • (u + w.2))) := by
      unfold Work.OneBodyKin.bsLf
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with w
    calc ‖Work.OneBodyKin.bsLf ℓ F p w.1 * ψ (ℓ • (w.1 + u)) * ψ (ℓ • (u + w.2))‖
        = |Work.OneBodyKin.bsLf ℓ F p w.1| * |ψ (ℓ • (w.1 + u))| * |ψ (ℓ • (u + w.2))| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ ((∫ z : ℝ³, |Submission.BoseGases.chi z|) * |F ‖p‖| *
            |Submission.BoseGases.chi w.1|) * Cψ * Cψ := by
          gcongr
          · exact Work.OneBodyKin.abs_bsLf_le ℓ F p w.1
          · exact hCψ _
          · exact hCψ _
      _ = ((∫ z : ℝ³, |Submission.BoseGases.chi z|) * |F ‖p‖| * Cψ * Cψ) *
            |Submission.BoseGases.chi w.1| := by ring

end Work.OneBodyKin.Cross
