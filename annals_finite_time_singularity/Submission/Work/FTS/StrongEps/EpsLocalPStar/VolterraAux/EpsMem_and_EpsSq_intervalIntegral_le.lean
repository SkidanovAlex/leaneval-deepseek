/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsMem_and_EpsSq_intervalIntegral_le` — Minkowski for the parametric interval integral

The lemma of this file is the contraction/closedness step of the abstract Volterra–Picard engine
`Work.FTS.StrongEps.EpsLocalPStar.exists_volterra_v3`: the parametric integral
`F z θ = ∫_s∈(0,τ) G s z θ` of a curve of profiles whose weighted `L²`-sizes are *uniformly*
bounded by `B` is again an honest member `EpsMem α` of the weighted space `X`, with size bounded by
`τ · (τ B) = τ²B`.

It is the `epsL2`-version of `EpsSq_integral_le` (`Submission/Work/FTS/StrongEps/EpsLocalPStar/`):
there the hypotheses were *membership* `EpsMem α (g s)` for every `s` plus integrability of
`s ↦ √(EpsSq α (g s))`; here they are only the a.e. *`epsL2`-bound* `epsL2 α (G s) ≤ B` together
with the a.e. strong measurability of the weighted curve `(s,z,θ) ↦ G s z θ · epsW α z θ`.  The
whole bookkeeping is therefore done in the honest `ℝ≥0∞`-valued integral `epsL2` (which has no
junk values), and membership is recovered at the very end from the finiteness of the bound via
`EpsMem_and_EpsSq_le_of_epsL2_le`.

The proof is the classical one: Cauchy–Schwarz in the parameter `s` (with weight `1`, giving the
factor `ν univ = τ`), Tonelli in `(p, s)`, and the a.e. bound.  In `ℝ≥0∞` no integrability side
conditions are needed anywhere, the only inputs being the a.e. strong measurability of the slices
(`AEStronglyMeasurable.prodMk_right`) and of the slice integral (`AEStronglyMeasurable.prod_swap`
composed with `integral_prod_right'`).

`l2_cs`/`ofReal_sq_abs` come from `EpsLocalPStar/EpsSqIntegralAux.lean`.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsSqIntegralAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.style.haveILetI false

namespace Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

set_option maxHeartbeats 1000000

theorem EpsMem_and_EpsSq_intervalIntegral_le {α τ B : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hbd : Filter.Eventually (fun s : ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s) ≤ ENNReal.ofReal B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc 0 τ)))) :
    Work.FTS.StrongEps.EpsMem α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) ≤ τ * (τ * B) := by
  classical
  -- the uncurried weighted curve, in the shape in which `hmeas` is stated
  set X : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2 with hX
  have hmeas' : MeasureTheory.AEStronglyMeasurable X
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := hmeas
  -- the interval integral of a profile is the integral of its weighted slice against
  -- `volume.restrict (uIoc 0 τ)`, the weight being constant in the parameter
  have hint_eq : ∀ p : ℝ × ℝ, (∫ s in (0 : ℝ)..τ, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
    intro p
    rw [intervalIntegral.integral_of_le hτ, Set.uIoc_of_le hτ, hX]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- the parameter measure is finite, of total mass `τ`
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      sub_zero, abs_of_nonneg hτ]
    exact ENNReal.ofReal_lt_top⟩
  have hnu : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ = ENNReal.ofReal τ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      sub_zero, abs_of_nonneg hτ]
  have hnu_ne : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ ≠ ⊤ := by
    rw [hnu]; exact ENNReal.ofReal_ne_top
  -- a.e. strong measurability of the weighted parametric integral
  have hAK : AK2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) := by
    unfold AK2
    refine (hmeas'.prod_swap.integral_prod_right').congr ?_
    filter_upwards with p
    exact (hint_eq p).symm
  -- `epsL2` of the parametric integral, in terms of the `s`-integral of the curve
  have hstep1 : epsL2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ)
      = ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := by
    unfold epsL2
    exact lintegral_congr (fun p => by rw [hint_eq p])
  -- Cauchy–Schwarz in the parameter, pointwise in the profile variable
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        ≤ (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
          * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
    filter_upwards [hmeas'.prodMk_right] with p hp
    have hen : ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))|
        ≤ ∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
      have h := enorm_integral_le_lintegral_enorm
        (μ := MeasureTheory.volume.restrict (Set.uIoc 0 τ)) (fun s => X (s, p))
      simpa [Real.enorm_eq_ofReal_abs] using h
    have hcs := l2_cs (ν := MeasureTheory.volume.restrict (Set.uIoc 0 τ)) (b := fun _ => (1 : ℝ))
      aemeasurable_const (fun _ => one_pos) hp.aemeasurable
    calc ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        = (ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))|)^2 :=
          ofReal_sq_abs _
      _ ≤ (∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2 :=
          pow_le_pow_left₀ bot_le hen 2
      _ ≤ (∫⁻ s, ENNReal.ofReal (X (s, p)^2 / 1) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * (∫⁻ s, ENNReal.ofReal (1 : ℝ) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))) := hcs
      _ = (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          simp only [div_one, ENNReal.ofReal_one, lintegral_one]
  -- joint measurability for Tonelli
  have hjoint : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal ((X (q.2, q.1))^2))
      ((Work.FTS.StrongEps.EpsLocalPStar.DomM).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 τ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hmeas'.prod_swap.aemeasurable).pow_const 2)
  -- the chain: Cauchy–Schwarz, Tonelli, the a.e. bound, and the arithmetic
  have hchain : ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM ≤ ENNReal.ofReal (τ * (τ * B)) := by
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal ((X (s, p))^2)
              ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          rw [MeasureTheory.lintegral_mul_const' _ _ hnu_ne]
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal ((X (s, p))^2) ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
            ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          rw [MeasureTheory.lintegral_lintegral_swap hjoint]
      _ = (∫⁻ s, epsL2 α (G s) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          congr 1
      _ ≤ (∫⁻ s, ENNReal.ofReal B ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) :=
          mul_le_mul_of_nonneg_right (lintegral_mono_ae hbd) bot_le
      _ = ENNReal.ofReal (τ * (τ * B)) := by
          rw [MeasureTheory.lintegral_const, hnu, ← ENNReal.ofReal_mul hB,
            ← ENNReal.ofReal_mul (mul_nonneg hB hτ)]
          congr 1
          ring
  -- membership and the size bound out of the `epsL2`-bound
  refine EpsMem_and_EpsSq_le_of_epsL2_le (mul_nonneg hτ (mul_nonneg hτ hB)) hAK ?_
  rw [hstep1]
  exact hchain

end Work.FTS.StrongEps.EpsLocalPStar.VolterraAux
