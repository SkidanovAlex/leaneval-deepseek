/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsSq_intervalIntegral_le_gen` — Minkowski for the parametric interval integral, general
interval `(a, b]`

This is the *general-interval* form of
`Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le` (which treats
`(0, τ]`): the parametric integral `F z θ = ∫_{s∈(a,b]} G s z θ` of a curve of profiles whose
weighted `L²`-sizes `epsL2 α (G s)` are a.e. bounded by `B` is again an honest member `EpsMem α`
of the weighted space, with size bounded by `(b - a) · ((b - a) B)`.

The proof is the sibling's, verbatim, with `0` replaced by `a` and `τ` by `b - a`: Cauchy–Schwarz
in the parameter `s` (with the constant weight `1`, giving the factor `ν univ = b - a`), Tonelli
in `(p, s)`, and the a.e. bound.  Everything is done in `ℝ≥0∞` through `epsL2` (no junk values,
no integrability side conditions), and membership together with the real-valued estimate is
recovered at the end from the finiteness of the bound via `EpsMem_and_EpsSq_le_of_epsL2_le`.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsSqIntegralAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

theorem EpsSq_intervalIntegral_le_gen {α a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hbd : Filter.Eventually (fun s : ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s) ≤ ENNReal.ofReal B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b)))) :
    Work.FTS.StrongEps.EpsMem α (fun z θ => ∫ s in a..b, G s z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => ∫ s in a..b, G s z θ) ≤ (b - a) * ((b - a) * B) := by
  classical
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  -- the uncurried weighted curve, in the shape in which `hmeas` is stated
  set X : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2 with hX
  have hmeas' : MeasureTheory.AEStronglyMeasurable X
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := hmeas
  -- the interval integral of a profile is the integral of its weighted slice against
  -- `volume.restrict (uIoc a b)`, the weight being constant in the parameter
  have hint_eq : ∀ p : ℝ × ℝ, (∫ s in a..b, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    intro p
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab, hX]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- the parameter measure is finite, of total mass `b - a`
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
    exact ENNReal.ofReal_lt_top⟩
  have hnu : (MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ = ENNReal.ofReal (b - a) := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
  have hnu_ne : (MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ ≠ ⊤ := by
    rw [hnu]; exact ENNReal.ofReal_ne_top
  -- a.e. strong measurability of the weighted parametric integral
  have hAK : Work.FTS.StrongEps.EpsLocalPStar.AK2 α (fun z θ => ∫ s in a..b, G s z θ) := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.AK2
    refine (hmeas'.prod_swap.integral_prod_right').congr ?_
    filter_upwards with p
    exact (hint_eq p).symm
  -- `epsL2` of the parametric integral, in terms of the `s`-integral of the curve
  have hstep1 : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (fun z θ => ∫ s in a..b, G s z θ)
      = ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.epsL2
    exact lintegral_congr (fun p => by rw [hint_eq p])
  -- Cauchy–Schwarz in the parameter, pointwise in the profile variable
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        ≤ (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
          * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
    filter_upwards [hmeas'.prodMk_right] with p hp
    have hen : ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))|
        ≤ ∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
      have h := enorm_integral_le_lintegral_enorm
        (μ := MeasureTheory.volume.restrict (Set.uIoc a b)) (fun s => X (s, p))
      simpa [Real.enorm_eq_ofReal_abs] using h
    have hcs := Work.FTS.StrongEps.EpsLocalPStar.l2_cs
      (ν := MeasureTheory.volume.restrict (Set.uIoc a b)) (b := fun _ => (1 : ℝ))
      aemeasurable_const (fun _ => one_pos) hp.aemeasurable
    calc ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        = (ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))|)^2 :=
          Work.FTS.StrongEps.EpsLocalPStar.ofReal_sq_abs _
      _ ≤ (∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2 :=
          pow_le_pow_left₀ bot_le hen 2
      _ ≤ (∫⁻ s, ENNReal.ofReal (X (s, p)^2 / 1) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * (∫⁻ s, ENNReal.ofReal (1 : ℝ) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) := hcs
      _ = (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          simp only [div_one, ENNReal.ofReal_one, lintegral_one]
  -- joint measurability for Tonelli
  have hjoint : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal ((X (q.2, q.1))^2))
      ((Work.FTS.StrongEps.EpsLocalPStar.DomM).prod
        (MeasureTheory.volume.restrict (Set.uIoc a b))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hmeas'.prod_swap.aemeasurable).pow_const 2)
  -- the arithmetic of the final constant (in `ℝ≥0∞`, via `ofReal_mul` on `ℝ`)
  have hBA : ENNReal.ofReal B * (ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a))
      = ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
    rw [← ENNReal.ofReal_mul hba]
    rw [← ENNReal.ofReal_mul hB]
    congr 1
    ring
  -- the chain: Cauchy–Schwarz, Tonelli, the a.e. bound, and the arithmetic
  have hchain : ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM ≤ ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal ((X (s, p))^2)
              ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          rw [MeasureTheory.lintegral_mul_const' _ _ hnu_ne]
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal ((X (s, p))^2) ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
            ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          rw [MeasureTheory.lintegral_lintegral_swap hjoint]
      _ = (∫⁻ s, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s)
            ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          congr 1
      _ ≤ (∫⁻ s, ENNReal.ofReal B ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) :=
          mul_le_mul_of_nonneg_right (lintegral_mono_ae hbd) bot_le
      _ = ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
          rw [MeasureTheory.lintegral_const, hnu, mul_assoc]
          exact hBA
  -- membership and the size bound out of the `epsL2`-bound
  refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_and_EpsSq_le_of_epsL2_le
    (mul_nonneg hba (mul_nonneg hba hB)) hAK ?_
  rw [hstep1]
  exact hchain

end

end Work.FTS.EpsEngine
