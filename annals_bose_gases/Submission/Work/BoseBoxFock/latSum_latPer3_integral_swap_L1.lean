import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.pinQBl_eq_boxAvg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latSum_latPer3_integral_swap_L1`

The `L¹`-version of the lattice-sum/integral interchange for the periodisation of `W` tested
against the scaled bump `χ_ℓ`.  This is the statement proved in
`Submission/Work/BoseBoxFock/pinQBl_eq_boxAvg.lean` as `latSum_latPer3_integral_swap`, but with the
hypotheses `AEStronglyMeasurable W` and `∃ C, ∀ x, ‖W x‖ ≤ C` replaced by the single
`MeasureTheory.Integrable W` (and no compact support hypothesis beyond the explicit support bound
`R < ‖x‖ → W x = 0`).

## Proof

The two support hypotheses (`χ_ℓ` carried by the ball of radius `ℓ/2`, `W` carried by the ball of
radius `R`) make every series a **finite** sum: for `R + ‖w‖ + ℓ/2 < ℓ‖latVec m‖` the `m`-th
summand vanishes identically.  So it suffices to apply `tsum_eq_sum` on both sides and
`integral_finsetSum`.

The only place boundedness of `W` was used in the original proof is the derivation of the
integrability of the shifted weight `y ↦ W (w - y + ℓ•latVec m)`, which here is available directly
from `hWi` by the measure-preserving change of variables `y ↦ (w + ℓ•latVec m) - y`; the product
with the bounded window `χ_ℓ` is then integrable by `Integrable.bdd_mul`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The lattice-sum/integral interchange, `L¹` form.**  Both support conditions (`χ_ℓ` in the
ball of radius `ℓ/2`, `W` in the ball of radius `R`) make both series finite sums; the only
integrability input needed is `W ∈ L¹`. -/
lemma latSum_latPer3_integral_swap_L1 {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hW : ∀ x, R < ‖x‖ → W x = 0) (w : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ, ∫ y : EuclideanSpace ℝ (Fin 3),
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
      = ∫ y : EuclideanSpace ℝ (Fin 3), (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- the finite set of lattice points that can contribute
  have hfin : {m : Fin 3 → ℤ | ‖latVec m‖ ≤ (R + ‖w‖ + ℓ / 2) / ℓ}.Finite :=
    finite_setOf_norm_latVec_le _
  set s : Finset (Fin 3 → ℤ) := hfin.toFinset with hs
  have hsmem : ∀ m : Fin 3 → ℤ, m ∈ s ↔ ‖latVec m‖ ≤ (R + ‖w‖ + ℓ / 2) / ℓ := fun m =>
    Set.Finite.mem_toFinset hfin
  have hsbig : ∀ m : Fin 3 → ℤ, m ∉ s → R + ‖w‖ + ℓ / 2 < ℓ * ‖latVec m‖ := by
    intro m hm
    have h2 : (R + ‖w‖ + ℓ / 2) / ℓ < ‖latVec m‖ :=
      lt_of_not_ge (fun h => hm ((hsmem m).mpr h))
    have h3 : R + ‖w‖ + ℓ / 2 < ‖latVec m‖ * ℓ := (div_lt_iff₀ hℓ).mp h2
    linarith
  -- far lattice points contribute nothing, pointwise
  have hfar : ∀ m : Fin 3 → ℤ, m ∉ s → ∀ y : E3,
      (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) = 0 := by
    intro m hm y
    by_cases hχ : Submission.BoseGases.chiScale ℓ y = 0
    · simp [hχ]
    · have hy : ‖y‖ ≤ ℓ / 2 := Submission.BoseGases.chiScale_support_le hℓ hχ
      have hwy : ‖w - y‖ ≤ ‖w‖ + ℓ / 2 := by
        have h := norm_sub_le w y
        linarith
      have hbig := hsbig m hm
      have hnorm : ℓ * ‖latVec m‖ - ‖w - y‖ ≤ ‖(w - y) + ℓ • latVec m‖ := by
        have h := norm_sub_le ((w - y) + ℓ • latVec m) (w - y)
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hℓ.le] at h
        linarith
      have hgt : R < ‖w - y + ℓ • latVec m‖ := by linarith
      simp [hW _ hgt]
  -- the outer series is a finite sum
  have hLsum : (∑' m : Fin 3 → ℤ, ∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ∑ m ∈ s, ∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    refine tsum_eq_sum (s := s) (fun m hm => ?_)
    rw [show (fun y : E3 => (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) = fun _ => 0 from funext (hfar m hm)]
    simp
  -- integrability of `W` and of its complexification (from the hypothesis `hWi`)
  have hWintC : MeasureTheory.Integrable (fun x : E3 => ((W x : ℝ) : ℂ)) := hWi.ofReal
  have hWmeasC : MeasureTheory.AEStronglyMeasurable (fun x : E3 => ((W x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hWi.aestronglyMeasurable
  -- integrability of the shifted weight, from invariance of Lebesgue measure under `y ↦ c - y`
  have hWshift : ∀ m : Fin 3 → ℤ,
      MeasureTheory.Integrable (fun y : E3 => ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) volume := by
    intro m
    have hψmp : MeasureTheory.MeasurePreserving (fun y : E3 => (w + ℓ • latVec m) - y) volume volume :=
      ⟨(continuous_const.sub continuous_id).measurable,
        Measure.map_sub_left_eq_self volume (w + ℓ • latVec m)⟩
    have hcomp : MeasureTheory.Integrable
        ((fun x : E3 => ((W x : ℝ) : ℂ)) ∘ fun y : E3 => (w + ℓ • latVec m) - y) volume :=
      (hψmp.integrable_comp hWmeasC).mpr hWintC
    have heq : ((fun x : E3 => ((W x : ℝ) : ℂ)) ∘ fun y : E3 => (w + ℓ • latVec m) - y)
        = fun y : E3 => ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
      funext y
      simp only [Function.comp_apply]
      rw [show (w + ℓ • latVec m) - y = w - y + ℓ • latVec m by abel]
    rwa [heq] at hcomp
  have hχmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : E3 => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp
      (Submission.BoseGases.chiScale_contDiff hℓne).continuous).aestronglyMeasurable
  have hχbdd : ∀ᵐ y : E3 ∂volume,
      ‖((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)‖ ≤ Submission.BoseGases.chiSup :=
    Filter.Eventually.of_forall (fun y => by
      simpa using Submission.BoseGases.abs_chiScale_le_chiSup ℓ y)
  have hInt : ∀ m : Fin 3 → ℤ, MeasureTheory.Integrable (fun y : E3 =>
      (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) volume :=
    fun m => (hWshift m).bdd_mul hχmeas hχbdd
  -- pointwise the right-hand integrand is the finite sum
  have hpt : ∀ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ∑ m ∈ s, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    intro y
    rw [← tsum_mul_left, tsum_eq_sum (s := s) (fun m hm => hfar m hm y)]
  have hRsum : (∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)))
      = ∑ m ∈ s, ∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [funext hpt]
    exact integral_finsetSum s (fun m _ => hInt m)
  rw [hLsum, hRsum]

end Work.BoseBoxFock
