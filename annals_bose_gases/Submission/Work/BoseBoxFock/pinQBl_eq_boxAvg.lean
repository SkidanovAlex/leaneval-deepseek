import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.latPer_bdd_of_norm_le
import Submission.Work.BoseBoxFock.latSum_integral_swap
import Submission.Work.BoseBoxFock.pinQBl_eq_periodisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQBl_eq_boxAvg` — the box-average form of the first `χ̂`-lattice sum

`pinQBl ℓ W w = Σ'_n Ŵ(k_n)·χ̂(ℓ k_n)·e^{i⟪k_n,w⟫}` (`k_n = kmomInt ℓ n`) is the limit of the
`pinQB`-row of the `Q₂` kernel expansion (`Work.BoseBoxFock.pinQBl_eq_periodisation` identifies it
with the periodised windowed convolution `Σ'_m ∫_x W x·χ_ℓ(w + ℓm − x) dx`).  This file proves the
other spelling of the same object, the **box average of the periodisation**

    `pinQBl ℓ W w = (ℓ³)⁻¹ ∫_{acube ℓ} χ_ℓ(y)·latPer3 ℓ W (w − y) dy`,

`latPer3 ℓ W z = ℓ³ Σ'_m W(z + ℓ·latVec m)` (`χ_ℓ = chiScale ℓ = χ(·/ℓ)`, even, supported in the
ball of radius `ℓ/2 ⊆ acube ℓ`).  This is the form `K1lim`'s `χχ`-row is stated in
(`pinQLimDefs.K1lim`), and the box-average twin of `pinQDl_eq_boxAvg`.

## Proof

The periodisation form (already proved) is

    `pinQBl ℓ W w = Σ'_m ∫_x W x·χ_ℓ(w + ℓm − x) dx`.

1. **Translation per lattice point** (`integral_sub_left_eq_self`): replacing `x` by `w + ℓm − x`
   turns each summand into `∫_y χ_ℓ(y)·W(w − y + ℓm) dy`; hence
   `pinQBl ℓ W w = Σ'_m ∫_y χ_ℓ(y)·W(w − y + ℓm) dy`.
2. **Lattice-sum/integral swap** (`latSum_latPer3_integral_swap`): both `χ_ℓ` (continuous,
   supported in the ball of radius `ℓ/2`) and `W` (supported in the ball of radius `R`) make the
   series *finite* — for `‖latVec m‖ > (R + ‖w‖ + ℓ/2)/ℓ` the whole summand vanishes identically —
   so the interchange with the integral is `integral_finsetSum` on that finite set.  (The
   integrability of the shifted weight `y ↦ W(w − y + ℓm)` is obtained from `W ∈ L¹` by the
   measure-preserving affine change of variables `y ↦ (w + ℓm) − y`,
   `Measure.map_sub_left_eq_self`, plus `bdd_mul` against the bounded window.)
3. **Support transfer to the cube** (`integral_eq_acube_integral`): the integrand vanishes outside
   `acube ℓ` because `χ_ℓ` does (`chiScale_mem_acube`), so the full-space integral is the integral
   over `acube ℓ`.
4. **The `ℓ³` bookkeeping**: `latPer3 = ↑(ℓ³)·latPer` and `(ℓ³)⁻¹·↑(ℓ³) = 1`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Support transfer.**  A function vanishing outside the centred cube `acube ℓ` has the same
integral over the whole space as over the cube. -/
lemma integral_eq_acube_integral {ℓ : ℝ} {f : E3 → ℂ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Submission.BoseGases.acube ℓ) :
    (∫ x : E3, f x) = ∫ x in Submission.BoseGases.acube ℓ, f x := by
  have hind : (Submission.BoseGases.acube ℓ).indicator f = f :=
    Set.indicator_eq_self.mpr (fun x hx => hf x hx)
  rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ) (f := f), hind]

/-- **The lattice-sum/integral interchange** for the periodisation of `W` tested against the
scaled bump `χ_ℓ`: the two support conditions (`χ_ℓ` in the ball of radius `ℓ/2`, `W` in the ball
of radius `R`) make both series finite sums. -/
lemma latSum_latPer3_integral_swap {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hW : ∀ x, R < ‖x‖ → W x = 0) (w : E3) :
    (∑' m : Fin 3 → ℤ, ∫ y : E3,
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) := by
  classical
  obtain ⟨C, hC⟩ := hWb
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
  -- `W` is `L¹` (it is bounded, a.e. strongly measurable and carried by the ball of radius `R`)
  have hWcs : HasCompactSupport W := by
    have hsub : Function.support W ⊆ Metric.closedBall (0 : E3) R := by
      intro x hx
      by_contra h
      exact hx (hW x (by
        have : ¬ ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using h
        exact not_le.mp this))
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) R) isClosed_closure
      (closure_minimal hsub Metric.isClosed_closedBall)
  have hWint : MeasureTheory.Integrable W := MeasureTheory.memLp_one_iff_integrable.mp
    (hWcs.memLp_of_bound hWm C (Filter.Eventually.of_forall hC))
  have hWintC : MeasureTheory.Integrable (fun x : E3 => ((W x : ℝ) : ℂ)) := hWint.ofReal
  have hWmeasC : MeasureTheory.AEStronglyMeasurable (fun x : E3 => ((W x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hWm
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

theorem pinQBl_eq_boxAvg {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) (w : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.pinQBl ℓ W w
      = ((ℓ ^ 3)⁻¹ : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (w - y) := by
  classical
  -- (1) translate each summand of the Poisson (periodisation) form
  have htrans : ∀ m : Fin 3 → ℤ,
      (∫ x : E3, ((W x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - x) : ℝ) : ℂ))
        = ∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
            * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    intro m
    have hstep : (∫ y : E3, ((W ((w + ℓ • latVec m) - y) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ
              ((w + ℓ • latVec m) - ((w + ℓ • latVec m) - y)) : ℝ) : ℂ))
        = ∫ x : E3, ((W x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ ((w + ℓ • latVec m) - x) : ℝ) : ℂ) :=
      MeasureTheory.integral_sub_left_eq_self
        (fun x : E3 => ((W x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ ((w + ℓ • latVec m) - x) : ℝ) : ℂ))
        volume (w + ℓ • latVec m)
    rw [← hstep]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [show (w + ℓ • latVec m) - ((w + ℓ • latVec m) - y) = y from sub_sub_cancel _ _,
      show (w + ℓ • latVec m) - y = w - y + ℓ • latVec m by abel, mul_comm]
  have h1 : Work.BoseBoxFock.pinQBl ℓ W w = ∑' m : Fin 3 → ℤ, ∫ y : E3,
      (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [pinQBl_eq_periodisation hℓ hWm hWb hWs hWev w]
    exact tsum_congr htrans
  -- (2) the lattice-sum/integral interchange
  have h2 := latSum_latPer3_integral_swap hℓ hWm hWb hW w
  -- (3) support transfer to the centred cube
  have h3 : (∫ y : E3, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)))
      = ∫ y in Submission.BoseGases.acube ℓ, (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) :=
    integral_eq_acube_integral (fun y hy => by
      have hχ : Submission.BoseGases.chiScale ℓ y ≠ 0 := fun h => hy (by simp [h])
      exact Submission.BoseGases.chiScale_mem_acube hℓ hχ)
  have hmain : Work.BoseBoxFock.pinQBl ℓ W w = ∫ y in Submission.BoseGases.acube ℓ,
      (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) := h1.trans (h2.trans h3)
  -- (4) the `ℓ³` bookkeeping of `latPer3`
  have h3' : ((ℓ ^ 3)⁻¹ : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow, inv_mul_cancel₀]
    exact pow_ne_zero 3 (by exact_mod_cast (ne_of_gt hℓ))
  have hA : (∫ y in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (w - y))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * LatFourier.latPer ℓ W (w - y) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (w - y))
        = ∫ y in Submission.BoseGases.acube ℓ, ((ℓ ^ 3 : ℝ) : ℂ)
            * ((((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * LatFourier.latPer ℓ W (w - y)) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp only [Work.BoseBoxFock.latPer3]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hmain, hA, ← mul_assoc, h3', one_mul]
  simp only [LatFourier.latPer]

end Work.BoseBoxFock
