import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mstTht_deriv_bounds
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.BourgainPlan.Maximal.mstHat_sampling_bound
import Submission.Work.BourgainPlan.Maximal.mstHat_dilate_eq
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.lattice_shift_inv_sq_bound
import Submission.Work.BourgainPlan.Maximal.fourierCoeff_mstEta

/-!
# Auxiliary lemmas for the per-arc freezing coefficient estimate `mst_lvl_err`

This module collects the *scale-free* analytic lemmas that the per-arc `l¹` coefficient estimate
(MST §4.4, eq. (99)) is assembled from: the coefficient identity converting the arc coefficient
into an average of samples of `mstHat`, the dilation identity converting the dilated symbol into
`mstFreezeXi`, and the two "size" bounds (supremum and quadratic-decay constant) of the frozen
symbol.

--/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The character `fourier (-m)` at a real point, in the exponential form of `polyE`. -/
private lemma fourier_neg_coe_M (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ) = polyE (-((m : ℝ) * x)) := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  unfold polyE
  congr 1
  push_cast
  ring

/-- **(C) The coefficient identity.**  For a bounded function `Λ` on the real line and a continuous
frequency `Pa`, the `m`-th Fourier coefficient of the circle function
`ξ ↦ (∫_0^1 e(−iwRep ξ · Pa s) ds) · Λ(iwRep ξ)` is the average over `s` of `mstHat Λ` at
`Pa s + m`.  (Fubini on the rectangle `(-1/2,1/2) × (0,1)` plus the definition of `mstHat`.) -/
theorem fourierCoeff_profile_avg {Λ : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hΛ : ∀ x : ℝ, ‖Λ x‖ ≤ M)
    (hΛm : AEStronglyMeasurable Λ (volume : Measure ℝ)) {Pa : ℝ → ℝ} (hPac : Continuous Pa)
    (m : ℤ) :
    fourierCoeff (fun ξ : Circ =>
        (∫ s in (0 : ℝ)..1, polyE (-(iwRep ξ * Pa s))) * Λ (iwRep ξ)) m
      = ∫ s in (0 : ℝ)..1, mstHat Λ (Pa s + (m : ℝ)) := by
  set F : Circ → ℂ := fun ξ =>
    (∫ s in (0 : ℝ)..1, polyE (-(iwRep ξ * Pa s))) * Λ (iwRep ξ) with hF
  have hA : fourierCoeff F m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), F (x : Circ) * polyE (-((m : ℝ) * x)) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) F m (-(1 / 2))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
    rw [show ((1 : ℝ) / 1) = 1 by norm_num]
    rw [one_smul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x _ => ?_))
    rw [smul_eq_mul, fourier_neg_coe_M, mul_comm]
  rw [hA]
  have hB : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), F (x : Circ) * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * Λ x) * polyE (-((m : ℝ) * x)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hx' : x ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hx
    have hrep : iwRep ((x : ℝ) : Circ) = x := by
      have h : AddCircle.liftIoc (1 : ℝ) (-(1 / 2)) (fun y : ℝ => y) ((x : ℝ) : Circ) = x :=
        AddCircle.liftIoc_coe_apply hx'
      simpa only [iwRep, AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply] using h
    simp only [hF, hrep]
  rw [hB]
  have hstep1 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * Λ x) * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ∫ s in (0 : ℝ)..1,
          polyE (-(x * Pa s)) * (Λ x * polyE (-((m : ℝ) * x))) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * Λ x) * polyE (-((m : ℝ) * x))
          = (∫ s in (0 : ℝ)..1, polyE (-(x * Pa s)))
              * (Λ x * polyE (-((m : ℝ) * x))) by ring]
    rw [intervalIntegral.integral_mul_const]
  have hInt : IntegrableOn (Function.uncurry (fun x s : ℝ =>
      polyE (-(x * Pa s)) * (Λ x * polyE (-((m : ℝ) * x)))))
      (Set.uIoc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) volume := by
    refine IntegrableOn.of_bound ?_ ?_ M ?_
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
      rw [Measure.prod_prod, Real.volume_uIoc, Real.volume_uIoc]
      norm_num
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
        ← Measure.prod_restrict]
      have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-(z.1 * Pa z.2)))
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (continuous_polyE.comp
          ((continuous_fst.mul (hPac.comp continuous_snd)).neg)).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => Λ z.1)
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (hΛm.mono_measure (Measure.restrict_le_self (s := Set.uIoc (-(1 / 2) : ℝ) (1 / 2)))).comp_fst
      have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-((m : ℝ) * z.1)))
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (continuous_polyE.comp ((continuous_const.mul continuous_fst).neg)).aestronglyMeasurable
      exact h1.mul (h2.mul h3)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry]
      have hb : ‖polyE (-(z.1 * Pa z.2)) * (Λ z.1 * polyE (-((m : ℝ) * z.1)))‖ = ‖Λ z.1‖ := by
        rw [norm_mul, norm_mul, norm_polyE, norm_polyE, one_mul, mul_one]
      rw [hb]
      exact hΛ _
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun x s : ℝ => polyE (-(x * Pa s)) * (Λ x * polyE (-((m : ℝ) * x))))
    (a := -(1 / 2)) (b := 1 / 2) (c := 0) (d := 1) hInt
  rw [hstep1, hswap]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have hinner : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        polyE (-(x * Pa s)) * (Λ x * polyE (-((m : ℝ) * x))))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), Λ x * polyE (-(x * (Pa s + (m : ℝ)))) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show polyE (-(x * Pa s)) * (Λ x * polyE (-((m : ℝ) * x)))
          = Λ x * (polyE (-(x * Pa s)) * polyE (-((m : ℝ) * x))) by ring]
    rw [polyE_add]
    congr 2
    ring
  rw [hinner, mstHat_apply]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [polyE]
  congr 1
  push_cast
  ring


end

end Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- **The dilation dictionary of the freezing estimate.**  The transform of the dilated symbol
`x ↦ Ξ (c x)` is the transform of `Ξ` at the rescaled frequency `t / c`, divided by `c`. -/
theorem mstHat_comp_mul_eq (P : Polynomial ℤ) (J : ℕ) (β : Circ) (c : ℝ) (hc : 1 ≤ c)
    (η : ℝ → ℂ) (hη : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (t : ℝ) :
    mstHat (fun x : ℝ => mstFreezeXi P J β c η (c * x)) t
      = c⁻¹ * mstHat (mstFreezeXi P J β c η) (t / c) := by
  have hcc : c ≠ 0 := by linarith
  have hsupp : ∀ w : ℝ, 1 / 2 < |w| → mstFreezeXi P J β c η w = 0 := by
    intro w hw
    rw [mstFreezeXi_apply, hη w hw, mul_zero]
  have h := mstHat_dilate_eq (mstFreezeXi P J β c η) c t hc hsupp
  have hcast : (((c⁻¹ : ℝ)) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, inv_mul_cancel₀ (by exact_mod_cast hcc)]
  have hI : (∫ u in (-(1 / 2))..(1 / 2), mstFreezeXi P J β c η (c * u) *
        Complex.exp ((((-(2 * Real.pi * (t * u))) : ℝ) : ℂ) * Complex.I))
      = ∫ u in (-(1 / 2))..(1 / 2), mstFreezeXi P J β c η (c * u) *
        Complex.exp ((((-(2 * Real.pi * t * u)) : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    congr 1
    push_cast
    ring
  rw [mstHat_apply, ← hI, h, ← mul_assoc, hcast, one_mul]

/-- The same identity for the *undilated* form of the frozen symbol,
`x ↦ mstTht P J β (iwRep β) x · η (c x)`. -/
theorem mstHat_dilated_eq (P : Polynomial ℤ) (J : ℕ) (β : Circ) (c : ℝ) (hc : 1 ≤ c)
    (η : ℝ → ℂ) (hη : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (t : ℝ) :
    mstHat (fun x : ℝ => mstTht P J β (iwRep β) x * η (c * x)) t
      = c⁻¹ * mstHat (mstFreezeXi P J β c η) (t / c) := by
  have hcc : c ≠ 0 := by linarith
  rw [← mstHat_comp_mul_eq P J β c hc η hη t]
  congr 1
  funext x
  rw [mstFreezeXi_apply]
  have hdiv : c * x / c = x := by field_simp
  rw [hdiv]


/-- **(B) Sharp sampling bound.**  If `‖mstHat Ξ‖ ≤ M` and `‖mstHat Ξ t‖ ≤ E/t²`, then the samples
of `mstHat Ξ` on the lattice `(ℤ+σ)/c` have total mass `≤ 16(M+E)`, uniformly in `c ≥ 1`, `σ`. -/
theorem mstHat_sampling_le {Ξ : ℝ → ℂ} {C M E : ℝ}
    (hClat : ∀ c : ℝ, 1 ≤ c → ∀ σ : ℝ,
      Summable (fun m : ℤ => 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) ∧
        (∑' m : ℤ, 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) ≤ C / c)
    (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hbound : ∀ t : ℝ, ‖mstHat Ξ t‖ ≤ M)
    (hdecay : ∀ t : ℝ, t ≠ 0 → ‖mstHat Ξ t‖ ≤ E / t ^ 2)
    (c σ : ℝ) (hc : 1 ≤ c) :
      Summable (fun m : ℤ => c⁻¹ * ‖mstHat Ξ ((m + σ) / c)‖) ∧
        (∑' m : ℤ, c⁻¹ * ‖mstHat Ξ ((m + σ) / c)‖) ≤ 2 * C * (M + E) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hdom : ∀ m : ℤ, c⁻¹ * ‖mstHat Ξ ((m + σ) / c)‖ ≤
      2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2) := by
    intro m
    refine mstHat_sampling_majorant (M := M) (E := E) (c := c) (u := (m : ℝ) + σ)
      (X := ‖mstHat Ξ (((m : ℝ) + σ) / c)‖) hM hE hc (hbound _) ?_
    intro hu
    have hdec := hdecay (((m : ℝ) + σ) / c) (div_ne_zero hu hcne)
    calc ‖mstHat Ξ (((m : ℝ) + σ) / c)‖ ≤ E / (((m : ℝ) + σ) / c) ^ 2 := hdec
      _ = E * c ^ 2 / ((m : ℝ) + σ) ^ 2 := by field_simp
  have hmaj : Summable (fun m : ℤ => 2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2)) := by
    refine ((hClat c hc σ).1.mul_left (2 * (M + E) * c)).congr (fun m => ?_)
    rw [one_div, div_eq_mul_inv]
  have hFsum : Summable (fun m : ℤ => c⁻¹ * ‖mstHat Ξ ((m + σ) / c)‖) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hdom hmaj
  refine ⟨hFsum, ?_⟩
  calc ∑' m : ℤ, c⁻¹ * ‖mstHat Ξ ((m + σ) / c)‖
      ≤ ∑' m : ℤ, 2 * (M + E) * c / (((m : ℝ) + σ) ^ 2 + c ^ 2) :=
        Summable.tsum_le_tsum hdom hFsum hmaj
    _ = 2 * (M + E) * c * (∑' m : ℤ, 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun m => by rw [one_div, div_eq_mul_inv])
    _ ≤ 2 * (M + E) * c * (C / c) := by
        refine mul_le_mul_of_nonneg_left (hClat c hc σ).2 (by positivity)
    _ = 2 * C * (M + E) := by field_simp


end

end Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The Fourier coefficient kernel of a single arc term.**  For the level-`s` arc set, the arc
`β` and the dyadic scale `2 ^ k`, `arcCoeff P l d χ η J s k β m` is the `m`-th Fourier coefficient
of MST's single-arc error symbol
`ξ ↦ (star (G β) − star (m_J ξ)) · star (Φ_{2^k}(ξ − β)) · η_s(ξ − β)`. -/
abbrev arcCoeff (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (J s k : ℕ) :
    Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ :=
  fun β m => fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      (star (mstG P β) - star (mstWeyl P J ξ))
        * arcTranslate β (fun ζ => star (mstProf P (2 ^ k) ζ) * mstEta d χ η s ζ) ξ) m

end

end Work.BourgainPlan.Maximal
