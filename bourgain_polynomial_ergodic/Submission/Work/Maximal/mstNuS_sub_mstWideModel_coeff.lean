import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.BourgainPlan.Maximal.mstHat_dilate_eq
import Submission.Work.BourgainPlan.Maximal.mst_prof_err1_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_decay

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal

/-! ## Elementary pieces -/

/-- The character `fourier (-m)` at a real point, in the exponential form of `polyE`. -/
private lemma fourier_neg_coe_polyE (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ) = polyE (-((m : ℝ) * x)) := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  unfold polyE
  congr 1
  push_cast
  ring

/-- `polyE (-(x A)) * polyE (-(B x)) = polyE (-(x (A + B)))`. -/
private lemma polyE_neg_mul_add (x A B : ℝ) :
    polyE (-(x * A)) * polyE (-(B * x)) = polyE (-(x * (A + B))) := by
  rw [polyE_add]
  congr 1
  ring

/-- The pointwise recombination of a difference of two bumps against the character. -/
private lemma polyE_neg_mul_diff (x A B : ℝ) (a b : ℂ) :
    polyE (-(x * A)) * ((a - b) * polyE (-(B * x)))
      = a * polyE (-(x * (B + A))) - b * polyE (-(x * (B + A))) := by
  have hA : polyE (-(x * A)) * polyE (-(B * x)) = polyE (-(x * (B + A))) := by
    rw [polyE_neg_mul_add x A B]
    congr 1
    ring
  rw [show polyE (-(x * A)) * ((a - b) * polyE (-(B * x)))
      = a * (polyE (-(x * A)) * polyE (-(B * x)))
        - b * (polyE (-(x * A)) * polyE (-(B * x))) by ring, hA]

/-- **The inner integral of a dilated bump against a character.**  For `c ≥ 1` and a bump `η`
supported in `[-1/2, 1/2]`,

`∫_{x ∈ (−1/2,1/2)} η (c x) · e(−x T) dx = c⁻¹ · mstHat η (T / c)`.

Immediate from the dilation dictionary `mstHat_dilate_eq`. -/
private lemma inner_integral_polyE {η : ℝ → ℂ} {c : ℝ} (hc1 : 1 ≤ c)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (T : ℝ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * T)))
      = ((c : ℝ) : ℂ)⁻¹ * mstHat η (T / c) := by
  have hcne : c ≠ 0 := by linarith
  have hcne' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcne
  have h := mstHat_dilate_eq η c T hc1 hη2
  have hexp : ∀ u : ℝ, Complex.exp ((((-(2 * Real.pi * (T * u))) : ℝ) : ℂ) * Complex.I)
      = polyE (-(u * T)) := by
    intro u
    unfold polyE
    congr 1
    push_cast
    ring
  rw [show (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * T)))
      = ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
          η (c * u) * Complex.exp ((((-(2 * Real.pi * (T * u))) : ℝ) : ℂ) * Complex.I) from
    intervalIntegral.integral_congr (fun u _ => by rw [hexp u])]
  rw [h, ← mul_assoc, inv_mul_cancel₀ hcne', one_mul]

/-! ## The coefficient identity for a difference of two dilated bumps

The lemma below computes the Fourier coefficient of `star (mstProf P N ·)` times the *difference*
`η (c₁ ·) − η (c₂ ·)` of two dilated bumps, for two unrelated dilations `c₁, c₂ ≥ 1`.  It is the
generalisation of `mstProfBumpS_coeff_identity` (which covers `c = mstScale d χ s ∈ {1} ∪ [2,∞)`
only, through the parametrisation `c = 2^{s(d−χ)}`) needed for the *wide* bump
`mstWideBump P χ η s = η (mstWideC P s ·)`, whose scale `mstWideC P s = (mstQ' s)^{3d}` is not of the
shape `2^{n(d−χ)}`. -/

/-- **The coefficient identity for a difference of two dilated bumps against the polynomial
profile.** -/
theorem mstProf_bumpDiff_coeff_identity (P : Polynomial ℤ) {η : ℝ → ℂ} {M c₁ c₂ : ℝ}
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηm : AEStronglyMeasurable η (volume : Measure ℝ))
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (N : ℕ) (m : ℤ) :
    (∫ ξ : Circ, (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
        * star (fourier m ξ) ∂haarT)
      = ∫ s in (0 : ℝ)..1,
          (((c₁ : ℝ) : ℂ)⁻¹ * mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)
            - ((c₂ : ℝ) : ℂ)⁻¹ * mstHat η
                (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)) := by
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le one_pos hc₁
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le one_pos hc₂
  have hc₁ne : c₁ ≠ 0 := hc₁pos.ne'
  have hc₂ne : c₂ ≠ 0 := hc₂pos.ne'
  have hPac : Continuous (fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s)) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  -- the difference of the two dilated bumps is bounded and a.e. strongly measurable
  have hβbd : ∀ x : ℝ, ‖η (c₁ * x) - η (c₂ * x)‖ ≤ 2 * M := by
    intro x
    calc ‖η (c₁ * x) - η (c₂ * x)‖ ≤ ‖η (c₁ * x)‖ + ‖η (c₂ * x)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hηbd _) (hηbd _)
      _ = 2 * M := by ring
  have hcms : ∀ {c : ℝ}, c ≠ 0 →
      AEStronglyMeasurable (fun x : ℝ => η (c * x)) (volume : Measure ℝ) := by
    intro c hc
    refine hηm.comp_quasiMeasurePreserving ⟨measurable_const_mul c, ?_⟩
    rw [Real.map_volume_mul_left hc]
    intro t ht
    rw [Measure.smul_apply, ht, smul_zero]
  have hβm : AEStronglyMeasurable (fun x : ℝ => η (c₁ * x) - η (c₂ * x)) (volume : Measure ℝ) :=
    (hcms hc₁ne).sub (hcms hc₂ne)
  -- Step 1: the Haar integral is the Fourier coefficient
  have h1 : (∫ ξ : Circ, (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
        * star (fourier m ξ) ∂haarT)
      = fourierCoeff (T := 1)
          (fun ξ : Circ => star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ))) m := by
    rw [fourierCoeff]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)).symm
    rw [fourier_neg, smul_eq_mul, Complex.star_def]
    ring
  -- Step 2: the coefficient as a fundamental-interval integral
  have h2 : fourierCoeff (T := 1)
        (fun ξ : Circ => star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ))) m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          (star (mstProf P N ((x : ℝ) : Circ))
            * (η (c₁ * iwRep ((x : ℝ) : Circ)) - η (c₂ * iwRep ((x : ℝ) : Circ))))
            * polyE (-((m : ℝ) * x)) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) _ m (-(1 / 2))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
    rw [show ((1 : ℝ) / 1) = 1 by norm_num]
    rw [one_smul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x _ => ?_))
    rw [smul_eq_mul, fourier_neg_coe_polyE, mul_comm]
  -- Step 3: the profile and the canonical lift on the fundamental interval
  have h3 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          (star (mstProf P N ((x : ℝ) : Circ))
            * (η (c₁ * iwRep ((x : ℝ) : Circ)) - η (c₂ * iwRep ((x : ℝ) : Circ))))
            * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ((∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))))
            * (η (c₁ * x) - η (c₂ * x))) * polyE (-((m : ℝ) * x)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hrep : iwRep ((x : ℝ) : Circ) = x := iwRep_coe_of_mem hx
    have hprof : star (mstProf P N ((x : ℝ) : Circ))
        = ∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))) := by
      have h : star (mstProf P N ((x : ℝ) : Circ))
          = ∫ s in (0 : ℝ)..1,
              polyE (-(x * Polynomial.eval ((N : ℝ) * s) (toRealPoly P))) := by
        rw [mstProf_apply, hrep, ← starRingEnd_apply, star_polyProfile]
      simpa only using h
    rw [hrep, hprof]
  -- Step 4: Fubini
  have h4 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ((∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))))
            * (η (c₁ * x) - η (c₂ * x))) * polyE (-((m : ℝ) * x)))
      = ∫ s in (0 : ℝ)..1, ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
            * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))) := by
    have hInt : IntegrableOn (Function.uncurry (fun x s : ℝ =>
        polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
          * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x)))))
        (Set.uIoc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) volume := by
      refine IntegrableOn.of_bound ?_ ?_ (2 * M) ?_
      · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
        rw [Measure.prod_prod, Real.volume_uIoc, Real.volume_uIoc]
        norm_num
      · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
          ← Measure.prod_restrict]
        have hm1 : AEStronglyMeasurable
            (fun z : ℝ × ℝ => polyE (-(z.1 * (toRealPoly P).eval ((N : ℝ) * z.2))))
            ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
              (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
          (continuous_polyE.comp ((continuous_fst.mul
            (hPac.comp continuous_snd)).neg)).aestronglyMeasurable
        have hm2 : AEStronglyMeasurable
            (fun z : ℝ × ℝ => η (c₁ * z.1) - η (c₂ * z.1))
            ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
              (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
          (hβm.mono_measure
            (Measure.restrict_le_self (s := Set.uIoc (-(1 / 2) : ℝ) (1 / 2)))).comp_fst
        have hm3 : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-((m : ℝ) * z.1)))
            ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
              (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
          (continuous_polyE.comp ((continuous_const.mul continuous_fst).neg)).aestronglyMeasurable
        exact hm1.mul (hm2.mul hm3)
      · refine Filter.Eventually.of_forall (fun z => ?_)
        simp only [Function.uncurry]
        have hb : ‖polyE (-(z.1 * (toRealPoly P).eval ((N : ℝ) * z.2)))
            * ((η (c₁ * z.1) - η (c₂ * z.1)) * polyE (-((m : ℝ) * z.1)))‖
            = ‖η (c₁ * z.1) - η (c₂ * z.1)‖ := by
          rw [norm_mul, norm_mul, norm_polyE, norm_polyE, one_mul, mul_one]
        rw [hb]
        exact hβbd _
    have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun x s : ℝ =>
        polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
          * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))))
      (a := -(1 / 2)) (b := 1 / 2) (c := 0) (d := 1) hInt
    have hstep1 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ((∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))))
            * (η (c₁ * x) - η (c₂ * x))) * polyE (-((m : ℝ) * x)))
        = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ∫ s in (0 : ℝ)..1,
            polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
              * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [show ((∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))))
              * (η (c₁ * x) - η (c₂ * x))) * polyE (-((m : ℝ) * x))
          = (∫ s in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s))))
              * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))) by ring]
      rw [intervalIntegral.integral_mul_const]
    rw [hstep1, hswap]
  -- Step 5: the inner integral, for each `s`
  have h5 : (∫ s in (0 : ℝ)..1, ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
            * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))))
      = ∫ s in (0 : ℝ)..1,
          (((c₁ : ℝ) : ℂ)⁻¹ * mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)
            - ((c₂ : ℝ) : ℂ)⁻¹ * mstHat η
                (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have hii : ∀ {c : ℝ}, 1 ≤ c → IntervalIntegrable
        (fun x : ℝ => η (c * x) * polyE (-(x * ((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)))))
        volume (-(1 / 2)) (1 / 2) := by
      intro c hc
      rw [intervalIntegrable_iff]
      refine IntegrableOn.of_bound (by rw [Real.volume_uIoc]; norm_num) ?_ M ?_
      · refine AEStronglyMeasurable.mul ?_ ?_
        · exact (hcms (by linarith : c ≠ 0)).mono_measure
            (Measure.restrict_le_self (s := Set.uIoc (-(1 / 2) : ℝ) (1 / 2)))
        · exact (continuous_polyE.comp
            ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [norm_mul, norm_polyE, mul_one]
        exact hηbd _
    have hpt : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * s)))
            * ((η (c₁ * x) - η (c₂ * x)) * polyE (-((m : ℝ) * x))))
        = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            (η (c₁ * x) * polyE (-(x * ((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s))))
              - η (c₂ * x) * polyE (-(x * ((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s))))) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      exact polyE_neg_mul_diff x ((toRealPoly P).eval ((N : ℝ) * s)) (m : ℝ)
        (η (c₁ * x)) (η (c₂ * x))
    rw [hpt, intervalIntegral.integral_sub (hii hc₁) (hii hc₂),
      inner_integral_polyE hc₁ hη2, inner_integral_polyE hc₂ hη2]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-! ## The `ℓ¹` bound for the coefficient sequence of the difference of two dilated bumps -/

/-- **The `ℓ¹` bound.**  Under the standing hypotheses of the coefficient identity — a bump `η`
bounded by `M`, supported in `[-1/2,1/2]` and with `C²` fundamental-domain lift — the total mass of
the Fourier coefficient sequence of `star (mstProf P N ·) · (η (c₁ ·) − η (c₂ ·))` is bounded by a
constant depending only on `η`, `M` and the smoothness of the level-zero bump, *uniformly* in the
profile scale `N` and in the two dilations `c₁, c₂ ≥ 1`.

The proof combines the coefficient identity `mstProf_bumpDiff_coeff_identity` with the uniform
shifted-lattice sampling bound `mstHat_sampling_bound`:
`Σ_m c⁻¹ ‖mstHat η ((m+σ)/c)‖ ≤ K₀` for every `c ≥ 1` and every shift `σ`. -/
theorem mstProf_bumpDiff_coeff_l1 (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (M : ℝ)
    (hM : 0 < M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0))) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ c₁ c₂ : ℝ, 1 ≤ c₁ → 1 ≤ c₂ →
      Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
            * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
            * star (fourier m ξ) ∂haarT‖) ≤ K := by
  have hηm : AEStronglyMeasurable η (volume : Measure ℝ) :=
    aestronglyMeasurable_profEta (d := d) (χ := χ) hη2 hcd0
  have hmh : Continuous fun t : ℝ => mstHat η t :=
    continuous_mstHat (d := d) (χ := χ) hη2 hcd0.continuous
  obtain ⟨E, hE0, hEdec⟩ := mstHat_decay (d := d) (χ := χ) η hcd0
  have hbnd : ∀ t : ℝ, ‖mstHat η t‖ ≤ M := mstHat_bound hM.le hηbd
  obtain ⟨K₀, hK₀pos, hK₀⟩ := mstHat_sampling_bound hM.le hE0 hbnd hEdec
  refine ⟨2 * K₀, by positivity, fun N c₁ c₂ hc₁ hc₂ => ?_⟩
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le one_pos hc₁
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le one_pos hc₂
  have hPac : Continuous fun s : ℝ => (toRealPoly P).eval ((N : ℝ) * s) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  have hnorm₁ : ‖(((c₁ : ℝ) : ℂ))⁻¹‖ = c₁⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₁pos]
  have hnorm₂ : ‖(((c₂ : ℝ) : ℂ))⁻¹‖ = c₂⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₂pos]
  -- the pointwise-in-`m` bound
  have hmaj : ∀ m : ℤ,
      ‖∫ ξ : Circ, (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
          * star (fourier m ξ) ∂haarT‖
        ≤ ∫ s in (0 : ℝ)..1,
            (c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
              + c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖) := by
    intro m
    rw [mstProf_bumpDiff_coeff_identity P hηbd hη2 hηm hc₁ hc₂ N m]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) ?_
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun s _ => ?_)
    · refine Continuous.intervalIntegrable ?_ 0 1
      exact ((((hmh.comp ((continuous_const.add hPac).div_const _)).const_mul _).sub
        ((hmh.comp ((continuous_const.add hPac).div_const _)).const_mul _))).norm
    · refine Continuous.intervalIntegrable ?_ 0 1
      exact (((hmh.comp ((continuous_const.add hPac).div_const _)).norm.const_mul _).add
        ((hmh.comp ((continuous_const.add hPac).div_const _)).norm.const_mul _))
    · calc ‖(((c₁ : ℝ) : ℂ))⁻¹ * mstHat η ((((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁))
              - (((c₂ : ℝ) : ℂ))⁻¹ * mstHat η ((((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂))‖
          ≤ ‖(((c₁ : ℝ) : ℂ))⁻¹ * mstHat η ((((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁))‖
            + ‖(((c₂ : ℝ) : ℂ))⁻¹ * mstHat η ((((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂))‖ :=
            norm_sub_le _ _
        _ = c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
            + c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖ := by
            rw [norm_mul, norm_mul, hnorm₁, hnorm₂]
  have hgcont : ∀ m : ℤ, Continuous fun s : ℝ =>
      c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
        + c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖ := by
    intro m
    exact (((hmh.comp ((continuous_const.add hPac).div_const _)).norm.const_mul _).add
      ((hmh.comp ((continuous_const.add hPac).div_const _)).norm.const_mul _))
  -- the finite-sum bound
  have hfin : ∀ F : Finset ℤ, ∑ m ∈ F,
      ‖∫ ξ : Circ, (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
          * star (fourier m ξ) ∂haarT‖ ≤ 2 * K₀ := by
    intro F
    have hstep : ∑ m ∈ F,
        ‖∫ ξ : Circ, (star (mstProf P N ξ) * (η (c₁ * iwRep ξ) - η (c₂ * iwRep ξ)))
            * star (fourier m ξ) ∂haarT‖
        ≤ ∑ m ∈ F, ∫ s in (0 : ℝ)..1,
            (c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
              + c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖) :=
      Finset.sum_le_sum (fun m _ => hmaj m)
    rw [← intervalIntegral.integral_finsetSum
      (fun m _ => (hgcont m).intervalIntegrable 0 1)] at hstep
    refine le_trans hstep ?_
    calc ∫ s in (0 : ℝ)..1, ∑ m ∈ F,
            (c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
              + c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖)
        ≤ ∫ s in (0 : ℝ)..1, 2 * K₀ := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun s _ => ?_)
          · exact (continuous_finsetSum F (fun m _ => hgcont m)).intervalIntegrable 0 1
          · exact continuous_const.intervalIntegrable 0 1
          · have h1 := hK₀ c₁ ((toRealPoly P).eval ((N : ℝ) * s)) hc₁
            have h2 := hK₀ c₂ ((toRealPoly P).eval ((N : ℝ) * s)) hc₂
            rw [Finset.sum_add_distrib]
            calc ∑ m ∈ F, c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖
                  + ∑ m ∈ F, c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖
                ≤ (∑' m : ℤ, c₁⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₁)‖)
                  + (∑' m : ℤ, c₂⁻¹ * ‖mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * s)) / c₂)‖) :=
                  add_le_add (Summable.sum_le_tsum F (fun m _ => by positivity) h1.1)
                    (Summable.sum_le_tsum F (fun m _ => by positivity) h2.1)
              _ ≤ K₀ + K₀ := add_le_add h1.2 h2.2
              _ = 2 * K₀ := by ring
      _ = 2 * K₀ := by simp
  exact ⟨summable_of_sum_le (fun m => norm_nonneg _) hfin,
    Real.tsum_le_of_sum_le (fun m => norm_nonneg _) hfin⟩

/-! ## The requested lemma -/

theorem mstNuS_sub_mstWideModel_coeff (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (M : ℝ) (hM : 0 < M) (hχd : χ ≤ (d : ℝ)) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta d χ η 0))) :
    ∃ K : ℝ, 0 < K ∧ ∀ N s : ℕ, 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (Work.BourgainPlan.Maximal.mstProf P N ξ) *
            (Work.BourgainPlan.Maximal.mstEta d χ η s ξ -
              Work.Maximal.mstWideBump P χ η s ξ)) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          (star (Work.BourgainPlan.Maximal.mstProf P N ξ) *
            (Work.BourgainPlan.Maximal.mstEta d χ η s ξ -
              Work.Maximal.mstWideBump P χ η s ξ)) * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K := by
  obtain ⟨K, hKpos, hKb⟩ := mstProf_bumpDiff_coeff_l1 P d χ η M hM hηbd hη2 hcd0
  refine ⟨K, hKpos, fun N s _ => ?_⟩
  have hc₁ : 1 ≤ mstScale d χ s := by
    rw [mstScale_apply]
    refine Real.one_le_rpow (by norm_num) ?_
    exact mul_nonneg (Nat.cast_nonneg s) (by linarith)
  have hc₂ : 1 ≤ mstWideC P s := one_le_mstWideC P s
  have h := hKb N (mstScale d χ s) (mstWideC P s) hc₁ hc₂
  have hfun : (fun m : ℤ => ‖∫ ξ : Circ,
        (star (mstProf P N ξ) * (η (mstScale d χ s * iwRep ξ) - η (mstWideC P s * iwRep ξ)))
          * star (fourier m ξ) ∂haarT‖)
      = (fun m : ℤ => ‖∫ ξ : Circ,
        (star (mstProf P N ξ) * (mstEta d χ η s ξ - mstWideBump P χ η s ξ))
          * star (fourier m ξ) ∂haarT‖) := by
    funext m
    simp only [mstEta_apply, mstWideBump_apply, mstScale_apply]
  rw [hfun] at h
  exact h

end

end Work.Maximal
