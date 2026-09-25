import Mathlib
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.nbrhd_window_count
import Submission.Work.BourgainPlan.Oscillation.nbrhd_sup_shell_l2

/-!
# The multi-frequency neighbourhood maximal at an antitone family of radii

This file proves `NbrhdMaximalLacunary` (the interface
`Work.BourgainPlan.Oscillation.NbrhdMaximalLacunary` of `oscZ_lacunary_defs`) from
`CircleNeighborhoodMaximal` (Bourgain's Lemma 4.1, the maximal estimate for the *dyadic* radii
`2 ^ (-(j+1))` of a periodically separated frequency set).

Given an antitone radius family `ρ : ℕ → ℝ` with `0 < ρ t ≤ 1/2` and the window hypothesis

  `ρ t ≤ 2 ^ (-(j+1))  ⟹  ρ (t + M) ≤ 2 ^ (-(j+2))`

(equivalently: at most `M + 1` radii lie in any dyadic window), the maximal function
`sup_t |∫ unNbhd T (ρ t) · Q · e(-2πix·)|` is `L²`-bounded with constant
`C · (log²(|T|+2) + M + 1)`.

The proof rounds each radius `ρ t` *up* to its dyadic window `2 ^ (-(jt t) - 1)`:
`unNbhd T (ρ t) = unNbhd T (2 ^ (-(jt t) - 1)) - shell_t`, where the *shell*
`shell_t = W T (2 ^ (-(jt t) - 1)) - W T (ρ t)` is the indicator of the part of the window not yet
covered.  Hence

  `sup_t |Â_t Q| ≤ sup_j |D̂_j Q| + sup_t |shell_t Q|`,

where the first term is exactly the hypothesis `CircleNeighborhoodMaximal`, and the second is
handled by the square function: the shells live in the disjoint dyadic annuli, at most `M + 1`
per annulus, so `Σ_t ‖shell_t Q‖²_{L²} ≤ (M+1) ‖Q‖²_{L²}`
(`nbrhd_window_count` + Plancherel, `nbrhd_sup_shell_l2`).
-/

namespace Work.BourgainPlan.Oscillation

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Commons.Analysis.ExponentialSums
open Classical

noncomputable section

/-! ## Elementary helpers -/

private theorem exists_dyadRad_lt (r : ℝ) (hr : 0 < r) : ∃ j : ℕ, (2:ℝ)^(-(j:ℝ)-2) < r := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)).eventually_gt_atTop r⁻¹)
  refine ⟨N, ?_⟩
  have h1 : r⁻¹ < (2:ℝ)^N := hN N le_rfl
  have h2 : (2:ℝ)^(-(N:ℝ)-2) ≤ ((2:ℝ)^N)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    linarith
  have h3 : ((2:ℝ)^N)⁻¹ < r := by
    rw [← one_div, div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^N)]
    have h4 := mul_lt_mul_of_pos_right h1 hr
    rw [inv_mul_cancel₀ (ne_of_gt hr)] at h4
    simpa [mul_comm] using h4
  exact lt_of_le_of_lt h2 h3

private theorem measurable_W (T : Finset (ℝ × ℂ)) (r : ℝ) : Measurable (W T r) := by
  have h : W T r = fun θ => (unNbhd T r θ).re := by
    funext θ; rw [unNbhd_eq_W]; simp
  rw [h]
  exact Complex.measurable_re.comp (measurable_unNbhd T r)

private theorem norm_unNbhd_le_one (T : Finset (ℝ × ℂ)) (r θ : ℝ) : ‖unNbhd T r θ‖ ≤ 1 := by
  rw [unNbhd]; split <;> simp

/-- The shell family: `W` at the rounded dyadic radius minus `W` at the given radius. -/
private def shell (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (jt : ℕ → ℕ) (t : ℕ) (θ : ℝ) : ℝ :=
  W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ

/-- The Fourier coefficient of `m · Q`. -/
private def coeff (m Q : ℝ → ℂ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, m θ * Q θ * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))

private theorem intervalIntegrable_bdd_mul (c Q : ℝ → ℂ) (x : ℤ) (hc : Measurable c)
    (hb : ∀ θ, ‖c θ‖ ≤ 1) (hQ : MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    IntervalIntegrable (fun θ => c θ * Q θ * Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))) volume 0 1 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [IntegrableOn]
  have he : MemLp (fun θ : ℝ => Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))) ⊤
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine MemLp.of_bound (by fun_prop) 1 ?_
    filter_upwards with θ
    rw [Complex.norm_exp]
    have : (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ))).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hc' : MemLp c ⊤ (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)
  have h1 : MemLp (fun θ => c θ * Q θ) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := hc'.mul' hQ
  have h2 : MemLp (fun θ => c θ * Q θ * Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))) 2
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall (fun θ => by ring)) (h1.mul' he)
  exact h2.integrable (by norm_num)

/-! ## The final arithmetic -/

private theorem four_mul_add_le (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 4 * A + 4 * B ≤ D)
    (I : ℝ≥0∞) :
    4 * (ENNReal.ofReal A * I) + 4 * (ENNReal.ofReal B * I) ≤ ENNReal.ofReal D * I := by
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := (ENNReal.ofReal_natCast 4).symm
  have e1 : (4 : ℝ≥0∞) * (ENNReal.ofReal A * I) = ENNReal.ofReal (4 * A) * I := by
    rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  have e2 : (4 : ℝ≥0∞) * (ENNReal.ofReal B * I) = ENNReal.ofReal (4 * B) * I := by
    rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  rw [e1, e2, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hD) (by positivity)

private theorem const_arith_K (C₀ L K : ℝ) (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L) (hK : 1 ≤ K) :
    4 * (C₀ * L) ^ 2 + 4 * K ≤ (2 * (C₀ + 1) * (L + K)) ^ 2 := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hC1 : (1:ℝ) ≤ C₀ + 1 := by linarith
  have hC1sq : (1:ℝ) ≤ (C₀+1)^2 := by nlinarith
  have hKs : K ≤ K^2 := by nlinarith
  have h1 : (C₀*L)^2 ≤ (C₀+1)^2 * L^2 := by nlinarith [sq_nonneg L, sq_nonneg C₀, sq_nonneg (C₀+1), hC₀]
  have h2 : K ≤ (C₀+1)^2 * K^2 := by nlinarith [sq_nonneg K, hKs, hC1sq]
  have h3 : L^2 + K^2 ≤ (L+K)^2 := by nlinarith [mul_nonneg hL hK0]
  have h4 : (2 * (C₀+1) * (L+K))^2 = 4 * ((C₀+1)^2 * (L+K)^2) := by ring
  rw [h4]
  have h5 : 4 * ((C₀+1)^2 * (L^2 + K^2)) ≤ 4 * ((C₀+1)^2 * (L+K)^2) := by
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (C₀+1))
    linarith
  have h6 : 4 * (C₀*L)^2 + 4 * K ≤ 4 * ((C₀+1)^2 * (L^2 + K^2)) := by
    have ha := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
    have hb := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 4)
    linarith
  linarith

private theorem const_arith (C₀ L : ℝ) (M : ℕ) (hC₀ : 0 ≤ C₀) (hL : 0 ≤ L) :
    4 * (C₀ * L) ^ 2 + 4 * ((M:ℝ) + 1) ≤ (2 * (C₀ + 1) * (L + (M:ℝ) + 1)) ^ 2 := by
  have h := const_arith_K C₀ L ((M:ℝ)+1) hC₀ hL (by linarith [show (0:ℝ) ≤ (M:ℝ) from Nat.cast_nonneg M])
  convert h using 2 <;> ring

/-! ## Shell elementary bounds -/

private theorem shell_nonneg (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (jt : ℕ → ℕ)
    (hupper : ∀ t, ρ t ≤ (2:ℝ)^(-(jt t : ℝ)-1)) (t : ℕ) (θ : ℝ) :
    0 ≤ shell T ρ jt t θ := by
  rw [shell]; exact sub_nonneg.mpr (W_mono T (hupper t) θ)

private theorem shell_le_one (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (jt : ℕ → ℕ) (t : ℕ) (θ : ℝ) :
    shell T ρ jt t θ ≤ 1 := by
  rw [shell]; linarith [W_le_one T ((2:ℝ)^(-(jt t : ℝ)-1)) θ, W_nonneg T (ρ t) θ]

private theorem norm_shell_le_one (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (jt : ℕ → ℕ)
    (hupper : ∀ t, ρ t ≤ (2:ℝ)^(-(jt t : ℝ)-1)) (t : ℕ) (θ : ℝ) :
    ‖(shell T ρ jt t θ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (shell_nonneg T ρ jt hupper t θ)]
  exact shell_le_one T ρ jt t θ

/-! ## The main theorem -/

theorem nbrhd_maximal_lacunary (H : Commons.Analysis.ExponentialSums.CircleNeighborhoodMaximal) :
    Work.BourgainPlan.Oscillation.NbrhdMaximalLacunary := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := H
  refine ⟨2 * (C₀ + 1), by linarith, ?_⟩
  intro T ρ M hρpos hρle hanti hwin Q hQ
  set jt : ℕ → ℕ := fun t => Nat.find (exists_dyadRad_lt (ρ t) (hρpos t)) with hjt
  have jth : ∀ t, jt t = Nat.find (exists_dyadRad_lt (ρ t) (hρpos t)) := by
    intro t; rw [hjt]
  have jt_spec : ∀ t, (2:ℝ)^(-(jt t : ℝ)-2) < ρ t := by
    intro t; rw [jth t]; exact Nat.find_spec (exists_dyadRad_lt (ρ t) (hρpos t))
  have jt_min : ∀ t (j : ℕ), (2:ℝ)^(-(j:ℝ)-2) < ρ t → jt t ≤ j := by
    intro t j hj; rw [jth t]; exact Nat.find_min' (exists_dyadRad_lt (ρ t) (hρpos t)) hj
  have jt_notlt : ∀ t (j : ℕ), j < jt t → ¬ ((2:ℝ)^(-(j:ℝ)-2) < ρ t) := by
    intro t j hj; rw [jth t] at hj
    exact Nat.find_min (exists_dyadRad_lt (ρ t) (hρpos t)) hj
  have jt_upper : ∀ t, ρ t ≤ (2:ℝ)^(-(jt t : ℝ)-1) := by
    intro t
    rcases Nat.eq_zero_or_pos (jt t) with h | h
    · have h0 : (2:ℝ)^(-(((0:ℕ)):ℝ)-1) = 1/2 := by norm_num
      rw [h, h0]; exact hρle t
    · have h2 := jt_notlt t (jt t - 1) (by omega)
      have h3 : (((jt t - 1 : ℕ) : ℝ)) = (jt t : ℝ) - 1 := by
        rw [Nat.cast_sub h]; norm_num
      rw [h3] at h2
      have h4 : (2:ℝ)^(-((jt t : ℝ) - 1)-2) = (2:ℝ)^(-(jt t : ℝ)-1) := by
        rw [show -((jt t : ℝ) - 1) - 2 = -(jt t : ℝ) - 1 by ring]
      rw [h4] at h2
      exact not_lt.mp h2
  -- the shell bound
  have hshell : ∫⁻ x : ℤ, (⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((M:ℝ) + 1) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) := by
    have h := nbrhd_sup_shell_l2 ((M:ℝ)+1) (by positivity)
      (fun t θ => shell T ρ jt t θ)
      (fun t => by
        show Measurable (fun θ => W T ((2:ℝ)^(-(jt t : ℝ)-1)) θ - W T (ρ t) θ)
        exact (measurable_W T _).sub (measurable_W T _))
      (fun t θ => shell_nonneg T ρ jt jt_upper t θ)
      (fun θ N => nbrhd_window_count T ρ jt M jt_spec jt_upper hanti hwin θ N) Q hQ
    simpa only [coeff, shell] using h
  -- the dyadic bound
  have hdy : ∫⁻ x : ℤ, (⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C₀ * (Real.log ((T.card:ℝ) + 2))^2)^2)
          * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) := by
    simpa only [coeff] using hC₀ T Q hQ
  -- the pointwise splitting
  have hsplit : ∀ x : ℤ,
      (⨆ t : ℕ, ‖coeff (unNbhd T (ρ t)) Q x‖ₑ)
        ≤ (⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ)
          + (⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) := by
    intro x
    refine iSup_le fun t => ?_
    have hident : coeff (unNbhd T (ρ t)) Q x
        = coeff (unNbhd T ((2:ℝ)^(-(jt t : ℝ)-1))) Q x
          - coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x := by
      show (∫ θ in (0:ℝ)..1, unNbhd T (ρ t) θ * Q θ * _)
          = (∫ θ in (0:ℝ)..1, unNbhd T ((2:ℝ)^(-(jt t : ℝ)-1)) θ * Q θ * _)
            - (∫ θ in (0:ℝ)..1, (shell T ρ jt t θ : ℂ) * Q θ * _)
      rw [← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr (fun θ _ => ?_)
        rw [unNbhd_eq_W, unNbhd_eq_W]
        show (W T (ρ t) θ : ℂ) * Q θ * _ = (W T ((2:ℝ)^(-(jt t:ℝ)-1)) θ : ℂ) * Q θ * _
          - (shell T ρ jt t θ : ℂ) * Q θ * _
        rw [shell]; push_cast; ring
      · exact intervalIntegrable_bdd_mul _ _ x (measurable_unNbhd T _) (norm_unNbhd_le_one T _) hQ
      · exact intervalIntegrable_bdd_mul _ _ x
          (Complex.measurable_ofReal.comp ((measurable_W T _).sub (measurable_W T _)))
          (norm_shell_le_one T ρ jt jt_upper t) hQ
    calc ‖coeff (unNbhd T (ρ t)) Q x‖ₑ
        = ‖coeff (unNbhd T ((2:ℝ)^(-(jt t : ℝ)-1))) Q x
            - coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ := by rw [hident]
      _ ≤ ‖coeff (unNbhd T ((2:ℝ)^(-(jt t : ℝ)-1))) Q x‖ₑ
            + ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ := enorm_sub_le
      _ ≤ (⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ)
            + (⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) :=
          add_le_add (le_iSup (fun j : ℕ => ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ) (jt t))
            (le_iSup (fun t : ℕ => ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) t)
  -- the final chain
  have harith : 4 * (C₀ * (Real.log ((T.card:ℝ) + 2))^2)^2 + 4 * ((M:ℝ) + 1)
      ≤ ((2 * (C₀ + 1)) * ((Real.log ((T.card:ℝ) + 2))^2 + (M:ℝ) + 1))^2 :=
    const_arith C₀ ((Real.log ((T.card:ℝ) + 2))^2) M hC₀pos.le (sq_nonneg _)
  calc ∫⁻ x : ℤ, (⨆ t : ℕ, ‖coeff (unNbhd T (ρ t)) Q x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, ((⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ)
          + (⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ)) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsplit x) (by norm_num : (0:ℝ) ≤ 2))
    _ ≤ ∫⁻ x : ℤ, 4 * (((⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ) ^ (2:ℝ))
          + ((⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) ^ (2:ℝ)))
        ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun x => Lacunary.add_sq_le _ _)
    _ = 4 * (∫⁻ x : ℤ, (⨆ j : ℕ, ‖coeff (unNbhd T ((2:ℝ)^(-(j:ℝ)-1))) Q x‖ₑ) ^ (2:ℝ)
            ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, (⨆ t : ℕ, ‖coeff (fun θ => (shell T ρ jt t θ : ℂ)) Q x‖ₑ) ^ (2:ℝ)
            ∂MeasureTheory.Measure.count) := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_add_left (measurable_of_countable _), mul_add]
    _ ≤ 4 * (ENNReal.ofReal ((C₀ * (Real.log ((T.card:ℝ) + 2))^2)^2)
            * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ))
          + 4 * (ENNReal.ofReal ((M:ℝ) + 1)
            * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hdy (by norm_num)
          · exact mul_le_mul_of_nonneg_left hshell (by norm_num)
    _ ≤ ENNReal.ofReal (((2 * (C₀ + 1)) * ((Real.log ((T.card:ℝ) + 2))^2 + (M:ℝ) + 1))^2)
          * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Q θ‖ₑ ^ (2:ℝ) :=
          four_mul_add_le _ _ _ (sq_nonneg _) (by positivity) harith _

end

end Work.BourgainPlan.Oscillation
