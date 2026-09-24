import Mathlib
import Submission.Work.GM.Energy.RLocal.Identity
import Submission.Work.GM.S3.Defs

/-!
# The analytic steps of GM Lemma 11.7

This file turns the Fourier identity `Rfun_eq_integral` of `Identity.lean` into the quantitative
statement one wants: `‖R v‖` is controlled by the average of `‖R‖` over a window around `v`.

* `fourierA` is the uniform bound `∫‖ψ‖` for `‖𝓕ψ‖`;
* `fourierTail L` is the mass of `‖𝓕ψ‖` beyond `|ξ| = L`; `fourierTail_bound` shows it is
  `O(L^{-m})`;
* `window_subst` is the change of variables `u = v e^{2πξ/T}` (Jacobian `T/(2πu)`);
* `cutoff_bound` combines the two: `‖R v‖ ≤ A·∫_{-L}^{L}‖R(v e^{2πξ/T})‖ + |W|·tail(L)`.

-/

namespace Work.GM.Energy.RLocal

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Submission.GM (Rfun)

open Work.GM.S3 (Rfun_norm_le_card)

/-- The uniform bound `A = ∫ ‖ψ‖ ≥ ‖𝓕ψ ξ‖` for the Fourier transform of the flat-top bump. -/
noncomputable def fourierA : ℝ := ∫ x, ‖PsiBump x‖

/-- The mass of `‖𝓕ψ‖` on the region `|ξ| > L`. -/
noncomputable def fourierTail (L : ℝ) : ℝ := ∫ ξ : ℝ, if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0

lemma fourierA_nonneg : 0 ≤ fourierA := integral_nonneg fun x => norm_nonneg _

lemma PsiBump_fourier_le_A (ξ : ℝ) : ‖𝓕 PsiBump ξ‖ ≤ fourierA :=
  PsiBump_fourier_le_integral ξ

lemma fourierTail_nonneg (L : ℝ) : 0 ≤ fourierTail L := by
  refine integral_nonneg fun ξ => ?_
  by_cases h : L < |ξ| <;> simp [h]

/-- `Rfun W ·` is continuous on the positive reals. -/
theorem Rfun_continuousOn_pos (W : Finset ℝ) :
    ContinuousOn (fun v : ℝ => Rfun W v) (Set.Ioi 0) := by
  have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Set.Ioi 0) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  have hsum : ContinuousOn
      (fun v : ℝ => ∑ t ∈ W, Complex.exp (Complex.I * ((t * Real.log v : ℝ) : ℂ)))
      (Set.Ioi 0) := by
    refine continuousOn_finsetSum _ (fun t ht => ?_)
    refine Complex.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hlog)
  refine hsum.congr (fun v hv => ?_)
  have h1 := Rfun_mul_exp_eq_sum W zero_lt_one (Real.log v)
  rw [Real.exp_log hv, one_mul] at h1
  simpa using h1

section TailBound

theorem fourierTail_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → fourierTail L ≤ C / L ^ m := by
  obtain ⟨Cd, hCd0, hCd⟩ := PsiBump_fourier_decay (m + 1)
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 1 ≤ m := le_trans (by norm_num) hm
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hma : (-(m : ℝ) - 1) < -1 := by linarith
  -- value of the halfline integral of the comparison function
  have hval : ∀ c : ℝ, 0 < c →
      ∫ t in Set.Ioi c, t ^ (-(m : ℝ) - 1) = 1 / ((m : ℝ) * c ^ m) := by
    intro c hc
    rw [integral_Ioi_rpow_of_lt hma hc]
    rw [show (-(m : ℝ) - 1) + 1 = -(m : ℝ) by ring, Real.rpow_neg hc.le, Real.rpow_natCast]
    field_simp
  -- comparison with the rpow form of the decay
  have hconv : ∀ x : ℝ, 0 < x → Cd / |x| ^ (m + 1) = Cd * x ^ (-(m : ℝ) - 1) := by
    intro x hx
    have hx' : x ^ (m + 1) = x ^ (((m + 1 : ℕ) : ℝ)) := (Real.rpow_natCast x (m + 1)).symm
    rw [abs_of_pos hx, hx', div_eq_mul_inv, ← Real.rpow_neg hx.le]
    rw [show -(((m + 1 : ℕ) : ℝ)) = -(m : ℝ) - 1 by push_cast; ring]
  refine ⟨max 1 (2 * Cd / (m : ℝ)), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLm : (0 : ℝ) < L ^ m := pow_pos hLpos m
  -- splitting `fourierTail L` into the two rays
  have hsplit : fourierTail L
      = (∫ x in Set.Ioi L, ‖𝓕 PsiBump x‖) + (∫ x in Set.Iio (-L), ‖𝓕 PsiBump x‖) := by
    rw [fourierTail]
    have hind : (fun ξ : ℝ => if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0)
        = (Set.Ioi L ∪ Set.Iio (-L)).indicator (fun x => ‖𝓕 PsiBump x‖) := by
      funext ξ
      have hiff : (L < |ξ|) ↔ ξ ∈ (Set.Ioi L ∪ Set.Iio (-L) : Set ℝ) := by
        rw [lt_abs, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by linarith)
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by linarith)
      by_cases h : L < |ξ|
      · rw [if_pos h, Set.indicator_of_mem (hiff.mp h)]
      · rw [if_neg h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hind, integral_indicator (measurableSet_Ioi.union measurableSet_Iio),
      setIntegral_union (Set.disjoint_left.mpr (fun x hx hx' => by
        have : x < -L := Set.mem_Iio.mp hx'
        have : L < x := Set.mem_Ioi.mp hx
        linarith)) measurableSet_Iio
      PsiBump_fourier_integrable.norm.integrableOn PsiBump_fourier_integrable.norm.integrableOn]
  -- the two ray estimates
  have hIoi : (∫ x in Set.Ioi L, ‖𝓕 PsiBump x‖) ≤ Cd * (1 / ((m : ℝ) * L ^ m)) := by
    have hfi : IntegrableOn (fun x : ℝ => ‖𝓕 PsiBump x‖) (Set.Ioi L) :=
      PsiBump_fourier_integrable.norm.integrableOn
    have hfg : IntegrableOn (fun x : ℝ => Cd * x ^ (-(m : ℝ) - 1)) (Set.Ioi L) :=
      (integrableOn_Ioi_rpow_of_lt hma hLpos).const_mul Cd
    calc (∫ x in Set.Ioi L, ‖𝓕 PsiBump x‖)
        ≤ ∫ x in Set.Ioi L, Cd * x ^ (-(m : ℝ) - 1) := by
          refine setIntegral_mono_on hfi hfg measurableSet_Ioi (fun x hx => ?_)
          have hx0 : 0 < x := lt_trans hLpos hx
          calc ‖𝓕 PsiBump x‖ ≤ Cd / |x| ^ (m + 1) := hCd x hx0.ne'
            _ = Cd * x ^ (-(m : ℝ) - 1) := hconv x hx0
      _ = Cd * ∫ x in Set.Ioi L, x ^ (-(m : ℝ) - 1) := integral_const_mul _ _
      _ = Cd * (1 / ((m : ℝ) * L ^ m)) := by rw [hval L hLpos]
  have hIio : (∫ x in Set.Iio (-L), ‖𝓕 PsiBump x‖) ≤ Cd * (1 / ((m : ℝ) * L ^ m)) := by
    have hfi : IntegrableOn (fun x : ℝ => ‖𝓕 PsiBump (-x)‖) (Set.Ioi L) :=
      PsiBump_fourier_integrable.norm.comp_neg.integrableOn
    have hfg : IntegrableOn (fun x : ℝ => Cd * x ^ (-(m : ℝ) - 1)) (Set.Ioi L) :=
      (integrableOn_Ioi_rpow_of_lt hma hLpos).const_mul Cd
    have h1 : (∫ x in Set.Ioi L, ‖𝓕 PsiBump (-x)‖) ≤ Cd * (1 / ((m : ℝ) * L ^ m)) := by
      calc (∫ x in Set.Ioi L, ‖𝓕 PsiBump (-x)‖)
          ≤ ∫ x in Set.Ioi L, Cd * x ^ (-(m : ℝ) - 1) := by
            refine setIntegral_mono_on hfi hfg measurableSet_Ioi (fun x hx => ?_)
            have hx0 : 0 < x := lt_trans hLpos hx
            have hne : -x ≠ 0 := neg_ne_zero.mpr hx0.ne'
            calc ‖𝓕 PsiBump (-x)‖ ≤ Cd / |(-x)| ^ (m + 1) := hCd (-x) hne
              _ = Cd / |x| ^ (m + 1) := by rw [abs_neg]
              _ = Cd * x ^ (-(m : ℝ) - 1) := hconv x hx0
        _ = Cd * ∫ x in Set.Ioi L, x ^ (-(m : ℝ) - 1) := integral_const_mul _ _
        _ = Cd * (1 / ((m : ℝ) * L ^ m)) := by rw [hval L hLpos]
    have h2 : (∫ x in Set.Iic (-L), ‖𝓕 PsiBump x‖) = ∫ x in Set.Ioi L, ‖𝓕 PsiBump (-x)‖ :=
      (integral_comp_neg_Ioi L (fun x => ‖𝓕 PsiBump x‖)).symm
    rw [← integral_Iic_eq_integral_Iio, h2]
    exact h1
  rw [hsplit]
  calc (∫ x in Set.Ioi L, ‖𝓕 PsiBump x‖) + (∫ x in Set.Iio (-L), ‖𝓕 PsiBump x‖)
      ≤ Cd * (1 / ((m : ℝ) * L ^ m)) + Cd * (1 / ((m : ℝ) * L ^ m)) := add_le_add hIoi hIio
    _ = 2 * Cd / (m : ℝ) / L ^ m := by
        field_simp
        ring
    _ ≤ max 1 (2 * Cd / (m : ℝ)) / L ^ m :=
        div_le_div_of_nonneg_right (le_max_right 1 (2 * Cd / (m : ℝ))) (le_of_lt hLm)

end TailBound

section WindowSubst

/-- **The window substitution behind GM Lemma 11.7.**  If the image of `[-L,L]` under
`ξ ↦ v * exp (2πξ/T)` stays inside the window `[a,b]` (which lies in the positive reals), then
`∫_{ξ=-L}^{L} ‖R(v e^{2πξ/T})‖ dξ` is at most `T/(2πa)` times the integral of `‖R‖` over
`[a,b]`.  This is the change of variables `u = v * exp (2πξ/T)`. -/
theorem window_subst (W : Finset ℝ) {v T a b L : ℝ} (hv : 0 < v) (hT : 0 < T) (hL : 0 < L)
    (ha : 0 < a) (hup : v * Real.exp (2 * Real.pi * L / T) ≤ b)
    (hdown : a ≤ v * Real.exp (-(2 * Real.pi * L / T))) :
    (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
      ≤ (T / (2 * Real.pi * a)) * ∫ u in a..b, ‖Rfun W u‖ := by
  have hφpos : ∀ ξ : ℝ, 0 < v * Real.exp (2 * Real.pi * ξ / T) :=
    fun ξ => mul_pos hv (Real.exp_pos _)
  have hderiv : ∀ ξ ∈ Set.Ioo (min (-L) L) (max (-L) L),
      HasDerivAt (fun x : ℝ => v * Real.exp (2 * Real.pi * x / T))
        ((2 * Real.pi / T) * (v * Real.exp (2 * Real.pi * ξ / T))) ξ := by
    intro ξ hx
    have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * x / T) (2 * Real.pi / T) ξ := by
      have h2 : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) ξ := by
        simpa using (hasDerivAt_id ξ).const_mul (2 * Real.pi)
      simpa using h2.div_const T
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (2 * Real.pi * x / T))
        (Real.exp (2 * Real.pi * ξ / T) * (2 * Real.pi / T)) ξ :=
      (Real.hasDerivAt_exp _).comp ξ h1
    have h4 : HasDerivAt (fun x : ℝ => v * Real.exp (2 * Real.pi * x / T))
        (v * (Real.exp (2 * Real.pi * ξ / T) * (2 * Real.pi / T))) ξ :=
      h3.const_mul v
    convert h4 using 1
    ring
  have hnonneg : ∀ ξ ∈ Set.Ioo (min (-L) L) (max (-L) L),
      0 ≤ (2 * Real.pi / T) * (v * Real.exp (2 * Real.pi * ξ / T)) :=
    fun ξ _ => mul_nonneg (div_nonneg (by positivity) hT.le) (le_of_lt (hφpos ξ))
  have hcont : ContinuousOn (fun x : ℝ => v * Real.exp (2 * Real.pi * x / T))
      (Set.uIcc (-L) L) := by fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := -L) (b := L)
      (f := fun x : ℝ => v * Real.exp (2 * Real.pi * x / T))
      (f' := fun ξ : ℝ => (2 * Real.pi / T) * (v * Real.exp (2 * Real.pi * ξ / T)))
      (g := fun u : ℝ => ‖Rfun W u‖ * (T / (2 * Real.pi * u))) hcont hderiv hnonneg
  -- rewrite the lower limit
  have hlimlo : v * Real.exp (2 * Real.pi * (-L) / T) = v * Real.exp (-(2 * Real.pi * L / T)) := by
    rw [show 2 * Real.pi * (-L) / T = -(2 * Real.pi * L / T) by ring]
  have hmain : (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
      = ∫ u in (v * Real.exp (2 * Real.pi * (-L) / T))..(v * Real.exp (2 * Real.pi * L / T)),
          ‖Rfun W u‖ * (T / (2 * Real.pi * u)) := by
    rw [← hsub]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : v * Real.exp (2 * Real.pi * x / T) ≠ 0 := ne_of_gt (hφpos x)
    show ‖Rfun W (v * Real.exp (2 * Real.pi * x / T))‖
      = (fun u : ℝ => ‖Rfun W u‖ * (T / (2 * Real.pi * u)))
          (v * Real.exp (2 * Real.pi * x / T))
          * ((2 * Real.pi / T) * (v * Real.exp (2 * Real.pi * x / T)))
    field_simp
  have hφle : v * Real.exp (2 * Real.pi * (-L) / T) ≤ v * Real.exp (2 * Real.pi * L / T) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hv.le
    apply div_le_div_of_nonneg_right _ hT.le
    nlinarith [Real.pi_pos, hL]
  have hlea : a ≤ v * Real.exp (2 * Real.pi * (-L) / T) := by rw [hlimlo]; exact hdown
  have hpos_of_mem : ∀ x ∈ Set.uIcc (v * Real.exp (2 * Real.pi * (-L) / T))
      (v * Real.exp (2 * Real.pi * L / T)), 0 < x := by
    intro x hx
    have hmin : 0 < min (v * Real.exp (2 * Real.pi * (-L) / T))
        (v * Real.exp (2 * Real.pi * L / T)) := lt_min (hφpos (-L)) (hφpos L)
    rcases Set.mem_uIcc.mp hx with h | h
    · exact lt_of_lt_of_le hmin (le_trans (min_le_left _ _) h.1)
    · exact lt_of_lt_of_le hmin (le_trans (min_le_right _ _) h.1)
  rw [hmain]
  have step1 : (∫ u in (v * Real.exp (2 * Real.pi * (-L) / T))..(v * Real.exp (2 * Real.pi * L / T)),
        ‖Rfun W u‖ * (T / (2 * Real.pi * u)))
      ≤ (T / (2 * Real.pi * a))
        * ∫ u in (v * Real.exp (2 * Real.pi * (-L) / T))..(v * Real.exp (2 * Real.pi * L / T)),
            ‖Rfun W u‖ := by
    have ih1 : IntervalIntegrable (fun u : ℝ => ‖Rfun W u‖ * (T / (2 * Real.pi * u)))
        volume (v * Real.exp (2 * Real.pi * (-L) / T)) (v * Real.exp (2 * Real.pi * L / T)) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.mul ((Rfun_continuousOn_pos W).norm.mono hpos_of_mem) ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => ?_)
      have hx0 : 0 < x := hpos_of_mem x hx
      exact ne_of_gt (mul_pos (mul_pos two_pos Real.pi_pos) hx0)
    have ih2 : IntervalIntegrable (fun u : ℝ => (T / (2 * Real.pi * a)) * ‖Rfun W u‖)
        volume (v * Real.exp (2 * Real.pi * (-L) / T)) (v * Real.exp (2 * Real.pi * L / T)) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.mul continuousOn_const ((Rfun_continuousOn_pos W).norm.mono hpos_of_mem)
    refine (intervalIntegral.integral_mono_on hφle ih1 ih2 (fun u hu => ?_)).trans_eq ?_
    · have hu0 : 0 < u := lt_of_lt_of_le ha (le_trans hlea hu.1)
      have hle : T / (2 * Real.pi * u) ≤ T / (2 * Real.pi * a) :=
        div_le_div_of_nonneg_left hT.le (by positivity)
          (mul_le_mul_of_nonneg_left (le_trans hlea hu.1) (by positivity))
      calc ‖Rfun W u‖ * (T / (2 * Real.pi * u)) ≤ ‖Rfun W u‖ * (T / (2 * Real.pi * a)) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = (T / (2 * Real.pi * a)) * ‖Rfun W u‖ := by ring
    · exact intervalIntegral.integral_const_mul _ _
  refine step1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_interval hlea hφle hup
    (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine (Rfun_continuousOn_pos W).norm.mono ?_
  intro x hx
  have hmin : 0 < min a b := lt_min ha (lt_of_lt_of_le (hφpos L) hup)
  rcases Set.mem_uIcc.mp hx with h | h
  · exact lt_of_lt_of_le hmin (le_trans (min_le_left _ _) h.1)
  · exact lt_of_lt_of_le hmin (le_trans (min_le_right _ _) h.1)

end WindowSubst

section Cutoff

/-- **The cutoff step of GM Lemma 11.7.**  The Fourier identity expresses `R v` as an integral
against `𝓕ψ`; splitting that integral into `|ξ| ≤ L` and `|ξ| > L` and using the uniform bound
`fourierA` for `‖𝓕ψ‖` on the first piece and the trivial bound `‖R‖ ≤ |W|` on the second gives

`‖R v‖ ≤ A · ∫_{-L}^{L} ‖R(v e^{2πξ/T})‖ dξ + |W| · (mass of ‖𝓕ψ‖ beyond |ξ| = L)`. -/
theorem cutoff_bound (T : ℝ) (hT : 0 < T) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) T) {v : ℝ} (hv : 0 < v) {L : ℝ} (hL : 0 < L) :
    ‖Rfun W v‖
      ≤ fourierA * (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
        + (W.card : ℝ) * fourierTail L := by
  have hId : Rfun W v
      = ∫ ξ, Rfun W (v * Real.exp (2 * Real.pi * ξ / T)) * (𝓕 PsiBump) ξ :=
    Rfun_eq_integral T hT W hW hv
  have hf_cont : Continuous fun ξ : ℝ => ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ := by
    have h1 : Continuous fun ξ : ℝ => v * Real.exp (2 * Real.pi * ξ / T) := by fun_prop
    have h2 : Continuous fun ξ : ℝ => Rfun W (v * Real.exp (2 * Real.pi * ξ / T)) :=
      (Rfun_continuousOn_pos W).comp_continuous h1 (fun ξ => mul_pos hv (Real.exp_pos _))
    exact h2.norm
  have hint : Integrable (fun ξ : ℝ =>
      ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖) := by
    refine Integrable.mono' (PsiBump_fourier_integrable.norm.const_mul (W.card : ℝ))
      (hf_cont.aestronglyMeasurable.mul continuous_fourier_PsiBump.norm.aestronglyMeasurable) ?_
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (Rfun_norm_le_card W _) (norm_nonneg _)
  have hstep1 : ‖Rfun W v‖
      ≤ ∫ ξ, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖ := by
    rw [hId]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [norm_mul]
  have hsplit : (∫ ξ, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
      = (∫ ξ in Set.Icc (-L) L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
        + (∫ ξ in (Set.Icc (-L) L)ᶜ,
            ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖) :=
    (integral_add_compl measurableSet_Icc hint).symm
  have hpiece1 : (∫ ξ in Set.Icc (-L) L,
        ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
      ≤ fourierA * (∫ ξ in Set.Icc (-L) L,
          ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖) := by
    have hfi : IntegrableOn (fun ξ : ℝ =>
        ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖) (Set.Icc (-L) L) :=
      hint.integrableOn
    have hgi : IntegrableOn (fun ξ : ℝ =>
        fourierA * ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖) (Set.Icc (-L) L) := by
      refine IntegrableOn.of_bound measure_Icc_lt_top
        ((hf_cont.const_mul fourierA).aestronglyMeasurable.restrict) (fourierA * (W.card : ℝ)) ?_
      filter_upwards with ξ
      rw [Real.norm_of_nonneg (mul_nonneg fourierA_nonneg (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (Rfun_norm_le_card W _) fourierA_nonneg
    calc (∫ ξ in Set.Icc (-L) L,
          ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
        ≤ ∫ ξ in Set.Icc (-L) L,
            fourierA * ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ := by
          refine setIntegral_mono_on hfi hgi measurableSet_Icc (fun ξ hx => ?_)
          calc ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖
              ≤ ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * fourierA :=
                mul_le_mul_of_nonneg_left (PsiBump_fourier_le_A ξ) (norm_nonneg _)
            _ = fourierA * ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ := mul_comm _ _
      _ = fourierA * (∫ ξ in Set.Icc (-L) L,
            ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖) := integral_const_mul _ _
  have hpiece2 : (∫ ξ in (Set.Icc (-L) L)ᶜ,
        ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
      ≤ (W.card : ℝ) * (∫ ξ in (Set.Icc (-L) L)ᶜ, ‖𝓕 PsiBump ξ‖) := by
    have hfi : IntegrableOn (fun ξ : ℝ =>
        ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖) ((Set.Icc (-L) L)ᶜ) :=
      hint.integrableOn
    have hgi : IntegrableOn (fun ξ : ℝ => (W.card : ℝ) * ‖𝓕 PsiBump ξ‖)
        ((Set.Icc (-L) L)ᶜ) :=
      (PsiBump_fourier_integrable.norm.const_mul (W.card : ℝ)).integrableOn
    calc (∫ ξ in (Set.Icc (-L) L)ᶜ,
          ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
        ≤ ∫ ξ in (Set.Icc (-L) L)ᶜ, (W.card : ℝ) * ‖𝓕 PsiBump ξ‖ := by
          refine setIntegral_mono_on hfi hgi measurableSet_Icc.compl (fun ξ hx => ?_)
          exact mul_le_mul_of_nonneg_right (Rfun_norm_le_card W _) (norm_nonneg _)
      _ = (W.card : ℝ) * (∫ ξ in (Set.Icc (-L) L)ᶜ, ‖𝓕 PsiBump ξ‖) := integral_const_mul _ _
  have htail : (∫ ξ in (Set.Icc (-L) L)ᶜ, ‖𝓕 PsiBump ξ‖) = fourierTail L := by
    rw [fourierTail, ← integral_indicator measurableSet_Icc.compl]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hiff : (ξ ∈ (Set.Icc (-L) L)ᶜ) ↔ L < |ξ| := by
      have h1 : (ξ ∈ Set.Icc (-L) L) ↔ |ξ| ≤ L := by rw [Set.mem_Icc, abs_le]
      rw [Set.mem_compl_iff, h1, not_le]
    rw [Set.indicator_apply]
    show (if ξ ∈ (Set.Icc (-L) L)ᶜ then ‖𝓕 PsiBump ξ‖ else 0)
        = (if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0)
    by_cases h : ξ ∈ (Set.Icc (-L) L)ᶜ
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hIcc_eq : (∫ ξ in Set.Icc (-L) L,
        ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
      = ∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  calc ‖Rfun W v‖
      ≤ ∫ ξ, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖ := hstep1
    _ = (∫ ξ in Set.Icc (-L) L,
          ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖)
        + (∫ ξ in (Set.Icc (-L) L)ᶜ,
            ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖ * ‖𝓕 PsiBump ξ‖) := hsplit
    _ ≤ fourierA * (∫ ξ in Set.Icc (-L) L,
          ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
        + (W.card : ℝ) * (∫ ξ in (Set.Icc (-L) L)ᶜ, ‖𝓕 PsiBump ξ‖) :=
        add_le_add hpiece1 hpiece2
    _ = fourierA * (∫ ξ in (-L)..L, ‖Rfun W (v * Real.exp (2 * Real.pi * ξ / T))‖)
        + (W.card : ℝ) * fourierTail L := by rw [hIcc_eq, htail]

end Cutoff

section RegimeSmall

/-- The tail bound in the form needed below: valid for **all** positive `L` (the `L < 1` case
being absorbed into the constant). -/
theorem fourierTail_bound' (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → fourierTail L ≤ C / L ^ m := by
  obtain ⟨Ct, hCt0, hCt⟩ := fourierTail_bound m hm
  set B : ℝ := ∫ ξ : ℝ, ‖𝓕 PsiBump ξ‖ with hBdef
  have hB : 0 ≤ B := integral_nonneg fun ξ => norm_nonneg _
  refine ⟨max (Ct + 1) (B + 1), lt_max_of_lt_left (by linarith), ?_⟩
  intro L hL
  have hLm : 0 < L ^ m := pow_pos hL m
  have htail : fourierTail L ≤ B := by
    rw [fourierTail, hBdef]
    have haesm : AEStronglyMeasurable
        (fun ξ : ℝ => if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0) volume :=
      ((continuous_fourier_PsiBump.norm).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const measurable_abs))
    have hint : Integrable (fun ξ : ℝ => if L < |ξ| then ‖𝓕 PsiBump ξ‖ else 0) := by
      refine Integrable.mono' PsiBump_fourier_integrable.norm haesm ?_
      filter_upwards with ξ
      by_cases h : L < |ξ| <;> simp [h, norm_nonneg]
    refine integral_mono_ae hint PsiBump_fourier_integrable.norm ?_
    filter_upwards with ξ
    by_cases h : L < |ξ| <;> simp [h, norm_nonneg]
  rcases le_or_gt 1 L with h1 | h1
  · have hstep : Ct / L ^ m ≤ max (Ct + 1) (B + 1) / L ^ m := by
      refine div_le_div_of_nonneg_right (by linarith [le_max_left (Ct + 1) (B + 1)]) (le_of_lt hLm)
    exact (hCt L h1).trans hstep
  · -- `0 < L < 1`
    have hge : (1 : ℝ) ≤ 1 / L ^ m := by
      rw [le_div_iff₀ hLm, one_mul]
      exact pow_le_one₀ (le_of_lt hL) (le_of_lt h1)
    calc fourierTail L ≤ B := htail
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (1 / L ^ m) := mul_le_mul_of_nonneg_left hge hB
      _ = B / L ^ m := by rw [div_eq_mul_inv]; ring
      _ ≤ max (Ct + 1) (B + 1) / L ^ m :=
          div_le_div_of_nonneg_right (by linarith [le_max_right (Ct + 1) (B + 1)]) (le_of_lt hLm)

end RegimeSmall

end Work.GM.Energy.RLocal

