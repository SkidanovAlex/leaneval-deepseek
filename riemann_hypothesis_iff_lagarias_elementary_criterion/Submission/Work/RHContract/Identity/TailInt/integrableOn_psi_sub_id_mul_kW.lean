import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Integrability of `t ↦ (ψ t − t) k(t)` on `(a, ∞)`

The kernel `k(t) = (log t + 1)/(t² log² t)` decays like `t⁻²/log t`, so the integrability of
the tail `∫_a^∞ (ψ t − t) k(t) dt` (the defining integral of `psiTail`) needs a genuine
estimate on `ψ t − t`.  We use the (unconditional) Chebyshev-type estimate
`|ψ t − t| ≤ t/(log t)^A` valid for large `t`
(`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real`), together with the elementary global
bound `(log t)² ≤ 4 t` for the region where `t` is bounded.
-/

namespace Work.RHContract.Identity.TailInt

open MeasureTheory

/-- `log t ≤ 2 √t` for `t ≥ 1`. -/
private lemma log_le_two_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ 2 * Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs0
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    have h2 := Real.log_pow (Real.sqrt t) 2
    rw [hs] at h2
    simpa using h2
  rw [hlog]
  linarith [Real.sqrt_nonneg t]

/-- `(log t)² ≤ 4 t` for `t ≥ 1`. -/
private lemma log_sq_le_four_mul {t : ℝ} (ht : 1 ≤ t) : (Real.log t) ^ 2 ≤ 4 * t := by
  have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht
  have h := log_le_two_sqrt ht
  have h2 : (Real.log t) ^ 2 ≤ (2 * Real.sqrt t) ^ 2 := pow_le_pow_left₀ hlog_nn h 2
  have hsq : (2 * Real.sqrt t) ^ 2 = 4 * t := by
    rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t)]
    norm_num
  rw [hsq] at h2
  exact h2

/-- `u ↦ (u+1)/u^4` is integrable on `(L, ∞)` for `L > 0`. -/
private lemma integrableOn_shifted_rpow {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun u : ℝ => (u + 1) / u ^ 4) (Set.Ioi L) := by
  have h3 : IntegrableOn (fun u : ℝ => u ^ (-3 : ℝ)) (Set.Ioi L) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hL
  have h4 : IntegrableOn (fun u : ℝ => u ^ (-4 : ℝ)) (Set.Ioi L) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hL
  have hsum : IntegrableOn (fun u : ℝ => u ^ (-3 : ℝ) + u ^ (-4 : ℝ)) (Set.Ioi L) :=
    h3.add h4
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := lt_trans hL hu
  change u ^ (-3 : ℝ) + u ^ (-4 : ℝ) = (u + 1) / u ^ 4
  rw [Real.rpow_neg hu0.le 3, Real.rpow_neg hu0.le 4]
  simp only [Real.rpow_ofNat]
  field_simp

/-- `t ↦ (log t + 1)/(t (log t)^4)` is integrable on `(a, ∞)` for `a > 1`. -/
private lemma integrableOn_logPoly_div {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t : ℝ => (Real.log t + 1) / (t * (Real.log t) ^ 4)) (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  have hg := integrableOn_shifted_rpow hL
  have h := (integrableOn_comp_log_Ioi (fun u : ℝ => (u + 1) / u ^ 4) ha0).mpr hg
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans ha0 hx
  have hlogx : Real.log x ≠ 0 := (Real.log_pos (lt_trans ha hx)).ne'
  have hxne : x ≠ 0 := hx0.ne'
  simp only [smul_eq_mul]
  field_simp

theorem integrableOn_psi_sub_id_mul_kW {a : ℝ} (ha : 2 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t)
      (Set.Ioi a) MeasureTheory.volume := by
  obtain ⟨x₀, hx₀⟩ := Commons.NumberTheory.Zeta.psi_sub_id_powLog_real 2 (by norm_num)
  set b : ℝ := max x₀ a with hb
  set C : ℝ := max 1 (4 * (Chebyshev.psi b + b)) with hCdef
  have ha1 : (1 : ℝ) < a := by linarith
  have hx₀_le_b : x₀ ≤ b := le_trans (le_max_left _ _) hb.ge
  have ha_le_b : a ≤ b := le_trans (le_max_right _ _) hb.ge
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) hCdef.ge
  have hC4 : 4 * (Chebyshev.psi b + b) ≤ C := le_trans (le_max_right _ _) hCdef.ge
  -- The key pointwise estimate `|ψ t − t| ≤ C t / (log t)²` for `t > a`.
  have key : ∀ t : ℝ, a < t → |Chebyshev.psi t - t| ≤ C * (t / (Real.log t) ^ 2) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_trans ha1 ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogpos : 0 < Real.log t := Real.log_pos ht1
    have hlogsq_pos : 0 < (Real.log t) ^ 2 := by positivity
    have hquarter : (1 : ℝ) / 4 ≤ t / (Real.log t) ^ 2 := by
      rw [le_div_iff₀ hlogsq_pos]
      have h := log_sq_le_four_mul (le_of_lt ht1)
      linarith
    rcases le_or_gt t b with htb | hbt
    · have hpsi_le : Chebyshev.psi t ≤ Chebyshev.psi b := Chebyshev.psi_mono htb
      have hbound : |Chebyshev.psi t - t| ≤ Chebyshev.psi b + b := by
        have hpt := Chebyshev.psi_nonneg t
        rw [abs_le]
        constructor <;> linarith
      have step : Chebyshev.psi b + b ≤ C * (t / (Real.log t) ^ 2) := by
        have h1 : (4 * (Chebyshev.psi b + b)) * (1 / 4) ≤ C * (t / (Real.log t) ^ 2) :=
          mul_le_mul hC4 hquarter (by norm_num) (le_of_lt (lt_of_lt_of_le zero_lt_one hC1))
        have h2 : (4 * (Chebyshev.psi b + b)) * (1 / 4) = Chebyshev.psi b + b := by ring
        linarith [h1, h2.le, h2.ge]
      linarith
    · have htb' : x₀ ≤ t := le_trans hx₀_le_b (le_of_lt hbt)
      have h1 := hx₀ t htb'
      rw [Real.rpow_ofNat] at h1
      have hnn : 0 ≤ t / (Real.log t) ^ 2 := le_trans (by norm_num) hquarter
      have h2 : t / (Real.log t) ^ 2 ≤ C * (t / (Real.log t) ^ 2) := by
        have h2' : 1 * (t / (Real.log t) ^ 2) ≤ C * (t / (Real.log t) ^ 2) :=
          mul_le_mul_of_nonneg_right hC1 hnn
        simpa using h2'
      exact le_trans h1 h2
  -- The pointwise bound on the integrand.
  have hbd : ∀ t : ℝ, a < t →
      ‖(Chebyshev.psi t - t) * Work.RHContract.kW t‖ ≤
        C * ((Real.log t + 1) / (t * (Real.log t) ^ 4)) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_trans ha1 ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogpos : 0 < Real.log t := Real.log_pos ht1
    have hlogne : Real.log t ≠ 0 := hlogpos.ne'
    have htne : t ≠ 0 := ht0.ne'
    have hkWval : Work.RHContract.kW t = (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := rfl
    have hkWnn : 0 ≤ Work.RHContract.kW t := by rw [hkWval]; positivity
    have hlogsq_pos : 0 < (Real.log t) ^ 2 := by positivity
    have hnonneg : 0 ≤ C * (t / (Real.log t) ^ 2) :=
      mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hC1))
        (div_nonneg (le_of_lt ht0) (le_of_lt hlogsq_pos))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkWnn]
    calc |Chebyshev.psi t - t| * Work.RHContract.kW t
        ≤ (C * (t / (Real.log t) ^ 2)) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
          mul_le_mul (key t ht) (le_of_eq hkWval) hkWnn hnonneg
      _ = C * ((Real.log t + 1) / (t * (Real.log t) ^ 4)) := by
          field_simp
  have hbase : Integrable (fun t : ℝ => (Real.log t + 1) / (t * (Real.log t) ^ 4))
      (MeasureTheory.volume.restrict (Set.Ioi a)) := integrableOn_logPoly_div ha1
  have hdom : Integrable (fun t : ℝ => C * ((Real.log t + 1) / (t * (Real.log t) ^ 4)))
      (MeasureTheory.volume.restrict (Set.Ioi a)) := hbase.const_mul C
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hpsi : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
    have hkW : Measurable (fun t : ℝ => Work.RHContract.kW t) := by
      unfold Work.RHContract.kW
      fun_prop
    have : Measurable (fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t) :=
      (hpsi.sub measurable_id).mul hkW
    exact this.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbd t ht

end Work.RHContract.Identity.TailInt
