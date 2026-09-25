import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite

namespace Commons.Dynamics.Transference

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- The Lebesgue integral with respect to counting measure of an `ℝ≥0∞`-valued function
which vanishes outside a finite set `s` is the finite sum over `s`. -/
lemma lintegral_count_eq_sum {f : ℕ → ℝ≥0∞} {s : Finset ℕ} (h : ∀ n ∉ s, f n = 0) :
    ∫⁻ n, f n ∂Measure.count = ∑ n ∈ s, f n := by
  rw [lintegral_count, tsum_eq_sum h]

/-- The `p`-th power map `x ↦ x ^ p` on `ℝ≥0∞` is measurable. -/
lemma measurable_ennreal_rpow_const (p : ℝ) : Measurable fun x : ℝ≥0∞ => x ^ p :=
  ENNReal.continuous_rpow_const.measurable

theorem calderon_transference {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    {k : ℕ → ℕ → ℝ}
    (hk0 : ∀ N j, N ≤ j → k N j = 0)
    (hk1 : ∀ N, ∑ j ∈ Finset.range N, |k N j| ≤ 1)
    (hℓp : ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖∑ j ∈ Finset.range N, k N j * g (n + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count)
    {f : X → ℝ} (hf : Measurable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∫⁻ x, (⨆ N : ℕ, ‖∑ j ∈ Finset.range N, k N j * f (T^[j] x)‖ₑ) ^ p ∂μ
      ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Measurable fun x : ℝ≥0∞ => x ^ p := measurable_ennreal_rpow_const p
  -- The reference `L^p` norm of `f`.
  set J : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hJ
  have hJtop : J ≠ ⊤ := by rw [hJ]; exact ne_of_lt hfp
  -- The `N`-th averaging operator, as an `ℝ≥0∞`-valued function.
  let a : ℕ → X → ℝ≥0∞ := fun N x => ‖∑ j ∈ Finset.range N, k N j * f (T^[j] x)‖ₑ
  have ha : ∀ N, Measurable (a N) := by
    intro N
    simp only [a]
    refine Measurable.enorm ?_
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hf.comp (hT.measurable.iterate j)))
  have hne : ∀ M : ℕ, (Finset.range (M + 1)).Nonempty :=
    fun M => ⟨0, Finset.mem_range.mpr (Nat.succ_pos M)⟩
  -- The `M`-th truncated maximal function.
  let b : ℕ → X → ℝ≥0∞ := fun M => (Finset.range (M + 1)).sup' (hne M) (fun N => a N)
  have hb : ∀ M, Measurable (b M) := by
    intro M
    simp only [b]
    exact measurable_sup' _ (fun N _ => ha N)
  have hb_apply : ∀ M x, b M x = (Finset.range (M + 1)).sup' (hne M) (fun N => a N x) := by
    intro M x
    simp only [b, Finset.sup'_apply]
  have hb_mono : ∀ M M', M ≤ M' → b M ≤ b M' := by
    intro M M' hMM'
    simp only [b]
    exact Finset.sup'_mono (fun N => a N) (fun n hn => by
      simp only [Finset.mem_range] at hn ⊢; omega) (hne M)
  -- Key estimate at level `M`, by the Calderón transference ("orbit") argument.
  have key : ∀ M : ℕ, ∫⁻ x, (b M x) ^ p ∂μ ≤ ENNReal.ofReal ((2 * C) ^ p) * J := by
    intro M
    -- The pointwise transference inequality.
    have hpt : ∀ x, ∑ n ∈ Finset.range (M + 2), (b M (T^[n] x)) ^ p ≤
        ENNReal.ofReal (C ^ p) * ∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p := by
      intro x
      let G : ℕ → ℝ := fun n => if n < 2 * M + 2 then f (T^[n] x) else 0
      have hGval : ∀ n, G n = if n < 2 * M + 2 then f (T^[n] x) else 0 := fun n => rfl
      have hGsupp : ∃ s : Finset ℕ, ∀ n, n ∉ s → G n = 0 := by
        refine ⟨Finset.range (2 * M + 2), fun n hn => ?_⟩
        rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h))]
      have hdisc := hℓp G hGsupp
      -- the finite orbit sum is dominated by the count integral of the discrete sup
      have hterm : ∀ n ∈ Finset.range (M + 2),
          b M (T^[n] x) ≤ ⨆ N : ℕ, ‖∑ j ∈ Finset.range N, k N j * G (n + j)‖ₑ := by
        intro n hn
        rw [hb_apply]
        refine Finset.sup'_le _ _ (fun N hN => ?_)
        simp only [Finset.mem_range] at hn hN
        have hlt : ∀ j ∈ Finset.range N, n + j < 2 * M + 2 := by
          intro j hj
          simp only [Finset.mem_range] at hj
          omega
        have hsum : a N (T^[n] x) = ‖∑ j ∈ Finset.range N, k N j * G (n + j)‖ₑ := by
          simp only [a]
          congr 1
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have hiter : T^[j] (T^[n] x) = T^[n + j] x := by
            rw [← Function.iterate_add_apply, Nat.add_comm]
          rw [hiter, hGval (n + j), if_pos (hlt j hj)]
        rw [hsum]
        exact le_iSup (fun N => ‖∑ j ∈ Finset.range N, k N j * G (n + j)‖ₑ) N
      have hsum_le : ∑ n ∈ Finset.range (M + 2), (b M (T^[n] x)) ^ p ≤
          ∫⁻ n, (⨆ N : ℕ, ‖∑ j ∈ Finset.range N, k N j * G (n + j)‖ₑ) ^ p ∂Measure.count := by
        rw [lintegral_count]
        refine le_trans (Finset.sum_le_sum (fun n hn =>
          ENNReal.rpow_le_rpow (hterm n hn) hp0.le)) (ENNReal.sum_le_tsum _)
      have hGcount : ∫⁻ n, ‖G n‖ₑ ^ p ∂Measure.count
          = ∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p := by
        rw [lintegral_count_eq_sum (s := Finset.range (2 * M + 2)) (fun n hn => by
          rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h)), enorm_zero,
            ENNReal.zero_rpow_of_pos hp0])]
        exact Finset.sum_congr rfl (fun n hn => by
          rw [hGval n, if_pos (Finset.mem_range.mp hn)])
      calc ∑ n ∈ Finset.range (M + 2), (b M (T^[n] x)) ^ p
          ≤ ∫⁻ n, (⨆ N : ℕ, ‖∑ j ∈ Finset.range N, k N j * G (n + j)‖ₑ) ^ p ∂Measure.count :=
            hsum_le
        _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖G n‖ₑ ^ p ∂Measure.count := hdisc
        _ = ENNReal.ofReal (C ^ p) * ∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p := by
            rw [hGcount]
    -- integrate the pointwise inequality
    have hmeas_sumF : Measurable fun x : X =>
        ∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p :=
      Finset.measurable_sum _ (fun n _ => hpow.comp ((hf.enorm).comp (hT.measurable.iterate n)))
    have hmeas_sumB : ∀ n : ℕ, Measurable fun x : X => (b M (T^[n] x)) ^ p :=
      fun n => hpow.comp ((hb M).comp (hT.measurable.iterate n))
    have hint : ∫⁻ x, ∑ n ∈ Finset.range (M + 2), (b M (T^[n] x)) ^ p ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal (C ^ p) *
            (∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p) ∂μ :=
      lintegral_mono (fun x => hpt x)
    have hL : ∫⁻ x, ∑ n ∈ Finset.range (M + 2), (b M (T^[n] x)) ^ p ∂μ
        = (M + 2) • (∫⁻ x, (b M x) ^ p ∂μ) := by
      rw [lintegral_finsetSum (Finset.range (M + 2)) (fun n _ => hmeas_sumB n)]
      rw [Finset.sum_congr rfl (fun n _ => (hT.iterate n).lintegral_comp
        (f := fun y => (b M y) ^ p) (hpow.comp (hb M)))]
      rw [Finset.sum_const, Finset.card_range]
    have hmeas_f : ∀ n : ℕ, Measurable fun x : X => ‖f (T^[n] x)‖ₑ ^ p :=
      fun n => hpow.comp ((hf.enorm).comp (hT.measurable.iterate n))
    have hJterm : ∀ n : ℕ, ∫⁻ x, ‖f (T^[n] x)‖ₑ ^ p ∂μ = J := by
      intro n
      rw [hJ]
      exact (hT.iterate n).lintegral_comp (f := fun y => ‖f y‖ₑ ^ p) (hpow.comp hf.enorm)
    have hR : ∫⁻ x, ENNReal.ofReal (C ^ p) *
          (∑ n ∈ Finset.range (2 * M + 2), ‖f (T^[n] x)‖ₑ ^ p) ∂μ
        = ENNReal.ofReal (C ^ p) * ((2 * M + 2) • J) := by
      rw [lintegral_const_mul _ hmeas_sumF]
      congr 1
      rw [lintegral_finsetSum (Finset.range (2 * M + 2)) (fun n _ => hmeas_f n)]
      rw [Finset.sum_congr rfl (fun n _ => hJterm n), Finset.sum_const, Finset.card_range]
    have hineq : (M + 2) • (∫⁻ x, (b M x) ^ p ∂μ)
        ≤ ENNReal.ofReal (C ^ p) * ((2 * M + 2) • J) := by
      rw [← hL, ← hR]
      exact hint
    -- arithmetic: conclude the level-`M` estimate
    set I : ℝ≥0∞ := ∫⁻ x, (b M x) ^ p ∂μ with hI
    have hineq' : (M + 2) • I ≤ ENNReal.ofReal (C ^ p) * ((2 * M + 2) • J) := by
      rw [hI]; exact hineq
    have hfin : ENNReal.ofReal (C ^ p) * ((2 * M + 2) • J) < ⊤ := by
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [nsmul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.mpr hJtop)
    have hIlt : I < ⊤ := by
      have h1 : I ≤ (M + 2) • I := by
        simpa using nsmul_le_nsmul_left (show (0:ℝ≥0∞) ≤ I from bot_le)
          (show (1:ℕ) ≤ M + 2 by omega)
      exact lt_of_le_of_lt h1 (lt_of_le_of_lt hineq' hfin)
    have hreal : I.toReal ≤ (2 * C) ^ p * J.toReal := by
      have hmono := ENNReal.toReal_mono (ne_of_lt hfin) hineq'
      rw [ENNReal.toReal_nsmul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hC p), ENNReal.toReal_nsmul] at hmono
      rw [nsmul_eq_mul, nsmul_eq_mul] at hmono
      -- `hmono : ↑(M+2) * I.toReal ≤ C^p * (↑(2M+2) * J.toReal)`
      have hMc : (0:ℝ) < ((M + 2 : ℕ) : ℝ) := by positivity
      have hCpow : (0:ℝ) ≤ C ^ p := Real.rpow_nonneg hC p
      have hj : (0:ℝ) ≤ J.toReal := ENNReal.toReal_nonneg
      have hmono' : I.toReal * ((M + 2 : ℕ) : ℝ) ≤
          C ^ p * ((2 * M + 2 : ℕ) : ℝ) * J.toReal := by
        have h := hmono
        rw [mul_comm (((M + 2 : ℕ) : ℝ)) I.toReal, ← mul_assoc] at h
        exact h
      have h1 : I.toReal ≤ C ^ p * (((2 * M + 2 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ)) * J.toReal := by
        calc I.toReal = I.toReal * ((M + 2 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ) :=
              (mul_div_cancel_right₀ I.toReal hMc.ne').symm
          _ ≤ (C ^ p * ((2 * M + 2 : ℕ) : ℝ) * J.toReal) / ((M + 2 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hmono' hMc.le
          _ = C ^ p * (((2 * M + 2 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ)) * J.toReal := by ring
      have hratio : (((2 * M + 2 : ℕ) : ℝ)) / ((M + 2 : ℕ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hMc]
        push_cast
        linarith
      have h2p : (2:ℝ) ≤ 2 ^ p := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
        simpa using h
      calc I.toReal ≤ C ^ p * (((2 * M + 2 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ)) * J.toReal := h1
        _ ≤ C ^ p * 2 * J.toReal :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hCpow) hj
        _ = 2 * C ^ p * J.toReal := by ring
        _ ≤ (2 * C) ^ p * J.toReal := by
            apply mul_le_mul_of_nonneg_right _ hj
            calc 2 * C ^ p ≤ 2 ^ p * C ^ p := mul_le_mul_of_nonneg_right h2p hCpow
              _ = (2 * C) ^ p := (Real.mul_rpow (by norm_num) hC).symm
    calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal (ne_of_lt hIlt)).symm
      _ ≤ ENNReal.ofReal ((2 * C) ^ p * J.toReal) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((2 * C) ^ p) * ENNReal.ofReal J.toReal :=
            ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) p)
      _ = ENNReal.ofReal ((2 * C) ^ p) * J := by rw [ENNReal.ofReal_toReal hJtop]
  -- Monotone convergence: pass from the truncations `b M` to the full supremum.
  have hsup_eq : ∀ x, (⨆ M : ℕ, b M x) = (⨆ N : ℕ, a N x) := by
    intro x
    refine le_antisymm (iSup_le fun M => ?_) (iSup_le fun N => ?_)
    · rw [hb_apply]
      exact Finset.sup'_le _ _ (fun N _ => le_iSup (fun N => a N x) N)
    · have h2 : a N x ≤ b N x := by
        rw [hb_apply]
        exact Finset.le_sup' (fun N => a N x) (Finset.mem_range.mpr (by omega : N < N + 1))
      exact le_trans h2 (le_iSup (fun M => b M x) N)
  have hcongr : ∀ x, (⨆ N : ℕ, a N x) ^ p = ⨆ M : ℕ, (b M x) ^ p := by
    intro x
    rw [← hsup_eq x, Commons.Analysis.Integral.ENNReal.iSup_rpow hp0]
  calc ∫⁻ x, (⨆ N : ℕ, a N x) ^ p ∂μ
      = ∫⁻ x, ⨆ M : ℕ, (b M x) ^ p ∂μ := lintegral_congr hcongr
    _ = ⨆ M : ℕ, ∫⁻ x, (b M x) ^ p ∂μ :=
        lintegral_iSup' (fun M => ((hb M).pow_const p).aemeasurable)
          (Eventually.of_forall (fun x => fun M M' hMM' =>
            ENNReal.rpow_le_rpow (hb_mono M M' hMM' x) hp0.le))
    _ ≤ ENNReal.ofReal ((2 * C) ^ p) * J := iSup_le key

end Commons.Dynamics.Transference