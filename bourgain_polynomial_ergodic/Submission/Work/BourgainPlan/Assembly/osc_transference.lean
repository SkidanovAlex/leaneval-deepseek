import Mathlib
import Submission.Work.BourgainPlan.Assembly.Defs

/-!
# Calderón transference of the discrete ℓ² oscillation inequality

The polynomial ergodic averages along a lacunary sequence are transferred from the
counting-measure (`ℕ`) oscillation inequality `Submission.BourgainPlan.OscillationStatement`
to a general probability-preserving system `(X, μ, T)`, by the orbit ("Calderón transference")
argument: one evaluates the discrete inequality on the truncation of the orbit of `x` and then
averages over `x`.  This is the sum-over-blocks analogue of
`Commons.Dynamics.Transference.calderon_transference_maximal`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Assembly

/-- The polynomial ergodic average `x ↦ polyAvg P T f N x` of a measurable function is
measurable (public: the later assembly steps need it, e.g. to invoke `lacunary_ae_of_osc`). -/
lemma measurable_polyAvg {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} (hT : MeasurePreserving T μ μ) {f : X → ℝ} (hf : Measurable f)
    (P : Polynomial ℤ) (N : ℕ) : Measurable (fun x : X => Submission.polyAvg P T f N x) := by
  simp only [Submission.polyAvg]
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
    hf.comp (hT.measurable.iterate _)))

/-- Calderón transference of the discrete ℓ² oscillation inequality `hO` to the ergodic
setting: for `f ∈ L²(μ)` the polynomial averages along a lacunary sequence satisfy the
oscillation inequality `HasOsc` with constant `‖f‖²_{L²}`. -/
theorem osc_transference (hO : Submission.BourgainPlan.OscillationStatement)
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasureTheory.MeasurePreserving T μ μ)
    {P : Polynomial ℤ} (hP : Submission.BourgainPlan.NonnegOnNat P)
    {ρ : ℝ} (hρ : 1 < ρ)
    {f : X → ℝ} (hf : Measurable f) (hf2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤) :
    HasOsc μ (fun i x => Submission.polyAvg P T f (lac ρ i) x)
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) := by
  have hpow2 : Measurable fun y : ℝ≥0∞ => y ^ (2 : ℝ) :=
    Commons.Dynamics.Transference.measurable_ennreal_rpow_const 2
  have hf2ne : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ⊤ := ne_of_lt hf2
  set u : ℕ → X → ℝ := fun i x => Submission.polyAvg P T f (lac ρ i) x with hu
  have havg : ∀ i : ℕ, Measurable (u i) := by
    intro i
    show Measurable (fun x : X => Submission.polyAvg P T f (lac ρ i) x)
    exact measurable_polyAvg hT hf P (lac ρ i)
  intro ε hε
  obtain ⟨J₀, hJ₀⟩ := hO P hP ρ hρ (ε / 2) (by linarith)
  refine ⟨J₀, fun J hJ k hk => ?_⟩
  set L : ℕ := (Finset.range (k J)).sup (fun i => Submission.polySupport P (lac ρ i)) with hL
  set K : ℕ := L + 1 with hK
  set J0 : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hJ0
  have hJ0top : J0 ≠ ⊤ := by rw [hJ0]; exact hf2ne
  have hKL : K + L ≤ 2 * K := by simp only [hK]; omega
  have hK1 : 1 ≤ K := by simp only [hK]; omega
  let E : ℕ → X → ℝ≥0∞ :=
    fun j x => ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ
  let I : ℝ≥0∞ := ∑ j ∈ Finset.range J, ∫⁻ x, (E j x) ^ (2 : ℝ) ∂μ
  have hEmeas : ∀ j : ℕ, Measurable (E j) := by
    intro j
    show Measurable (fun x : X =>
      ⨆ i, ⨆ (_ : i ∈ Finset.Ico (k j) (k (j + 1))), ‖u i x - u (k j) x‖ₑ)
    exact Measurable.iSup (fun i => Measurable.iSup (fun _ : i ∈ Finset.Ico (k j) (k (j + 1)) =>
      ((havg i).sub (havg (k j))).enorm))
  -- The pointwise orbit estimate.
  have hpt : ∀ x : X,
      (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ))
        ≤ ENNReal.ofReal (ε / 2 * J) *
            ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) := by
    intro x
    set G : ℕ → ℝ := fun n => if n < K + L then f (T^[n] x) else 0 with hG
    have hGval : ∀ n, G n = if n < K + L then f (T^[n] x) else 0 := fun n => rfl
    have hGsupp : ∃ s : Finset ℕ, ∀ n, n ∉ s → G n = 0 := by
      refine ⟨Finset.range (K + L), fun n hn => ?_⟩
      rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h))]
    have hdisc := hJ₀ J hJ k hk G hGsupp
    have hGcount : ∫⁻ n, ‖G n‖ₑ ^ (2 : ℝ) ∂Measure.count
        = ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) := by
      rw [Commons.Dynamics.Transference.lintegral_count_eq_sum (s := Finset.range (K + L))
        (fun n hn => by
          rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h)), enorm_zero,
            ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [hGval n, if_pos (Finset.mem_range.mp hn)])
    -- Reading the ergodic averages as the discrete averages of the truncated orbit.
    have hAg : ∀ (N : ℕ) (n : ℕ), Submission.polySupport P (lac ρ N) ≤ L → n < K →
        u N (T^[n] x) = Submission.BourgainPlan.discAvg P (lac ρ N) G n := by
      intro N n hNL hn
      have huN : u N (T^[n] x) = Submission.polyAvg P T f (lac ρ N) (T^[n] x) := by simp only [hu]
      rw [huN]
      simp only [Submission.polyAvg_eq_kernel, Submission.BourgainPlan.discAvg]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjN : j < Submission.polySupport P (lac ρ N) := Finset.mem_range.mp hj
      have hjL : j < L := lt_of_lt_of_le (lt_of_lt_of_le hjN hNL) (le_refl L)
      have hnL : n < L + 1 := by rw [← hK]; exact hn
      have hlt : n + j < K + L := by
        have hKeq : K = L + 1 := hK
        omega
      have hiter : T^[j] (T^[n] x) = T^[n + j] x := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
      rw [hiter, hGval (n + j), if_pos hlt]
    -- Pointwise comparison of the (ergodic vs discrete) block oscillations.
    have hterm : ∀ j ∈ Finset.range J, ∀ n ∈ Finset.range K,
        (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i (T^[n] x) - u (k j) (T^[n] x)‖ₑ)
          ≤ (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n - Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) := by
      intro j hj n hn
      have hjJ : j + 1 ≤ J := by have := Finset.mem_range.mp hj; omega
      have hjlt : j < J := Finset.mem_range.mp hj
      refine iSup_le (fun i => iSup_le (fun hi => ?_))
      have hiJ : i < k J := lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 (hk.monotone hjJ)
      have hkjJ : k j < k J := hk hjlt
      have hiL : Submission.polySupport P (lac ρ i) ≤ L := by
        rw [hL]
        exact Finset.le_sup (f := fun i => Submission.polySupport P (lac ρ i)) (Finset.mem_range.mpr hiJ)
      have hkjL : Submission.polySupport P (lac ρ (k j)) ≤ L := by
        rw [hL]
        exact Finset.le_sup (f := fun i => Submission.polySupport P (lac ρ i)) (Finset.mem_range.mpr hkjJ)
      rw [hAg i n hiL (Finset.mem_range.mp hn), hAg (k j) n hkjL (Finset.mem_range.mp hn)]
      exact le_iSup₂ (f := fun (i : ℕ) (_ : i ∈ Finset.Ico (k j) (k (j + 1))) =>
        ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n -
          Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) i hi
    have hstep : ∀ j ∈ Finset.range J,
        ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)
          ≤ ∫⁻ n, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n - Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) ^ (2 : ℝ)
              ∂Measure.count := by
      intro j hj
      calc ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)
          ≤ ∑ n ∈ Finset.range K,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n - Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) ^ (2 : ℝ) :=
            Finset.sum_le_sum (fun n hn => ENNReal.rpow_le_rpow (hterm j hj n hn) (by norm_num))
        _ ≤ ∫⁻ n, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n - Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) ^ (2 : ℝ)
                ∂Measure.count := by
            rw [MeasureTheory.lintegral_count]
            exact ENNReal.sum_le_tsum _
    calc ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)
        ≤ ∑ j ∈ Finset.range J, ∫⁻ n, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖Submission.BourgainPlan.discAvg P (lac ρ i) G n - Submission.BourgainPlan.discAvg P (lac ρ (k j)) G n‖ₑ) ^ (2 : ℝ)
              ∂Measure.count := Finset.sum_le_sum hstep
      _ ≤ ENNReal.ofReal (ε / 2 * J) * ∫⁻ n, ‖G n‖ₑ ^ (2 : ℝ) ∂Measure.count := hdisc
      _ = ENNReal.ofReal (ε / 2 * J) * ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) := by
          rw [hGcount]
  -- Integrate the pointwise estimate over `X`.
  have hmeas_fsum : Measurable fun x : X =>
      ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) :=
    Finset.measurable_sum _ (fun n _ => hpow2.comp ((hf.enorm).comp (hT.measurable.iterate n)))
  have hInt : ∫⁻ x, (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)) ∂μ
      ≤ ENNReal.ofReal (ε / 2 * J) *
          ∫⁻ x, (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ)) ∂μ := by
    calc ∫⁻ x, (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal (ε / 2 * J) *
            (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ)) ∂μ :=
          lintegral_mono (fun x => hpt x)
      _ = ENNReal.ofReal (ε / 2 * J) *
            ∫⁻ x, (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ)) ∂μ :=
          lintegral_const_mul _ hmeas_fsum
  have hinner : ∀ j : ℕ, Measurable fun x : X =>
      ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ) :=
    fun j => Finset.measurable_sum _
      (fun n _ => hpow2.comp ((hEmeas j).comp (hT.measurable.iterate n)))
  have hsplit : ∫⁻ x, (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)) ∂μ
      = ∑ j ∈ Finset.range J, ∫⁻ x, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ) ∂μ :=
    lintegral_finsetSum (Finset.range J) (fun j _ => hinner j)
  have hper : ∀ j : ℕ, ∫⁻ x, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ) ∂μ
      = K • ∫⁻ x, (E j x) ^ (2 : ℝ) ∂μ := by
    intro j
    have hmeasA : ∀ n : ℕ, Measurable fun x : X => (E j (T^[n] x)) ^ (2 : ℝ) :=
      fun n => hpow2.comp ((hEmeas j).comp (hT.measurable.iterate n))
    rw [lintegral_finsetSum (Finset.range K) (fun n _ => hmeasA n)]
    rw [Finset.sum_congr rfl (fun n _ => (hT.iterate n).lintegral_comp
      (f := fun y => (E j y) ^ (2 : ℝ)) (hpow2.comp (hEmeas j)))]
    rw [Finset.sum_const, Finset.card_range]
  have hJterm : ∀ n : ℕ, ∫⁻ x, ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) ∂μ = J0 := by
    intro n
    rw [hJ0]
    exact (hT.iterate n).lintegral_comp (f := fun y => ‖f y‖ₑ ^ (2 : ℝ)) (hpow2.comp hf.enorm)
  have hRHS : ∫⁻ x, (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ (2 : ℝ)) ∂μ
      = (K + L) • J0 := by
    have hmeasB : ∀ n : ℕ, Measurable fun x : X => ‖f (T^[n] x)‖ₑ ^ (2 : ℝ) :=
      fun n => hpow2.comp ((hf.enorm).comp (hT.measurable.iterate n))
    rw [lintegral_finsetSum (Finset.range (K + L)) (fun n _ => hmeasB n)]
    rw [Finset.sum_congr rfl (fun n _ => hJterm n), Finset.sum_const, Finset.card_range]
  have hIeq : ∫⁻ x, (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range K, (E j (T^[n] x)) ^ (2 : ℝ)) ∂μ
      = K • I := by
    rw [hsplit, Finset.sum_congr rfl (fun j _ => hper j), Finset.sum_nsmul]
  have hineq : K • I ≤ ENNReal.ofReal (ε / 2 * J) * ((K + L) • J0) := by
    rw [← hIeq, ← hRHS]
    exact hInt
  have hfin : ENNReal.ofReal (ε / 2 * J) * ((K + L) • J0) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [nsmul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.mpr hJ0top)
  have hIlt : I < ⊤ := by
    have h1 : I ≤ K • I := by
      simpa using nsmul_le_nsmul_left (show (0 : ℝ≥0∞) ≤ I from bot_le) hK1
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt hineq hfin)
  have hreal : I.toReal ≤ ε * J * J0.toReal := by
    have hmono := ENNReal.toReal_mono (ne_of_lt hfin) hineq
    rw [ENNReal.toReal_nsmul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_nsmul] at hmono
    rw [nsmul_eq_mul, nsmul_eq_mul] at hmono
    have hKc : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := by simp only [hK]; omega
      exact_mod_cast this
    have hj : (0 : ℝ) ≤ J0.toReal := ENNReal.toReal_nonneg
    have hratio : ((K + L : ℕ) : ℝ) / (K : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hKc]
      have hcast : ((K + L : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast hKL
      calc ((K + L : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := hcast
        _ = 2 * (K : ℝ) := by push_cast; ring
    have hmono' : I.toReal * (K : ℝ) ≤ (ε / 2 * J) * ((K + L : ℕ) : ℝ) * J0.toReal := by
      have h := hmono
      rw [mul_comm ((K : ℝ)) I.toReal, ← mul_assoc] at h
      exact h
    have h1 : I.toReal ≤ (ε / 2 * J) * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := by
      calc I.toReal = I.toReal * (K : ℝ) / (K : ℝ) :=
            (mul_div_cancel_right₀ I.toReal hKc.ne').symm
        _ ≤ ((ε / 2 * J) * ((K + L : ℕ) : ℝ) * J0.toReal) / (K : ℝ) :=
            div_le_div_of_nonneg_right hmono' hKc.le
        _ = (ε / 2 * J) * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := by ring
    have hεJ : (0 : ℝ) ≤ ε / 2 * J := by positivity
    calc I.toReal ≤ (ε / 2 * J) * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := h1
      _ ≤ (ε / 2 * J) * 2 * J0.toReal :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hεJ) hj
      _ = ε * J * J0.toReal := by ring
  have hI : I ≤ ENNReal.ofReal (ε * J) * J0 := by
    calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal (ne_of_lt hIlt)).symm
      _ ≤ ENNReal.ofReal (ε * J * J0.toReal) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (ε * J) * ENNReal.ofReal J0.toReal :=
            ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (ε * J) * J0 := by rw [ENNReal.ofReal_toReal hJ0top]
  exact hI

end Work.BourgainPlan.Assembly
