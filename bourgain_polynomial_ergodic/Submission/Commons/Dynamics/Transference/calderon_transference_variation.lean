import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Dynamics.Transference.calderon_transference_maximal

namespace Commons.Dynamics.Transference

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

theorem calderon_transference_variation {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : MeasurePreserving T μ μ)
    {t : ℕ → ℕ} (hmono : Monotone t)
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    {J : ℕ → ℕ} {k : ℕ → ℕ → ℝ}
    (hk0 : ∀ N j, J N ≤ j → k N j = 0)
    (hk1 : ∀ N, ∑ j ∈ Finset.range (J N), |k N j| ≤ 1)
    (hℓp : ∀ (M₀ : ℕ) (g : ℕ → ℝ), (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * g (n + j))
            - (∑ j ∈ Finset.range (J N), k N j * g (n + j))|‖ₑ ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count)
    {f : X → ℝ} (hf : Measurable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∀ M₀ : ℕ, ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * f (T^[j] x))
            - (∑ j ∈ Finset.range (J N), k N j * f (T^[j] x))|‖ₑ ^ p ∂μ
        ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  intro M₀
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Measurable fun x : ℝ≥0∞ => x ^ p := measurable_ennreal_rpow_const p
  set J0 : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hJ0
  have hJ0top : J0 ≠ ⊤ := by rw [hJ0]; exact ne_of_lt hfp
  let S : X → ℝ := fun x =>
    ∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
      |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * f (T^[j] x))
        - (∑ j ∈ Finset.range (J N), k N j * f (T^[j] x))|
  let A : X → ℝ≥0∞ := fun x => ‖S x‖ₑ
  have hS : Measurable S := by
    simp only [S]
    refine Finset.measurable_sum _ (fun M _ => Finset.measurable_sum _ (fun N _ => ?_))
    refine Measurable.abs ?_
    refine Measurable.sub ?_ ?_
    · exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hf.comp (hT.measurable.iterate j)))
    · exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hf.comp (hT.measurable.iterate j)))
  have hA : Measurable A := show Measurable (fun x : X => ‖S x‖ₑ) from hS.enorm
  have hAapply : ∀ x, A x = ‖S x‖ₑ := fun x => rfl
  let L : ℕ := (Finset.range (t M₀ + 2)).sup (fun N => J N)
  let K : ℕ := L + 1
  have hJ_le_L : ∀ N, N < t M₀ + 2 → J N ≤ L := by
    intro N hN
    exact Finset.le_sup (f := fun N => J N) (Finset.mem_range.mpr hN)
  have hKL : K + L ≤ 2 * K := by simp only [K]; omega
  have hpt : ∀ x, ∑ n ∈ Finset.range K, (A (T^[n] x)) ^ p ≤
      ENNReal.ofReal (C ^ p) * ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p := by
    intro x
    let G : ℕ → ℝ := fun n => if n < K + L then f (T^[n] x) else 0
    have hGval : ∀ n, G n = if n < K + L then f (T^[n] x) else 0 := fun n => rfl
    have hGsupp : ∃ s : Finset ℕ, ∀ n, n ∉ s → G n = 0 := by
      refine ⟨Finset.range (K + L), fun n hn => ?_⟩
      rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h))]
    have hsum_eq : ∀ (c : ℕ → ℝ) (m : ℕ), m ≤ L → ∀ n, n < K →
        (∑ j ∈ Finset.range m, c j * f (T^[j] (T^[n] x)))
          = (∑ j ∈ Finset.range m, c j * G (n + j)) := by
      intro c m hm n hn
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjlt : j < m := Finset.mem_range.mp hj
      have hjL : j < L := lt_of_lt_of_le hjlt hm
      have hlt : n + j < K + L := by
        have hn' : n < K := hn
        simp only [K] at hn' ⊢
        omega
      have hiter : T^[j] (T^[n] x) = T^[n + j] x := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
      rw [hiter, hGval (n + j), if_pos hlt]
    have hS_eq : ∀ n, n < K → S (T^[n] x) =
        ∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * G (n + j))
            - (∑ j ∈ Finset.range (J N), k N j * G (n + j))| := by
      intro n hn
      simp only [S]
      refine Finset.sum_congr rfl (fun M hM => Finset.sum_congr rfl (fun N hNM => ?_))
      have hMlt : M < M₀ := Finset.mem_range.mp hM
      have hle : t (M + 1) ≤ t M₀ := hmono (by omega)
      have hNle : N ≤ t M₀ :=
        le_trans (le_trans (Finset.mem_Icc.mp hNM).2 (Nat.sub_le _ _)) hle
      have hJL1 : J (N + 1) ≤ L := hJ_le_L (N + 1) (by omega)
      have hJL2 : J N ≤ L := hJ_le_L N (by omega)
      rw [hsum_eq (fun j => k (N + 1) j) (J (N + 1)) hJL1 n hn,
          hsum_eq (fun j => k N j) (J N) hJL2 n hn]
    have hterm : ∀ n ∈ Finset.range K, A (T^[n] x) =
        ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * G (n + j))
            - (∑ j ∈ Finset.range (J N), k N j * G (n + j))|‖ₑ := by
      intro n hn
      rw [hAapply, hS_eq n (Finset.mem_range.mp hn)]
    have hGcount : ∫⁻ n, ‖G n‖ₑ ^ p ∂Measure.count
        = ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p := by
      rw [lintegral_count_eq_sum (s := Finset.range (K + L)) (fun n hn => by
        rw [hGval n, if_neg (fun h => hn (Finset.mem_range.mpr h)), enorm_zero,
          ENNReal.zero_rpow_of_pos hp0])]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [hGval n, if_pos (Finset.mem_range.mp hn)])
    calc ∑ n ∈ Finset.range K, (A (T^[n] x)) ^ p
        ≤ ∫⁻ n, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
            |(∑ j ∈ Finset.range (J (N + 1)), k (N + 1) j * G (n + j))
              - (∑ j ∈ Finset.range (J N), k N j * G (n + j))|‖ₑ ^ p ∂Measure.count := by
          rw [lintegral_count]
          refine le_trans (Finset.sum_le_sum (fun n hn =>
            ENNReal.rpow_le_rpow (le_of_eq (hterm n hn)) hp0.le)) (ENNReal.sum_le_tsum _)
      _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖G n‖ₑ ^ p ∂Measure.count :=
          hℓp M₀ G hGsupp
      _ = ENNReal.ofReal (C ^ p) * ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p := by
          rw [hGcount]
  have hmeas_sumF : Measurable fun x : X =>
      ∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p :=
    Finset.measurable_sum _ (fun n _ => hpow.comp ((hf.enorm).comp (hT.measurable.iterate n)))
  have hmeas_sumA : ∀ n : ℕ, Measurable fun x : X => (A (T^[n] x)) ^ p :=
    fun n => hpow.comp (hA.comp (hT.measurable.iterate n))
  have hint : ∫⁻ x, ∑ n ∈ Finset.range K, (A (T^[n] x)) ^ p ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (C ^ p) *
          (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p) ∂μ :=
    lintegral_mono (fun x => hpt x)
  have hLsum : ∫⁻ x, ∑ n ∈ Finset.range K, (A (T^[n] x)) ^ p ∂μ
      = K • (∫⁻ x, (A x) ^ p ∂μ) := by
    rw [lintegral_finsetSum (Finset.range K) (fun n _ => hmeas_sumA n)]
    rw [Finset.sum_congr rfl (fun n _ => (hT.iterate n).lintegral_comp
      (f := fun y => (A y) ^ p) (hpow.comp hA))]
    rw [Finset.sum_const, Finset.card_range]
  have hmeas_f : ∀ n : ℕ, Measurable fun x : X => ‖f (T^[n] x)‖ₑ ^ p :=
    fun n => hpow.comp ((hf.enorm).comp (hT.measurable.iterate n))
  have hJterm : ∀ n : ℕ, ∫⁻ x, ‖f (T^[n] x)‖ₑ ^ p ∂μ = J0 := by
    intro n
    rw [hJ0]
    exact (hT.iterate n).lintegral_comp (f := fun y => ‖f y‖ₑ ^ p) (hpow.comp hf.enorm)
  have hRsum : ∫⁻ x, ENNReal.ofReal (C ^ p) *
        (∑ n ∈ Finset.range (K + L), ‖f (T^[n] x)‖ₑ ^ p) ∂μ
      = ENNReal.ofReal (C ^ p) * ((K + L) • J0) := by
    rw [lintegral_const_mul _ hmeas_sumF]
    congr 1
    rw [lintegral_finsetSum (Finset.range (K + L)) (fun n _ => hmeas_f n)]
    rw [Finset.sum_congr rfl (fun n _ => hJterm n), Finset.sum_const, Finset.card_range]
  have hineq : K • (∫⁻ x, (A x) ^ p ∂μ) ≤ ENNReal.ofReal (C ^ p) * ((K + L) • J0) := by
    rw [← hLsum, ← hRsum]
    exact hint
  set I : ℝ≥0∞ := ∫⁻ x, (A x) ^ p ∂μ with hI
  have hineq' : K • I ≤ ENNReal.ofReal (C ^ p) * ((K + L) • J0) := by
    rw [hI]; exact hineq
  have hfin : ENNReal.ofReal (C ^ p) * ((K + L) • J0) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [nsmul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.mpr hJ0top)
  have hIlt : I < ⊤ := by
    have hK1 : (1:ℕ) ≤ K := by simp only [K]; omega
    have h1 : I ≤ K • I := by
      simpa using nsmul_le_nsmul_left (show (0:ℝ≥0∞) ≤ I from bot_le) hK1
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt hineq' hfin)
  have hreal : I.toReal ≤ (2 * C) ^ p * J0.toReal := by
    have hmono := ENNReal.toReal_mono (ne_of_lt hfin) hineq'
    rw [ENNReal.toReal_nsmul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hC p), ENNReal.toReal_nsmul] at hmono
    rw [nsmul_eq_mul, nsmul_eq_mul] at hmono
    have hKc : (0:ℝ) < (K : ℝ) := by
      have : 0 < K := by simp only [K]; omega
      exact_mod_cast this
    have hCpow : (0:ℝ) ≤ C ^ p := Real.rpow_nonneg hC p
    have hj : (0:ℝ) ≤ J0.toReal := ENNReal.toReal_nonneg
    have hratio : ((K + L : ℕ) : ℝ) / (K : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hKc]
      have hcast : ((K + L : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast hKL
      calc ((K + L : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := hcast
        _ = 2 * (K : ℝ) := by push_cast; ring
    have hmono' : I.toReal * (K : ℝ) ≤ C ^ p * ((K + L : ℕ) : ℝ) * J0.toReal := by
      have h := hmono
      rw [mul_comm ((K : ℝ)) I.toReal, ← mul_assoc] at h
      exact h
    have h1 : I.toReal ≤ C ^ p * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := by
      calc I.toReal = I.toReal * (K : ℝ) / (K : ℝ) :=
            (mul_div_cancel_right₀ I.toReal hKc.ne').symm
        _ ≤ (C ^ p * ((K + L : ℕ) : ℝ) * J0.toReal) / (K : ℝ) :=
            div_le_div_of_nonneg_right hmono' hKc.le
        _ = C ^ p * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := by ring
    have h2p : (2:ℝ) ≤ 2 ^ p := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
      simpa using h
    calc I.toReal ≤ C ^ p * (((K + L : ℕ) : ℝ) / (K : ℝ)) * J0.toReal := h1
      _ ≤ C ^ p * 2 * J0.toReal :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hCpow) hj
      _ = 2 * C ^ p * J0.toReal := by ring
      _ ≤ (2 * C) ^ p * J0.toReal := by
          apply mul_le_mul_of_nonneg_right _ hj
          calc 2 * C ^ p ≤ 2 ^ p * C ^ p := mul_le_mul_of_nonneg_right h2p hCpow
            _ = (2 * C) ^ p := (Real.mul_rpow (by norm_num) hC).symm
  show I ≤ ENNReal.ofReal ((2 * C) ^ p) * J0
  calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal (ne_of_lt hIlt)).symm
    _ ≤ ENNReal.ofReal ((2 * C) ^ p * J0.toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((2 * C) ^ p) * ENNReal.ofReal J0.toReal :=
          ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * C) p)
    _ = ENNReal.ofReal ((2 * C) ^ p) * J0 := by rw [ENNReal.ofReal_toReal hJ0top]

end Commons.Dynamics.Transference