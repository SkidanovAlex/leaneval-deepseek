import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.buchstab_decomp
import Submission.Work.BMF.mr_direct.card_has_prime_factor_le
import Submission.Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2
import Submission.Work.BMF.mr_direct.ebound_integral_le
import Submission.Work.BMF.mr_direct.ep2_integral_le
import Submission.Work.BMF.mr_direct.dupExtra_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Buchstab/Ramaré decomposition inequality `Work.BMF.mr_direct.buchstab_identity`

See the module docstring of the proofs below.  The proof follows Matomäki–Radziwiłł
(Annals 2016), Lemma `lem:decomp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace mr_direct

noncomputable section

open Work.BMF.mrDirect

/-! ### Elementary helpers -/

lemma bi_natCast_cpow_mul (p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m) (s : ℂ) :
    ((p * m : ℕ) : ℂ) ^ s = (p : ℂ) ^ s * (m : ℂ) ^ s := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s

lemma bi_norm_cpow (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ = 1 / (n : ℝ) := by
  have harg : Complex.I * (((-(Real.log (n : ℝ)) : ℝ) : ℂ) * (t : ℂ))
      = (((-(Real.log (n : ℝ)) * t : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [Work.BMF.cpow_neg_one_sub_I n hn t, harg, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, norm_inv, Complex.norm_natCast, one_div]

lemma bi_norm_inv_natCast_le_one (k : ℕ) (hk : 1 ≤ k) : ‖(((k : ℕ)) : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)

/-- `Σ` over a filtered set plus its complement. -/
lemma bi_sum_filter_add (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ) :
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, f x := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x <;> simp [h]

/-- The cardinality of `indexSet K P Q`. -/
lemma bi_indexSet_card_le (K P Q : ℝ) (hK : 0 < K) (hP : 1 < P) (hPQ : P ≤ Q) :
    ((indexSet K P Q).card : ℝ) ≤ K * Real.log (Q / P) + 2 := by
  have hQ1 : 1 ≤ Q := le_trans (le_of_lt hP) hPQ
  have hab : ⌊K * Real.log P⌋₊ ≤ ⌊K * Real.log Q⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hPQ) hK.le)
  have hcardNat : (indexSet K P Q).card + ⌊K * Real.log P⌋₊ ≤ ⌊K * Real.log Q⌋₊ + 1 := by
    have hidx : indexSet K P Q = Finset.Icc ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊ := rfl
    have h3 : (Finset.Icc ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊).card
        ≤ ⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊ := by
      have h1 : Finset.Icc ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊ ⊆
          (Finset.range (⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊)).image
            (fun j => j + ⌊K * Real.log P⌋₊) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        refine Finset.mem_image.mpr ⟨j - ⌊K * Real.log P⌋₊, ?_, by omega⟩
        rw [Finset.mem_range]
        omega
      calc (Finset.Icc ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊).card
          ≤ ((Finset.range (⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊)).image
              (fun j => j + ⌊K * Real.log P⌋₊)).card := Finset.card_le_card h1
        _ ≤ (Finset.range (⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊)).card := Finset.card_image_le
        _ = ⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊ := Finset.card_range _
    rw [hidx]
    omega
  have hreal : ((indexSet K P Q).card : ℝ) + (⌊K * Real.log P⌋₊ : ℝ) ≤
      (⌊K * Real.log Q⌋₊ : ℝ) + 1 := by exact_mod_cast hcardNat
  have hb : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q :=
    Nat.floor_le (mul_nonneg (by positivity) (Real.log_nonneg hQ1))
  have ha : K * Real.log P - 1 < ((⌊K * Real.log P⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (K * Real.log P)
    linarith
  have hdiv : Real.log Q - Real.log P = Real.log (Q / P) :=
    (Real.log_div (by linarith) (by linarith)).symm
  have hmul : K * Real.log Q - K * Real.log P = K * Real.log (Q / P) := by
    rw [← hdiv]; ring
  linarith

/-- Continuity of `t ↦ n^{-(1+it)}`. -/
lemma bi_continuous_cpow (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have hfun : (fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = fun t : ℝ => (n : ℂ)⁻¹ *
          Complex.exp (Complex.I * (((-(Real.log (n : ℝ)) : ℝ) : ℂ) * (t : ℂ))) := by
    funext t
    exact Work.BMF.cpow_neg_one_sub_I n hn t
  rw [hfun]
  fun_prop

lemma bi_continuous_dirPolyM (a : ℕ → ℂ) (X : ℝ) (hX : 1 ≤ X) :
    Continuous fun t => dirPolyM a X t := by
  unfold dirPolyM
  refine continuous_finsetSum _ fun n hn => ?_
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_ceil_iff.mpr (by linarith)) hn.1
  exact Continuous.mul continuous_const (bi_continuous_cpow n hn1)

lemma bi_continuous_primePoly (c : ℕ → ℂ) (K : ℝ) (j : ℕ) :
    Continuous fun t => primePoly c K j t := by
  unfold primePoly
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const (bi_continuous_cpow p hp.2.one_le)

lemma bi_continuous_remPoly (b : ℕ → ℂ) (P Q K X : ℝ) (j : ℕ) (hX : 0 < X) :
    Continuous fun t => remPoly b P Q K X j t := by
  unfold remPoly
  refine continuous_finsetSum _ fun m hm => ?_
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hm
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_ceil_iff.mpr
    (mul_pos hX (Real.exp_pos _))) hm.1
  exact Continuous.mul (Continuous.mul continuous_const continuous_const)
    (bi_continuous_cpow m hm1)

lemma bi_continuous_MT (b c : ℕ → ℂ) (K P Q X : ℝ) (hX : 0 < X) :
    Continuous fun t => ∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t :=
  continuous_finsetSum _ fun j _ =>
    (bi_continuous_primePoly c K j).mul (bi_continuous_remPoly b P Q K X j hX)

lemma bi_continuous_ebound (b c : ℕ → ℂ) (K P Q X : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hX : 0 < X) :
    Continuous fun t => ebound b c K P Q X t := by
  unfold ebound
  refine continuous_finsetSum _ fun p hp => Continuous.mul ?_ ?_
  · exact Continuous.mul continuous_const (bi_continuous_cpow p (by
      exact ((mem_primeSet (by linarith : (0:ℝ) ≤ Q)).mp hp).1.one_le))
  · refine continuous_finsetSum _ fun m hm => ?_
    have hm1 : 1 ≤ m := by
      have hmem := (Finset.mem_filter.mp hm).1
      rw [winIdx, Work.BMF.natIcc, Finset.mem_Icc] at hmem
      exact le_trans (Nat.one_le_ceil_iff.mpr (mul_pos hX (Real.exp_pos _))) hmem.1
    exact Continuous.mul (Continuous.mul continuous_const continuous_const)
      (bi_continuous_cpow m hm1)

lemma bi_continuous_dupExtra (b c : ℕ → ℂ) (K P Q X : ℝ) (hX : 0 < X) :
    Continuous fun t => dupExtra b c K P Q X t := by
  unfold dupExtra
  refine continuous_finsetSum _ fun j hj => Continuous.mul ?_ (bi_continuous_remPoly b P Q K X j hX)
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const
    (bi_continuous_cpow p (mem_winPrimes.mp hp.1).1.one_le)

lemma bi_continuous_ep2 (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 0 < X) :
    Continuous fun t => ep2 a b c P Q X t := by
  unfold ep2
  refine continuous_finsetSum _ fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_filter.mp hp).2.one_le
  have hppos : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp1)
  refine continuous_finsetSum _ fun m hm => ?_
  have hm1 : 1 ≤ m * p := by
    have h2 : 1 ≤ m := by
      have hmem := (Finset.mem_filter.mp hm).1
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hmem
      exact le_trans (Nat.one_le_ceil_iff.mpr (div_pos hX hppos)) hmem.1
    calc 1 ≤ 1 * 1 := by norm_num
      _ ≤ m * p := Nat.mul_le_mul h2 hp1
  exact Continuous.mul (Continuous.sub (Continuous.mul continuous_const continuous_const)
    (Continuous.mul (Continuous.mul continuous_const continuous_const) continuous_const))
    (bi_continuous_cpow _ hm1)

/-! ### The two regroupings -/

lemma bi_mainA_eq_mainB_sub_ebound (b c : ℕ → ℂ) (K P Q X : ℝ) (hK : 0 < K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) (hX : 0 < X) :
    ∀ t, mainA b c P Q X t = mainB b c K P Q X t - ebound b c K P Q X t := by
  intro t
  unfold mainA mainB ebound
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet (by linarith : (0:ℝ) ≤ Q)).mp hp
  have hwidx : p ∈ winPrimes K (jdex K p) := mem_winPrimes_jdex hK hpp
  have hsub := natIcc_div_subset_winIdx hX hwidx
  have hfilt : (winIdx K X (jdex K p)).filter
        (fun m => m ∈ Work.BMF.natIcc (X / p) (2 * X / p))
      = Work.BMF.natIcc (X / p) (2 * X / p) := by
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hkey : (∑ m ∈ winIdx K X (jdex K p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      - (∑ m ∈ (winIdx K X (jdex K p)).filter
          (fun m => m ∉ Work.BMF.natIcc (X / p) (2 * X / p)),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ m ∈ Work.BMF.natIcc (X / p) (2 * X / p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← bi_sum_filter_add (winIdx K X (jdex K p))
      (fun m => m ∈ Work.BMF.natIcc (X / p) (2 * X / p))
      (fun m => b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
        (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))), hfilt]
    ring
  rw [← mul_sub, hkey]

lemma bi_canon_set (K P Q : ℝ) (hK : 0 < K) (hP : 2 ≤ P) (hPQ : P ≤ Q) (j : ℕ) :
    (primeSet P Q).filter (fun p => jdex K p = j)
      = (winPrimes K j).filter
          (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p) := by
  have hQnn : (0 : ℝ) ≤ Q := by linarith
  ext p
  constructor
  · intro hp
    obtain ⟨hp', hjd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet hQnn).mp hp'
    have hw : p ∈ winPrimes K j := by
      rw [← hjd]
      exact mem_winPrimes_jdex hK hpp
    exact Finset.mem_filter.mpr ⟨hw, hPp, hpQ, hjd.symm⟩
  · intro hp
    obtain ⟨hpw, hPp, hpQ, hjd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨mem_primeSet' (mem_winPrimes.mp hpw).1 hPp hpQ, hjd.symm⟩

lemma bi_primeSet_group (Ψ : ℕ → ℂ) (K P Q : ℝ) (hK : 0 < K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ primeSet P Q, Ψ p) =
      ∑ j ∈ indexSet K P Q,
        ∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p), Ψ p := by
  have hmem : ∀ p ∈ primeSet P Q, jdex K p ∈ indexSet K P Q := by
    intro p hp
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet (by linarith : (0:ℝ) ≤ Q)).mp hp
    exact jdex_mem_indexSet hK hpp.one_le (by linarith) hPp hpQ
  rw [← Finset.sum_fiberwise_of_maps_to (s := primeSet P Q) (t := indexSet K P Q)
    (g := fun p => jdex K p) hmem]
  exact Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr (bi_canon_set K P Q hK hP hPQ j) (fun _ _ => rfl)

lemma bi_mainTerm_eq_mainB_add_dupExtra (b c : ℕ → ℂ) (K P Q X : ℝ) (hK : 0 < K)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∀ t, (∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t)
      = mainB b c K P Q X t + dupExtra b c K P Q X t := by
  intro t
  set Ψ : ℕ → ℂ := fun p =>
    c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) *
      (∑ m ∈ winIdx K X (jdex K p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) with hΨ
  have hmainB : mainB b c K P Q X t = ∑ p ∈ primeSet P Q, Ψ p := rfl
  have hsplit : ∀ j ∈ indexSet K P Q,
      primePoly c K j t * remPoly b P Q K X j t =
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPoly b P Q K X j t
        + (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPoly b P Q K X j t := by
    intro j hj
    rw [primePoly_eq, ← bi_sum_filter_add (winPrimes K j)
      (fun p => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)
      (fun p => c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    ring
  have hdup : dupExtra b c K P Q X t =
      ∑ j ∈ indexSet K P Q,
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPoly b P Q K X j t := rfl
  have hcanon : (∑ j ∈ indexSet K P Q,
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPoly b P Q K X j t)
      = ∑ p ∈ primeSet P Q, Ψ p := by
    rw [bi_primeSet_group Ψ K P Q hK hP hPQ]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨-, -, hjd⟩ := (Finset.mem_filter.mp hp).2
    show c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) * remPoly b P Q K X j t = Ψ p
    rw [hjd, hΨ]
    rfl
  rw [hmainB, hdup, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcanon]

/-! ### The mean square of the main term -/

lemma bi_mainTerm_integral_le (c b : ℕ → ℂ) (K P Q X S : ℝ) (hX : 0 < X) (hS : 0 ≤ S) :
    (∫ t in (-S)..S,
        ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
      ≤ ((indexSet K P Q).card : ℝ) *
          (∑ j ∈ indexSet K P Q,
            ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) := by
  have hpt : ∀ t, ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2
      ≤ ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2 := by
    intro t
    calc ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2
        ≤ (∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPoly b P Q K X j t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hcont : Continuous fun t => ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2 :=
    Continuous.mul continuous_const (continuous_finsetSum _ fun j _ =>
      ((bi_continuous_primePoly c K j).mul (bi_continuous_remPoly b P Q K X j hX)).norm.pow 2)
  have hint : (∫ t in (-S)..S, ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
      = ((indexSet K P Q).card : ℝ) *
        (∑ j ∈ indexSet K P Q,
          ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    intro j _
    exact (((bi_continuous_primePoly c K j).mul
      (bi_continuous_remPoly b P Q K X j hX)).norm.pow 2).intervalIntegrable _ _
  exact (intervalIntegral.integral_mono (by linarith)
    (((bi_continuous_MT b c K P Q X hX).norm.pow 2).intervalIntegrable (-S) S)
    (hcont.intervalIntegrable (-S) S) hpt).trans (le_of_eq hint)


/-! ### Arithmetic helpers for the error bounds -/

lemma bi_arith1 (X K P : ℝ) (hX : 0 < X) (hK : 0 < K) (hP : 0 < P) :
    200000 / X * (1 / K + 1 / P) + 100 / (P * X) ≤ 200100 * ((1 / K + 1 / P) / X) := by
  have h2 : (1 : ℝ) / P ≤ (1 / K + 1 / P) := by
    have : (0 : ℝ) ≤ 1 / K := by positivity
    linarith
  have h1 : 100 / (P * X) ≤ 100 * ((1 / K + 1 / P) / X) := by
    calc 100 / (P * X) = 100 * ((1 / P) / X) := by ring
      _ ≤ 100 * ((1 / K + 1 / P) / X) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hX.le) (by norm_num)
  have h3 : 200000 / X * (1 / K + 1 / P) = 200000 * ((1 / K + 1 / P) / X) := by ring
  rw [h3]
  linarith

lemma bi_arith2 (X K P : ℝ) (hX : 0 < X) (hK : 0 < K) (hP : 0 < P) (hPX : P ≤ 2 * X) :
    (8 * X / K + 8) * Real.exp 2 / X ^ 2 ≤ 24 * Real.exp 2 * ((1 / K + 1 / P) / X) := by
  have hsplit : (8 * X / K + 8) * Real.exp 2 / X ^ 2
      = 8 * Real.exp 2 / (K * X) + 8 * Real.exp 2 / X ^ 2 := by
    have hXne : X ≠ 0 := ne_of_gt hX
    have hKne : K ≠ 0 := ne_of_gt hK
    field_simp
  rw [hsplit]
  have h1 : 8 * Real.exp 2 / (K * X) ≤ 8 * Real.exp 2 * ((1 / K + 1 / P) / X) := by
    have h : (1 : ℝ) / K ≤ (1 / K + 1 / P) := by
      have : (0 : ℝ) ≤ 1 / P := by positivity
      linarith
    calc 8 * Real.exp 2 / (K * X) = 8 * Real.exp 2 * ((1 / K) / X) := by ring
      _ ≤ 8 * Real.exp 2 * ((1 / K + 1 / P) / X) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hX.le) (by positivity)
  have h2 : 8 * Real.exp 2 / X ^ 2 ≤ 16 * Real.exp 2 * ((1 / K + 1 / P) / X) := by
    have hP' : 1 / X ≤ 2 / P := by
      rw [div_le_iff₀ hX]
      rw [show 2 / P * X = 2 * X / P by ring]
      rw [le_div_iff₀ hP]
      linarith [hPX]
    have hP'' : (2 : ℝ) / P ≤ 2 * (1 / K + 1 / P) := by
      have h2P : (2 : ℝ) / P = 2 * (1 / P) := by ring
      rw [h2P]
      have : (0 : ℝ) ≤ 1 / K := by positivity
      have : (1 : ℝ) / P ≤ 1 / K + 1 / P := by linarith
      linarith
    calc 8 * Real.exp 2 / X ^ 2 = 8 * Real.exp 2 * ((1 / X) / X) := by ring
      _ ≤ 8 * Real.exp 2 * ((2 / P) / X) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hP' hX.le) (by positivity)
      _ ≤ 8 * Real.exp 2 * ((2 * (1 / K + 1 / P)) / X) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hP'' hX.le) (by positivity)
      _ = 16 * Real.exp 2 * ((1 / K + 1 / P) / X) := by ring
  calc 8 * Real.exp 2 / (K * X) + 8 * Real.exp 2 / X ^ 2
      ≤ 8 * Real.exp 2 * ((1 / K + 1 / P) / X) + 16 * Real.exp 2 * ((1 / K + 1 / P) / X) := by
        linarith
    _ = 24 * Real.exp 2 * ((1 / K + 1 / P) / X) := by ring

lemma bi_arith3 (X K P : ℝ) (hX : 0 < X) (hK : 0 < K) (hP : 0 < P) :
    16 / (P * X) ≤ 16 * ((1 / K + 1 / P) / X) := by
  have h2 : (1 : ℝ) / P ≤ (1 / K + 1 / P) := by
    have : (0 : ℝ) ≤ 1 / K := by positivity
    linarith
  calc 16 / (P * X) = 16 * ((1 / P) / X) := by ring
    _ ≤ 16 * ((1 / K + 1 / P) / X) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hX.le) (by norm_num)

/-! ### Placeholders for the delegated mean-square bounds (to be replaced by imports) -/

/-! ### The main theorem -/

theorem buchstab_identity :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X K P Q : ℝ) (a b c : ℕ → ℂ) (S : ℝ), 1 ≤ X → 1 ≤ K → 2 ≤ P → P ≤ Q →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) → a n = 0) →
      (∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
        a (m * p) = b m * c p) → 0 ≤ S →
      (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyM a X t‖ ^ 2) ≤
        C * (K * Real.log (Q / P) *
              (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                ∫ t in (-S)..S,
                  ‖Work.BMF.mrDirect.primePoly c K j t *
                    Work.BMF.mrDirect.remPoly b P Q K X j t‖ ^ 2)
          + (S + X) / X * (1 / K + 1 / P)) := by
  obtain ⟨C₀, hC₀pos, hC₀mvt⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨max 4 (1000000000 * (C₀ + 1)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro X K P Q a b c S hX hK hP hPQ ha hb hc hzero hmul hS
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  set T1 : ℝ := K * Real.log (Q / P) *
    (∑ j ∈ indexSet K P Q,
      ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) with hT1
  set T2 : ℝ := (S + X) / X * (1 / K + 1 / P) with hT2
  have hT1nn : 0 ≤ T1 := by
    rw [hT1]
    refine mul_nonneg (mul_nonneg (by linarith) ?_) ?_
    · apply Real.log_nonneg
      rw [le_div_iff₀ hPpos]
      linarith
    · exact Finset.sum_nonneg fun j _ =>
        intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hT2nn : 0 ≤ T2 := by rw [hT2]; positivity
  have hgoal : (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
      ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
    by_cases hPX : P ≤ 2 * X
    · by_cases hsmall : K * Real.log (Q / P) < 1
      · -- Case B: `K log (Q/P) < 1`, only the support hypothesis and counting are used
        have hcard : ((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card
            ≤ ((Work.BMF.natIcc X (2 * X)).filter
                (fun n => ∃ p ∈ primeSet P Q, p ∣ n)).card := by
          apply Finset.card_le_card
          intro n hn
          obtain ⟨hnN, hna⟩ := Finset.mem_filter.mp hn
          refine Finset.mem_filter.mpr ⟨hnN, ?_⟩
          by_contra hcon
          exact hna (hzero n (fun p hp hPp hpQ hpd =>
            hcon ⟨p, mem_primeSet' hp hPp hpQ, hpd⟩))
        have hcardle := card_has_prime_factor_le X K P Q hX hK hP hPQ hsmall
        have hsum : (∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
            ≤ ((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card * (1 / X ^ 2) := by
          have h1 : (∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
              = ∑ n ∈ (Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun n hn => ?_
            by_cases h : a n = 0 <;> simp [h]
          rw [h1]
          calc (∑ n ∈ (Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0),
                ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
              ≤ ∑ _n ∈ (Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0), 1 / X ^ 2 := by
                refine Finset.sum_le_sum fun n hn => ?_
                obtain ⟨hnN, hna⟩ := Finset.mem_filter.mp hn
                have hnX : X ≤ (n : ℝ) := by
                  rw [Work.BMF.natIcc, Finset.mem_Icc] at hnN
                  exact le_trans (Nat.le_ceil X) (by exact_mod_cast hnN.1)
                have hn1 : (0 : ℝ) < (n : ℝ) := by linarith
                have hb1 : ‖a n‖ ≤ 1 := ha n
                have h2 : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a n)]
                calc ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
                      div_le_div_of_nonneg_right h2 (by positivity)
                  _ ≤ 1 / X ^ 2 := one_div_le_one_div_of_le (by positivity)
                    (by nlinarith [hnX, hXpos])
            _ = ((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card * (1 / X ^ 2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hmvt := Work.BMF.mrDirect.dirPolyM_mean_value C₀ hC₀mvt a X S hX hS
        have hB : (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
            ≤ 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P) := by
          have hstep : (2 * S + 3 * C₀ * X) *
                (((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card * (1 / X ^ 2))
              ≤ 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P) := by
            have h1 : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
            have h2 : (((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card : ℝ)
                ≤ 12 * X * (1 / K + 1 / P) := le_trans (by exact_mod_cast hcard) hcardle
            have h3 : (0 : ℝ) ≤ 2 * S + 3 * C₀ * X := by nlinarith [hC₀nn, hS]
            have h4 : ((((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card : ℝ)
                * (1 / X ^ 2)) ≤ 12 * X * (1 / K + 1 / P) * (1 / X ^ 2) :=
              mul_le_mul_of_nonneg_right h2 h1
            have h5 : 12 * X * (1 / K + 1 / P) * (1 / X ^ 2) = 12 * (1 / K + 1 / P) / X := by
              field_simp
            calc (2 * S + 3 * C₀ * X) *
                  (((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card * (1 / X ^ 2))
                ≤ (2 * S + 3 * C₀ * X) * (12 * X * (1 / K + 1 / P) * (1 / X ^ 2)) :=
                  mul_le_mul_of_nonneg_left h4 h3
              _ = 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P) := by
                  rw [h5]; ring
          calc (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * X) *
                  (∑ n ∈ Work.BMF.natIcc X (2 * X), ‖a n‖ ^ 2 / (n : ℝ) ^ 2) := hmvt
            _ ≤ (2 * S + 3 * C₀ * X) *
                  (((Work.BMF.natIcc X (2 * X)).filter (fun n => a n ≠ 0)).card * (1 / X ^ 2)) :=
                mul_le_mul_of_nonneg_left hsum (by nlinarith [hC₀nn, hS])
            _ ≤ 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P) := hstep
        have hfin : 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P)
            ≤ T2 * (1000000000 * (C₀ + 1)) := by
          rw [hT2]
          have h1 : 12 * (2 * S + 3 * C₀ * X) ≤ 1000000000 * (C₀ + 1) * (S + X) := by
            nlinarith [hC₀nn, hS, hX]
          have h2 : (0 : ℝ) ≤ (1 / K + 1 / P) / X := by positivity
          calc 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P)
              = (12 * (2 * S + 3 * C₀ * X)) * ((1 / K + 1 / P) / X) := by ring
            _ ≤ (1000000000 * (C₀ + 1) * (S + X)) * ((1 / K + 1 / P) / X) :=
                mul_le_mul_of_nonneg_right h1 h2
            _ = (S + X) / X * (1 / K + 1 / P) * (1000000000 * (C₀ + 1)) := by ring
        have hMnn : (0 : ℝ) ≤ max 4 (1000000000 * (C₀ + 1)) :=
          le_trans (by norm_num) (le_max_left _ _)
        calc (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
            ≤ 12 * (2 * S + 3 * C₀ * X) / X * (1 / K + 1 / P) := hB
          _ ≤ T2 * (1000000000 * (C₀ + 1)) := hfin
          _ ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
              have h6 : T2 * (1000000000 * (C₀ + 1))
                  ≤ T2 * max 4 (1000000000 * (C₀ + 1)) :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) hT2nn
              have h7 : T2 * max 4 (1000000000 * (C₀ + 1))
                  ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
                nlinarith [hT1nn, hT2nn, hMnn]
              linarith
      · -- Case A: `1 ≤ K log (Q/P)`
        have hbig : 1 ≤ K * Real.log (Q / P) := not_lt.mp hsmall
        set B1 : ℝ := 2 * X * Real.exp (1 / K) with hB1def
        set U : ℝ := (1 / K + 1 / P) / X with hUdef
        have hUnn : 0 ≤ U := by rw [hUdef]; positivity
        have hB1ge : (1 : ℝ) ≤ B1 := by
          have h1 : (1 : ℝ) ≤ X := hX
          have h2 : (1 : ℝ) ≤ Real.exp (1 / K) := Real.one_le_exp (by positivity)
          rw [hB1def]
          nlinarith
        have hB1nn : 0 ≤ B1 := le_trans zero_le_one hB1ge
        have hidI := dirPolyM_eq_mainA_add_ep2 a b c P Q X hXpos hP hPQ hzero hmul
        have hidII := bi_mainA_eq_mainB_sub_ebound b c K P Q X hKpos hP hPQ hXpos
        have hidIII := bi_mainTerm_eq_mainB_add_dupExtra b c K P Q X hKpos hP hPQ
        have hDerr : ∀ t, dirPolyM a X t =
            (∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t)
              - (dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t) := by
          intro t
          rw [hidIII t, hidI t, hidII t]
          ring
        have hcD : Continuous fun t => ‖dirPolyM a X t‖ ^ 2 :=
          (bi_continuous_dirPolyM a X hX).norm.pow 2
        have hcMT : Continuous fun t =>
            ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2 :=
          (bi_continuous_MT b c K P Q X hXpos).norm.pow 2
        have hcd : Continuous fun t => ‖dupExtra b c K P Q X t‖ ^ 2 :=
          (bi_continuous_dupExtra b c K P Q X hXpos).norm.pow 2
        have hce : Continuous fun t => ‖ebound b c K P Q X t‖ ^ 2 :=
          (bi_continuous_ebound (b := b) (c := c) (K := K) (P := P) (Q := Q) (X := X)
            hP hPQ hXpos).norm.pow 2
        have hcp : Continuous fun t => ‖ep2 a b c P Q X t‖ ^ 2 :=
          (bi_continuous_ep2 a b c P Q X hXpos).norm.pow 2
        have hcdp : Continuous fun t =>
            ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2 :=
          (((bi_continuous_dupExtra b c K P Q X hXpos).add
              (bi_continuous_ebound (b := b) (c := c) (K := K) (P := P) (Q := Q) (X := X)
                hP hPQ hXpos)).sub (bi_continuous_ep2 a b c P Q X hXpos)).norm.pow 2
        have hpt : ∀ t, ‖dirPolyM a X t‖ ^ 2
            ≤ 2 * ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2
              + 2 * ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2 := by
          intro t
          rw [hDerr t]
          set u := (∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t) with hu
          set v := (dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t) with hv
          have h1 : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
          have h2 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
          have h3 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
          have h5 : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
            have := mul_self_le_mul_self (norm_nonneg (u - v)) h1
            nlinarith [this]
          nlinarith [h5, sq_nonneg (‖u‖ - ‖v‖)]
        have hsplit : (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
            ≤ 2 * (∫ t in (-S)..S,
                  ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
              + 2 * (∫ t in (-S)..S,
                  ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2) := by
          have hcont2 : Continuous fun t => 2 * ‖∑ j ∈ indexSet K P Q,
              primePoly c K j t * remPoly b P Q K X j t‖ ^ 2
              + 2 * ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2 :=
            (Continuous.const_mul hcMT 2).add (Continuous.const_mul hcdp 2)
          have hmono := intervalIntegral.integral_mono (μ := volume) (hab := by linarith)
            (hf := hcD.intervalIntegrable (-S) S) (hg := hcont2.intervalIntegrable (-S) S) hpt
          have heq : (∫ t in (-S)..S, 2 * ‖∑ j ∈ indexSet K P Q,
                primePoly c K j t * remPoly b P Q K X j t‖ ^ 2
                + 2 * ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2)
              = 2 * (∫ t in (-S)..S,
                  ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
                + 2 * (∫ t in (-S)..S,
                  ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2) := by
            rw [intervalIntegral.integral_add
              (f := fun t => 2 * ‖∑ j ∈ indexSet K P Q,
                primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
              (g := fun t => 2 * ‖dupExtra b c K P Q X t + ebound b c K P Q X t
                - ep2 a b c P Q X t‖ ^ 2)
              ((Continuous.const_mul hcMT 2).intervalIntegrable (-S) S)
              ((Continuous.const_mul hcdp 2).intervalIntegrable (-S) S)]
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          exact hmono.trans (le_of_eq heq)
        have hMT6 : (∫ t in (-S)..S,
              ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) ≤ 6 * T1 := by
          have hcard := bi_indexSet_card_le K P Q hKpos (by linarith) hPQ
          have hcard6 : ((indexSet K P Q).card : ℝ) ≤ 6 * (K * Real.log (Q / P)) := by
            linarith [hcard, hbig]
          have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ indexSet K P Q,
              ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2 :=
            Finset.sum_nonneg fun j _ =>
              intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
          calc (∫ t in (-S)..S,
                ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
              ≤ ((indexSet K P Q).card : ℝ) *
                  (∑ j ∈ indexSet K P Q,
                    ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) :=
                bi_mainTerm_integral_le c b K P Q X S hXpos hS
            _ ≤ (6 * (K * Real.log (Q / P))) *
                  (∑ j ∈ indexSet K P Q,
                    ∫ t in (-S)..S, ‖primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hcard6 hsum_nn
            _ = 6 * T1 := by rw [hT1]; ring
        have herr1 := dupExtra_integral_le C₀ hC₀mvt b c K P Q X S hX hK hP hPQ hb hc hS
        have herr2 := ebound_integral_le C₀ hC₀mvt b c K P Q X S hX hK hP hPQ hb hc hS
        have herr3 := ep2_integral_le C₀ hC₀mvt a b c P Q X S hX hP hPQ ha hb hc hS
        have hM1 : (0 : ℝ) ≤ 2 * S + 3 * C₀ * B1 := by nlinarith [hC₀nn, hS, hB1nn]
        have hXB1 : X ≤ B1 := by
          rw [hB1def]
          nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 1 / K), hX]
        have h2XB1 : 2 * X ≤ B1 := by
          rw [hB1def]
          nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 1 / K), hX]
        have h1x : (2 * S + 3 * C₀ * X) ≤ (2 * S + 3 * C₀ * B1) := by
          nlinarith [hC₀nn, hS, hXB1]
        have hsum_nn3 : (0 : ℝ) ≤ (2 * S + 3 * C₀ * X) := by nlinarith [hC₀nn, hS]
        have ha1 := bi_arith1 X K P hXpos hKpos hPpos
        have ha2 := bi_arith2 X K P hXpos hKpos hPpos hPX
        have ha3 := bi_arith3 X K P hXpos hKpos hPpos
        have hErrSum : (∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
              + (∫ t in (-S)..S, ‖ebound b c K P Q X t‖ ^ 2)
              + (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)
            ≤ (2 * S + 3 * C₀ * B1) * (201000 * U) := by
          have hUeq : U = (1 / K + 1 / P) / X := hUdef
          have e1 : (∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * B1) * (200100 * U) := by
            rw [hUeq]
            exact le_trans herr1 (mul_le_mul_of_nonneg_left ha1 hM1)
          have e2 : (∫ t in (-S)..S, ‖ebound b c K P Q X t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * B1) * (24 * Real.exp 2 * U) := by
            rw [hUeq]
            exact le_trans herr2 (mul_le_mul_of_nonneg_left ha2 hM1)
          have e3 : (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * B1) * (16 * U) := by
            have h3' : (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)
                ≤ (2 * S + 3 * C₀ * (2 * X)) * (16 * U) := by
              rw [hUeq]
              exact le_trans herr3 (mul_le_mul_of_nonneg_left ha3 (by nlinarith [hC₀nn, hS, hX]))
            have h4' : (2 * S + 3 * C₀ * (2 * X)) * (16 * U) ≤ (2 * S + 3 * C₀ * B1) * (16 * U) :=
              mul_le_mul_of_nonneg_right (by nlinarith [hC₀nn, hS, h2XB1]) (by linarith)
            exact le_trans h3' h4'
          have hcomb : (2 * S + 3 * C₀ * B1) * (200100 * U) + (2 * S + 3 * C₀ * B1) * (24 * Real.exp 2 * U)
                + (2 * S + 3 * C₀ * B1) * (16 * U)
              = (2 * S + 3 * C₀ * B1) * ((200100 + 24 * Real.exp 2 + 16) * U) := by ring
          have he2 : Real.exp 2 ≤ 9 := by
            have h := Real.exp_one_lt_three
            have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
              rw [← Real.exp_add]
              norm_num
            rw [h2]
            nlinarith [Real.exp_pos 1]
          have hconst : 200100 + 24 * Real.exp 2 + 16 ≤ 201000 := by linarith
          have hfinal : (2 * S + 3 * C₀ * B1) * ((200100 + 24 * Real.exp 2 + 16) * U)
              ≤ (2 * S + 3 * C₀ * B1) * (201000 * U) := by
            apply mul_le_mul_of_nonneg_left _ hM1
            apply mul_le_mul_of_nonneg_right hconst hUnn
          linarith [e1, e2, e3, hcomb, hfinal]
        have herrfin : (∫ t in (-S)..S,
              ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2)
            ≤ 30000000 * (C₀ + 1) * T2 := by
          have h3 : (2 * S + 3 * C₀ * B1) ≤ 20 * (C₀ + 1) * (S + X) := by
            have h4 : Real.exp (1 / K) ≤ Real.exp 1 := by
              apply Real.exp_le_exp.mpr
              rw [div_le_iff₀ hKpos]
              linarith
            have hB1' : B1 ≤ 2 * Real.exp 1 * X := by
              rw [hB1def]
              nlinarith [Real.exp_pos 1, h4, hX]
            nlinarith [hC₀nn, hS, hX, hB1', Real.exp_pos 1, Real.exp_one_lt_three]
          have hpt3 : ∀ t, ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2
              ≤ 3 * (‖dupExtra b c K P Q X t‖ ^ 2 + (‖ebound b c K P Q X t‖ ^ 2
                  + ‖ep2 a b c P Q X t‖ ^ 2)) := by
            intro t
            have h1 : ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖
                ≤ ‖dupExtra b c K P Q X t‖ + ‖ebound b c K P Q X t‖ + ‖ep2 a b c P Q X t‖ := by
              have ha' := norm_sub_le (dupExtra b c K P Q X t + ebound b c K P Q X t)
                (ep2 a b c P Q X t)
              have hb' := norm_add_le (dupExtra b c K P Q X t) (ebound b c K P Q X t)
              linarith
            have h2 : (0 : ℝ) ≤ ‖dupExtra b c K P Q X t‖ := norm_nonneg _
            have h3' : (0 : ℝ) ≤ ‖ebound b c K P Q X t‖ := norm_nonneg _
            have h4 : (0 : ℝ) ≤ ‖ep2 a b c P Q X t‖ := norm_nonneg _
            have h5 : ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2
                ≤ (‖dupExtra b c K P Q X t‖ + ‖ebound b c K P Q X t‖ + ‖ep2 a b c P Q X t‖) ^ 2 := by
              have := mul_self_le_mul_self
                (norm_nonneg (dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t)) h1
              nlinarith [this]
            have h6 : (‖dupExtra b c K P Q X t‖ + ‖ebound b c K P Q X t‖ + ‖ep2 a b c P Q X t‖) ^ 2
                ≤ 3 * (‖dupExtra b c K P Q X t‖ ^ 2 + (‖ebound b c K P Q X t‖ ^ 2
                    + ‖ep2 a b c P Q X t‖ ^ 2)) := by
              nlinarith [h2, h3', h4, sq_nonneg (‖dupExtra b c K P Q X t‖ - ‖ebound b c K P Q X t‖),
                sq_nonneg (‖ebound b c K P Q X t‖ - ‖ep2 a b c P Q X t‖)]
            linarith [h5, h6]
          have hint1 : (∫ t in (-S)..S,
                ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2)
              ≤ 3 * ((∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ebound b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)) := by
            have hcont3 : Continuous fun t => 3 * (‖dupExtra b c K P Q X t‖ ^ 2
                + (‖ebound b c K P Q X t‖ ^ 2 + ‖ep2 a b c P Q X t‖ ^ 2)) :=
              Continuous.const_mul (hcd.add (hce.add hcp)) 3
            have hmono := intervalIntegral.integral_mono (μ := volume) (hab := by linarith)
              (hf := hcdp.intervalIntegrable (-S) S)
              (hg := hcont3.intervalIntegrable (-S) S) hpt3
            have heq : (∫ t in (-S)..S, 3 * (‖dupExtra b c K P Q X t‖ ^ 2
                  + (‖ebound b c K P Q X t‖ ^ 2 + ‖ep2 a b c P Q X t‖ ^ 2)))
                = 3 * ((∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ebound b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)) := by
              rw [intervalIntegral.integral_const_mul]
              congr 1
              rw [intervalIntegral.integral_add
                (f := fun t => ‖dupExtra b c K P Q X t‖ ^ 2)
                (g := fun t => ‖ebound b c K P Q X t‖ ^ 2 + ‖ep2 a b c P Q X t‖ ^ 2)
                (hcd.intervalIntegrable (-S) S) ((hce.add hcp).intervalIntegrable (-S) S)]
              rw [intervalIntegral.integral_add
                (f := fun t => ‖ebound b c K P Q X t‖ ^ 2)
                (g := fun t => ‖ep2 a b c P Q X t‖ ^ 2)
                (hce.intervalIntegrable (-S) S) (hcp.intervalIntegrable (-S) S)]
              ring
            exact hmono.trans (le_of_eq heq)
          have hU6 : 3 * (20 * (C₀ + 1) * (S + X)) * (201000 * U) = 12060000 * (C₀ + 1) * T2 := by
            rw [hUdef, hT2]
            ring
          calc (∫ t in (-S)..S,
                ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2)
              ≤ 3 * ((∫ t in (-S)..S, ‖dupExtra b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ebound b c K P Q X t‖ ^ 2)
                  + (∫ t in (-S)..S, ‖ep2 a b c P Q X t‖ ^ 2)) := hint1
            _ ≤ 3 * ((2 * S + 3 * C₀ * B1) * (201000 * U)) :=
                mul_le_mul_of_nonneg_left hErrSum (by norm_num)
            _ ≤ 3 * ((20 * (C₀ + 1) * (S + X)) * (201000 * U)) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul_of_nonneg_right h3 (by linarith)
            _ = 3 * (20 * (C₀ + 1) * (S + X)) * (201000 * U) := by ring
            _ = 12060000 * (C₀ + 1) * T2 := hU6
            _ ≤ 30000000 * (C₀ + 1) * T2 := by
                have h7 : (0 : ℝ) ≤ (C₀ + 1) * T2 := mul_nonneg (by linarith) hT2nn
                nlinarith [h7]
        have hMnn : (0 : ℝ) ≤ max 4 (1000000000 * (C₀ + 1)) :=
          le_trans (by norm_num) (le_max_left _ _)
        have h9 : 2 * (∫ t in (-S)..S,
              ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2)
            ≤ max 4 (1000000000 * (C₀ + 1)) * T2 := by
          have h14 : (0 : ℝ) ≤ (C₀ + 1) * T2 := mul_nonneg (by linarith) hT2nn
          have h13 : 2 * (30000000 * (C₀ + 1) * T2) ≤ 1000000000 * (C₀ + 1) * T2 := by
            nlinarith [h14]
          have h15 : (1000000000 : ℝ) * (C₀ + 1) * T2
              ≤ max 4 (1000000000 * (C₀ + 1)) * T2 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hT2nn
          linarith [herrfin, h13, h15]
        calc (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2)
            ≤ 2 * (∫ t in (-S)..S,
                  ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2)
                + 2 * (∫ t in (-S)..S,
                  ‖dupExtra b c K P Q X t + ebound b c K P Q X t - ep2 a b c P Q X t‖ ^ 2) := hsplit
          _ ≤ 2 * (6 * T1) + max 4 (1000000000 * (C₀ + 1)) * T2 := by
              have h10 : 2 * (∫ t in (-S)..S,
                    ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPoly b P Q K X j t‖ ^ 2) ≤ 2 * (6 * T1) :=
                mul_le_mul_of_nonneg_left hMT6 (by norm_num)
              linarith [h10, h9]
          _ ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
              have h11 : (12 : ℝ) ≤ max 4 (1000000000 * (C₀ + 1)) := by
                have hM1 : (12 : ℝ) ≤ 1000000000 * (C₀ + 1) := by nlinarith [hC₀pos]
                exact le_trans hM1 (le_max_right _ _)
              have h12 : 2 * (6 * T1) ≤ max 4 (1000000000 * (C₀ + 1)) * T1 := by
                nlinarith [h11, hT1nn]
              calc 2 * (6 * T1) + max 4 (1000000000 * (C₀ + 1)) * T2
                  ≤ max 4 (1000000000 * (C₀ + 1)) * T1
                    + max 4 (1000000000 * (C₀ + 1)) * T2 := by linarith
                _ = max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by ring
    · -- `2 * X < P`: the support of `a` is empty
      have hPX' : 2 * X < P := not_le.mp hPX
      have hone : ∀ n ∈ Work.BMF.natIcc X (2 * X), a n = 0 := by
        intro n hn
        rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
        exact hzero n (fun p hp hPp hpQ hpd => by
          have hn1 : 1 ≤ n := le_trans (Nat.one_le_ceil_iff.mpr (by linarith)) hn.1
          have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpd
          have hcast : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpn
          have hn2 : (n : ℝ) ≤ 2 * X := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
          linarith)
      have hzero_poly : ∀ t, dirPolyM a X t = 0 := by
        intro t
        rw [dirPolyM]
        exact Finset.sum_eq_zero fun n hn => by rw [hone n hn, zero_mul]
      have hLHS : (∫ t in (-S)..S, ‖dirPolyM a X t‖ ^ 2) = 0 := by
        simp [hzero_poly]
      rw [hLHS]
      have : 0 ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
        apply mul_nonneg (le_trans (by norm_num) (le_max_left _ _))
        linarith [hT1nn, hT2nn]
      linarith
  exact hgoal

end

end mr_direct

end Work.BMF
