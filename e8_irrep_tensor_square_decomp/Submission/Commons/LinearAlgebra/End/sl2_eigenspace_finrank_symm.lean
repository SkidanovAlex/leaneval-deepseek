import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Commons.Algebra.Lie.expAd_isLieEquiv

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset

namespace Commons.LinearAlgebra.End

section ModuleExp

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

noncomputable def adEnd (a : Module.End K V) : Module.End K (Module.End K V) where
  toFun b := a * b - b * a
  map_add' b c := by rw [mul_add, add_mul]; abel
  map_smul' r b := by simp only [RingHom.id_apply]; rw [mul_smul_comm, smul_mul_assoc, smul_sub]

lemma adEnd_apply (a b : Module.End K V) : adEnd a b = a * b - b * a := rfl

lemma adEnd_pow_succ (a : Module.End K V) (i : ℕ) (b : Module.End K V) :
    ((adEnd a)^(i+1)) b = a * ((adEnd a)^i) b - ((adEnd a)^i) b * a := by
  rw [pow_succ', Module.End.mul_apply]; rfl

theorem adEnd_pow_mul_eq_sum (a b : Module.End K V) (m : ℕ) :
    a^m * b = ∑ i ∈ range (m+1), (Nat.choose m i : K) • (((adEnd a)^i) b * a^(m-i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hterm : ∀ i ∈ range (m+1),
        a * ((Nat.choose m i : K) • (((adEnd a)^i) b * a^(m-i)))
          = (Nat.choose m i : K) • (((adEnd a)^i) b * a^(m+1-i))
            + (Nat.choose m i : K) • (((adEnd a)^(i+1)) b * a^(m-i)) := by
      intro i hi
      rw [mem_range] at hi
      have hac : a * ((adEnd a)^i) b = ((adEnd a)^i) b * a + ((adEnd a)^(i+1)) b := by
        have h := adEnd_pow_succ a i b
        rw [h]; abel
      rw [mul_smul_comm, ← mul_assoc, hac, add_mul, smul_add,
          mul_assoc, ← pow_succ', show m - i + 1 = m + 1 - i from by omega]
    have hpascal : ∀ i : ℕ, (Nat.choose (m+1) (i+1) : K)
        = (Nat.choose m (i+1) : K) + (Nat.choose m i : K) := by
      intro i
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum,
        Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have h1 : (∑ i ∈ range (m+1), (Nat.choose m i : K) • (((adEnd a)^i) b * a^(m+1-i)))
        = (∑ i ∈ range m,
            (Nat.choose m (i+1) : K) • (((adEnd a)^(i+1)) b * a^(m-i))) + b * a^(m+1) := by
      rw [Finset.sum_range_succ']
      have hf0 : (Nat.choose m 0 : K) • (((adEnd a)^0) b * a^(m+1-0)) = b * a^(m+1) := by simp
      have hsum : (∑ i ∈ range m, (Nat.choose m (i+1) : K) •
            (((adEnd a)^(i+1)) b * a^(m+1-(i+1))))
          = ∑ i ∈ range m, (Nat.choose m (i+1) : K) •
            (((adEnd a)^(i+1)) b * a^(m-i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Nat.succ_sub_succ]
      rw [hsum, hf0]
    have h2 : (∑ i ∈ range (m+1), (Nat.choose m i : K) • (((adEnd a)^(i+1)) b * a^(m-i)))
        = (∑ i ∈ range m, (Nat.choose m i : K) • (((adEnd a)^(i+1)) b * a^(m-i)))
          + (Nat.choose m m : K) • (((adEnd a)^(m+1)) b * a^(m-m)) := by
      rw [Finset.sum_range_succ]
    have hR : (∑ i ∈ range (m+1+1), (Nat.choose (m+1) i : K) • (((adEnd a)^i) b * a^(m+1-i)))
        = ((∑ i ∈ range m, (Nat.choose (m+1) (i+1) : K) •
                (((adEnd a)^(i+1)) b * a^(m+1-(i+1))))
             + (Nat.choose (m+1) (m+1) : K) • (((adEnd a)^(m+1)) b * a^(m+1-(m+1))))
          + (Nat.choose (m+1) 0 : K) • (((adEnd a)^0) b * a^(m+1-0)) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hAB : (∑ i ∈ range m, (Nat.choose m (i+1) : K) • (((adEnd a)^(i+1)) b * a^(m-i)))
              + (∑ i ∈ range m, (Nat.choose m i : K) • (((adEnd a)^(i+1)) b * a^(m-i)))
              = ∑ i ∈ range m, (Nat.choose (m+1) (i+1) : K) •
                  (((adEnd a)^(i+1)) b * a^(m-i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← add_smul, ← hpascal i]
    rw [h1, h2, hR,
        show (∑ i ∈ range m, (Nat.choose (m+1) (i+1) : K) •
                (((adEnd a)^(i+1)) b * a^(m+1-(i+1))))
              = ∑ i ∈ range m, (Nat.choose (m+1) (i+1) : K) •
                (((adEnd a)^(i+1)) b * a^(m-i)) from by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Nat.succ_sub_succ],
        ← hAB]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_smul, pow_zero,
      Nat.sub_zero, Nat.sub_self, Module.End.one_apply, mul_one]
    abel

lemma adEnd_pow_eq_zero_of_le {a b : Module.End K V} {k n : ℕ}
    (hk : ((adEnd a)^k) b = 0) (hkn : k ≤ n) : ((adEnd a)^n) b = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_comm, pow_add, Module.End.mul_apply, hk, map_zero]

lemma adEnd_pow_mul_eq_sum_trunc (a b : Module.End K V) {k : ℕ}
    (hk : ((adEnd a)^k) b = 0) (m : ℕ) :
    a^m * b = ∑ i ∈ range k, (Nat.choose m i : K) • (((adEnd a)^i) b * a^(m-i)) := by
  rw [adEnd_pow_mul_eq_sum]
  rcases le_or_gt k (m+1) with h | h
  · refine (Finset.sum_subset (fun i hi => ?_) (fun i hi2 hi1 => ?_)).symm
    · simp only [mem_range] at hi ⊢; omega
    · simp only [mem_range] at hi2 hi1
      rw [adEnd_pow_eq_zero_of_le hk (by omega), zero_mul, smul_zero]
  · refine (Finset.sum_subset (fun i hi => ?_) (fun i hi2 hi1 => ?_))
    · simp only [mem_range] at hi ⊢; omega
    · simp only [mem_range, not_lt] at hi1 hi2
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

noncomputable def expTrunc (a : Module.End K V) (N : ℕ) : Module.End K V :=
  ∑ n ∈ range N, ((n.factorial : K))⁻¹ • (a ^ n)

@[simp] lemma expTrunc_apply (a : Module.End K V) (N : ℕ) (v : V) :
    expTrunc a N v = ∑ n ∈ range N, ((n.factorial : K))⁻¹ • ((a ^ n) v) := by
  simp [expTrunc]

lemma exp_pow_eq_zero_of_le {a : Module.End K V} {v : V} {N M : ℕ}
    (h : (a^N) v = 0) (hNM : N ≤ M) : (a^M) v = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [Nat.add_comm N k, pow_add, Module.End.mul_apply, h, map_zero]

lemma expTrunc_eq_of_le {a : Module.End K V} {v : V} {N M : ℕ}
    (h : (a^N) v = 0) (hNM : N ≤ M) : expTrunc a N v = expTrunc a M v := by
  simp only [expTrunc_apply]
  refine sum_subset (fun n hn => ?_) (fun n hnM hnN => ?_)
  · simp only [mem_range] at hn ⊢; omega
  · simp only [mem_range, not_lt] at hnN
    rw [exp_pow_eq_zero_of_le h hnN, smul_zero]

noncomputable def expIndex (a : Module.End K V)
    (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0) (v : V) : ℕ := by
  classical exact Nat.find (ha v)

lemma exp_pow_expIndex (a : Module.End K V) (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0) (v : V) :
    (a ^ expIndex a ha v) v = 0 := by classical exact Nat.find_spec (ha v)

lemma expIndex_le (a : Module.End K V) (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0)
    {v : V} {n : ℕ} (h : (a^n) v = 0) : expIndex a ha v ≤ n := by
  classical exact Nat.find_min' (ha v) h

lemma expIndex_pos (a : Module.End K V) (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0)
    {v : V} (hv : v ≠ 0) : 0 < expIndex a ha v := by
  rcases Nat.eq_zero_or_pos (expIndex a ha v) with h | h
  · exfalso
    have hh := exp_pow_expIndex a ha v
    rw [h, pow_zero, Module.End.one_apply] at hh
    exact hv hh
  · exact h

noncomputable def expMap (a : Module.End K V) (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0)
    (v : V) : V := expTrunc a (expIndex a ha v) v

lemma expMap_apply (a : Module.End K V) (ha) (v : V) :
    expMap a ha v = expTrunc a (expIndex a ha v) v := rfl

lemma expMap_add (a : Module.End K V) (ha) (v w : V) :
    expMap a ha (v + w) = expMap a ha v + expMap a ha w := by
  set M := expIndex a ha (v+w) + expIndex a ha v + expIndex a ha w with hM
  have h1 : expIndex a ha (v+w) ≤ M := by rw [hM]; omega
  have h2 : expIndex a ha v ≤ M := by rw [hM]; omega
  have h3 : expIndex a ha w ≤ M := by rw [hM]; omega
  rw [expMap_apply, expMap_apply, expMap_apply,
    expTrunc_eq_of_le (exp_pow_expIndex a ha (v+w)) h1,
    expTrunc_eq_of_le (exp_pow_expIndex a ha v) h2,
    expTrunc_eq_of_le (exp_pow_expIndex a ha w) h3]
  exact map_add _ _ _

lemma expMap_smul (a : Module.End K V) (ha) (c : K) (v : V) :
    expMap a ha (c • v) = c • expMap a ha v := by
  set M := expIndex a ha (c • v) + expIndex a ha v with hM
  have h1 : expIndex a ha (c • v) ≤ M := by rw [hM]; omega
  have h2 : expIndex a ha v ≤ M := by rw [hM]; omega
  rw [expMap_apply, expMap_apply,
    expTrunc_eq_of_le (exp_pow_expIndex a ha (c • v)) h1,
    expTrunc_eq_of_le (exp_pow_expIndex a ha v) h2]
  exact map_smul _ _ _

noncomputable def expEnd (a : Module.End K V) (ha : ∀ v : V, ∃ n : ℕ, (a^n) v = 0) :
    Module.End K V where
  toFun := expMap a ha
  map_add' := expMap_add a ha
  map_smul' := expMap_smul a ha

@[simp] lemma expEnd_apply (a : Module.End K V) (ha) (v : V) :
    expEnd a ha v = expMap a ha v := rfl

@[simp] lemma expMap_zero (a : Module.End K V) (ha) : expMap a ha (0 : V) = 0 := by
  rw [expMap_apply, expTrunc_apply]; simp

lemma neg_pow_eq (a : Module.End K V) (n : ℕ) : (-a)^n = ((-1:K)^n) • (a^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, show -a = (-1:K) • a from (neg_one_smul K a).symm,
        smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_succ, ← pow_succ]

lemma neg_pow_apply (a : Module.End K V) (n : ℕ) (v : V) :
    ((-a)^n) v = ((-1:K)^n) • ((a^n) v) := by
  rw [neg_pow_eq, LinearMap.smul_apply]

lemma neg_locallyNilpotent (a : Module.End K V) (ha : ∀ v, ∃ n, (a^n) v = 0) :
    ∀ v, ∃ n, (((-a)^n) v = 0) := by
  intro v; obtain ⟨n, hn⟩ := ha v; exact ⟨n, by rw [neg_pow_apply, hn, smul_zero]⟩

lemma expEnd_mul_eq_sum (a b : Module.End K V) (ha : ∀ v, ∃ n, (a^n) v = 0) {k : ℕ}
    (hk : ((adEnd a)^k) b = 0) :
    expEnd a ha * b
      = (∑ i ∈ range k, ((i.factorial : K))⁻¹ • ((adEnd a)^i) b) * expEnd a ha := by
  ext v
  rw [Module.End.mul_apply]
  set N := expIndex a ha (b v) + (expIndex a ha v + k) with hN
  have hbN : expIndex a ha (b v) ≤ N := by rw [hN]; omega
  have hvN : expIndex a ha v ≤ N := by rw [hN]; omega
  have hL : expEnd a ha (b v)
      = ∑ m ∈ range N, ∑ i ∈ range k,
          (((m.factorial : K))⁻¹ * (Nat.choose m i : K)) •
            ((((adEnd a)^i) b * a^(m-i)) v) := by
    rw [expEnd_apply, expMap_apply,
        expTrunc_eq_of_le (exp_pow_expIndex a ha (b v)) hbN, expTrunc_apply]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [← Module.End.mul_apply, adEnd_pow_mul_eq_sum_trunc a b hk m, LinearMap.sum_apply,
        Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [LinearMap.smul_apply, smul_smul]
  have hR : ((∑ i ∈ range k, ((i.factorial : K))⁻¹ • ((adEnd a)^i) b) * expEnd a ha) v
      = ∑ i ∈ range k, ∑ l ∈ range N,
          (((i.factorial : K))⁻¹ * ((l.factorial : K))⁻¹) •
            ((((adEnd a)^i) b * a^l) v) := by
    rw [Module.End.mul_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [LinearMap.smul_apply, expEnd_apply, expMap_apply,
        expTrunc_eq_of_le (exp_pow_expIndex a ha v) hvN, expTrunc_apply, map_sum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [map_smul, smul_smul, ← Module.End.mul_apply]
  have hinner : ∀ i ∈ range k,
      (∑ m ∈ range N, (((m.factorial : K))⁻¹ * (Nat.choose m i : K)) •
          ((((adEnd a)^i) b * a^(m-i)) v))
      = ∑ l ∈ range N, (((i.factorial : K))⁻¹ * ((l.factorial : K))⁻¹) •
          ((((adEnd a)^i) b * a^l) v) := by
    intro i hi
    rw [mem_range] at hi
    have hiN : i ≤ N := by rw [hN] at *; omega
    have hvNi : expIndex a ha v ≤ N - i := by
      rw [Nat.le_sub_iff_add_le hiN]; rw [hN] at *; omega
    have hsplit := Finset.sum_range_add
      (fun m => (((m.factorial : K))⁻¹ * (Nat.choose m i : K)) •
          ((((adEnd a)^i) b * a^(m-i)) v)) i (N - i)
    rw [show i + (N - i) = N from by omega] at hsplit
    have hzero : (∑ m ∈ range i, (((m.factorial : K))⁻¹ * (Nat.choose m i : K)) •
          ((((adEnd a)^i) b * a^(m-i)) v)) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [mem_range] at hm
      rw [Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, mul_zero, zero_smul]
    rw [hzero, zero_add] at hsplit
    rw [hsplit]
    have hfm : ∀ m : ℕ,
        ((((i+m).factorial : K))⁻¹ * (Nat.choose (i+m) i : K)) •
            ((((adEnd a)^i) b * a^((i+m)-i)) v)
          = (((i.factorial : K))⁻¹ * ((m.factorial : K))⁻¹) •
            ((((adEnd a)^i) b * a^m) v) := by
      intro m
      rw [show i + m - i = m from by omega]
      rw [Commons.Algebra.Lie.coeff_eq (m := i + m) (k := i) (l := m) rfl]
    have hstep : (∑ m ∈ range (N-i), ((((i+m).factorial : K))⁻¹ * (Nat.choose (i+m) i : K)) •
            ((((adEnd a)^i) b * a^((i+m)-i)) v))
        = ∑ l ∈ range N, (((i.factorial : K))⁻¹ * ((l.factorial : K))⁻¹) •
            ((((adEnd a)^i) b * a^l) v) := by
      refine (Finset.sum_congr rfl (fun m _ => hfm m)).trans ?_
      refine Finset.sum_subset (fun l hl => ?_) (fun l hlN hl1 => ?_)
      · simp only [mem_range] at hl ⊢; omega
      · simp only [mem_range] at hlN hl1
        rw [show (((adEnd a)^i) b * a^l) v = 0 from by
          rw [Module.End.mul_apply, exp_pow_eq_zero_of_le (exp_pow_expIndex a ha v) (by omega),
            map_zero], smul_zero]
    rw [hstep]
  rw [hL, hR, Finset.sum_comm]
  exact Finset.sum_congr rfl hinner

lemma expEnd_mul_comm (a : Module.End K V) (ha) : expEnd a ha * a = a * expEnd a ha := by
  have h := expEnd_mul_eq_sum a a ha (k := 1) (by rw [pow_one, adEnd_apply]; abel)
  simpa using h


lemma filter_prod_eq_antidiagonal {r s m : ℕ} (hr : m < r) (hs : m < s) :
    ((range r ×ˢ range s).filter (fun p : ℕ × ℕ => p.1 + p.2 = m)) = antidiagonal m := by
  ext p
  simp only [mem_filter, mem_product, mem_range, HasAntidiagonal.mem_antidiagonal]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

lemma sum_sum_smul_eq_of_conv {a b : ℕ → K} {u : ℕ → V} {M Kk N : ℕ} (hN : 0 < N)
    (hu : ∀ m, N ≤ m → u m = 0) (hMN : N ≤ M) (hKN : N ≤ Kk)
    (h0 : a 0 * b 0 = 1)
    (hconv : ∀ m, 0 < m → m < N → ∑ k ∈ range (m + 1), a k * b (m - k) = 0) :
    ∑ k ∈ range M, ∑ l ∈ range Kk, (a k * b l) • u (k + l) = u 0 := by
  rw [← Finset.sum_product']
  have h1 : ∑ p ∈ range M ×ˢ range Kk, (a p.1 * b p.2) • u (p.1 + p.2)
      = ∑ m ∈ range (M + Kk), ∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m),
          (a p.1 * b p.2) • u (p.1 + p.2) :=
    (sum_fiberwise_of_maps_to
      (fun p hp => by simp only [mem_product, mem_range] at hp; simp only [mem_range]; omega) _).symm
  have h2 : ∑ m ∈ range (M + Kk), ∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m),
          (a p.1 * b p.2) • u (p.1 + p.2)
      = ∑ m ∈ range (M + Kk),
          (∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m), a p.1 * b p.2) • u m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  have h3 : ∑ m ∈ range N, (∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m
      = ∑ m ∈ range (M + Kk), (∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m := by
    refine sum_subset (fun m hm => by simp only [mem_range] at *; omega) ?_
    intro m hm hmN
    simp only [mem_range] at hm
    rw [hu m (by simp only [mem_range] at hmN; omega), smul_zero]
  have h4 : ∀ m ∈ range N, ((∑ p ∈ (range M ×ˢ range Kk).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m) = (∑ k ∈ range (m + 1), a k * b (m - k)) • u m := by
    intro m hm
    rw [mem_range] at hm
    congr 1
    rw [filter_prod_eq_antidiagonal (by omega) (by omega)]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * b l) m
  have h5 : ∀ m ∈ range N, (∑ k ∈ range (m + 1), a k * b (m - k)) • u m
      = (if m = 0 then (1 : K) else 0) • u m := by
    intro m hm
    rw [mem_range] at hm
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [sum_range_one, tsub_zero, h0, if_pos rfl]
    · rw [hconv m h (by omega), if_neg (by omega), zero_smul]
  rw [h1, h2, ← h3, Finset.sum_congr rfl h4, Finset.sum_congr rfl h5,
    Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [if_neg hb0, zero_smul]
  · intro h
    exact absurd (mem_range.mpr hN) h

lemma sum_alt_conv'' (m : ℕ) (hm : 0 < m) :
    ∑ k ∈ range (m+1), ((k.factorial : K))⁻¹ * ((-1 : K)^(m-k) * ((m-k).factorial : K)⁻¹) = 0 := by
  have h1 : (∑ k ∈ range (m+1), ((k.factorial : K))⁻¹ * ((-1:K)^(m-k) * ((m-k).factorial:K)⁻¹))
      = ∑ k ∈ range (m+1), ((-1:K)^(m-k) * (((m-k).factorial:K)⁻¹ * ((k.factorial:K))⁻¹)) := by
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1]
  have h2 : (∑ k ∈ range (m+1), ((-1:K)^(m-k) * (((m-k).factorial:K)⁻¹ * ((k.factorial:K))⁻¹)))
      = ∑ j ∈ range (m+1), ((-1:K)^j * (((j.factorial:K))⁻¹ * ((m-j).factorial:K)⁻¹)) := by
    rw [← Finset.sum_range_reflect
      (fun j => (-1:K)^j * (((j.factorial:K))⁻¹ * ((m-j).factorial:K)⁻¹)) (m+1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mem_range] at hk
    rw [show m + 1 - 1 - k = m - k from by omega, show m - (m - k) = k from by omega]
  rw [h2, show (∑ j ∈ range (m+1), ((-1:K)^j * (((j.factorial:K))⁻¹ * ((m-j).factorial:K)⁻¹)))
        = ∑ j ∈ range (m+1), ((-1:K)^j * ((j.factorial:K))⁻¹ * ((m-j).factorial:K)⁻¹) from
        Finset.sum_congr rfl (fun j _ => by ring)]
  exact Commons.Algebra.Lie.sum_alternating_conv m hm

lemma expEnd_mul_neg (a : Module.End K V) (ha : ∀ v, ∃ n, (a^n) v = 0)
    (hneg : ∀ v, ∃ n, (((-a)^n) v = 0)) :
    expEnd a ha * expEnd (-a) hneg = 1 := by
  ext v
  rw [Module.End.mul_apply, Module.End.one_apply]
  by_cases hv : v = 0
  · subst hv; simp
  · set N := expIndex a ha (expEnd (-a) hneg v) + (expIndex (-a) hneg v + expIndex a ha v) with hN
    have h1 : expIndex a ha (expEnd (-a) hneg v) ≤ N := by rw [hN]; omega
    have h2 : expIndex (-a) hneg v ≤ N := by rw [hN]; omega
    have h3 : expIndex a ha v ≤ N := by rw [hN]; omega
    have hNpos : 0 < N := by rw [hN]; have := expIndex_pos a ha hv; omega
    have hL : expEnd a ha (expEnd (-a) hneg v)
        = ∑ k ∈ range N, ∑ l ∈ range N,
            (((k.factorial : K))⁻¹ * (((-1:K)^l) * ((l.factorial : K))⁻¹)) • ((a^(k+l)) v) := by
      rw [expEnd_apply, expMap_apply,
          expTrunc_eq_of_le (exp_pow_expIndex a ha (expEnd (-a) hneg v)) h1,
          expEnd_apply, expMap_apply, expTrunc_eq_of_le (exp_pow_expIndex (-a) hneg v) h2]
      simp only [expTrunc_apply]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [map_smul, neg_pow_apply, map_smul, ← Module.End.mul_apply, ← pow_add,
          smul_smul, smul_smul]
      congr 1
      ring
    rw [hL, sum_sum_smul_eq_of_conv (a := fun k => ((k.factorial : K))⁻¹)
        (b := fun l => (-1:K)^l * ((l.factorial : K))⁻¹) (u := fun m => (a^m) v)
        hNpos (fun m hm => exp_pow_eq_zero_of_le (exp_pow_expIndex a ha v) (by omega))
        le_rfl le_rfl (by simp) (fun m hm _ => sum_alt_conv'' m hm)]
    simp

lemma expEnd_neg_mul (a : Module.End K V) (ha : ∀ v, ∃ n, (a^n) v = 0)
    (hneg : ∀ v, ∃ n, (((-a)^n) v = 0)) :
    expEnd (-a) hneg * expEnd a ha = 1 := by
  ext v
  rw [Module.End.mul_apply, Module.End.one_apply]
  by_cases hv : v = 0
  · subst hv; simp
  · set N := expIndex (-a) hneg (expEnd a ha v) + (expIndex a ha v + expIndex (-a) hneg v) with hN
    have h1 : expIndex (-a) hneg (expEnd a ha v) ≤ N := by rw [hN]; omega
    have h2 : expIndex a ha v ≤ N := by rw [hN]; omega
    have h3 : expIndex (-a) hneg v ≤ N := by rw [hN]; omega
    have hNpos : 0 < N := by rw [hN]; have := expIndex_pos a ha hv; omega
    have hL : expEnd (-a) hneg (expEnd a ha v)
        = ∑ k ∈ range N, ∑ l ∈ range N,
            ((((-1:K)^k * ((k.factorial : K))⁻¹) * ((l.factorial : K))⁻¹)) • ((a^(k+l)) v) := by
      rw [expEnd_apply, expMap_apply,
          expTrunc_eq_of_le (exp_pow_expIndex (-a) hneg (expEnd a ha v)) h1,
          expEnd_apply, expMap_apply, expTrunc_eq_of_le (exp_pow_expIndex a ha v) h2]
      simp only [expTrunc_apply]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [map_smul, neg_pow_apply, ← Module.End.mul_apply, ← pow_add,
          smul_smul, smul_smul]
      congr 1
      ring
    rw [hL, sum_sum_smul_eq_of_conv (a := fun k => (-1:K)^k * ((k.factorial:K))⁻¹)
        (b := fun l => ((l.factorial : K))⁻¹) (u := fun m => (a^m) v)
        hNpos (fun m hm => exp_pow_eq_zero_of_le (exp_pow_expIndex a ha v) (by omega))
        le_rfl le_rfl (by simp)
        (fun m hm _ => Commons.Algebra.Lie.sum_alternating_conv m hm)]
    simp

/-! ### The three sl₂ commutation relations -/

lemma sl2_Ah (h e : Module.End K V) (hhe : h * e - e * h = (2 : K) • e)
    (he : ∀ v : V, ∃ n : ℕ, (e ^ n) v = 0) :
    expEnd e he * h = (h - (2 : Module.End K V) * e) * expEnd e he := by
  have had : (adEnd e) h = -((2:K) • e) := by
    rw [adEnd_apply, show e * h - h * e = -(h * e - e * h) from by abel, hhe]
  have had_ee : (adEnd e) e = 0 := by rw [adEnd_apply]; abel
  have had2 : ((adEnd e)^2) h = 0 := by
    rw [pow_two, Module.End.mul_apply, had, map_neg, map_smul, had_ee, smul_zero, neg_zero]
  have hsum : (∑ i ∈ range 2, ((i.factorial : K))⁻¹ • ((adEnd e)^i) h)
      = h - (2 : Module.End K V) * e := by
    have h2 : (2 : Module.End K V) * e = (2:K) • e := by rw [Algebra.smul_def, map_ofNat]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
      pow_one, Module.End.one_apply, one_smul]
    rw [had, ← h2]
    abel
  rw [expEnd_mul_eq_sum e h he (k := 2) had2, hsum]

lemma sl2_Bh (h f : Module.End K V) (hhf : h * f - f * h = -((2 : K) • f))
    (hnf : ∀ v : V, ∃ n : ℕ, (((-f) ^ n) v = 0)) :
    expEnd (-f) hnf * h = (h - (2 : Module.End K V) * f) * expEnd (-f) hnf := by
  have had : (adEnd (-f)) h = -((2:K) • f) := by
    have h1 : (-f) * h - h * (-f) = -(f * h - h * f) := by rw [neg_mul, mul_neg]; abel
    have h2 : f * h - h * f = (2:K) • f := by
      rw [show f * h - h * f = -(h * f - f * h) by abel, hhf, neg_neg]
    rw [adEnd_apply, h1, h2]
  have had_ff : (adEnd (-f)) f = 0 := by rw [adEnd_apply]; simp only [mul_neg, neg_mul]; abel
  have had2 : ((adEnd (-f))^2) h = 0 := by
    rw [pow_two, Module.End.mul_apply, had, map_neg, map_smul, had_ff, smul_zero, neg_zero]
  have hsum : (∑ i ∈ range 2, ((i.factorial : K))⁻¹ • ((adEnd (-f))^i) h)
      = h - (2 : Module.End K V) * f := by
    have h2 : (2 : Module.End K V) * f = (2:K) • f := by rw [Algebra.smul_def, map_ofNat]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
      pow_one, Module.End.one_apply, one_smul]
    rw [had, ← h2]
    abel
  rw [expEnd_mul_eq_sum (-f) h hnf (k := 2) had2, hsum]

lemma sl2_Be (h e f : Module.End K V) (hhf : h * f - f * h = -((2 : K) • f))
    (hef : e * f - f * e = h) (hnf : ∀ v : V, ∃ n : ℕ, (((-f) ^ n) v = 0)) :
    expEnd (-f) hnf * e = (e + h - f) * expEnd (-f) hnf := by
  have had1 : (adEnd (-f)) e = h := by
    rw [adEnd_apply, show (-f)*e - e*(-f) = e*f - f*e from by
      rw [neg_mul, mul_neg]; abel, hef]
  have had2 : (adEnd (-f)) h = -((2:K) • f) := by
    have h1 : (-f) * h - h * (-f) = -(f * h - h * f) := by rw [neg_mul, mul_neg]; abel
    have h2 : f * h - h * f = (2:K) • f := by
      rw [show f * h - h * f = -(h * f - f * h) by abel, hhf, neg_neg]
    rw [adEnd_apply, h1, h2]
  have had_ff : (adEnd (-f)) f = 0 := by rw [adEnd_apply]; simp only [mul_neg, neg_mul]; abel
  have had2h : ((adEnd (-f))^2) h = 0 := by
    rw [pow_two, Module.End.mul_apply, had2, map_neg, map_smul, had_ff, smul_zero, neg_zero]
  have had3 : ((adEnd (-f))^3) e = 0 := by
    rw [show (3:ℕ) = 2 + 1 from by norm_num, pow_add, Module.End.mul_apply, pow_one, had1]
    exact had2h
  have hsq : ((adEnd (-f))^2) e = -((2:K) • f) := by
    rw [pow_two, Module.End.mul_apply, had1, had2]
  have hsum : (∑ i ∈ range 3, ((i.factorial : K))⁻¹ • ((adEnd (-f))^i) e) = e + h - f := by
    rw [show (3:ℕ) = 2 + 1 from by norm_num, Finset.sum_range_succ,
        show (2:ℕ) = 1 + 1 from by norm_num, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
      pow_zero, pow_one, Module.End.one_apply, one_smul]
    rw [had1, hsq, smul_neg, smul_smul]
    have hc : ((Nat.factorial (1+1) : ℕ) : K)⁻¹ * (2:K) = 1 := by
      rw [show ((Nat.factorial (1+1) : ℕ) : K) = (2:K) from by norm_num]
      exact inv_mul_cancel₀ (by norm_num : (2:K) ≠ 0)
    rw [hc, one_smul]
    abel
  rw [expEnd_mul_eq_sum (-f) e hnf (k := 3) had3, hsum]

end ModuleExp

theorem sl2_eigenspace_finrank_symm {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] (h e f : Module.End K V)
    (hhe : h * e - e * h = (2 : K) • e) (hhf : h * f - f * h = -((2 : K) • f))
    (hef : e * f - f * e = h)
    (he : ∀ v : V, ∃ n : ℕ, (e ^ n) v = 0) (hf : ∀ v : V, ∃ n : ℕ, (f ^ n) v = 0)
    (mu : K) :
    Module.finrank K (Module.End.eigenspace h mu) = Module.finrank K (Module.End.eigenspace h (-mu)) := by
  classical
  have hne : ∀ v : V, ∃ n : ℕ, (((-e)^n) v = 0) := neg_locallyNilpotent e he
  have hnf : ∀ v : V, ∃ n : ℕ, (((-f)^n) v = 0) := neg_locallyNilpotent f hf
  have hE1E1' : expEnd e he * expEnd (-e) hne = 1 := expEnd_mul_neg e he hne
  have hE1'E1 : expEnd (-e) hne * expEnd e he = 1 := expEnd_neg_mul e he hne
  have hE2E2' : expEnd (-f) hnf * expEnd f hf = 1 := expEnd_neg_mul f hf hnf
  have hE2'E2 : expEnd f hf * expEnd (-f) hnf = 1 := expEnd_mul_neg f hf hnf
  have hkey : (expEnd e he * expEnd (-f) hnf * expEnd e he) * h
      = -(h * (expEnd e he * expEnd (-f) hnf * expEnd e he)) := by
    have hB : expEnd (-f) hnf * (h - (2:Module.End K V)*e)
        = (-h - (2:Module.End K V)*e) * expEnd (-f) hnf := by
      have h1 : expEnd (-f) hnf * (2:Module.End K V) = (2:Module.End K V) * expEnd (-f) hnf := by
        noncomm_ring
      rw [mul_sub, sl2_Bh h f hhf hnf, ← mul_assoc, h1, mul_assoc,
          sl2_Be h e f hhf hef hnf, ← mul_assoc, ← sub_mul]
      congr 1
      noncomm_ring
    have hA : expEnd e he * (-h - (2:Module.End K V)*e)
        = -((h - (2:Module.End K V)*e) * expEnd e he)
            - ((2:Module.End K V)*e) * expEnd e he := by
      have h1 : expEnd e he * (2:Module.End K V) = (2:Module.End K V) * expEnd e he := by
        noncomm_ring
      rw [mul_sub, mul_neg, sl2_Ah h e hhe he, ← mul_assoc, h1, mul_assoc,
          expEnd_mul_comm e he, ← mul_assoc]
    calc (expEnd e he * expEnd (-f) hnf * expEnd e he) * h
        = expEnd e he * expEnd (-f) hnf * (expEnd e he * h) := by noncomm_ring
      _ = expEnd e he * expEnd (-f) hnf * ((h - (2:Module.End K V)*e) * expEnd e he) := by
            rw [sl2_Ah h e hhe he]
      _ = expEnd e he * (expEnd (-f) hnf * (h - (2:Module.End K V)*e)) * expEnd e he := by
            noncomm_ring
      _ = expEnd e he * ((-h - (2:Module.End K V)*e) * expEnd (-f) hnf) * expEnd e he := by rw [hB]
      _ = (expEnd e he * (-h - (2:Module.End K V)*e)) * expEnd (-f) hnf * expEnd e he := by
            noncomm_ring
      _ = (-((h - (2:Module.End K V)*e) * expEnd e he)
              - ((2:Module.End K V)*e) * expEnd e he)
              * expEnd (-f) hnf * expEnd e he := by rw [hA]
      _ = -((h - (2:Module.End K V)*e) * (expEnd e he * expEnd (-f) hnf * expEnd e he))
            - ((2:Module.End K V)*e) * (expEnd e he * expEnd (-f) hnf * expEnd e he) := by
            noncomm_ring
      _ = -(h * (expEnd e he * expEnd (-f) hnf * expEnd e he)) := by noncomm_ring
  -- Set up the operators
  let θ : Module.End K V := expEnd e he * expEnd (-f) hnf * expEnd e he
  let θ' : Module.End K V := expEnd (-e) hne * expEnd f hf * expEnd (-e) hne
  have hθkey : θ * h = -(h * θ) := hkey
  have hθθ' : θ * θ' = 1 := by
    have e1 : θ * θ' = expEnd e he * expEnd (-f) hnf * (expEnd e he * expEnd (-e) hne)
        * expEnd f hf * expEnd (-e) hne := by
      show (expEnd e he * expEnd (-f) hnf * expEnd e he)
            * (expEnd (-e) hne * expEnd f hf * expEnd (-e) hne) = _
      noncomm_ring
    rw [e1, hE1E1']
    have e2 : expEnd e he * expEnd (-f) hnf * 1 * expEnd f hf * expEnd (-e) hne
        = expEnd e he * (expEnd (-f) hnf * expEnd f hf) * expEnd (-e) hne := by noncomm_ring
    rw [e2, hE2E2']
    have e3 : expEnd e he * 1 * expEnd (-e) hne = expEnd e he * expEnd (-e) hne := by noncomm_ring
    rw [e3, hE1E1']
  have hθ'θ : θ' * θ = 1 := by
    have e1 : θ' * θ = expEnd (-e) hne * expEnd f hf * (expEnd (-e) hne * expEnd e he)
        * expEnd (-f) hnf * expEnd e he := by
      show (expEnd (-e) hne * expEnd f hf * expEnd (-e) hne)
            * (expEnd e he * expEnd (-f) hnf * expEnd e he) = _
      noncomm_ring
    rw [e1, hE1'E1]
    have e2 : expEnd (-e) hne * expEnd f hf * 1 * expEnd (-f) hnf * expEnd e he
        = expEnd (-e) hne * (expEnd f hf * expEnd (-f) hnf) * expEnd e he := by noncomm_ring
    rw [e2, hE2'E2]
    have e3 : expEnd (-e) hne * 1 * expEnd e he = expEnd (-e) hne * expEnd e he := by noncomm_ring
    rw [e3, hE1'E1]
  have hinj : Function.Injective θ := by
    intro a b hab
    have h1 : θ' (θ a) = θ' (θ b) := by rw [hab]
    have h2 : (θ' * θ) a = (θ' * θ) b := by
      rw [Module.End.mul_apply, Module.End.mul_apply]; exact h1
    rw [hθ'θ, Module.End.one_apply, Module.End.one_apply] at h2
    exact h2
  have hsurj : Function.Surjective θ := fun b => ⟨θ' b, by
    rw [← Module.End.mul_apply, hθθ', Module.End.one_apply]⟩
  let θe : V ≃ₗ[K] V := LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩
  have hθe_apply : ∀ x : V, θe x = θ x := fun x => rfl
  have hconj : ∀ w : V, θ (h w) = -(h (θ w)) := by
    intro w
    have := congrArg (fun F : Module.End K V => F w) hθkey
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using this
  have hconj' : ∀ w : V, θ' (h w) = -(h (θ' w)) := by
    have hh : θ' * h = -(h * θ') := by
      have hθh : h * θ = -(θ * h) := by rw [hθkey]; abel
      calc θ' * h = θ' * h * (θ * θ') := by rw [hθθ']; noncomm_ring
        _ = (θ' * (h * θ)) * θ' := by noncomm_ring
        _ = (θ' * (-(θ * h))) * θ' := by rw [hθh]
        _ = -((θ' * θ) * h * θ') := by noncomm_ring
        _ = -(h * θ') := by rw [hθ'θ]; noncomm_ring
    intro w
    have := congrArg (fun F : Module.End K V => F w) hh
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using this
  have hmem1 : ∀ x ∈ Module.End.eigenspace h mu, θ x ∈ Module.End.eigenspace h (-mu) := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have hcx : h (θ x) = -(θ (h x)) := by rw [hconj x]; abel
    rw [hcx, hx, map_smul, neg_smul mu (θ x)]
  have hmem2 : ∀ y ∈ Module.End.eigenspace h (-mu), θ' y ∈ Module.End.eigenspace h mu := by
    intro y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    have hcy : h (θ' y) = -(θ' (h y)) := by rw [hconj' y]; abel
    rw [hcy, hy, map_smul,
        show (-mu) • θ' y = -(mu • θ' y) from neg_smul mu (θ' y), neg_neg]
  have hmap : Submodule.map θe.toLinearMap (Module.End.eigenspace h mu)
      = Module.End.eigenspace h (-mu) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hmem1 x hx
    · intro y hy
      refine Submodule.mem_map.mpr ⟨θ' y, hmem2 y hy, ?_⟩
      show θ (θ' y) = y
      rw [← Module.End.mul_apply, hθθ', Module.End.one_apply]
  rw [← hmap]
  exact LinearEquiv.finrank_eq (LinearEquiv.submoduleMap θe (Module.End.eigenspace h mu))


end Commons.LinearAlgebra.End