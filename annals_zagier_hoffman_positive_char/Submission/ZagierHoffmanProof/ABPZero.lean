import Submission.ZagierHoffmanProof.ABPGauss
import Submission.ZagierHoffmanProof.ABPDiv
import Submission.ZagierHoffmanProof.GenSpecialisation

/-!
# Zero counting for super-entire series (the Jensen/Gauss-norm bound of ABP)

* `exists_isGaussNormAt_of_GSuperEntire` — a super-entire series has a Gauss norm at every
  radius (the value group being archimedean).
-/

set_option autoImplicit false
open Filter Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- **A super-entire series has a Gauss norm at every radius.** -/
theorem exists_isGaussNormAt_of_GSuperEntire {γ : Γ₀} (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) {f : PowerSeries K} (hf : GSuperEntire γ f) (r : Γ₀) :
    ∃ A : Γ₀, IsGaussNormAt r f A := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨Valued.v (PowerSeries.coeff 0 f), ⟨fun n => ?_, ⟨0, by rw [pow_zero, mul_one]⟩⟩⟩
    rcases eq_or_ne n 0 with rfl | hn
    · rw [pow_zero, mul_one]
    · rw [zero_pow hn, mul_zero]
      exact zero_le
  · rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, isGaussNormAt_zero r⟩
    · have hex : ∃ n, PowerSeries.coeff n f ≠ 0 := by
        by_contra h
        push Not at h
        exact hf0 (PowerSeries.ext fun n => by rw [h n, map_zero])
      obtain ⟨n₀, hn₀⟩ := hex
      have hrpos : 0 < r := zero_lt_of_ne_zero hr
      have hv0 : Valued.v (PowerSeries.coeff n₀ f) ≠ 0 := fun hcon =>
        hn₀ ((Valuation.zero_iff Valued.v).mp hcon)
      have hu : 0 < Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ :=
        mul_pos (zero_lt_of_ne_zero hv0) (pow_pos hrpos n₀)
      obtain ⟨M, hM⟩ := harch γ hγ (r⁻¹) (inv_ne_zero hr)
      set M' := max M 1 with hM'def
      have hMle : M ≤ M' := le_max_left M 1
      have hM'1 : 1 ≤ M' := le_max_right M 1
      have hMr : γ ^ M' * r < 1 := by
        have h1 : γ ^ M' ≤ γ ^ M := pow_le_pow_of_le_one zero_le hγ.le hMle
        have h2 : γ ^ M' * r ≤ γ ^ M * r := mul_le_mul_of_nonneg_right h1 zero_le
        have h3 : γ ^ M * r < 1 := by
          have h := mul_lt_mul_of_pos_right hM hrpos
          rwa [inv_mul_cancel₀ hr] at h
        exact lt_of_le_of_lt h2 h3
      obtain ⟨a, ha⟩ := hf M'
      have hdecay : ∀ n : ℕ,
          Valued.v (PowerSeries.coeff n f) * r ^ n ≤ a * (γ ^ M' * r) ^ n := by
        intro n
        calc Valued.v (PowerSeries.coeff n f) * r ^ n ≤ (a * γ ^ (M' * n)) * r ^ n :=
              mul_le_mul_left (ha n) _
          _ = a * (γ ^ M' * r) ^ n := by rw [mul_pow, ← pow_mul, mul_assoc]
      rcases eq_or_ne a 0 with ha0 | ha0
      · exfalso
        have hz : PowerSeries.coeff n₀ f = 0 := by
          have h := ha n₀
          rw [ha0, zero_mul] at h
          exact (Valuation.zero_iff Valued.v).mp (le_antisymm h zero_le)
        exact hn₀ hz
      · have hapos : 0 < a := zero_lt_of_ne_zero ha0
        obtain ⟨N, hN⟩ := harch (γ ^ M' * r) hMr
          (Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ / a) (div_ne_zero (ne_of_gt hu) ha0)
        set N' := max N 1 with hN'def
        have hNN' : N ≤ N' := le_max_left N 1
        have hN'1 : 1 ≤ N' := le_max_right N 1
        have hbase : (γ ^ M' * r) ^ N' ≤ (γ ^ M' * r) ^ N :=
          pow_le_pow_of_le_one zero_le hMr.le hNN'
        have hNu : a * (γ ^ M' * r) ^ N' < Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ := by
          have h1 : a * (γ ^ M' * r) ^ N' ≤ a * (γ ^ M' * r) ^ N := mul_le_mul_right hbase a
          have h2 : a * (γ ^ M' * r) ^ N < Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ := by
            have h := mul_lt_mul_of_pos_right hN hapos
            rw [div_mul_cancel₀ _ ha0, mul_comm ((γ ^ M' * r) ^ N) a] at h
            exact h
          exact lt_of_le_of_lt h1 h2
        have hmem : n₀ ∈ Finset.range N' := by
          rw [Finset.mem_range]
          by_contra hcon
          push Not at hcon
          have h1 : Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ ≤ a * (γ ^ M' * r) ^ n₀ :=
            hdecay n₀
          have h2 : a * (γ ^ M' * r) ^ n₀ ≤ a * (γ ^ M' * r) ^ N' :=
            mul_le_mul_right (pow_le_pow_of_le_one zero_le hMr.le hcon) a
          exact absurd hNu (not_lt.mpr (le_trans h1 h2))
        set A : Γ₀ := (Finset.range N').sup (fun n => Valued.v (PowerSeries.coeff n f) * r ^ n)
          with hA
        refine ⟨A, fun n => ?_, ?_⟩
        · rcases lt_or_ge n N' with hn | hn
          · exact Finset.le_sup (f := fun n => Valued.v (PowerSeries.coeff n f) * r ^ n)
              (Finset.mem_range.mpr hn)
          · have huA : Valued.v (PowerSeries.coeff n₀ f) * r ^ n₀ ≤ A :=
              Finset.le_sup (f := fun m => Valued.v (PowerSeries.coeff m f) * r ^ m) hmem
            refine le_trans ?_ (le_trans (le_of_lt hNu) huA)
            calc Valued.v (PowerSeries.coeff n f) * r ^ n ≤ a * (γ ^ M' * r) ^ n := hdecay n
              _ ≤ a * (γ ^ M' * r) ^ N' :=
                  mul_le_mul_right (pow_le_pow_of_le_one zero_le hMr.le hn) a
        · obtain ⟨n, hn, hne⟩ := Finset.exists_mem_eq_sup (Finset.range N')
            ⟨0, Finset.mem_range.mpr hN'1⟩
            (fun n => Valued.v (PowerSeries.coeff n f) * r ^ n)
          refine ⟨n, ?_⟩
          rw [hA]
          exact hne.symm

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

section divSuper

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- `x⁻¹ * (y * x) = y` in a group with zero. -/
lemma inv_mul_mul_cancel {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x y : Γ₀}
    (hx : x ≠ 0) : x⁻¹ * (y * x) = y := by
  rw [mul_comm y x, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

/-- `a * γ ^ (M * (N+j)) * u ^ (N+j) = (a * γ ^ (M*N) * u ^ N) * (γ ^ M * u) ^ j`. -/
lemma gamma_pow_mul_eq (γ u a : Γ₀) (M N j : ℕ) :
    a * γ ^ (M * (N + j)) * u ^ (N + j) = (a * γ ^ (M * N) * u ^ N) * (γ ^ M * u) ^ j := by
  rw [Nat.mul_add, pow_add, mul_pow, ← pow_mul, pow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Summability of the tails of a super-entire series at a point `c` with `1 ≤ v c`. -/
lemma summable_tail_mul_super {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {c : K} (hc0 : c ≠ 0) {M : ℕ} {a : Γ₀} {f : PowerSeries K}
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a * γ ^ (M * n))
    (hMvc : γ ^ M * Valued.v c < 1) (N : ℕ) :
    Summable fun j : ℕ => PowerSeries.coeff (N + j) f * c ^ (N + j) := by
  refine summable_of_v_le_mul_pow hMvc harch
    (C := a * γ ^ (M * N) * (Valued.v c) ^ N) (fun j => ?_)
  rw [map_mul, map_pow]
  calc Valued.v (PowerSeries.coeff (N + j) f) * (Valued.v c) ^ (N + j)
      ≤ (a * γ ^ (M * (N + j))) * (Valued.v c) ^ (N + j) :=
        mul_le_mul_of_nonneg_right (hf (N + j)) zero_le
    _ = (a * γ ^ (M * N) * (Valued.v c) ^ N) * (γ ^ M * Valued.v c) ^ j := by
        rw [gamma_pow_mul_eq]

/-- The valuation of the `N`-th tail sum. -/
lemma v_tail_le_super {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) {c : K}
    (hc0 : c ≠ 0) {M : ℕ} {a : Γ₀} {f : PowerSeries K}
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a * γ ^ (M * n))
    (hMvc : γ ^ M * Valued.v c < 1) (N : ℕ) :
    Valued.v (∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j))
      ≤ a * γ ^ (M * N) * (Valued.v c) ^ N := by
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
    (summable_tail_mul_super hγ harch hc0 hf hMvc N) (fun j => ?_)
  rw [map_mul, map_pow]
  calc Valued.v (PowerSeries.coeff (N + j) f) * (Valued.v c) ^ (N + j)
      ≤ (a * γ ^ (M * (N + j))) * (Valued.v c) ^ (N + j) :=
        mul_le_mul_of_nonneg_right (hf (N + j)) zero_le
    _ = (a * γ ^ (M * N) * (Valued.v c) ^ N) * (γ ^ M * Valued.v c) ^ j := by
        rw [gamma_pow_mul_eq]
    _ ≤ (a * γ ^ (M * N) * (Valued.v c) ^ N) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le hMvc.le) zero_le
    _ = a * γ ^ (M * N) * (Valued.v c) ^ N := mul_one _

/-- The recursion of the tail sums (super-entire version). -/
lemma tail_rec_super {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) {c : K}
    (hc0 : c ≠ 0) {M : ℕ} {a : Γ₀} {f : PowerSeries K}
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a * γ ^ (M * n))
    (hMvc : γ ^ M * Valued.v c < 1) (N : ℕ) :
    (∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j))
      = PowerSeries.coeff N f * c ^ N
        + ∑' j : ℕ, PowerSeries.coeff (N + 1 + j) f * c ^ (N + 1 + j) := by
  have hg := summable_tail_mul_super hγ harch hc0 hf hMvc N
  have h := hg.tsum_eq_zero_add
  have h1 : PowerSeries.coeff (N + 0) f * c ^ (N + 0) = PowerSeries.coeff N f * c ^ N := by
    rw [Nat.add_zero]
  rw [h, h1]
  refine congrArg (fun x => PowerSeries.coeff N f * c ^ N + x) ?_
  exact tsum_congr (fun j => by rw [show N + (j + 1) = N + 1 + j from by omega])

/-- **Division by `(t - c)` for `1 ≤ v c` preserves super-entireness.** -/
theorem GSuperEntire.exists_quot_X_sub_C {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    {c : K} (hc0 : c ≠ 0) (hc1 : 1 ≤ Valued.v c) {f : PowerSeries K}
    (hf : GSuperEntire γ f) (hroot : evalSeriesGen f c = 0) :
    ∃ g : PowerSeries K, f = (PowerSeries.X - PowerSeries.C c) * g ∧ GSuperEntire γ g := by
  classical
  have hvc0 : Valued.v c ≠ 0 := by simpa using hc0
  obtain ⟨M₀, hM₀⟩ := harch γ hγ (Valued.v c)⁻¹ (inv_ne_zero hvc0)
  have hM₀vc : γ ^ M₀ * Valued.v c < 1 := by
    have h := mul_lt_mul_of_pos_right hM₀ (zero_lt_of_ne_zero hvc0)
    rwa [inv_mul_cancel₀ hvc0] at h
  have hroot' : (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) = 0 := hroot
  have hgcoeff : ∀ n : ℕ, PowerSeries.coeff n (tailQuot f c)
      = (c ^ (n + 1))⁻¹
        * (∑' j : ℕ, PowerSeries.coeff (n + 1 + j) f * c ^ (n + 1 + j)) :=
    fun n => by rw [coeff_tailQuot, tailQuotCoeff]
  have hstep : ∀ M : ℕ, γ ^ (M + M₀) * Valued.v c < 1 := by
    intro M
    have h1 : γ ^ (M + M₀) = γ ^ M * γ ^ M₀ := pow_add γ M M₀
    rw [h1, mul_assoc]
    calc γ ^ M * (γ ^ M₀ * Valued.v c) ≤ 1 * (γ ^ M₀ * Valued.v c) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hγ.le) zero_le
      _ = γ ^ M₀ * Valued.v c := one_mul _
      _ < 1 := hM₀vc
  set T : ℕ → K := fun N => ∑' j : ℕ, PowerSeries.coeff (N + j) f * c ^ (N + j) with hTdef
  have hgc : ∀ n, PowerSeries.coeff n (tailQuot f c) = (c ^ (n + 1))⁻¹ * T (n + 1) :=
    fun n => by rw [hgcoeff n, hTdef]
  have hspec : f = (PowerSeries.X - PowerSeries.C c) * tailQuot f c := by
    obtain ⟨a, ha⟩ := hf M₀
    have hyield : ∀ N, T N = PowerSeries.coeff N f * c ^ N + T (N + 1) := by
      intro N
      rw [hTdef]
      exact tail_rec_super hγ harch hc0 ha hM₀vc N
    have hT0 : T 0 = 0 := by
      simp only [hTdef]
      rw [show (∑' j : ℕ, PowerSeries.coeff (0 + j) f * c ^ (0 + j))
          = ∑' n : ℕ, PowerSeries.coeff n f * c ^ n from
          tsum_congr (fun j => by rw [Nat.zero_add])]
      exact hroot'
    ext n
    symm
    rw [sub_mul, mul_comm (PowerSeries.X) (tailQuot f c), map_sub,
      Commons.RingTheory.PowerSeries.coeff_mul_X, PowerSeries.coeff_C_mul]
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      rw [if_neg (by omega : ¬ (1 ≤ 0)), hgc 0]
      have hr := hyield 0
      rw [hT0, pow_zero, mul_one] at hr
      have hr' : PowerSeries.coeff 0 f + T 1 = 0 := by simpa using hr.symm
      have hT1 : T 1 = -PowerSeries.coeff 0 f := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hr'
      rw [hT1, pow_one]
      field_simp
      ring
    · have h1 : PowerSeries.coeff (n - 1) (tailQuot f c) = (c ^ n)⁻¹ * T n := by
        rw [hgc (n - 1), Nat.sub_add_cancel hn]
      rw [if_pos (show 1 ≤ n from hn), h1, hgc n, hyield n]
      have h2 : c * (c ^ (n + 1))⁻¹ = (c ^ n)⁻¹ := by
        rw [pow_succ]
        field_simp
      rw [← mul_assoc, h2, mul_add,
        show (c ^ n)⁻¹ * (PowerSeries.coeff n f * c ^ n)
          = PowerSeries.coeff n f * ((c ^ n)⁻¹ * c ^ n) from by ring,
        inv_mul_cancel₀ (pow_ne_zero n hc0), mul_one]
      ring
  refine ⟨tailQuot f c, hspec, fun M => ?_⟩
  obtain ⟨a, ha⟩ := hf (M + M₀)
  refine ⟨a * γ ^ (M + M₀), fun n => ?_⟩
  rw [hgc n, map_mul, Valuation.map_inv, map_pow]
  have hvcn : (Valued.v c) ^ (n + 1) ≠ 0 := pow_ne_zero _ hvc0
  calc ((Valued.v c) ^ (n + 1))⁻¹
        * Valued.v (T (n + 1))
      ≤ ((Valued.v c) ^ (n + 1))⁻¹
          * (a * γ ^ ((M + M₀) * (n + 1)) * (Valued.v c) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left
          (v_tail_le_super hγ harch hc0 ha (hstep M) (n + 1)) zero_le
    _ = a * γ ^ ((M + M₀) * (n + 1)) := by
        exact inv_mul_mul_cancel hvcn
    _ = (a * γ ^ (M + M₀)) * γ ^ ((M + M₀) * n) := by
        rw [Nat.mul_succ, pow_add]
        simp only [mul_assoc, mul_comm]
    _ ≤ (a * γ ^ (M + M₀)) * γ ^ (M * n) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one zero_le hγ.le (Nat.mul_le_mul_right n (Nat.le_add_right M M₀)))
          zero_le

end divSuper

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

section zeroCount

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Evaluation of a product of linear factors. -/
lemma evalSeriesGen_prod_X_sub_C {ι : Type*} (t : Finset ι) (ω : ι → K) (c : K) :
    evalSeriesGen (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K) :
        PowerSeries K)) c = ∏ i ∈ t, (c - ω i) := by
  rw [evalSeriesGen_polynomial, Polynomial.eval_prod]
  exact Finset.prod_congr rfl (fun i _ => by
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])

/-- The coercion of a product of linear factors. -/
lemma coe_prod_X_sub_C {ι : Type*} (t : Finset ι) (ω : ι → K) :
    (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K)) : PowerSeries K)
      = ∏ i ∈ t, (PowerSeries.X - PowerSeries.C (ω i)) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.coe_mul,
        Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, ih]

/-- **The zero count bound.**  A nonzero super-entire series has at most boundedly many distinct
zeros in any disc of radius `r' < r` (the bound depends only on the series and on `r, r'`). -/
theorem exists_card_le_of_zeros {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) {f : PowerSeries K} (hf : GSuperEntire γ f) (hf0 : f ≠ 0)
    {r r' : Γ₀} (hr1 : 1 ≤ r') (hrr : r' < r) :
    ∃ N : ℕ, ∀ {ι : Type*} (s : Finset ι) (ω : ι → K),
      (∀ i ∈ s, evalSeriesGen f (ω i) = 0) →
      (∀ i ∈ s, 1 ≤ Valued.v (ω i) ∧ Valued.v (ω i) ≤ r') →
      Set.InjOn ω ↑s → s.card ≤ N := by
  classical
  have hr1' : 1 ≤ r := le_of_lt (lt_of_le_of_lt hr1 hrr)
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1')
  have hratio : r' / r < 1 := by
    rw [div_eq_mul_inv]
    calc r' * r⁻¹ < r * r⁻¹ :=
          mul_lt_mul_of_pos_right hrr (inv_pos_of_pos (lt_of_lt_of_le zero_lt_one hr1'))
      _ = 1 := mul_inv_cancel₀ hrne
  obtain ⟨A, hA⟩ := exists_isGaussNormAt_of_GSuperEntire hγ harch hf r
  have hApos : 0 < A := by
    rcases eq_or_ne A 0 with h0 | h0
    · exfalso
      apply hf0
      ext n
      have h := hA.1 n
      rw [h0] at h
      have hz : Valued.v (PowerSeries.coeff n f) * r ^ n = 0 := le_antisymm h zero_le
      rcases mul_eq_zero.mp hz with h' | h'
      · exact (Valuation.zero_iff Valued.v).mp h'
      · exact absurd h' (pow_ne_zero n hrne)
    · exact zero_lt_of_ne_zero h0
  have hex : ∃ n, PowerSeries.coeff n f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (PowerSeries.ext fun n => by rw [h n, map_zero])
  obtain ⟨m, hm⟩ := hex
  have hvm : Valued.v (PowerSeries.coeff m f) ≠ 0 := fun hcon =>
    hm ((Valuation.zero_iff Valued.v).mp hcon)
  have hvmpos : 0 < Valued.v (PowerSeries.coeff m f) := zero_lt_of_ne_zero hvm
  obtain ⟨N, hN⟩ := harch (r' / r) hratio
    (Valued.v (PowerSeries.coeff m f) / A) (div_ne_zero (ne_of_gt hvmpos) (ne_of_gt hApos))
  refine ⟨N, fun {ι} s ω hroot hb hinj => ?_⟩
  by_contra hcon
  push Not at hcon
  have hdiv : ∀ t : Finset ι, (∀ i ∈ t, evalSeriesGen f (ω i) = 0) →
      (∀ i ∈ t, 1 ≤ Valued.v (ω i) ∧ Valued.v (ω i) ≤ r') → Set.InjOn ω ↑t →
      ∃ G : PowerSeries K,
        f = (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K)) :
          PowerSeries K) * G ∧ GSuperEntire γ G := by
    intro t
    induction t using Finset.induction with
    | empty => intro _ _ _; exact ⟨f, by simp, hf⟩
    | insert a t ha ih =>
      intro hroot' hval' hinj'
      have hroot_t : ∀ i ∈ t, evalSeriesGen f (ω i) = 0 :=
        fun i hi => hroot' i (Finset.mem_insert_of_mem hi)
      have hinj_t : Set.InjOn ω ↑t := hinj'.mono fun x hx => Finset.mem_insert_of_mem hx
      obtain ⟨G, hGf, hGs⟩ := ih hroot_t (fun i hi => hval' i (Finset.mem_insert_of_mem hi)) hinj_t
      have hP : GSuperEntire γ
          (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K)) : PowerSeries K) :=
        GSuperEntire.polynomial hγ0 hγ.le _
      have hPa : evalSeriesGen
          (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K)) :
            PowerSeries K) (ω a) ≠ 0 := by
        rw [evalSeriesGen_prod_X_sub_C]
        intro hz
        rcases Finset.prod_eq_zero_iff.mp hz with ⟨i, hi, hzi⟩
        have hai : a = i := hinj' (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
          (sub_eq_zero.mp hzi)
        exact ha (hai ▸ hi)
      have hGa : evalSeriesGen G (ω a) = 0 := by
        have h1 : evalSeriesGen f (ω a)
            = evalSeriesGen
                (((∏ i ∈ t, (Polynomial.X - Polynomial.C (ω i)) : Polynomial K)) :
                  PowerSeries K) (ω a) * evalSeriesGen G (ω a) := by
          rw [hGf]
          exact evalSeriesGen_mul hγ harch hP hGs (ω a)
        rw [hroot' a (Finset.mem_insert_self a t)] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_left hPa
      have ha0 : ω a ≠ 0 := by
        intro h0
        have h := (hval' a (Finset.mem_insert_self a t)).1
        rw [h0] at h
        simp at h
      obtain ⟨G', hG', hG's⟩ := GSuperEntire.exists_quot_X_sub_C hγ harch ha0
        (hval' a (Finset.mem_insert_self a t)).1 hGs hGa
      refine ⟨G', ?_, hG's⟩
      rw [hGf, hG', Finset.prod_insert ha, Polynomial.coe_mul, Polynomial.coe_sub,
        Polynomial.coe_X, Polynomial.coe_C]
      ring
  obtain ⟨G, hGf, hGs⟩ := hdiv s hroot hb hinj
  obtain ⟨B, hB⟩ := exists_isGaussNormAt_of_GSuperEntire hγ harch hGs r
  have hGf' : f = (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) * G := by
    rw [hGf, coe_prod_X_sub_C]
  have hSJ := v_coeff_le_of_gaussNorm hr1' (fun i hi => (hb i hi).1)
    (fun i hi => le_trans (hb i hi).2 hrr.le) hGf' hA hB m
  have hprod : (∏ i ∈ s, Valued.v (ω i)) ≤ r' ^ s.card := by
    calc (∏ i ∈ s, Valued.v (ω i)) ≤ ∏ _i ∈ s, r' :=
          Finset.prod_le_prod (fun i hi => zero_le) (fun i hi => (hb i hi).2)
      _ = r' ^ s.card := by rw [Finset.prod_const]
  have hfinal : Valued.v (PowerSeries.coeff m f) ≤ A * (r' / r) ^ s.card := by
    calc Valued.v (PowerSeries.coeff m f)
        ≤ (∏ i ∈ s, Valued.v (ω i)) * A * (r ^ s.card)⁻¹ := hSJ
      _ ≤ r' ^ s.card * A * (r ^ s.card)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod zero_le) zero_le
      _ = A * ((r') ^ s.card * (r ^ s.card)⁻¹) := by
          rw [mul_comm (r' ^ s.card) A, mul_assoc]
      _ = A * (r' / r) ^ s.card := by rw [div_pow, div_eq_mul_inv]
  have hsmall : A * (r' / r) ^ s.card < Valued.v (PowerSeries.coeff m f) := by
    have h2 : (r' / r) ^ s.card ≤ (r' / r) ^ N :=
      pow_le_pow_of_le_one zero_le hratio.le (by omega)
    have h3 : A * (r' / r) ^ N < A * (Valued.v (PowerSeries.coeff m f) / A) :=
      mul_lt_mul_of_pos_left hN hApos
    rw [mul_div_cancel₀ _ (ne_of_gt hApos)] at h3
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 zero_le) h3
  exact absurd hfinal (not_le.mpr hsmall)

end zeroCount

end ZagierHoffmanPositiveChar
