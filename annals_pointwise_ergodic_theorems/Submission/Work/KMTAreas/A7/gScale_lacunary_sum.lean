import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open Finset
open Work.Analysis.EndVar (logN)

/-!
# The lacunary sum of the clipped `g`-side frequency scale

Let `gScale d N 0 = 2^{d·Log N}` be the frequency scale of the `g`-side bump at the scale `N`
(`randSymbG_aux.lean`), where `Log N = Nat.log 2 (max N 2) = ⌊log₂ N⌋`
(`Work.Analysis.EndVar.logN`).  The goal of this file is

`gScale_lacunary_sum`: for every lacunary sequence `a` (`a (n+1)/a n > Λ > 1`, `a n ≥ 1`) and
every real `c`, the clipped sum
`∑_{m<L} (c·gScale d ⌊a m⌋ 0)·[c·gScale d ⌊a m⌋ 0 ≤ 1]`
is bounded uniformly in `L`, in `c` and in the lacunary sequence.

The mathematics is a geometric-growth argument.  Since `Λ^j ≥ 4` for some `j`,
`a (m+2j) ≥ Λ^{2j} a m ≥ 16 a m` and therefore `⌊a (m+2j)⌋ ≥ 4·max (⌊a m⌋) 2`, whence
`Log ⌊a (m+2j)⌋ ≥ Log ⌊a m⌋ + 2` and `gScale d ⌊a (m+2j)⌋ 0 ≥ 4 · gScale d ⌊a m⌋ 0`.
So `t m = c·gScale d ⌊a m⌋ 0` is nonnegative and nondecreasing, and grows by a factor `4` every
`2j` steps.  On the (initial) set where `t m ≤ 1` it is therefore dominated by the geometric
sequence `(1/4)^{⌊(M-m)/(2j)⌋}`, whose sum is bounded by `4·(2j)`; beyond that initial set the
summand is `0`.  For `c ≤ 0` all summands are `≤ 0` and the sum is `≤ 0`.

-/

noncomputable section

/-! ## 1. Arithmetic of the `g`-side scale -/

/-- `Log` is monotone in the scale and increases by at least `2` when the scale grows from `N`
to some `N' ≥ 4 · max N 2`. -/
lemma logN_le_of_four_max_le {N N' : ℕ} (h : 4 * max N 2 ≤ N') : logN N + 2 ≤ logN N' := by
  have hMpos : max N 2 ≠ 0 := by omega
  have hN' : max N' 2 = N' := by omega
  have key : Nat.log 2 (max N 2) + 2 ≤ Nat.log 2 N' := by
    have hmono : Nat.log 2 (4 * max N 2) ≤ Nat.log 2 N' := Nat.log_monotone h
    rw [show (4:ℕ) * max N 2 = (max N 2 * 2) * 2 by ring] at hmono
    rw [Nat.log_mul_base (by norm_num) (by omega : max N 2 * 2 ≠ 0),
        Nat.log_mul_base (by norm_num) hMpos] at hmono
    omega
  rw [logN, logN, hN']
  omega

/-- The `g`-side scale is positive. -/
lemma gScale_pos (d N : ℕ) : 0 < gScale d N 0 := by
  rw [gScale]
  exact zpow_pos (by norm_num) _

/-- The `g`-side scale is monotone in the logarithmic scale. -/
lemma gScale_mono_logN (d : ℕ) {N N' : ℕ} (h : logN N ≤ logN N') :
    gScale d N 0 ≤ gScale d N' 0 := by
  rw [gScale, gScale]
  apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  simpa using mul_le_mul_of_nonneg_left h (Int.natCast_nonneg d)

/-- The `g`-side scale at `k₂ = 0` is `2 ^ (d · Log N)`. -/
lemma gScale_eq (d N : ℕ) : gScale d N 0 = (2:ℝ) ^ ((d:ℤ) * logN N) := by
  rw [gScale]
  simp

/-- Growth of the `g`-side scale: `Log` up by `2` multiplies `gScale d · 0` by at least `4`
(for `d ≥ 1`). -/
lemma gScale_four_le (d : ℕ) (hd : 1 ≤ d) {N N' : ℕ} (h : logN N + 2 ≤ logN N') :
    4 * gScale d N 0 ≤ gScale d N' 0 := by
  rw [gScale_eq, gScale_eq]
  have h2 : (2:ℤ) ≤ logN N' - logN N := by omega
  have hB : (2:ℤ) ≤ (d:ℤ) * (logN N' - logN N) := by
    have hd1 : (1:ℤ) ≤ (d:ℤ) := by omega
    calc (2:ℤ) = 1 * 2 := by ring
      _ ≤ (d:ℤ) * (logN N' - logN N) := mul_le_mul hd1 h2 (by omega) (by omega)
  have hsum : (d:ℤ) * logN N' = (d:ℤ) * logN N + (d:ℤ) * (logN N' - logN N) := by ring
  have h4 : (4:ℝ) ≤ (2:ℝ) ^ ((d:ℤ) * (logN N' - logN N)) := by
    have hh := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hB
    have h22 : (2:ℝ) ^ ((2:ℤ)) = 4 := by norm_num
    rwa [h22] at hh
  rw [hsum, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have hpos : (0:ℝ) ≤ (2:ℝ) ^ ((d:ℤ) * logN N) := by positivity
  calc 4 * (2:ℝ) ^ ((d:ℤ) * logN N)
      = (2:ℝ) ^ ((d:ℤ) * logN N) * 4 := by ring
    _ ≤ (2:ℝ) ^ ((d:ℤ) * logN N) * (2:ℝ) ^ ((d:ℤ) * (logN N' - logN N)) :=
        mul_le_mul_of_nonneg_left h4 hpos

/-! ## 2. Growth of the floors of a lacunary sequence -/

/-- The product form of lacunarity. -/
lemma lacunary_prod_form (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (hlac : PointwiseErgodicTheorems.Lacunary Λ a) : ∀ n, Λ * a n ≤ a (n + 1) := by
  intro n
  have hpos : (0:NNReal) < a n := by
    by_contra h
    push_neg at h
    have hz : a n = 0 := le_antisymm h zero_le
    have hcontra := hlac n
    rw [hz, div_zero] at hcontra
    exact absurd hcontra (not_lt.mpr (show (0:NNReal) ≤ Λ from zero_le))
  have h1 : ((Λ:NNReal) : ℝ) < ((a (n+1) / a n : NNReal) : ℝ) := by exact_mod_cast hlac n
  rw [NNReal.coe_div] at h1
  have hnpos : (0:ℝ) < (a n : ℝ) := by exact_mod_cast hpos
  have h2 : (Λ:ℝ) * (a n : ℝ) < (a (n+1) : ℝ) := (lt_div_iff₀ hnpos).mp h1
  exact NNReal.coe_le_coe.mp (by push_cast; exact h2.le)

/-- Growth of the floors: if `Λ^j ≥ 4` then `⌊a (m+2j)⌋ ≥ 4 · max ⌊a m⌋ 2` for a lacunary `a`
with `a n ≥ 1`. -/
lemma lacunary_floor_growth (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (hlac : ∀ n, Λ * a n ≤ a (n + 1)) (ha : ∀ n, 1 ≤ a n)
    {j : ℕ} (hj : (4:ℝ) ≤ (Λ:ℝ)^j) (m : ℕ) :
    4 * max (Nat.floor (a m)) 2 ≤ Nat.floor (a (m + 2*j)) := by
  have hpow : (16:NNReal) ≤ Λ ^ (2*j) := by
    have h16 : (16:ℝ) ≤ (Λ:ℝ) ^ (2*j) := by
      have hp : (4:ℝ)^2 ≤ ((Λ:ℝ)^j)^2 := pow_le_pow_left₀ (by norm_num) hj 2
      have hmul : ((Λ:ℝ)^j)^2 = (Λ:ℝ)^(2*j) := by rw [← pow_mul]; ring_nf
      calc (16:ℝ) = 4^2 := by norm_num
        _ ≤ ((Λ:ℝ)^j)^2 := hp
        _ = (Λ:ℝ)^(2*j) := hmul
    exact NNReal.coe_le_coe.mp (by push_cast; exact h16)
  have hiter : ∀ k : ℕ, ((Λ:NNReal)^k) * a m ≤ a (m + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (Λ:NNReal)^(k+1) * a m = Λ * ((Λ:NNReal)^k * a m) := by rw [pow_succ']; ring
          _ ≤ Λ * a (m + k) := mul_le_mul_of_nonneg_left ih (show (0:NNReal) ≤ Λ from zero_le)
          _ ≤ a ((m + k) + 1) := hlac (m + k)
          _ = a (m + (k+1)) := by rw [show (m+k) + 1 = m + (k+1) by omega]
  have hbig : (16:NNReal) * a m ≤ a (m + 2*j) :=
    le_trans (mul_le_mul_of_nonneg_right hpow (show (0:NNReal) ≤ a m from zero_le)) (hiter (2*j))
  apply (Nat.le_floor_iff (show (0:NNReal) ≤ a (m + 2*j) from zero_le)).mpr
  push_cast
  have ham0 : (0:NNReal) ≤ a m := zero_le
  have hmaxle : max ((Nat.floor (a m) : ℕ) : NNReal) 2 ≤ 4 * a m := by
    refine max_le ?_ ?_
    · have h1 : ((Nat.floor (a m) : ℕ) : NNReal) ≤ a m := Nat.floor_le ham0
      linarith
    · linarith [ha m]
  calc 4 * max ((Nat.floor (a m) : ℕ) : NNReal) 2 ≤ 4 * (4 * a m) :=
        mul_le_mul_of_nonneg_left hmaxle (by norm_num)
    _ = 16 * a m := by ring
    _ ≤ a (m + 2*j) := hbig

/-- **Growth of the `g`-side scale along a lacunary sequence.**  If `Λ^j ≥ 4` and `d ≥ 1` then
the scale grows by a factor at least `4` at distance `2j` in the index. -/
lemma lacunary_gScale_growth (d : ℕ) (hd : 1 ≤ d) (Λ : NNReal) (hΛ : 1 < Λ)
    (a : ℕ → NNReal) (hlac : PointwiseErgodicTheorems.Lacunary Λ a) (ha : ∀ n, 1 ≤ a n)
    {j : ℕ} (hj : (4 : ℝ) ≤ (Λ : ℝ) ^ j) (m : ℕ) :
    4 * gScale d (Nat.floor (a m)) 0 ≤ gScale d (Nat.floor (a (m + 2 * j))) 0 :=
  gScale_four_le d hd (logN_le_of_four_max_le
    (lacunary_floor_growth Λ hΛ a (lacunary_prod_form Λ hΛ a hlac) ha hj m))

/-- Positivity of the `g`-side scale and its monotonicity along the floors of a lacunary
sequence. -/
lemma gScale_mono_lacunary (d : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (hlac : PointwiseErgodicTheorems.Lacunary Λ a) :
    (∀ N : ℕ, 0 < gScale d N 0) ∧ Monotone (fun m => gScale d (Nat.floor (a m)) 0) := by
  refine ⟨fun N => gScale_pos d N, ?_⟩
  have hprod := lacunary_prod_form Λ hΛ a hlac
  have hmono_a : Monotone a := monotone_nat_of_le_succ fun n =>
    le_trans (le_mul_of_one_le_left zero_le hΛ.le) (hprod n)
  exact fun m m' h =>
    gScale_mono_logN d (Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hmono_a h)))

/-! ## 3. The combinatorial bound -/

/-- Iterated geometric growth. -/
private lemma geom_iter {B : ℕ} {t : ℕ → ℝ} (hgr : ∀ m, 4 * t m ≤ t (m + B)) (k m : ℕ) :
    (4 : ℝ) ^ k * t m ≤ t (m + k * B) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      have hidx : m + (k + 1) * B = (m + k * B) + B := by ring
      calc (4:ℝ) ^ (k+1) * t m = 4 * ((4:ℝ)^k * t m) := by ring
        _ ≤ 4 * t (m + k * B) := mul_le_mul_of_nonneg_left (ih m) (by norm_num)
        _ ≤ t ((m + k * B) + B) := hgr (m + k * B)
        _ = t (m + (k+1) * B) := by rw [hidx]

/-- Block decomposition of the sum of `(1/4)^{⌊d/B⌋}` over `d < q*B`. -/
private lemma block_sum_quarter {B q : ℕ} (hB : 0 < B) :
    ∑ d ∈ Finset.range (q * B), (1 / 4 : ℝ) ^ (d / B)
      = (B : ℝ) * ∑ i ∈ Finset.range q, (1 / 4 : ℝ) ^ i := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hsplit : (q+1) * B = q * B + B := by ring
      rw [hsplit, Finset.sum_range_add, ih]
      have hinner : ∑ d ∈ Finset.range B, (1/4:ℝ) ^ ((q*B + d) / B)
          = (B:ℝ) * (1/4:ℝ)^q := by
        have hcongr : ∀ d ∈ Finset.range B, (1/4:ℝ) ^ ((q*B + d) / B) = (1/4:ℝ)^q := by
          intro d hd
          have hdB : d < B := Finset.mem_range.mp hd
          have hdiv : (q*B + d) / B = q := by
            rw [Nat.add_comm (q*B) d, Nat.mul_comm q B, Nat.add_mul_div_left d q hB,
                Nat.div_eq_of_lt hdB, Nat.zero_add]
          rw [hdiv]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hinner, Finset.sum_range_succ]
      ring

/-- The truncated geometric series with ratio `1/4` is bounded by `4/3`. -/
private lemma geom_sum_quarter_le (q : ℕ) : ∑ i ∈ Finset.range q, (1/4:ℝ)^i ≤ 4/3 := by
  have hsumm : Summable (fun i : ℕ => (1/4:ℝ)^i) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h := Summable.sum_le_tsum (Finset.range q) (fun i _ => by positivity) hsumm
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)] at h
  norm_num at h ⊢
  exact h

/-- **The sum over an initial segment.**  If `t ≥ 0` is nondecreasing and grows by a factor `4`
every `B` steps, and `t M ≤ 1`, then `∑_{m ≤ M} t m ≤ 4 B`. -/
private lemma clipped_prefix_sum {B : ℕ} (hB : 0 < B) {t : ℕ → ℝ} (ht0 : ∀ m, 0 ≤ t m)
    (htmono : Monotone t) (hgr : ∀ m, 4 * t m ≤ t (m + B)) (M : ℕ) (hM : t M ≤ 1) :
    ∑ m ∈ Finset.range (M + 1), t m ≤ 4 * (B : ℝ) := by
  have hkey : ∀ m ≤ M, t m ≤ (1/4:ℝ) ^ ((M - m) / B) := by
    intro m hm
    have hidx : m + ((M - m) / B) * B ≤ M := by
      have := Nat.div_mul_le_self (M - m) B
      omega
    have h1 : (4:ℝ) ^ ((M-m)/B) * t m ≤ t (m + ((M-m)/B) * B) := geom_iter hgr _ m
    have h2 : (4:ℝ) ^ ((M-m)/B) * t m ≤ 1 :=
      le_trans h1 (le_trans (htmono hidx) hM)
    have hpos : (0:ℝ) < (4:ℝ) ^ ((M-m)/B) := by positivity
    have h3 : t m ≤ ((4:ℝ) ^ ((M-m)/B))⁻¹ := by
      have hinv : ((4:ℝ)^((M-m)/B))⁻¹ * ((4:ℝ)^((M-m)/B) * t m) = t m := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      rw [← hinv]
      simpa using mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hpos))
    have h4 : ((4:ℝ)^((M-m)/B))⁻¹ = (1/4:ℝ)^((M-m)/B) := by
      rw [← inv_pow]; norm_num
    rwa [h4] at h3
  have hreflect : ∑ m ∈ Finset.range (M + 1), (1/4:ℝ) ^ ((M-m)/B)
      = ∑ d ∈ Finset.range (M + 1), (1/4:ℝ) ^ (d/B) := by
    have h1 : ∑ m ∈ Finset.range (M + 1), (1/4:ℝ) ^ ((M-m)/B)
        = ∑ j ∈ Finset.range (M + 1), (1/4:ℝ) ^ ((M + 1 - 1 - j)/B) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjj : M + 1 - 1 - j = M - j := by omega
      rw [hjj]
    rw [h1, Finset.sum_range_reflect (f := fun d => (1/4:ℝ) ^ (d/B)) (n := M + 1)]
  calc ∑ m ∈ Finset.range (M + 1), t m
      ≤ ∑ m ∈ Finset.range (M + 1), (1/4:ℝ) ^ ((M-m)/B) :=
        Finset.sum_le_sum fun m hm => hkey m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    _ = ∑ d ∈ Finset.range (M + 1), (1/4:ℝ) ^ (d/B) := hreflect
    _ ≤ ∑ d ∈ Finset.range (((M+1)/B + 1) * B), (1/4:ℝ) ^ (d/B) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_range] at hx ⊢
          have hlt : (M+1)/B < (M+1)/B + 1 := Nat.lt_succ_self _
          have := (Nat.div_lt_iff_lt_mul hB).mp hlt
          omega
        · intro x _ _
          positivity
    _ = (B:ℝ) * ∑ i ∈ Finset.range ((M+1)/B + 1), (1/4:ℝ) ^ i := block_sum_quarter hB
    _ ≤ (B:ℝ) * (4/3) := by
        have h := geom_sum_quarter_le ((M+1)/B + 1)
        have hBnn : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg B
        exact mul_le_mul_of_nonneg_left h hBnn
    _ ≤ 4 * (B:ℝ) := by
        have hBnn : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg B
        linarith

/-- **The clipped sum.**  For `t ≥ 0` nondecreasing and growing by a factor `4` every `B` steps,
the sum of `t m` over the indices with `t m ≤ 1` is at most `4 B`, uniformly in `L`. -/
private lemma sum_clipped_le {B : ℕ} (hB : 0 < B) {t : ℕ → ℝ} (ht0 : ∀ m, 0 ≤ t m)
    (htmono : Monotone t) (hgr : ∀ m, 4 * t m ≤ t (m + B)) (L : ℕ) :
    ∑ m ∈ Finset.range L, (if t m ≤ 1 then t m else 0) ≤ 4 * (B : ℝ) := by
  set S : Finset ℕ := (Finset.range L).filter (fun m => t m ≤ 1) with hSdef
  have hsum_eq : ∑ m ∈ Finset.range L, (if t m ≤ 1 then t m else 0) = ∑ m ∈ S, t m := by
    rw [hSdef]
    simp only [Finset.sum_filter]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hsum_eq, hSe, Finset.sum_empty]
    positivity
  · obtain ⟨M, hMmem, hMmax⟩ : ∃ M, M ∈ S ∧ ∀ m ∈ S, m ≤ M :=
      ⟨S.max' hSne, S.max'_mem hSne, fun m hm => Finset.le_max' S m hm⟩
    have hMt : t M ≤ 1 := (Finset.mem_filter.mp hMmem).2
    have hML : M < L := Finset.mem_range.mp (Finset.mem_filter.mp hMmem).1
    have hSrange : S = Finset.range (M + 1) := by
      ext m
      simp only [Finset.mem_range]
      constructor
      · intro hm
        exact Nat.lt_succ_of_le (hMmax m hm)
      · intro hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), le_trans (htmono (Nat.le_of_lt_succ hm)) hMt⟩
    rw [hsum_eq, hSrange]
    exact clipped_prefix_sum hB ht0 htmono hgr M hMt

/-! ## 4. The theorem -/

theorem gScale_lacunary_sum (d : ℕ) (hd : 1 ≤ d) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a →
      (∀ n, 1 ≤ a n) → ∀ (c : ℝ) (L : ℕ),
      ∑ m ∈ Finset.range L,
        (if c * gScale d (Nat.floor (a m)) 0 ≤ 1 then c * gScale d (Nat.floor (a m)) 0 else 0) ≤ C := by
  have hΛ1 : (1:ℝ) < (Λ:ℝ) := by exact_mod_cast hΛ
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (4:ℝ) ≤ (Λ:ℝ)^j := by
    have htend : Filter.Tendsto (fun n : ℕ => (Λ:ℝ)^n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hΛ1
    have hev : ∀ᶠ n : ℕ in Filter.atTop, (4:ℝ) ≤ (Λ:ℝ)^n :=
      htend (Filter.eventually_ge_atTop 4)
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
    exact ⟨n, hn n le_rfl⟩
  have hjpos : 1 ≤ j := by
    by_contra h
    interval_cases j
    · norm_num at hj
  refine ⟨4 * ((2*j : ℕ) : ℝ), by positivity, ?_⟩
  intro a hlac ha c L
  have hsm := gScale_mono_lacunary d Λ hΛ a hlac
  have hmono : Monotone (fun m => gScale d (Nat.floor (a m)) 0) := hsm.2
  have hgpos : ∀ N : ℕ, 0 < gScale d N 0 := hsm.1
  by_cases hc : c ≤ 0
  · have hle0 : ∑ m ∈ Finset.range L,
        (if c * gScale d (Nat.floor (a m)) 0 ≤ 1
          then c * gScale d (Nat.floor (a m)) 0 else 0) ≤ 0 := by
      apply Finset.sum_nonpos
      intro m _
      have hg := hgpos (Nat.floor (a m))
      have hneg : c * gScale d (Nat.floor (a m)) 0 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc hg.le
      by_cases h : c * gScale d (Nat.floor (a m)) 0 ≤ 1
      · rw [if_pos h]; exact hneg
      · rw [if_neg h]
    refine le_trans hle0 ?_
    positivity
  · push_neg at hc
    have ht0 : ∀ m, 0 ≤ c * gScale d (Nat.floor (a m)) 0 := fun m =>
      mul_nonneg hc.le (hgpos _).le
    have htmono : Monotone (fun m => c * gScale d (Nat.floor (a m)) 0) := fun m m' h =>
      mul_le_mul_of_nonneg_left (hmono h) hc.le
    have hgr : ∀ m, 4 * (c * gScale d (Nat.floor (a m)) 0)
        ≤ c * gScale d (Nat.floor (a (m + 2*j))) 0 := by
      intro m
      have hg := lacunary_gScale_growth d hd Λ hΛ a hlac ha hj m
      calc 4 * (c * gScale d (Nat.floor (a m)) 0)
          = c * (4 * gScale d (Nat.floor (a m)) 0) := by ring
        _ ≤ c * gScale d (Nat.floor (a (m + 2*j))) 0 := mul_le_mul_of_nonneg_left hg hc.le
    exact sum_clipped_le (B := 2*j) (by omega) ht0 htmono hgr L

end

end Work.KMTAreas.A7
