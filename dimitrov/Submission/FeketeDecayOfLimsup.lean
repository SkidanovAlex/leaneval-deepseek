import Mathlib
import Submission.FeketeLim

/-!
# Isolated task: generic "root-limsup <= rho0 < 1 ⟹ geometric Fekete decay"

Self-contained statements (import Submission.FeketeLim).  Prove the lemma
below.  This is the
mechanical step-6 conversion of the SS1 route: given that the Fekete root
limsup of a bounded set `K` is at most `ρ0 < 1`, its Fekete numbers decay
geometrically in the pair-count exponent:

    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n ≥ 1, feketeNumber K n ≤ C · ρ^(n(n−1)/2)

Proof structure:

* Pick `ρ := (ρ0 + 1)/2` (so `0 ≤ ρ < 1` and `ρ0 < ρ`).
* For *bounded nonempty* `K`: bound the root terms above (`feketeRoot_bounded`)
  so `IsBoundedUnder` holds, use `Filter.eventually_lt_of_limsup_lt` to get
  the root terms eventually `< ρ`, raise to the pair-count power
  (`Real.rpow_mul` + the exponent identity `((n+1)·n/2)·(2/((n+1)·n)) = 1`)
  to obtain `m_{n+1} ≤ ρ^((n+1)·n/2)` for all large `n`, and absorb the
  finite prefix into a constant `C`.
* For the degenerate cases (`K = ∅` or `K` unbounded) the Fekete numbers are
  zero (junk `sSup` conventions: `Real.sSup_empty`,
  `Real.sSup_of_not_bddAbove`); an unbounded `K` contains arbitrarily far
  points, giving pairwise-far configurations and hence unbounded Vandermonde
  products, so `m_k = 0` for `k ≥ 2` (`m_1 = 1` for nonempty `K`).

The `sSup` junk convention (`sSup s = 0` when `s` is empty or unbounded
above) makes `feketeNumber K n ≥ 0` unconditionally
(`feketeNumber_nonneg_all`), which is all the nonnegativity we need.
-/

noncomputable section
open scoped Real Polynomial Topology BigOperators

namespace Submission.FeketeDecayOfLimsup

open Filter
open Submission.FeketeLim

lemma feketeNumber_nonneg_all (K : Set ℂ) (n : ℕ) : 0 ≤ feketeNumber K n := by
  classical
  unfold feketeNumber
  let S : Set ℝ := feketeSet K n
  change 0 ≤ sSup S
  have hSsub : ∀ d ∈ S, 0 ≤ d := by
    intro d hd
    rcases hd with ⟨x, hx, rfl⟩
    exact vdm_nonneg x n
  by_cases hne : S.Nonempty
  · by_cases hb : BddAbove S
    · rcases hne with ⟨d, hd⟩
      exact le_trans (hSsub d hd) (le_csSup hb hd)
    · rw [Real.sSup_of_not_bddAbove hb]
  · have hS : S = ∅ := (Set.not_nonempty_iff_eq_empty).mp hne
    rw [hS, Real.sSup_empty]

/-- An unbounded set contains points of arbitrarily large norm. -/
lemma unbounded_norm {K : Set ℂ} (hK : ¬ Bornology.IsBounded K) :
    ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖ := by
  intro R
  by_contra h
  push_neg at h
  have hb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (c := (0 : ℂ))]
    refine ⟨max R 0, ?_⟩
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (h z hz) (le_max_left R 0)
  exact hK hb

/-- A point of `K` with norm bigger than any given threshold. -/
noncomputable def farPoint {K : Set ℂ} (hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖) (R : ℝ) : ℂ :=
  Classical.choose (hK R)

lemma farPoint_spec {K : Set ℂ} (hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖) (R : ℝ) :
    farPoint hK R ∈ K ∧ R < ‖farPoint hK R‖ :=
  Classical.choose_spec (hK R)

/-- A sequence in `K` whose norms grow strictly (gaps at least `L`). -/
noncomputable def zSeq {K : Set ℂ} (hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖) (L : ℝ) : ℕ → ℂ
  | 0 => farPoint hK 0
  | n + 1 => farPoint hK (‖zSeq hK L n‖ + L)

lemma zSeq_mem {K : Set ℂ} (hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖) (L : ℝ) (n : ℕ) :
    zSeq hK L n ∈ K := by
  induction n with
  | zero => exact (farPoint_spec hK 0).1
  | succ n ih =>
      change farPoint hK (‖zSeq hK L n‖ + L) ∈ K
      exact (farPoint_spec hK (‖zSeq hK L n‖ + L)).1

lemma zSeq_norm_succ {K : Set ℂ} (hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖) (L : ℝ) (n : ℕ) :
    ‖zSeq hK L n‖ + L < ‖zSeq hK L (n + 1)‖ := by
  change ‖zSeq hK L n‖ + L < ‖farPoint hK (‖zSeq hK L n‖ + L)‖
  exact (farPoint_spec hK (‖zSeq hK L n‖ + L)).2

lemma zSeq_norm_ge {K : Set ℂ} {hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖} {L : ℝ} (hL : 0 ≤ L) :
    ∀ i j : ℕ, j < i → ‖zSeq hK L j‖ + L ≤ ‖zSeq hK L i‖ := by
  intro i
  induction i with
  | zero =>
      intro j hj
      omega
  | succ i ih =>
      intro j hj
      by_cases hji : j = i
      · subst j
        exact le_of_lt (zSeq_norm_succ hK L i)
      · have hji' : j < i := lt_of_le_of_ne (Nat.le_of_lt_succ hj) hji
        have hprev := ih j hji'
        have hmono : ‖zSeq hK L i‖ ≤ ‖zSeq hK L (i + 1)‖ := by
          have h := zSeq_norm_succ hK L i
          nlinarith
        exact le_trans hprev hmono

/-- `zSeq` values are pairwise at least `L` apart (in norm). -/
lemma zSeq_pairwise {K : Set ℂ} {hK : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖} {L : ℝ} (hL : 0 ≤ L) :
    ∀ i : ℕ, ∀ j : ℕ, j < i → L ≤ ‖zSeq hK L j - zSeq hK L i‖ := by
  intro i j hji
  have hn := zSeq_norm_ge (hK := hK) (L := L) hL i j hji
  have hrev := norm_sub_norm_le (zSeq hK L i) (zSeq hK L j)
  have hnorm : ‖zSeq hK L i‖ - ‖zSeq hK L j‖ ≤ ‖zSeq hK L j - zSeq hK L i‖ := by
    calc
      ‖zSeq hK L i‖ - ‖zSeq hK L j‖ ≤ ‖zSeq hK L i - zSeq hK L j‖ := hrev
      _ = ‖zSeq hK L j - zSeq hK L i‖ := norm_sub_rev _ _
  nlinarith

/-- If all `f i` are at least `L ≥ 0`, the product is at least `L^card`. -/
lemma pow_card_le_prod (s : Finset ℕ) (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hfL : ∀ i ∈ s, L ≤ f i) : L ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      have hfa : L ≤ f a := hfL a (by simp)
      have hfs : ∀ i ∈ s, L ≤ f i := fun i hi => hfL i (by simp [hi])
      have hprod0 : 0 ≤ ∏ i ∈ s, f i := by
        refine Finset.prod_nonneg ?_
        intro i hi
        exact le_trans hL (hfL i (by simp [hi]))
      calc
        L ^ (insert a s).card = L ^ (s.card + 1) := by rw [Finset.card_insert_of_notMem has]
        _ = L ^ s.card * L := by rw [pow_succ]
        _ ≤ (∏ i ∈ s, f i) * f a := by
              exact mul_le_mul (ih hfs) hfa hL hprod0
        _ = ∏ i ∈ insert a s, f i := by
              rw [Finset.prod_insert has]
              exact (mul_comm _ _).symm

/-- Vandermonde of a configuration whose first `n` pairs are at least `L`
apart is at least `L` to the number-of-pairs power. -/
lemma vdm_lower_bound (x : ℕ → ℂ) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ i : ℕ, i < n → ∀ j : ℕ, j < i → L ≤ ‖x j - x i‖) :
    L ^ (∑ i ∈ Finset.range n, i) ≤ vdm x n := by
  unfold vdm
  induction n with
  | zero => simp
  | succ n ih =>
      have h' : ∀ i : ℕ, i < n → ∀ j : ℕ, j < i → L ≤ ‖x j - x i‖ := by
        intro i hi j hji
        exact h i (by omega) j hji
      have hinner : L ^ n ≤ ∏ j ∈ Finset.range n, ‖x j - x n‖ := by
        simpa using
          (pow_card_le_prod (Finset.range n) (fun j => ‖x j - x n‖) L hL (by
            intro j hj
            have hjlt : j < n := by simpa using hj
            exact h n (by omega) j hjlt))
      have hprod_nonneg : 0 ≤ ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖ := by
        refine Finset.prod_nonneg ?_
        intro i hi
        refine Finset.prod_nonneg ?_
        intro j hj
        exact norm_nonneg _
      have hprod := ih h'
      calc
        L ^ (∑ i ∈ Finset.range (n + 1), i) = L ^ ((∑ i ∈ Finset.range n, i) + n) := by
              rw [Finset.sum_range_succ]
        _ = L ^ (∑ i ∈ Finset.range n, i) * L ^ n := by rw [pow_add]
        _ ≤ (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖) *
              (∏ j ∈ Finset.range n, ‖x j - x n‖) := by
              exact mul_le_mul hprod hinner (pow_nonneg hL n) hprod_nonneg
        _ = ∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range i, ‖x j - x i‖ := by
              rw [Finset.prod_range_succ]


/-- For `K = ∅`, the `feketeSet` of size `n ≥ 1` is empty. -/
lemma feketeSet_eq_empty_of_empty_set {K : Set ℂ} (hK : K = ∅) {n : ℕ} (hn : 1 ≤ n) :
    feketeSet K n = ∅ := by
  apply (Set.not_nonempty_iff_eq_empty).1
  rintro ⟨d, hd⟩
  rcases hd with ⟨x, hx, rfl⟩
  have h0 : (0 : ℕ) < n := by omega
  have hx0 : x 0 ∈ K := hx 0 h0
  rw [hK] at hx0
  exact hx0

/-- For `K = ∅`, every Fekete number of size `n ≥ 1` is zero. -/
lemma feketeNumber_eq_zero_of_empty_set {K : Set ℂ} (hK : K = ∅) {n : ℕ} (hn : 1 ≤ n) :
    feketeNumber K n = 0 := by
  unfold feketeNumber
  rw [feketeSet_eq_empty_of_empty_set hK hn, Real.sSup_empty]

/-- For an unbounded `K` the `feketeSet` of size `k ≥ 2` is unbounded above. -/
lemma feketeSet_not_bddAbove_of_unbounded {K : Set ℂ} (hK : ¬ Bornology.IsBounded K)
    {k : ℕ} (hk : 2 ≤ k) : ¬ BddAbove (feketeSet K k) := by
  intro hb
  rcases hb with ⟨B, hBall⟩
  let L : ℝ := max (B + 1) 1
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact le_max_right (B + 1) 1
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hBL : B < L := by
    dsimp [L]
    have hle : B + 1 ≤ max (B + 1) 1 := le_max_left (B + 1) 1
    nlinarith
  let hKf : ∀ R : ℝ, ∃ z ∈ K, R < ‖z‖ := unbounded_norm hK
  let x : ℕ → ℂ := zSeq hKf L
  have hmem : ∀ i : ℕ, i < k → x i ∈ K := by
    intro i hi
    exact zSeq_mem hKf L i
  have hpair : ∀ i : ℕ, i < k → ∀ j : ℕ, j < i → L ≤ ‖x j - x i‖ := by
    intro i hi j hji
    dsimp [x]
    exact zSeq_pairwise (hK := hKf) (L := L) hL0 i j hji
  have hlb := vdm_lower_bound x k L hL0 hpair
  have hSum1 : (1 : ℕ) ≤ ∑ i ∈ Finset.range k, i := by
    have hmem1 : (1 : ℕ) ∈ Finset.range k := by
      rw [Finset.mem_range]
      omega
    have h := Finset.single_le_sum (s := Finset.range k) (f := fun i => i)
      (by intro i hi; exact Nat.zero_le i) hmem1
    simpa using h
  have hLpow : L ≤ L ^ (∑ i ∈ Finset.range k, i) := by
    simpa using (pow_le_pow_right₀ hL1 hSum1)
  have hvdm : L ≤ vdm x k := le_trans hLpow hlb
  have hgt : B < vdm x k := lt_of_lt_of_le hBL hvdm
  have hmemS : vdm x k ∈ feketeSet K k := by
    refine ⟨x, hmem, rfl⟩
  have hleB : vdm x k ≤ B := hBall hmemS
  linarith

/-- For an unbounded `K` the Fekete number of size `k ≥ 2` is zero. -/
lemma feketeNumber_eq_zero_of_unbounded {K : Set ℂ} (hK : ¬ Bornology.IsBounded K)
    {k : ℕ} (hk : 2 ≤ k) : feketeNumber K k = 0 := by
  unfold feketeNumber
  rw [Real.sSup_of_not_bddAbove (feketeSet_not_bddAbove_of_unbounded hK hk)]


/-- `IsBoundedUnder (≤)` for a sequence bounded above. -/
lemma isBoundedUnder_atTop_of_le {u : ℕ → ℝ} (hb : ∃ b : ℝ, ∀ n, u n ≤ b) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
  rcases hb with ⟨b, hb⟩
  unfold Filter.IsBoundedUnder Filter.IsBounded
  refine ⟨b, ?_⟩
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall hb

/-- `2` divides the product of two consecutive naturals `(n+1)·n`. -/
lemma two_dvd_mul_succ (n : ℕ) : (2 : ℕ) ∣ (n + 1) * n := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (n.two_dvd_mul_add_one)

/-- The exponent arithmetic `((n+1)·n/2) · (2/((n+1)·n)) = 1`. -/
lemma expo_cancel (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1) * n / 2 : ℕ) : ℝ) * (2 / (((n : ℝ) + 1) * (n : ℝ)))) = 1 := by
  have hdiv : (2 : ℕ) ∣ (n + 1) * n := two_dvd_mul_succ n
  have hcast : ((((n + 1) * n / 2 : ℕ) : ℝ) = (((n + 1) * n : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_div_charZero hdiv]
    norm_num
  have hs : (((n + 1) * n : ℕ) : ℝ) = ((n : ℝ) + 1) * (n : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    ((((n + 1) * n / 2 : ℕ) : ℝ) * (2 / (((n : ℝ) + 1) * (n : ℝ))))
        = ((((n + 1) * n : ℕ) : ℝ) / 2) * (2 / (((n : ℝ) + 1) * (n : ℝ))) := by rw [hcast]
    _ = ((((n : ℝ) + 1) * (n : ℝ)) / 2) * (2 / (((n : ℝ) + 1) * (n : ℝ))) := by rw [hs]
    _ = 1 := by
      field_simp [hn0]

/-- The pair-count exponent `2/((n+1)·n)` is positive for `1 ≤ n`. -/
lemma expo_pos (n : ℕ) (hn : 1 ≤ n) : 0 < 2 / (((n : ℝ) + 1) * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  positivity


/-- **Bounded nonempty case**: root-limsup `≤ ρ0 < 1` forces geometric
decay of the Fekete numbers in the pair-count exponent. -/
theorem fekete_decay_bounded (K : Set ℂ) (hKne : K.Nonempty) (hKb : Bornology.IsBounded K)
    {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0) (hρ1 : ρ0 < 1)
    (hlim : Filter.limsup (fun n : ℕ =>
        (feketeNumber K (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop ≤ ρ0) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n → feketeNumber K n ≤ C * ρ ^ (n * (n - 1) / 2) := by
  classical
  let e : ℕ → ℝ := fun n : ℕ => (2 : ℝ) / (((n : ℝ) + 1) * (n : ℝ))
  let u : ℕ → ℝ := fun n : ℕ => (feketeNumber K (n + 1)) ^ e n
  let ρ : ℝ := (1 + ρ0) / 2
  have hρ0' : 0 ≤ ρ := by dsimp [ρ]; nlinarith
  have hρpos : 0 < ρ := by dsimp [ρ]; nlinarith
  have hρ1' : ρ < 1 := by dsimp [ρ]; nlinarith
  have hρ0ρ : ρ0 < ρ := by dsimp [ρ]; nlinarith
  have hρle1 : ρ ≤ 1 := le_of_lt hρ1'
  have hlim' : Filter.limsup u Filter.atTop ≤ ρ0 := by
    simpa [u, e] using hlim
  rcases bounded_radius hKb with ⟨R, hRpos, hR⟩
  let M : ℝ := max 1 (2 * R)
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_left 1 (2 * R)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hub : ∀ n : ℕ, u n ≤ M ^ 4 := by
    intro n
    dsimp [u, e, M]
    exact feketeRoot_bounded hKne hKb (le_of_lt hRpos) hR n
  have huB : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
    exact isBoundedUnder_atTop_of_le ⟨M ^ 4, hub⟩
  have hlimlt : Filter.limsup u Filter.atTop < ρ :=
    lt_of_le_of_lt hlim' hρ0ρ
  have hEv : ∀ᶠ n : ℕ in Filter.atTop, u n < ρ :=
    Filter.eventually_lt_of_limsup_lt hlimlt huB
  rcases (Filter.eventually_atTop).1 hEv with ⟨N0, hN0⟩
  let N : ℕ := max N0 1
  have hNge1 : 1 ≤ N := by dsimp [N]; exact le_max_right N0 1
  have hN0leN : N0 ≤ N := by dsimp [N]; exact le_max_left N0 1
  have hEvN : ∀ n : ℕ, N ≤ n → u n < ρ := fun n hn => hN0 n (le_trans hN0leN hn)
  -- the geometric bound for all large indices
  have hbig : ∀ m : ℕ, N + 1 ≤ m → feketeNumber K m ≤ ρ ^ (m * (m - 1) / 2) := by
    intro m hm
    let n : ℕ := m - 1
    have hmn : n + 1 = m := by dsimp [n]; omega
    have hNn : N ≤ n := by dsimp [n]; omega
    have hn1 : 1 ≤ n := le_trans hNge1 hNn
    have hu_n : u n < ρ := hEvN n hNn
    have hm0 : 0 ≤ feketeNumber K (n + 1) := feketeNumber_nonneg_all K (n + 1)
    have hroot0 : 0 ≤ u n := by
      dsimp [u]
      exact Real.rpow_nonneg hm0 (e n)
    let E : ℕ := (n + 1) * n / 2
    have hEc : ((E : ℕ) : ℝ) * e n = 1 := by
      dsimp [E, e]
      exact expo_cancel n hn1
    have hEcancel : e n * ((E : ℕ) : ℝ) = 1 := by
      rw [mul_comm]
      exact hEc
    have hE0 : 0 ≤ ((E : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le E
    have hstep1 := Real.rpow_le_rpow hroot0 (le_of_lt hu_n) hE0
    have hL : (u n) ^ ((E : ℕ) : ℝ) = feketeNumber K (n + 1) := by
      dsimp [u]
      calc
        (feketeNumber K (n + 1) ^ e n) ^ ((E : ℕ) : ℝ)
            = feketeNumber K (n + 1) ^ (e n * ((E : ℕ) : ℝ)) := by
                rw [← Real.rpow_mul hm0]
        _ = feketeNumber K (n + 1) ^ (1 : ℝ) := by rw [hEcancel]
        _ = feketeNumber K (n + 1) := by rw [Real.rpow_one]
    have hmain' : feketeNumber K (n + 1) ≤ ρ ^ ((E : ℕ) : ℝ) := by
      rwa [hL] at hstep1
    have hmain : feketeNumber K (n + 1) ≤ ρ ^ E := by
      simpa [Real.rpow_natCast] using hmain'
    have hEeq : E = m * (m - 1) / 2 := by
      dsimp [E]
      rw [← hmn]
      congr 1
    simpa [hmn, hEeq] using hmain
  -- the constant absorbing the finite prefix
  let Ebig : ℕ := N * (N - 1) / 2
  let C : ℝ := max 1 (M ^ (N * N) / ρ ^ Ebig)
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left 1 (M ^ (N * N) / ρ ^ Ebig)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hρEpos : 0 < ρ ^ Ebig := pow_pos hρpos Ebig
  have hExpLe : ∀ m : ℕ, 1 ≤ m → m ≤ N → m * (m - 1) / 2 ≤ Ebig := by
    intro m hm1 hmN
    dsimp [Ebig]
    have hmlt : m * (m - 1) ≤ N * (N - 1) := by
      exact Nat.mul_le_mul hmN (by omega)
    exact Nat.div_le_div_right hmlt
  have hsmall : ∀ m : ℕ, 1 ≤ m → m ≤ N → feketeNumber K m ≤ C * ρ ^ (m * (m - 1) / 2) := by
    intro m hm1 hmN
    have hsq : feketeNumber K m ≤ M ^ (m * m) := by
      dsimp [M]
      exact feketeNumber_le_sq hKne hR
    have hmm : m * m ≤ N * N := by
      exact Nat.mul_le_mul hmN hmN
    have h1 : feketeNumber K m ≤ M ^ (N * N) := by
      exact le_trans hsq (pow_le_pow_right₀ hM1 hmm)
    have h2 : M ^ (N * N) ≤ C * ρ ^ Ebig := by
      have hCge : M ^ (N * N) / ρ ^ Ebig ≤ C := by
        dsimp [C]
        exact le_max_right 1 (M ^ (N * N) / ρ ^ Ebig)
      have hdiv : M ^ (N * N) ≤ C * ρ ^ Ebig := (div_le_iff₀ hρEpos).1 hCge
      exact hdiv
    have h3 : C * ρ ^ Ebig ≤ C * ρ ^ (m * (m - 1) / 2) := by
      have hExp : m * (m - 1) / 2 ≤ Ebig := hExpLe m hm1 hmN
      have hpowle : ρ ^ Ebig ≤ ρ ^ (m * (m - 1) / 2) := by
        exact pow_le_pow_of_le_one hρ0' hρle1 hExp
      exact mul_le_mul_of_nonneg_left hpowle hC0
    exact le_trans (le_trans h1 h2) h3
  have hbigC : ∀ m : ℕ, N + 1 ≤ m → feketeNumber K m ≤ C * ρ ^ (m * (m - 1) / 2) := by
    intro m hm
    have hge : ρ ^ (m * (m - 1) / 2) ≤ C * ρ ^ (m * (m - 1) / 2) := by
      exact le_mul_of_one_le_left (pow_nonneg hρ0' (m * (m - 1) / 2)) hC1
    exact le_trans (hbig m hm) hge
  refine ⟨ρ, C, hρ0', hρ1', hC0, ?_⟩
  intro m hm1
  by_cases hmN : m ≤ N
  · exact hsmall m hm1 hmN
  · have hbigm : N + 1 ≤ m := by omega
    exact hbigC m hbigm


/-- Root-limsup `≤ ρ0 < 1` forces geometric decay of the Fekete numbers. -/
theorem fekete_decay_of_root_limsup_le (K : Set ℂ) {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0)
    (hρ1 : ρ0 < 1)
    (hlim : Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber K (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop ≤ ρ0) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n → Submission.FeketeLim.feketeNumber K n ≤ C * ρ ^ (n * (n - 1) / 2) := by
  classical
  by_cases hKne : K.Nonempty
  · by_cases hKb : Bornology.IsBounded K
    · exact fekete_decay_bounded K hKne hKb hρ0 hρ1 hlim
    · -- `K` nonempty and unbounded: `m_1 = 1`, `m_k = 0` for `k ≥ 2`
      refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
      intro n hn
      by_cases hn2 : n = 1
      · subst n
        rw [feketeNumber_one hKne]
        norm_num
      · have hn2' : 2 ≤ n := by omega
        have hz : Submission.FeketeLim.feketeNumber K n = 0 :=
          feketeNumber_eq_zero_of_unbounded hKb hn2'
        rw [hz]
        positivity
  · -- `K` empty: all Fekete numbers vanish
    have hK : K = ∅ := (Set.not_nonempty_iff_eq_empty).1 hKne
    refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro n hn
    have hz : Submission.FeketeLim.feketeNumber K n = 0 :=
      feketeNumber_eq_zero_of_empty_set hK hn
    rw [hz]
    positivity

end Submission.FeketeDecayOfLimsup
