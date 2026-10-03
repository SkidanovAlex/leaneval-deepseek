import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.sunrise_card_le_sum
import Submission.Commons.Analysis.HardyLittlewood.lintegral_rpow_le_of_restricted_weak_type

namespace Commons.Analysis.HardyLittlewood

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology
open Classical

/-! ## The sunrise potential -/

/-- Auxiliary construction: for a sequence `a` vanishing for `n ≥ M` and `lam > 0`, there is a
nonnegative `φ` satisfying the backwards recursion `φ n = max 0 (a n - lam + φ (n+1))` and such
that `φ n > 0` exactly when some forward average of `a` starting at `n` exceeds `lam`. -/
theorem exists_sunrise_phi_aux {a : ℕ → ℝ} {M : ℕ} (ha : ∀ n, M ≤ n → a n = 0) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ φ : ℕ → ℝ, (∀ n, 0 ≤ φ n) ∧ (∀ n, φ n = max 0 (a n - lam + φ (n + 1))) ∧
      (∀ n, 0 < φ n ↔ ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)) := by
  let ψ : ℕ → ℝ := fun k => Nat.rec 0 (fun k acc => max 0 (a (M - (k + 1)) - lam + acc)) k
  have hψsucc : ∀ k, ψ (k + 1) = max 0 (a (M - (k + 1)) - lam + ψ k) := fun k => rfl
  let φ : ℕ → ℝ := fun n => if M ≤ n then 0 else ψ (M - n)
  have hφM : ∀ n, M ≤ n → φ n = 0 := by intro n hn; simp [φ, hn]
  have hφle : ∀ n ≤ M, φ n = ψ (M - n) := by
    intro n hn
    rcases lt_or_eq_of_le hn with h | h
    · simp only [φ]; rw [if_neg (not_le.mpr h)]
    · rw [h, Nat.sub_self, hφM M le_rfl, show ψ 0 = 0 from rfl]
  have hφrec : ∀ n < M, φ n = max 0 (a n - lam + φ (n + 1)) := by
    intro n hn
    have h1 : M - n = (M - (n + 1)) + 1 := by omega
    have h2 : M - ((M - (n + 1)) + 1) = n := by omega
    have h3 : φ (n + 1) = ψ (M - (n + 1)) := hφle (n + 1) (by omega)
    rw [hφle n hn.le, h1, hψsucc, h2, h3]
  have hφnn : ∀ n, 0 ≤ φ n := by
    intro n
    rcases lt_or_ge n M with h | h
    · rw [hφrec n h]; exact le_max_left 0 _
    · rw [hφM n h]
  let S : ℕ → ℕ → ℝ := fun n N => (∑ j ∈ Finset.range N, a (n + j)) - lam * N
  have hS0 : ∀ n, S n 0 = 0 := by intro n; simp [S]
  have hSsucc : ∀ n N, S n (N + 1) = a n - lam + S (n + 1) N := by
    intro n N
    simp only [S, Finset.sum_range_succ', Nat.add_zero, Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_congr rfl (fun i _ => by rw [show n + (i + 1) = n + 1 + i from by omega])]
    ring
  have hkey : ∀ n ≤ M, (∀ N, S n N ≤ φ n) ∧ ∃ N, φ n = S n N := by
    intro n hn
    refine Nat.decreasingInduction (n := M)
      (motive := fun m _ => (∀ N, S m N ≤ φ m) ∧ ∃ N, φ m = S m N) ?_ ?_ hn
    · intro k hk ih
      constructor
      · intro N
        cases N with
        | zero => rw [hS0]; exact hφnn k
        | succ N' =>
          rw [hSsucc]
          linarith [ih.1 N', hφrec k hk, le_max_right (0 : ℝ) (a k - lam + φ (k + 1))]
      · rcases lt_or_ge (a k - lam + φ (k + 1)) 0 with hlt | hge
        · exact ⟨0, by rw [hS0, hφrec k hk, max_eq_left hlt.le]⟩
        · obtain ⟨N0, hN0⟩ := ih.2
          exact ⟨N0 + 1, by rw [hφrec k hk, max_eq_right hge, hSsucc, ← hN0]⟩
    · constructor
      · intro N
        have hzero : (∑ j ∈ Finset.range N, a (M + j)) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          exact ha (M + j) (Nat.le_add_right M j)
        have hS : S M N = -(lam * N) := by simp only [S, hzero]; ring
        rw [hS, hφM M le_rfl]
        have : (0 : ℝ) ≤ lam * N := mul_nonneg hlam.le (Nat.cast_nonneg N)
        linarith
      · exact ⟨0, by rw [hS0, hφM M le_rfl]⟩
  refine ⟨φ, hφnn, ?_, ?_⟩
  · intro n
    by_cases hn : n < M
    · exact hφrec n hn
    · have hnM : M ≤ n := not_lt.mp hn
      have hn1M : M ≤ n + 1 := by omega
      rw [hφM n hnM, ha n hnM, hφM (n + 1) hn1M, max_eq_left]
      linarith
  · intro n
    by_cases hn : n < M
    · constructor
      · intro hpos
        obtain ⟨N, hN⟩ := (hkey n hn.le).2
        have hSpos : 0 < S n N := by rw [← hN]; exact hpos
        refine ⟨N, ?_, ?_⟩
        · rcases Nat.eq_zero_or_pos N with h | h
          · rw [h, hS0] at hSpos; exact absurd hSpos (lt_irrefl 0)
          · exact h
        · simp only [S] at hSpos; linarith
      · rintro ⟨N, hNpos, hlt⟩
        have h1 : 0 < S n N := by simp only [S]; linarith
        linarith [(hkey n hn.le).1 N]
    · have hnM : M ≤ n := not_lt.mp hn
      constructor
      · intro h
        rw [hφM n hnM] at h
        exact absurd h (lt_irrefl 0)
      · rintro ⟨N, hNpos, hlt⟩
        have hzero : (∑ j ∈ Finset.range N, a (n + j)) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          exact ha (n + j) (by omega)
        rw [hzero] at hlt
        have : 0 < lam * N := mul_pos hlam (Nat.cast_pos.mpr hNpos)
        linarith

/-! ## The counting-measure form of the sunrise inequality -/

/-- A window sum of a nonnegative sequence supported in `range M` is bounded by its total mass. -/
lemma sum_shift_le_sum_range {a : ℕ → ℝ} (ha_nn : ∀ n, 0 ≤ a n) {M : ℕ}
    (ha : ∀ n, M ≤ n → a n = 0) (n N : ℕ) :
    ∑ j ∈ Finset.range N, a (n + j) ≤ ∑ k ∈ Finset.range M, a k := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun j => n + j < M)
    (fun j => a (n + j))]
  have h1 : ∑ j ∈ (Finset.range N).filter (fun j => ¬ n + j < M), a (n + j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_filter] at hj
    exact ha (n + j) (by omega)
  rw [h1, add_zero]
  have h2 : ∑ j ∈ (Finset.range N).filter (fun j => n + j < M), a (n + j)
      = ∑ k ∈ ((Finset.range N).filter (fun j => n + j < M)).image (fun j => n + j), a k := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Nat.add_left_cancel (show n + x = n + y from hxy)
  rw [h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => ha_nn k)
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  rw [Finset.mem_filter] at hj
  exact Finset.mem_range.mpr hj.2

/-- The forward window averages of a finitely supported sequence are bounded above. -/
lemma bddAbove_window_avg {a : ℕ → ℝ} (ha_nn : ∀ n, 0 ≤ a n) {M : ℕ}
    (ha : ∀ n, M ≤ n → a n = 0) (n : ℕ) :
    BddAbove (Set.range fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)) := by
  refine ⟨∑ k ∈ Finset.range M, a k, ?_⟩
  rintro x ⟨N, rfl⟩
  have hB : 0 ≤ ∑ k ∈ Finset.range M, a k := Finset.sum_nonneg (fun k _ => ha_nn k)
  have hT : 0 ≤ ∑ j ∈ Finset.range N, a (n + j) := Finset.sum_nonneg (fun j _ => ha_nn _)
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h]
    simp
    exact hB
  · have hinv : (N : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by exact_mod_cast h)]
      exact_mod_cast h
    calc (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)
        ≤ 1 * ∑ j ∈ Finset.range N, a (n + j) := mul_le_mul_of_nonneg_right hinv hT
      _ = ∑ j ∈ Finset.range N, a (n + j) := one_mul _
      _ ≤ ∑ k ∈ Finset.range M, a k := sum_shift_le_sum_range ha_nn ha n N

/-- The Lebesgue integral with respect to counting measure of a function vanishing outside a
finite set is the finite sum over that set. -/
lemma lintegral_count_finset (E : Finset ℕ) (g : ℕ → ℝ≥0∞) :
    ∫⁻ n in (E : Set ℕ), g n ∂Measure.count = ∑ n ∈ E, g n := by
  rw [← lintegral_indicator E.measurableSet g, lintegral_count,
    tsum_eq_sum (s := E) (f := (E : Set ℕ).indicator g)]
  · exact Finset.sum_congr rfl fun n hn => Set.indicator_of_mem (by simpa using hn) g
  · intro n hn
    rw [Set.indicator_of_notMem]
    exact fun h => hn (by simpa using h)

/-- The sunrise weak-type inequality, in counting-measure form: the measure of the set of `n`
for which some forward average of `a` exceeds `lam` is controlled by the sum of `a` over that
same set. -/
theorem sunrise_count_le {a : ℕ → ℝ} (ha_nn : ∀ n, 0 ≤ a n) {M : ℕ}
    (ha : ∀ n, M ≤ n → a n = 0) {lam : ℝ} (hlam : 0 < lam) :
    ENNReal.ofReal lam * Measure.count {n : ℕ | ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)}
      ≤ ∫⁻ n in {n : ℕ | ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)},
          ENNReal.ofReal (a n) ∂Measure.count := by
  set E : Finset ℕ :=
    (Finset.range M).filter (fun n => ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j))
    with hE
  -- the set in question is exactly `E`; in particular it is finite
  have hPfin : ∀ n, (∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)) → n < M := by
    rintro n ⟨N, hN, hlt⟩
    by_contra hcon
    push Not at hcon
    have hzero : (∑ j ∈ Finset.range N, a (n + j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact ha (n + j) (by omega)
    rw [hzero] at hlt
    have : 0 < lam * N := mul_pos hlam (Nat.cast_pos.mpr hN)
    linarith
  have hEeq : ∀ n, n ∈ E ↔ ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j) := by
    intro n
    rw [hE, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hPfin n h, h⟩⟩
  have hset : {n : ℕ | ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)} = (E : Set ℕ) := by
    ext n
    rw [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hEeq n).symm
  obtain ⟨φ, hφnn, hφrec, hφiff⟩ := exists_sunrise_phi_aux ha hlam
  have hEmem : ∀ n, n ∈ E ↔ 0 < φ n := by
    intro n; rw [hEeq n]; exact (hφiff n).symm
  have hrecE : ∀ n ∈ E, φ n = a n - lam + φ (n + 1) := by
    intro n hn
    have hpos : 0 < φ n := (hEmem n).mp hn
    rcases lt_or_ge (a n - lam + φ (n + 1)) 0 with hlt | hge
    · rw [hφrec n, max_eq_left hlt.le] at hpos
      exact absurd hpos (lt_irrefl 0)
    · rw [hφrec n, max_eq_right hge]
  have hbound : lam * (E.card : ℝ) ≤ ∑ n ∈ E, a n :=
    sunrise_card_le_sum hφnn hEmem hrecE
  rw [hset, Measure.count_apply_finset, lintegral_count_finset, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hlam.le, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => ha_nn n)]
  exact ENNReal.ofReal_le_ofReal hbound

/-! ## The weak-type inequality for the forward maximal function -/

/-- The level set of the forward maximal function is the sunrise set. -/
lemma lt_window_sup_iff {a : ℕ → ℝ} (ha_nn : ∀ n, 0 ≤ a n) {M : ℕ}
    (ha : ∀ n, M ≤ n → a n = 0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    lam < ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j) ↔
      ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (lt_ciSup_iff (bddAbove_window_avg ha_nn ha n)).mp h
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0] at hN; simp at hN; linarith
      · exact hpos
    refine ⟨N, hNpos, ?_⟩
    have hstep := mul_lt_mul_of_pos_right hN (Nat.cast_pos.mpr hNpos)
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
    have heq : ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)) * (N : ℝ)
        = ∑ j ∈ Finset.range N, a (n + j) := by
      field_simp
    linarith [hstep, heq]
  · rintro ⟨N, hNpos, hlt⟩
    have h1 : lam < (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j) := by
      rw [inv_mul_eq_div, lt_div_iff₀ (Nat.cast_pos.mpr hNpos)]
      exact hlt
    exact lt_of_lt_of_le h1 (le_ciSup (bddAbove_window_avg ha_nn ha n) N)

/-- The weak-type (sunrise) inequality for the forward maximal function of a nonnegative
finitely supported sequence: `lam * #{n : sup_N avg_N a(n) > lam} ≤ ∫_{...} a`. -/
theorem weak_type_forward_maximal_aux {a : ℕ → ℝ} (ha_nn : ∀ n, 0 ≤ a n) {M : ℕ}
    (ha : ∀ n, M ≤ n → a n = 0) {lam : ℝ} (hlam : 0 < lam) :
    ENNReal.ofReal lam
        * Measure.count {n : ℕ | lam < ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)}
      ≤ ∫⁻ n in {n : ℕ | lam < ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)},
          ENNReal.ofReal (a n) ∂Measure.count := by
  have hset : {n : ℕ | lam < ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j)}
      = {n : ℕ | ∃ N, 0 < N ∧ lam * N < ∑ j ∈ Finset.range N, a (n + j)} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    exact lt_window_sup_iff ha_nn ha hlam n
  rw [hset]
  exact sunrise_count_le ha_nn ha hlam


/-! ## The discrete forward maximal inequality -/

/-- Pointwise domination of the `ℝ≥0∞`-valued forward maximal function of `g` by the real
forward maximal function of `|g|`. -/
lemma max_enorm_le {g : ℕ → ℝ} {M : ℕ} (hM : ∀ n, M ≤ n → |g n| = 0) (n : ℕ) :
    (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g (n + j)‖ₑ)
      ≤ ENNReal.ofReal (⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, |g (n + j)|) := by
  refine iSup_le fun N => ?_
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  calc |(N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g (n + j)|
      = (N : ℝ)⁻¹ * |∑ j ∈ Finset.range N, g (n + j)| := by rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, |g (n + j)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hnn
    _ ≤ ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, |g (n + j)| :=
        le_ciSup (bddAbove_window_avg (fun k => abs_nonneg (g k)) hM n) N

/-- **Discrete forward maximal inequality.**  For `p > 1` the one-sided discrete Hardy--Littlewood
maximal function of a finitely supported sequence satisfies an `ℓ^p` bound, with constant
`p/(p-1)`. -/
theorem discrete_forward_maximal {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ → ℝ), (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (n + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  refine ⟨p / (p - 1), div_pos hp0 hp1, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  set M : ℕ := s.sup id + 1 with hMs
  have hgM : ∀ n, M ≤ n → g n = 0 := by
    intro n hn
    by_cases hmem : n ∈ s
    · have h1 : n ≤ s.sup id := Finset.le_sup (f := id) hmem
      omega
    · exact hs n hmem
  set a : ℕ → ℝ := fun n => |g n| with ha
  have ha_nn : ∀ n, 0 ≤ a n := fun n => abs_nonneg _
  have haM : ∀ n, M ≤ n → a n = 0 := by
    intro n hn
    simp only [ha]
    rw [hgM n hn, abs_zero]
  set S : ℕ → ℝ := fun n => ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a (n + j) with hS
  have hSnn : ∀ n, 0 ≤ S n := by
    intro n
    have := le_ciSup (bddAbove_window_avg ha_nn haM n) 0
    simpa only [hS, Nat.cast_zero, inv_zero, zero_mul] using this
  have hpoint : ∀ n,
      (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g (n + j)‖ₑ) ≤ ENNReal.ofReal (S n) := by
    intro n
    have h1 : (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g (n + j)‖ₑ)
        ≤ ENNReal.ofReal (⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, |g (n + j)|) :=
      max_enorm_le (fun k hk => by rw [hgM k hk, abs_zero]) n
    simpa only [hS, ha] using h1
  have hweak : ∀ lam : ℝ, 0 < lam →
      ENNReal.ofReal lam * Measure.count {n : ℕ | lam < S n}
        ≤ ∫⁻ n in {n : ℕ | lam < S n}, ENNReal.ofReal (a n) ∂Measure.count := by
    intro lam hlam
    have h1 := weak_type_forward_maximal_aux (a := a) ha_nn haM hlam
    simpa only [hS] using h1
  have has : ∀ n, n ∉ s → a n = 0 := by
    intro n hn
    simp only [ha]
    rw [hs n hn, abs_zero]
  have hLp := lintegral_rpow_le_of_restricted_weak_type (p := p) hp hSnn ha_nn has hweak
  calc ∫⁻ n, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (n + j)‖ₑ) ^ p ∂Measure.count
      ≤ ∫⁻ n, (ENNReal.ofReal (S n)) ^ p ∂Measure.count :=
        lintegral_mono fun n => ENNReal.rpow_le_rpow (hpoint n) hp0.le
    _ = ∫⁻ n, ENNReal.ofReal ((S n) ^ p) ∂Measure.count :=
        lintegral_congr fun n => ENNReal.ofReal_rpow_of_nonneg (hSnn n) hp0.le
    _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p)
          * ∫⁻ n, ENNReal.ofReal ((a n) ^ p) ∂Measure.count := hLp
    _ = ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
        congr 1
        refine lintegral_congr fun n => ?_
        rw [ha, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (g n)) hp0.le,
          ← Real.enorm_eq_ofReal_abs]


end Commons.Analysis.HardyLittlewood
