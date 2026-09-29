import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0
import Submission.Work.TMC16Core.Assembly.uniform_of_sum_bounds_gen
import Submission.Work.TMC16Core.Core.uni_res5
import Submission.Work.TMC16Core.Core.irrat_blk_shift
import Submission.Work.TMC16Core.Core.blk_sep_base

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-! ## The index picture of the window -/

/-- The shift of the `k`-th index: `0` on the head `k ≤ 2U`, `m` on the tail. -/
def s0q4Lsh (U : ℕ) (m : ℤ) (k : ℤ) : ℤ := (if k ≤ (2 * (U : ℤ)) then (0 : ℤ) else 1) * m

/-- The phase index of the `k`-th site of the window. -/
def s0q4Idx (U : ℕ) (m : ℤ) (qn : ℕ) (k : ℤ) : ℤ := k + s0q4Lsh U m k * (qn : ℤ)

lemma s0q4Lsh_abs (U : ℕ) (m : ℤ) (k : ℤ) : |s0q4Lsh U m k| ≤ |m| := by
  unfold s0q4Lsh
  split_ifs <;> simp

lemma s0q4Lsh_zero_of_le {U : ℕ} {m : ℤ} {k : ℤ} (hk : k ≤ 2 * (U : ℤ)) :
    s0q4Lsh U m k = 0 := by
  simp [s0q4Lsh, hk]

lemma s0q4Lsh_m_of_lt {U : ℕ} {m : ℤ} {k : ℤ} (hk : 2 * (U : ℤ) < k) :
    s0q4Lsh U m k = m := by
  simp [s0q4Lsh, not_le.mpr hk]

lemma s0q4Idx_of_le {U : ℕ} {m : ℤ} {qn : ℕ} {k : ℤ} (hk : k ≤ 2 * (U : ℤ)) :
    s0q4Idx U m qn k = k := by simp [s0q4Idx, s0q4Lsh_zero_of_le hk]

lemma s0q4Idx_of_lt {U : ℕ} {m : ℤ} {qn : ℕ} {k : ℤ} (hk : 2 * (U : ℤ) < k) :
    s0q4Idx U m qn k = k + m * (qn : ℤ) := by simp [s0q4Idx, s0q4Lsh_m_of_lt hk]

lemma s0q4Idx_sub (U : ℕ) (m : ℤ) (qn : ℕ) (k l : ℤ) :
    s0q4Idx U m qn k - s0q4Idx U m qn l
      = (k - l) + (s0q4Lsh U m k - s0q4Lsh U m l) * (qn : ℤ) := by
  simp only [s0q4Idx]; ring

/-- The sum of two indices is `k + l` plus `t · (m · q n)` with `t ∈ {0,1,2}`. -/
lemma s0q4Idx_add_eq (U : ℕ) (m : ℤ) (qn : ℕ) (k l : ℤ) :
    ∃ t : ℤ, (t = 0 ∨ t = 1 ∨ t = 2) ∧
      s0q4Idx U m qn k + s0q4Idx U m qn l = (k + l) + t * (m * (qn : ℤ)) := by
  refine ⟨(if k ≤ 2 * (U : ℤ) then (0:ℤ) else 1) + (if l ≤ 2 * (U : ℤ) then (0:ℤ) else 1),
    ?_, ?_⟩
  · split_ifs <;> omega
  · unfold s0q4Idx s0q4Lsh
    split_ifs <;> ring

/-- The difference of two shifts is `0` or `± m`. -/
lemma s0q4Lsh_sub_cases (U : ℕ) (m : ℤ) (k l : ℤ) :
    s0q4Lsh U m l - s0q4Lsh U m k = 0 ∨ s0q4Lsh U m l - s0q4Lsh U m k = m
      ∨ s0q4Lsh U m l - s0q4Lsh U m k = -m := by
  rcases le_or_gt k (2 * (U : ℤ)) with hk | hk <;>
    rcases le_or_gt l (2 * (U : ℤ)) with hl | hl
  · rw [s0q4Lsh_zero_of_le hk, s0q4Lsh_zero_of_le hl]; left; ring
  · rw [s0q4Lsh_zero_of_le hk, s0q4Lsh_m_of_lt hl]; right; left; ring
  · rw [s0q4Lsh_m_of_lt hk, s0q4Lsh_zero_of_le hl]; right; right; ring
  · rw [s0q4Lsh_m_of_lt hk, s0q4Lsh_m_of_lt hl]; left; ring

/-- The map `k ↦ k + ℓ_k m q n` is injective on `[1,H]` when `H < q n`. -/
lemma s0q4Idx_injOn {U : ℕ} {m : ℤ} {qn H : ℕ} (hHq : H < qn) {k l : ℤ}
    (hk : k ∈ Finset.Icc 1 (H : ℤ)) (hl : l ∈ Finset.Icc 1 (H : ℤ))
    (heq : s0q4Idx U m qn k = s0q4Idx U m qn l) : k = l := by
  rw [Finset.mem_Icc] at hk hl
  have hsub := s0q4Idx_sub U m qn k l
  rw [heq, sub_self] at hsub
  have h1 : k - l = (s0q4Lsh U m l - s0q4Lsh U m k) * (qn : ℤ) := by linarith [hsub]
  have hq : (0 : ℤ) < (qn : ℤ) := by
    have h1' : (0 : ℕ) < qn := by omega
    exact_mod_cast h1'
  have hklu : |k - l| ≤ (H : ℤ) - 1 := by
    rw [abs_le]; constructor <;> omega
  rcases s0q4Lsh_sub_cases U m k l with h0 | hm | hneg
  · rw [h0, zero_mul] at h1; omega
  · have habs : |k - l| = |m| * (qn : ℤ) := by
      rw [h1, abs_mul, hm, abs_of_pos hq]
    have hm0 : m = 0 := by
      by_contra h
      have h1' : (1 : ℤ) ≤ |m| := Int.one_le_abs h
      have h2 : (qn : ℤ) ≤ |m| * (qn : ℤ) := by
        calc (qn : ℤ) = 1 * (qn : ℤ) := by ring
          _ ≤ |m| * (qn : ℤ) := mul_le_mul_of_nonneg_right h1' (le_of_lt hq)
      rw [habs] at hklu
      omega
    rw [hm0] at habs
    simp at habs
    omega
  · have habs : |k - l| = |m| * (qn : ℤ) := by
      rw [h1, abs_mul, hneg, abs_neg, abs_of_pos hq]
    have hm0 : m = 0 := by
      by_contra h
      have h1' : (1 : ℤ) ≤ |m| := Int.one_le_abs h
      have h2 : (qn : ℤ) ≤ |m| * (qn : ℤ) := by
        calc (qn : ℤ) = 1 * (qn : ℤ) := by ring
          _ ≤ |m| * (qn : ℤ) := mul_le_mul_of_nonneg_right h1' (le_of_lt hq)
      rw [habs] at hklu
      omega
    rw [hm0] at habs
    simp at habs
    omega

/-! ## Elementary `fracDist` facts -/

lemma s0q4_fracDist_sub_le (x y : ℝ) :
    Work.TMC16Core.fracDist x - Work.TMC16Core.fracDist y ≤ Work.TMC16Core.fracDist (x - y) := by
  have h : Work.TMC16Core.fracDist x ≤ Work.TMC16Core.fracDist (x - y) + Work.TMC16Core.fracDist y := by
    have h2 : Work.TMC16Core.Basic.nn ((x - y) + y) ≤
        Work.TMC16Core.Basic.nn (x - y) + Work.TMC16Core.Basic.nn y :=
      Work.TMC16Core.Basic.nn_add_le (x - y) y
    rw [show (x - y) + y = x from sub_add_cancel x y] at h2
    exact h2
  linarith

lemma s0q4_fracDist_mul_le (m : ℤ) (w : ℝ) :
    Work.TMC16Core.fracDist ((m : ℝ) * w) ≤ |(m : ℝ)| * Work.TMC16Core.fracDist w := by
  have h : Work.TMC16Core.fracDist ((m : ℝ) * w) ≤ (((m.natAbs : ℕ)) : ℝ) * Work.TMC16Core.fracDist w :=
    Work.TMC16Core.Core.nn_intCast_mul_le m w
  rw [Nat.cast_natAbs, Int.cast_abs] at h
  exact h

/-- `fracDist (d α) ≥ 1/(2 q (n-1))` for `1 ≤ |d| < q (n-1)`. -/
lemma s0q4_fracDist_small {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {d : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n) (hd : 1 ≤ |d|) (hLt : |d| < (q (n - 1) : ℤ)) :
    1 / (2 * (q (n - 1) : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) := by
  have hbase := Work.TMC16Core.Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
  have hdn : (((|d|).natAbs : ℕ) : ℤ) = |d| := Int.natAbs_of_nonneg (abs_nonneg d)
  have hD1 : 1 ≤ (|d|).natAbs := by omega
  have hD2 : (|d|).natAbs < q (n - 1) := by omega
  have h := Work.TMC16Core.Core.sep_all hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase
    (n - 1) ((|d|).natAbs) hD1 hD2
  have hcast : ((((|d|).natAbs : ℕ)) : ℝ) = |(d : ℝ)| := by simp [Nat.cast_natAbs]
  rw [hcast] at h
  rcases abs_choice (d : ℝ) with hdc | hdc
  · rw [hdc] at h; exact h
  · rw [hdc] at h
    have : (-(d : ℝ)) * α = -((d : ℝ) * α) := by ring
    rw [this, Work.TMC16Core.Core.fracDist_neg] at h
    exact h

/-- `fracDist (d α) ≥ 1/(2 q n)` for `1 ≤ |d| < q n`. -/
lemma s0q4_fracDist_lt_qn {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {d : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n) (hd : 1 ≤ |d|) (hLt : |d| < (q n : ℤ)) :
    1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((d : ℝ) * α) := by
  have hdn : (((|d|).natAbs : ℕ) : ℤ) = |d| := Int.natAbs_of_nonneg (abs_nonneg d)
  have hD1 : 1 ≤ (|d|).natAbs := by omega
  have hD2 : (|d|).natAbs < q n := by omega
  have hcast : ((((|d|).natAbs : ℕ)) : ℝ) = |(d : ℝ)| := by simp [Nat.cast_natAbs]
  have hmain : 1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist ((((|d|).natAbs : ℕ) : ℝ) * α) := by
    rcases lt_or_ge ((|d|).natAbs) (q 0) with hsmall | hbig
    · have hb := Work.TMC16Core.Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
        ((|d|).natAbs) hD1 hsmall
      have hq0n : (q 0 : ℝ) ≤ (q n : ℝ) := by
        exact_mod_cast hmono.monotone (Nat.zero_le n)
      have h1 : 1 / (2 * (q n : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) := by
        have h2 : (0 : ℝ) < 2 * (q 0 : ℝ) := by
          have := hqpos 0; positivity
        have h3 : 2 * (q 0 : ℝ) ≤ 2 * (q n : ℝ) := by linarith
        exact one_div_le_one_div_of_le h2 h3
      linarith
    · obtain ⟨i, hi1, hi2⟩ := Work.TMC16Core.Core.exists_block hmono hbig
      have hi_le : i + 1 ≤ n := by
        by_contra h
        push_neg at h
        have hq : q n ≤ q i := hmono.monotone (by omega)
        omega
      have hΔi : Δ i ≤ Work.TMC16Core.fracDist ((((|d|).natAbs : ℕ) : ℝ) * α) :=
        hbest i ((|d|).natAbs) hi1 hi2
      have hlo := hΔlo i
      have hqi : (q (i + 1) : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hmono.monotone hi_le
      have hqi' : (q i : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hmono.monotone (by omega)
      have h3 : (0 : ℝ) < (q (i + 1) : ℝ) + (q i : ℝ) := by
        have h4 := hqpos (i + 1); have h5 := hqpos i; positivity
      have h4 : (q (i + 1) : ℝ) + (q i : ℝ) ≤ 2 * (q n : ℝ) := by linarith
      have h2 : 1 / (2 * (q n : ℝ)) ≤ 1 / ((q (i + 1) : ℝ) + (q i : ℝ)) :=
        one_div_le_one_div_of_le h3 h4
      linarith
  rw [hcast] at hmain
  rcases abs_choice (d : ℝ) with hdc | hdc
  · rw [hdc] at hmain; exact hmain
  · rw [hdc] at hmain
    have : (-(d : ℝ)) * α = -((d : ℝ) * α) := by ring
    rw [this, Work.TMC16Core.Core.fracDist_neg] at hmain
    exact hmain

/-- `fracDist`-typed form of the triangle inequality. -/
lemma s0q4_nn_sub_le (a b : ℝ) :
    Work.TMC16Core.fracDist (a - b) ≤ Work.TMC16Core.fracDist a + Work.TMC16Core.fracDist b :=
  Work.TMC16Core.Core.nn_sub_le_aux a b

/-- `fracDist`-typed form of the triangle inequality. -/
lemma s0q4_nn_add_le (a b : ℝ) :
    Work.TMC16Core.fracDist (a + b) ≤ Work.TMC16Core.fracDist a + Work.TMC16Core.fracDist b :=
  Work.TMC16Core.Basic.nn_add_le a b

/-- `fracDist` is non-negative. -/
lemma s0q4_fracDist_nonneg (x : ℝ) : 0 ≤ Work.TMC16Core.fracDist x := abs_nonneg _

/-- `fracDist (m q n α) ≤ 1/(10 q n)`. -/
lemma s0q4_fracDist_mqn_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {m : ℤ}
    (hqpos : ∀ i, 0 < q i)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) :
    Work.TMC16Core.fracDist ((m : ℝ) * ((q n : ℝ) * α)) ≤ 1 / (10 * (q n : ℝ)) := by
  by_cases hm0 : m = 0
  · rw [hm0]; simp [Work.TMC16Core.fracDist]
  · have hmul := s0q4_fracDist_mul_le (m : ℤ) ((q n : ℝ) * α)
    rw [← hΔeq n] at hmul
    have hmΔ : (|(m : ℝ)|) * Δ n < 1 / (10 * (q n : ℝ)) := by
      have h1 : 10 * ((|m| : ℝ) + 1) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
        have := hmq hm0
        exact_mod_cast this
      have hqn : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
      have h3 : (|m| : ℝ) + 1 ≤ (q (n + 1) : ℝ) / (10 * (q n : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h4 : (|m| : ℝ) < (q (n + 1) : ℝ) / (10 * (q n : ℝ)) := by linarith
      have h5 : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
      have h6 : (0 : ℝ) < (q (n + 1) : ℝ) / (10 * (q n : ℝ)) := by
        have h8 : (0 : ℝ) < (q (n + 1) : ℝ) := by
          have := hqpos (n + 1); exact_mod_cast this
        exact div_pos h8 (by positivity)
      have h7 : (q (n + 1) : ℝ) ≠ 0 := by
        have := hqpos (n + 1); exact_mod_cast (ne_of_gt this)
      calc (|(m : ℝ)|) * Δ n < (q (n + 1) : ℝ) / (10 * (q n : ℝ)) * Δ n :=
            mul_lt_mul_of_pos_right h4 (hΔpos n)
        _ < (q (n + 1) : ℝ) / (10 * (q n : ℝ)) * (1 / (q (n + 1) : ℝ)) :=
            mul_lt_mul_of_pos_left h5 h6
        _ = 1 / (10 * (q n : ℝ)) := by
            have hD : (10 * (q n : ℝ)) ≠ 0 := by positivity
            field_simp
    linarith [hmul, hmΔ]

/-- The difference of two shifted indices is `(k-l)`, `(k-l) + m q n` or `(k-l) - m q n`. -/
lemma s0q4_idx_diff_cases {U : ℕ} {m : ℤ} {qn : ℕ} {k l : ℤ} :
    s0q4Idx U m qn k - s0q4Idx U m qn l = (k - l) ∨
      s0q4Idx U m qn k - s0q4Idx U m qn l = (k - l) + m * (qn : ℤ) ∨
      s0q4Idx U m qn k - s0q4Idx U m qn l = (k - l) - m * (qn : ℤ) := by
  have hsub := s0q4Idx_sub U m qn k l
  rcases s0q4Lsh_sub_cases U m k l with h | h | h
  · have h' : s0q4Lsh U m k - s0q4Lsh U m l = 0 := by linarith
    left; rw [hsub, h', zero_mul, add_zero]
  · have h' : s0q4Lsh U m k - s0q4Lsh U m l = -m := by linarith
    right; right; rw [hsub, h']; try ring
  · have h' : s0q4Lsh U m k - s0q4Lsh U m l = m := by linarith
    right; left; rw [hsub, h']; try ring

/-- `fracDist (d α) ≥ fracDist ((k-l) α) - fracDist (m q n α)` for the difference `d` of two
shifted indices. -/
lemma s0q4_idx_diff_ge {U : ℕ} {m : ℤ} {qn : ℕ} {k l : ℤ} {α : ℝ} :
    Work.TMC16Core.fracDist (((k - l : ℤ) : ℝ) * α)
        - Work.TMC16Core.fracDist ((m : ℝ) * ((qn : ℝ) * α))
      ≤ Work.TMC16Core.fracDist (((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α) := by
  rcases s0q4_idx_diff_cases (U := U) (m := m) (qn := qn) (k := k) (l := l) with h | h | h
  · rw [h]
    linarith [s0q4_fracDist_nonneg ((m : ℝ) * ((qn : ℝ) * α))]
  · have hreal : ((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α
          - (m : ℝ) * ((qn : ℝ) * α) = ((k - l : ℤ) : ℝ) * α := by
      have h2 : ((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α
          = ((k - l : ℤ) : ℝ) * α + (m : ℝ) * ((qn : ℝ) * α) := by rw [h]; push_cast; ring
      rw [h2]; ring
    have key := s0q4_nn_sub_le (((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α)
      ((m : ℝ) * ((qn : ℝ) * α))
    rw [hreal] at key
    linarith
  · have hreal : ((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α
          + (m : ℝ) * ((qn : ℝ) * α) = ((k - l : ℤ) : ℝ) * α := by
      have h2 : ((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α
          = ((k - l : ℤ) : ℝ) * α - (m : ℝ) * ((qn : ℝ) * α) := by rw [h]; push_cast; ring
      rw [h2]; ring
    have key := s0q4_nn_add_le (((s0q4Idx U m qn k - s0q4Idx U m qn l : ℤ) : ℝ) * α)
      ((m : ℝ) * ((qn : ℝ) * α))
    rw [hreal] at key
    linarith

/-- **Separation inside a block**: the shifted sites of a block of `q (n-1)` consecutive
indices are `3/(10 q(n-1))`-separated. -/
lemma s0q4_sep_blk {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {m : ℤ} {p k l : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = 4 * q (n - 1)) (hHq : H < q n)
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hk : k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1))
    (hl : l ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1)) (hkl : k ≠ l) :
    (3 : ℝ) / (10 * (q (n - 1) : ℝ)) ≤
      Work.TMC16Core.fracDist (((s0q4Idx U m (q n) k - s0q4Idx U m (q n) l : ℤ) : ℝ) * α) := by
  rw [Finset.mem_Icc] at hk hl
  have hd1 : 1 ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hkl)
  have hdL : |k - l| < (q (n - 1) : ℤ) := by
    have hle : |k - l| ≤ (q (n - 1) : ℤ) - 1 := by rw [abs_le]; constructor <;> omega
    omega
  have hsl : 1 / (2 * (q (n - 1) : ℝ)) ≤
      Work.TMC16Core.fracDist (((k - l : ℤ) : ℝ) * α) :=
    s0q4_fracDist_small hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (by omega) hd1 hdL
  have hmqΔ := s0q4_fracDist_mqn_le hqpos hΔpos hΔeq hΔup hmq
  have hge := s0q4_idx_diff_ge (U := U) (m := m) (qn := q n) (k := k) (l := l) (α := α)
  have hLpos : (0 : ℝ) < (q (n - 1) : ℝ) := by
    have h0 : 0 < q 0 := hqpos 0
    have h1 : (0 : ℝ) < (q 0 : ℝ) := by exact_mod_cast h0
    have h2 : (q 0 : ℝ) ≤ (q (n - 1) : ℝ) := by
      exact_mod_cast hmono.monotone (by omega)
    linarith
  have h40 : (1 : ℝ) / (10 * (q n : ℝ)) ≤ 1 / (40 * (q (n - 1) : ℝ)) := by
    have h4 : (4 : ℝ) * (q (n - 1) : ℝ) < (q n : ℝ) := by
      have h3 : (H : ℝ) < (q n : ℝ) := by exact_mod_cast hHq
      calc (4 : ℝ) * (q (n - 1) : ℝ) = (H : ℝ) := by rw [hH]; push_cast; ring
        _ < (q n : ℝ) := h3
    have h6 : 10 * (q n : ℝ) ≥ 40 * (q (n - 1) : ℝ) := by linarith
    exact one_div_le_one_div_of_le (by linarith) h6
  have hfin : (3 : ℝ) / (10 * (q (n - 1) : ℝ)) ≤
      1 / (2 * (q (n - 1) : ℝ)) - 1 / (40 * (q (n - 1) : ℝ)) := by
    have h1 : (1 : ℝ) / (2 * (q (n - 1) : ℝ)) - 1 / (40 * (q (n - 1) : ℝ))
        = 19 / (40 * (q (n - 1) : ℝ)) := by field_simp; ring
    have h2 : (3 : ℝ) / (10 * (q (n - 1) : ℝ)) = 12 / (40 * (q (n - 1) : ℝ)) := by
      field_simp; ring
    rw [h1, h2]
    have h : (0 : ℝ) < 40 * (q (n - 1) : ℝ) := by linarith
    rw [div_le_div_iff_of_pos_right h]; linarith
  linarith [hsl, hmqΔ, hge, h40, hfin]

/-- **Separation of the window**: distinct shifted indices of `[1,H]` are separated by
`2/(5 q n)`. -/
lemma s0q4_sep_global {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {m : ℤ} {k l : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 1 ≤ n) (hH : H = 4 * q (n - 1)) (hHq : H < q n)
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hk : k ∈ Finset.Icc 1 (H : ℤ)) (hl : l ∈ Finset.Icc 1 (H : ℤ)) (hkl : k ≠ l) :
    2 / (5 * (q n : ℝ)) ≤
      Work.TMC16Core.fracDist (((s0q4Idx U m (q n) k - s0q4Idx U m (q n) l : ℤ) : ℝ) * α) := by
  rw [Finset.mem_Icc] at hk hl
  have hd1 : 1 ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hkl)
  have hdH : |k - l| < (q n : ℤ) := by
    have hle : |k - l| ≤ (H : ℤ) - 1 := by rw [abs_le]; constructor <;> omega
    have h3 : (H : ℤ) < (q n : ℤ) := by exact_mod_cast hHq
    omega
  have hsl : 1 / (2 * (q n : ℝ)) ≤ Work.TMC16Core.fracDist (((k - l : ℤ) : ℝ) * α) :=
    s0q4_fracDist_lt_qn hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hd1 hdH
  have hmqΔ := s0q4_fracDist_mqn_le hqpos hΔpos hΔeq hΔup hmq
  have hge := s0q4_idx_diff_ge (U := U) (m := m) (qn := q n) (k := k) (l := l) (α := α)
  have hfin : 2 / (5 * (q n : ℝ)) = 1 / (2 * (q n : ℝ)) - 1 / (10 * (q n : ℝ)) := by
    ring
  linarith [hsl, hmqΔ, hge, hfin]

/-! ## The block estimate for the shifted blocks -/

/-- The two-sided block estimate for a block of `L` consecutive `k`-indices, at the phase `ξ`
and with the shift `s0q4Idx`. -/
def S0q4Blk (U : ℕ) (m : ℤ) (qn L : ℕ) (ξ α : ℝ) : Prop :=
  ∀ (p0 k₀ : ℤ), k₀ ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1) →
    (∀ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k₀ : ℤ) : ℝ) * α))|) →
    |∑ k ∈ (Finset.Icc p0 (p0 + (L : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|
      + ((L : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (L : ℝ)

/-- **The block estimate** (from `Core.irrat_blk_nr` when `m = 0` and from
`Core.irrat_blk_shift` otherwise). -/
theorem s0q4_blk_est {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = 4 * q (n - 1)) (hHq : H < q n)
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (ξ : ℝ) : S0q4Blk U m (q n) (q (n - 1)) ξ α := by
  intro p0 k₀ hk₀ hmin
  have hL1 : 1 ≤ q (n - 1) := by
    have h0 : 1 ≤ q 0 := hqpos 0
    exact le_trans h0 (hmono.monotone (by omega))
  by_cases hm0 : m = 0
  · subst hm0
    have hidx : ∀ k : ℤ, s0q4Idx U 0 (q n) k = k := fun k => by simp [s0q4Idx, s0q4Lsh]
    have hmin' : ∀ k ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))| := by
      intro k hk
      have := hmin k hk
      rwa [hidx k, hidx k₀] at this
    have h := Work.TMC16Core.Core.irrat_blk_nr hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      (by omega : 1 ≤ n) hk₀ hmin'
    simpa only [hidx] using h
  · set ℓ : ℕ := m.natAbs + 1 with hℓdef
    have hℓ1 : 1 ≤ ℓ := by omega
    have hℓZ : ((ℓ : ℤ)) = |m| + 1 := by
      simp only [hℓdef]
      have : (((m.natAbs : ℕ)) : ℤ) = |m| := by
        rcases Int.natAbs_eq m with h | h <;> rw [h] <;> simp
      omega
    have hLsh : ∀ k : ℤ, |s0q4Lsh U m k| ≤ (ℓ : ℤ) - 1 := by
      intro k
      have := s0q4Lsh_abs U m k
      omega
    have hweak : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
      have := hmq hm0
      rw [hℓZ]
      convert this using 2 <;> ring
    have hstrict := Work.TMC16Core.Core.res_strict_hℓb hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      (by omega : 1 ≤ n) hℓ1 hweak
    have hmin' : ∀ k ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + ((k + s0q4Lsh U m k * (q n : ℤ) : ℤ) : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + ((k₀ + s0q4Lsh U m k₀ * (q n : ℤ) : ℤ) : ℝ) * α))| := by
      intro k hk
      simpa only [s0q4Idx] using hmin k hk
    have hblk := Work.TMC16Core.Core.irrat_blk_shift hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
      (n := n - 1) (r := n) (Nat.sub_le n 1) hℓ1 hstrict (Lsh := s0q4Lsh U m) hLsh hk₀ hmin'
    -- numeric bound of the error term
    have hLpos : (0 : ℝ) < (q (n - 1) : ℝ) := by exact_mod_cast hL1
    have hqnpos : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
    have hlogL : (0 : ℝ) ≤ Real.log (q (n - 1) : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
    have h4L : (4 : ℝ) * (q (n - 1) : ℝ) < (q n : ℝ) := by
      have h3 : (H : ℝ) < (q n : ℝ) := by exact_mod_cast hHq
      calc (4 : ℝ) * (q (n - 1) : ℝ) = (H : ℝ) := by rw [hH]; push_cast; ring
        _ < (q n : ℝ) := h3
    have hd1 : Δ (n - 1) * (q (n - 1) : ℝ) < 1 / 4 := by
      have h5 : Δ (n - 1) < 1 / (q n : ℝ) := by
        have h6 := hΔup (n - 1)
        have h7 : n - 1 + 1 = n := by omega
        rwa [h7] at h6
      have h6 : (1 / (q n : ℝ)) * (q (n - 1) : ℝ) < 1 / 4 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hqnpos]
        linarith
      linarith [mul_lt_mul_of_pos_right h5 hLpos]
    have hd2 : (ℓ : ℝ) * Δ n * (q (n - 1) : ℝ) < 1 / 40 := by
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
      have hq1 : (0 : ℝ) < (q (n + 1) : ℝ) := by have := hqpos (n + 1); exact_mod_cast this
      have h10 : (10 : ℝ) * (ℓ : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by exact_mod_cast hweak
      have hA : (ℓ : ℝ) * Δ n < 1 / (10 * (q n : ℝ)) := by
        have h5 : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
        have h6 : (ℓ : ℝ) * Δ n < (ℓ : ℝ) * (1 / (q (n + 1) : ℝ)) :=
          mul_lt_mul_of_pos_left h5 hℓpos
        have h7 : (ℓ : ℝ) * (1 / (q (n + 1) : ℝ)) ≤ 1 / (10 * (q n : ℝ)) := by
          rw [mul_one_div, div_le_iff₀ hq1, div_mul_eq_mul_div,
            le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (q n : ℝ))]
          linarith
        linarith
      have h8 : (ℓ : ℝ) * Δ n * (q (n - 1) : ℝ) < (1 / (10 * (q n : ℝ))) * (q (n - 1) : ℝ) :=
        mul_lt_mul_of_pos_right hA hLpos
      have h9 : (1 / (10 * (q n : ℝ))) * (q (n - 1) : ℝ) < 1 / 40 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 10 * (q n : ℝ))]
        linarith
      linarith
    have herr : Real.log (q (n - 1) : ℝ)
        + 32 * ((Δ (n - 1) + (ℓ : ℝ) * Δ n) * (q (n - 1) : ℝ) * Real.log (q (n - 1) : ℝ))
        ≤ 32 * Real.log (q (n - 1) : ℝ) := by
      have h31 : 32 * ((Δ (n - 1) + (ℓ : ℝ) * Δ n) * (q (n - 1) : ℝ)) ≤ 31 := by linarith
      have h32 : 32 * ((Δ (n - 1) + (ℓ : ℝ) * Δ n) * (q (n - 1) : ℝ) * Real.log (q (n - 1) : ℝ))
          ≤ 31 * Real.log (q (n - 1) : ℝ) := by
        calc 32 * ((Δ (n - 1) + (ℓ : ℝ) * Δ n) * (q (n - 1) : ℝ) * Real.log (q (n - 1) : ℝ))
            = (32 * ((Δ (n - 1) + (ℓ : ℝ) * Δ n) * (q (n - 1) : ℝ))) * Real.log (q (n - 1) : ℝ) := by
              ring
          _ ≤ 31 * Real.log (q (n - 1) : ℝ) := mul_le_mul_of_nonneg_right h31 hlogL
      linarith
    have := hblk
    simp only [s0q4Idx] at this ⊢
    linarith [this, herr]

/-- Upper bound for the sum over a whole block. -/
lemma s0q4_blk_le {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α) (hL : 1 ≤ L)
    (p0 : ℤ) :
    ∑ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1),
        Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|
      ≤ -((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) := by
  have hne : (Finset.Icc p0 (p0 + (L : ℤ) - 1)).Nonempty :=
    ⟨p0, by rw [Finset.mem_Icc]; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p0 (p0 + (L : ℤ) - 1))
    (fun k => |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|) hne
  have hb' := hb p0 k₀ hk₀ (fun k hk => hk₀min k hk)
  refine Work.TMC16Core.Core.blk_sum_le hk₀ (Work.TMC16Core.Core.log_abs_sin_nonpos _) ?_
  have h := (abs_le.mp hb').2
  linarith

/-- Upper bound for the sum over a block with one index removed. -/
lemma s0q4_blk_le_erase {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α)
    (hL : 1 ≤ L) {p0 k_j : ℤ} (hk_j : k_j ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1))
    (hnz : ∀ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1), k ≠ k_j →
      Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α)) ≠ 0) :
    ∑ k ∈ (Finset.Icc p0 (p0 + (L : ℤ) - 1)).erase k_j,
        Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|
      ≤ -((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) := by
  have hne : (Finset.Icc p0 (p0 + (L : ℤ) - 1)).Nonempty :=
    ⟨p0, by rw [Finset.mem_Icc]; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p0 (p0 + (L : ℤ) - 1))
    (fun k => |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|) hne
  have hb' := hb p0 k₀ hk₀ (fun k hk => hk₀min k hk)
  have hfk : Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k₀ : ℤ) : ℝ) * α))|
      ≤ Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k_j : ℤ) : ℝ) * α))| := by
    rcases eq_or_ne k₀ k_j with h | h
    · rw [h]
    · have hpos : 0 < |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k₀ : ℤ) : ℝ) * α))| := by
        rw [abs_pos]
        exact hnz k₀ hk₀ h
      exact Real.log_le_log hpos (hk₀min k_j hk_j)
  refine Work.TMC16Core.Core.blk_sum_le_erase hk₀ hk_j hfk ?_
  have h := (abs_le.mp hb').2
  linarith

/-- Lower bound for the sum over a whole block, given a lower bound for every term. -/
lemma s0q4_blk_ge {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α) (hL : 1 ≤ L)
    {p0 : ℤ} {B0 : ℝ}
    (hB0 : ∀ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1),
      B0 ≤ Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|) :
    -((L : ℝ) - 1) * Real.log 2 - 32 * Real.log (L : ℝ) + B0
      ≤ ∑ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1),
          Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))| := by
  have hne : (Finset.Icc p0 (p0 + (L : ℤ) - 1)).Nonempty :=
    ⟨p0, by rw [Finset.mem_Icc]; omega⟩
  obtain ⟨k₀, hk₀, hk₀min⟩ := Finset.exists_min_image (Finset.Icc p0 (p0 + (L : ℤ) - 1))
    (fun k => |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|) hne
  have hb' := hb p0 k₀ hk₀ (fun k hk => hk₀min k hk)
  refine Work.TMC16Core.Core.blk_sum_ge hk₀ (hB0 k₀ hk₀) ?_
  have h := (abs_le.mp hb').1
  linarith

/-- Lower bound for the sum over a block whose removed index is a zero of the sine. -/
lemma s0q4_blk_ge_zero {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α)
    (hL : 1 ≤ L) {p0 k_j : ℤ} (hk_j : k_j ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1))
    (h0 : Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k_j : ℤ) : ℝ) * α)) = 0) :
    -((L : ℝ) - 1) * Real.log 2 - 32 * Real.log (L : ℝ)
      ≤ ∑ k ∈ (Finset.Icc p0 (p0 + (L : ℤ) - 1)).erase k_j,
          Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))| := by
  have hb' := hb p0 k_j hk_j (fun k hk => by rw [h0, abs_zero]; exact abs_nonneg _)
  have h := (abs_le.mp hb').1
  linarith

/-- The four-fold block decomposition of the index set `[1, 4L]`. -/
private lemma s0q4_erase_union {A B : Finset ℤ} {c : ℤ} :
    (A ∪ B).erase c = A.erase c ∪ B.erase c := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union]
  tauto

private lemma s0q4_blocks_eq {L : ℕ} (hL : 1 ≤ L) :
    Finset.Icc (1 : ℤ) (4 * (L : ℤ)) =
      (((Finset.Icc (1 : ℤ) (L : ℤ) ∪ Finset.Icc ((L : ℤ) + 1) (2 * (L : ℤ)))
        ∪ Finset.Icc (2 * (L : ℤ) + 1) (3 * (L : ℤ)))
        ∪ Finset.Icc (3 * (L : ℤ) + 1) (4 * (L : ℤ))) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union]
  constructor
  · intro h
    by_cases h1 : x ≤ L
    · exact Or.inl (Or.inl (Or.inl ⟨h.1, h1⟩))
    · by_cases h2 : x ≤ 2 * L
      · exact Or.inl (Or.inl (Or.inr ⟨by omega, h2⟩))
      · by_cases h3 : x ≤ 3 * L
        · exact Or.inl (Or.inr ⟨by omega, h3⟩)
        · exact Or.inr ⟨by omega, h.2⟩
  · rintro (((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩) <;> omega

/-- The sum over `[1,4L]` with one point removed, split into the four blocks of length `L`. -/
lemma s0q4_sum4 {L : ℕ} (hL : 1 ≤ L) (f : ℤ → ℝ) (c : ℤ) :
    ∑ k ∈ (Finset.Icc (1 : ℤ) (4 * (L : ℤ))).erase c, f k
      = (∑ k ∈ (Finset.Icc (1 : ℤ) (L : ℤ)).erase c, f k)
        + (∑ k ∈ (Finset.Icc ((L : ℤ) + 1) (2 * (L : ℤ))).erase c, f k)
        + (∑ k ∈ (Finset.Icc (2 * (L : ℤ) + 1) (3 * (L : ℤ))).erase c, f k)
        + (∑ k ∈ (Finset.Icc (3 * (L : ℤ) + 1) (4 * (L : ℤ))).erase c, f k) := by
  set A : Finset ℤ := Finset.Icc (1 : ℤ) (L : ℤ) with hA
  set B : Finset ℤ := Finset.Icc ((L : ℤ) + 1) (2 * (L : ℤ)) with hB
  set C : Finset ℤ := Finset.Icc (2 * (L : ℤ) + 1) (3 * (L : ℤ)) with hC
  set D : Finset ℤ := Finset.Icc (3 * (L : ℤ) + 1) (4 * (L : ℤ)) with hD
  have hset : Finset.Icc (1 : ℤ) (4 * (L : ℤ)) = ((A ∪ B) ∪ C) ∪ D := by
    rw [s0q4_blocks_eq hL, hA, hB, hC, hD]
  have hd01 : Disjoint A B := by
    rw [hA, hB, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have hd02 : Disjoint A C := by
    rw [hA, hC, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have hd03 : Disjoint A D := by
    rw [hA, hD, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have hd12 : Disjoint B C := by
    rw [hB, hC, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have hd13 : Disjoint B D := by
    rw [hB, hD, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have hd23 : Disjoint C D := by
    rw [hC, hD, Finset.disjoint_left]; intro x hx hy; rw [Finset.mem_Icc] at hx hy; omega
  have e01 : Disjoint (A.erase c) (B.erase c) :=
    hd01.mono (Finset.erase_subset c A) (Finset.erase_subset c B)
  have e02 : Disjoint (A.erase c) (C.erase c) :=
    hd02.mono (Finset.erase_subset c A) (Finset.erase_subset c C)
  have e03 : Disjoint (A.erase c) (D.erase c) :=
    hd03.mono (Finset.erase_subset c A) (Finset.erase_subset c D)
  have e12 : Disjoint (B.erase c) (C.erase c) :=
    hd12.mono (Finset.erase_subset c B) (Finset.erase_subset c C)
  have e13 : Disjoint (B.erase c) (D.erase c) :=
    hd13.mono (Finset.erase_subset c B) (Finset.erase_subset c D)
  have e23 : Disjoint (C.erase c) (D.erase c) :=
    hd23.mono (Finset.erase_subset c C) (Finset.erase_subset c D)
  have u02 : Disjoint (A.erase c ∪ B.erase c) (C.erase c) :=
    Finset.disjoint_union_left.mpr ⟨e02, e12⟩
  have u03 : Disjoint (A.erase c ∪ B.erase c) (D.erase c) :=
    Finset.disjoint_union_left.mpr ⟨e03, e13⟩
  have u012 : Disjoint ((A.erase c ∪ B.erase c) ∪ C.erase c) (D.erase c) :=
    Finset.disjoint_union_left.mpr ⟨u03, e23⟩
  rw [hset, s0q4_erase_union, s0q4_erase_union, s0q4_erase_union,
    Finset.sum_union u012, Finset.sum_union u02, Finset.sum_union e01]

/-! ## Wrappers: block sums with an arbitrary removed index, and the `θ`-pair range -/

/-- Upper bound for the block sum with an arbitrary index removed (which may lie outside the
block). -/
lemma s0q4_blk_le_erase_any {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α)
    (hL : 1 ≤ L) {p0 kj : ℤ}
    (hnz : ∀ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1), k ≠ kj →
      Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α)) ≠ 0) :
    ∑ k ∈ (Finset.Icc p0 (p0 + (L : ℤ) - 1)).erase kj,
        Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|
      ≤ -((L : ℝ) - 1) * Real.log 2 + 32 * Real.log (L : ℝ) := by
  by_cases hkj : kj ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1)
  · exact s0q4_blk_le_erase hb hL hkj hnz
  · rw [Finset.erase_eq_of_notMem hkj]
    exact s0q4_blk_le hb hL p0

/-- Lower bound for the block sum with an arbitrary index removed. -/
lemma s0q4_blk_ge_erase_any {U : ℕ} {m : ℤ} {qn L : ℕ} {ξ α : ℝ} (hb : S0q4Blk U m qn L ξ α)
    (hL : 1 ≤ L) {p0 kj : ℤ} {B0 : ℝ}
    (hB0 : ∀ k ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1),
      B0 ≤ Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|) :
    -((L : ℝ) - 1) * Real.log 2 - 32 * Real.log (L : ℝ) + B0
      ≤ ∑ k ∈ (Finset.Icc p0 (p0 + (L : ℤ) - 1)).erase kj,
          Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))| := by
  by_cases hkj : kj ∈ Finset.Icc p0 (p0 + (L : ℤ) - 1)
  · have h1 := s0q4_blk_ge hb hL hB0
    have h2 := Work.TMC16Core.Core.sum_erase_ge_of_nonpos
      (f := fun k : ℤ => Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m qn k : ℤ) : ℝ) * α))|)
      hkj (Work.TMC16Core.Core.log_abs_sin_nonpos _)
    linarith
  · rw [Finset.erase_eq_of_notMem hkj]
    exact s0q4_blk_ge hb hL hB0

/-- The four points at which the phase `ξ = -(p_k)·α` is separated from `ℤ`. -/
lemma s0q4_erase_image {U : ℕ} {m : ℤ} {qn H : ℕ} {kj : ℤ}
    (hinj : Set.InjOn (fun k : ℤ => s0q4Idx U m qn k) ↑(Finset.Icc (1 : ℤ) (H : ℤ)))
    (hkj : kj ∈ Finset.Icc (1 : ℤ) (H : ℤ)) :
    ((Finset.Icc (1 : ℤ) (H : ℤ)).image (fun k : ℤ => s0q4Idx U m qn k)).erase
        (s0q4Idx U m qn kj)
      = ((Finset.Icc (1 : ℤ) (H : ℤ)).erase kj).image (fun k : ℤ => s0q4Idx U m qn k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hne, hximg⟩ := hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hximg
    refine Finset.mem_image.mpr ⟨k, ?_, hkx⟩
    exact Finset.mem_erase.mpr ⟨fun h => hne (by rw [← hkx, h]), hk⟩
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_erase] at hk
    exact Finset.mem_erase.mpr ⟨fun hcontra => hk.1 (hinj hk.2 hkj (hkx.trans hcontra)),
      Finset.mem_image.mpr ⟨k, hk.2, hkx⟩⟩

/-- The `θ`-range condition for a pair of window indices. -/
lemma s0q4_theta_pair {α θ : ℝ} {qn H U : ℕ} {m A0 k l : ℤ}
    (hA0b : 2 * |A0| + 2 * (H : ℤ) ≤ 8 * (H : ℤ) + 8)
    (hk : k ∈ Finset.Icc 1 (H : ℤ)) (hl : l ∈ Finset.Icc 1 (H : ℤ)) :
    ∃ t j : ℤ, (t = 0 ∨ t = 1 ∨ t = 2) ∧ |j| ≤ 8 * (H : ℤ) + 8 ∧
      2 * (θ + (A0 : ℝ) * α) + ((s0q4Idx U m qn k + s0q4Idx U m qn l : ℤ) : ℝ) * α
        = 2 * θ + (((j + t * m * (qn : ℤ) : ℤ)) : ℝ) * α := by
  obtain ⟨t, ht, hadd⟩ := s0q4Idx_add_eq U m qn k l
  refine ⟨t, 2 * A0 + k + l, ht, ?_, ?_⟩
  · rw [Finset.mem_Icc] at hk hl
    have hkb : |k| ≤ (H : ℤ) := by
      rw [abs_of_pos (by omega : (0 : ℤ) < k)]; exact hk.2
    have hlb : |l| ≤ (H : ℤ) := by
      rw [abs_of_pos (by omega : (0 : ℤ) < l)]; exact hl.2
    have hthis : |2 * A0 + k + l| ≤ 2 * |A0| + |k| + |l| := by
      calc |2 * A0 + k + l| ≤ |2 * A0 + k| + |l| := abs_add_le _ _
        _ ≤ (|2 * A0| + |k|) + |l| := by
              have h := abs_add_le (2 * A0) k; linarith
        _ = 2 * |A0| + |k| + |l| := by rw [abs_mul]; norm_num
    omega
  · rw [hadd]
    push_cast
    ring

/-- The set of shifted indices of the `q4` window. -/
def S0q4Set (U H : ℕ) (m : ℤ) (qn : ℕ) : Finset ℤ :=
  (Finset.Icc 1 (H : ℤ)).image (fun k : ℤ => s0q4Idx U m qn k)

lemma s0q4_fwd_mem {a : ℤ} {U H : ℕ} {m : ℤ} {qn : ℕ} {j : ℤ}
    (h2U : 2 * U ≤ H)
    (hj : j ∈ W1s0 a U ∪ W2s0 a U H (m * (qn : ℤ))) : j + 1 - a ∈ S0q4Set U H m qn := by
  rw [Finset.mem_union] at hj
  rcases hj with hj | hj
  · rw [W1s0, Finset.mem_Icc] at hj
    obtain ⟨h1, h2⟩ := hj
    refine Finset.mem_image.mpr ⟨j + 1 - a, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have : 2 * (U : ℤ) ≤ (H : ℤ) := by exact_mod_cast h2U
      constructor <;> omega
    · exact s0q4Idx_of_le (by omega)
  · rw [W2s0, Finset.mem_Icc] at hj
    obtain ⟨h1, h2⟩ := hj
    refine Finset.mem_image.mpr ⟨j + 1 - a - m * (qn : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · rw [s0q4Idx_of_lt (by omega)]
      ring

lemma s0q4_inv_mem {a : ℤ} {U H : ℕ} {m : ℤ} {qn : ℕ} {p : ℤ}
    (hp : p ∈ S0q4Set U H m qn) : p + a - 1 ∈ W1s0 a U ∪ W2s0 a U H (m * (qn : ℤ)) := by
  rw [S0q4Set, Finset.mem_image] at hp
  obtain ⟨k, hk, hkp⟩ := hp
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_union, W1s0, W2s0]
  rcases le_or_gt k (2 * (U : ℤ)) with hk2U | hk2U
  · left
    rw [Finset.mem_Icc]
    have hpk : p = k := by rw [← hkp, s0q4Idx_of_le hk2U]
    omega
  · right
    rw [Finset.mem_Icc]
    have hpk : p = k + m * (qn : ℤ) := by rw [← hkp, s0q4Idx_of_lt hk2U]
    omega

/-- The site window of the `q4` branch is the shifted-index set `S0q4Set`. -/
def s0q4Equiv (a : ℤ) (U H : ℕ) (m : ℤ) (qn : ℕ) (h2U : 2 * U ≤ H) :
    {j : ℤ // j ∈ W1s0 a U ∪ W2s0 a U H (m * (qn : ℤ))} ≃ {p : ℤ // p ∈ S0q4Set U H m qn} where
  toFun j := ⟨j.1 + 1 - a, s0q4_fwd_mem h2U j.2⟩
  invFun p := ⟨p.1 + a - 1, s0q4_inv_mem p.2⟩
  left_inv j := Subtype.ext (by ring)
  right_inv p := Subtype.ext (by ring)

theorem s0q4_budget {cθ H L X : ℝ} (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2)
    (hL : 1 ≤ L) (hH : H = 4 * L) (hX : 0 < X) (hXH : X ≤ H ^ 2) :
    2 * (128 * Real.log L + 3 * Real.log 2)
      + (128 * Real.log L + 3 * Real.log 2 + 2 * Real.log (1 / (2 * cθ)))
      + (128 * Real.log L + 3 * Real.log 2 + 3 * Real.log (5 * X / 2))
      + 2 * Real.log (1 / (2 * cθ)) + Real.log (5 * X / 2)
    ≤ 1200 * Real.log H + 32 * Real.log (1 / cθ) + 8 * Real.log (2 * H) := by
  have hHpos : (0 : ℝ) < H := by linarith
  have hlogH : (0 : ℝ) ≤ Real.log H := Real.log_nonneg (by linarith)
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogLle : Real.log L ≤ Real.log H := Real.log_le_log (by linarith) (by linarith)
  have hcθ2 : (2 : ℝ) ≤ 1 / cθ := by rw [le_div_iff₀ hcθ]; linarith
  have hlogcθ : Real.log 2 ≤ Real.log (1 / cθ) := Real.log_le_log (by norm_num) hcθ2
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog4le : Real.log 4 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by linarith)
  have hXlog : Real.log X ≤ 2 * Real.log H := by
    have h1 : Real.log X ≤ Real.log (H ^ 2) := Real.log_le_log hX hXH
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  have h5X : Real.log (5 * X / 2) = Real.log (5 / 2) + Real.log X := by
    rw [show (5 : ℝ) * X / 2 = (5 / 2) * X by ring, Real.log_mul (by norm_num) hX.ne']
  have h52 : Real.log (5 / 2) ≤ 3 / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 2 by norm_num)
    linarith
  have h1over : Real.log (1 / (2 * cθ)) = Real.log (1 / cθ) - Real.log 2 := by
    rw [show (1 : ℝ) / (2 * cθ) = (1 / cθ) / 2 by field_simp]
    rw [Real.log_div (by positivity) (by norm_num)]
  have h2H : Real.log (2 * H) = Real.log 2 + Real.log H := Real.log_mul (by norm_num) hHpos.ne'
  have hLHS : 2 * (128 * Real.log L + 3 * Real.log 2)
      + (128 * Real.log L + 3 * Real.log 2 + 2 * Real.log (1 / (2 * cθ)))
      + (128 * Real.log L + 3 * Real.log 2 + 3 * Real.log (5 * X / 2))
      + 2 * Real.log (1 / (2 * cθ)) + Real.log (5 * X / 2)
      = 512 * Real.log L + 8 * Real.log 2 + 4 * Real.log (1 / cθ) + 4 * Real.log (5 / 2)
        + 4 * Real.log X := by
    rw [h5X, h1over]; ring
  rw [hLHS, h2H]
  have hstep1 : 512 * Real.log L + 8 * Real.log 2 + 4 * Real.log (1 / cθ) + 4 * Real.log (5 / 2)
      + 4 * Real.log X ≤ 520 * Real.log H + 8 * Real.log 2 + 4 * Real.log (1 / cθ) + 6 := by
    linarith [hlogLle, h52, hXlog]
  have hbig : (6 : ℝ) ≤ 688 * Real.log H + 28 * Real.log (1 / cθ) := by
    have h3 : (688 * 2) * Real.log 2 ≤ 688 * Real.log H := by
      have h := hlog4le
      rw [hlog4] at h
      linarith
    nlinarith [h3, hlogcθ, Real.log_two_gt_d9]
  have hstep2 : 520 * Real.log H + 8 * Real.log 2 + 4 * Real.log (1 / cθ) + 6
      ≤ 1200 * Real.log H + 32 * Real.log (1 / cθ) + 8 * (Real.log 2 + Real.log H) := by
    linarith [hbig]
  linarith [hstep1, hstep2]

theorem s0_uniform_q4 {α θ ε cθ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {a m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = 4 * q (n - 1)) (hHq : H < q n)
    (hqH : (q n : ℝ) ≤ (H : ℝ) ^ 2) (hH2 : 2 ≤ H) (h2U : 2 * U ≤ H)
    (ha : |a| ≤ 2 * (H : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2)
    (hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * (H : ℤ) + 8 →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α))
    (hbudget : 1200 * Real.log (H : ℝ) + 32 * Real.log (1 / cθ) + 8 * Real.log (2 * (H : ℝ))
      < ((H : ℝ) - 1) * ε) :
    Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
          Work.TMC16Core.Assembly.W2s0 a U H (m * (q n : ℤ))} =>
        θ + (((j : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α) := by
  have hn1 : 1 ≤ n := by omega
  have hH4 : (H : ℤ) = 4 * (q (n - 1) : ℤ) := by rw [hH]; push_cast; ring
  have hH4R : (H : ℝ) = 4 * (q (n - 1) : ℝ) := by rw [hH]; push_cast; ring
  have hL1 : 1 ≤ q (n - 1) := le_trans (hqpos 0) (hmono.monotone (by omega))
  have hLpR : (0 : ℝ) < (q (n - 1) : ℝ) := by exact_mod_cast hL1
  have hqnp : (0 : ℝ) < (q n : ℝ) := by have := hqpos n; exact_mod_cast this
  have hHpR : (0 : ℝ) < (H : ℝ) := by rw [hH4R]; linarith
  set ch : ℤ := 2 * (q (n - 1) : ℤ) - 1 with hch
  have hchR : (ch : ℝ) = ((H : ℝ) - 2) / 2 := by rw [hch, hH4R]; push_cast; ring
  set A0 : ℤ := a + ch - 1 with hA0
  have hA0b : 2 * |A0| + 2 * (H : ℤ) ≤ 8 * (H : ℤ) + 8 := by
    have hchb : 2 * |ch| ≤ (H : ℤ) + 2 := by
      have hA : |2 * (q (n - 1) : ℤ) - 1| ≤ 2 * (q (n - 1) : ℤ) + 1 := by
        rw [abs_le]; constructor <;> omega
      rw [hch, hH4]
      linarith
    have h1 : |A0| ≤ 2 * (H : ℤ) + |ch| + 1 := by
      rw [hA0]
      have h2 : |a + ch - 1| ≤ |a| + |ch| + 1 := by
        calc |a + ch - 1| ≤ |a + ch| + |(-1 : ℤ)| := abs_add_le _ _
          _ = |a + ch| + 1 := by norm_num
          _ ≤ (|a| + |ch|) + 1 := by linarith [abs_add_le a ch]
      linarith [ha]
    omega
  set th : ℝ := θ + (A0 : ℝ) * α with hth
  have hinj : Set.InjOn (fun k : ℤ => s0q4Idx U m (q n) k) ↑(Finset.Icc 1 (H : ℤ)) :=
    fun x hx y hy hxy => s0q4Idx_injOn hHq hx hy hxy
  have hScard : (S0q4Set U H m (q n)).card = H := by
    rw [S0q4Set, Finset.card_image_of_injOn hinj]
    rw [Int.card_Icc]
    have h1 : (H : ℤ) + 1 - 1 = (H : ℤ) := by ring
    rw [h1, Int.toNat_natCast]
  have hcardR : ((S0q4Set U H m (q n)).card : ℝ) - 1 = (H : ℝ) - 1 := by rw [hScard]
  have hb : ∀ ξ : ℝ, S0q4Blk U m (q n) (q (n - 1)) ξ α :=
    fun ξ => s0q4_blk_est hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq hmq ξ
  set Acoef : ℝ := 128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2 with hAcoef
  set Bcoef : ℝ := 128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2
    + 2 * Real.log (1 / (2 * cθ)) with hBcoef
  set csep : ℝ := 1 / (5 * (q n : ℝ)) with hcsepdef
  have hcsep : 0 < csep := by rw [hcsepdef]; exact one_div_pos.mpr (by positivity)
  have hcsepval : 1 / (2 * csep) = 5 * (q n : ℝ) / 2 := by rw [hcsepdef]; field_simp
  set Ccoef : ℝ := 128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2
    + 3 * Real.log (5 * (q n : ℝ) / 2) with hCcoef
  have hsuball : ∀ p0 : ℤ, (1 : ℤ) ≤ p0 → p0 + (q (n - 1) : ℤ) - 1 ≤ (H : ℤ) →
      ∀ k' ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1), k' ∈ Finset.Icc (1 : ℤ) (H : ℤ) := by
    intro p0 h1 h2 k' hk'
    rw [Finset.mem_Icc] at hk' ⊢
    exact ⟨by omega, by omega⟩
  have hKB' : Finset.Icc (1 : ℤ) (H : ℤ) = Finset.Icc (1 : ℤ) (4 * (q (n - 1) : ℤ)) := by
    rw [hH4]
  have h2pi_real : (2 * Real.pi) ≠ 0 := by positivity
  have hcos : ∀ i ∈ S0q4Set U H m (q n), ∀ j ∈ S0q4Set U H m (q n), i ≠ j →
      Real.cos (2 * Real.pi * (th + (i : ℝ) * α)) ≠ Real.cos (2 * Real.pi * (th + (j : ℝ) * α)) := by
    intro i hi j hj hij hcon
    rw [S0q4Set] at hi hj
    obtain ⟨ki, hki, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hj
    have hkine : ki ≠ kj := fun h => hij (by rw [h])
    rw [Real.cos_eq_cos_iff] at hcon
    obtain ⟨k, hk | hk⟩ := hcon
    · have h2pi : (2 * Real.pi) ≠ 0 := by positivity
      have h3 : 2 * Real.pi * (th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
          - 2 * Real.pi * (th + ((s0q4Idx U m (q n) ki : ℤ) : ℝ) * α) = (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
          - 2 * Real.pi * (th + ((s0q4Idx U m (q n) ki : ℤ) : ℝ) * α)
          = (2 * Real.pi) * (((s0q4Idx U m (q n) kj - s0q4Idx U m (q n) ki : ℤ) : ℝ) * α) := by
        push_cast; ring
      rw [h4] at h3
      have h2' : (2 * Real.pi) * (((s0q4Idx U m (q n) kj - s0q4Idx U m (q n) ki : ℤ) : ℝ) * α)
          = (2 * Real.pi) * (k : ℝ) := by linarith [h3]
      have hz := mul_left_cancel₀ h2pi h2'
      have hfd0 : Work.TMC16Core.fracDist (((s0q4Idx U m (q n) kj - s0q4Idx U m (q n) ki : ℤ) : ℝ) * α) = 0 := by
        rw [hz, Work.TMC16Core.Core.fracDist_intCast]
      have hsep := s0q4_sep_global (U := U) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hH hHq hmq hki hkj hkine
      have hev : (((s0q4Idx U m (q n) ki - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α
          = -((((s0q4Idx U m (q n) kj - s0q4Idx U m (q n) ki : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [hev, Work.TMC16Core.Core.fracDist_neg] at hsep
      have hpos : (0 : ℝ) < 2 / (5 * (q n : ℝ)) := by positivity
      linarith [hsep, hfd0, hpos]
    · have h3 : 2 * Real.pi * (th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
          + 2 * Real.pi * (th + ((s0q4Idx U m (q n) ki : ℤ) : ℝ) * α) = (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
          + 2 * Real.pi * (th + ((s0q4Idx U m (q n) ki : ℤ) : ℝ) * α)
          = (2 * Real.pi) * (2 * th + (((s0q4Idx U m (q n) ki + s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α) := by
        push_cast; ring
      rw [h4] at h3
      have hz : 2 * th + (((s0q4Idx U m (q n) ki + s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α = (k : ℝ) :=
        mul_left_cancel₀ h2pi_real (by linarith [h3])
      have htp := s0q4_theta_pair (θ := θ) (α := α) (A0 := A0) (H := H) (U := U) (m := m)
        (qn := q n) (k := ki) (l := kj) hA0b hki hkj
      obtain ⟨t, j', ht, hj', heq⟩ := htp
      have hgoal : 2 * th + (((s0q4Idx U m (q n) ki + s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α
          = 2 * θ + (((j' + t * m * (q n : ℤ) : ℤ)) : ℝ) * α := by
        have h1 : 2 * th = 2 * (θ + (A0 : ℝ) * α) := by rw [hth]
        rw [h1, heq]
      have hfd0 : Work.TMC16Core.fracDist (2 * θ + (((j' + t * m * (q n : ℤ) : ℤ)) : ℝ) * α) = 0 := by
        rw [← hgoal, hz, Work.TMC16Core.Core.fracDist_intCast]
      have ht0 : 0 ≤ t := by rcases ht with h | h | h <;> omega
      have ht2 : t ≤ 2 := by rcases ht with h | h | h <;> omega
      have hc := hθC t ht0 ht2 j' hj'
      linarith [hc, hfd0]
  have hN : ∀ k ∈ S0q4Set U H m (q n), ∀ ξ : ℝ,
      (∀ i ∈ (S0q4Set U H m (q n)).erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ (S0q4Set U H m (q n)).erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -(((S0q4Set U H m (q n)).card : ℝ) - 1) * Real.log 2 + Acoef := by
    intro k hk ξ hnz
    rw [S0q4Set] at hk
    obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hk
    rw [show S0q4Set U H m (q n)
        = (Finset.Icc (1 : ℤ) (H : ℤ)).image (fun k : ℤ => s0q4Idx U m (q n) k) from rfl]
    rw [s0q4_erase_image hinj hkj]
    rw [Finset.sum_image (f := fun i : ℤ => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
      (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
    rw [show ((Finset.image (fun k : ℤ => s0q4Idx U m (q n) k) (Finset.Icc (1 : ℤ) (H : ℤ))).card : ℝ) - 1
        = (H : ℝ) - 1 from hcardR, hKB']
    rw [s0q4_sum4 hL1 (fun k' : ℤ => Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))|) kj]
    have hnzB : ∀ p0 : ℤ, (∀ k' ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1), k' ∈ Finset.Icc (1 : ℤ) (H : ℤ)) →
        ∀ k' ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1), k' ≠ kj →
          Real.sin (Real.pi * (ξ + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α)) ≠ 0 := by
      intro p0 hsub k' hk' hne
      refine hnz (s0q4Idx U m (q n) k') ?_
      rw [Finset.mem_erase]
      refine ⟨fun hcontr => hne (s0q4Idx_injOn hHq (hsub k' hk') hkj hcontr), ?_⟩
      rw [S0q4Set]
      exact Finset.mem_image.mpr ⟨k', hsub k' hk', rfl⟩
    have e1 := s0q4_blk_le_erase_any (hb ξ) hL1 (p0 := 1) (kj := kj)
      (hnzB 1 (hsuball 1 (by omega) (by rw [hH4]; omega)))
    have e2 := s0q4_blk_le_erase_any (hb ξ) hL1 (p0 := (q (n - 1) : ℤ) + 1) (kj := kj)
      (hnzB ((q (n - 1) : ℤ) + 1) (hsuball ((q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega)))
    have e3 := s0q4_blk_le_erase_any (hb ξ) hL1 (p0 := 2 * (q (n - 1) : ℤ) + 1) (kj := kj)
      (hnzB (2 * (q (n - 1) : ℤ) + 1) (hsuball (2 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega)))
    have e4 := s0q4_blk_le_erase_any (hb ξ) hL1 (p0 := 3 * (q (n - 1) : ℤ) + 1) (kj := kj)
      (hnzB (3 * (q (n - 1) : ℤ) + 1) (hsuball (3 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega)))
    rw [hAcoef]
    rw [show (1 : ℤ) + (q (n - 1) : ℤ) - 1 = (q (n - 1) : ℤ) from by ring] at e1
    rw [show ((q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 2 * (q (n - 1) : ℤ) from by ring] at e2
    rw [show (2 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 3 * (q (n - 1) : ℤ) from by ring] at e3
    rw [show (3 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 4 * (q (n - 1) : ℤ) from by ring] at e4
    have h4id : -((H : ℝ) - 1) * Real.log 2 + (128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2)
        = 4 * (-((q (n - 1) : ℝ) - 1) * Real.log 2 + 32 * Real.log (q (n - 1) : ℝ)) := by
      rw [hH4R]; ring
    linarith [e1, e2, e3, e4, h4id]
  have hD1 : ∀ k ∈ S0q4Set U H m (q n),
      ∑ i ∈ (S0q4Set U H m (q n)).erase k,
          Real.log |Real.sin (Real.pi * (2 * th + (((i + k : ℤ)) : ℝ) * α))|
        ≥ -(((S0q4Set U H m (q n)).card : ℝ) - 1) * Real.log 2 - Bcoef + 2 * Real.log (2 * cθ) := by
    intro k hk
    rw [S0q4Set] at hk
    obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hk
    rw [show S0q4Set U H m (q n)
        = (Finset.Icc (1 : ℤ) (H : ℤ)).image (fun k : ℤ => s0q4Idx U m (q n) k) from rfl]
    rw [s0q4_erase_image hinj hkj]
    rw [Finset.sum_image (f := fun i : ℤ =>
        Real.log |Real.sin (Real.pi * (2 * th + (((i + s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α))|)
      (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
    have hcongr : ∀ k' : ℤ,
        Real.log |Real.sin (Real.pi * (2 * th + ((((s0q4Idx U m (q n) k' + s0q4Idx U m (q n) kj) : ℤ)) : ℝ) * α))|
        = Real.log |Real.sin (Real.pi * ((2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
            + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))| := by
      intro k'
      congr 1
      push_cast
      ring
    simp only [hcongr]
    rw [show ((Finset.image (fun k : ℤ => s0q4Idx U m (q n) k) (Finset.Icc (1 : ℤ) (H : ℤ))).card : ℝ) - 1
        = (H : ℝ) - 1 from hcardR, hKB']
    rw [s0q4_sum4 hL1 (fun k' : ℤ => Real.log |Real.sin (Real.pi * ((2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
        + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))|) kj]
    have hB0 : ∀ k' ∈ Finset.Icc (1 : ℤ) (H : ℤ),
        Real.log (2 * cθ) ≤ Real.log |Real.sin (Real.pi * ((2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
            + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))| := by
      intro k' hk'
      have htp := s0q4_theta_pair (θ := θ) (α := α) (A0 := A0) (H := H) (U := U) (m := m)
        (qn := q n) (k := k') (l := kj) hA0b hk' hkj
      obtain ⟨t, j', ht, hj', heq⟩ := htp
      have ht0 : 0 ≤ t := by rcases ht with h | h | h <;> omega
      have ht2 : t ≤ 2 := by rcases ht with h | h | h <;> omega
      have hc := hθC t ht0 ht2 j' hj'
      have hsin := Work.TMC16Core.Core.two_mul_fracDist_le_abs_sin' (2 * θ + (((j' + t * m * (q n : ℤ) : ℤ)) : ℝ) * α)
      have harg : Real.pi * ((2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
            + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α)
          = Real.pi * (2 * θ + (((j' + t * m * (q n : ℤ) : ℤ)) : ℝ) * α) := by
        have h5 : (2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α) + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α
            = 2 * θ + (((j' + t * m * (q n : ℤ) : ℤ)) : ℝ) * α := by
          have h1 : 2 * th = 2 * (θ + (A0 : ℝ) * α) := by rw [hth]
          rw [h1]
          rw [show (2 * (θ + (A0 : ℝ) * α) + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
                + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α
              = 2 * (θ + (A0 : ℝ) * α)
                + (((s0q4Idx U m (q n) k' + s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α by
            push_cast; ring]
          rw [heq]
        rw [h5]
      rw [harg]
      refine Real.log_le_log (by linarith) ?_
      linarith [hc, hsin]
    have e1 := s0q4_blk_ge_erase_any (hb (2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)) hL1
      (p0 := 1) (kj := kj) (B0 := Real.log (2 * cθ))
      (fun k' hk' => hB0 k' (hsuball 1 (by omega) (by rw [hH4]; omega) k' hk'))
    have e2 := s0q4_blk_ge_erase_any (hb (2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)) hL1
      (p0 := (q (n - 1) : ℤ) + 1) (kj := kj) (B0 := Real.log (2 * cθ))
      (fun k' hk' => hB0 k' (hsuball ((q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega) k' hk'))
    have e3 := s0q4_blk_ge_erase_any (hb (2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)) hL1
      (p0 := 2 * (q (n - 1) : ℤ) + 1) (kj := kj) (B0 := Real.log (2 * cθ))
      (fun k' hk' => hB0 k' (hsuball (2 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega) k' hk'))
    have e4 := s0q4_blk_ge_erase_any (hb (2 * th + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)) hL1
      (p0 := 3 * (q (n - 1) : ℤ) + 1) (kj := kj) (B0 := Real.log (2 * cθ))
      (fun k' hk' => hB0 k' (hsuball (3 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega) k' hk'))
    have hlogid : Real.log (2 * cθ) + Real.log (1 / (2 * cθ)) = 0 := by
      rw [← Real.log_mul (by linarith) (by positivity)]
      rw [show 2 * cθ * (1 / (2 * cθ)) = 1 by field_simp]
      exact Real.log_one
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [hBcoef]
    rw [show (1 : ℤ) + (q (n - 1) : ℤ) - 1 = (q (n - 1) : ℤ) from by ring] at e1
    rw [show ((q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 2 * (q (n - 1) : ℤ) from by ring] at e2
    rw [show (2 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 3 * (q (n - 1) : ℤ) from by ring] at e3
    rw [show (3 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 4 * (q (n - 1) : ℤ) from by ring] at e4
    have h4id : -((H : ℝ) - 1) * Real.log 2 - (128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2
          + 2 * Real.log (1 / (2 * cθ))) + 2 * Real.log (2 * cθ)
        = 4 * (-((q (n - 1) : ℝ) - 1) * Real.log 2 - 32 * Real.log (q (n - 1) : ℝ) + Real.log (2 * cθ))
          - 6 * Real.log 2 := by
      rw [hH4R]
      have hlogid' : Real.log (1 / (2 * cθ)) = -Real.log (2 * cθ) := by linarith [hlogid]
      rw [hlogid']
      ring
    linarith [e1, e2, e3, e4, h4id, hlogid, hlog2pos]
  have hD2 : ∀ k ∈ S0q4Set U H m (q n),
      ∑ i ∈ (S0q4Set U H m (q n)).erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -(((S0q4Set U H m (q n)).card : ℝ) - 1) * Real.log 2 - Ccoef + Real.log (2 * csep) := by
    intro k hk
    rw [S0q4Set] at hk
    obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hk
    rw [show S0q4Set U H m (q n)
        = (Finset.Icc (1 : ℤ) (H : ℤ)).image (fun k : ℤ => s0q4Idx U m (q n) k) from rfl]
    rw [s0q4_erase_image hinj hkj]
    rw [Finset.sum_image (f := fun i : ℤ =>
        Real.log |Real.sin (Real.pi * (((i - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α)|)
      (fun a ha b hb hab => hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
    have hcongr : ∀ k' : ℤ,
        Real.log |Real.sin (Real.pi * (((s0q4Idx U m (q n) k' - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α)|
        = Real.log |Real.sin (Real.pi * ((-((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)
            + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))| := by
      intro k'
      congr 1
      push_cast
      ring
    simp only [hcongr]
    rw [show ((Finset.image (fun k : ℤ => s0q4Idx U m (q n) k) (Finset.Icc (1 : ℤ) (H : ℤ))).card : ℝ) - 1
        = (H : ℝ) - 1 from hcardR, hKB']
    set ξ : ℝ := -((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α with hξ
    rw [s0q4_sum4 hL1 (fun k' : ℤ => Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))|) kj]
    have hzeros : Real.sin (Real.pi * (ξ + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α)) = 0 := by
      rw [hξ]
      rw [show -((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α + ((s0q4Idx U m (q n) kj : ℤ) : ℝ) * α = 0 by ring]
      simp
    have hblk : ∀ p0 : ℤ, (∀ k' ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1), k' ∈ Finset.Icc (1 : ℤ) (H : ℤ)) →
        -((q (n - 1) : ℝ) - 1) * Real.log 2 - 32 * Real.log (q (n - 1) : ℝ) + Real.log (2 * csep)
          ≤ ∑ k' ∈ (Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1)).erase kj,
              Real.log |Real.sin (Real.pi * (ξ + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α))| := by
      intro p0 hsub
      by_cases hkjblk : kj ∈ Finset.Icc p0 (p0 + (q (n - 1) : ℤ) - 1)
      · have h1 := s0q4_blk_ge_zero (hb ξ) hL1 hkjblk hzeros
        have h2 : Real.log (2 * csep) ≤ 0 := by
          refine Real.log_nonpos (by linarith [hcsep]) ?_
          rw [show 2 * csep = 2 / (5 * (q n : ℝ)) by rw [hcsepdef]; ring]
          rw [div_le_one (by positivity)]
          have hqn1 : (1 : ℝ) ≤ (q n : ℝ) := by
            have h : (1 : ℕ) ≤ q n := hqpos n
            exact_mod_cast h
          linarith
        linarith
      · rw [Finset.erase_eq_of_notMem hkjblk]
        refine s0q4_blk_ge (hb ξ) hL1 ?_
        intro k' hk'
        have hne : k' ≠ kj := fun h => hkjblk (h ▸ hk')
        have hsep := s0q4_sep_global (U := U) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hH hHq hmq (hsub k' hk') hkj hne
        have hsep' : 2 * csep ≤ Work.TMC16Core.fracDist ((((s0q4Idx U m (q n) k' - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α) := by
          rw [show 2 * csep = 2 / (5 * (q n : ℝ)) by rw [hcsepdef]; ring]
          exact hsep
        have hsin := Work.TMC16Core.Core.two_mul_fracDist_le_abs_sin' ((((s0q4Idx U m (q n) k' - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α)
        have harg : ((((s0q4Idx U m (q n) k' - s0q4Idx U m (q n) kj : ℤ)) : ℝ) * α)
            = ξ + ((s0q4Idx U m (q n) k' : ℤ) : ℝ) * α := by rw [hξ]; push_cast; ring
        rw [harg] at hsin hsep'
        refine Real.log_le_log (by linarith [hcsep]) ?_
        linarith [hsep', hsin, hcsep]
    have f1 := hblk 1 (hsuball 1 (by omega) (by rw [hH4]; omega))
    have f2 := hblk ((q (n - 1) : ℤ) + 1) (hsuball ((q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega))
    have f3 := hblk (2 * (q (n - 1) : ℤ) + 1) (hsuball (2 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega))
    have f4 := hblk (3 * (q (n - 1) : ℤ) + 1) (hsuball (3 * (q (n - 1) : ℤ) + 1) (by omega) (by rw [hH4]; omega))
    have hlogid : Real.log (2 * csep) + Real.log (1 / (2 * csep)) = 0 := by
      rw [← Real.log_mul (by linarith [hcsep]) (by positivity)]
      rw [show 2 * csep * (1 / (2 * csep)) = 1 by field_simp]
      exact Real.log_one
    have hcinv : 1 / (2 * csep) = 5 * (q n : ℝ) / 2 := hcsepval
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [hCcoef, ← hcinv]
    rw [show (1 : ℤ) + (q (n - 1) : ℤ) - 1 = (q (n - 1) : ℤ) from by ring] at f1
    rw [show ((q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 2 * (q (n - 1) : ℤ) from by ring] at f2
    rw [show (2 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 3 * (q (n - 1) : ℤ) from by ring] at f3
    rw [show (3 * (q (n - 1) : ℤ) + 1) + (q (n - 1) : ℤ) - 1 = 4 * (q (n - 1) : ℤ) from by ring] at f4
    have h4id : -((H : ℝ) - 1) * Real.log 2 - (128 * Real.log (q (n - 1) : ℝ) + 3 * Real.log 2
          + 3 * Real.log (1 / (2 * csep))) + Real.log (2 * csep)
        = 4 * (-((q (n - 1) : ℝ) - 1) * Real.log 2 - 32 * Real.log (q (n - 1) : ℝ) + Real.log (2 * csep))
          - 6 * Real.log 2 - 3 * (Real.log (2 * csep) + Real.log (1 / (2 * csep))) := by
      rw [hH4R]
      have hlogid' : Real.log (1 / (2 * csep)) = -Real.log (2 * csep) := by linarith [hlogid]
      rw [hlogid']
      ring
    linarith [f1, f2, f3, f4, h4id, hlogid, hlog2pos]
  have hbudget' : 2 * Acoef + Bcoef + Ccoef + 2 * Real.log (1 / (2 * cθ))
      + Real.log (1 / (2 * csep)) < (((S0q4Set U H m (q n)).card : ℝ) - 1) * ε := by
    rw [hAcoef, hBcoef, hCcoef, hcardR, hcsepval]
    have hL1R : (1 : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast hL1
    have h1 := s0q4_budget (L := (q (n - 1) : ℝ)) (X := (q n : ℝ)) hcθ hcθ1 hL1R hH4R hqnp hqH
    linarith [h1, hbudget]
  have huni := uniform_of_sum_bounds_gen (S := S0q4Set U H m (q n)) (α := α) (θ := th) (ε := ε)
    (cθ := cθ) (csep := csep) (A := Acoef) (B := Bcoef) (C := Ccoef)
    hcos hN hD1 hD2 hcθ hcsep hbudget'
  refine (Work.TMC16Core.Core.Uniform_congr (s0q4Equiv a U H m (q n) h2U) ?_).mpr huni
  intro j
  show θ + (A0 : ℝ) * α + (((j : ℤ) + 1 - a : ℤ) : ℝ) * α
    = θ + (((j : ℤ) : ℝ) + ((H : ℝ) - 2) / 2) * α
  rw [hA0]
  push_cast
  rw [hchR]
  ring


end

end Work.TMC16Core.Assembly
