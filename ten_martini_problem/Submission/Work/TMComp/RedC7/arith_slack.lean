import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Fourier.ac_defs
import Submission.Work.TMC7Core.Fourier.blk_first
import Submission.Work.TMComp.RedC7.blk_count

/-!
# `RedC7.arith_slack`: a (correct) arithmetic estimate for the large deviation theorem

The large deviation theorem of Bourgain–Goldstein needs the harmonic-sum estimate

`Σ_{k ≤ K} (1/k) (1 + (s q ‖kα‖)²)⁻¹ ≤ small`,   `α` within `1/q²` of `a/q`,

and the workspace proves it in `Fourier/arith_core.lean` from the per-block estimate
`blk_block_bound` — which is **false** (see `NOTES_blk_counterexample.md`).

Here we prove a weaker but *correct* and *sufficient* estimate, with a larger constant:

`Σ_{k ≤ K} (1/k) (1 + (s q ‖kα‖)²)⁻¹ ≤ 50/s² + 2/q + 12 (1/q) (1 + log (1 + K/q))`.

The proof avoids the per-block estimate entirely:

* the first block `k ≤ q` is `blk_first` (proved, and correct);
* for the remaining blocks we only need the *witness count* `#{r ∈ [1,q] : blkY < τ} ≤ 2τ + 2`
  of `RedC7.blkY_count` (a direct consequence of `win_count`) together with the level
  decomposition `f(y) = Σ_j c_j 1{y < j+1}` of `f(y) = (1+y²)⁻¹`, `c_j = f(j) - f(j+1) ≥ 0`.

The constant `12` is irrelevant for the application: in `large_deviation` one has
`κ ≥ 10⁴/s²`, `q ≥ 864/κ²` and `K ≈ 8 e^{κq/1000}/κ²`, so the right-hand side is `≤ 0.01 κ`,
far below the `κ/16` that the LDT needs.  (The `1+50/s` of the workspace statement is *not*
provable by this route and is not needed.)
-/

namespace Work.TMComp.RedC7

open Finset
open Work.TMC7Core Work.TMC7Core.Fourier

noncomputable section

/-! ## Elementary facts -/

/-- `ff j = (1 + j²)⁻¹`. -/
def ff (j : ℕ) : ℝ := (1 + (j : ℝ) ^ 2)⁻¹

/-- Level weights `lw j = ff j - ff (j+1)`. -/
def lw (j : ℕ) : ℝ := ff j - ff (j + 1)

/-- The summand of the arithmetic estimate. -/
def acTerm (α : ℝ) (q s k : ℕ) : ℝ :=
  (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹

/-- The level-sum that bounds one block: `Σ_j c_j (2(j+1)/s + 2) + q f(J+1)`. -/
def levBound (s : ℝ) (q : ℕ) (J : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (J + 1), lw j * (2 * (((j : ℝ) + 1) / s) + 2)) + (q : ℝ) * ff (J + 1)

lemma acTerm_nonneg (α : ℝ) (q s k : ℕ) : 0 ≤ acTerm α q s k := by
  unfold acTerm; positivity

/-- `blkY` is nonnegative. -/
lemma blkY_nonneg_red (α : ℝ) (q m r : ℕ) : 0 ≤ blkY α q m r := by
  unfold blkY
  exact mul_nonneg (Nat.cast_nonneg q) (fracDist_nonneg _)

lemma ff_pos (j : ℕ) : 0 < ff j := by unfold ff; positivity

lemma ff_nonneg (j : ℕ) : 0 ≤ ff j := le_of_lt (ff_pos j)

lemma ff_anti : Antitone ff := by
  intro a b hab
  unfold ff
  refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
  have h : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  nlinarith

lemma lw_nonneg (j : ℕ) : 0 ≤ lw j := sub_nonneg.mpr (ff_anti (Nat.le_succ j))

lemma sum_lw_Icc (n J : ℕ) (h : n ≤ J) :
    ∑ j ∈ Finset.Icc n J, lw j = ff n - ff (J + 1) := by
  induction J, h using Nat.le_induction with
  | base =>
    have hsing : Finset.Icc n n = {n} := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [hsing, Finset.sum_singleton]
    simp only [lw]
  | succ J _ ih =>
    rw [Finset.sum_Icc_succ_top (by omega : n ≤ J + 1), ih]
    simp only [lw]
    ring

lemma sum_lw_range_le_one (J : ℕ) : ∑ j ∈ Finset.range (J + 1), lw j ≤ 1 := by
  have heq : Finset.range (J + 1) = Finset.Icc 0 J := by
    ext k; simp only [Finset.mem_range, Finset.mem_Icc]; omega
  rw [heq, sum_lw_Icc 0 J (Nat.zero_le J)]
  have h0 : ff 0 = 1 := by unfold ff; norm_num
  rw [h0]
  have := ff_pos (J + 1)
  linarith

lemma sum_lw_mul_range (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1)
      = ff 0 + (∑ j ∈ Finset.Icc 1 J, ff j) - ((J : ℝ) + 1) * ff (J + 1) := by
  induction J with
  | zero => simp [lw, ff]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1)]
    simp only [lw, ff]
    push_cast
    ring

lemma sum_lw_mul_range_le_three (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1) ≤ 3 := by
  rw [sum_lw_mul_range]
  have h0 : ff 0 = 1 := by unfold ff; norm_num
  have hff : ∑ j ∈ Finset.Icc 1 J, ff j ≤ 2 := by
    have hpt : ∀ j ∈ Finset.Icc 1 J, ff j ≤ (1 / (j : ℝ)) ^ 2 := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
      have hjpos : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos hj1
      have h2 : (1 / (j : ℝ)) ^ 2 = ((j : ℝ) ^ 2)⁻¹ := by rw [div_pow, one_pow, one_div]
      rw [h2]
      unfold ff
      have ha : (0 : ℝ) < 1 + (j : ℝ) ^ 2 := by nlinarith [sq_nonneg (j : ℝ)]
      have hb : (0 : ℝ) < (j : ℝ) ^ 2 := pow_pos hjpos 2
      refine (inv_le_inv₀ ha hb).mpr ?_
      nlinarith
    exact le_trans (Finset.sum_le_sum hpt) (sum_inv_sq_Icc_le J)
  have hpos : 0 ≤ ((J : ℝ) + 1) * ff (J + 1) :=
    mul_nonneg (by positivity) (ff_nonneg _)
  linarith

/-- **Level decomposition.**  For `y ≥ 0` and `f(y) = (1+y²)⁻¹`,
`f(s y) ≤ Σ_{j ≤ J} c_j 1{s y < j+1} + f(J+1)` with `c_j = f(j) - f(j+1) ≥ 0`. -/
lemma level_ineq (s y : ℝ) (hs : 0 ≤ s) (hy : 0 ≤ y) (J : ℕ) :
    (1 + (s * y) ^ 2)⁻¹
      ≤ (∑ j ∈ Finset.range (J + 1), lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0))
        + ff (J + 1) := by
  have hsy : 0 ≤ s * y := mul_nonneg hs hy
  set n : ℕ := ⌊s * y⌋₊ with hn
  have hnle : (n : ℝ) ≤ s * y := Nat.floor_le hsy
  have hnlt : s * y < (n : ℝ) + 1 := Nat.lt_floor_add_one (s * y)
  have hterm_nonneg : ∀ j : ℕ, 0 ≤ lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0) := by
    intro j
    by_cases hh : s * y < (j : ℝ) + 1
    · rw [if_pos hh, mul_one]; exact lw_nonneg j
    · rw [if_neg hh]; norm_num
  rcases le_or_gt n J with h | h
  · have hsub : Finset.Icc n J ⊆ Finset.range (J + 1) := by
      intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    have h1 : ∑ j ∈ Finset.Icc n J, lw j
        ≤ ∑ j ∈ Finset.range (J + 1),
            lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0) := by
      calc ∑ j ∈ Finset.Icc n J, lw j
          = ∑ j ∈ Finset.Icc n J,
              lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_Icc] at hj
            have h2 : ((n : ℕ) : ℝ) + 1 ≤ (j : ℝ) + 1 := by
              have : n + 1 ≤ j + 1 := by omega
              exact_mod_cast this
            rw [if_pos (by linarith : s * y < (j : ℝ) + 1), mul_one]
        _ ≤ ∑ j ∈ Finset.range (J + 1),
              lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun j _ _ => hterm_nonneg j)
    have h3 : ∑ j ∈ Finset.Icc n J, lw j = ff n - ff (J + 1) := sum_lw_Icc n J h
    have h4 : (1 + (s * y) ^ 2)⁻¹ ≤ ff n := by
      unfold ff
      refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
      have h5 : ((n : ℝ)) ^ 2 ≤ (s * y) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hnle 2
      linarith
    linarith
  · have hJ1 : (J : ℝ) + 1 ≤ s * y := by
      have h2 : J + 1 ≤ n := by omega
      have h3 : ((J + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
    have hnonneg : 0 ≤ ∑ j ∈ Finset.range (J + 1),
        lw j * (if s * y < (j : ℝ) + 1 then (1 : ℝ) else 0) :=
      Finset.sum_nonneg (fun j _ => hterm_nonneg j)
    have hbound : (1 + (s * y) ^ 2)⁻¹ ≤ ff (J + 1) := by
      unfold ff
      push_cast
      refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
      have h5 : ((J : ℝ) + 1) ^ 2 ≤ (s * y) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hJ1 2
      linarith
    linarith

/-! ## Finite-sum manipulations -/

/-- Splitting an interval of naturals at an interior point. -/
lemma sum_Icc_split3 {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc a c, f k
      = ∑ k ∈ Finset.Icc a b, f k + ∑ k ∈ Finset.Icc (b+1) c, f k := by
  have hunion : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b+1) c := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hunion, Finset.sum_union hdisj]

/-- Reindexing a shifted interval of naturals. -/
private lemma sum_Icc_shift (a n : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 n, f (a+r) = ∑ k ∈ Finset.Icc (a+1) (a+n), f k := by
  refine Finset.sum_bij (fun r _ => a + r) ?_ ?_ ?_ ?_
  · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
  · intro r1 hr1 r2 hr2 h; omega
  · intro b hb; simp only [Finset.mem_Icc] at hb
    exact ⟨b - a, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro r hr; rfl

/-- Chunking a range of naturals into `M` consecutive blocks of length `q`. -/
lemma sum_Icc_block (q : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (q+1) (M*q+q), f k
      = ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 q, f (m*q+r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · subst hM0
      have h2 : (0+1)*q + q = q + q := by ring
      rw [h2, ← sum_Icc_shift q q f]
      simp
    · have h1 : (M+1)*q + q = M*q + q + q := by ring
      have hM1 : 1 ≤ M := hMpos
      have hMq1 : 1 * 1 ≤ M * q := Nat.mul_le_mul hM1 hq
      rw [h1, sum_Icc_split3 (a := q+1) (b := M*q+q) (c := M*q+q+q) (by omega) (by omega) f, ih,
        ← sum_Icc_shift (M*q+q) q f, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      ring

/-- Harmonic bound. -/
lemma ac_harmonic (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ))) ≤ 1 + Real.log (1 + (M : ℝ)) := by
  have h1 : (∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ))) = ((harmonic M : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp
  rw [h1]
  have h2 := harmonic_le_one_add_log M
  have h3 : Real.log (M : ℝ) ≤ Real.log (1 + (M : ℝ)) := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
      exact Real.log_le_log hM0 (by linarith)
  linarith

/-! ## The per-block level bound -/

/-- **One block is bounded by the level sum.** -/
lemma blk_sum_le_levBound (α : ℝ) (a : ℤ) (q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (m J : ℕ) :
    (∑ r ∈ Finset.Icc 1 q, (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹)
      ≤ levBound (s : ℝ) q J := by
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := le_of_lt hspos
  have hstep : ∀ r ∈ Finset.Icc 1 q,
      (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹
        ≤ (∑ j ∈ Finset.range (J + 1),
            lw j * (if (s : ℝ) * blkY α q m r < (j : ℝ) + 1 then (1 : ℝ) else 0))
          + ff (J + 1) :=
    fun r _ => level_ineq (s : ℝ) (blkY α q m r) hs0 (blkY_nonneg_red α q m r) J
  have hcard : ∀ j : ℕ,
      (∑ r ∈ Finset.Icc 1 q,
          (if (s : ℝ) * blkY α q m r < (j : ℝ) + 1 then (1 : ℝ) else 0))
        = (((Finset.Icc 1 q).filter
            (fun r => (s : ℝ) * blkY α q m r < (j : ℝ) + 1)).card : ℝ) := by
    intro j
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcnt : ∀ j ∈ Finset.range (J + 1),
      (((Finset.Icc 1 q).filter
          (fun r => (s : ℝ) * blkY α q m r < (j : ℝ) + 1)).card : ℝ)
        ≤ 2 * (((j : ℝ) + 1) / (s : ℝ)) + 2 := by
    intro j _
    have heq : (Finset.Icc 1 q).filter (fun r => (s : ℝ) * blkY α q m r < (j : ℝ) + 1)
        = (Finset.Icc 1 q).filter (fun r => blkY α q m r < ((j : ℝ) + 1) / (s : ℝ)) := by
      apply Finset.filter_congr
      intro r _
      rw [lt_div_iff₀ hspos, mul_comm]
    rw [heq]
    exact blkY_count α a q hq hcop hα m (((j : ℝ) + 1) / (s : ℝ)) (by positivity)
  have hqcard : ((Finset.Icc 1 q).card : ℝ) = (q : ℝ) := by
    simp
  calc (∑ r ∈ Finset.Icc 1 q, (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹)
      ≤ ∑ r ∈ Finset.Icc 1 q,
          ((∑ j ∈ Finset.range (J + 1),
              lw j * (if (s : ℝ) * blkY α q m r < (j : ℝ) + 1 then (1 : ℝ) else 0))
            + ff (J + 1)) := Finset.sum_le_sum hstep
    _ = (∑ j ∈ Finset.range (J + 1), lw j *
            (((Finset.Icc 1 q).filter
              (fun r => (s : ℝ) * blkY α q m r < (j : ℝ) + 1)).card : ℝ))
          + (q : ℝ) * ff (J + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          rw [← hcard j, Finset.mul_sum]
        · rw [Finset.sum_const, nsmul_eq_mul, hqcard]
    _ ≤ (∑ j ∈ Finset.range (J + 1), lw j * (2 * (((j : ℝ) + 1) / (s : ℝ)) + 2))
          + (q : ℝ) * ff (J + 1) := by
        have hsl : (∑ j ∈ Finset.range (J + 1), lw j *
              (((Finset.Icc 1 q).filter
                (fun r => (s : ℝ) * blkY α q m r < (j : ℝ) + 1)).card : ℝ))
            ≤ ∑ j ∈ Finset.range (J + 1), lw j * (2 * (((j : ℝ) + 1) / (s : ℝ)) + 2) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hcnt j hj) (lw_nonneg j)
        linarith
    _ = levBound (s : ℝ) q J := rfl

/-- **`levBound` is small.** -/
lemma levBound_le (s : ℝ) (hs : 1 ≤ s) (q J : ℕ) (hq : 1 ≤ q)
    (hJ : (s * (q : ℝ)) / 2 ≤ (J : ℝ)) : levBound s q J ≤ 12 := by
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 : (∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1)) ≤ 3 :=
    sum_lw_mul_range_le_three J
  have h2 : (∑ j ∈ Finset.range (J + 1), lw j) ≤ 1 := sum_lw_range_le_one J
  have h3 : (∑ j ∈ Finset.range (J + 1), lw j * (2 * (((j : ℝ) + 1) / s) + 2)) ≤ 6 / s + 2 := by
    have hsplit : (∑ j ∈ Finset.range (J + 1), lw j * (2 * (((j : ℝ) + 1) / s) + 2))
        = (2 / s) * (∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1))
          + 2 * (∑ j ∈ Finset.range (J + 1), lw j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit]
    have ha : (2 / s) * (∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1)) ≤ 6 / s := by
      calc (2 / s) * (∑ j ∈ Finset.range (J + 1), lw j * ((j : ℝ) + 1))
          ≤ (2 / s) * 3 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 6 / s := by ring
    have hb : 2 * (∑ j ∈ Finset.range (J + 1), lw j) ≤ 2 := by
      simpa using mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have h4 : (q : ℝ) * ff (J + 1) ≤ 4 := by
    have hJ1 : s * (q : ℝ) / 2 ≤ (J : ℝ) + 1 := by linarith
    have hpos : 0 < s * (q : ℝ) / 2 := by positivity
    have hff : ff (J + 1) ≤ (s * (q : ℝ) / 2)⁻¹ ^ 2 := by
      unfold ff
      push_cast
      rw [inv_pow]
      refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
      have h6 : ((s * (q : ℝ) / 2)) ^ 2 ≤ ((J : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hpos) hJ1 2
      linarith
    have hsq : (s * (q : ℝ) / 2)⁻¹ ^ 2 * (q : ℝ) ≤ 4 := by
      rw [inv_pow]
      have hpow : (s * (q : ℝ) / 2) ^ 2 = s ^ 2 * (q : ℝ) ^ 2 / 4 := by ring
      rw [hpow]
      have hqq : (0 : ℝ) < s ^ 2 * (q : ℝ) ^ 2 / 4 := by positivity
      have h7 : (s ^ 2 * (q : ℝ) ^ 2 / 4)⁻¹ * (q : ℝ) = 4 / (s ^ 2 * (q : ℝ)) := by
        field_simp
      have hsq1 : (1 : ℝ) ≤ s ^ 2 * (q : ℝ) := by
        have hs2 : (1 : ℝ) ≤ s ^ 2 := by nlinarith
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ s ^ 2 * (q : ℝ) := mul_le_mul hs2 hq1 (by norm_num) (by positivity)
      rw [h7, div_le_iff₀ (by positivity)]
      linarith
    calc (q : ℝ) * ff (J + 1) ≤ (q : ℝ) * (s * (q : ℝ) / 2)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hff (le_of_lt hqpos)
      _ = (s * (q : ℝ) / 2)⁻¹ ^ 2 * (q : ℝ) := by ring
      _ ≤ 4 := hsq
  have h5 : 6 / s + 2 ≤ 8 := by
    have h6 : 6 / s ≤ 6 := by
      rw [div_le_iff₀ hspos]
      nlinarith
    linarith
  unfold levBound
  linarith

/-! ## The main arithmetic estimate -/

/-- **Arithmetic estimate (slack form).**  For `α` within `1/q²` of the reduced fraction
`a/q`, `q ≥ 1`, `s ≥ 1` and any `K`,
`Σ_{k ≤ K} (1/k)(1 + (s q ‖kα‖)²)⁻¹ ≤ 50/s² + 2/q + 12 (1/q)(1 + log (1 + K/q))`. -/
theorem arith_slack (α : ℝ) (a : ℤ) (q s K : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hcop : Nat.Coprime (Int.natAbs a) q)
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) :
    (∑ k ∈ Finset.Icc 1 K, acTerm α q s k)
      ≤ 50 / (s : ℝ) ^ 2 + 2 / (q : ℝ)
        + 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ 1 ≤ 0), Finset.sum_empty]
    have hlog0 : 0 ≤ Real.log (1 + ((0 : ℕ) : ℝ) / (q : ℝ)) := by
      rw [Nat.cast_zero, zero_div, add_zero, Real.log_one]
    have h1 : (0 : ℝ) < 50 / (s : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 2 / (q : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + ((0 : ℕ) : ℝ) / (q : ℝ))) := by
      have hqinv : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
      have hsum : (0 : ℝ) ≤ 1 + Real.log (1 + ((0 : ℕ) : ℝ) / (q : ℝ)) := by linarith
      exact mul_nonneg (mul_nonneg (by norm_num) hqinv) hsum
    linarith
  set J : ℕ := ⌈(s : ℝ) * (q : ℝ) / 2⌉₊ with hJ
  have hJle : (s : ℝ) * (q : ℝ) / 2 ≤ (J : ℝ) := Nat.le_ceil _
  -- the split
  have hsplit := sum_Icc_split3 (a := 1) (b := min K q) (c := K) (by omega) (min_le_left K q)
    (fun k => acTerm α q s k)
  -- first block
  have hfirst : (∑ k ∈ Finset.Icc 1 (min K q), acTerm α q s k)
      ≤ 50 / (s : ℝ) ^ 2 + 2 / (q : ℝ) := by
    simpa only [acTerm] using blk_first α a q s K hq hs hcop hα
  -- the tail
  have hsecond : (∑ k ∈ Finset.Icc (min K q + 1) K, acTerm α q s k)
      ≤ 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by
    rcases le_or_gt K q with hKq | hKq
    · have hemp : Finset.Icc (min K q + 1) K = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        have h1 : min K q = K := min_eq_left hKq
        omega
      rw [hemp, Finset.sum_empty]
      have : (0 : ℝ) ≤ 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by
        have hlog : 0 ≤ Real.log (1 + (K : ℝ) / (q : ℝ)) :=
          Real.log_nonneg (by linarith [div_nonneg (Nat.cast_nonneg K) (le_of_lt hqpos)])
        positivity
      linarith
    · have hmin : min K q = q := min_eq_right (le_of_lt hKq)
      rw [hmin]
      set M : ℕ := K / q with hM
      have hKle : K ≤ M * q + q := by
        have h := Nat.div_add_mod K q
        have hlt : K % q < q := Nat.mod_lt K (by omega)
        calc K = q * (K / q) + K % q := h.symm
          _ = K / q * q + K % q := by rw [Nat.mul_comm]
          _ ≤ K / q * q + q := Nat.add_le_add_left (le_of_lt hlt) _
      have hstep : (∑ k ∈ Finset.Icc (q+1) K, acTerm α q s k)
          ≤ ∑ k ∈ Finset.Icc (q+1) (M*q+q), acTerm α q s k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
        · intro k _ _; exact acTerm_nonneg α q s k
      rw [sum_Icc_block q hq (fun k => acTerm α q s k) M] at hstep
      -- per-block bound
      have hblk : ∀ m ∈ Finset.Icc 1 M, (∑ r ∈ Finset.Icc 1 q, acTerm α q s (m*q+r))
          ≤ (1 / ((m : ℝ) * (q : ℝ))) * levBound (s : ℝ) q J := by
        intro m hm
        simp only [Finset.mem_Icc] at hm
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
        have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le one_pos hm1
        have hmq : (0 : ℝ) < (m : ℝ) * (q : ℝ) := mul_pos hmpos hqpos
        have hterm : ∀ r ∈ Finset.Icc 1 q,
            acTerm α q s (m*q+r)
              ≤ (1 / ((m : ℝ) * (q : ℝ))) * (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹ := by
          intro r hr
          simp only [Finset.mem_Icc] at hr
          have hmqr : (m : ℝ) * (q : ℝ) ≤ ((m*q+r : ℕ) : ℝ) := by
            have : m*q ≤ m*q+r := by omega
            push_cast
            exact_mod_cast this
          have hle : (1 : ℝ) / (((m*q+r : ℕ)) : ℝ) ≤ 1 / ((m : ℝ) * (q : ℝ)) := by
            rw [one_div, one_div]
            exact (inv_le_inv₀ (lt_of_lt_of_le hmq hmqr) hmq).mpr hmqr
          have hY : ((s : ℝ) * blkY α q m r) ^ 2
              = ((s : ℝ) * (q : ℝ) * fracDist ((((m * q + r : ℕ)) : ℝ) * α)) ^ 2 := by
            rw [blkY]; ring
          rw [acTerm, hY]
          exact mul_le_mul_of_nonneg_right hle (by positivity)
        calc (∑ r ∈ Finset.Icc 1 q, acTerm α q s (m*q+r))
            ≤ ∑ r ∈ Finset.Icc 1 q,
                (1 / ((m : ℝ) * (q : ℝ))) * (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹ :=
              Finset.sum_le_sum hterm
          _ = (1 / ((m : ℝ) * (q : ℝ))) *
                ∑ r ∈ Finset.Icc 1 q, (1 + ((s : ℝ) * blkY α q m r) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ (1 / ((m : ℝ) * (q : ℝ))) * levBound (s : ℝ) q J :=
              mul_le_mul_of_nonneg_left (blk_sum_le_levBound α a q s hq hs hcop hα m J)
                (by positivity)
      -- sum over the blocks
      have hharm := ac_harmonic M
      have htail : (∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 q, acTerm α q s (m*q+r))
          ≤ (1 / (q : ℝ)) * levBound (s : ℝ) q J * (1 + Real.log (1 + (M : ℝ))) := by
        calc (∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 q, acTerm α q s (m*q+r))
            ≤ ∑ m ∈ Finset.Icc 1 M, (1 / ((m : ℝ) * (q : ℝ))) * levBound (s : ℝ) q J :=
              Finset.sum_le_sum hblk
          _ = (∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ))) * ((1 / (q : ℝ)) * levBound (s : ℝ) q J) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro m _
              field_simp
          _ ≤ (1 + Real.log (1 + (M : ℝ))) * ((1 / (q : ℝ)) * levBound (s : ℝ) q J) := by
              apply mul_le_mul_of_nonneg_right hharm
              have h1 := levBound_le (s : ℝ) hs1 q J hq hJle
              have h2 : (0 : ℝ) ≤ levBound (s : ℝ) q J := by
                unfold levBound
                have h3 : 0 ≤ ∑ j ∈ Finset.range (J + 1),
                    lw j * (2 * (((j : ℝ) + 1) / (s : ℝ)) + 2) := by
                  apply Finset.sum_nonneg
                  intro j _
                  apply mul_nonneg (lw_nonneg j)
                  have : 0 ≤ ((j : ℝ) + 1) / (s : ℝ) := by positivity
                  linarith
                have h4 : 0 ≤ (q : ℝ) * ff (J + 1) := mul_nonneg (by positivity) (ff_nonneg _)
                linarith
              positivity
          _ = (1 / (q : ℝ)) * levBound (s : ℝ) q J * (1 + Real.log (1 + (M : ℝ))) := by ring
      have hMcast : (M : ℝ) ≤ (K : ℝ) / (q : ℝ) := by
        rw [hM]; exact Nat.cast_div_le
      have hlogM : Real.log (1 + (M : ℝ)) ≤ Real.log (1 + (K : ℝ) / (q : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      have hlev := levBound_le (s : ℝ) hs1 q J hq hJle
      have hlevnonneg : 0 ≤ levBound (s : ℝ) q J := by
        unfold levBound
        have h3 : 0 ≤ ∑ j ∈ Finset.range (J + 1),
            lw j * (2 * (((j : ℝ) + 1) / (s : ℝ)) + 2) := by
          apply Finset.sum_nonneg
          intro j _
          apply mul_nonneg (lw_nonneg j)
          have : 0 ≤ ((j : ℝ) + 1) / (s : ℝ) := by positivity
          linarith
        have h4 : 0 ≤ (q : ℝ) * ff (J + 1) := mul_nonneg (by positivity) (ff_nonneg _)
        linarith
      have hfinal : (1 / (q : ℝ)) * levBound (s : ℝ) q J * (1 + Real.log (1 + (M : ℝ)))
          ≤ 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by
        have hL : 1 + Real.log (1 + (M : ℝ)) ≤ 1 + Real.log (1 + (K : ℝ) / (q : ℝ)) := by
          linarith
        have hLnn : 0 ≤ 1 + Real.log (1 + (M : ℝ)) := by
          have : 0 ≤ Real.log (1 + (M : ℝ)) :=
            Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg M))
          linarith
        calc (1 / (q : ℝ)) * levBound (s : ℝ) q J * (1 + Real.log (1 + (M : ℝ)))
            ≤ (1 / (q : ℝ)) * 12 * (1 + Real.log (1 + (M : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hLnn
              exact mul_le_mul_of_nonneg_left hlev (by positivity)
          _ ≤ (1 / (q : ℝ)) * 12 * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by
              apply mul_le_mul_of_nonneg_left hL
              positivity
          _ = 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by ring
      linarith [hstep, htail, hfinal]
  calc (∑ k ∈ Finset.Icc 1 K, acTerm α q s k)
      = (∑ k ∈ Finset.Icc 1 (min K q), acTerm α q s k)
        + (∑ k ∈ Finset.Icc (min K q + 1) K, acTerm α q s k) := hsplit
    _ ≤ (50 / (s : ℝ) ^ 2 + 2 / (q : ℝ))
        + 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := add_le_add hfirst hsecond
    _ = 50 / (s : ℝ) ^ 2 + 2 / (q : ℝ)
        + 12 * (1 / (q : ℝ)) * (1 + Real.log (1 + (K : ℝ) / (q : ℝ))) := by ring

end

end Work.TMComp.RedC7
