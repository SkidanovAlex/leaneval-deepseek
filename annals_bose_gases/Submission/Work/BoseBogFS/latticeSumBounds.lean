import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBogFS.CleanRiem
import Submission.Work.BoseBogFS.latSumOneDCount
import Submission.Work.BoseBogFS.latSumOneDThreeFour
import Submission.Work.BoseBogFS.latSumOneDTwoCube
import Submission.Work.BoseBogFS.latSumOneDTwoSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lattice-sum bounds on the dual lattice `ℤ³ ⊂ ℝ³`

This file proves `Work.BoseBogFS.latticeSumBounds`, the family of lattice-sum bounds needed for
the bootstrap of the free energy of the dilute Bose gas.  The sums run over the integer
lattice `n : Fin 3 → ℤ` embedded in `ℝ³` as `lpt 1 n = n`.

## Method

A decreasing nonnegative profile `g` can be summed on the lattice by grouping the lattice points
into the *shells* of the maximal norm: writing `mn n = max_i |n_i|`, the shell `{n | mn n = j}`
has exactly `(2j+1)³ - (2j-1)³ = 24 j² + 2` elements, and every `n` in it satisfies `‖n‖ ≥ j`.
Hence

`Σ_{n} g (‖lpt 1 n‖) ≤ Σ_j (24 j² + 2) g j`,

and the right hand side is an explicit one-dimensional series which is bounded in the auxiliary
modules `latSumOneD*` (`(2,3)`, `(2,2)`, `(3,4)` profiles) and `latSumOneDCount` (the elementary
bounds used for the counting estimates).

The reduction is implemented by `tsum_le_of_cube` (untruncated sums) and `tsum_trunc_le`
(sums cut off at `‖n‖ ≤ N`), both resting on `Real.tsum_le_of_sum_le`, which bounds a `tsum` by a
constant as soon as every finite partial sum is bounded by it.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

set_option maxHeartbeats 1000000

/-! ## 1. The maximal norm and the lattice cubes -/

/-- The maximal norm `max_i |n_i|` of an integer vector, as a natural number. -/
def mn (n : Fin 3 → ℤ) : ℕ := Finset.univ.sup fun i => (n i).natAbs

/-- The cube of lattice points of maximal norm at most `J`. -/
def cube (J : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(J : ℤ)) (J : ℤ)

/-- The shell profile `24 j² + 2`: the number of lattice points of maximal norm exactly `j`. -/
def prof (j : ℕ) : ℝ := 24 * (j : ℝ) ^ 2 + 2

lemma mem_cube {n : Fin 3 → ℤ} {J : ℕ} : n ∈ cube J ↔ mn n ≤ J := by
  rw [cube, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, mn, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i
    have h' := h i
    have h2 : ((n i).natAbs : ℤ) ≤ (J : ℤ) := by
      rw [Nat.cast_natAbs]; exact abs_le.mpr h'
    exact_mod_cast h2
  · intro h i
    have h2 : ((n i).natAbs : ℤ) ≤ (J : ℤ) := by exact_mod_cast h i
    rw [Nat.cast_natAbs] at h2
    exact abs_le.mp h2

lemma mn_coord_le (n : Fin 3 → ℤ) (i : Fin 3) : (n i).natAbs ≤ mn n :=
  Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)

lemma card_cube (J : ℕ) : (cube J).card = (2 * J + 1) ^ 3 := by
  rw [cube, Fintype.card_piFinset]
  have h : ∀ i : Fin 3, (Finset.Icc (-(J : ℤ)) (J : ℤ)).card = 2 * J + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Each coordinate of a lattice point is bounded by the Euclidean norm. -/
lemma abs_coord_le_norm (n : Fin 3 → ℤ) (i : Fin 3) : |((n i : ℤ) : ℝ)| ≤ ‖lpt 1 n‖ := by
  have h := PiLp.norm_apply_le (lpt 1 n) i
  rwa [lpt_ofLp, one_mul, Real.norm_eq_abs] at h

/-- The maximal norm is dominated by the Euclidean norm. -/
lemma mn_cast_le_norm (n : Fin 3 → ℤ) : (mn n : ℝ) ≤ ‖lpt 1 n‖ := by
  have h : mn n ≤ ⌊‖lpt 1 n‖⌋₊ := by
    refine Finset.sup_le fun i _ => ?_
    apply Nat.le_floor
    rw [Nat.cast_natAbs (n i), Int.cast_abs]
    exact abs_coord_le_norm n i
  calc (mn n : ℝ) ≤ (⌊‖lpt 1 n‖⌋₊ : ℝ) := by exact_mod_cast h
    _ ≤ ‖lpt 1 n‖ := Nat.floor_le (norm_nonneg _)

/-- A lattice point of Euclidean norm `≤ N` has maximal norm `≤ ⌈N⌉`. -/
lemma mn_le_ceil_of_norm_le {n : Fin 3 → ℤ} {N : ℝ} (h : ‖lpt 1 n‖ ≤ N) : mn n ≤ ⌈N⌉₊ := by
  have hfloor : mn n ≤ ⌊N⌋₊ := by
    refine Finset.sup_le fun i _ => ?_
    apply Nat.le_floor
    rw [Nat.cast_natAbs (n i), Int.cast_abs]
    exact le_trans (abs_coord_le_norm n i) h
  exact le_trans hfloor (Nat.floor_le_ceil N)

lemma cube_mono : Monotone cube := by
  intro J K hJK n hn
  rw [mem_cube] at hn ⊢
  exact le_trans hn hJK

/-- The shell `cube (J+1) \ cube J` has at most `24 (J+1)² + 2` points (in fact exactly). -/
lemma card_shell_le (J : ℕ) : (cube (J + 1) \ cube J).card ≤ 24 * (J + 1) ^ 2 + 2 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (cube_mono (Nat.le_succ J)), card_cube,
    card_cube]
  have h2 : 24 * (J + 1) ^ 2 + 2 = 24 * J ^ 2 + 48 * J + 26 := by ring
  rw [h2]
  have h : (2 * (J + 1) + 1) ^ 3 = (2 * J + 1) ^ 3 + (24 * J ^ 2 + 48 * J + 26) := by ring
  omega

/-! ## 2. The shell decomposition of the sums over the cubes -/

/-- The lattice origin has norm zero. -/
lemma norm_lpt_zero : ‖lpt 1 (0 : Fin 3 → ℤ)‖ = 0 := by
  have hz : lpt 1 (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [lpt_ofLp]
  rw [hz, norm_zero]

/-- **Shell decomposition.**  For a nonnegative profile `g` decreasing on `(0,∞)`, the sum over
the cube `{mn ≤ J}` is bounded by the one-dimensional shell series. -/
lemma sum_cube_le {g : ℝ → ℝ} (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a) (J : ℕ) :
    ∑ n ∈ cube J, g (‖lpt 1 n‖) ≤ ∑ j ∈ Finset.range (J + 1), prof j * g (j : ℝ) := by
  induction J with
  | zero =>
    have hsub : cube 0 ⊆ ({0} : Finset (Fin 3 → ℤ)) := by
      intro n hn
      rw [mem_cube] at hn
      rw [Finset.mem_singleton]
      funext i
      have h1 : (n i).natAbs ≤ mn n := mn_coord_le n i
      exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero (le_trans h1 hn))
    have h0 : (0 : ℝ) ≤ g 0 := hg0 0 le_rfl
    calc ∑ n ∈ cube 0, g (‖lpt 1 n‖)
        ≤ ∑ n ∈ ({0} : Finset (Fin 3 → ℤ)), g (‖lpt 1 n‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hg0 _ (norm_nonneg _)
      _ = g 0 := by rw [Finset.sum_singleton, norm_lpt_zero]
      _ ≤ 2 * g 0 := by linarith
      _ = ∑ j ∈ Finset.range (0 + 1), prof j * g (j : ℝ) := by
            rw [Finset.range_one, Finset.sum_singleton]
            simp [prof]
  | succ J ih =>
    have hsub : cube J ⊆ cube (J + 1) := cube_mono (Nat.le_succ J)
    have hsplit := Finset.sum_sdiff hsub (f := fun n => g (‖lpt 1 n‖))
    rw [← hsplit, Finset.sum_range_succ]
    have hshell : ∑ n ∈ cube (J + 1) \ cube J, g (‖lpt 1 n‖)
        ≤ prof (J + 1) * g ((J + 1 : ℕ) : ℝ) := by
      have hb : ∀ n ∈ cube (J + 1) \ cube J, g (‖lpt 1 n‖) ≤ g ((J + 1 : ℕ) : ℝ) := by
        intro n hn
        have hnotmem : n ∉ cube J := (Finset.mem_sdiff.mp hn).2
        rw [mem_cube] at hnotmem
        have hle : J + 1 ≤ mn n := Nat.succ_le_of_lt (Nat.lt_of_not_le hnotmem)
        exact hdec (Nat.cast_pos.mpr (Nat.succ_pos J))
          (le_trans (by exact_mod_cast hle) (mn_cast_le_norm n))
      calc ∑ n ∈ cube (J + 1) \ cube J, g (‖lpt 1 n‖)
          ≤ ∑ _n ∈ cube (J + 1) \ cube J, g ((J + 1 : ℕ) : ℝ) := Finset.sum_le_sum hb
        _ = ((cube (J + 1) \ cube J).card : ℝ) * g ((J + 1 : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ prof (J + 1) * g ((J + 1 : ℕ) : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ (hg0 _ (Nat.cast_nonneg _))
              have hc := card_shell_le J
              have hcast : ((24 * (J + 1) ^ 2 + 2 : ℕ) : ℝ)
                  = 24 * ((J + 1 : ℕ) : ℝ) ^ 2 + 2 := by push_cast; ring
              calc ((cube (J + 1) \ cube J).card : ℝ)
                  ≤ ((24 * (J + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast hc
                _ = prof (J + 1) := by rw [hcast]; simp [prof]
    linarith

/-- A finite set of lattice points is dominated by the cube of maximal norm `s.sup mn`. -/
lemma sum_le_cube_sum {g : ℝ → ℝ} (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (s : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ s, g (‖lpt 1 n‖) ≤ ∑ n ∈ cube (s.sup mn), g (‖lpt 1 n‖) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hg0 _ (norm_nonneg _)
  intro n hn
  rw [mem_cube]
  exact Finset.le_sup (f := mn) hn

/-! ## 3. Reduction of the lattice sums to one-dimensional series -/

/-- **Main reduction (untruncated).**  If `f ≤ g (‖·‖)` pointwise with `g` nonnegative and
decreasing on `[0,∞)`, and if every one-dimensional shell partial sum of `g` is bounded by `L`,
then the lattice sum of `f` is bounded by `L`. -/
lemma tsum_le_of_cube {f : (Fin 3 → ℤ) → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    {g : ℝ → ℝ} (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a)
    (hfg : ∀ n, f n ≤ g (‖lpt 1 n‖))
    {L : ℝ} (hL : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), prof j * g (j : ℝ) ≤ L) :
    ∑' n : Fin 3 → ℤ, f n ≤ L := by
  refine Real.tsum_le_of_sum_le hf0 fun s => ?_
  calc ∑ n ∈ s, f n ≤ ∑ n ∈ s, g (‖lpt 1 n‖) := Finset.sum_le_sum fun n _ => hfg n
    _ ≤ ∑ n ∈ cube (s.sup mn), g (‖lpt 1 n‖) := sum_le_cube_sum hg0 s
    _ ≤ ∑ j ∈ Finset.range (s.sup mn + 1), prof j * g (j : ℝ) := sum_cube_le hg0 hdec _
    _ ≤ L := hL _

/-- **Main reduction (truncated).**  The same, for the sums cut off at `‖n‖ ≤ N`. -/
lemma tsum_trunc_le {g : ℝ → ℝ} (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a) {N : ℝ} (_hN : 0 ≤ N) {L : ℝ}
    (hL : ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * g (j : ℝ) ≤ L) :
    ∑' n : Fin 3 → ℤ, (if ‖lpt 1 n‖ ≤ N then g (‖lpt 1 n‖) else 0) ≤ L := by
  refine Real.tsum_le_of_sum_le (fun n => ?_) fun s => ?_
  · by_cases h : ‖lpt 1 n‖ ≤ N
    · simp only [h, reduceIte]
      exact hg0 _ (norm_nonneg _)
    · simp [h]
  · rw [← Finset.sum_filter]
    have hsub : s.filter (fun n => ‖lpt 1 n‖ ≤ N) ⊆ cube ⌈N⌉₊ := by
      intro n hn
      rw [mem_cube]
      exact mn_le_ceil_of_norm_le (Finset.mem_filter.mp hn).2
    calc ∑ n ∈ s.filter (fun n => ‖lpt 1 n‖ ≤ N), g (‖lpt 1 n‖)
        ≤ ∑ n ∈ cube ⌈N⌉₊, g (‖lpt 1 n‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hg0 _ (norm_nonneg _)
      _ ≤ ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * g (j : ℝ) := sum_cube_le hg0 hdec _
      _ ≤ L := hL

/-! ## 4. The profiles are decreasing on `(0,∞)` -/

/-- `r ↦ 1 / ((1 + m r)^k * r^l)` is decreasing on `(0,∞)` for `m > 0`, `k, l > 0`. -/
lemma antitone_inv_mul (m : ℝ) (hm : 0 < m) (k l : ℕ) (_hk : 0 < k) (_hl : 0 < l) :
    ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b →
      1 / ((1 + m * b) ^ k * b ^ l) ≤ 1 / ((1 + m * a) ^ k * a ^ l) := by
  intro a b ha hab
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have h1 : (1 + m * a) ^ k ≤ (1 + m * b) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have hmul := mul_le_mul_of_nonneg_left hab hm.le
    linarith
  have h2 : a ^ l ≤ b ^ l := pow_le_pow_left₀ ha.le hab l
  exact mul_le_mul h1 h2 (pow_nonneg ha.le l) (pow_nonneg (by positivity) k)

/-- `r ↦ 1 / r^l` is decreasing on `(0,∞)` for `l > 0`. -/
lemma antitone_inv_pow (l : ℕ) (_hl : 0 < l) :
    ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → 1 / b ^ l ≤ 1 / a ^ l := by
  intro a b ha hab
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le hab l)

/-! ## 5. The four groups of bounds -/

/-- `Σ_n 1 / ((1 + m‖n‖)² ‖n‖³)` is bounded by `100 (1 + log (2 + 1/m))`. -/
lemma tsum_two_cube (m : ℝ) (hm : 0 < m) :
    ∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 3)
      ≤ 100 * (1 + Real.log (2 + 1 / m)) := by
  refine tsum_le_of_cube (f := fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 3))
    (g := fun r : ℝ => 1 / ((1 + m * r) ^ 2 * r ^ 3))
    (fun n => by positivity) (fun r hr => by positivity)
    (antitone_inv_mul m hm 2 3 (by norm_num) (by norm_num)) (fun n => le_refl _) ?_
  intro J
  have h := latSumOneDTwoCube m hm J
  have hsimp : ∑ j ∈ Finset.range (J + 1),
        prof j * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 3))
      = ∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 3)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [prof]
  rw [hsimp]
  exact h

/-- `Σ_n 1 / ((1 + m‖n‖)² ‖n‖²)` is bounded by `100 (1/m + 1)`. -/
lemma tsum_two_sq (m : ℝ) (hm : 0 < m) :
    ∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 2)
      ≤ 100 * (1 / m + 1) := by
  refine tsum_le_of_cube (f := fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 2))
    (g := fun r : ℝ => 1 / ((1 + m * r) ^ 2 * r ^ 2))
    (fun n => by positivity) (fun r hr => by positivity)
    (antitone_inv_mul m hm 2 2 (by norm_num) (by norm_num)) (fun n => le_refl _) ?_
  intro J
  have h := latSumOneDTwoSq m hm J
  have hsimp : ∑ j ∈ Finset.range (J + 1),
        prof j * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 2))
      = ∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 2 * (j : ℝ) ^ 2)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [prof]
  rw [hsimp]
  exact h

/-- `Σ_n 1 / ((1 + m‖n‖)³ ‖n‖⁴) ≤ 100`. -/
lemma tsum_three_four (m : ℝ) (hm : 0 < m) :
    ∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 3 * ‖lpt 1 n‖ ^ 4) ≤ 100 := by
  refine tsum_le_of_cube (f := fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 3 * ‖lpt 1 n‖ ^ 4))
    (g := fun r : ℝ => 1 / ((1 + m * r) ^ 3 * r ^ 4))
    (fun n => by positivity) (fun r hr => by positivity)
    (antitone_inv_mul m hm 3 4 (by norm_num) (by norm_num)) (fun n => le_refl _) ?_
  intro J
  have h := latSumOneDThreeFour m hm J
  have hsimp : ∑ j ∈ Finset.range (J + 1),
        prof j * (1 / ((1 + m * (j : ℝ)) ^ 3 * (j : ℝ) ^ 4))
      = ∑ j ∈ Finset.range (J + 1),
        (24 * (j : ℝ) ^ 2 + 2) * (1 / ((1 + m * (j : ℝ)) ^ 3 * (j : ℝ) ^ 4)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [prof]
  rw [hsimp]
  exact h

/-- The pure counting bound: `Σ_n 1_{‖n‖ ≤ N} ≤ L` whenever the cardinality of the cube of
maximal norm `⌈N⌉` is at most `L`. -/
lemma tsum_indicator_le {N : ℝ} {L : ℝ} (hL : ((cube ⌈N⌉₊).card : ℝ) ≤ L) :
    ∑' n : Fin 3 → ℤ, (if ‖lpt 1 n‖ ≤ N then (1 : ℝ) else 0) ≤ L := by
  refine Real.tsum_le_of_sum_le (fun n => ?_) fun s => ?_
  · by_cases h : ‖lpt 1 n‖ ≤ N <;> simp [h]
  · rw [← Finset.sum_filter]
    have hsub : s.filter (fun n => ‖lpt 1 n‖ ≤ N) ⊆ cube ⌈N⌉₊ := by
      intro n hn
      rw [mem_cube]
      exact mn_le_ceil_of_norm_le (Finset.mem_filter.mp hn).2
    have h1 : ∑ n ∈ s.filter (fun n => ‖lpt 1 n‖ ≤ N), (1 : ℝ)
        = ((s.filter (fun n => ‖lpt 1 n‖ ≤ N)).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1]
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hL

/-- The three counting bounds with a common constant `300`. -/
lemma count_bounds (N : ℝ) (hN : 0 ≤ N) :
    (∑' n : Fin 3 → ℤ, (if ‖lpt 1 n‖ ≤ N then (1 : ℝ) else 0)) ≤ 300 * (N + 1) ^ 3 ∧
    (∑' n : Fin 3 → ℤ, (if ‖lpt 1 n‖ ≤ N then (1 : ℝ) / ‖lpt 1 n‖ ^ 2 else 0))
        ≤ 300 * (N + 1) ∧
    (∑' n : Fin 3 → ℤ, (if ‖lpt 1 n‖ ≤ N then (1 : ℝ) / ‖lpt 1 n‖ ^ 3 else 0))
        ≤ 300 * (1 + Real.log (2 + N)) := by
  have hK : (⌈N⌉₊ : ℝ) ≤ N + 1 := le_of_lt (Nat.ceil_lt_add_one hN)
  have hN1 : (0 : ℝ) ≤ N + 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine tsum_indicator_le ?_
    rw [card_cube]
    have h2 : (((2 * ⌈N⌉₊ + 1) ^ 3 : ℕ) : ℝ) = (2 * (⌈N⌉₊ : ℝ) + 1) ^ 3 := by
      push_cast; ring
    rw [h2]
    have h3 : 2 * (⌈N⌉₊ : ℝ) + 1 ≤ 3 * (N + 1) := by linarith
    calc (2 * (⌈N⌉₊ : ℝ) + 1) ^ 3 ≤ (3 * (N + 1)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h3 3
      _ = 27 * (N + 1) ^ 3 := by ring
      _ ≤ 300 * (N + 1) ^ 3 := by nlinarith [pow_nonneg hN1 3]
  · refine tsum_trunc_le (g := fun r : ℝ => (1 : ℝ) / r ^ 2) (fun r hr => by positivity)
      (antitone_inv_pow 2 (by norm_num)) hN ?_
    have h := (latSumOneDCount ⌈N⌉₊).2.1
    have hsimp : ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (j : ℝ) ^ 2)
        = ∑ j ∈ Finset.range (⌈N⌉₊ + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [prof]; ring
    rw [hsimp]
    calc ∑ j ∈ Finset.range (⌈N⌉₊ + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2
        ≤ 30 * ((⌈N⌉₊ : ℝ) + 1) := h
      _ ≤ 300 * (N + 1) := by linarith
  · refine tsum_trunc_le (g := fun r : ℝ => (1 : ℝ) / r ^ 3) (fun r hr => by positivity)
      (antitone_inv_pow 3 (by norm_num)) hN ?_
    have h := (latSumOneDCount ⌈N⌉₊).2.2
    have hsimp : ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (j : ℝ) ^ 3)
        = ∑ j ∈ Finset.range (⌈N⌉₊ + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [prof]; ring
    rw [hsimp]
    have hlog : Real.log ((⌈N⌉₊ : ℝ) + 1) ≤ Real.log (2 + N) := by
      refine Real.log_le_log (by positivity) ?_
      linarith
    calc ∑ j ∈ Finset.range (⌈N⌉₊ + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3
        ≤ 30 * (1 + Real.log ((⌈N⌉₊ : ℝ) + 1)) := h
      _ ≤ 30 * (1 + Real.log (2 + N)) := by linarith
      _ ≤ 300 * (1 + Real.log (2 + N)) := by
          have hnn : (0 : ℝ) ≤ 1 + Real.log (2 + N) := by
            have : (0 : ℝ) ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
            linarith
          linarith

/-! ## 6. The target -/

theorem latticeSumBounds :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℝ, 0 < m →
      (∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 3))
        ≤ K * (1 + Real.log (2 + 1 / m)))
    ∧ (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℝ, 0 < m →
      (∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 2))
        ≤ K * (1 / m + 1))
    ∧ (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℝ, 0 < m →
      (∑' n : Fin 3 → ℤ, 1 / ((1 + m * ‖lpt 1 n‖) ^ 3 * ‖lpt 1 n‖ ^ 4)) ≤ K)
    ∧ (∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 0 ≤ N →
      (∑' n : Fin 3 → ℤ, if ‖lpt 1 n‖ ≤ N then (1 : ℝ) else 0) ≤ K * (N + 1) ^ 3
      ∧ (∑' n : Fin 3 → ℤ, if ‖lpt 1 n‖ ≤ N then (1 : ℝ) / ‖lpt 1 n‖ ^ 2 else 0)
          ≤ K * (N + 1)
      ∧ (∑' n : Fin 3 → ℤ, if ‖lpt 1 n‖ ≤ N then (1 : ℝ) / ‖lpt 1 n‖ ^ 3 else 0)
          ≤ K * (1 + Real.log (2 + N))) := by
  refine ⟨⟨100, by norm_num, fun m hm => tsum_two_cube m hm⟩,
          ⟨100, by norm_num, fun m hm => tsum_two_sq m hm⟩,
          ⟨100, by norm_num, fun m hm => tsum_three_four m hm⟩,
          ⟨300, by norm_num, fun N hN => count_bounds N hN⟩⟩

end Work.BoseBogFS
