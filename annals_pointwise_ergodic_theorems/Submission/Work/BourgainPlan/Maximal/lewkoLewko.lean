import Mathlib
import Submission.Work.BourgainPlan.Maximal.varSeminormDefs

/-!
# The Lewko–Lewko / Mirek–Stein–Zorin-Kranich inequality for `2`-variations

Kosz–Mirek–Słomian–Zhang, Definition 5.1, condition (2), and the `r = 2` case of the
Lewko–Lewko inequality (arXiv:1808.09048, Lemma 2.5-style): the `ℓ²`-length of the increments of a
sequence along an increasing chain of indices `t 0 ≤ t 1 ≤ … ≤ t J` inside `[0, 2^n]` is dominated
by `2` times the sum, over the `n+1` dyadic levels `l ≤ n`, of the dyadic **block square functions**
`rmLevel n l a` of the increment sequence.

## The structure of the proof

Write `rmL l p = (p / 2^l) * 2^l` for the largest multiple of `2^l` below `p`, and telescope the
increment of a single chain step at each level:

  `a y - a x = Σ_{l<n} (g_l y - g_l x) + (a (rmL n y) - a (rmL n x))`,  where
  `g_l p = a (rmL l p) - a (rmL (l+1) p) ∈ {0} ∪ {δ^l_m : m}`,

with `δ^l_m = a ((m+1)·2^l) - a (m·2^l)` the level-`l` dyadic block increments of `a`.

* `glVec_div` : `g_l p = glVec l a (p / 2^l)`, where `glVec` is the explicit "state" of the level-`l`
  walk, indexed by `p / 2^l`.
* `walk_sq_sum_le` : **the walk inequality**.  For *any* sequence `b` and monotone `μ`, the squared
  `ℓ²`-length of the steps of the walk `j ↦ b (μ j)` is at most `4 Σ_ν ‖b ν‖²`.  The point is that
  the nonzero steps of a monotone walk are in bijection with the visited states (the last step out of
  a state and the first step into a state are each unique), so each state is charged at most `4`
  times.  Levels `l < n`: `μ j = t j / 2^l`, `b = glVec l a`, `N = 2^{n-l}+1`.
* `glVec_sq_sum_le` : the sum over the walk states is at most the sum of the level-`l` dyadic block
  square function (`glVec l a ν = δ^l_{ν-1}` for odd `ν`, and `0` for even `ν`).
* `walk_sq_sum_le_two` handles the top level `l = n`, where the walk takes only the two values
  `0, 2^n`: there is at most one nontrivial step.
* `minkowski_l2` / `sum_norm_sq_le_sq_sum_sqrt` : the `ℓ²` triangle inequality that sums the level
  estimates; `sqrt (Σ_j ‖Σ_l u_{j,l}‖²) ≤ Σ_l sqrt (Σ_j ‖u_{j,l}‖²)`.

The constants `4` for the level bound (giving `2` after the square root) and `1` for the top level
give exactly the `2` of the statement.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- `rmL i` is monotone. -/
lemma rmL_mono (i : ℕ) : Monotone (rmL i) := by
  intro j k hjk
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hjk)

/-- The level-`l` **state** of the dyadic walk: at level `l`, an index `p` either sits in the first
half of its dyadic block (state `0`) or in the second half (state `δ^l_m`).  Encoded by
`glVec l a κ = δ^l_{κ-1}` for odd `κ` (the "second half" of the `κ`-th block of length `2^l`) and
`0` for even `κ` (the "first half" of the `κ`-th block). -/
def glVec (l : ℕ) (a : ℕ → E) (κ : ℕ) : E :=
  if κ % 2 = 1 then a (κ * 2 ^ l) - a ((κ - 1) * 2 ^ l) else 0

/-- **The level-`l` increment is the state of the walk at `p / 2^l`.** -/
lemma glVec_div (l p : ℕ) (a : ℕ → E) :
    a (rmL l p) - a (rmL (l + 1) p) = glVec l a (p / 2 ^ l) := by
  have hdiv : p / 2 ^ (l + 1) = p / 2 ^ l / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have hrml1 : rmL (l + 1) p = (p / 2 ^ l - p / 2 ^ l % 2) * 2 ^ l := by
    rw [rmL_succ_eq, hdiv]
    have h := Nat.div_add_mod (p / 2 ^ l) 2
    congr 1
    omega
  rw [rmL, hrml1, glVec]
  rcases Nat.eq_zero_or_pos (p / 2 ^ l % 2) with hc | hc
  · have hc0 : ¬ (p / 2 ^ l % 2 = 1) := by omega
    rw [if_neg hc0, hc, Nat.sub_zero]
    abel
  · have hc1 : p / 2 ^ l % 2 = 1 := by omega
    rw [if_pos hc1, show p / 2 ^ l - p / 2 ^ l % 2 = p / 2 ^ l - 1 by omega]

/-- The level-`l` part of the increment of the chain step `[t j, t (j+1))`.  At level `n` it is the
full increment of `a` between the indices `rmL n (t j)` and `rmL n (t (j+1))`. -/
def chainStep (n : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (j : ℕ) : ℕ → E :=
  fun l => if l < n then glVec l a (t (j + 1) / 2 ^ l) - glVec l a (t j / 2 ^ l)
    else a (rmL n (t (j + 1))) - a (rmL n (t j))

/-- **The telescoping decomposition of an increment.** For any two indices `x, y`,
`a y - a x` is the sum of the level-`l` state differences plus the increment of the dyadic
approximations `rmL n`. -/
lemma sub_eq_sum_glVec (n : ℕ) (a : ℕ → E) (x y : ℕ) :
    a y - a x
      = (∑ l ∈ range n, (glVec l a (y / 2 ^ l) - glVec l a (x / 2 ^ l)))
        + (a (rmL n y) - a (rmL n x)) := by
  have htel : ∀ m : ℕ, (∑ l ∈ range n, (a (rmL l m) - a (rmL (l + 1) m)))
      = a m - a (rmL n m) := by
    intro m
    rw [Finset.sum_range_sub' (f := fun i => a (rmL i m)) n, rmL_zero]
  calc a y - a x
      = (a y - a (rmL n y)) - (a x - a (rmL n x)) + (a (rmL n y) - a (rmL n x)) := by abel
    _ = (∑ l ∈ range n, (a (rmL l y) - a (rmL (l + 1) y)))
        - (∑ l ∈ range n, (a (rmL l x) - a (rmL (l + 1) x)))
        + (a (rmL n y) - a (rmL n x)) := by rw [htel y, htel x]
    _ = (∑ l ∈ range n, ((a (rmL l y) - a (rmL (l + 1) y))
          - (a (rmL l x) - a (rmL (l + 1) x)))) + (a (rmL n y) - a (rmL n x)) := by
        rw [← Finset.sum_sub_distrib]
    _ = (∑ l ∈ range n, (glVec l a (y / 2 ^ l) - glVec l a (x / 2 ^ l)))
        + (a (rmL n y) - a (rmL n x)) := by
        rw [Finset.sum_congr rfl (fun l _ => by rw [glVec_div l y a, glVec_div l x a])]

/-- **The walk inequality.**  For a monotone walk `μ` in the index set and any sequence `b`, the
squared `ℓ²`-length of the steps of `j ↦ b (μ j)` is at most `4` times the `ℓ²`-norm of `b` over the
range of `μ`.  Each nonzero step is either the last step out of a state or the first step into one,
and both maps are injective along a monotone walk. -/
lemma walk_sq_sum_le (b : ℕ → E) (μ : ℕ → ℕ) (hμ : Monotone μ) (N J : ℕ)
    (hN : ∀ j ≤ J, μ j < N) :
    ∑ j ∈ range J, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 ≤ 4 * ∑ ν ∈ range N, ‖b ν‖ ^ 2 := by
  classical
  set T := (range J).filter (fun j => b (μ (j + 1)) ≠ b (μ j)) with hT
  have hTsub : T ⊆ range J := Finset.filter_subset _ _
  have hTmem : ∀ j ∈ T, b (μ (j + 1)) ≠ b (μ j) := fun j hj => (Finset.mem_filter.mp hj).2
  have hTlt : ∀ j ∈ T, j < J := fun j hj => Finset.mem_range.mp (hTsub hj)
  have hinj1 : ∀ j ∈ T, ∀ j' ∈ T, μ j = μ j' → j = j' := by
    intro j hj j' hj' heq
    rcases lt_trichotomy j j' with h | h | h
    · have h1 : μ (j + 1) ≤ μ j := by
        calc μ (j + 1) ≤ μ j' := hμ (by omega)
          _ = μ j := heq.symm
      have h2 : μ j ≤ μ (j + 1) := hμ (by omega)
      exact absurd (by rw [le_antisymm h1 h2]) (hTmem j hj)
    · exact h
    · have h1 : μ (j' + 1) ≤ μ j' := by
        calc μ (j' + 1) ≤ μ j := hμ (by omega)
          _ = μ j' := heq
      have h2 : μ j' ≤ μ (j' + 1) := hμ (by omega)
      exact absurd (by rw [le_antisymm h1 h2]) (hTmem j' hj')
  have hinj2 : ∀ j ∈ T, ∀ j' ∈ T, μ (j + 1) = μ (j' + 1) → j = j' := by
    intro j hj j' hj' heq
    rcases lt_trichotomy j j' with h | h | h
    · have h1 : μ j' = μ (j + 1) := le_antisymm (by rw [heq]; exact hμ (by omega)) (hμ (by omega))
      exact absurd (by rw [h1, heq]) (hTmem j' hj')
    · exact h
    · have h1 : μ j = μ (j' + 1) := le_antisymm (by rw [← heq]; exact hμ (by omega)) (hμ (by omega))
      exact absurd (by rw [h1, heq]) (hTmem j hj)
  have hsum1 : ∑ j ∈ T, ‖b (μ j)‖ ^ 2 ≤ ∑ ν ∈ range N, ‖b ν‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun ν => ‖b ν‖ ^ 2) (g := μ)
      (fun j hj j' hj' h => hinj1 j hj j' hj' h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun ν _ _ => by positivity)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_range.mpr (hN j (le_of_lt (hTlt j hj)))
  have hsum2 : ∑ j ∈ T, ‖b (μ (j + 1))‖ ^ 2 ≤ ∑ ν ∈ range N, ‖b ν‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun ν => ‖b ν‖ ^ 2) (g := fun j => μ (j + 1))
      (fun j hj j' hj' h => hinj2 j hj j' hj' h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun ν _ _ => by positivity)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_range.mpr (hN (j + 1) (hTlt j hj))
  have hzero : ∀ j ∈ range J, j ∉ T → ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 = 0 := by
    intro j hj hjT
    have h : ¬ (b (μ (j + 1)) ≠ b (μ j)) := by
      intro hc; exact hjT (Finset.mem_filter.mpr ⟨hj, hc⟩)
    rw [not_not] at h
    rw [h, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hpt : ∀ j ∈ T, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2
      ≤ 2 * (‖b (μ (j + 1))‖ ^ 2 + ‖b (μ j)‖ ^ 2) := by
    intro j _
    have h1 : ‖b (μ (j + 1)) - b (μ j)‖ ≤ ‖b (μ (j + 1))‖ + ‖b (μ j)‖ := norm_sub_le _ _
    have h2 : ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 ≤ (‖b (μ (j + 1))‖ + ‖b (μ j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖b (μ (j + 1))‖ - ‖b (μ j)‖)]
  calc ∑ j ∈ range J, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2
      = ∑ j ∈ T, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 :=
        (Finset.sum_subset hTsub hzero).symm
    _ ≤ ∑ j ∈ T, 2 * (‖b (μ (j + 1))‖ ^ 2 + ‖b (μ j)‖ ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * (∑ j ∈ T, ‖b (μ (j + 1))‖ ^ 2 + ∑ j ∈ T, ‖b (μ j)‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (∑ ν ∈ range N, ‖b ν‖ ^ 2 + ∑ ν ∈ range N, ‖b ν‖ ^ 2) := by
        have h1 := hsum1; have h2 := hsum2; linarith
    _ = 4 * ∑ ν ∈ range N, ‖b ν‖ ^ 2 := by ring

/-- **The two-value walk inequality.**  If a monotone walk takes at most the two values `ν₁ ≤ ν₂`,
then it has at most one nontrivial step and the squared `ℓ²`-length is at most
`‖b ν₂ - b ν₁‖²`. -/
lemma walk_sq_sum_le_two (b : ℕ → E) (μ : ℕ → ℕ) (hμ : Monotone μ) {ν₁ ν₂ : ℕ} (hle : ν₁ ≤ ν₂)
    (J : ℕ) (hval : ∀ j ≤ J, μ j = ν₁ ∨ μ j = ν₂) :
    ∑ j ∈ range J, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 ≤ ‖b ν₂ - b ν₁‖ ^ 2 := by
  classical
  set T := (range J).filter (fun j => μ (j + 1) ≠ μ j) with hT
  have hTsub : T ⊆ range J := Finset.filter_subset _ _
  have hTlt : ∀ j ∈ T, j < J := fun j hj => Finset.mem_range.mp (hTsub hj)
  have hTne : ∀ j ∈ T, μ (j + 1) ≠ μ j := fun j hj => (Finset.mem_filter.mp hj).2
  have key : ∀ j ∈ T, μ j = ν₁ ∧ μ (j + 1) = ν₂ := by
    intro j hj
    have hjJ : j < J := hTlt j hj
    have hback : μ j ≤ μ (j + 1) := hμ (by omega)
    rcases hval j (le_of_lt hjJ) with h1 | h1 <;> rcases hval (j + 1) hjJ with h2 | h2
    · exact absurd (by rw [h1, h2] : μ j = μ (j + 1)) (fun h => hTne j hj h.symm)
    · exact ⟨h1, h2⟩
    · exfalso
      have heq : ν₁ = ν₂ := le_antisymm hle (by omega)
      exact (hTne j hj) (by rw [h2, h1, heq])
    · exact absurd (by rw [h1, h2] : μ j = μ (j + 1)) (fun h => hTne j hj h.symm)
  have hone : ∀ j ∈ T, ∀ j' ∈ T, j = j' := by
    intro j hj j' hj'
    rcases lt_trichotomy j j' with h | h | h
    · have h1 : μ (j + 1) = ν₂ := (key j hj).2
      have h2 : μ j' = ν₁ := (key j' hj').1
      have hmono : μ (j + 1) ≤ μ j' := hμ (by omega)
      have heq : ν₁ = ν₂ := le_antisymm hle (by omega)
      have h3 : μ (j' + 1) = μ j' := by
        rcases hval (j' + 1) (by have := hTlt j' hj'; omega) with hh | hh
        · rw [hh, h2]
        · rw [hh, h2, heq]
      exact absurd h3 (hTne j' hj')
    · exact h
    · have h1 : μ (j' + 1) = ν₂ := (key j' hj').2
      have h2 : μ j = ν₁ := (key j hj).1
      have hmono : μ (j' + 1) ≤ μ j := hμ (by omega)
      have heq : ν₁ = ν₂ := le_antisymm hle (by omega)
      have h3 : μ (j + 1) = μ j := by
        rcases hval (j + 1) (by have := hTlt j hj; omega) with hh | hh
        · rw [hh, h2]
        · rw [hh, h2, heq]
      exact absurd h3 (hTne j hj)
  have hzero : ∀ j ∈ range J, j ∉ T → ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 = 0 := by
    intro j hj hjT
    have h : μ (j + 1) = μ j := by
      by_contra hc
      exact hjT (Finset.mem_filter.mpr ⟨hj, hc⟩)
    rw [h, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hsum : ∑ j ∈ range J, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2
      = ∑ j ∈ T, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 := (Finset.sum_subset hTsub hzero).symm
  rw [hsum]
  rcases T.eq_empty_or_nonempty with hempty | ⟨j₀, hj₀⟩
  · rw [hempty, Finset.sum_empty]; positivity
  · have hsub : T ⊆ {j₀} := by
      intro j hj
      simp only [Finset.mem_singleton]
      exact hone j hj j₀ hj₀
    calc ∑ j ∈ T, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2
        ≤ ∑ j ∈ {j₀}, ‖b (μ (j + 1)) - b (μ j)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ‖b (μ (j₀ + 1)) - b (μ j₀)‖ ^ 2 := Finset.sum_singleton _ _
      _ = ‖b ν₂ - b ν₁‖ ^ 2 := by rw [(key j₀ hj₀).1, (key j₀ hj₀).2]

/-- The walk states of level `l` indexed by `ν ∈ {0, …, 2^{n-l}}` are at most the level-`l` dyadic
block increments `δ^l_{ν-1}` (for odd `ν`), so the walk's state sum is dominated by the level-`l`
block square function. -/
lemma glVec_sq_sum_le (n l : ℕ) (a : ℕ → E) (_hl : l < n) :
    ∑ ν ∈ range (2 ^ (n - l) + 1), ‖glVec l a ν‖ ^ 2
      ≤ ∑ m ∈ range (2 ^ (n - l)), ‖a ((m + 1) * 2 ^ l) - a (m * 2 ^ l)‖ ^ 2 := by
  classical
  set M := 2 ^ (n - l) with hM
  set s := (range (M + 1)).filter (fun ν => ν % 2 = 1) with hs
  have hs_sub : s ⊆ range (M + 1) := Finset.filter_subset _ _
  have h1 : ∑ ν ∈ range (M + 1), ‖glVec l a ν‖ ^ 2 = ∑ ν ∈ s, ‖glVec l a ν‖ ^ 2 := by
    refine (Finset.sum_subset hs_sub ?_).symm
    intro ν hν hνs
    have hc : ¬ (ν % 2 = 1) := by
      intro hc; exact hνs (Finset.mem_filter.mpr ⟨hν, hc⟩)
    simp [glVec, hc]
  have hinj : Set.InjOn (fun ν => ν - 1) ↑s := by
    intro ν hν ν' hν' heq
    have h1 : 1 ≤ ν := by have := (Finset.mem_filter.mp hν).2; omega
    have h2 : 1 ≤ ν' := by have := (Finset.mem_filter.mp hν').2; omega
    beta_reduce at heq
    omega
  have h2 : ∑ ν ∈ s, ‖glVec l a ν‖ ^ 2
      = ∑ m ∈ s.image (fun ν => ν - 1), ‖a ((m + 1) * 2 ^ l) - a (m * 2 ^ l)‖ ^ 2 := by
    rw [Finset.sum_image (f := fun m => ‖a ((m + 1) * 2 ^ l) - a (m * 2 ^ l)‖ ^ 2)
      (g := fun ν => ν - 1) hinj]
    refine Finset.sum_congr rfl fun ν hν => ?_
    have hodd : ν % 2 = 1 := (Finset.mem_filter.mp hν).2
    have hpos : 1 ≤ ν := by omega
    rw [glVec, if_pos hodd, Nat.sub_add_cancel hpos]
  have h3 : s.image (fun ν => ν - 1) ⊆ range M := by
    intro m hm
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hm
    have hνM : ν ≤ M := by have := Finset.mem_range.mp (Finset.mem_filter.mp hν).1; omega
    have hν1 : 1 ≤ ν := by have := (Finset.mem_filter.mp hν).2; omega
    have hM1 : 1 ≤ M := by rw [hM]; exact Nat.one_le_two_pow
    simp only [Finset.mem_range]
    omega
  refine le_trans (le_of_eq (h1.trans h2)) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg h3 (fun m _ _ => by positivity)

/-- **The level-`l` (`l < n`) square function bound.**  The squared `ℓ²`-length of the level-`l`
state walk along the chain is at most `4` times the square of the level-`l` block square function. -/
lemma level_sq_bound (n l J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (hl : l < n)
    (ht : Monotone t) (htop : ∀ j ≤ J, t j ≤ 2 ^ n) :
    ∑ j ∈ range J, ‖glVec l a (t (j + 1) / 2 ^ l) - glVec l a (t j / 2 ^ l)‖ ^ 2
      ≤ 4 * ∑ m ∈ range (2 ^ (n - l)), ‖a ((m + 1) * 2 ^ l) - a (m * 2 ^ l)‖ ^ 2 := by
  have hwalk := walk_sq_sum_le (glVec l a) (fun j => t j / 2 ^ l)
    (fun i j h => Nat.div_le_div_right (ht h)) (2 ^ (n - l) + 1) J (fun j hj => by
      have h1 : t j / 2 ^ l ≤ 2 ^ n / 2 ^ l := Nat.div_le_div_right (htop j hj)
      have h2 : 2 ^ n / 2 ^ l = 2 ^ (n - l) := Nat.pow_div hl.le (by norm_num)
      omega)
  exact le_trans hwalk (mul_le_mul_of_nonneg_left (glVec_sq_sum_le n l a hl) (by norm_num))

/-- **The top level (`l = n`).**  The walk `j ↦ rmL n (t j)` takes only the two values `0` and `2^n`,
so there is at most one nontrivial step. -/
lemma top_sq_bound (n J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t)
    (htop : ∀ j ≤ J, t j ≤ 2 ^ n) :
    ∑ j ∈ range J, ‖a (rmL n (t (j + 1))) - a (rmL n (t j))‖ ^ 2 ≤ ‖a (2 ^ n) - a 0‖ ^ 2 := by
  have hμ : Monotone (fun j => t j / 2 ^ n) := fun i j h => Nat.div_le_div_right (ht h)
  have hval : ∀ j ≤ J, t j / 2 ^ n = 0 ∨ t j / 2 ^ n = 1 := by
    intro j hj
    have h2 : 2 ^ n / 2 ^ n = 1 := Nat.div_self (Nat.two_pow_pos n)
    have h1 : t j / 2 ^ n ≤ 1 := by
      rw [← h2]
      exact Nat.div_le_div_right (htop j hj)
    exact Nat.le_one_iff_eq_zero_or_eq_one.mp h1
  have hwalk := walk_sq_sum_le_two (fun κ => a (κ * 2 ^ n)) (fun j => t j / 2 ^ n) hμ
    (by norm_num : (0 : ℕ) ≤ 1) J hval
  simpa [rmL] using hwalk

/-- **Minkowski's inequality for finite `ℓ²` sums**, derived from Cauchy–Schwarz. -/
lemma minkowski_l2 {ι κ : Type*} (s : Finset ι) (t : Finset κ) (x : ι → κ → ℝ) :
    Real.sqrt (∑ k ∈ t, (∑ i ∈ s, x i k) ^ 2)
      ≤ ∑ i ∈ s, Real.sqrt (∑ k ∈ t, (x i k) ^ 2) := by
  have hsq : ∑ k ∈ t, (∑ i ∈ s, x i k) ^ 2
      ≤ (∑ i ∈ s, Real.sqrt (∑ k ∈ t, (x i k) ^ 2)) ^ 2 := by
    have h1 : ∀ k ∈ t, (∑ i ∈ s, x i k) ^ 2 = ∑ i ∈ s, ∑ i' ∈ s, x i k * x i' k := by
      intro k _
      rw [sq, Finset.sum_mul_sum]
    calc ∑ k ∈ t, (∑ i ∈ s, x i k) ^ 2
        = ∑ k ∈ t, ∑ i ∈ s, ∑ i' ∈ s, x i k * x i' k := Finset.sum_congr rfl h1
      _ = ∑ i ∈ s, ∑ i' ∈ s, ∑ k ∈ t, x i k * x i' k := by
            rw [Finset.sum_comm]
            congr 1; ext i; rw [Finset.sum_comm]
      _ ≤ ∑ i ∈ s, ∑ i' ∈ s,
            Real.sqrt (∑ k ∈ t, (x i k) ^ 2) * Real.sqrt (∑ k ∈ t, (x i' k) ^ 2) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
            exact Real.sum_mul_le_sqrt_mul_sqrt t (fun k => x i k) (fun k => x i' k)
      _ = (∑ i ∈ s, Real.sqrt (∑ k ∈ t, (x i k) ^ 2)) ^ 2 := by
            rw [sq, Finset.sum_mul_sum]
  calc Real.sqrt (∑ k ∈ t, (∑ i ∈ s, x i k) ^ 2)
      ≤ Real.sqrt ((∑ i ∈ s, Real.sqrt (∑ k ∈ t, (x i k) ^ 2)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i ∈ s, Real.sqrt (∑ k ∈ t, (x i k) ^ 2) :=
        Real.sqrt_sq (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)

/-- The `ℓ²` triangle inequality in the form used to sum the level estimates. -/
lemma sum_norm_sq_le_sq_sum_sqrt {ι : Type*} (s : Finset ι) (J : ℕ) (u : ℕ → ι → E) :
    ∑ j ∈ range J, ‖∑ l ∈ s, u j l‖ ^ 2
      ≤ (∑ l ∈ s, Real.sqrt (∑ j ∈ range J, ‖u j l‖ ^ 2)) ^ 2 := by
  have h1 : ∑ j ∈ range J, ‖∑ l ∈ s, u j l‖ ^ 2 ≤ ∑ j ∈ range J, (∑ l ∈ s, ‖u j l‖) ^ 2 :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hm := minkowski_l2 s (range J) (fun l j => ‖u j l‖)
  have hA : 0 ≤ ∑ j ∈ range J, (∑ l ∈ s, ‖u j l‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  calc ∑ j ∈ range J, ‖∑ l ∈ s, u j l‖ ^ 2
      ≤ ∑ j ∈ range J, (∑ l ∈ s, ‖u j l‖) ^ 2 := h1
    _ = (Real.sqrt (∑ j ∈ range J, (∑ l ∈ s, ‖u j l‖) ^ 2)) ^ 2 := (Real.sq_sqrt hA).symm
    _ ≤ (∑ l ∈ s, Real.sqrt (∑ j ∈ range J, ‖u j l‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hm 2

/-- The top level `l = n` block square function is the single full increment of `a`. -/
lemma rmLevel_self (n : ℕ) (a : ℕ → E) : rmLevel n n a = ‖a (2 ^ n) - a 0‖ := by
  rw [rmLevel, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton]
  simp only [zero_add, one_mul, zero_mul]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (a (2 ^ n) - a 0))]

/-- For a sequence `a` in a seminormed group and a nondecreasing chain of indices `t` with `t j ≤ 2^n` for `j ≤ J`, the `ℓ²`-length `chainSq J a t` of the increments of `a` along `t` is bounded by `2` times the sum, over the `n+1` levels `l ≤ n`, of the dyadic block square functions `rmLevel n l a`. This is the Lewko–Lewko / Mirek-Stein-Zorin-Kranich inequality for `2`-variations (arXiv:1808.09048, Lemma 2.5-style, with `r = 2`); it is condition (2) of KMSZ Definition 5.1 (arXiv:2606.12663) for the `2`-variation seminorm. -/
theorem lewkoLewko {E : Type*} [SeminormedAddCommGroup E]
    (n J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t) (htop : ∀ j ≤ J, t j ≤ 2 ^ n) :
    Work.BourgainPlan.Maximal.chainSq J a t
      ≤ 2 * ∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l a := by
  have hdec : ∀ j ≤ J, a (t (j + 1)) - a (t j) = ∑ l ∈ range (n + 1), chainStep n a t j l := by
    intro j hj
    rw [sub_eq_sum_glVec n a (t j) (t (j + 1)), Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun l hl => ?_
      simp only [chainStep, if_pos (Finset.mem_range.mp hl)]
    · simp only [chainStep, if_neg (lt_irrefl n)]
  have hmain1 : ∑ j ∈ range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2
      ≤ (∑ l ∈ range (n + 1), Real.sqrt (∑ j ∈ range J, ‖chainStep n a t j l‖ ^ 2)) ^ 2 := by
    have h2 : ∑ j ∈ range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2
        = ∑ j ∈ range J, ‖∑ l ∈ range (n + 1), chainStep n a t j l‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hdec j (le_of_lt (Finset.mem_range.mp hj))]
    rw [h2]
    exact sum_norm_sq_le_sq_sum_sqrt (range (n + 1)) J (chainStep n a t)
  have hmain2 : Real.sqrt (∑ j ∈ range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2)
      ≤ ∑ l ∈ range (n + 1), Real.sqrt (∑ j ∈ range J, ‖chainStep n a t j l‖ ^ 2) := by
    rw [← Real.sqrt_sq (Finset.sum_nonneg fun l _ => Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hmain1
  have hmain3 : ∑ l ∈ range (n + 1), Real.sqrt (∑ j ∈ range J, ‖chainStep n a t j l‖ ^ 2)
      ≤ ∑ l ∈ range (n + 1), 2 * rmLevel n l a := by
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' : l < n + 1 := Finset.mem_range.mp hl
    by_cases hln : l < n
    · have hstep : ∀ j, chainStep n a t j l
          = glVec l a (t (j + 1) / 2 ^ l) - glVec l a (t j / 2 ^ l) :=
        fun j => by simp only [chainStep, if_pos hln]
      simp only [hstep]
      calc Real.sqrt (∑ j ∈ range J,
            ‖glVec l a (t (j + 1) / 2 ^ l) - glVec l a (t j / 2 ^ l)‖ ^ 2)
          ≤ Real.sqrt (4 * ∑ m ∈ range (2 ^ (n - l)),
              ‖a ((m + 1) * 2 ^ l) - a (m * 2 ^ l)‖ ^ 2) :=
            Real.sqrt_le_sqrt (level_sq_bound n l J a t hln ht htop)
        _ = 2 * rmLevel n l a := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
              show Real.sqrt 4 = 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
            rfl
    · have hln' : l = n := by omega
      rw [hln']
      have hstep : ∀ j, chainStep n a t j n
          = a (rmL n (t (j + 1))) - a (rmL n (t j)) :=
        fun j => by simp only [chainStep, if_neg (lt_irrefl n)]
      simp only [hstep]
      calc Real.sqrt (∑ j ∈ range J, ‖a (rmL n (t (j + 1))) - a (rmL n (t j))‖ ^ 2)
          ≤ Real.sqrt (‖a (2 ^ n) - a 0‖ ^ 2) :=
            Real.sqrt_le_sqrt (top_sq_bound n J a t ht htop)
        _ = ‖a (2 ^ n) - a 0‖ := Real.sqrt_sq (norm_nonneg _)
        _ = rmLevel n n a := (rmLevel_self n a).symm
        _ ≤ 2 * rmLevel n n a := by
            have := rmLevel_nonneg n n a
            linarith
  calc chainSq J a t
      = Real.sqrt (∑ j ∈ range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2) := rfl
    _ ≤ ∑ l ∈ range (n + 1), Real.sqrt (∑ j ∈ range J, ‖chainStep n a t j l‖ ^ 2) := hmain2
    _ ≤ ∑ l ∈ range (n + 1), 2 * rmLevel n l a := hmain3
    _ = 2 * ∑ l ∈ range (n + 1), rmLevel n l a := by rw [Finset.mul_sum]

end

end Work.BourgainPlan.Maximal
