import Mathlib
import Submission.Work.PL.Subdiv.Cube.Defs

/-!
# `unitSimp π` is the convex hull of the Freudenthal vertices `unitVerts π`

The (closed) Freudenthal simplex `unitSimp π` of the unit cube is the set of points
`y ∈ [0,1]ⁿ` which are non-decreasing along the ordering `π`; its extreme points are the
`n + 1` `{0,1}`-vectors `wvec π k = {i | k ≤ π⁻¹ i}` (the vertices of `unitVerts π`).

We prove that `unitSimp π` is exactly their convex hull:

* `⊆`: every monotone `y ∈ [0,1]ⁿ` is the convex combination `∑ k, (t_k - t_{k-1}) • wvec π k`,
  where `t_k = y (π k)` and `t_{-1} = 0`, `t_n = 1` (the "Kuhn weights").  Non-negativity of
  the weights is exactly monotonicity, and they sum to one by telescoping.
* `⊇`: `unitSimp π` is convex (its defining conditions are linear inequalities) and contains
  `unitVerts π`.

The telescoping is packaged through the "staircase" function `kuhnStair t : ℕ → ℝ` with
`kuhnStair t 0 = 0` and `kuhnStair t (k+1) = t_k` (`= 1` for `k ≥ n`); the Kuhn weight of the
vertex `wvec π k` is `kuhnStair t (k+1) - kuhnStair t k`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

/-- The staircase function of a family of real numbers `t : Fin n → ℝ` indexed along an
ordering: `0, t_0, t_1, …, t_{n-1}, 1`, extended by `1` above `n`.  Consecutive differences are
the Kuhn weights of the Freudenthal simplex. -/
def kuhnStair (t : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | (k+1) => if h : k < n then t ⟨k, h⟩ else 1

@[simp] lemma kuhnStair_zero (t : Fin n → ℝ) : kuhnStair t 0 = 0 := rfl

lemma kuhnStair_succ (t : Fin n → ℝ) (k : ℕ) :
    kuhnStair t (k+1) = if h : k < n then t ⟨k, h⟩ else 1 := rfl

lemma kuhnStair_succ_of_lt (t : Fin n → ℝ) {k : ℕ} (h : k < n) :
    kuhnStair t (k+1) = t ⟨k, h⟩ := by
  rw [kuhnStair_succ]; simp [h]

lemma kuhnStair_succ_of_ge (t : Fin n → ℝ) {k : ℕ} (h : ¬ k < n) : kuhnStair t (k+1) = 1 := by
  rw [kuhnStair_succ]; simp [h]

lemma kuhnStair_succ_fin (t : Fin n → ℝ) (a : Fin n) : kuhnStair t ((a : ℕ) + 1) = t a := by
  rw [kuhnStair_succ_of_lt t a.isLt]

/-- The staircase function is non-decreasing up to `n`, provided `t` is non-decreasing with
values in `[0,1]`. -/
lemma kuhnStair_mono {t : Fin n → ℝ} (ht : ∀ a b : Fin n, a ≤ b → t a ≤ t b)
    (h0 : ∀ a : Fin n, 0 ≤ t a) (h1 : ∀ a : Fin n, t a ≤ 1) :
    ∀ k ≤ n, kuhnStair t k ≤ kuhnStair t (k+1) := by
  intro k hk
  rcases k with _ | k
  · rw [kuhnStair_zero, kuhnStair_succ]
    split_ifs with hn
    · exact h0 ⟨0, hn⟩
    · norm_num
  · have hk' : k < n := by omega
    rw [kuhnStair_succ_of_lt t hk']
    by_cases h : k + 1 < n
    · rw [kuhnStair_succ_of_lt t h]
      exact ht _ _ (by simp [Fin.le_iff_val_le_val])
    · rw [kuhnStair_succ_of_ge t h]
      exact h1 _

/-- The Kuhn weights `kuhnStair t (k+1) - kuhnStair t k`, `k = 0, …, n`, sum to `1`. -/
lemma kuhnStair_sum_weights (t : Fin n → ℝ) :
    ∑ k ∈ Finset.range (n+1), (kuhnStair t (k+1) - kuhnStair t k) = 1 := by
  rw [Finset.sum_range_sub, kuhnStair_zero, kuhnStair_succ_of_ge t (lt_irrefl n)]
  ring

/-- Partial sums of the Kuhn weights: for `m ≤ n` the terms with index `≤ m` sum to the `m`-th
staircase value. -/
lemma kuhnStair_sum_ite_le (f : ℕ → ℝ) {m : ℕ} (_hm : m ≤ n) :
    (∑ k ∈ Finset.range (n+1), (if k ≤ m then f k else 0)) = ∑ k ∈ Finset.range (m+1), f k := by
  have hf : (Finset.range (n+1)).filter (fun k => k ≤ m) = Finset.range (m+1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [← Finset.sum_filter, hf]

lemma kuhnStair_sum_range_le (t : Fin n → ℝ) {m : ℕ} (_hm : m ≤ n) :
    ∑ k ∈ Finset.range (m+1), (kuhnStair t (k+1) - kuhnStair t k) = kuhnStair t (m+1) := by
  rw [Finset.sum_range_sub, kuhnStair_zero]; ring

/-- `unitSimp π` is convex: it is cut out by the linear inequalities `0 ≤ y i`, `y i ≤ 1` and
`y (π a) ≤ y (π b)`. -/
lemma convex_unitSimp (π : Equiv.Perm (Fin n)) : Convex ℝ (unitSimp π) := by
  rw [convex_iff_forall_pos]
  rintro x ⟨hx0, hxm⟩ y ⟨hy0, hym⟩ a b ha hb hab
  have key : ∀ i : Fin n, (a • x + b • y) i = a * x i + b * y i := fun i => by
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · intro i
    rw [key i]
    exact ⟨by nlinarith [(hx0 i).1, (hy0 i).1], by nlinarith [(hx0 i).2, (hy0 i).2]⟩
  · intro a' b' hab'
    rw [key (π a'), key (π b')]
    nlinarith [hxm a' b' hab', hym a' b' hab']

theorem convexHull_unitVerts (n : ℕ) (π : Equiv.Perm (Fin n)) :
    convexHull ℝ ((unitVerts π : Finset (PL.E n)) : Set (PL.E n)) = unitSimp π := by
  refine le_antisymm (convexHull_min (unitVerts_subset_unitSimp π) (convex_unitSimp π)) ?_
  intro y hy
  obtain ⟨hyb, hym⟩ := hy
  set t : Fin n → ℝ := fun a => y (π a) with ht
  have ht0 : ∀ a, 0 ≤ t a := fun a => (hyb (π a)).1
  have ht1 : ∀ a, t a ≤ 1 := fun a => (hyb (π a)).2
  have htmono : ∀ a b : Fin n, a ≤ b → t a ≤ t b := fun a b hab => hym a b hab
  have hlam : ∀ k ≤ n, 0 ≤ kuhnStair t (k+1) - kuhnStair t k :=
    fun k hk => sub_nonneg.mpr (kuhnStair_mono htmono ht0 ht1 k hk)
  have hsum : ∑ k ∈ Finset.range (n+1), (kuhnStair t (k+1) - kuhnStair t k) = 1 :=
    kuhnStair_sum_weights t
  have hcoord : ∀ i : Fin n,
      y i = ∑ k ∈ Finset.range (n+1),
        (kuhnStair t (k+1) - kuhnStair t k) *
          (if k ≤ ((π.symm i : Fin n) : ℕ) then (1:ℝ) else 0) := by
    intro i
    have hta : t (π.symm i) = y i := by simp [ht]
    rw [← hta]
    have hsplit : (∑ k ∈ Finset.range (n+1),
          (kuhnStair t (k+1) - kuhnStair t k) *
            (if k ≤ ((π.symm i : Fin n) : ℕ) then (1:ℝ) else 0))
        = ∑ k ∈ Finset.range (n+1),
          (if k ≤ ((π.symm i : Fin n) : ℕ) then (kuhnStair t (k+1) - kuhnStair t k) else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : k ≤ ((π.symm i : Fin n) : ℕ) <;> simp [h]
    rw [hsplit,
      kuhnStair_sum_ite_le (fun k => kuhnStair t (k+1) - kuhnStair t k)
        (Nat.le_of_lt (π.symm i).isLt),
      kuhnStair_sum_range_le t (Nat.le_of_lt (π.symm i).isLt)]
    exact (kuhnStair_succ_fin t (π.symm i)).symm
  have hyeq : y = ∑ k ∈ Finset.range (n+1), (kuhnStair t (k+1) - kuhnStair t k) • wvec π k := by
    apply WithLp.ofLp_injective 2
    funext i
    rw [hcoord i, WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, wvec_apply]
  rw [hyeq]
  have hw0 : ∀ k ∈ Finset.range (n+1), 0 ≤ kuhnStair t (k+1) - kuhnStair t k := fun k hk => by
    simp only [Finset.mem_range] at hk
    exact hlam k (by omega)
  have hz : ∀ k ∈ Finset.range (n+1),
      wvec π k ∈ convexHull ℝ ((unitVerts π : Finset (PL.E n)) : Set (PL.E n)) := fun k hk => by
    simp only [Finset.mem_range] at hk
    exact subset_convexHull ℝ ((unitVerts π : Finset (PL.E n)) : Set (PL.E n))
      (mem_unitVerts (by omega))
  exact Convex.sum_mem (convex_convexHull ℝ _) hw0 hsum hz

end

end Work.PL.Subdiv.Cube
