import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Basic

open scoped BigOperators
open Classical

namespace Work.Deep.GKO.OneFact.N5

noncomputable section

variable {n c : ℕ}

/-- The total number of misses, `∑_j |uncov (N j)|`, equals `∑_v missOf N v`. -/
theorem sum_card_uncov_eq_sum_missOf (N : Fin c → SimpleGraph (Fin n)) :
    (∑ j : Fin c, (uncov (N j)).card) = ∑ v : Fin n, missOf N v := by
  simp only [uncov, missOf, Finset.card_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]

/-- Few vertices are re-matched `L` times.  The family re-matches `v` on `cntOf N P v` classes;
if the total number of re-matches over all vertices is at most `5 * ∑_j |uncov (N j)|` and every
vertex is missed by at most `m` classes, then the set of vertices re-matched at least `L` times has
at most `5*n*m/L` elements (double counting: `L * |F| ≤ ∑_{v∈F} cntOf N P v ≤ ∑_v cntOf N P v`
while `∑_j |uncov (N j)| ≤ n*m`). -/
theorem cardHeavyLe {n c : ℕ} (N P : Fin c → SimpleGraph (Fin n)) {m L : ℕ}
    (hL : 0 < L)
    (hmiss : ∀ v, Work.Deep.GKO.OneFact.N5.missOf N v ≤ m)
    (hsum : ∑ v, Work.Deep.GKO.OneFact.N5.cntOf N P v
      ≤ 5 * ∑ j, (Work.Deep.GKO.OneFact.N5.uncov (N j)).card) :
    (Finset.univ.filter fun v => L ≤ Work.Deep.GKO.OneFact.N5.cntOf N P v).card
      ≤ 5 * n * m / L := by
  -- The total number of misses is at most `n * m`, since every vertex is missed at most `m` times.
  have hM : (∑ j : Fin c, (uncov (N j)).card) ≤ n * m := by
    rw [sum_card_uncov_eq_sum_missOf]
    calc ∑ v : Fin n, missOf N v ≤ ∑ v : Fin n, m := Finset.sum_le_sum fun v _ => hmiss v
      _ = n * m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Double counting on the set `F` of heavily re-matched vertices.
  have hstep1 : L * (Finset.univ.filter fun v => L ≤ cntOf N P v).card
      ≤ ∑ v, cntOf N P v := by
    have h1 : L * (Finset.univ.filter fun v => L ≤ cntOf N P v).card
        = ∑ v ∈ (Finset.univ.filter fun v => L ≤ cntOf N P v), L := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      simp
    rw [h1]
    calc ∑ v ∈ (Finset.univ.filter fun v => L ≤ cntOf N P v), L
        ≤ ∑ v ∈ (Finset.univ.filter fun v => L ≤ cntOf N P v), cntOf N P v :=
          Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, cntOf N P v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun v _ _ => Nat.zero_le _)
  have hkey : L * (Finset.univ.filter fun v => L ≤ cntOf N P v).card ≤ 5 * n * m := by
    calc L * (Finset.univ.filter fun v => L ≤ cntOf N P v).card ≤ ∑ v, cntOf N P v := hstep1
      _ ≤ 5 * (n * m) := le_trans hsum (Nat.mul_le_mul_left 5 hM)
      _ = 5 * n * m := by ring
  rw [Nat.le_div_iff_mul_le hL]
  calc (Finset.univ.filter fun v => L ≤ cntOf N P v).card * L
      = L * (Finset.univ.filter fun v => L ≤ cntOf N P v).card := Nat.mul_comm _ _
    _ ≤ 5 * n * m := hkey

end

end Work.Deep.GKO.OneFact.N5
