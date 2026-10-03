import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.exists_powerSeriesToeplitz
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix
import Submission.Work.ORHughesFree.RankAPI.rk_le_sum_diag_of_upperTriangular
import Submission.Work.ORHughesFree.NaturalExtension.rk_oneByOne_twist_pow
import Submission.Work.ORHughesFree.NaturalExtension.toeplitzSeries_submatrix_general
import Submission.Work.ORHughesFree.NaturalExtension.sum_rk_oneByOne_twist
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The "positive part minus negative part" decomposition of an integer:
`max i 0 - max (-i) 0 = i`. -/
private lemma int_max_sub_eq (i : ℤ) : max i 0 - max (-i) 0 = i := by
  rcases le_total 0 i with h | h
  · rw [max_eq_left h, max_eq_right (by omega : -i ≤ 0)]; ring
  · rw [max_eq_right h, max_eq_left (by omega : 0 ≤ -i)]; ring

/-- The absolute value of an integer is the sum of its positive and negative parts:
`max i (-i) = max i 0 + max (-i) 0`. -/
private lemma int_max_neg_decomp (i : ℤ) : max i (-i) = max i 0 + max (-i) 0 := by
  rcases le_total 0 i with h | h
  · rw [max_eq_left (by omega : -i ≤ i), max_eq_left h, max_eq_right (by omega : -i ≤ 0)]; ring
  · rw [max_eq_right (by omega : i ≤ -i), max_eq_right h,
      max_eq_left (by omega : 0 ≤ -i)]; ring

/-- Every integer `i` can be written `i = q - p` with `p, q : ℕ` and `p + q = max i (-i)`. -/
private lemma exists_nat_decomp (i : ℤ) :
    ∃ pp q : ℕ, ((q : ℤ) - (pp : ℤ) = i) ∧ (max i (-i) = ((pp + q : ℕ) : ℤ)) := by
  refine ⟨(max (-i) 0).toNat, (max i 0).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (le_max_right (-i) 0), Int.toNat_of_nonneg (le_max_right i 0)]
    exact int_max_sub_eq i
  · have h1 : ((((max (-i) 0).toNat : ℕ)) : ℤ) = max (-i) 0 :=
      Int.toNat_of_nonneg (le_max_right (-i) 0)
    have h2 : ((((max i 0).toNat : ℕ)) : ℤ) = max i 0 :=
      Int.toNat_of_nonneg (le_max_right i 0)
    push_cast
    rw [h1, h2, add_comm]
    exact int_max_neg_decomp i

/-- Rank lower bound for the Toeplitz matrix of a skew Laurent series whose first non-zero
coefficient is `a` in degree `i` (of any sign).  Take the submatrix on the rows `r` with
`max 0 (-i) ≤ r` and `r ≤ N-1-i`, and the columns `s = r + i` (the "diagonal" of the shifted
Toeplitz matrix).  The entry `(r, s)` of `toeplitzSeries N p` is `τ^r (p_{s-r})`, which vanishes for
`s - r < i` by the hypothesis `hlo`, so the submatrix is upper triangular with diagonal entries
`τ^r a` (when `s - r = i`); it has `N - max i (-i)` rows.  The upper triangular rank estimate, the
`τ`-compatibility of `rk` and the submatrix estimate `rk_submatrix` give the bound.  (An upper
triangular estimate is available as
`Work.ORHughesFree.RankAPI.rk_le_sum_diag_of_upperTriangular`, being proved in parallel: if it is
not yet present, prove it inline — it is an induction on `n` using the Sylvester axiom
`rk_blockUpper`.) -/
theorem rk_toeplitzSeries_ge_of_leading_general {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (rk : Work.ORHughesFree.SylvesterRank U)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (p : Work.ORHughesFree.SkewLaurentSeries U) (i : ℤ) (a : U) (hi : p.1 i = a)
    (hlo : ∀ k : ℤ, k < i → p.1 k = 0) (N : ℕ) (hN : max i (-i) < (N : ℤ)) :
    ((((N : ℤ) - max i (-i) : ℤ)) : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a) ≤
      rk.rk N N (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p) := by
  classical
  obtain ⟨pp, q, hdiff, hm⟩ := exists_nat_decomp i
  have hpqN : pp + q < N := by
    have h' : ((pp + q : ℕ) : ℤ) < (N : ℤ) := by rw [← hm]; exact hN
    exact_mod_cast h'
  obtain ⟨hut, hdiag⟩ := toeplitzSeries_submatrix_general p i a hi hlo N pp q hdiff hpqN
  set M : Matrix (Fin (N - (pp + q))) (Fin (N - (pp + q))) U :=
    (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p).submatrix
      (fun c : Fin (N - (pp + q)) => (⟨pp + c.1, by omega⟩ : Fin N))
      (fun d : Fin (N - (pp + q)) => (⟨q + d.1, by omega⟩ : Fin N)) with hM
  have hutM : ∀ c d : Fin (N - (pp + q)), (d : ℕ) < (c : ℕ) → M c d = 0 := by
    intro c d hcd
    rw [hM]
    exact hut c d hcd
  have hdiagM : ∀ c : Fin (N - (pp + q)),
      M c c = (Multiplicative.ofAdd ((pp + c.1 : ℕ) : ℤ)) • a := by
    intro c
    rw [hM]
    exact hdiag c
  have hUT := Work.ORHughesFree.RankAPI.rk_le_sum_diag_of_upperTriangular rk M hutM
  have hsum : (∑ c : Fin (N - (pp + q)),
        rk.rk 1 1 (Work.ORHughesFree.oneByOne (M c c)))
      = ((N - (pp + q) : ℕ) : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a) := by
    rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => by rw [hdiagM c])]
    exact sum_rk_oneByOne_twist rk hτ a (N - (pp + q)) pp
  have hsub : rk.rk (N - (pp + q)) (N - (pp + q)) M
      ≤ rk.rk N N (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p) := by
    rw [hM]
    exact Work.ORHughesFree.RankAPI.rk_submatrix rk _ _ _
  have harith : ((((N : ℤ) - max i (-i) : ℤ)) : ℝ) = ((N - (pp + q) : ℕ) : ℝ) := by
    have h1 : ((N : ℤ) - max i (-i)) = ((N - (pp + q) : ℕ) : ℤ) := by
      rw [hm, Int.ofNat_sub (le_of_lt hpqN)]
    rw [h1]
    push_cast
    ring
  calc ((((N : ℤ) - max i (-i) : ℤ)) : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a)
      = ((N - (pp + q) : ℕ) : ℝ) * rk.rk 1 1 (Work.ORHughesFree.oneByOne a) := by
        rw [harith]
    _ = ∑ c : Fin (N - (pp + q)), rk.rk 1 1 (Work.ORHughesFree.oneByOne (M c c)) := hsum.symm
    _ ≤ rk.rk (N - (pp + q)) (N - (pp + q)) M := hUT
    _ ≤ rk.rk N N (Work.ORHughesFree.NaturalExtension.toeplitzSeries N p) := hsub

end Work.ORHughesFree.NaturalExtension
