import Mathlib
import Submission.Work.Peluse.Ulower.ss_defs

/-!
# The size ratio of the two boxes in the `U`-lowering display

`Work.Peluse.Ulower.ss_ratio` is the elementary comparison of the two support boxes that occur in
`dSup P N₀ N` and `dSup P (max N₀ (N ^ P.natDegree)) N`, i.e. the two choices `M = N` (polynomial
scale `N`) and `N₀ ↦ max N₀ (N ^ P.natDegree)` of the `x`-range in the display of `small_shift`.

Both boxes are symmetric intervals: `dSup P L N = L + polySup P N` and `symIcc L = [-L,L]`, so the
cardinality of the box is `2 * dSup P L N + 1`.  Since `polySup P N = ∑_{i ≤ d} |a_i| N^i`
contains the leading term `|a_d| N^d` with `d = P.natDegree` and `a_d = P.leadingCoeff`, and since
the second `x`-range dominates the first one by at most `N^d`, the ratio of the two cardinalities is
at least the "Weyl fraction" `|a| / (1 + |a|)` of the leading coefficient.

The proof is pure arithmetic and does not use either `hd` or `hN`; both are kept because the
statement is fixed by the caller.
-/

namespace Work.Peluse.Ulower

/-- The symmetric interval `symIcc L = [-L,L]` has `2L+1` elements. -/
private lemma card_symIcc (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - -((L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `polySup P N` dominates its leading term `|P.leadingCoeff| * N ^ P.natDegree`. -/
private lemma polySup_leading_le (P : Polynomial ℤ) (N : ℕ) :
    P.leadingCoeff.natAbs * N ^ P.natDegree ≤ Work.Peluse.polySup P N := by
  have hmem : P.natDegree ∈ Finset.range (P.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have h := Finset.single_le_sum (f := fun i => (P.coeff i).natAbs * N ^ i)
    (fun i (_ : i ∈ Finset.range (P.natDegree + 1)) => Nat.zero_le _) hmem
  simpa [Work.Peluse.polySup, Polynomial.coeff_natDegree] using h

/-- The arithmetic core: for `0 ≤ N0 ≤ M ≤ N0 + nd` and `0 ≤ p` with `a * nd ≤ p` one has
`a / (1+a) ≤ (2(N0+p)+1) / (2(M+p)+1)`. -/
private lemma ratio_alg {a p M N0 nd : ℝ} (ha : 0 ≤ a) (hN0 : 0 ≤ N0) (hp0 : 0 ≤ p)
    (hp : a * nd ≤ p) (hMN : N0 ≤ M) (hM : M ≤ N0 + nd) :
    a / (1 + a) ≤ (2 * (N0 + p) + 1) / (2 * (M + p) + 1) := by
  have h1 : (0:ℝ) < 1 + a := by linarith
  have h2 : (0:ℝ) < 2 * (M + p) + 1 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  have hDnd : M - N0 ≤ nd := by linarith
  have hprod : a * (M - N0) ≤ a * nd := mul_le_mul_of_nonneg_left hDnd ha
  nlinarith [hprod, hp]

theorem ss_ratio {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) {N N₀ : ℕ} (hN : 1 ≤ N) :
    ((P.leadingCoeff.natAbs : ℝ) / (1 + (P.leadingCoeff.natAbs : ℝ))) ≤
      (((Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)).card : ℝ) /
        ((Work.Peluse.symIcc (Work.Peluse.dSup P (max N₀ (N ^ P.natDegree)) N)).card : ℝ)) := by
  have hcard1 : ((Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)).card : ℝ) =
      2 * ((Work.Peluse.dSup P N₀ N : ℕ) : ℝ) + 1 := by
    rw [card_symIcc]; push_cast; ring
  have hcard2 :
      ((Work.Peluse.symIcc (Work.Peluse.dSup P (max N₀ (N ^ P.natDegree)) N)).card : ℝ) =
      2 * ((Work.Peluse.dSup P (max N₀ (N ^ P.natDegree)) N : ℕ) : ℝ) + 1 := by
    rw [card_symIcc]; push_cast; ring
  have hdSup1 : ((Work.Peluse.dSup P N₀ N : ℕ) : ℝ) =
      (N₀ : ℝ) + (Work.Peluse.polySup P N : ℝ) := by
    rw [Work.Peluse.dSup]; push_cast; ring
  have hdSup2 : ((Work.Peluse.dSup P (max N₀ (N ^ P.natDegree)) N : ℕ) : ℝ) =
      ((max N₀ (N ^ P.natDegree) : ℕ) : ℝ) + (Work.Peluse.polySup P N : ℝ) := by
    rw [Work.Peluse.dSup]; push_cast; ring
  rw [hcard1, hcard2, hdSup1, hdSup2]
  have hmax : ((max N₀ (N ^ P.natDegree) : ℕ) : ℝ) = max (N₀ : ℝ) ((N : ℝ) ^ P.natDegree) := by
    push_cast; rfl
  rw [hmax]
  refine ratio_alg (nd := (N:ℝ) ^ P.natDegree) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) ?_ ?_ ?_
  · exact_mod_cast polySup_leading_le P N
  · exact_mod_cast le_max_left N₀ (N ^ P.natDegree)
  · have : max N₀ (N ^ P.natDegree) ≤ N₀ + N ^ P.natDegree :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact_mod_cast this

end Work.Peluse.Ulower
