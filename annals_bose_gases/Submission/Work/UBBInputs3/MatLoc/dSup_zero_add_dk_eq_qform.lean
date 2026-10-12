import Mathlib.Analysis.Complex.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.dSup_zero_add_dk_eq_qform`

The identity underlying the definition of the diagonal expectations in the
Lieb–Solovej localisation: the sum of the band expectations reconstructs the full
sesquilinear form,

    dSup A n ψ 0 + Σ_{k=1}^{n-1} d_k = ⟪ψ, A ψ⟫ = qform A (iRange n) ψ ψ ,

where `d_k = dSup A n ψ k + dSup A n ψ (-k)` collects the `k`-th supra- and
infra-diagonal of `A`.

## Proof

Everything is a finite reindexing of the double sum `Σ_{i,j ∈ iRange n} B i j`,
`B i j = conj(ψ i) A i j ψ j`.  Since `ψ` is supported in `iRange n = [0,n-1]`, the
summand `B i j` vanishes outside `iRange n × iRange n`, so

    Σ_{j∈[0,N]} B i j = Σ_{k∈[-N,N]} B i (i+k)         (N = n-1)

for every `i ∈ [0,N]`: the *only* nonzero contributions come from `k ∈ [-i, N-i]`
(parts `Work.UBBInputs3.MatLoc.sum_Icc_Icc_eq_sum_shift`).  Summing over `i` and
swapping the order (`Finset.sum_comm`) turns the double sum into `Σ_k cSup k`, where
`cSup k = Σ_i B i (i+k)` is the complex version of `dSup A n ψ k`.  Finally the
symmetric interval `[-N,N]` splits into `{0} ⊎ [1,N] ⊎ (-[1,N])`, giving
`Σ_{k∈[-N,N]} cSup k = cSup 0 + Σ_{k∈[1,N]} (cSup k + cSup (-k))`
(`Work.UBBInputs3.MatLoc.sum_Icc_symm_split`).  Taking real parts finishes.

Neither the support hypothesis on `A` nor its hermiticity is needed: the identity
holds for an arbitrary matrix function `A`.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- **Splitting a symmetric `ℤ`-interval.**  For `0 ≤ N`,

    Σ_{k ∈ [-N,N]} f k = f 0 + Σ_{k ∈ [1,N]} f k + Σ_{k ∈ [1,N]} f (-k) .

The interval `[-N,N]` is the disjoint union of the nonnegative part `[0,N]` and the
negative part `[-N,-1]`; the latter is carried to `[1,N]` by `k ↦ -k`. -/
theorem sum_Icc_symm_split (f : ℤ → ℂ) {N : ℤ} (hN : 0 ≤ N) :
    ∑ k ∈ Finset.Icc (-N) N, f k
      = f 0 + ∑ k ∈ Finset.Icc 1 N, f k + ∑ k ∈ Finset.Icc 1 N, f (-k) := by
  have hsplit : Finset.Icc (-N) N = Finset.Icc 0 N ∪ Finset.Icc (-N) (-1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 0 N) (Finset.Icc (-N) (-1)) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  have hA : ∑ k ∈ Finset.Icc 0 N, f k = f 0 + ∑ k ∈ Finset.Icc 1 N, f k := by
    rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hB : ∑ k ∈ Finset.Icc (-N) (-1), f k = ∑ k ∈ Finset.Icc 1 N, f (-k) := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; ring
    · intro k hk; ring
    · intro k hk; simp
  rw [hsplit, Finset.sum_union hdisj, hA, hB]

/-- **Reindexing a double sum by the difference.**  If `B` vanishes on the second
index outside `[0,N]`, then

    Σ_{i ∈ [0,N]} Σ_{j ∈ [0,N]} B i j = Σ_{k ∈ [-N,N]} Σ_{i ∈ [0,N]} B i (i+k) .

For fixed `i ∈ [0,N]` the map `j ↦ j - i` is a bijection `[0,N] → [-i, N-i]`, and
extending the range to `[-N,N]` adds only vanishing terms `B i (i+k)`
(`i + k ∉ [0,N]`).  Swapping the two sums finishes. -/
theorem sum_Icc_Icc_eq_sum_shift (B : ℤ → ℤ → ℂ) (N : ℤ)
    (hB : ∀ i j, j ∉ Finset.Icc 0 N → B i j = 0) :
    ∑ i ∈ Finset.Icc 0 N, ∑ j ∈ Finset.Icc 0 N, B i j
      = ∑ k ∈ Finset.Icc (-N) N, ∑ i ∈ Finset.Icc 0 N, B i (i + k) := by
  have hinner : ∀ i ∈ Finset.Icc 0 N,
      ∑ j ∈ Finset.Icc 0 N, B i j = ∑ k ∈ Finset.Icc (-N) N, B i (i + k) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have h1 : ∑ j ∈ Finset.Icc 0 N, B i j = ∑ k ∈ Finset.Icc (-i) (N - i), B i (i + k) := by
      refine Finset.sum_nbij' (fun j => j - i) (fun k => k + i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro j hj; omega
      · intro k hk; omega
      · intro j hj; congr 1; omega
    rw [h1]
    exact (Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside (f := fun k => B i (i + k))
      (a := -N) (b := N) (c := -i) (d := N - i) (by omega) (by omega)
      (by intro t ht; apply hB; simp only [Finset.mem_Icc] at ht ⊢; omega)).symm
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]

theorem dSup_zero_add_dk_eq_qform (A : ℤ → ℤ → ℂ) (n : ℕ) (ψ : ℤ → ℂ)
    (hAsupp : ∀ i j, A i j ≠ 0 → i ∈ Work.UBBInputs3.iRange n ∧ j ∈ Work.UBBInputs3.iRange n)
    (hAherm : ∀ i j, A j i = star (A i j))
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ Work.UBBInputs3.iRange n) :
    Work.UBBInputs3.dSup A n ψ 0
        + ∑ k ∈ Finset.Icc 1 ((n : ℤ) - 1), Work.UBBInputs3.dk A n ψ k
      = Work.UBBInputs3.qform A (Work.UBBInputs3.iRange n) ψ ψ := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp [Work.UBBInputs3.dSup, Work.UBBInputs3.dk, Work.UBBInputs3.qform, Work.UBBInputs3.iRange]
  · set N : ℤ := (n : ℤ) - 1 with hN
    have hNnn : 0 ≤ N := by
      have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
      omega
    -- `ψ` vanishes off `iRange n = [0,N]`, hence so does the summand `B`.
    have hB : ∀ i j, j ∉ Finset.Icc 0 N → star (ψ i) * A i j * ψ j = 0 := by
      intro i j hj
      have hψj : ψ j = 0 := by
        by_contra hne
        have hmem := hψsupp j hne
        simp only [Work.UBBInputs3.iRange] at hmem
        rw [← hN] at hmem
        exact hj hmem
      rw [hψj, mul_zero]
    -- The two reindexing facts.
    have hkey := sum_Icc_Icc_eq_sum_shift (fun i j => star (ψ i) * A i j * ψ j) N hB
    have hkey2 := sum_Icc_symm_split
      (fun k => ∑ i ∈ Finset.Icc 0 N, star (ψ i) * A i (i + k) * ψ (i + k)) hNnn
    -- The underlying identity of complex sums.
    have hcomplex :
        (∑ i ∈ Finset.Icc 0 N, star (ψ i) * A i (i + 0) * ψ (i + 0))
          + ∑ k ∈ Finset.Icc 1 N,
              ((∑ i ∈ Finset.Icc 0 N, star (ψ i) * A i (i + k) * ψ (i + k))
               + ∑ i ∈ Finset.Icc 0 N, star (ψ i) * A i (i + -k) * ψ (i + -k))
        = ∑ i ∈ Finset.Icc 0 N, ∑ j ∈ Finset.Icc 0 N, star (ψ i) * A i j * ψ j := by
      rw [hkey, hkey2, Finset.sum_add_distrib, add_assoc]
    -- For `k ∈ [1,N]` the diagonal `d_k` is the sum of the two shifted bands.
    have hdk : ∀ k ∈ Finset.Icc 1 N, Work.UBBInputs3.dk A n ψ k
        = Work.UBBInputs3.dSup A n ψ k + Work.UBBInputs3.dSup A n ψ (-k) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Work.UBBInputs3.dk, if_neg (by omega : k ≠ 0)]
    rw [Finset.sum_congr rfl hdk]
    simp only [Work.UBBInputs3.dSup, Work.UBBInputs3.qform, Work.UBBInputs3.iRange, ← hN]
    simp only [← Complex.add_re, ← Complex.re_sum]
    rw [hcomplex]

end Work.UBBInputs3.MatLoc
