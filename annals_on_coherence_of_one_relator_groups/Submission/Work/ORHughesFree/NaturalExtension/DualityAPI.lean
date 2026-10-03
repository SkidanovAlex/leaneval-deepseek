/-
# The row-wise dimension `rdim`: basic API

This file develops the elementary properties of `rdim rk K` (see `DualityDefs.lean`), the
supremum of `rk A` over the matrices `A` whose rows lie in the submodule `K ≤ R^n`.

The proofs are direct matrix arguments (no use of the idempotent-projection dimension `dimOf`):

* `rdim_bddAbove`, `rdim_nonempty` : the defining set is bounded (by the number of columns,
  `RankAPI.rk_le_right`) and nonempty;
* `rdim_mono` : monotonicity;
* `rdim_sup_le` : subadditivity, from `rk (A + B) ≤ rk A + rk B`;
* `rdim_le_card` : `rdim rk K ≤ n`;
* `rdim_eq_rk_rows` : for a matrix `A`, the dimension of the span of its rows is `rk A`
  (every matrix with rows in that span factors as `C * A`).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.DivisionRank.regular_leftIdeal_idempotent

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

variable {R : Type u} [Ring R] [VonNeumannRegularRing R]

/-- The defining set of `rdim` is bounded above: a matrix with `n` columns has rank at most
`n` (`RankAPI.rk_le_right`). -/
theorem rdim_bddAbove (rk : SylvesterRank R) {n : ℕ} (K : Submodule R (Fin n → R)) :
    BddAbove {x : ℝ | ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) R),
      (∀ i, (fun j => A i j) ∈ K) ∧ x = rk.rk m n A} :=
  ⟨(n : ℝ), fun x hx => by
    obtain ⟨m, A, -, rfl⟩ := hx
    exact RankAPI.rk_le_right rk A⟩

/-- The defining set of `rdim` is nonempty (the empty matrix). -/
theorem rdim_nonempty (rk : SylvesterRank R) {n : ℕ} (K : Submodule R (Fin n → R)) :
    ({x : ℝ | ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) R),
      (∀ i, (fun j => A i j) ∈ K) ∧ x = rk.rk m n A} : Set ℝ).Nonempty :=
  ⟨0, 0, 0, fun i => Fin.elim0 i, by rw [rk.rk_zero]⟩

/-- `rdim` is monotone in the submodule. -/
theorem rdim_mono (rk : SylvesterRank R) {n : ℕ} {K L : Submodule R (Fin n → R)}
    (h : K ≤ L) : rdim rk K ≤ rdim rk L := by
  refine csSup_le (rdim_nonempty rk K) ?_
  rintro x ⟨m, A, hA, rfl⟩
  exact le_csSup (rdim_bddAbove rk L) ⟨m, A, fun i => h (hA i), rfl⟩

/-- `rdim` is non-negative. -/
theorem rdim_nonneg (rk : SylvesterRank R) {n : ℕ} (K : Submodule R (Fin n → R)) :
    0 ≤ rdim rk K :=
  le_csSup (rdim_bddAbove rk K) ⟨0, 0, fun i => Fin.elim0 i, by rw [rk.rk_zero]⟩

/-- `rdim rk K ≤ n` for `K ≤ R^n`. -/
theorem rdim_le_card (rk : SylvesterRank R) {n : ℕ} (K : Submodule R (Fin n → R)) :
    rdim rk K ≤ (n : ℝ) :=
  csSup_le (rdim_nonempty rk K) (by
    rintro x ⟨m, A, -, rfl⟩
    exact RankAPI.rk_le_right rk A)

/-- `rdim` is subadditive. -/
theorem rdim_sup_le (rk : SylvesterRank R) {n : ℕ} (K L : Submodule R (Fin n → R)) :
    rdim rk (K ⊔ L) ≤ rdim rk K + rdim rk L := by
  classical
  refine csSup_le (rdim_nonempty rk (K ⊔ L)) ?_
  rintro x ⟨m, A, hA, rfl⟩
  have hdec : ∀ i : Fin m, ∃ b ∈ K, ∃ c ∈ L, b + c = (fun j : Fin n => A i j) :=
    fun i => Submodule.mem_sup.mp (hA i)
  choose b hb c hc hbc using hdec
  let B : Matrix (Fin m) (Fin n) R := fun i j => b i j
  let C : Matrix (Fin m) (Fin n) R := fun i j => c i j
  have hsum : B + C = A := by
    ext i j
    exact congrFun (hbc i) j
  have hB : rk.rk m n B ≤ rdim rk K :=
    le_csSup (rdim_bddAbove rk K) ⟨m, B, fun i => hb i, rfl⟩
  have hC : rk.rk m n C ≤ rdim rk L :=
    le_csSup (rdim_bddAbove rk L) ⟨m, C, fun i => hc i, rfl⟩
  calc rk.rk m n A = rk.rk m n (B + C) := by rw [hsum]
    _ ≤ rk.rk m n B + rk.rk m n C := RankAPI.rk_add_le rk B C
    _ ≤ rdim rk K + rdim rk L := add_le_add hB hC

/-- The dimension of the span of the rows of a matrix `A` equals `rk A`.  Indeed every matrix
`B` whose rows lie in the span of the rows of `A` factors as `B = C * A`, so
`rk B ≤ rk A` by `(SMat2)`. -/
theorem rdim_eq_rk_rows (rk : SylvesterRank R) {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    rdim rk (Submodule.span R (Set.range (fun i : Fin m => (fun j : Fin n => A i j)))) =
      rk.rk m n A := by
  classical
  unfold rdim
  refine le_antisymm ?_ ?_
  · refine csSup_le (rdim_nonempty rk _) ?_
    rintro x ⟨l, B, hB, rfl⟩
    have hrow : ∀ i : Fin l, ∃ c : Fin m → R,
        ∑ k, c k • (fun j : Fin n => A k j) = (fun j => B i j) := fun i =>
      (Submodule.mem_span_range_iff_exists_fun R).mp (hB i)
    choose c hc using hrow
    let C : Matrix (Fin l) (Fin m) R := fun i k => c i k
    have hCA : B = C * A := by
      ext i j
      have h := congrFun (hc i) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [Matrix.mul_apply]
      simp only [C]
      exact h.symm
    rw [hCA]
    exact rk.rk_mul_le_right C A
  · exact le_csSup (rdim_bddAbove rk _)
      ⟨m, A, fun i => Submodule.subset_span (Set.mem_range_self i), rfl⟩

section C01

variable [MulSemiringAction (Multiplicative ℤ) R]

/-- The left ideal of constant terms of polynomial elements of the left ideal generated by `p`
is contained in `C0set R p`. -/
theorem constIdeal_genIdeal_le_C0sub (p : SkewL R) (k : ℕ) :
    constIdeal (genIdeal p) k ≤ C0sub p := by
  unfold constIdeal degPart
  rw [Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨a, ⟨f, hfI, hfneg, rfl⟩, rfl⟩
  change (cvec R k f) 0 ∈ C0set R p
  obtain ⟨q, hq⟩ := hfI
  exact ⟨f, q, hq.symm, hfneg, rfl⟩

/-- The left ideal of constant terms of polynomial elements of the left annihilator of `p`
is contained in `C1set R p`. -/
theorem constIdeal_annSet_le_C1sub (p : SkewL R) (k : ℕ) :
    constIdeal (annSet p) k ≤ C1sub p := by
  unfold constIdeal degPart
  rw [Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨a, ⟨f, hfI, hfneg, rfl⟩, rfl⟩
  exact ⟨f, hfI, hfneg, rfl⟩

end C01

end Work.ORHughesFree.NaturalExtension
