import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Submission.Work.BoseBoxFock.KafzSym
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SymSum` — generic lattice-sum manipulations for `symDiscrep`

The discrepancy identity `symR r − KzOpC (r²/ℓ³) = r²•D2F + r•D1F + D0F`
(`Submission/Work/BoseBoxFock/symDiscrep.lean`) is proved by normalising *both* sides
into a linear combination of a fixed list of "word blocks" (single `Σ_k` sums of
k-independent weight against a fixed word, see `SymBlocks.lean`).

This file contains the purely generic (no-modes-specific) tools that the
normalisation uses:

* `sum_neg_smul_index`, `sum_neg_index` — the reindexing `k ↦ −k` of a lattice sum;
* `sum_neg_smul_add`, `sum_neg_smul_four` — the same for the symmetric combinations
  `X k + X (−k)` occurring in the Bogoliubov row `KzBogC`;
* `sum_excited_eq_sub` — `Σ_{k ≠ 0} = Σ_k − (k = 0)`;
* `sum_add_smul_split` — the *monomial split* of a coefficient function (this is what
  replaces "fusing" the many sums: we split every occurrence into monomial blocks
  instead of merging);
* `sum_smul_const_left/right` — pulling a constant scalar out of a lattice sum.

All are stated for an arbitrary ℂ-module target, so that they apply verbatim to
`cfock (Excited m) →ₗ[ℂ] cfock (Excited m)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Reindex a lattice sum by the involution `k ↦ −k`. -/
theorem sum_neg_smul_index {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : Mode → ℂ) (X : Mode → M) :
    (∑ k : Mode, c k • X (-k)) = ∑ k : Mode, c (-k) • X k := by
  refine Fintype.sum_equiv (Equiv.neg Mode) (fun k => c k • X (-k)) (fun k => c (-k) • X k) ?_
  intro k
  simp

/-- Reindex an unweighted lattice sum by the involution `k ↦ −k`. -/
theorem sum_neg_index {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (X : Mode → M) :
    (∑ k : Mode, X (-k)) = ∑ k : Mode, X k := by
  refine Fintype.sum_equiv (Equiv.neg Mode) (fun k => X (-k)) (fun k => X k) ?_
  intro k
  simp

/-- The symmetric pair `X k + X (−k)` reindexed into a single weight. -/
theorem sum_neg_smul_add {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : Mode → ℂ) (X : Mode → M) :
    (∑ k : Mode, c k • (X k + X (-k))) = ∑ k : Mode, (c k + c (-k)) • X k := by
  have h1 : (∑ k : Mode, c k • (X k + X (-k)))
      = (∑ k : Mode, c k • X k) + ∑ k : Mode, c k • X (-k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => (smul_add (c k) (X k) (X (-k))))
  rw [h1, sum_neg_smul_index c X, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => (add_smul (c k) (c (-k)) (X k)).symm)

/-- The symmetric four-term combination of two words, reindexed into a single weight. -/
theorem sum_neg_smul_four {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : Mode → ℂ) (X Y : Mode → M) :
    (∑ k : Mode, c k • (X k + Y k + X (-k) + Y (-k)))
      = ∑ k : Mode, (c k + c (-k)) • (X k + Y k) := by
  have h1 : (∑ k : Mode, c k • (X k + Y k + X (-k) + Y (-k)))
      = (∑ k : Mode, c k • (X k + Y k)) + ∑ k : Mode, c k • (X (-k) + Y (-k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [add_assoc, smul_add])
  have h2 : (∑ k : Mode, c k • (X (-k) + Y (-k)))
      = ∑ k : Mode, c (-k) • (X k + Y k) := by
    rw [sum_neg_smul_index c (fun k => X k + Y k)]
  rw [h1, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => (add_smul (c k) (c (-k)) (X k + Y k)).symm)

/-- The sum over the excited lattice points is the full sum minus the `k = 0` term. -/
theorem sum_excited_eq_sub {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {M : Type*} [AddCommGroup M] (F : Mode → M) :
    (∑ k ∈ Work.BoseB7.excited Mode, F k) = (∑ k : Mode, F k) - F 0 := by
  have h := Finset.sum_erase_add (Finset.univ : Finset Mode) F (Finset.mem_univ (0 : Mode))
  simp only [Work.BoseB7.excited]
  rw [eq_sub_iff_add_eq]
  exact h

/-- **Monomial split**: a lattice sum whose weight is a sum of two weights is the sum
of the two lattice sums.  (This is the direction used by the normalisation: every
occurrence is split into monomial blocks rather than fused.) -/
theorem sum_add_smul_split {Mode : Type*} [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (a b : Mode → ℂ) (X : Mode → M) :
    (∑ k : Mode, (a k + b k) • X k) = (∑ k : Mode, a k • X k) + ∑ k : Mode, b k • X k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => (add_smul (a k) (b k) (X k)))

/-- Pull a constant scalar (on the left) out of a lattice sum. -/
theorem sum_smul_const_left {Mode : Type*} [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (b : Mode → ℂ) (X : Mode → M) :
    (∑ k : Mode, (c * b k) • X k) = c • ∑ k : Mode, b k • X k := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [smul_smul])

/-- Pull a constant scalar (on the right) out of a lattice sum. -/
theorem sum_smul_const_right {Mode : Type*} [Fintype Mode]
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (b : Mode → ℂ) (X : Mode → M) :
    (∑ k : Mode, (b k * c) • X k) = c • ∑ k : Mode, b k • X k := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm, smul_smul])

end Work.BoseBoxFock
