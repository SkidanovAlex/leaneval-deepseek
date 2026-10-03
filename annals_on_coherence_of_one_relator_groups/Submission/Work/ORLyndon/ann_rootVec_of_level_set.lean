import Mathlib
import Submission.Work.ORLyndon.ann_rootVec_of_level
import Submission.Work.ORLyndon.topPart_mul
import Submission.Work.ORLyndon.levelPart_zero_mul_tauZpow

/-
# The leading-level transfer for a *family* of root Fox vectors

`Work.ORLyndon.ann_rootVec_of_level_top` (`Submission/Work/ORLyndon/ann_rootVec_of_level.lean`)
ports the "component of the base Fox vector is right regular" statement across one letter `x`: if
`levelPart i (rootVec K r u x) = E * τ ^ i` with `E` supported on the Magnus base, then
`b * rootVec K r u x = 0` forces `b = 0`, provided base elements annihilated on the right by `E`
vanish.

Here we need the same statement for a whole family of letters `x j` (`j : ι`), each possibly at its
own level `i j` and with its own base element `E j`, under the single *weaker* hypothesis that a base
element annihilated by *all* the `E j` simultaneously vanishes.  This is exactly what the induction
of the Cohen--Lyndon theorem consumes: for each letter of the Magnus rewriting one obtains a
decomposition of the corresponding root Fox vector, and the induction hypothesis at the base is
available only jointly (one may not know a priori that each individual `E j` is right regular).

The proof is the leading-level argument of `ann_rootVec_of_level_decomp`, run simultaneously for all
`j`:

* let `N` be the maximal level occurring in the support of a nonzero `b`; the `N`-th level part of
  `b` does not vanish;
* for every `j`, `topPart_mul` identifies the `(N + i j)`-th level part of `b * rootVec K r u (x j)`
  with `levelPart N b * E j * τ ^ (i j)`; that product is the `(N + i j)`-th level part of `0`, so
  it vanishes, and cancelling the unit `τ ^ (i j)` yields `levelPart N b * E j = 0` for **every**
  `j`;
* the bookkeeping step `Work.ORLyndon.levelPart_zero_mul_tauZpow` turns `levelPart N b` into the
  base element `c = τ ^ (-N) * levelPart N b`, which is annihilated on the right by every `E j`;
* the joint base hypothesis gives `c = 0`, hence `levelPart N b = 0`, a contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

theorem ann_rootVec_of_level_set {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1)
    {ι : Type*} (x : ι → α) (hxt : ∀ j, x j ≠ t) (i : ι → ℤ)
    (E : ι → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hEbase : ∀ j, ∀ g ∈ (E j).coeff.support,
      Work.ORLyndon.levelOf t r u l hpow hσ g = 1)
    (hDecomp : ∀ j, Work.ORLyndon.levelPart t r u l hpow hσ (i j)
        (Work.ORLyndon.rootVec K r u (x j)) =
      E j * MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r)
        ((Work.ORLyndon.presentRho r (FreeGroup.of t)) ^ (i j)))
    (hDbound : ∀ j, ∀ g ∈ (Work.ORLyndon.rootVec K r u (x j)).coeff.support,
      (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ i j)
    (hbase : ∀ c : MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, Work.ORLyndon.levelOf t r u l hpow hσ g = 1) →
      (∀ j, c * E j = 0) → c = 0)
    (b : MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hb : ∀ j, b * Work.ORLyndon.rootVec K r u (x j) = 0) : b = 0 := by
  classical
  by_contra hb0
  -- the maximal level occurring in the support of `b`
  have hsne : (b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd)).Nonempty := by
    rw [Finset.image_nonempty, Finsupp.support_nonempty_iff]
    intro h
    exact hb0 (by ext g; rw [h]; rfl)
  let N : ℤ := (b.coeff.support.image (fun g => (levelOf t r u l hpow hσ g).toAdd)).max' hsne
  have hNmem : N ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd) := Finset.max'_mem _ hsne
  have hNmax : ∀ y ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd), y ≤ N := fun y hy =>
    Finset.le_max' _ _ hy
  have hb_le : ∀ g ∈ b.coeff.support, (levelOf t r u l hpow hσ g).toAdd ≤ N := fun g hg =>
    hNmax _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  obtain ⟨gN, hgN_supp, hgN_eq⟩ := Finset.mem_image.mp hNmem
  -- the top level part of `b` does not vanish
  have hpartN : levelPart t r u l hpow hσ N b ≠ 0 := by
    intro hzero
    have hcoe : (levelPart t r u l hpow hσ N b).coeff gN = 0 := by rw [hzero]; rfl
    rw [levelPart_coeff,
      if_pos (by rw [← hgN_eq]; simp : levelOf t r u l hpow hσ gN = Multiplicative.ofAdd N)] at hcoe
    exact Finsupp.mem_support_iff.mp hgN_supp hcoe
  -- the unit `τ ^ (i j)`
  have hτi : ∀ j, MonoidAlgebra.of K (OneRelatorGroup r)
        ((presentRho r (FreeGroup.of t)) ^ (i j)) *
      MonoidAlgebra.of K (OneRelatorGroup r)
        (((presentRho r (FreeGroup.of t)) ^ (i j)))⁻¹ = 1 := by
    intro j
    rw [← map_mul, mul_inv_cancel, map_one]
  -- for every `j`, the top level part of `b` annihilates `E j`
  have h1 : ∀ j, levelPart t r u l hpow hσ N b * E j = 0 := by
    intro j
    have htop := topPart_mul (t := t) (hpow := hpow) (hσ := hσ)
      (a := b) (b := rootVec K r u (x j)) (N := N) (M := i j) hb_le (hDbound j)
    rw [hb j, levelPart_zero] at htop
    rw [hDecomp j] at htop
    have h2 : (levelPart t r u l hpow hσ N b * E j) *
        MonoidAlgebra.of K (OneRelatorGroup r)
          ((presentRho r (FreeGroup.of t)) ^ (i j)) = 0 := by
      rw [mul_assoc]; exact htop
    have h3 := congrArg (fun (z : MonoidAlgebra K (OneRelatorGroup r)) =>
      z * MonoidAlgebra.of K (OneRelatorGroup r)
        (((presentRho r (FreeGroup.of t)) ^ (i j)))⁻¹) h2
    rw [mul_assoc, hτi j, mul_one, zero_mul] at h3
    exact h3
  -- the bookkeeping: a level-`N` element is `τ ^ (-N)` times a level-`0` element
  set c : MonoidAlgebra K (OneRelatorGroup r) :=
    MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
      levelPart t r u l hpow hσ N b with hc
  have hbk' : levelPart t r u l hpow hσ 0 c = c := by
    rw [hc]; exact levelPart_zero_mul_tauZpow t (hpow := hpow) (hσ := hσ)
  have hc0 : ∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1 := by
    intro g hg
    have hg' : g ∈ (levelPart t r u l hpow hσ 0 c).coeff.support := by rw [hbk']; exact hg
    have := levelPart_mem_support t r u l hpow hσ 0 c hg'
    simpa using this
  have hcE : ∀ j, c * E j = 0 := by
    intro j
    rw [hc, mul_assoc, h1 j, mul_zero]
  have hc_eq : c = 0 := hbase c hc0 hcE
  -- hence the top level part of `b` vanishes: contradiction
  refine hpartN ?_
  have hzero : MonoidAlgebra.of K (OneRelatorGroup r)
      ((presentRho r (FreeGroup.of t)) ^ N) * c = 0 := by rw [hc_eq, mul_zero]
  rw [hc] at hzero
  have hτN : MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ N) *
      MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) = 1 := by
    rw [← map_mul, ← zpow_add, add_neg_cancel, zpow_zero, map_one]
  have hcancel2 : ∀ x : MonoidAlgebra K (OneRelatorGroup r),
      MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ N) *
          (MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) * x) =
        x := by
    intro x
    rw [← mul_assoc, hτN, one_mul]
  rw [hcancel2 (levelPart t r u l hpow hσ N b)] at hzero
  exact hzero

end Work.ORLyndon
