import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.botPart_mul
import Submission.Work.ORLyndon.levelPart_zero_mul_tauZpow

/-!
# The bottom-level transfer of the Magnus step

This is the mirror of `Work.ORLyndon.ann_rootVec_of_level_decomp`
(`Submission/Work/ORLyndon/ann_rootVec_of_level.lean`) for the *minimum* level of the root Fox vector
instead of the maximum.

The top-level transfer is used with the letter `x` and the level `i = mmHi t (u^l) x` (the largest
decoration of `x` in the Magnus rewriting); it consumes the induction hypothesis at the base at the
*top* decorated symbol `(x, mmHi)`.  The bottom-level transfer consumes it at the *bottom* decorated
symbol `(x, mmLo)`, which is what makes the induction step available when the top symbol of the only
available letter happens to be the letter exempted by the base induction hypothesis.

`Work.ORLyndon.ann_rootVec_of_level_decomp_bot` states: given

* `hDecomp : levelPart i (rootVec K r u x) = E * of (τ ^ i)` (the chain rule at the level `i`),
* `hDbound : every level in `supp (rootVec K r u x)` is `≥ i``,
* `hbook` (`Work.ORLyndon.levelPart_zero_mul_tauZpow`),
* `hbase : ∀ c supported on ker (levelOf), c * E = 0 → c = 0`,

one has `∀ b, b * rootVec K r u x = 0 → b = 0`.  The proof is the mirror of the top-level one: take
the *minimum* level `N` occurring in `b`, and identify the `(N+i)`-th level part of `b * rootVec` with
`levelPart N b * E * τ ^ i` using `Work.ORLyndon.botPart_mul`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The bottom-level transfer.**  Let `t` be a letter with `σ_t u = 1`, `x ≠ t` any other letter,
`i : ℤ` a level, and `E` an element of the group algebra supported on the Magnus base
`ker (levelOf)`.  Suppose

* the `i`-th level part of the `x`-component of the root Fox vector is `E * τ ^ i` (`hDecomp`);
* every level occurring in `rootVec K r u x` is `≥ i` (`hDbound`);
* the decomposition step `hbook`;
* `E` annihilates no non-zero base element (`hbase`), and `E ≠ 0`.

Then `b * rootVec K r u x = 0` forces `b = 0`. -/
theorem ann_rootVec_of_level_decomp_bot (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hE0 : E ≠ 0)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      i ≤ (levelOf t r u l hpow hσ g).toAdd)
    (hbook : ∀ (N : ℤ) (b : MonoidAlgebra K (OneRelatorGroup r)),
      levelPart t r u l hpow hσ 0
          (MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
            levelPart t r u l hpow hσ N b) =
        MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
          levelPart t r u l hpow hσ N b)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) → c * E = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 := by
  classical
  by_contra hb0
  -- the minimal level occurring in the support of `b`
  have hsne : (b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd)).Nonempty := by
    rw [Finset.image_nonempty, Finsupp.support_nonempty_iff]
    intro h
    exact hb0 (by ext g; rw [h]; rfl)
  set N : ℤ := (b.coeff.support.image (fun g => (levelOf t r u l hpow hσ g).toAdd)).min' hsne
    with hN
  have hNmem : N ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd) := Finset.min'_mem _ hsne
  have hNmin : ∀ y ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd), N ≤ y := fun y hy =>
    Finset.min'_le _ _ hy
  have hb_ge : ∀ g ∈ b.coeff.support, N ≤ (levelOf t r u l hpow hσ g).toAdd := fun g hg =>
    hNmin _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  obtain ⟨gN, hgN_supp, hgN_eq⟩ := Finset.mem_image.mp hNmem
  -- the bottom level part of `b` does not vanish
  have hpartN : levelPart t r u l hpow hσ N b ≠ 0 := by
    intro hzero
    have hcoe : (levelPart t r u l hpow hσ N b).coeff gN = 0 := by rw [hzero]; rfl
    rw [levelPart_coeff,
      if_pos (by rw [← hgN_eq]; simp : levelOf t r u l hpow hσ gN = Multiplicative.ofAdd N)] at hcoe
    exact Finsupp.mem_support_iff.mp hgN_supp hcoe
  -- the corresponding part of the product `b * rootVec` vanishes
  have hbot := botPart_mul (t := t) (hpow := hpow) (hσ := hσ)
    (a := b) (b := rootVec K r u x) (N := N) (M := i) hb_ge hDbound
  rw [hb, levelPart_zero] at hbot
  rw [hDecomp] at hbot
  -- cancel the factor `τ ^ i`
  have hτi : MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i) *
      MonoidAlgebra.of K (OneRelatorGroup r)
        (((presentRho r (FreeGroup.of t)) ^ i))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcancel : ∀ x : MonoidAlgebra K (OneRelatorGroup r),
      x * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i) *
          MonoidAlgebra.of K (OneRelatorGroup r)
            (((presentRho r (FreeGroup.of t)) ^ i))⁻¹ = x := by
    intro x
    rw [mul_assoc, hτi, mul_one]
  have h1 : levelPart t r u l hpow hσ N b * E = 0 := by
    have h2 : (levelPart t r u l hpow hσ N b * E) *
        MonoidAlgebra.of K (OneRelatorGroup r)
          ((presentRho r (FreeGroup.of t)) ^ i) = 0 := by
      rw [mul_assoc]; exact hbot
    have h3 := congrArg (fun z => z * MonoidAlgebra.of K (OneRelatorGroup r)
      (((presentRho r (FreeGroup.of t)) ^ i))⁻¹) h2
    rw [hcancel (levelPart t r u l hpow hσ N b * E), zero_mul] at h3
    exact h3
  -- the bookkeeping: a level-`N` element is `τ ^ (-N)` times a level-`0` element
  have hbk := hbook N b
  set c : MonoidAlgebra K (OneRelatorGroup r) :=
    MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
      levelPart t r u l hpow hσ N b with hc
  have hbk' : levelPart t r u l hpow hσ 0 c = c := by rw [hc]; exact hbk
  have hc0 : ∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1 := by
    intro g hg
    have hg' : g ∈ (levelPart t r u l hpow hσ 0 c).coeff.support := by rw [hbk']; exact hg
    have := levelPart_mem_support t r u l hpow hσ 0 c hg'
    simpa using this
  have hcE : c * E = 0 := by
    rw [hc]
    calc (MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ (-N)) *
            levelPart t r u l hpow hσ N b) * E
        = MonoidAlgebra.of K (OneRelatorGroup r)
            ((presentRho r (FreeGroup.of t)) ^ (-N)) *
            (levelPart t r u l hpow hσ N b * E) := by rw [mul_assoc]
      _ = 0 := by rw [h1, mul_zero]
  have hc0' : c = 0 := hbase c hc0 hcE
  -- hence the bottom level part of `b` vanishes: contradiction
  refine hpartN ?_
  have hzero : MonoidAlgebra.of K (OneRelatorGroup r)
      ((presentRho r (FreeGroup.of t)) ^ N) * c = 0 := by rw [hc0', mul_zero]
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

/-- **The bottom-level transfer**, with the bookkeeping `hbook` supplied by
`Work.ORLyndon.levelPart_zero_mul_tauZpow`. -/
theorem ann_rootVec_of_level_bot (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hE0 : E ≠ 0)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      i ≤ (levelOf t r u l hpow hσ g).toAdd)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) → c * E = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 :=
  ann_rootVec_of_level_decomp_bot t x hxt r u l hpow hσ i E hEbase hE0 hDecomp hDbound
    (fun N b => levelPart_zero_mul_tauZpow t (hpow := hpow) (hσ := hσ) (N := N) (b := b))
    hbase b hb

end Work.ORLyndon
