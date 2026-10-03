import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.topPart_mul
import Submission.Work.ORLyndon.levelPart_zero_mul_tauZpow

/-!
# The leading-level transfer of the Magnus step

`Work.ORLyndon.ann_rootVec_of_level_decomp` is the algebraic heart of the induction of the
Cohen--Lyndon theorem: it ports the "component of the base Fox vector is right regular" statement
from the Magnus base `B = ker (levelOf)` to the annihilator statement for the root Fox vector of the
root `u` in the one-relator group `⟨α | u ^ l⟩`, in the case where some letter `t` of the root has
vanishing exponent sum `σ_t u = 1`.

The two inputs from the geometry of the Magnus rewriting are taken as hypotheses, so that this file
is independent of the rewriting theory:

* `hDecomp` -- the chain rule for the *top* level `i` of the `x`-component of the root Fox vector:
  `levelPart i (rootVec K r u x) = E * of (τ ^ i)`, where `E` is the image of the base Fox derivative
  `∂v/∂(x,i)` and `τ` is the class of `t` (`Work.ORLyndon.levelPart_rootVec_magnus` proves the case
  of every level `i`);
* `hbook` -- the bookkeeping step: an element of level `N` is a `τ ^ (-N)`-multiple of an element of
  level `0` (`Work.ORLyndon.levelPart_zero_mul_tauZpow`).

The statement `hbase` is the induction hypothesis at the base: `E` is right regular on the
subalgebra of elements supported on the base.

The transfer itself is the leading-term argument: for `b ≠ 0` with `b * rootVec = 0`, the product of
the top level part of `b` with the top level part of `rootVec` (which is `E * τ ^ i` by `hDecomp`)
equals the top level part of `b * rootVec = 0` by `topPart_mul`, hence vanishes; `hbase` then forces
the top level part of `b` to vanish, contradicting the choice of the top level.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The leading-level transfer.**  Let `t` be a letter with `σ_t u = 1`, `x ≠ t` any other letter,
`i : ℤ` a level, and `E` an element of the group algebra supported on the Magnus base
`ker (levelOf)`.  Suppose

* the `i`-th level part of the `x`-component of the root Fox vector is `E * τ ^ i` (`hDecomp`);
* every level occurring in `rootVec K r u x` is `≤ i` (`hDbound`);
* the decomposition step `hbook`;
* `E` annihilates no non-zero base element (`hbase`), and `E ≠ 0`.

Then `b * rootVec K r u x = 0` forces `b = 0`. -/
theorem ann_rootVec_of_level_decomp (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hE0 : E ≠ 0)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      (levelOf t r u l hpow hσ g).toAdd ≤ i)
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
  -- the maximal level occurring in the support of `b`
  have hsne : (b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd)).Nonempty := by
    rw [Finset.image_nonempty, Finsupp.support_nonempty_iff]
    intro h
    exact hb0 (by ext g; rw [h]; rfl)
  set N : ℤ := (b.coeff.support.image (fun g => (levelOf t r u l hpow hσ g).toAdd)).max' hsne
    with hN
  have hNmem : N ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd) := Finset.max'_mem _ hsne
  have hNmax : ∀ y ∈ b.coeff.support.image
      (fun g => (levelOf t r u l hpow hσ g).toAdd), y ≤ N := fun y hy => Finset.le_max' _ _ hy
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
  -- the corresponding part of the product `b * rootVec` vanishes
  have htop := topPart_mul (t := t) (hpow := hpow) (hσ := hσ)
    (a := b) (b := rootVec K r u x) (N := N) (M := i) hb_le hDbound
  rw [hb, levelPart_zero] at htop
  rw [hDecomp] at htop
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
      rw [mul_assoc]; exact htop
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
  -- hence the top level part of `b` vanishes: contradiction
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

/-- **The leading-level transfer**, with the bookkeeping `hbook` supplied by
`Work.ORLyndon.levelPart_zero_mul_tauZpow`. -/
theorem ann_rootVec_of_level_top (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hE0 : E ≠ 0)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      (levelOf t r u l hpow hσ g).toAdd ≤ i)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) → c * E = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 :=
  ann_rootVec_of_level_decomp t x hxt r u l hpow hσ i E hEbase hE0 hDecomp hDbound
    (fun N b => levelPart_zero_mul_tauZpow t (hpow := hpow) (hσ := hσ) (N := N) (b := b))
    hbase b hb

end Work.ORLyndon
