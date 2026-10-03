import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.levelPart_rootVec_eq_base
import Submission.Work.ORLyndon.mmHi_mem_relatorLetters

/-!
# Lower bounds for the levels of the root Fox vector, and the bottom decoration of a letter

Two mirrors of the facts used at the *top* level in
`Submission/Work/ORLyndon/lyndonIndependence_eps_zero.lean`:

* `Work.ORLyndon.level_ge_of_foxD_eq_zero` -- the level *lower* bound `hDbound` of the bottom-level
  transfer: if the Fox derivative `∂(magRewRel t u)/∂(x,j)` vanishes for all decorations `j < i`, then
  every level occurring in the `x`-component of the root Fox vector is `≥ i`.  (The top-level
  counterpart is `Work.ORLyndon.level_le_of_foxD_eq_zero`.)
* `Work.ORLyndon.mmLo_le_of_mem_relatorLetters` -- a generator `(x,j)` of the decorated alphabet
  occurs in `magRewRel t u` only if `mmLo t u x ≤ j`.  (The top-level counterpart is
  `Work.ORLyndon.mmHi_mem_relatorLetters`.)
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- The `j`-th level part of the `x`-component of the root Fox vector vanishes when the Fox
derivative `∂(magRewRel t u)/∂(x,j)` does (the chain rule). -/
theorem levelPart_eq_zero_of_foxD_eq_zero' {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {x : α} (hxt : x ≠ t) {j : ℤ}
    (h : foxD (K := K) (X := ({a : α // a ≠ t} × ℤ)) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
      (Work.OROneRel.magRewRel t u) = 0) :
    levelPart t r u l hpow hσ j (rootVec K r u x) = 0 := by
  rw [levelPart_rootVec_eq_base t x hxt r u l hpow hσ j, h, map_zero, zero_mul]

/-- **The level lower bound.**  If every decoration `j < i` of the letter `x` is absent from the
Magnus rewriting of `u` (i.e. `∂v/∂(x,j) = 0`), then every level occurring in the `x`-component of
the root Fox vector is `≥ i`.  This is the hypothesis `hDbound` of the bottom-level transfer
`Work.ORLyndon.ann_rootVec_of_level_bot`. -/
theorem level_ge_of_foxD_eq_zero {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {x : α} (hxt : x ≠ t) {i : ℤ}
    (hdec : ∀ j : ℤ, j < i →
      foxD (K := K) (X := ({a : α // a ≠ t} × ℤ)) ((⟨x, hxt⟩ : {a : α // a ≠ t}), j)
        (Work.OROneRel.magRewRel t u) = 0) :
    ∀ g ∈ (rootVec K r u x).coeff.support, i ≤ (levelOf t r u l hpow hσ g).toAdd := by
  intro g hg
  by_contra hcon
  have hj : (levelOf t r u l hpow hσ g).toAdd < i := lt_of_not_ge hcon
  have hzero := levelPart_eq_zero_of_foxD_eq_zero' (K := K) (t := t) (r := r) (u := u) (l := l)
    (hpow := hpow) (hσ := hσ) hxt (hdec _ hj)
  have hcoeff : (levelPart t r u l hpow hσ ((levelOf t r u l hpow hσ g).toAdd)
      (rootVec K r u x)).coeff g = 0 := by rw [hzero]; rfl
  rw [levelPart_coeff, if_pos] at hcoeff
  · exact (Finsupp.mem_support_iff.mp hg) hcoeff
  · exact (ofAdd_toAdd (levelOf t r u l hpow hσ g)).symm

/-- **The bottom decoration of an occurring letter.**  A generator `(x, j)` of the decorated
alphabet `{a // a ≠ t} × ℤ` occurs in the Magnus rewriting `magRewRel t u` only if the decoration `j`
is at least `mmLo t u x`. -/
theorem mmLo_le_of_mem_relatorLetters (t : α) (u : FreeGroup α) (x : {a : α // a ≠ t}) {j : ℤ}
    (hj : ((x, j) : ({a : α // a ≠ t} × ℤ)) ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u)) :
    Work.OROneRel.mmLo t u x ≤ j := by
  classical
  have hjmem : j ∈ Work.OROneRel.mmDecs t u x :=
    (mem_relatorLetters_magRewRel_iff t u x j).mp hj
  rw [Work.OROneRel.mmLo, dif_pos ⟨j, hjmem⟩]
  exact Finset.min'_le _ _ hjmem

end Work.ORLyndon
