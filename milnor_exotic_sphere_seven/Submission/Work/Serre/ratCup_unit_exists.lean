import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The unit class of the Alexander–Whitney cup product on rational cohomology

`Work.Serre.ratCup` is the Alexander–Whitney product on the rational singular cohomology of a
space, chosen by `Classical.choose` from `Work.Cohomology.cupH`; `Work.Cohomology.cupH'` is
*the same* choice (both are `(Classical.choose (cupH ℚ X)) n m`, so `ratCup` and `cupH'` are
definitionally equal).  Hence the ring laws proved for `cupH'` in
`Submission/Work/Cohomology/CupRing.lean` apply verbatim to `ratCup`, and the unit class is the
class of the augmentation `Work.Cohomology.oneH ℚ X`, already proved there to be a left and right
unit (`cupH'_one_left`, `cupH'_one_right`).

The only work here is the bookkeeping of the degree casts: `H^{n+0} = H^n` definitionally, while
`H^{0+n} → H^n` requires transporting along `Nat.zero_add n`.
-/

namespace Work.Serre

/-- Transporting a cohomology class along a degree equality in one direction and back is the
identity.  (`h ▸ (h.symm ▸ y) = y`; proved by `cases h` since the cast along `rfl` is the
identity.) -/
theorem eqRec_symm_eqRec_self_ratCoh (X : TopCat) {a b : ℕ} (h : a = b)
    (y : ratCoh X b) :
    h ▸ (h.symm ▸ y) = y := by
  cases h
  rfl

/-- **The cup product on rational singular cohomology has a unit in degree `0`**: the class of the
augmentation `oneH` is a two-sided unit for `Work.Serre.ratCup`. -/
theorem ratCup_unit_exists (X : Type) [TopologicalSpace X] :
    ∃ u : Work.Serre.ratCoh (TopCat.of X) 0,
      ∀ (n : ℕ) (y : Work.Serre.ratCoh (TopCat.of X) n),
        (Nat.zero_add n) ▸ (Work.Serre.ratCup (TopCat.of X) 0 n u y) = y ∧
          (Nat.add_zero n) ▸ (Work.Serre.ratCup (TopCat.of X) n 0 y u) = y := by
  refine ⟨Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X)), ?_⟩
  intro n y
  constructor
  · -- `1 ⌣ y = y`, transported along `0 + n = n`
    have h1 : Work.Serre.ratCup (TopCat.of X) 0 n
        (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X))) y =
          (Nat.zero_add n).symm ▸ y :=
      Work.Cohomology.cupH'_one_left ℚ (TopCat.toSSet.obj (TopCat.of X)) n y
    rw [h1]
    exact eqRec_symm_eqRec_self_ratCoh (TopCat.of X) (Nat.zero_add n) y
  · -- `y ⌣ 1 = y`; `n + 0 = n` is definitional, so the cast is the identity
    have h2 : Work.Serre.ratCup (TopCat.of X) n 0 y
        (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X))) = y :=
      Work.Cohomology.cupH'_one_right ℚ (TopCat.toSSet.obj (TopCat.of X)) n y
    rw [h2]

end Work.Serre
