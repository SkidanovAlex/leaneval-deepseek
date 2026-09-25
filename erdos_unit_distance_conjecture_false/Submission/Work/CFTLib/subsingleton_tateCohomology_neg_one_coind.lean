/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CFTLib
-/
import Mathlib
import Submission.Work.CFTLib.NKHerbrand

/-!
# Vanishing of `Ĥ⁻¹` passes to a coinduced representation

For an injective homomorphism `φ : G →* H` of finite groups and a `ℤ`-linear representation `A`
of `G`, Shapiro's lemma in degree `-1` of Tate cohomology gives
`Ĥ⁻¹(H, coind φ A) ≃ Ĥ⁻¹(G, A)` (the functor `coind` along an injective `φ` is "induction from
the subgroup `φ.range ≤ H`", and for finite groups induction and coinduction agree).  Hence
`Ĥ⁻¹(G, A) = 0` implies `Ĥ⁻¹(H, coind φ A) = 0`.

We deduce this from the two ingredients already available in the library:

* `Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient`, which presents `Ĥ⁻¹` as
  `ker N ⧸ I` (`Hm1Quotient`);
* `Work.CFT.Ledger.Hm1Quotient_coind`, Shapiro's lemma in degree `-1` in that presentation.

## Main result

* `Work.CFTLib.subsingleton_tateCohomology_neg_one_coind`
-/

open CategoryTheory

namespace Work.CFTLib

/-- If the `(-1)`-st Tate cohomology of a `ℤ`-representation `A` of a finite group `G` is a
subsingleton, then so is the `(-1)`-st Tate cohomology of the coinduced representation
`Rep.coind φ A` of `H`, for any injective `φ : G →* H` (Shapiro's lemma in degree `-1`). -/
theorem subsingleton_tateCohomology_neg_one_coind {G H : Type} [Group G] [Group H]
    [Fintype G] [Fintype H] (φ : G →* H) (hφ : Function.Injective φ) (A : Rep ℤ G)
    (h : Subsingleton (tateCohomology A (-1))) :
    Subsingleton (tateCohomology (Rep.coind φ A) (-1)) := by
  classical
  obtain ⟨eA⟩ := Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient A
  have hA : Subsingleton (Work.CFT.Ledger.Hm1Quotient A) := eA.symm.injective.subsingleton
  have hB : Subsingleton (Work.CFT.Ledger.Hm1Quotient (Rep.coind φ A)) :=
    (Work.CFT.Ledger.Hm1Quotient_coind φ A hφ).toEquiv.symm.subsingleton
  obtain ⟨eB⟩ := Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient (Rep.coind φ A)
  exact eB.injective.subsingleton

end Work.CFTLib
