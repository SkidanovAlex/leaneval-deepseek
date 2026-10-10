import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.style.haveILetI false

open Polynomial

/-!
Given a finite normal `L ⊆ ℚ̄` and `0 < p`, produce a finite normal `K ⊆ ℚ̄` containing `L` plus a
primitive `p^(i+1)`-st root of unity inside `K`.

Suggested route: `ℚ̄ = AlgebraicClosure ℚ` is algebraically closed of characteristic `0`, hence
carries `ζ : SSGRoute.QBar` with `IsPrimitiveRoot ζ (p ^ (i+1))`. Take
`K := L ⊔ IntermediateField.adjoin ℚ {ζ}`, and supply `FiniteDimensional ℚ K`, `Normal ℚ K`
(via the compositum-of-normals instance, using that `ℚ(ζ)` is the splitting field of
`X ^ (p^(i+1)) - 1` over `ℚ`), the inclusion `L ≤ K`, and `HasRootsOfUnity p K i` witnessed by
`ζ ∈ K`.  Use `namespace Work.SSGRoute` for the file.
-/
theorem exists_normal_sup_rootsOfUnity
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [Normal ℚ L]
    {p i : ℕ} (hp : 0 < p) :
    ∃ K : IntermediateField ℚ SSGRoute.QBar,
      FiniteDimensional ℚ K ∧ Normal ℚ K ∧ L ≤ K ∧ SSGRoute.HasRootsOfUnity p K i := by
  -- `p ≠ 0`, so `HasEnoughRootsOfUnity QBar (p ^ (i+1))` is available.
  haveI hne : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne'⟩
  -- a primitive `p^(i+1)`-st root of unity in `ℚ̄`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot SSGRoute.QBar (p ^ (i + 1))
  -- `ℚ(ζ)` is the splitting field of `X^(p^(i+1)) - 1`, hence finite and normal over `ℚ`.
  let f : ℚ[X] := X ^ (p ^ (i + 1)) - C 1
  let E : IntermediateField ℚ SSGRoute.QBar := IntermediateField.adjoin ℚ (f.rootSet SSGRoute.QBar)
  have hfnz : f ≠ 0 := by
    have : 0 < p ^ (i + 1) := pow_pos hp _
    simpa [f] using (X_pow_sub_C_ne_zero (R := ℚ) this (1 : ℚ))
  haveI hsplit : IsSplittingField ℚ E f :=
    IntermediateField.adjoin_rootSet_isSplittingField (K := ℚ) (L := SSGRoute.QBar) (p := f)
      (IsAlgClosed.splits (f.map (algebraMap ℚ SSGRoute.QBar)))
  haveI hnormE : Normal ℚ ↥E := Normal.of_isSplittingField f
  haveI hfdE : FiniteDimensional ℚ ↥E := IsSplittingField.finiteDimensional (↥E) f
  -- `ζ` is a root of `X^(p^(i+1)) - 1`.
  have hmem : ζ ∈ f.rootSet SSGRoute.QBar := by
    rw [mem_rootSet_of_ne hfnz]
    simp [f, hζ.pow_eq_one]
  refine ⟨L ⊔ E, ?_, ?_, le_sup_left, ζ, ?_, hζ⟩
  · -- finite: compositum of two finite extensions
    exact inferInstance
  · -- normal: compositum of two normal extensions
    exact @IntermediateField.normal_sup ℚ SSGRoute.QBar _ _ _ L E ‹Normal ℚ ↥L› hnormE
  · -- `ζ ∈ E ≤ L ⊔ E`
    exact (le_sup_right : E ≤ L ⊔ E) (IntermediateField.subset_adjoin ℚ _ hmem)

end Work.SSGRoute
