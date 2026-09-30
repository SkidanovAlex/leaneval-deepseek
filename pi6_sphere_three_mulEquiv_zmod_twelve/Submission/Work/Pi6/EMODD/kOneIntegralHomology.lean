import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.EMFG.kOneComparison
import Submission.Work.EMFG.torusFGandEM
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The integral homology of a range model of `K(ℤ,1)` (area EMODD)

For `W` a range model of `K(ℤ,1)` through degree `N` (`Work.Serre.IsEMSpaceUpTo ℤ 1 _ N W w₀`) the
integral singular homology of `W` is that of the circle `S¹` in the range: `H₀(W;ℤ) ≅ ℤ`,
`H₁(W;ℤ) ≅ ℤ`, and `H_i(W;ℤ) = 0` for `2 ≤ i ≤ N`.

The argument is the `k = 1` comparison of Serre's finiteness chapter: `Work.EMFG.kOneComparison`
compares the integral homology of two range models of `K(A,1)` through `N`, and `S¹` is a range
model of `K(ℤ,1)` through every `N` (`Work.EMFG.sphOne_isEMSpaceUpTo`, from
`π₁(S¹) ≅ ℤ` and `Work.Serre.sphOneAspherical`).  The homology of the circle is the library's
`H_n(S^n) ≅ ℤ` (`Work.Cohomology.sphereHomologyTop`) in degree `1`, the vanishing
`H_k(S^n) = 0` for `k ≠ 0, n` (`Work.Cohomology.sphereHomologyZero`) in degrees `≥ 2`, and the
degree-`0` isomorphism `H₀(X;ℤ) ≅ ℤ` for path connected `X` (the augmentation
`TopCat.singularHomology₀ε`).
-/

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace Work.Pi6.EMODD

noncomputable section

/-- **`H₀(X;ℤ) ≅ ℤ` for a path-connected space `X`.**  The augmentation
`ε : H₀(X;ℤ) ⟶ ℤ` is an isomorphism for path connected `X`
(`TopCat.instIsIsoSingularHomology₀ε`). -/
theorem hZeroIsoOfPathConnected (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    Nonempty (Work.Pi6.HR ℤ X 0 ≅ ModuleCat.of ℤ ℤ) := by
  haveI hpc : PathConnectedSpace (TopCat.of X) := ‹PathConnectedSpace X›
  have hε : IsIso (TopCat.singularHomology₀ε (C := ModuleCat ℤ) (TopCat.of X)
      (ModuleCat.of ℤ ℤ)) := inferInstance
  exact ⟨@asIso (ModuleCat ℤ) _ (Work.Pi6.HR ℤ X 0) (ModuleCat.of ℤ ℤ)
    (TopCat.singularHomology₀ε (C := ModuleCat ℤ) (TopCat.of X) (ModuleCat.of ℤ ℤ)) hε⟩

/-- **`H₁(S¹;ℤ) ≅ ℤ`.**  Specialisation of `H_n(S^n) ≅ ℤ` to `n = 1`. -/
theorem hOneSphOne :
    Nonempty (Work.Pi6.HR ℤ (Work.Serre.Sph 1) 1 ≅ ModuleCat.of ℤ ℤ) :=
  Work.Cohomology.sphereHomologyTop 1 le_rfl

/-- **The integral homology of a range model of `K(ℤ,1)` through `N` is that of the circle.**
`H₀(W;ℤ) ≅ ℤ`, `H₁(W;ℤ) ≅ ℤ`, and `H_i(W;ℤ) = 0` for `2 ≤ i ≤ N`.

`Work.EMFG.kOneComparison` (`S¹` is a range model of `K(ℤ,1)` through every `N`,
`Work.EMFG.sphOne_isEMSpaceUpTo`) gives `H_i(W;ℤ) ≅ H_i(S¹;ℤ)` for every `i ≤ N`; the homology of
`S¹` is known from `Work.Cohomology.sphereHomologyTop`/`sphereHomologyZero` and the degree-`0`
augmentation `Work.Pi6.EMODD.hZeroIsoOfPathConnected`. -/
theorem kOneIntegralHomology (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W)
    (hW : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N W w₀) :
    (∀ i : ℕ, i ≤ 1 → i ≤ N → Nonempty (Work.Pi6.HR ℤ W i ≅ ModuleCat.of ℤ ℤ)) ∧
    (∀ i : ℕ, 2 ≤ i → i ≤ N → CategoryTheory.Limits.IsZero (Work.Pi6.HR ℤ W i)) := by
  -- comparison of `W` with the circle
  have hcmp := Work.EMFG.kOneComparison ℤ N W w₀ hW (Work.Serre.Sph 1) Work.Serre.sphOneBase
    (Work.EMFG.sphOne_isEMSpaceUpTo N)
  have h0 : Nonempty (Work.Pi6.HR ℤ (Work.Serre.Sph 1) 0 ≅ ModuleCat.of ℤ ℤ) := by
    haveI : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
    exact hZeroIsoOfPathConnected (Work.Serre.Sph 1)
  constructor
  · intro i hi1 hiN
    obtain ⟨e⟩ := hcmp i hiN
    rcases Nat.eq_zero_or_pos i with h0i | hpos
    · subst h0i
      exact ⟨e ≪≫ h0.some⟩
    · have hi1' : i = 1 := by omega
      subst hi1'
      exact ⟨e ≪≫ hOneSphOne.some⟩
  · intro i hi2 hiN
    obtain ⟨e⟩ := hcmp i hiN
    exact IsZero.of_iso (Work.Cohomology.sphereHomologyZero 1 i le_rfl (by omega) (by omega)) e

end

end Work.Pi6.EMODD
