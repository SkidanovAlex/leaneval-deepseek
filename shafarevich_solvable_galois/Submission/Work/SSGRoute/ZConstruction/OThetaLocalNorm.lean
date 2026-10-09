import Mathlib
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.ZDataMup.mupOddLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factor `oTheta` is trivial exactly on the local norm group

`Work.SSGRoute.ZDataMup.OddForm.oTheta α β v` is the local factor at the place `v` of `↥K` of the
abelian idèlic Artin map of the Kummer level `↥K(α^{1/p})`, evaluated at `β`.  By the one-place
faithfulness of that Artin map (`oddArtin_onePlace`) it is trivial exactly when the local image of
`β` at `v` is a **local norm** from the level:

  `oTheta α β v = 1 ↔ localImageAt v β ∈ localNormSubgroup (hLevel α) v`.

This is the interface through which the p. 16 computation (Schmidt–Wingberg, the diagonal case of
`TwoRec.claimOfPreTwo_diagonal`) supplies the `hout` hypothesis of the product formula
`oPairForm_sum_attach_eq_zero_of_outside`: at every place outside `T' = Σ ∪ {σQ}` the element
`σz` must be a local norm from `↥K(√X)` (a unit times a uniformiser square, the level being
unramified there), and at `P ∈ Σ` the pair `(X, a)` must give a trivial factor.

The analogous *finite-place* statement in the other direction (the local factor is `1` when the two
Kummer cochains kill the inertia outside `T'`) is
`Work.SSGRoute.H9.oTheta_ofFinite_eq_one_of_outside`; the archimedean companion, phrased with
`localNormSubgroup`, is
`Work.SSGRoute.H9.localNormSubgroup_hLevel_ofInfinite_of_not_isNegAt`.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

open Work.SSGRoute.ZDataMup.OddForm
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The local factor is trivial exactly on the local norm group.** -/
theorem oTheta_eq_one_iff_localNorm (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (α β : (↥K)ˣ)
    (v : NK.GlobalCFT.Place ↥K)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) α)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) α)] :
    oTheta (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ α β v = 1 ↔
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) α)) v :=
  Work.SSGRoute.ZDataMup.oddArtin_onePlace (K := K) (hLevel (Ω := Ω) (K := K) (p := p) α)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) ζ hζ α) v
    (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v β)

end Work.SSGRoute.ZConstruction
