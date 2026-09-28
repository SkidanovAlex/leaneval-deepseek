import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.StemsB.serreC3_of_two_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The endgame of the `famSpace` route to `serreC3FiniteOne`

If `Γ` carries a map `g : Γ → X` with `π_i(g)` bijective for `i ≤ N` and a map `h : Γ → B` with
`π_i(h)` bijective for `i ≤ N` into a space `B` whose rational homology vanishes in degrees
`0 < t ≤ N`, then the rational homology of `X` vanishes there too.  This is the assembly of the
route described in `C3ONE_FAMSPACE_ROUTE.md`: with `B = famSpace` (the lens-space range model of
`K(A,1)`, `Work.RatHurewicz.famSpace`), both maps are the ones built from the model tower of `X`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The endgame.**  Two `π`-isomorphisms in a range out of a common space `Γ`, one into `X` and
one into a space `B` whose rational homology vanishes below `N`, force the rational homology of `X`
to vanish below `N`. -/
theorem ratH_isZero_of_two_models {Γ X B : Type} [TopologicalSpace Γ] [TopologicalSpace X]
    [TopologicalSpace B] (γ₀ : Γ) [PathConnectedSpace Γ] (g : C(Γ, X)) (h : C(Γ, B)) (N : ℕ)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN g i x))
    (hh : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN h i x))
    (hB : ∀ t : ℕ, 0 < t → t ≤ N → IsZero (ratH (TopCat.of B) t)) :
    ∀ t : ℕ, 0 < t → t < N → IsZero (ratH (TopCat.of X) t) := by
  have : Nonempty Γ := ⟨γ₀⟩
  intro t ht htN
  -- `h` is a rational homology isomorphism below `N` (range Whitehead), so the vanishing of
  -- `H_t(B;ℚ)` carries to `Γ`
  have hiso_h : IsIso (ratHomologyMap h t) :=
    RangeOne.rangeWhitehead Γ B γ₀ h N hh t htN
  have hΓ : IsZero (ratH (TopCat.of Γ) t) :=
    IsZero.of_iso (hB t ht (le_of_lt htN)) (asIso (ratHomologyMap h t))
  -- and `g` carries it from `Γ` to `X`
  have hiso_g : IsIso (ratHomologyMap g t) :=
    RangeOne.rangeWhitehead Γ X γ₀ g N hg t htN
  exact IsZero.of_iso hΓ (asIso (ratHomologyMap g t)).symm

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **Rational vanishing plus `π₀`-triviality gives rational acyclicity.**  This is the final step
of the `famSpace` route: the vanishing `H_t(X;ℚ) = 0` for every `t > 0` together with the
connectedness coming from `IsEMSpace` gives `RatAcyclic X`. -/
theorem ratAcyclic_of_ratH_vanishing {X : Type} [TopologicalSpace X] (pt : X)
    (hpi0 : Subsingleton (HomotopyGroup (Fin 0) X pt))
    (hvan : ∀ t : ℕ, 0 < t → IsZero (ratH (TopCat.of X) t)) : RatAcyclic X := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 X pt hpi0
  · have h1 : IsZero (ratH (TopCat.of X) n) := hvan n hn
    have h2 : IsZero (ratH (TopCat.of PUnit) n) :=
      (ratAcyclic_of_contractible PUnit).isZero_ratH hn
    exact Work.StemsB.serreC3Aux_isIso_of_subsingleton_module
      (ModuleCat.isZero_iff_subsingleton.mp h1) (ModuleCat.isZero_iff_subsingleton.mp h2)
      (ratHomologyMap (toPoint X) n)

end

end Work.Serre
