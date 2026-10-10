import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.ext_idele_shapiro
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E9's gluing leg: the restricted product of the local groups *is* `Ext^r_G(M, 𝕀_K)`

`E2` (`Work.SSGRoute.ext_idele_shapiro`, proved) states the restricted-product description of
`Ext^r_G(M, 𝕀_K)` as a *triple of statements*: localisation at a transversal `R` of the place orbits
is injective (clause (i)), is almost always unramified (clause (ii)), and every almost-everywhere
unramified `R`-family is attained (clause (iii)).  This file packages the last two into a single
*map* `glue` in the Shapiro direction — the `ι_v` of `SSGRoute/DESIGN_EXT.md` §2 — with the two
properties the design consumes:

* **(components)** `extLoc w (glue a) = a w` for every `w : R`, for every `a` which is unramified
  outside a finite set;
* **(reconstruction)** `glue (fun w => extLoc w x) = x` for every `x`.

This is the only place in the E9 chain where a choice enters (the `Classical.choose` witness); the
choice is harmless because the two clauses pin `glue` down.  Reading the primitive square
`Work.SSGRoute.PT.extLoc_yonedaPair` place by place turns "the local components of a globally paired
class" into "the sum of the local values", and this `glue` is what lets a consumer write a class as
the sum of its glued single-place components (the `Σ_v ι_v` of `DESIGN_EXT.md` §2), hence compare
`χ ∘ pairK` with `Σ_v pair_v` in the annihilator step of the design's assembly bullet 2.
-/

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT

noncomputable section

/-- **E9's gluing leg.**  There is a map from `R`-families of local classes (unramified outside a
finite set) to `Ext^r_G(M, 𝕀_K)` whose local components are the given family, and which is the
identity on the families coming from a class. -/
theorem exists_glue_extLoc (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M] (r : ℕ) (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) :
    ∃ glue : (∀ w : R, Abelian.Ext.{0} (Rep.res (decompK (k := k) w.1).subtype M)
        (localUnitsK (k := k) w.1) r) → Abelian.Ext.{0} M (idelesK k K) r,
      (∀ a : ∀ w : R, Abelian.Ext.{0} (Rep.res (decompK (k := k) w.1).subtype M)
          (localUnitsK (k := k) w.1) r,
        {w : R | ¬ IsUnramifiedExt (k := k) w.1 (a w)}.Finite →
        ∀ w : R, extLoc (k := k) w.1 (glue a) = a w) ∧
      (∀ x : Abelian.Ext.{0} M (idelesK k K) r,
        glue (fun w => extLoc (k := k) w.1 x) = x) := by
  classical
  obtain ⟨hinj, hunr, hsurj⟩ := ext_idele_shapiro k K M r R hR
  let glue : (∀ w : R, Abelian.Ext.{0} (Rep.res (decompK (k := k) w.1).subtype M)
      (localUnitsK (k := k) w.1) r) → Abelian.Ext.{0} M (idelesK k K) r :=
    fun a => if h : {w : R | ¬ IsUnramifiedExt (k := k) w.1 (a w)}.Finite
      then Classical.choose (hsurj a h) else 0
  refine ⟨glue, ?_, ?_⟩
  · intro a hfin w
    have hspec : ∀ w : R, extLoc (k := k) w.1 (Classical.choose (hsurj a hfin)) = a w :=
      Classical.choose_spec (hsurj a hfin)
    dsimp only [glue]
    rw [dif_pos hfin]
    exact hspec w
  · intro x
    have hbad : {w : R | ¬ IsUnramifiedExt (k := k) w.1
        (extLoc (k := k) w.1 x)}.Finite := by
      have hK : {w : NK.GlobalCFT.Place K | ¬ IsUnramifiedExt (k := k) w
          (extLoc (k := k) w x)}.Finite := hunr x
      exact hK.preimage (f := fun w : R => w.1) (fun a _ b _ h => Subtype.eq h)
    have hspec : ∀ w : R, extLoc (k := k) w.1
        (Classical.choose (hsurj (fun w => extLoc (k := k) w.1 x) hbad))
        = extLoc (k := k) w.1 x :=
      Classical.choose_spec (hsurj (fun w => extLoc (k := k) w.1 x) hbad)
    -- the chosen class agrees with `x` at every place of `R`, so it equals `x` by E2's clause (i)
    have hzero : ∀ w ∈ R, extLoc (k := k) w
        (Classical.choose (hsurj (fun w => extLoc (k := k) w.1 x) hbad) + (-x)) = 0 := by
      intro w hw
      have hneg : extLoc (k := k) w (-x) = -extLoc (k := k) w x := by
        have h := extLoc_add k K w (-x) x
        rw [neg_add_cancel, extLoc_zero k K w] at h
        exact eq_neg_of_add_eq_zero_left h.symm
      rw [extLoc_add k K w, hneg, hspec ⟨w, hw⟩, add_neg_cancel]
    have hsum := hinj _ hzero
    dsimp only [glue]
    rw [dif_pos hbad]
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hsum)

end

end Work.SSGRoute.PT
