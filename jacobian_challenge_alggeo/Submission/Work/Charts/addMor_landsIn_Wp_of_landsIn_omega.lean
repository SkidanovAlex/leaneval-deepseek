import Mathlib
import Submission.Work.Charts.Step3Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### Helper lemmas -/

/-- **Naturality of `addMor` in the source**: precomposing both arguments with the same
morphism.  This is the naturality of `CartesianMonoidalCategory.liftEquiv`. -/
theorem addMor_comp {C : Curve K} [Work.SpecLin.DivBase C]
    {symGeom : ∀ n, Work.SpecLin.SymGeom C n}
    {addMap : ∀ m n, (symGeom m).S ⊗ (symGeom n).S ⟶ (symGeom (m + n)).S}
    {X Y : Sch K} {r m : ℕ} (f : Y ⟶ X) (u : X ⟶ (symGeom r).S) (v : X ⟶ (symGeom m).S) :
    f ≫ Work.Domain.Resid.addMor symGeom addMap u v =
      Work.Domain.Resid.addMor symGeom addMap (f ≫ u) (f ≫ v) := by
  change f ≫ (CartesianMonoidalCategory.lift u v ≫ addMap r m) =
    CartesianMonoidalCategory.lift (f ≫ u) (f ≫ v) ≫ addMap r m
  rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]

/-- **The key set-theoretic step.**  The preimage of `Ω_E` under `bcFst : S_L ⟶ S` is
contained in the preimage of `W′` under `addCentre E`.

Indeed, `Ω_E` is by definition the complement of the image of the complement of
`addCentre E ⁻¹ᵁ W′`: so if `f x ∈ Ω_E` and `x ∉ addCentre E ⁻¹ᵁ W′`, then `f x` would lie
in the image of the complement of `addCentre E ⁻¹ᵁ W′`, a contradiction. -/
theorem preimage_omegaOpen_le_preimage_Wp {C : Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (G : Step3Geo R symGeom) (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : BNDataAt R symGeom)
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (E : FPt ((symGeom R.g).S) L) :
    (bcFst ((symGeom R.g).S) L).left ⁻¹ᵁ (omegaOpen R symGeom D G E a d) ≤
      (addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d) := by
  intro x hx
  by_contra hxnot
  have hx' : (bcFst ((symGeom R.g).S) L).left x ∈
      (omegaOpen R symGeom D G E a d : Set _) :=
    (Scheme.Hom.mem_preimage (f := (bcFst ((symGeom R.g).S) L).left)).mp hx
  have hxnot' : ¬ ((addCentre R symGeom D E).left x ∈ ((Wp R symGeom D G a d) : Set _)) :=
    fun hc => hxnot
      ((Scheme.Hom.mem_preimage (f := (addCentre R symGeom D E).left)).mpr hc)
  have key : (bcFst ((symGeom R.g).S) L).left x ∈
      Set.image ((bcFst ((symGeom R.g).S) L).left)
        ((((addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d)) : Set _)ᶜ) := by
    refine ⟨x, ?_, rfl⟩
    rw [Set.mem_compl_iff]
    exact hxnot'
  have hx'' := hx'
  simp only [omegaOpen] at hx''
  exact hx'' key

/-! ### The main theorem -/

theorem addMor_landsIn_Wp_of_landsIn_omega {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (G : Work.Charts.Step3Geo R symGeom)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : Work.Charts.BNDataAt R symGeom)
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (E : Work.GCBasics.FPt ((symGeom R.g).S) L) {F : Type u} [Field F] [Algebra K F]
    (ε : L →ₐ[K] F) (Dp : Work.GCBasics.FPt ((symGeom R.g).S) F)
    (h : Work.GCBasics.RPt.LandsIn Dp (Work.Charts.omegaOpen R symGeom D G E a d)) :
    Work.GCBasics.RPt.LandsIn
      (Work.Domain.Resid.addMor symGeom D.addMap Dp (Work.GCBasics.RPt.map ε E))
      (Work.Charts.Wp R symGeom D G a d) := by
  set q : FPt (bcSch ((symGeom R.g).S) L) F := bcLift ((symGeom R.g).S) L ε Dp with hq
  have hqf : q ≫ bcFst ((symGeom R.g).S) L = Dp := by
    rw [hq]; exact bcLift_fst _ _ ε Dp
  have hqs : q ≫ bcSnd ((symGeom R.g).S) L = specOfMap (K := K) ε := by
    rw [hq]; exact bcLift_snd _ _ ε Dp
  have hkey : q ≫ addCentre R symGeom D E =
      Work.Domain.Resid.addMor symGeom D.addMap Dp (RPt.map ε E) := by
    rw [addCentre, addMor_comp, hqf, ← Category.assoc, hqs]
    rfl
  have hmem : RPt.LandsIn q
      ((bcFst ((symGeom R.g).S) L).left ⁻¹ᵁ (omegaOpen R symGeom D G E a d)) :=
    (RPt.landsIn_preimage q (bcFst ((symGeom R.g).S) L) _).mp (by rw [hqf]; exact h)
  have hstep : RPt.LandsIn q
      ((addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d)) :=
    RPt.LandsIn.mono q (preimage_omegaOpen_le_preimage_Wp R symGeom D G a d E) hmem
  rw [← hkey]
  exact (RPt.landsIn_preimage q (addCentre R symGeom D E) _).mpr hstep

end

end Work.Charts
