import Mathlib
import Submission.Work.GCBasics.Basic
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.FinBC
import Submission.Work.Charts.addMor_landsIn_Wp_of_landsIn_omega
import Submission.Work.Domain.Resid.exists_resPt_factor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

open CategoryTheory in
theorem mem_omegaOpen_of_landsIn_step3U {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g) (G : Work.Charts.Step3Geo R symGeom)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : Work.Charts.BNDataAt R symGeom) (x : ((symGeom R.g).S).left)
    [hx : FiniteDimensional K (Work.GCBasics.resField ((symGeom R.g).S) x)]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    (E : Work.GCBasics.FPt ((symGeom R.g).S) L)
    (hE : Work.GCBasics.RPt.LandsIn E (Work.Charts.step3U R symGeom D G x a d)) :
    x ∈ Work.Charts.omegaOpen R symGeom D G E a d := by
  haveI : IsIntegral ((symGeom R.g).S).left := G.integral_g
  -- Unfold the goal
  change x ∉ (bcFst ((symGeom R.g).S) L).left.base ''
      ((((addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d)) : Set _)ᶜ)
  rintro ⟨y, hyWp, hyx⟩
  have hyWp' : (addCentre R symGeom D E).left y ∉ (Wp R symGeom D G a d : Set _) := hyWp
  -- Unfold `hE`
  have hE' : E.left (IsLocalRing.closedPoint L) ∉
      (bcFst ((symGeom R.g).S) (Work.GCBasics.resField ((symGeom R.g).S) x)).left.base ''
        (step3Z R symGeom D G x a d) := by
    have h : E.left (IsLocalRing.closedPoint L) ∈
        (step3U R symGeom D G x a d : Set ((symGeom R.g).S).left) := hE
    rwa [show (step3U R symGeom D G x a d : Set ((symGeom R.g).S).left) =
        ((bcFst ((symGeom R.g).S) (Work.GCBasics.resField ((symGeom R.g).S) x)).left.base ''
          (step3Z R symGeom D G x a d))ᶜ from rfl, Set.mem_compl_iff] at h

  let Ly := Work.GCBasics.resField (bcSch ((symGeom R.g).S) L) y
  let yL : Work.GCBasics.FPt (bcSch ((symGeom R.g).S) L) Ly :=
    Work.GCBasics.resPt (bcSch ((symGeom R.g).S) L) y
  have hyL_pt : yL.left (IsLocalRing.closedPoint Ly) = y :=
    Work.GCBasics.resPt_apply (bcSch ((symGeom R.g).S) L) y _
  have hyL_fst : (yL ≫ bcFst ((symGeom R.g).S) L).left (IsLocalRing.closedPoint Ly) = x := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hyL_pt, hyx]
  obtain ⟨φ, hφ⟩ := Work.Domain.Resid.exists_resPt_factor (X := (symGeom R.g).S) x
      (F := Ly) (yL ≫ bcFst ((symGeom R.g).S) L) hyL_fst
  let b : Work.GCBasics.FPt (Work.GCBasics.specOf K L) Ly := yL ≫ bcSnd ((symGeom R.g).S) L
  let κ := Work.GCBasics.resField ((symGeom R.g).S) x
  let u : Work.GCBasics.FPt (bcSch ((symGeom R.g).S) κ) Ly :=
    bcLift ((symGeom R.g).S) κ φ (b ≫ E)
  have hu_fst : u ≫ bcFst ((symGeom R.g).S) κ = b ≫ E := bcLift_fst _ _ φ _
  have hu_snd : u ≫ bcSnd ((symGeom R.g).S) κ = Work.GCBasics.specOfMap (K := K) φ :=
    bcLift_snd _ _ φ _

  have h1 : u ≫ step3b R symGeom D x =
      Work.Domain.Resid.addMor symGeom D.addMap
        (Work.GCBasics.RPt.map φ (Work.GCBasics.resPt ((symGeom R.g).S) x)) (b ≫ E) := by
    rw [step3b, addMor_comp]
    rw [show u ≫ (bcSnd ((symGeom R.g).S) κ ≫ Work.GCBasics.resPt ((symGeom R.g).S) x)
        = Work.GCBasics.RPt.map φ (Work.GCBasics.resPt ((symGeom R.g).S) x) from by
      rw [← Category.assoc, hu_snd]; rfl]
    rw [hu_fst]
  have h2 : yL ≫ addCentre R symGeom D E =
      Work.Domain.Resid.addMor symGeom D.addMap
        (Work.GCBasics.RPt.map φ (Work.GCBasics.resPt ((symGeom R.g).S) x)) (b ≫ E) := by
    rw [addCentre, addMor_comp, hφ]
    simp only [b, Category.assoc]
  have hkey : u ≫ step3b R symGeom D x = yL ≫ addCentre R symGeom D E := by
    rw [h1, h2]

  have hnotZ : u.left (IsLocalRing.closedPoint Ly) ∉ step3Z R symGeom D G x a d := by
    intro huz
    apply hE'
    refine ⟨u.left (IsLocalRing.closedPoint Ly), huz, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hu_fst, Over.comp_left, Scheme.Hom.comp_apply]
    have hb : b.left (IsLocalRing.closedPoint Ly) = IsLocalRing.closedPoint L := by
      haveI : Subsingleton ↥(Over.left (Work.GCBasics.specOf K L)) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum L))
      exact Subsingleton.elim _ _
    rw [hb]
  have hWp : (step3b R symGeom D x).left (u.left (IsLocalRing.closedPoint Ly)) ∈
      (Wp R symGeom D G a d : Set ((symGeom (R.g + R.g)).S).left) := by
    have h := hnotZ
    rw [mem_step3Z] at h
    exact not_not.mp h
  have hWp' : (step3b R symGeom D x).left (u.left (IsLocalRing.closedPoint Ly)) ∉
      (Wp R symGeom D G a d : Set ((symGeom (R.g + R.g)).S).left) := by
    have heq : (step3b R symGeom D x).left (u.left (IsLocalRing.closedPoint Ly)) =
        (addCentre R symGeom D E).left y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hkey, Over.comp_left,
        Scheme.Hom.comp_apply, hyL_pt]
    rw [heq]
    exact hyWp'
  exact hWp' hWp


end

end Work.Charts
