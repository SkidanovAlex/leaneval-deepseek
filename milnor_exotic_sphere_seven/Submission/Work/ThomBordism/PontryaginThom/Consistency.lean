import Submission.Work.ThomBordism.PontryaginThom.Geometry
import Submission.Work.ThomBordism.PontryaginThom.Torsion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Consistency (non-vacuity) of the interfaces

The structures of this chapter constrain their data (the Whitney relation, the connectedness of `T`,
the torsion-detection property, the pairings); here are checks that the constraints are
*satisfiable*, i.e. that no interface is contradictory:

* `NormalBundlData.nonempty` — for every closed oriented smooth `8`-manifold `V` the normal
  Pontryagin classes with the Whitney relation exist: `q₁ = -p₁`, `q₂ = p₁² - p₂` satisfy the two
  equations identically, so the `normal` field of `PTRep` is never the obstruction.
* `ThomTarget.nonempty_pt` — a `ThomTarget k` exists: the degenerate case of the one-point space
  with the two zero classes (trivial homotopy groups, vanishing homology).  The intended instance is
  of course the tautological Thom space (`GrassmannBridge.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open TensorProduct
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- **The normal-bundle data always exist**: taking `q₁ = -p₁` and `q₂ = p₁² - p₂` makes the two
Whitney equations hold identically, so no manifold is excluded by the `NormalBundlData` fields. -/
theorem NormalBundlData.nonempty (V : Man8) : Nonempty (NormalBundlData V) :=
  ⟨{ q1 := -V.p1
     q2 := cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 V.p1 V.p1 - V.p2
     whitney4 := by simp
     whitney8 := by
       rw [map_neg, LinearMap.neg_apply]
       abel }⟩

/-- Homotopy groups of a subsingleton space are subsingletons. -/
theorem subsingleton_homotopyGroup_punit (i : ℕ) (x : PUnit) :
    Subsingleton (HomotopyGroup (Fin i) PUnit x) := by
  have hgen : Subsingleton (GenLoop (Fin i) PUnit x) :=
    ⟨fun p q => Subtype.ext (ContinuousMap.ext fun a => Subsingleton.elim _ _)⟩
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound (by
        obtain rfl : p = q := Subsingleton.elim p q
        exact Setoid.refl _)

/-- **A `ThomTarget` exists**: the one-point space with the two zero classes.  This is the degenerate
instance showing that the interface of the Grassmann chapter is consistent. -/
theorem ThomTarget.nonempty_pt (k : ℕ) : Nonempty (ThomTarget k) :=
  ⟨{ T := PUnit, t₀ := PUnit.unit, p1sqU := 0, p2U := 0
     connected := fun i _ => subsingleton_homotopyGroup_punit i PUnit.unit
     detects_torsion := fun y _ _ => by
       have hzero : CategoryTheory.Limits.IsZero
           ((chainC ℤ (ssetOf PUnit)).homology (k + 8)) :=
         Work.Cohomology.homologyContractible (X := TopCat.of PUnit) (k + 8) (by omega)
       have h1 : (𝟙 ((chainC ℤ (ssetOf PUnit)).homology (k + 8))) = 0 :=
         hzero.eq_zero_of_tgt _
       have h2 : (𝟙 ((chainC ℤ (ssetOf PUnit)).homology (k + 8))).hom y
           = (0 : ((chainC ℤ (ssetOf PUnit)).homology (k + 8)) ⟶ _).hom y := by rw [h1]
       have hy : y = 0 := by simpa using h2
       exact ⟨1, one_pos, by simp [hy]⟩ }⟩

/-- **The rational detection hypothesis is satisfiable**: on the one-point space there is nothing to
detect, `H_{k+8}(pt;ℤ) = 0`.  (This is the hypothesis of `ThomTarget.ofRationally`; the instance
shows that the constructor and the definition `ThomTarget.detects_rationally` are not vacuous.) -/
theorem detects_rationally_punit (k : ℕ) :
    ∀ y : (chainC ℤ (ssetOf PUnit)).homology (k + 8),
      kronH ℤ (ssetOf PUnit) (k + 8) (0 : (cochainC ℤ (ssetOf PUnit)).homology (k + 8)) y = 0 →
      kronH ℤ (ssetOf PUnit) (k + 8) (0 : (cochainC ℤ (ssetOf PUnit)).homology (k + 8)) y = 0 →
      y ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  intro y _ _
  have hzero : CategoryTheory.Limits.IsZero
      ((chainC ℤ (ssetOf PUnit)).homology (k + 8)) :=
    Work.Cohomology.homologyContractible (X := TopCat.of PUnit) (k + 8) (by omega)
  have h1 : (𝟙 ((chainC ℤ (ssetOf PUnit)).homology (k + 8))) = 0 :=
    hzero.eq_zero_of_tgt _
  have h2 : (𝟙 ((chainC ℤ (ssetOf PUnit)).homology (k + 8))).hom y
      = (0 : ((chainC ℤ (ssetOf PUnit)).homology (k + 8)) ⟶ _).hom y := by rw [h1]
  have hy : y = 0 := by simpa using h2
  rw [hy]
  simp

end

end Work.ThomBordism.PontryaginThom
