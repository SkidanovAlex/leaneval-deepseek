import Mathlib
import Submission.Work.Kunneth.CohKunneth.CtensStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology (dualComplex dualComplexMap Cochain cochainDiff cohomologyClassOf
  cohomologyClassOf_congr)

/-- The differential of the homology complex vanishes on elements. -/
theorem homSum_d_apply_zero (D : ChainComplex (ModuleCat ℤ) ℕ) (q : ℕ)
    (h : ↥(D.homology q)) : ((homSum D).d q (q - 1)).hom h = 0 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [show (homSum D).d 0 (0 - 1) = 0 from HomologicalComplex.shape (homSum D) 0 0
      (by simp [ComplexShape.down]), ModuleCat.hom_zero]
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [show (homSum D).d (m + 1) (m + 1 - 1) = 0 from
      sumShift_d (fun q => D.homology q) m, ModuleCat.hom_zero]
    rfl

variable (D : ChainComplex (ModuleCat ℤ) ℕ) (π : D ⟶ homSum D) (ι : homSum D ⟶ D)

/-- **A section of the homology projection lands in the cycles**, and the resulting cycle
represents the class it came from. -/
theorem iota_section (hιπ : ι ≫ π = 𝟙 (homSum D))
    (hπval : ∀ (q : ℕ) (v : ↥(D.cycles q)),
      (π.f q).hom ((D.iCycles q).hom v) = (D.homologyπ q).hom v)
    (q : ℕ) (h : ↥(D.homology q)) :
    ∃ w : ↥(D.cycles q), (D.iCycles q).hom w = (ι.f q).hom h ∧ (D.homologyπ q).hom w = h := by
  have hcyc : (D.d q (q - 1)).hom ((ι.f q).hom h) = 0 := by
    rw [Hom_comm_apply ι q (q - 1) h, homSum_d_apply_zero D q h, map_zero]
  set w : ↥(D.cycles q) := (cycIso D q).inv.hom ⟨(ι.f q).hom h, hcyc⟩ with hw
  have hval : ((cycIso D q).hom.hom w : ↥(D.X q)) = (ι.f q).hom h := by
    rw [hw]
    exact congrArg (fun z : ↥(cycKer D q) => (z : ↥(D.X q)))
      (homIso_hom_apply (cycIso D q) ⟨(ι.f q).hom h, hcyc⟩)
  have hw1 : (D.iCycles q).hom w = (ι.f q).hom h := (cycIso_hom_val D q w).symm.trans hval
  refine ⟨w, hw1, ?_⟩
  have hπι : (π.f q).hom ((ι.f q).hom h) = h := by
    have hc := congrArg (fun (m : homSum D ⟶ homSum D) => (m.f q).hom) hιπ
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      ModuleCat.hom_id] at hc
    exact congrArg (fun (f : ↥((homSum D).X q) →ₗ[ℤ] ↥((homSum D).X q)) => f h) hc
  rw [← hπval q w, hw1, hπι]

/-- **The dual universal coefficient isomorphism, on the functional given by a section.**
If `e` is a UCT isomorphism sending the class of a cocycle `z` to the functional `c ↦ z(c)`,
then the inverse of `e` sends `β ∘ ι` to the class of `zβ`. -/
theorem uctSymm_apply (hιπ : ι ≫ π = 𝟙 (homSum D))
    (hπval : ∀ (q : ℕ) (v : ↥(D.cycles q)),
      (π.f q).hom ((D.iCycles q).hom v) = (D.homologyπ q).hom v)
    (q : ℕ) (zβ : ↥((dualComplex ℤ D).cycles q))
    (e : (dualComplex ℤ D).homology q ≅ ModuleCat.of ℤ (↥(D.homology q) →ₗ[ℤ] ℤ))
    (he : ∀ (z : ↥((dualComplex ℤ D).cycles q)) (c : ↥(D.cycles q)),
      e.hom.hom (((dualComplex ℤ D).homologyπ q).hom z) ((D.homologyπ q).hom c)
        = (show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom z)
            ((D.iCycles q).hom c)) :
    e.symm.hom.hom
        ((show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ).comp (ι.f q).hom)
      = ((dualComplex ℤ D).homologyπ q).hom zβ := by
  rw [← homIso_inv_apply e (((dualComplex ℤ D).homologyπ q).hom zβ)]
  congr 1
  apply LinearMap.ext
  intro h
  obtain ⟨w, hw1, hw2⟩ := iota_section D π ι hιπ hπval q h
  have hL : (show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ) ((ι.f q) h)
      = (show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ) ((D.iCycles q) w) :=
    congrArg (fun x => (show ↥(D.X q) →ₗ[ℤ] ℤ from
      ((dualComplex ℤ D).iCycles q).hom zβ) x) hw1.symm
  have hR : e.hom.hom (((dualComplex ℤ D).homologyπ q).hom zβ) ((D.homologyπ q).hom w)
      = e.hom.hom (((dualComplex ℤ D).homologyπ q).hom zβ) h :=
    congrArg (fun x => e.hom.hom (((dualComplex ℤ D).homologyπ q).hom zβ) x) hw2
  calc ((show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ).comp
        (ι.f q).hom) h
      = (show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ) ((ι.f q) h) :=
        LinearMap.comp_apply _ _ _
    _ = (show ↥(D.X q) →ₗ[ℤ] ℤ from ((dualComplex ℤ D).iCycles q).hom zβ) ((D.iCycles q) w) := hL
    _ = e.hom.hom (((dualComplex ℤ D).homologyπ q).hom zβ) ((D.homologyπ q).hom w) :=
        (he zβ w).symm
    _ = e.hom.hom (((dualComplex ℤ D).homologyπ q).hom zβ) h := hR

end

end Work.Kunneth
