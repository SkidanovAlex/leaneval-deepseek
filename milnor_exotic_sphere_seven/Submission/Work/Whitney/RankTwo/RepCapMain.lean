import Mathlib
import Submission.Work.Whitney.RankTwo.RepCapAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- The plain-cochain form of a relative cocycle condition. -/
theorem cochainDiff_of_relDiffLM {X : TopCat} (A : Set X) {n : ℕ}
    (a : ↥(relKern ℤ X A n)) (h : relDiffLM ℤ X A n a = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj X) a.1 = 0 := by
  have hh := congrArg Subtype.val h
  simp only [relDiffLM_coe, Submodule.coe_zero] at hh
  rwa [singularCochain_d_apply ℤ X a.1] at hh

/-- **The cap comparison.**  For a relative representative `ψ` of `stepSph Y 1 (Mn 1 Y)`, the
pullback of its underlying cochain along the cap map differs from the explicit cocycle `eta` by a
coboundary of a *relative* `0`-cochain of the disc pair. -/
theorem cap_rep_eq_eta
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψcoc : relDiffLM ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 ψ = 0)
    (hψclass : relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψcoc
      = stepSph Y 1 (Mn 1 Y)) :
    ∃ h : ↥(relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 0),
      pullCM (capMapPairSph Y 1) ψ.1 - eta Y
        = cochainDiff ℤ (ssBall Y) h.1 := by
  let Ψ : ↥(relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1) :=
    relMapLM (X₁ := TopCat.of (BBall Y)) (X₂ := TopCat.of (Y × MSph 2))
      ℤ (DiscB Y 1) (SphB Y 1) (TopCat.ofHom (capMapPairSph Y 1))
      (fun x hx => CleanA.capMapPairSph_mem_mLower 1 x hx) 1 ψ
  have hcocB : relDiffLM ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1 Ψ = 0 :=
    relDiffLM_relMapLM (X₁ := TopCat.of (BBall Y)) (X₂ := TopCat.of (Y × MSph 2))
      ℤ (DiscB Y 1) (SphB Y 1) (TopCat.ofHom (capMapPairSph Y 1))
      (fun x hx => CleanA.capMapPairSph_mem_mLower 1 x hx) ψ hψcoc
  have hclassB : relClassOf ℤ (TopCat.of (BBall Y)) (DiscB Y 1) Ψ hcocB
      = stepDisc Y 1 (Mn 1 Y) := by
    have h := homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of (BBall Y)) (X₂ := TopCat.of (Y × MSph 2))
      (A₁ := DiscB Y 1) (A₂ := SphB Y 1)
      (f := TopCat.ofHom (capMapPairSph Y 1))
      (h := fun x hx => CleanA.capMapPairSph_mem_mLower 1 x hx) (n := 1) ψ hψcoc
    rw [hψclass] at h
    have hspec : (relCohMap (capMapPairSph Y 1) (DiscB Y 1) (SphB Y 1)
        (fun x hx => CleanA.capMapPairSph_mem_mLower 1 x hx) ℤ 1).hom (stepSph Y 1 (Mn 1 Y))
        = stepDisc Y 1 (Mn 1 Y) := by
      rw [relCohMap_hcongrA (capMapPairSph Y 1) (DiscB Y 1) (SphB Y 1)
        (fun x hx => CleanA.capMapPairSph_mem_mLower 1 x hx)
        (CleanA.capMapPairSph_mem_mLower 1) ℤ 1]
      exact stepSph_spec Y 1 (Mn 1 Y)
    rw [hspec] at h
    exact h.symm
  obtain ⟨hmem, hcoc, hclass⟩ := eta_class Y
  obtain ⟨v, hv⟩ := relClassOf_coboundary (X := TopCat.of (BBall Y)) (DiscB Y 1) (n := 0)
    Ψ ⟨eta Y, hmem⟩ hcocB hcoc (by rw [hclassB, hclass])
  refine ⟨v, ?_⟩
  have h := congrArg Subtype.val hv
  simp only [relDiffLM_coe, Submodule.coe_sub, relMapLM_coe] at h
  rw [singularCochain_d_apply ℤ (TopCat.of (BBall Y)) v.1] at h
  exact h.symm

end

end Work.Whitney.RankTwo
