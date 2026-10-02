import Submission.Work.StemsB.SphZeroDecomp
import Submission.Work.Thom.ModelThomDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `S⁰`-decomposition of the subspace `{p : B × ℝ¹ | p.2 ∈ S⁰}`

`Work.StemsB.coh_S0_decomp` decomposes the cohomology of the *product of subtypes*
`B × ↥(sphSet 1)`.  The rank-one model Thom class (`Work.Thom.ModelThom B 1`) lives on the *pair*
`(B × ℝ¹, {p : B × ℝ¹ | p.2 ∈ S⁰})`, where the sphere direction is a *subspace* of
`EuclideanSpace ℝ (Fin 1)` rather than a factor.

This file transports the decomposition along the canonical homeomorphism
`Work.Thom.prodSubsetHomeo : B × ↥S⁰ ≃ₜ {p : B × ℝ¹ | p.2 ∈ S⁰}` and records the two facts the
rank-one Thom argument uses:

* the two components of the decomposition are the pullbacks along the two sections
  `b ↦ (b, 1)`, `b ↦ (b, −1)` of `{p | p.2 ∈ S⁰} → B` (`coh_S0_subspace_fst`, `..._snd`);
* the restriction `H^k(B × ℝ¹) → H^k({p | p.2 ∈ S⁰})`, composed with the decomposition, is the
  *diagonal* (`restr_coh_S0_subspace`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial Topology

namespace Work.StemsB

noncomputable section

variable {B : Type} [TopologicalSpace B]

abbrev Euc1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The space `B × ℝ¹`. -/
abbrev Xone (B : Type) [TopologicalSpace B] : TopCat := TopCat.of (B × Euc1)

/-- The subspace `S⁰ ⊆ B × ℝ¹`. -/
abbrev Aone (B : Type) [TopologicalSpace B] : Set (B × Euc1) := {p | p.2 ∈ sphSet 1}

/-- The canonical homeomorphism `B × ↥S⁰ ≃ₜ ↥(Aone B)`. -/
def hSubsetHomeo (B : Type) [TopologicalSpace B] :
    TopCat.of (B × ↥(sphSet 1)) ≃ₜ TopCat.of ↥(Aone B) :=
  Work.Thom.prodSubsetHomeo B Euc1 (sphSet 1)

/-- The canonical homeomorphism, as a morphism of `TopCat`. -/
noncomputable abbrev hSubset (B : Type) [TopologicalSpace B] :
    TopCat.of (B × ↥(sphSet 1)) ⟶ TopCat.of ↥(Aone B) :=
  TopCat.ofHom (hSubsetHomeo B)

/-- A homeomorphism of spaces induces an isomorphism on singular cohomology (in the contravariant
direction: `H^n(Y) ≅ H^n(X)` for `e : X ≃ₜ Y`). -/
noncomputable abbrev cohomologyIsoOfHomeomorph (R : Type) [CommRing R] {X Y : TopCat}
    (e : X ≃ₜ Y) (n : ℕ) : singularCohomology R n Y ≅ singularCohomology R n X :=
  letI : IsIso (singularCohomologyMap R X Y (TopCat.ofHom e) n) :=
    homotopyEquiv R X Y (TopCat.ofHom e) (TopCat.ofHom e.symm)
      e.toHomotopyEquiv.left_inv.some e.toHomotopyEquiv.right_inv.some n
  asIso (singularCohomologyMap R X Y (TopCat.ofHom e) n)

theorem cohomologyIsoOfHomeomorph_hom (R : Type) [CommRing R] {X Y : TopCat}
    (e : X ≃ₜ Y) (n : ℕ) :
    (cohomologyIsoOfHomeomorph R e n).hom
      = singularCohomologyMap R X Y (TopCat.ofHom e) n := rfl

/-- The projection `↥(Aone B) → B`. -/
def aProj (B : Type) [TopologicalSpace B] : TopCat.of ↥(Aone B) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun q => q.1.1, by fun_prop⟩

/-- The section `b ↦ (b, 1)`. -/
def aSec₁ (B : Type) [TopologicalSpace B] : TopCat.of B ⟶ TopCat.of ↥(Aone B) :=
  TopCat.ofHom ⟨fun b => ⟨(b, (s0N : ↥(sphSet 1)).1), (s0N : ↥(sphSet 1)).2⟩, by fun_prop⟩

/-- The section `b ↦ (b, −1)`. -/
def aSec₂ (B : Type) [TopologicalSpace B] : TopCat.of B ⟶ TopCat.of ↥(Aone B) :=
  TopCat.ofHom ⟨fun b => ⟨(b, (s0S : ↥(sphSet 1)).1), (s0S : ↥(sphSet 1)).2⟩, by fun_prop⟩

/-- The inclusion `↥(Aone B) ⊆ B × ℝ¹`. -/
def aIncl (B : Type) [TopologicalSpace B] : TopCat.of ↥(Aone B) ⟶ Xone B :=
  subtypeIncl (TopCat.of (B × Euc1)) (Aone B)

/-- The projection `B × ℝ¹ → B`. -/
def xProj (B : Type) [TopologicalSpace B] : Xone B ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- **The `S⁰`-decomposition of the subspace `{p : B × ℝ¹ | p.2 ∈ S⁰}`**, with the two components
identified with the pullbacks along the two sections. -/
noncomputable abbrev cohAoneIso (k : ℕ) :
    singularCohomology ℚ k (TopCat.of ↥(Aone B)) ≅
      singularCohomology ℚ k (TopCat.of B) ⊞ singularCohomology ℚ k (TopCat.of B) :=
  cohomologyIsoOfHomeomorph ℚ (hSubsetHomeo B) k ≪≫ cohS0Iso (R := ℚ) (Y := B) k

theorem cohAoneIso_fst (k : ℕ) :
    (cohAoneIso (B := B) k).hom ≫ biprod.fst
      = singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₁ B) k := by
  have hcomp : (cohAoneIso (B := B) k).hom
      = singularCohomologyMap ℚ (TopCat.of (B × ↥(sphSet 1))) (TopCat.of ↥(Aone B))
          (hSubset B) k ≫ (cohS0Iso (R := ℚ) (Y := B) k).hom := rfl
  rw [hcomp, Category.assoc, cohS0Iso_hom_fst,
    ← singularCohomologyMap_comp (R := ℚ) (X := TopCat.of B)
      (Y := TopCat.of (B × ↥(sphSet 1))) (Z := TopCat.of ↥(Aone B)) (ySec₁ (Y := B))
      (hSubset B) k]
  congr 1

theorem cohAoneIso_snd (k : ℕ) :
    (cohAoneIso (B := B) k).hom ≫ biprod.snd
      = singularCohomologyMap ℚ (TopCat.of B) (TopCat.of ↥(Aone B)) (aSec₂ B) k := by
  have hcomp : (cohAoneIso (B := B) k).hom
      = singularCohomologyMap ℚ (TopCat.of (B × ↥(sphSet 1))) (TopCat.of ↥(Aone B))
          (hSubset B) k ≫ (cohS0Iso (R := ℚ) (Y := B) k).hom := rfl
  rw [hcomp, Category.assoc, cohS0Iso_hom_snd,
    ← singularCohomologyMap_comp (R := ℚ) (X := TopCat.of B)
      (Y := TopCat.of (B × ↥(sphSet 1))) (Z := TopCat.of ↥(Aone B)) (ySec₂ (Y := B))
      (hSubset B) k]
  congr 1


/-- The projection `B × ℝ¹ → B` is a homotopy equivalence, hence its pullback on cohomology is an
isomorphism. -/
theorem isIso_xProj_pullback (k : ℕ) :
    IsIso (singularCohomologyMap ℚ (Xone B) (TopCat.of B) (xProj B) k) := by
  refine homotopyEquiv ℚ (Xone B) (TopCat.of B) (xProj B)
    (TopCat.ofHom ⟨fun b => (b, (0 : Euc1)), by fun_prop⟩) ?_ ?_ k
  · refine (ContinuousMap.Homotopy.mk
      ⟨fun z : unitInterval × (B × Euc1) => (z.2.1, ((1 : ℝ) - (z.1 : ℝ)) • z.2.2),
        by fun_prop⟩
      (fun x => by simp) (fun x => by simp [xProj])).symm
  · have h : (TopCat.ofHom ⟨fun b => (b, (0 : Euc1)), by fun_prop⟩ : TopCat.of B ⟶ Xone B)
        ≫ xProj B = 𝟙 (TopCat.of B) := by
      apply TopCat.hom_ext; ext b; rfl
    rw [h]
    exact ContinuousMap.Homotopy.refl _

/-- **The restriction `H^k(B × ℝ¹) → H^k(S⁰-subspace)`, composed with the decomposition, is the
diagonal** `x ↦ x ⊞ x`, the total space being identified with `B` through the homotopy equivalence
`B × ℝ¹ → B` (in the equivalent "multiplied" form, which avoids exhibiting the inverse). -/
theorem xProj_restr_cohAoneIso (k : ℕ) :
    singularCohomologyMap ℚ (Xone B) (TopCat.of B) (xProj B) k
        ≫ (singularCohomologyMap ℚ (TopCat.of ↥(Aone B)) (Xone B) (aIncl B) k
            ≫ (cohAoneIso (B := B) k).hom)
      = biprod.lift (𝟙 (singularCohomology ℚ k (TopCat.of B)))
          (𝟙 (singularCohomology ℚ k (TopCat.of B))) := by
  have hyProj2 : (hSubset B ≫ aIncl B) ≫ xProj B = yProj (Y := B) := by
    apply TopCat.hom_ext; ext q; rfl
  have hcomb : (singularCohomologyMap ℚ (Xone B) (TopCat.of B) (xProj B) k
        ≫ singularCohomologyMap ℚ (TopCat.of ↥(Aone B)) (Xone B) (aIncl B) k)
      ≫ singularCohomologyMap ℚ (TopCat.of (B × ↥(sphSet 1))) (TopCat.of ↥(Aone B)) (hSubset B) k
      = singularCohomologyMap ℚ (TopCat.of (B × ↥(sphSet 1))) (TopCat.of B) (yProj (Y := B)) k := by
    rw [Category.assoc, ← singularCohomologyMap_comp (R := ℚ) (hSubset B) (aIncl B) k]
    rw [← singularCohomologyMap_comp (R := ℚ) (hSubset B ≫ aIncl B) (xProj B) k, hyProj2]
  simp only [cohAoneIso, cohomologyIsoOfHomeomorph, Iso.trans_hom, CategoryTheory.asIso_hom]
  rw [← Category.assoc, ← Category.assoc, hcomb, cohS0Iso_yProj]

end

end Work.StemsB
