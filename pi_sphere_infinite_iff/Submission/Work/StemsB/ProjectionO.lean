import Submission.Work.StemsB.ProjLemma

/-!
# The projection lemma with the outer-piece spelling of the collar

The pentagon of `Submission/Work/StemsB/SERRE_PLAN.md` §2 combines the excision (whose relative part
on the total space is written as `p ⁻¹' sphLoopOuter n`), the fibrewise triviality over the inner
cube `sphLoopBig n` and the projection.  For the composite to be a composite of `relChainsMapOf`'s
with *literally matching* relative parts, the projection lemma is needed with the collar of
`↥(sphLoopBig n)` written as `{y | (y : SphModel n) ∈ sphLoopOuter n}` rather than as
`{y | (y : SphModel n) ∈ sphLoopCollar n}`.  The two sets are equal (the first coordinate already
lies in the cube), so this is a re-spelling, but not a definitional one.

This file provides that re-spelling of the projection lemma of `ProjLemma.lean`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB

noncomputable section

/-- The collar cut out by the **outer piece** inside `↥(sphLoopBig n) × Y`.  Equal, as a set, to
`sphLoopCollarProd n Y`. -/
abbrev collarProdO (n : ℕ) (Y : Type) : Set (↥(sphLoopBig n) × Y) :=
  {x | (x.1 : SphModel n) ∈ sphLoopOuter n}

/-- The collar cut out by the **outer piece** inside `↥(sphLoopBig n)`. -/
abbrev collarInG (n : ℕ) : Set ↥(sphLoopBig n) :=
  {y | (y : SphModel n) ∈ sphLoopOuter n}

theorem collarProdO_eq (n : ℕ) (Y : Type) : collarProdO n Y = sphLoopCollarProd n Y := by
  ext x
  exact ⟨fun h => ⟨h, x.1.2⟩, fun h => h.1⟩

/-- The relative Künneth for the re-spelled collar. -/
theorem collarProdO_iso (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (collarProdO n Y)).homology (j + n)) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j) := by
  rw [collarProdO_eq n Y]
  exact serreSphere_collar_iso n hn Y j

/-- The vanishing below the collar dimension, for the re-spelled collar. -/
theorem collarProdO_isZero (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hm : m < n) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
      (collarProdO n Y)).homology m) := by
  rw [collarProdO_eq n Y]
  exact serreSphere_collar_isZero n hn Y m hm

/-! ## The projection and its section, with the outer spelling -/

/-- The restriction of the projection to the re-spelled collar. -/
def sphProjRelHomO (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    TopCat.of ↥(collarProdO n Y) ⟶ TopCat.of ↥(collarProdO n PUnit) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.1, ()), p.2⟩, by
    have hf : Continuous fun p : ↥(collarProdO n Y) => (p.1.1, ()) :=
      Continuous.prodMk (continuous_fst.comp continuous_subtype_val) continuous_const
    exact Continuous.subtype_mk hf (fun p => p.2)⟩

theorem sphProjHom_subtypeInclO (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × Y)) (collarProdO n Y)
        ≫ sphProjHom n Y
      = sphProjRelHomO n Y
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
            (collarProdO n PUnit) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The restriction of the section to the re-spelled collar. -/
def sphProjSecRelO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    TopCat.of ↥(collarProdO n PUnit) ⟶ TopCat.of ↥(collarProdO n Y) :=
  TopCat.ofHom ⟨fun p => ⟨(p.1.1, y₀), p.2⟩, by
    have hf : Continuous fun p : ↥(collarProdO n PUnit) => (p.1.1, y₀) :=
      Continuous.prodMk (continuous_fst.comp continuous_subtype_val) continuous_const
    exact Continuous.subtype_mk hf (fun p => p.2)⟩

theorem sphProjSec_subtypeInclO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
        (collarProdO n PUnit) ≫ sphProjSec n Y y₀
      = sphProjSecRelO n Y y₀
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × Y))
            (collarProdO n Y) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

theorem sphProjSecRelO_comp_projRelHomO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    sphProjSecRelO n Y y₀ ≫ sphProjRelHomO n Y
      = 𝟙 (TopCat.of ↥(collarProdO n PUnit)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

/-! ## The projection lemma with the outer spelling -/

/-- The chain map of relative complexes induced by the projection, with the outer spelling. -/
def sphProjRelMapO (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y)) (collarProdO n Y) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
        (collarProdO n PUnit) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig n) × Y))
    (TopCat.of (↥(sphLoopBig n) × PUnit)) (collarProdO n Y) (collarProdO n PUnit)
    (sphProjHom n Y) (sphProjRelHomO n Y) (sphProjHom_subtypeInclO n Y)

/-- The chain map of relative complexes induced by the section, with the outer spelling. -/
def sphSecRelMapO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit)) (collarProdO n PUnit) ⟶
      Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y)) (collarProdO n Y) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (↥(sphLoopBig n) × PUnit))
    (TopCat.of (↥(sphLoopBig n) × Y)) (collarProdO n PUnit) (collarProdO n Y)
    (sphProjSec n Y y₀) (sphProjSecRelO n Y y₀) (sphProjSec_subtypeInclO n Y y₀)

/-- The compatibility proof of the composite `sec ≫ proj` (outer spelling). -/
theorem sphProjSec_projHom_relO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit)) (collarProdO n PUnit)
        ≫ (sphProjSec n Y y₀ ≫ sphProjHom n Y)
      = (sphProjSecRelO n Y y₀ ≫ sphProjRelHomO n Y)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig n) × PUnit))
            (collarProdO n PUnit) := by
  rw [← Category.assoc, sphProjSec_subtypeInclO, Category.assoc, sphProjHom_subtypeInclO,
    ← Category.assoc]

/-- **The projection is a split epimorphism on relative chain complexes** (outer spelling). -/
theorem sphSecRelMapO_comp_sphProjRelMapO (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    sphSecRelMapO n Y y₀ ≫ sphProjRelMapO n Y
      = 𝟙 (Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (collarProdO n PUnit)) := by
  have h := Work.Cohomology.relChainsMapOf_comp
    (X := TopCat.of (↥(sphLoopBig n) × PUnit))
    (Y := TopCat.of (↥(sphLoopBig n) × Y)) (Z := TopCat.of (↥(sphLoopBig n) × PUnit))
    (A := collarProdO n PUnit) (B := collarProdO n Y) (C := collarProdO n PUnit)
    (f := sphProjSec n Y y₀) (g := sphProjSecRelO n Y y₀)
    (w := sphProjSec_subtypeInclO n Y y₀)
    (f' := sphProjHom n Y) (g' := sphProjRelHomO n Y) (w' := sphProjHom_subtypeInclO n Y)
    (w'' := sphProjSec_projHom_relO n Y y₀)
  rw [sphSecRelMapO, sphProjRelMapO, h]
  rw [relChainsMapOf_congr (A := collarProdO n PUnit) (B := collarProdO n PUnit)
    (f := sphProjSec n Y y₀ ≫ sphProjHom n Y)
    (g := sphProjSecRelO n Y y₀ ≫ sphProjRelHomO n Y) (f' := 𝟙 _) (g' := 𝟙 _)
    (sphProjSec_comp_projHom n Y y₀) (sphProjSecRelO_comp_projRelHomO n Y y₀)
    (w' := by rw [Category.id_comp, Category.comp_id])]
  exact relChainsMapOf_id _ _ _

/-- The collar isomorphism in the degree-shifted form used in the middle degree. -/
theorem collarIsoAtO (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] (k : ℕ) (h : n ≤ k) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (collarProdO n Y)).homology k) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology (k - n)) := by
  obtain ⟨e⟩ := collarProdO_iso n hn Y (k - n)
  exact ⟨homologyCongr (C := Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
      (collarProdO n Y)) (i := k) (j := k - n + n) (Nat.sub_add_cancel h).symm ≪≫ e⟩

/-- **The projection lemma with the outer spelling.**  The projection `(q, y) ↦ (q, ())` induces an
isomorphism on relative homology in degrees `k < n + f`. -/
theorem sphProjRelMapO_isIso (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y]
    (f : ℕ) (hY0 : Nonempty Y)
    (hY : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j))
    (hH0 : Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology 0) ≃ₗ[ℤ] ℤ))
    (k : ℕ) (hk : k < n + f) :
    IsIso (HomologicalComplex.homologyMap (sphProjRelMapO n Y) k) := by
  rcases lt_or_ge k n with hklt | hkle
  · have hS : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
        (collarProdO n Y)).homology k) := collarProdO_isZero n hn Y k hklt
    have hT : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
        (collarProdO n PUnit)).homology k) := collarProdO_isZero n hn PUnit k hklt
    exact isIso_of_isZero_of_isZero hS hT
  · rcases lt_or_eq_of_le hkle with hkgt | hkeq
    · have hj0 : 0 < k - n := Nat.sub_pos_of_lt hkgt
      have hjf : k - n < f := by omega
      obtain ⟨e⟩ := collarIsoAtO n hn Y k hkle
      have hS : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
          (collarProdO n Y)).homology k) := IsZero.of_iso (hY (k - n) hj0 hjf) e
      obtain ⟨e'⟩ := collarIsoAtO n hn PUnit k hkle
      have hT : IsZero ((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (collarProdO n PUnit)).homology k) :=
        IsZero.of_iso (isZero_homology_punit (k - n) hj0) e'
      exact isIso_of_isZero_of_isZero hS hT
    · subst hkeq
      obtain ⟨y₀⟩ := hY0
      have hsplit : HomologicalComplex.homologyMap (sphSecRelMapO n Y y₀) n
            ≫ HomologicalComplex.homologyMap (sphProjRelMapO n Y) n = 𝟙 _ := by
        rw [← HomologicalComplex.homologyMap_comp, sphSecRelMapO_comp_sphProjRelMapO n Y y₀,
          HomologicalComplex.homologyMap_id]
      have hsurj : Function.Surjective
          ((HomologicalComplex.homologyMap (sphProjRelMapO n Y) n).hom : _ → _) := by
        intro b
        refine ⟨(HomologicalComplex.homologyMap (sphSecRelMapO n Y y₀) n) b, ?_⟩
        have h := congrArg (fun φ => φ b) hsplit
        simpa [ModuleCat.comp_apply] using h
      have hM : Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × Y))
          (collarProdO n Y)).homology n) ≃ₗ[ℤ] ℤ) := by
        obtain ⟨e⟩ := collarIsoAtO n hn Y n le_rfl
        obtain ⟨e0⟩ := hH0
        exact ⟨(Work.Cohomology.uctIsoToLinearEquiv
          (e ≪≫ homologyCongr (C := Work.Cohomology.singularChains ℤ (TopCat.of Y))
            (Nat.sub_self n))).trans e0⟩
      have hN : Nonempty (((Work.Cohomology.relChains (TopCat.of (↥(sphLoopBig n) × PUnit))
          (collarProdO n PUnit)).homology n) ≃ₗ[ℤ] ℤ) := by
        obtain ⟨e⟩ := collarIsoAtO n hn PUnit n le_rfl
        obtain ⟨e0⟩ := nonempty_homology_zero_punit_linEquiv
        exact ⟨(Work.Cohomology.uctIsoToLinearEquiv
          (e ≪≫ homologyCongr (C := Work.Cohomology.singularChains ℤ (TopCat.of PUnit))
            (Nat.sub_self n))).trans e0⟩
      refine (ConcreteCategory.isIso_iff_bijective
        (HomologicalComplex.homologyMap (sphProjRelMapO n Y) n)).mpr ?_
      exact bijective_of_surjective_of_int_iso hM hN
        (HomologicalComplex.homologyMap (sphProjRelMapO n Y) n).hom hsurj

end

end Work.StemsB
