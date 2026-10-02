import Mathlib
import Submission.Work.Serre.MVShift.HonestCup
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Serre.MVGlue.mvSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology map of the honest cup is the mixed cup

`Work.Serre.cupRelChain Y B n₀ t ht` is the honest chain map `ψ ↦ ψ ⌣ t` from the absolute
cochains of `Y` to the relative cochains of `(Y,B)`, *shifted* by `n₀`.  This file identifies its
effect on cohomology:

  `H(cupRelChain) ≫ shK_homologyIso = relToAbs ≫ (mixed cup with [t])`,

i.e. the induced map `H^j(Y;ℚ) → H^{j+n₀}(Y,B;ℚ)` is the mixed cup product with the class of the
relative cocycle `t`.  This is the first clause of `Work.Serre.MVGlue.honestCupMorphism`.

## The proof

Every cohomology class of `(Y,∅)` is the class of a relative cocycle `a`
(`Work.Cohomology.exists_relClassOf`), so it suffices to evaluate both sides there.

* *Right hand side.*  `relToAbs` sends the class of `a` to the absolute class of the underlying
  cochain `a.1` (`Work.Cohomology.relIncl_homologyMap_relClassOf`), and the mixed cup with the
  class of `t` is computed by the defining rule of `Work.Cohomology.mixedRelCupH`: it is the class
  of the Alexander–Whitney product `a.1 ⌣ t.1`.
* *Left hand side.*  We push `a` through `homologyMap cupRelChain` (`homologyπ_naturality`, so the
  cycle `relCocycleOf a` is sent to `iCycles ((cupRelLM …) a)`), and then through the degree-shift
  comparison `shK_homologyIso`.  The two technical inputs are

  - `shK_homologyIso_comp_homologyπ`: on cycles of the shift, `shK_homologyIso` is the composition
    of the *cycle* comparison `shK_cyclesIso` with the class map of the unshifted complex (this is
    Mathlib's `homologyπ_restrictionHomologyIso_hom`, exposed at the degrees of `shEmb n₀`),
  - `shK_cyclesIso_cyclesMap_iCycles`: `shK_cyclesIso` sends the `iCycles`-image of a pushed cycle
    to the `iCycles`-image of the pushed cochain (Mathlib's `restrictionCyclesIso_hom_iCycles`
    plus `cyclesMap_i`; the `restrictionXIso`-cast is trivial at `shEmb`).

  Combining, the left hand side is the class of a cycle whose underlying cochain is
  `(cupRelLM Y B n₀ t j) a = mixedRelStar a.1 t`, i.e. exactly the Alexander–Whitney product
  `a.1 ⌣ t.1` (whose cocycle condition is the Leibniz rule
  `Work.Cohomology.mstar_cocycle_cochain`).  This is the same class as on the right.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre.DiscPair

noncomputable section

open Work.Cohomology

/-! ## Exposing the definitions of the degree-shift comparisons

`shK_homologyIso` and `shK_cyclesIso` are defined as particular instances of Mathlib's
`restrictionHomologyIso` / `restrictionCyclesIso` for the shape embedding `shEmb n₀`.  The
following `rfl`-lemmas exhibit those instances (with the degrees made explicit), so that the
general Mathlib API applies to them. -/

/-- `shK_homologyIso` is Mathlib's `restrictionHomologyIso` for the shape embedding `shEmb p`. -/
theorem shK_homologyIso_hom_eq (K : CochainComplex (ModuleCat ℚ) ℕ) (p k : ℕ) (hk : 1 ≤ k) :
    (MVShift.shK_homologyIso K p k hk).hom =
      (K.restrictionHomologyIso (MVShift.shEmb p) (k - 1) k (k + 1)
        (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (k - 1) k from by
          change (k - 1) + 1 = k; omega))
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl))
        (by change k - 1 + p = k + p - 1; omega)
        (by change k + p = k + p; rfl)
        (by change k + 1 + p = k + 1 + p; rfl)
        (by change (ComplexShape.up ℕ).prev (k + p) = k + p - 1
            exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (k + p - 1) (k + p) from by
              change (k + p - 1) + 1 = k + p; omega))
        (by change (ComplexShape.up ℕ).next (k + p) = k + 1 + p
            exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (k + p) (k + 1 + p) from by
              change k + p + 1 = k + 1 + p; omega))).hom := rfl

/-- `shK_cyclesIso` is Mathlib's `restrictionCyclesIso` for the shape embedding `shEmb p`. -/
theorem shK_cyclesIso_hom_eq (K : CochainComplex (ModuleCat ℚ) ℕ) (p k : ℕ) :
    (MVShift.shK_cyclesIso K p k).hom =
      (K.restrictionCyclesIso (MVShift.shEmb p) k (k + 1)
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl))
        (by change (k : ℕ) + p = k + p; rfl)
        (by change (k + 1) + p = (k + 1) + p; rfl)
        (by change (ComplexShape.up ℕ).next (k + p) = (k + 1) + p
            exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (k + p) ((k + 1) + p) from by
              change k + p + 1 = (k + 1) + p; omega))).hom := rfl

/-! ## The two computation rules for the degree-shift comparison -/

/-- **`shK_homologyIso` is the cycle comparison followed by the class map.**  On cycles of the
shift, the homology comparison of the degree shift `k ↦ k + p` is Mathlib's cycle comparison
`shK_cyclesIso` followed by the class map of the unshifted complex. -/
theorem shK_homologyIso_comp_homologyπ (K : CochainComplex (ModuleCat ℚ) ℕ) (p k : ℕ) (hk : 1 ≤ k) :
    CategoryTheory.CategoryStruct.comp ((MVShift.shK K p).homologyπ k)
        (MVShift.shK_homologyIso K p k hk).hom
      = CategoryTheory.CategoryStruct.comp (MVShift.shK_cyclesIso K p k).hom
          (K.homologyπ (k + p)) := by
  rw [shK_homologyIso_hom_eq K p k hk]
  rw [HomologicalComplex.homologyπ_restrictionHomologyIso_hom]
  rw [shK_cyclesIso_hom_eq K p k]

/-- The elementwise form of `shK_homologyIso_comp_homologyπ`. -/
theorem shK_homologyIso_homologyπ_apply (K : CochainComplex (ModuleCat ℚ) ℕ) (p k : ℕ) (hk : 1 ≤ k)
    (w : (MVShift.shK K p).cycles k) :
    (MVShift.shK_homologyIso K p k hk).hom (((MVShift.shK K p).homologyπ k).hom w)
      = (K.homologyπ (k + p)).hom ((MVShift.shK_cyclesIso K p k).hom w) := by
  have h := shK_homologyIso_comp_homologyπ K p k hk
  have h2 := congrArg (fun (g : (MVShift.shK K p).cycles k ⟶ K.homology (k + p)) => g.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- **The cycle comparison is compatible with `iCycles`.**  It is Mathlib's
`restrictionCyclesIso_hom_iCycles`; the `restrictionXIso`-cast occurring there is trivial because
`shEmb p` is given by `k ↦ k + p`. -/
theorem shK_cyclesIso_comp_iCycles (K : CochainComplex (ModuleCat ℚ) ℕ) (p k : ℕ) :
    CategoryTheory.CategoryStruct.comp (MVShift.shK_cyclesIso K p k).hom (K.iCycles (k + p))
      = CategoryTheory.CategoryStruct.comp ((MVShift.shK K p).iCycles k)
          (K.restrictionXIso (MVShift.shEmb p) (by change (k : ℕ) + p = k + p; rfl)).hom := by
  rw [shK_cyclesIso_hom_eq K p k]
  exact HomologicalComplex.restrictionCyclesIso_hom_iCycles (K := K) (e := MVShift.shEmb p)
    k (k + 1) (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl))
    (by change (k : ℕ) + p = k + p; rfl)
    (by change (k + 1) + p = (k + 1) + p; rfl)
    (by change (ComplexShape.up ℕ).next (k + p) = (k + 1) + p
        exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (k + p) ((k + 1) + p) from by
          change k + p + 1 = (k + 1) + p; omega))

/-- **The cycle comparison commutes with `cyclesMap`.**  The `iCycles`-image of the comparison of
a pushed cycle is the push of the `iCycles`-image. -/
theorem shK_cyclesIso_cyclesMap_iCycles {A K : CochainComplex (ModuleCat ℚ) ℕ} (p k : ℕ)
    (φ : A ⟶ MVShift.shK K p) (z : A.cycles k) :
    (K.iCycles (k + p)).hom ((MVShift.shK_cyclesIso K p k).hom
      ((HomologicalComplex.cyclesMap φ k).hom z))
      = (φ.f k).hom ((A.iCycles k).hom z) := by
  have h := shK_cyclesIso_comp_iCycles K p k
  have h2 := congrArg (fun (g : (MVShift.shK K p).cycles k ⟶ K.X (k + p)) =>
    g.hom ((HomologicalComplex.cyclesMap φ k).hom z)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have hcm : ((MVShift.shK K p).iCycles k).hom
      ((HomologicalComplex.cyclesMap φ k).hom z) = (φ.f k).hom ((A.iCycles k).hom z) := by
    have hh := HomologicalComplex.cyclesMap_i φ k
    have hh2 := congrArg (fun (g : A.cycles k ⟶ (K.restriction (MVShift.shEmb p)).X k) =>
      g.hom z) hh
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh2
  rw [hcm] at h2
  exact h2

/-! ## The identification on the class of a relative cocycle -/

/-- **The identification, on the class of a relative cocycle of `(Y,∅)`.**  This is the whole
content of `cupRelChainHomology`; the general statement follows because every cohomology class of
`(Y,∅)` is the class of a relative cocycle (`Work.Cohomology.exists_relClassOf`). -/
theorem cupRelChain_homologyMap_class (Y : TopCat) (B : Set Y) (n₀ j : ℕ) (hj : 1 ≤ j)
    (t : relKern ℚ Y B n₀) (ht : relDiffLM ℚ Y B n₀ t = 0)
    (a : relKern ℚ Y (∅ : Set Y) j) (ha : relDiffLM ℚ Y (∅ : Set Y) j a = 0) :
    (MVShift.shK_homologyIso (relComplex ℚ Y B) n₀ j hj).hom
        ((HomologicalComplex.homologyMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
          (relClassOf ℚ Y (∅ : Set Y) a ha))
      = (ModuleCat.ofHom (Work.Serre.MVGlue.cupWith Y B j n₀
          (relClassOf ℚ Y B t ht))).hom
        ((Work.Thom.relToAbs ℚ (∅ : Set Y) j).hom (relClassOf ℚ Y (∅ : Set Y) a ha)) := by
  -- the cocycle conditions of `a.1` and of `t`
  have ha' : cochainDiff ℚ (TopCat.toSSet.obj Y) a.1 = 0 :=
    relClassOf_cochainDiff ℚ Y (∅ : Set Y) a ha
  have hac : ((SSetCochainComplex ℚ (TopCat.toSSet.obj Y)).d j (j + 1)).hom a.1 = 0 := by
    rw [SSetCochainComplex_d_hom]; exact ha'
  have ht' : ((relComplex ℚ Y B).d n₀ (n₀ + 1)).hom t = 0 := by
    rw [relComplex_d_apply]; exact ht
  -- the product `a.1 ⌣ t.1` is a cocycle (Leibniz rule), and `b := cupRelLM … a` is it
  have hbc : ((relComplex ℚ Y B).d (j + n₀) (j + n₀ + 1)).hom
      ((Work.Serre.cupRelLM Y B n₀ t j) a) = 0 :=
    mstar_cocycle_cochain (mixedLeibniz_mixedRelStar ℚ Y B) j n₀ a.1 t hac ht'
  have hb : relDiffLM ℚ Y B (j + n₀) ((Work.Serre.cupRelLM Y B n₀ t j) a) = 0 := by
    rw [← relComplex_d_apply]
    exact hbc
  -- the computation rule of the mixed cup product
  obtain ⟨hmem, h, hcup_eq⟩ :=
    Classical.choose_spec (mixedRelCupH ℚ (TopCat.of Y) B) j n₀ a.1 t ha' ht
  -- step 1: `homologyMap cupRelChain` on the class of the cocycle
  have hstep1 : (HomologicalComplex.homologyMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
        (relClassOf ℚ Y (∅ : Set Y) a ha)
      = ((MVShift.shK (relComplex ℚ Y B) n₀).homologyπ j).hom
          ((HomologicalComplex.cyclesMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
            (relCocycleOf ℚ Y (∅ : Set Y) a ha)) := by
    have hh := HomologicalComplex.homologyπ_naturality (Work.Serre.cupRelChain Y B n₀ t ht) j
    have h2 := congrArg (fun (g : (relComplex ℚ Y (∅ : Set Y)).cycles j ⟶
      (MVShift.shK (relComplex ℚ Y B) n₀).homology j) =>
      g.hom (relCocycleOf ℚ Y (∅ : Set Y) a ha)) hh
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, relClassOf] using h2
  -- step 2: the degree-shift comparison on the class of that cycle
  have hstep2 : (MVShift.shK_homologyIso (relComplex ℚ Y B) n₀ j hj).hom
        (((MVShift.shK (relComplex ℚ Y B) n₀).homologyπ j).hom
          ((HomologicalComplex.cyclesMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
            (relCocycleOf ℚ Y (∅ : Set Y) a ha)))
      = ((relComplex ℚ Y B).homologyπ (j + n₀)).hom
          ((MVShift.shK_cyclesIso (relComplex ℚ Y B) n₀ j).hom
            ((HomologicalComplex.cyclesMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
              (relCocycleOf ℚ Y (∅ : Set Y) a ha))) :=
    shK_homologyIso_homologyπ_apply (relComplex ℚ Y B) n₀ j hj _
  -- step 3: the underlying cochain of the pushed cycle is `mixedRelStar a.1 t`
  have hstep3 : ((relComplex ℚ Y B).homologyπ (j + n₀)).hom
          ((MVShift.shK_cyclesIso (relComplex ℚ Y B) n₀ j).hom
            ((HomologicalComplex.cyclesMap (Work.Serre.cupRelChain Y B n₀ t ht) j).hom
              (relCocycleOf ℚ Y (∅ : Set Y) a ha)))
      = ((relComplex ℚ Y B).homologyπ (j + n₀)).hom
          (relCocycleOf ℚ Y B ((Work.Serre.cupRelLM Y B n₀ t j) a) hb) := by
    congr 1
    apply iCycles_injective_K (relComplex ℚ Y B) (j + n₀)
    rw [shK_cyclesIso_cyclesMap_iCycles, iCycles_relCocycleOf, iCycles_relCocycleOf,
      Work.Serre.cupRelChain_f]
    rfl
  -- step 4: this is the class of the Alexander--Whitney product `a.1 ⌣ t.1`
  have hstep4 : ((relComplex ℚ Y B).homologyπ (j + n₀)).hom
          (relCocycleOf ℚ Y B ((Work.Serre.cupRelLM Y B n₀ t j) a) hb)
      = relClassOf ℚ Y B
          ⟨cup ℚ (TopCat.toSSet.obj Y) a.1 t.1, hmem⟩ h := by
    rw [relClassOf]
    rfl
  -- the right hand side, computed by the defining rule of the mixed cup product
  have hR : (ModuleCat.ofHom (Work.Serre.MVGlue.cupWith Y B j n₀
          (relClassOf ℚ Y B t ht))).hom
        ((Work.Thom.relToAbs ℚ (∅ : Set Y) j).hom (relClassOf ℚ Y (∅ : Set Y) a ha))
      = relClassOf ℚ Y B ⟨cup ℚ (TopCat.toSSet.obj Y) a.1 t.1, hmem⟩ h := by
    rw [show (Work.Thom.relToAbs ℚ (∅ : Set Y) j).hom (relClassOf ℚ Y (∅ : Set Y) a ha)
        = cohomologyClassOf ℚ (TopCat.toSSet.obj Y) a.1 ha' from
      relIncl_homologyMap_relClassOf ℚ Y (∅ : Set Y) a ha]
    exact hcup_eq
  rw [hstep1, hstep2, hstep3]
  exact hstep4.trans hR.symm

/-! ## The statement -/

theorem cupRelChainHomology (Y : TopCat) (B : Set Y) (n₀ j : ℕ) (hj : 1 ≤ j)
    (t : Work.Cohomology.relKern ℚ Y B n₀)
    (ht : Work.Cohomology.relDiffLM ℚ Y B n₀ t = 0) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Serre.cupRelChain Y B n₀ t ht) j)
        (Work.Serre.MVShift.shK_homologyIso (Work.Cohomology.relComplex ℚ Y B) n₀ j hj).hom
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relToAbs ℚ (∅ : Set Y) j)
        (ModuleCat.ofHom (Work.Serre.MVGlue.cupWith Y B j n₀
            (Work.Cohomology.relClassOf ℚ Y B t ht))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ Y (∅ : Set Y) j x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact cupRelChain_homologyMap_class Y B n₀ j hj t ht a ha

end

end Work.Serre.DiscPair
