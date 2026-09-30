import Mathlib
import Submission.Work.Cohomology.relCohMVDefs

/-!
# Exactness at the middle of the relative cohomological Mayer–Vietoris sequence

The chain level relative Mayer–Vietoris sequence

`C^{U,V}(U ∩ V, U ∩ V ∩ A) --f--> C^{U,V}(U, U ∩ A) ⊞ C^{U,V}(V, V ∩ A) --g--> C^{U,V}(X,A)`

is degreewise short exact (`relMVChainDegreewise_ker`, `relMVChainDegreewise_surjective`).  Its
dual

`C^*(X,A) --relCohMVF--> C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A) --relCohMVG--> C^*(U ∩ V, U ∩ V ∩ A)`

is therefore exact in the middle, because the dual of a short exact sequence of modules is exact
in the middle (`Work.Cohomology.exists_dualMap_eq_of_mem_ker`).

## Main result

* `relCohMVG_ker_le_range` — `ker (relCohMVG).f n ≤ range (relCohMVF).f n`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

open DualBiprod

variable (X : TopCat) (A U V : Set X) (n : ℕ)

/-! ## The degreewise components of the relative cohomological maps -/

/-- `relCohMVG` on the first summand is the transpose of `relMVChainBeta₁`. -/
lemma relCohMVG_apply_inl (a : (dualComplex ℤ (relMVUU X A U V)).X n) :
    ModuleCat.Hom.hom ((relCohMVG X A U V).f n)
      (ModuleCat.Hom.hom ((biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) a)
      = a.comp ((relMVChainBeta₁ X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVG_inl]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- `relCohMVG` on the second summand is the transpose of `relMVChainBeta₂`. -/
lemma relCohMVG_apply_inr (b : (dualComplex ℤ (relMVVV X A U V)).X n) :
    ModuleCat.Hom.hom ((relCohMVG X A U V).f n)
      (ModuleCat.Hom.hom ((biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) b)
      = b.comp ((relMVChainBeta₂ X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVG_inr]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- The `fst`-component of `relCohMVF` is the transpose of `relMVChainAlpha₁`. -/
lemma relCohMVF_fst_apply (χ : (dualComplex ℤ (relMVTopC X A U V)).X n) :
    ModuleCat.Hom.hom ((biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n)
      (ModuleCat.Hom.hom ((relCohMVF X A U V).f n) χ)
      = χ.comp ((relMVChainAlpha₁ X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVF_fst]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-- The `snd`-component of `relCohMVF` is the transpose of `relMVChainAlpha₂`. -/
lemma relCohMVF_snd_apply (χ : (dualComplex ℤ (relMVTopC X A U V)).X n) :
    ModuleCat.Hom.hom ((biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n)
      (ModuleCat.Hom.hom ((relCohMVF X A U V).f n) χ)
      = χ.comp ((relMVChainAlpha₂ X A U V).f n).hom := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVF_snd]
  simp only [DualBiprod.dualMapHom_hom]
  rfl

/-! ## Exactness at the middle -/

/-- **Exactness at the middle of the relative cohomological Mayer–Vietoris sequence**, degree `n`:
every `n`-cochain of the pair `(U, V)` that is killed by `relCohMVG` comes from the cochain complex
of `(X,A)` through `relCohMVF`. -/
theorem relCohMVG_ker_le_range (X : TopCat) (A U V : Set X) (n : ℕ) :
    LinearMap.ker (ModuleCat.Hom.hom ((Work.Cohomology.relCohMVG X A U V).f n))
      ≤ LinearMap.range (ModuleCat.Hom.hom ((Work.Cohomology.relCohMVF X A U V).f n)) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [LinearMap.mem_range]
  -- ## Step 1: the chain-level relative Mayer–Vietoris sequence is exact in degree `n`
  have hsurj := relMVChainDegreewise_surjective X A U V n
  have hex := relMVChainDegreewise_ker X A U V n
  -- ## Step 2: the two components of `y`
  set a : (relMVUU X A U V).X n →ₗ[ℤ] ℤ :=
    ModuleCat.Hom.hom ((biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
      dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n) y with ha
  set b : (relMVVV X A U V).X n →ₗ[ℤ] ℤ :=
    ModuleCat.Hom.hom ((biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
      dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n) y with hb
  have hydec : ModuleCat.Hom.hom ((biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
      dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) a
      + ModuleCat.Hom.hom ((biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
      dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) b = y := by
    rw [ha, hb]
    exact biprodX_total y
  -- ## Step 3: they satisfy the compatibility relation
  have hcond : a.comp ((relMVChainBeta₁ X A U V).f n).hom
      + b.comp ((relMVChainBeta₂ X A U V).f n).hom = 0 := by
    have h0 : ModuleCat.Hom.hom ((relCohMVG X A U V).f n)
        (ModuleCat.Hom.hom ((biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
            dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) a
          + ModuleCat.Hom.hom ((biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
            dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n) b) = 0 := by
      rw [hydec]; exact hy
    rw [map_add, relCohMVG_apply_inl, relCohMVG_apply_inr] at h0
    exact h0
  -- ## Step 4: the chain-level functional `ψ`
  set ψ : ((relMVUU X A U V) ⊞ (relMVVV X A U V)).X n →ₗ[ℤ] ℤ :=
    a.comp ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n).hom
      + b.comp ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n).hom
    with hψ
  have hψ0 : ∀ m, ψ (((relMVChainLeft X A U V).f n).hom m) = 0 := by
    intro m
    have h1 : (((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n).hom)
        (((relMVChainLeft X A U V).f n).hom m) = ((relMVChainBeta₁ X A U V).f n).hom m := by
      have h := congrArg ModuleCat.Hom.hom (relMVChainBeta₁_f X A U V n)
      rw [ModuleCat.hom_comp] at h
      exact (LinearMap.congr_fun h m).symm
    have h2 : (((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n).hom)
        (((relMVChainLeft X A U V).f n).hom m) = ((relMVChainBeta₂ X A U V).f n).hom m := by
      have h := congrArg ModuleCat.Hom.hom (relMVChainBeta₂_f X A U V n)
      rw [ModuleCat.hom_comp] at h
      exact (LinearMap.congr_fun h m).symm
    have h3 : a (((relMVChainBeta₁ X A U V).f n).hom m)
        + b (((relMVChainBeta₂ X A U V).f n).hom m) = 0 := by
      have h := LinearMap.congr_fun hcond m
      rwa [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [hψ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, h1, h2]
    exact h3
  -- ## Step 5: the dual of the chain-level short exact sequence
  obtain ⟨χ, hχ⟩ := exists_dualMap_eq_of_mem_ker (((relMVChainLeft X A U V).f n).hom)
    (((relMVChainRight X A U V).f n).hom) hsurj hex ψ hψ0
  refine ⟨χ, ?_⟩
  -- ## Step 6: `relCohMVF χ = y`
  apply biprodX_ext
  · show ModuleCat.Hom.hom ((biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n)
        (ModuleCat.Hom.hom ((relCohMVF X A U V).f n) χ) = a
    rw [relCohMVF_fst_apply]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply]
    have hA : ((relMVChainAlpha₁ X A U V).f n).hom x
        = ((relMVChainRight X A U V).f n).hom
            (((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) := by
      have h := congrArg ModuleCat.Hom.hom (relMVChainAlpha₁_f X A U V n)
      rw [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h x
    rw [hA, hχ]
    rw [hψ]
    have hP : (((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n).hom)
        (((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) = x := by
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.biprod_inl_fst_f (relMVUU X A U V) (relMVVV X A U V) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h x
    have hQ : (((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n).hom)
        (((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) = 0 := by
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.biprod_inl_snd_f (relMVUU X A U V) (relMVVV X A U V) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h x
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hP, hQ]
    simp
  · show ModuleCat.Hom.hom ((biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n)
        (ModuleCat.Hom.hom ((relCohMVF X A U V).f n) χ) = b
    rw [relCohMVF_snd_apply]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply]
    have hA : ((relMVChainAlpha₂ X A U V).f n).hom x
        = ((relMVChainRight X A U V).f n).hom
            (((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) := by
      have h := congrArg ModuleCat.Hom.hom (relMVChainAlpha₂_f X A U V n)
      rw [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h x
    rw [hA, hχ]
    rw [hψ]
    have hP : (((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n).hom)
        (((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) = 0 := by
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.biprod_inr_fst_f (relMVUU X A U V) (relMVVV X A U V) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h x
    have hQ : (((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n).hom)
        (((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n).hom x) = x := by
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.biprod_inr_snd_f (relMVUU X A U V) (relMVVV X A U V) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h x
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hP, hQ]
    simp

end

end Work.Cohomology
