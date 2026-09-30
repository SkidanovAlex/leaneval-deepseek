import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.BOCK.bocksteinLES
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.FGThm.sphereFG
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

/-!
# The low-degree mod-`2` cohomology of `S³`

`Work.StemsB.SphModel 3 = OnePoint ℝ³` is (homeomorphic to) the `3`-sphere, so its mod-`2`
cohomology is `𝔽₂` in degree `0`, vanishes in degrees `1, 2` (and `4`) and is `𝔽₂` again in
degree `3`.  This file provides exactly the low-degree part needed downstream: `H² = H⁴ = 0`,
`finrank H⁰ = 1`, and finite dimensionality in degrees `≤ 4`.

Everything is proved for the metric sphere `Work.Pi6.S3 = S³ ⊆ ℝ⁴` (whose integral homology is
computed in the library by `Work.Cohomology.sphereHomologyTop` / `sphereHomologyZero`), and then
transported along the homeomorphism `Work.Pi6.EFACTS.sHomeo : SphModel 3 ≃ₜ S³`.

The mod-`2` homology of the sphere is computed from the integral one by the Bockstein long exact
sequence (`Work.Pi6.BOCK.bocksteinLES`): at a spot
`H_{m+1}(X;ℤ) --·2--> H_{m+1}(X;ℤ) --red--> H_{m+1}(X;𝔽₂) --∂--> H_m(X;ℤ) --·2--> H_m(X;ℤ)`
the vanishing of `H_{m+1}(X;ℤ)` together with the absence of `2`-torsion in `H_m(X;ℤ)` forces
`H_{m+1}(X;𝔽₂) = 0`.  The field universal coefficient theorem
(`Work.StemsB.fieldDualUCT`) converts this into the vanishing of the cohomology.
-/

namespace Work.Pi6.EFACTS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## 1. Homotopy invariance of singular cohomology

The library has this for `ℤ` coefficients (`Work.Cohomology.cohomologyIso_of_homotopyEquiv`); we
need it for arbitrary coefficients in order to move the computation from `S³` to `SphModel 3`. -/

theorem cohIso_of_homotopyEquiv (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology R n (TopCat.of X) ≅
      Work.Cohomology.singularCohomology R n (TopCat.of Y)) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := e.right_inv.some
  haveI := Work.Cohomology.homotopyEquiv R (TopCat.of X) (TopCat.of Y) f g h1 h2 n
  exact ⟨(CategoryTheory.asIso
    (Work.Cohomology.singularCohomologyMap R (TopCat.of X) (TopCat.of Y) f n)).symm⟩

/-! ## 2. The field universal coefficient theorem -/

/-- The universal coefficient theorem over a field: `H^n(X;𝕜) ≅ Hom_𝕜(H_n(X;𝕜), 𝕜)`. -/
theorem cohIsoDualField (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (n : ℕ) :
    Nonempty (Work.Pi6.Coh 𝕜 X n ≅
      ModuleCat.of 𝕜 (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜)) :=
  Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) n

/-- Cohomology vanishes as soon as homology does. -/
theorem isZero_coh_of_subsingleton (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (n : ℕ)
    (h : Subsingleton (Work.Pi6.HR 𝕜 X n)) : IsZero (Work.Pi6.Coh 𝕜 X n) := by
  obtain ⟨e⟩ := cohIsoDualField 𝕜 X n
  haveI := h
  haveI : Subsingleton (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) := inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

/-- Finite dimensional homology gives finite dimensional cohomology (the dual of a finite
dimensional vector space is finite dimensional). -/
theorem moduleFinite_coh_of_moduleFinite (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X]
    (n : ℕ) (h : Module.Finite 𝕜 ↥(Work.Pi6.HR 𝕜 X n)) :
    Module.Finite 𝕜 ↥(Work.Pi6.Coh 𝕜 X n) := by
  obtain ⟨e⟩ := cohIsoDualField 𝕜 X n
  haveI := h
  haveI : Module.Finite 𝕜 (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) :=
    Module.Finite.linearMap 𝕜 𝕜 _ 𝕜
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- `H⁰` of a path connected space is the coefficient field. -/
theorem finrank_coh_zero (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 X 0) = 1 := by
  obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of X)
  rw [LinearEquiv.finrank_eq e.toLinearEquiv]
  exact Module.finrank_self 𝕜

/-! ## 3. The Bockstein vanishing lemma -/

/-- **Vanishing mod `2` from the integral Bockstein sequence.**  If `H_{m+1}(X;ℤ) = 0` and
`H_m(X;ℤ)` has no `2`-torsion, then `H_{m+1}(X;𝔽₂) = 0`. -/
theorem subsingleton_modTwo_of_no_twoTorsion {X : Type} [TopologicalSpace X] (m : ℕ)
    (hn0 : Subsingleton (Work.Pi6.HR ℤ X (m + 1)))
    (htf : ∀ z : Work.Pi6.HR ℤ X m, (2 : ℤ) • z = 0 → z = 0) :
    Subsingleton (Work.Pi6.HR (ZMod 2) X (m + 1)) := by
  obtain ⟨red, del, _, hrd, hdel, _, _⟩ := Work.Pi6.BOCK.bocksteinLES 2 (by norm_num)
  haveI := hn0
  -- exactness at `H_{m+1}(X;𝔽₂)` and at `H_m(X;ℤ)`
  have hex1 : Function.Exact (⇑(red (X := X) (m + 1))) (⇑(del (X := X) m)) := hrd X m
  have hex2 : Function.Exact (⇑(del (X := X) m))
      (fun z : Work.Pi6.HR ℤ X m => (2 : ℤ) • z) := hdel X m
  refine ⟨fun y₁ y₂ => ?_⟩
  have hdel0 : del (X := X) m (y₁ - y₂) = 0 := by
    have h2 : (2 : ℤ) • (del (X := X) m (y₁ - y₂)) = 0 :=
      (hex2 (del (X := X) m (y₁ - y₂))).mpr ⟨y₁ - y₂, rfl⟩
    exact htf _ h2
  obtain ⟨x, hx⟩ := (hex1 (y₁ - y₂)).mp hdel0
  have hy : y₁ - y₂ = 0 := by
    rw [← hx, show red (X := X) (m + 1) x = red (X := X) (m + 1) 0 from
      congrArg _ (Subsingleton.elim x 0), map_zero]
  exact sub_eq_zero.mp hy

/-! ## 4. The target -/

theorem sphereModTwoLow :
    CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 2) ∧
    CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 4) ∧
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 0) = 1 ∧
    (∀ s : ℕ, s ≤ 4 → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) s)) := by
  haveI hpc : PathConnectedSpace (Work.Pi6.S3) :=
    Work.FGThm.pathConnectedSpace_sph 3 (by norm_num)
  -- integral homology of `S³`
  have hZ1 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 1) :=
    ModuleCat.subsingleton_of_isZero
      (Work.Cohomology.sphereHomologyZero 3 1 (by norm_num) (by norm_num) (by norm_num))
  have hZ2 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 2) :=
    ModuleCat.subsingleton_of_isZero
      (Work.Cohomology.sphereHomologyZero 3 2 (by norm_num) (by norm_num) (by norm_num))
  have hZ4 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 4) :=
    ModuleCat.subsingleton_of_isZero
      (Work.Cohomology.sphereHomologyZero 3 4 (by norm_num) (by norm_num) (by norm_num))
  -- `H₃(S³;ℤ) ≅ ℤ` has no `2`-torsion
  have hTF3 : ∀ z : Work.Pi6.HR ℤ (Work.Pi6.S3) 3, (2 : ℤ) • z = 0 → z = 0 := by
    intro z hz
    obtain ⟨e3⟩ := Work.Cohomology.sphereHomologyTop 3 (by norm_num)
    have h1 : (2 : ℤ) • e3.toLinearEquiv z = 0 := by
      have h : e3.toLinearEquiv ((2 : ℤ) • z) = 0 := by rw [hz, map_zero]
      rwa [map_zsmul] at h
    have h3 : (2 : ℤ) * e3.toLinearEquiv z = 0 := by rwa [zsmul_eq_mul] at h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (by norm_num)
    · exact e3.toLinearEquiv.injective (by rw [h4, map_zero])
  -- mod-`2` homology of `S³` in degrees `2` and `4`
  have hM2 : Subsingleton (Work.Pi6.HR (ZMod 2) (Work.Pi6.S3) 2) :=
    subsingleton_modTwo_of_no_twoTorsion 1 hZ2 (fun z _ => Subsingleton.elim z 0)
  have hM4 : Subsingleton (Work.Pi6.HR (ZMod 2) (Work.Pi6.S3) 4) :=
    subsingleton_modTwo_of_no_twoTorsion 3 hZ4 hTF3
  -- mod-`2` cohomology of `S³`
  have hCoh2 : IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) 2) :=
    isZero_coh_of_subsingleton (ZMod 2) (Work.Pi6.S3) 2 hM2
  have hCoh4 : IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) 4) :=
    isZero_coh_of_subsingleton (ZMod 2) (Work.Pi6.S3) 4 hM4
  have hCoh0 : Module.finrank (ZMod 2) ↥(Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) 0) = 1 :=
    finrank_coh_zero (ZMod 2) (Work.Pi6.S3)
  have hCohFin : ∀ s : ℕ, s ≤ 4 →
      Module.Finite (ZMod 2) ↥(Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) s) := by
    intro s hs
    have hHR : Module.Finite (ZMod 2) ↥(Work.Pi6.HR (ZMod 2) (Work.Pi6.S3) s) :=
      Work.Pi6.EMM2.moduleFinite_singularHomology (ZMod 2) (Work.Pi6.S3) 4
        (Work.FGThm.fgUpTo_sph 3 (by norm_num) 4) s hs
    exact moduleFinite_coh_of_moduleFinite (ZMod 2) (Work.Pi6.S3) s hHR
  -- transport along `SphModel 3 ≃ₜ S³`
  have hT : ∀ n : ℕ, Work.Cohomology.singularCohomology (ZMod 2) n
        (TopCat.of (Work.StemsB.SphModel 3)) ≅
      Work.Cohomology.singularCohomology (ZMod 2) n (TopCat.of (Work.Pi6.S3)) :=
    fun n => (cohIso_of_homotopyEquiv (ZMod 2) (sHomeo.toHomotopyEquiv) n).some
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsZero.of_iso hCoh2 (hT 2)
  · exact IsZero.of_iso hCoh4 (hT 4)
  · rw [LinearEquiv.finrank_eq (hT 0).toLinearEquiv]
    exact hCoh0
  · intro s hs
    haveI := hCohFin s hs
    exact Module.Finite.equiv (hT s).toLinearEquiv.symm

end

end Work.Pi6.EFACTS
