import Mathlib
import Submission.Work.SSS.E2Zero.Defs
import Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff
import Submission.Work.SSS.E2Zero.Cincl_mem_V_one_iff
import Submission.Work.SSS.E2Zero.ker_chi_eq_ker_homologyMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.E2Zero

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- `chi`, with its domain displayed through the definitional equality
`(ξ.F.obj 0).homology t = ((ξ.F.obj 0).sc t).homology`.  This is the same linear map as
`chi ξ t`, but the spelling of its domain makes it composable with statements phrased at the
degree `t` of the ambient complex rather than at the degree `t` of the short complex `sc t`. -/
def chiB (ξ : Work.SSS.Filtration C) (t : ℕ) :
    ↥((ξ.F.obj 0).homology t) →ₗ[ℤ] (↥(Work.SSS.Zof ξ t) ⧸ Work.SSS.VZ ξ t 1) :=
  Work.SSS.E2Zero.chi ξ t

/-- An `eqToHom` in `ModuleCat ℤ` is injective (it is an isomorphism). -/
lemma eqToHom_hom_injective {A B : ModuleCat ℤ} (h : A = B) :
    Function.Injective (eqToHom h).hom := by
  have hh : (eqToHom h).hom = ((eqToIso h).toLinearEquiv).toLinearMap := rfl
  rw [hh]
  exact (eqToIso h).toLinearEquiv.injective

/-- Naturality of `homologyMap` under an equality of the degree indices: transporting along
`eqToHom` commutes with the map induced on homology by a chain map. -/
lemma homologyMap_eqToHom_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (h : i = j) (y : ↥(K.homology i)) :
    (eqToHom (congrArg (fun x => L.homology x) h)).hom
        ((HomologicalComplex.homologyMap φ i).hom y)
      = (HomologicalComplex.homologyMap φ j).hom
        ((eqToHom (congrArg (fun x => K.homology x) h)).hom y) := by
  subst h
  simp

/-- Context: `Submission/Work/SSS/E2Zero/Defs.lean` (namespace `Work.SSS.E2Zero`) defines, for `ξ : Work.SSS.Filtration C`, `t : ℕ`: `valCyc`, `valK`, `incf ξ t`, `psi0 ξ t` with `psi0_eq_zero_iff`, `psi ξ t`, `chi ξ t` with `chi_apply ξ t v : chi ξ t ((F_0.sc t).homologyπ v) = psi0 ξ t ((F_0.sc t).moduleCatCyclesIso.hom v)`, `valK_cycle_eq`, `valK_isCycle`, `valCyc_isCycle`, `iCycles_cyclesMap_apply`, and `hT ξ t : ↥((ξ.F.obj 0).homology (0+t)) ≃ₗ ↥(((ξ.F.obj 0).sc t).homology)`. Available: `Work.SSS.range_kF_eq_ker_incF` (`Submission/Work/SSS/LESFacts.lean`): `LinearMap.range (kF ξ 0 t).hom = LinearMap.ker (HomologicalComplex.homologyMap (incF ξ.F 0) (0+t)).hom`; `Work.SSS.E2Zero.homologypi_eq_zero_iff`: `K.homologyπ i z = 0 ↔ ∃ w, K.d (i+1) i w = K.iCycles i z`; `Work.SSS.E2Zero.Cincl_mem_V_one_iff`: for a cycle `z` of `F_0` in degree `t`, `Cincl ξ 0 t z ∈ V ξ t 1 ↔ ∃ w, dFs ξ 1 (t+1) t w = (incF ξ.F 0).f t z`.

Route: reduce both sides to submodules of `↥(((ξ.F.obj 0).sc t).cycles)` by pulling back along the surjective `((ξ.F.obj 0).sc t).homologyπ` (`ModuleCat.epi_iff_surjective`, `LinearMap.range_eq_top`, `LinearMap.ker_comp`, `Submodule.map_comap_eq`); identify the composite `chi ∘ homologyπ` with `psi0 ∘ (F_0.sc t).moduleCatCyclesIso.hom` using `chi_apply` + `ShortComplex.π_moduleCatCyclesIso_hom`, and the other side with `((F_1.sc t).homologyπ) ∘ cyclesMap (incF ξ.F 0) t` using `HomologicalComplex.homologyπ_naturality`; the membership equivalence is then `psi0_eq_zero_iff` + `valK_cycle_eq` + the naturality `valCyc (F_1) t ((cyclesMap (incF ξ.F 0) t) v) = incf ξ t (valCyc (F_0) t v)` (`iCycles_cyclesMap_apply` + `tau2_incf`) + `homologypi_eq_zero_iff` + `Cincl_mem_V_one_iff`. Finally transport along `hT` (via `Submodule.map` and the injectivity/surjectivity of the induced maps). -/
theorem ker_chi_map {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (t : ℕ) :
    (LinearMap.ker (Work.SSS.E2Zero.chi ξ t)).map (Work.SSS.E2Zero.hT ξ t).symm.toLinearMap
      = LinearMap.range (Work.SSS.kF ξ 0 t).hom := by
  rw [Work.SSS.range_kF_eq_ker_incF]
  -- `ker χ` is `ker (homologyMap (incF ξ.F 0) t)` by `ker_chi_eq_ker_homologyMap`,
  -- phrased with the domain of `χ` displayed as `(ξ.F.obj 0).homology t`.
  have hmain : LinearMap.ker (chiB ξ t)
      = LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) t).hom := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact ker_chi_eq_ker_homologyMap ξ t x
  -- membership on the left, transported along `hT`
  have hL : ∀ y : ↥((ξ.F.obj 0).homology (0 + t)),
      (y ∈ (LinearMap.ker (Work.SSS.E2Zero.chi ξ t)).map
        (Work.SSS.E2Zero.hT ξ t).symm.toLinearMap)
      ↔ Work.SSS.E2Zero.chi ξ t ((Work.SSS.E2Zero.hT ξ t) y) = 0 := by
    intro y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = (Work.SSS.E2Zero.hT ξ t) y :=
        (LinearEquiv.symm_apply_eq (Work.SSS.E2Zero.hT ξ t)).mp (by simpa using hzy)
      rw [← hzy']
      exact LinearMap.mem_ker.mp hz
    · intro hy
      refine ⟨(Work.SSS.E2Zero.hT ξ t) y, LinearMap.mem_ker.mpr hy, ?_⟩
      simpa using (Work.SSS.E2Zero.hT ξ t).symm_apply_apply y
  ext y
  rw [hL y, LinearMap.mem_ker]
  -- `hT ξ t` is the `eqToHom` given by `Nat.zero_add t`
  have hww : ((Work.SSS.E2Zero.hT ξ t) y : ↥((ξ.F.obj 0).homology t))
      = (eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y := rfl
  rw [hww]
  -- naturality of `homologyMap (incF ξ.F 0)` under the index equality `0 + t = t`
  have hnat := homologyMap_eqToHom_apply (Work.SSS.incF ξ.F 0) (Nat.zero_add t) y
  constructor
  · intro hchi
    have hchiB : chiB ξ t
        ((eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y)
        = 0 := hchi
    have h1 : (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) t).hom
        ((eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y)
        = 0 := by
      have hmem : ((eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y)
          ∈ LinearMap.ker (chiB ξ t) := LinearMap.mem_ker.mpr hchiB
      rw [hmain] at hmem
      exact LinearMap.mem_ker.mp hmem
    have h2 : (eqToHom (congrArg (fun x => (ξ.F.obj 1).homology x) (Nat.zero_add t))).hom
        ((HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) (0 + t)).hom y) = 0 := by
      rw [hnat]
      exact h1
    exact eqToHom_hom_injective _ (h2.trans (map_zero _).symm)
  · intro h0
    have h1 : (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) t).hom
        ((eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y)
        = 0 := by
      rw [← hnat, h0, map_zero]
    have hmem : ((eqToHom (congrArg (fun x => (ξ.F.obj 0).homology x) (Nat.zero_add t))).hom y)
        ∈ LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) t).hom :=
      LinearMap.mem_ker.mpr h1
    rw [← hmain] at hmem
    exact LinearMap.mem_ker.mp hmem

end

end Work.SSS.E2Zero
