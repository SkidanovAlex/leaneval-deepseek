import Mathlib
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the tautological line bundle over the projectivisation

For a complex gluing-data bundle `Z` over `B` and a continuous map `f : C(B', B)`, the
projectivisation is functorial (`Work.LerayHirsch.projMapComap Z f : P(f^*E) → P(E)`,
`Submission/Work/LerayHirsch/Naturality.lean`), and the tautological line bundle is natural along
this map: pulling back the tautological line bundle `ℓ ⊆ π^*E` of `P(E)` along `P(f)` gives the
tautological line bundle of the projectivisation `P(f^*E)` of the pullback,

`P(f)^*(ℓ_Z) = ℓ_{f^*Z}`,

as gluing data; consequently the two bundles are isomorphic
(`Work.LerayHirsch.nonempty_bundleIso_tautLine_comap`).  This is the naturality input needed to
compare the classes `ζ = c₁(ℓ)` of the two projectivisations.

Both cores are gluing data over `ProjSpace (bundleComap Z f)` with cover indexed by `ι × Fin m` and
model fibre `LineFibre = ℂ`, so by `Work.Thom.bundleCore_ext` it suffices to compare `baseSet`,
`indexAt` and `coordChange`:

* the base sets agree because the charts of the tautological line bundle are those of `Z` pulled
  back under `projMapComap` (`mem_tautBaseSetProj_comap`);
* the index maps agree: both are `Classical.choose` over predicates on the same index type
  `ι × Fin m` that are *equal* by the preceding point, so `Classical.choose.congr_simp` and proof
  irrelevance apply (the same device as `Work.Thom.tautQuotientCore_comap`);
* the transition functions agree because the tautological transition coefficient is the ratio of
  two chart coordinates, and the chart coordinates of the pullback are those of `Z`
  (`chartCoord_comap`): `tautCoeffLift Z ik jl (projMapComap Z f x)
  = tautCoeffLift (bundleComap Z f) ik jl x`.

Everything below is `sorry`-free and axiom-clean.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} {m : ℕ}

/-! ## The chart coordinates of a pullback are those of the original bundle -/

/-- **The chart coordinates commute with pullback**: the `i`-th chart coordinate of a point `p` of
the punctured total space of `bundleComap Z f` is the `i`-th chart coordinate of the corresponding
point `punctComap Z f p` of `Z`. -/
theorem chartCoord_bundleComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (i : ι) (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    chartCoord (bundleComap Z f) i p = chartCoord Z i (punctComap Z f p) := by
  rw [chartCoord_eq_realification, chartCoord_eq_realification]
  rw [realification_bundleComap]
  rw [localTriv_snd_bundleComap]
  rfl

/-! ## The tautological transition coefficient is natural -/

/-- **The tautological transition coefficient commutes with pullback.** -/
theorem tautCoeff_bundleComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (ik jl : ι × Fin m)
    (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    tautCoeff (bundleComap Z f) ik jl p = tautCoeff Z ik jl (punctComap Z f p) := by
  have hiff : chartCoord (bundleComap Z f) ik.1 p ik.2 ≠ 0 ↔
      chartCoord Z ik.1 (punctComap Z f p) ik.2 ≠ 0 := by rw [chartCoord_bundleComap]
  by_cases h : chartCoord (bundleComap Z f) ik.1 p ik.2 ≠ 0
  · rw [tautCoeff, tautCoeff, dif_pos h, dif_pos (hiff.mp h), chartCoord_bundleComap,
      chartCoord_bundleComap]
  · rw [tautCoeff, tautCoeff, dif_neg h, dif_neg (fun hh => h (hiff.mpr hh))]

/-- **The transition coefficient of the tautological line bundle is natural**: the transition
coefficient of `ℓ` at the image point `projMapComap Z f x` is the transition coefficient of `ℓ`
at `x`.  This is the equality of the transition functions of the two gluing data compared below. -/
theorem tautCoeffLift_comap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (ik jl : ι × Fin m) (x : ProjSpace (bundleComap Z f)) :
    tautCoeffLift Z ik jl (projMapComap Z f x)
      = tautCoeffLift (bundleComap Z f) ik jl x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj (bundleComap Z f) x
  rw [projMapComap_mkProj_apply, tautCoeffLift_mk, tautCoeffLift_mk]
  exact tautCoeff_bundleComap Z f ik jl p

/-- **The charts of the tautological line bundle are natural**: the chart of `ℓ_Z` indexed by
`ik` pulls back along `projMapComap Z f` to the chart of `ℓ_{f^*Z}` indexed by `ik`. -/
theorem mem_tautBaseSetProj_comap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (ik : ι × Fin m) (x : ProjSpace (bundleComap Z f)) :
    projMapComap Z f x ∈ tautBaseSetProj Z ik ↔ x ∈ tautBaseSetProj (bundleComap Z f) ik := by
  obtain ⟨p, rfl⟩ := surjective_mkProj (bundleComap Z f) x
  rw [projMapComap_mkProj_apply, mem_tautBaseSetProj_mk, mem_tautBaseSetProj_mk,
    mem_tautBaseSet, mem_tautBaseSet, bundleComap_baseSet, Set.mem_preimage,
    chartCoord_bundleComap]
  rfl

/-! ## The tautological line bundle is natural -/

/-- **Naturality of the tautological line bundle, as gluing data**: the pullback of `ℓ_Z` along
`projMapComap Z f` is the tautological line bundle of the pullback bundle `f^*Z`. -/
theorem bundleComap_tautLine_eq_tautLine_bundleComap
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    bundleComap (tautLine Z) (projMapComap Z f) = tautLine (bundleComap Z f) := by
  refine bundleCore_ext ?_ ?_ ?_
  · -- the base sets: `projMapComap` pulls the charts of `ℓ_Z` back to those of `ℓ_{f^*Z}`
    funext ik
    rw [bundleComap_baseSet, tautLine_baseSet, tautLine_baseSet]
    ext x
    exact mem_tautBaseSetProj_comap Z f ik x
  · -- the index maps: two `Classical.choose`s over equal predicates on `ι × Fin m`
    funext x
    rw [bundleComap_indexAt]
    change Classical.choose (exists_mem_tautBaseSetProj Z (projMapComap Z f x))
        = Classical.choose (exists_mem_tautBaseSetProj (bundleComap Z f) x)
    have hpred : (fun ik => projMapComap Z f x ∈ tautBaseSetProj Z ik)
        = (fun ik => x ∈ tautBaseSetProj (bundleComap Z f) ik) :=
      funext fun ik => propext (mem_tautBaseSetProj_comap Z f ik x)
    have hL := exists_mem_tautBaseSetProj Z (projMapComap Z f x)
    have hR := exists_mem_tautBaseSetProj (bundleComap Z f) x
    calc Classical.choose hL = Classical.choose (hpred ▸ hL) :=
          Classical.choose.congr_simp hpred hL
      _ = Classical.choose hR := congrArg Classical.choose (Subsingleton.elim _ _)
  · -- the transition functions
    intro ik jl x
    rw [bundleComap_coordChange, tautLine_coordChange, tautLine_coordChange]
    apply ContinuousLinearMap.ext
    intro v
    rw [tautCoeffCLM_apply, tautCoeffCLM_apply, tautCoeffLift_comap]

/-- **The tautological line bundle is natural under pullback of the base**: the pullback of `ℓ_Z`
along `P(f)` is isomorphic to `ℓ_{f^*Z}`. -/
theorem nonempty_bundleIso_tautLine_comap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} {m : ℕ} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.LerayHirsch.tautLine Z) (Work.LerayHirsch.projMapComap Z f))
      (Work.LerayHirsch.tautLine (Work.Thom.bundleComap Z f))) :=
  ⟨BundleIso.ofEq (bundleComap_tautLine_eq_tautLine_bundleComap Z f)⟩

end

end Work.LerayHirsch
