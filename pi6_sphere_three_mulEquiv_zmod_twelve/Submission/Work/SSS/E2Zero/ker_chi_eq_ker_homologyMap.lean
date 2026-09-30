import Mathlib
import Submission.Work.SSS.E2Zero.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.E2Zero

open CategoryTheory CategoryTheory.Limits

/-- The left-hand side of `ker_chi_eq_ker_homologyMap`, evaluated on the homology class of a
cycle `v` of `F_0` in degree `t`: the two reductions `chi_apply`, `psi0_eq_zero_iff`,
`valK_cycle_eq` and `Cincl_mem_V_one_iff` produce the explicit boundary condition. -/
theorem chi_homologyπ_eq_zero_iff {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ)
    (v : ↥(((ξ.F.obj 0).sc t).cycles)) :
    (chi ξ t (((ξ.F.obj 0).sc t).homologyπ v) = 0) ↔
      (∃ w : ↥((ξ.F.obj 1).X (t + 1)),
        dFs ξ 1 (t + 1) t w = incf ξ t (valCyc (ξ.F.obj 0) t v)) := by
  rw [chi_apply, psi0_eq_zero_iff, valK_cycle_eq,
    Cincl_mem_V_one_iff ξ t (valCyc (ξ.F.obj 0) t v) (valCyc_isCycle (ξ.F.obj 0) t v)]
  rfl

/-- The right-hand side of `ker_chi_eq_ker_homologyMap`, evaluated on the homology class of a
cycle `v` of `F_0` in degree `t`: naturality of `homologyπ`, `homologypi_eq_zero_iff`,
`iCycles_cyclesMap_apply` and `tau2_incf` produce the same explicit boundary condition. -/
theorem homologyMap_homologyπ_eq_zero_iff {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C)
    (t : ℕ) (v : ↥(((ξ.F.obj 0).sc t).cycles)) :
    ((HomologicalComplex.homologyMap (incF ξ.F 0) t) (((ξ.F.obj 0).sc t).homologyπ v) = 0) ↔
      (∃ w : ↥((ξ.F.obj 1).X (t + 1)),
        dFs ξ 1 (t + 1) t w = incf ξ t (valCyc (ξ.F.obj 0) t v)) := by
  -- write the cycle in the `K.cycles t` shape expected by the Mathlib naturality lemma
  rw [show ((ξ.F.obj 0).sc t).homologyπ v
        = (ξ.F.obj 0).homologyπ t (show ↥((ξ.F.obj 0).cycles t) from v) from rfl]
  -- naturality of `homologyπ` applied to `v`
  have hnat : (HomologicalComplex.homologyMap (incF ξ.F 0) t).hom
        ((ξ.F.obj 0).homologyπ t (show ↥((ξ.F.obj 0).cycles t) from v))
      = (ξ.F.obj 1).homologyπ t (HomologicalComplex.cyclesMap (incF ξ.F 0) t
          (show ↥((ξ.F.obj 0).cycles t) from v)) := by
    have h := congrArg (fun (g : (ξ.F.obj 0).cycles t ⟶ (ξ.F.obj 1).homology t) => g.hom)
      (HomologicalComplex.homologyπ_naturality (incF ξ.F 0) t)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h (show ↥((ξ.F.obj 0).cycles t) from v)
  rw [hnat]
  -- the kernel of `homologyπ` of `F_1` is the range of `d`
  rw [homologypi_eq_zero_iff]
  -- `iCycles` of `F_1` commutes with `cyclesMap`
  rw [show (ξ.F.obj 1).iCycles t (HomologicalComplex.cyclesMap (incF ξ.F 0) t
          (show ↥((ξ.F.obj 0).cycles t) from v))
      = ((incF ξ.F 0).f t) (((ξ.F.obj 0).sc t).iCycles v) from iCycles_cyclesMap_apply ξ t v]
  rfl

/-- `χ` has the same kernel as the map induced by the inclusion `F_0 ⊆ F_1` on `H_t`: a homology class of `F_0` in degree `t` is killed by `χ` (equivalently, the image of a representing cycle under `Cincl ξ 0 t` lies in `V ξ t 1`) exactly when it dies in `H_t(F_1)`, i.e. is killed by `HomologicalComplex.homologyMap (incF ξ.F 0) t`.

Route: reduce both sides to conditions on a cycle `v` of `F_0` in degree `t` by pulling back along the surjective `((ξ.F.obj 0).sc t).homologyπ` (`ModuleCat.epi_iff_surjective`, `LinearMap.range_eq_top`). For `χ` use `Work.SSS.E2Zero.chi_apply` to get `psi0 ξ t ((F_0.sc t).moduleCatCyclesIso.hom v)`, then `psi0_eq_zero_iff`, `valK_cycle_eq` and `Cincl_mem_V_one_iff` (with `valCyc_isCycle (ξ.F.obj 0) t v`) to reach `∃ w : ↥((ξ.F.obj 1).X (t+1)), dFs ξ 1 (t+1) t w = incf ξ t (valCyc (ξ.F.obj 0) t v)`. On the other side use `HomologicalComplex.homologyπ_naturality` to rewrite `homologyMap (incF ξ.F 0) t ((F_0.sc t).homologyπ v)` as `((ξ.F.obj 1).sc t).homologyπ (cyclesMap (incF ξ.F 0) t v)`, then `Work.SSS.E2Zero.homologypi_eq_zero_iff` (with `K := ξ.F.obj 1`), `Work.SSS.E2Zero.iCycles_cyclesMap_apply` and `Work.SSS.E2Zero.tau2_incf` (with `valCyc` written as `tau2LM` composed with `iCycles`) to reach the same condition. All cited lemmas are in `Submission.Work.SSS.E2Zero.Defs` (which imports `Submission.Work.SSS.LESFacts`, `Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff`, `Submission.Work.SSS.E2Zero.Cincl_mem_V_one_iff`). The statement is phrased elementwise because `LinearMap.ker` on the quotient-codomain map `χ` does not elaborate without `attribute [-instance] AddCommGroup.toIntModule`, which is set in the files of this workspace but not in a bare statement file. -/
theorem ker_chi_eq_ker_homologyMap {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (t : ℕ) :
    ∀ x : ↥((ξ.F.obj 0).homology t),
      (Work.SSS.E2Zero.chi ξ t x = 0) ↔
        ((HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) t).hom x = 0) := by
  intro x
  obtain ⟨v, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((ξ.F.obj 0).sc t).homologyπ).mp inferInstance x
  exact (chi_homologyπ_eq_zero_iff ξ t v).trans (homologyMap_homologyπ_eq_zero_iff ξ t v).symm

end Work.SSS.E2Zero
