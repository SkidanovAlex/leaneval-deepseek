import Mathlib
import Submission.Work.SSS.E2Zero.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Work.SSS.E2Zero

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Context: `Submission/Work/SSS/E2Zero/Defs.lean` (namespace `Work.SSS.E2Zero`) defines, for `ξ : Work.SSS.Filtration C` and `t : ℕ`:
* `Cincl_injective ξ s n : Function.Injective (Cincl ξ s n)`, `Cincl_dFs`, `next_eq_down i : (ComplexShape.down ℕ).next i = i - 1`;
* `valK K i : ↥((K.sc i).moduleCatLeftHomologyData.K) →ₗ ↥(K.X i)`, with `valK_mk` and `tau2LM_eq`;
* `psi0 ξ t : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K) →ₗ ↥(Zof ξ t) ⧸ VZ ξ t 1`, with `psi0_apply ξ t y : psi0 ξ t y = (VZ ξ t 1).mkQ ⟨Cincl ξ 0 t (valK (ξ.F.obj 0) t y), _⟩`;
* `psi ξ t := Submodule.liftQ _ (psi0 ξ t) _` and `chi ξ t := (psi ξ t).comp (((ξ.F.obj 0).sc t).moduleCatHomologyIso.hom).hom`, with `chi_apply ξ t v : chi ξ t ((ξ.F.obj 0).sc t).homologyπ v = psi0 ξ t ((ξ.F.obj 0).sc t).moduleCatCyclesIso.hom v`.

Proof sketch: given `q : ↥(Zof ξ t) ⧸ VZ ξ t 1`, take `x0 : ↥(Zof ξ t)` with `(VZ ξ t 1).mkQ x0 = q` (`Submodule.mkQ_surjective`); `Submodule.mem_inf.mp x0.2` gives `dC C t (t-1) x0.1 = 0` and `x0.1 ∈ Fch ξ 0 t = LinearMap.range (Cincl ξ 0 t)`, so `x0.1 = Cincl ξ 0 t y`; `Cincl_dFs ξ 0 t y` plus `Cincl_injective ξ 0 (t-1)` give `dFs ξ 0 t (t-1) y = 0`, hence `((ξ.F.obj 0).sc t).g.hom y = 0` via `HomologicalComplex.shortComplexFunctor_obj_g` and `next_eq_down`; then `⟨y,_⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)` and `chi ξ t (((ξ.F.obj 0).sc t).homologyπ (((...).moduleCatCyclesIso).inv ⟨y,_⟩)) = psi0 ξ t ⟨y,_⟩ = (VZ ξ t 1).mkQ ⟨Cincl ξ 0 t y, _⟩ = q` using `chi_apply`, `Iso.inv_hom_id_apply`, `psi0_apply`, `valK_mk`, `tau2LM_eq`. Conclude with `LinearMap.range_eq_top`. -/
theorem range_chi {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (t : ℕ) :
    LinearMap.range (Work.SSS.E2Zero.chi ξ t) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro q
  obtain ⟨x0, hx0⟩ := Submodule.mkQ_surjective (VZ ξ t 1) q
  obtain ⟨hker, hfch⟩ := Submodule.mem_inf.mp x0.2
  have hker' : dC C t (t - 1) x0.1 = 0 := hker
  obtain ⟨y, hy⟩ : ∃ y : ↥((ξ.F.obj 0).X t), Cincl ξ 0 t y = x0.1 := hfch
  have hyc : dFs ξ 0 t (t - 1) y = 0 := by
    have h := Cincl_dFs ξ 0 t y
    have h2 : Cincl ξ 0 (t - 1) (dFs ξ 0 t (t - 1) y) = 0 := by
      rw [← h, hy, hker']
    exact Cincl_injective ξ 0 (t - 1) (by rw [h2, map_zero])
  have hyg : ((ξ.F.obj 0).sc t).g.hom y = 0 := by
    show (ModuleCat.Hom.hom ((ξ.F.obj 0).d t ((ComplexShape.down ℕ).next t))) y = 0
    rw [next_eq_down]
    exact hyc
  refine ⟨((ξ.F.obj 0).sc t).homologyπ
      (((ξ.F.obj 0).sc t).moduleCatCyclesIso.inv
        (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))), ?_⟩
  have hv : ((ξ.F.obj 0).sc t).moduleCatCyclesIso.hom
      (((ξ.F.obj 0).sc t).moduleCatCyclesIso.inv
        (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)))
      = (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)) :=
    Iso.inv_hom_id_apply _ _
  have hval : valK (ξ.F.obj 0) t (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))
      = tau2LM (ξ.F.obj 0) t y := valK_mk (ξ.F.obj 0) t y hyg
  calc chi ξ t (((ξ.F.obj 0).sc t).homologyπ
          (((ξ.F.obj 0).sc t).moduleCatCyclesIso.inv
            (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))))
      = psi0 ξ t (((ξ.F.obj 0).sc t).moduleCatCyclesIso.hom
          (((ξ.F.obj 0).sc t).moduleCatCyclesIso.inv
            (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)))) :=
        chi_apply ξ t _
    _ = psi0 ξ t (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)) := by rw [hv]
    _ = Submodule.mkQ (VZ ξ t 1)
          ⟨Cincl ξ 0 t (valK (ξ.F.obj 0) t
            (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))), by
              refine ⟨?_, ?_⟩
              · show dC C t (t - 1) (Cincl ξ 0 t (valK (ξ.F.obj 0) t
                  (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K)))) = 0
                rw [Cincl_dFs,
                  show dFs ξ 0 t (t - 1) (valK (ξ.F.obj 0) t
                      (⟨y, hyg⟩ : ↥(((ξ.F.obj 0).sc t).moduleCatLeftHomologyData.K))) = 0 from
                    valK_isCycle (ξ.F.obj 0) t _, map_zero]
              · exact ⟨valK (ξ.F.obj 0) t _, rfl⟩⟩ := psi0_apply ξ t _
    _ = Submodule.mkQ (VZ ξ t 1) x0 := by
          refine congrArg (Submodule.mkQ (VZ ξ t 1)) (Subtype.ext ?_)
          show Cincl ξ 0 t (valK (ξ.F.obj 0) t ⟨y, hyg⟩) = (x0.1 : C.X t)
          rw [hval]
          exact hy
    _ = q := hx0

end

end Work.SSS.E2Zero
