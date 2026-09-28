import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.ModelIncl.Zs_le_Zsq
import Submission.Work.SSS.Transgression.vzQuotAux

namespace Work.SSS.E2Zero

open CategoryTheory CategoryTheory.Limits

/-- The inclusion `F_0 ⟶ C` factors through the inclusion `F_0 ⟶ F_1`: on elements,
`Cincl ξ 0 n y = Cincl ξ 1 n ((incF ξ.F 0).f n y)`. -/
theorem Cincl_zero_eq {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (n : ℕ)
    (y : (ξ.F.obj 0).X n) :
    Work.SSS.Cincl ξ 0 n y = Work.SSS.Cincl ξ 1 n ((Work.SSS.incF ξ.F 0).f n y) := by
  have hfin : Work.SSS.Finc ξ 0 1 (Nat.zero_le 1) n y = (Work.SSS.incF ξ.F 0).f n y := by
    have hm : homOfLE (Nat.zero_le 1) = homOfLE (Nat.le_succ 0) := Subsingleton.elim _ _
    simp only [Work.SSS.Finc, Work.SSS.incF, hm]
  rw [← hfin, ← Work.SSS.Transgression.Cincl_Finc_apply ξ (Nat.zero_le 1) n y]

/-- A cycle `z` of `F_0` in degree `t` has its `Cincl`-image in `V ξ t 1` (the `∂`-images of `F_1`-chains that lie in `Z_t(F_0)`) exactly when `z` is the boundary of a chain of `F_1` in degree `t+1`.
Roadmap.  `Cincl ξ 0 t z = Cincl ξ 1 t ((incF ξ.F 0).f t z)` because `ξ.incl 0` factors as `ξ.F.map (homOfLE (Nat.zero_le 1)) ≫ ξ.incl 1` (`Filtration.compat`, and `incF ξ.F 0 = ξ.F.map (homOfLE (Nat.le_succ 0))` is definitionally the same map); `dC C (t+1) t ∘ Cincl ξ 1 (t+1) = Cincl ξ 1 t ∘ dFs ξ 1 (t+1) t` because `ξ.incl 1` is a chain map (`HomologicalComplex.Hom.comm`, plus `ConcreteCategory.congr_hom` and `HomologicalComplex.comp_f`); and `Cincl ξ 1 t` is injective because `ξ.mono_incl 1` is a monomorphism of chain complexes: use `haveI := ξ.mono_incl 1` together with the instance `[Mono φ] → Mono (φ.f n)` for morphisms of chain complexes and `ModuleCat.mono_iff_injective`.  The `Zof ξ t` half of the intersection is automatic from `hz` and the chain-map property of `ξ.incl 0`.  Use `Work.SSS.mem_Fch` to unfold membership in `Fch`. -/
theorem Cincl_mem_V_one_iff {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (t : ℕ)
    (z : (ξ.F.obj 0).X t) (hz : (ξ.F.obj 0).d t (t - 1) z = 0) :
    Work.SSS.Cincl ξ 0 t z ∈ Work.SSS.V ξ t 1 ↔
      ∃ w : (ξ.F.obj 1).X (t + 1),
        Work.SSS.dFs ξ 1 (t + 1) t w = (Work.SSS.incF ξ.F 0).f t z := by
  have hc : Work.SSS.Cincl ξ 0 t z = Work.SSS.Cincl ξ 1 t ((Work.SSS.incF ξ.F 0).f t z) :=
    Cincl_zero_eq ξ t z
  constructor
  · intro h
    rw [Work.SSS.V, Submodule.mem_inf] at h
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp h.1
    rw [Work.SSS.mem_Fch] at hy
    obtain ⟨v, hv⟩ := hy
    refine ⟨v, Work.SSS.ModelIncl.Cincl_injective ξ 1 t ?_⟩
    rw [Work.SSS.Transgression.Cincl_dFs_apply, hv, hyz, hc]
  · rintro ⟨w, hw⟩
    rw [Work.SSS.V, Submodule.mem_inf]
    constructor
    · rw [Submodule.mem_map]
      refine ⟨Work.SSS.Cincl ξ 1 (t + 1) w, ?_, ?_⟩
      · rw [Work.SSS.mem_Fch]; exact ⟨w, rfl⟩
      · rw [← Work.SSS.Transgression.Cincl_dFs_apply, hw, hc]
    · rw [Work.SSS.Zof, Submodule.mem_inf]
      constructor
      · rw [LinearMap.mem_ker]
        have hd : Work.SSS.dFs ξ 0 t (t - 1) z = 0 := hz
        rw [← Work.SSS.Transgression.Cincl_dFs_apply ξ 0 t (t - 1) z, hd, map_zero]
      · rw [Work.SSS.mem_Fch]; exact ⟨z, rfl⟩

end Work.SSS.E2Zero
