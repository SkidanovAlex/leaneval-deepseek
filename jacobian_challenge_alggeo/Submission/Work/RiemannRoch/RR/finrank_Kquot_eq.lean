import Mathlib
import Submission.Work.RiemannRoch.Quotients

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.RiemannRoch.RR

open Work.RiemannRoch.Curve

universe u

/-- Auxiliary linear-algebra fact: for an injective linear map `s : W →ₗ V` and submodules
`M ≤ N` of `W`, the quotient `(N.map s) / (M.map s)` computed inside `V` is linearly
equivalent to the image of `N` under the projection `W → W ⧸ M`. -/
lemma finrank_quot_map_subtype {k : Type u} [Field k] {W V : Type u}
    [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : W →ₗ[k] V) (hs : Function.Injective s) {M N : Submodule k W} (hMN : M ≤ N) :
    Module.finrank k (↥(N.map s) ⧸ (M.map s).comap (N.map s).subtype)
      = Module.finrank k ↥(N.map (Submodule.mkQ M)) := by
  let fN : ↥N →ₗ[k] ↥(N.map s) :=
    { toFun := fun x => ⟨s x, Submodule.mem_map_of_mem (f := s) x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let t : ↥N →ₗ[k] ↥(N.map s) ⧸ (M.map s).comap (N.map s).subtype :=
    (Submodule.mkQ _).comp fN
  have ht : Function.Surjective t := by
    intro y
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨n, hn, hsn⟩ := Submodule.mem_map.mp y'.2
    refine ⟨⟨n, hn⟩, ?_⟩
    have hfx : fN ⟨n, hn⟩ = y' := by
      refine Subtype.ext ?_
      show s n = (y' : V)
      rw [hsn]
    show (Submodule.mkQ _) (fN ⟨n, hn⟩) = (Submodule.mkQ _) y'
    rw [hfx]
  have hker : LinearMap.ker t = M.comap N.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    constructor
    · intro hx
      have hx' : fN x ∈ (M.map s).comap (N.map s).subtype := by
        simpa only [t, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] using hx
      have hx'' : s (x : W) ∈ M.map s := by
        rw [Submodule.mem_comap] at hx'
        exact hx'
      obtain ⟨m, hm, hsm⟩ := Submodule.mem_map.mp hx''
      have hmx : m = (x : W) := hs hsm
      rwa [hmx] at hm
    · intro hx
      have hx'' : s (x : W) ∈ M.map s := ⟨x, hx, rfl⟩
      have hx' : fN x ∈ (M.map s).comap (N.map s).subtype := by
        rw [Submodule.mem_comap]
        exact hx''
      simpa only [t, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] using hx'
  have e1 : (↥N ⧸ M.comap N.subtype) ≃ₗ[k]
      (↥(N.map s) ⧸ (M.map s).comap (N.map s).subtype) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (t.quotKerEquivOfSurjective ht)
  let ψ : ↥N →ₗ[k] W ⧸ M := (Submodule.mkQ M).comp N.subtype
  have hψker : LinearMap.ker ψ = M.comap N.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    constructor
    · intro hx
      simpa only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] using hx
    · intro hx
      simpa only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] using hx
  have hψrange : LinearMap.range ψ = N.map (Submodule.mkQ M) := by
    change LinearMap.range ((Submodule.mkQ M).comp N.subtype) = N.map (Submodule.mkQ M)
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e2 : (↥N ⧸ M.comap N.subtype) ≃ₗ[k] ↥(N.map (Submodule.mkQ M)) :=
    ((Submodule.quotEquivOfEq _ _ hψker.symm).trans ψ.quotKerEquivRange).trans
      (LinearEquiv.ofEq _ _ hψrange)
  exact (e1.symm.trans e2).finrank_eq

theorem finrank_Kquot_eq {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    Module.finrank k (Work.RiemannRoch.Curve.Kquot C D E)
      = Module.finrank k ↥(Work.RiemannRoch.Curve.KquotAd C D E) := by
  have hAsub : ∀ F : C.Div, (Asub C F).map (Adeles C).subtype = A C F := by
    intro F
    rw [Asub, Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.mpr (A_le_adeles C F)
  have hdiag : (diagK C).map (Adeles C).subtype = Kdiag C := by
    have hc : (Adeles C).subtype.comp (diag C) = diagFn C := by
      ext a Q
      rfl
    rw [diagK, Kdiag, ← LinearMap.range_comp, hc]
  have hmap : ∀ F : C.Div,
      (Asub C F ⊔ diagK C).map (Adeles C).subtype = A C F ⊔ Kdiag C := by
    intro F
    rw [Submodule.map_sup, hAsub F, hdiag]
  have hMN : Asub C D ⊔ diagK C ≤ Asub C E ⊔ diagK C :=
    sup_le_sup (Submodule.comap_mono (A_mono C h)) le_rfl
  have key := finrank_quot_map_subtype (Adeles C).subtype (Submodule.subtype_injective _) hMN
  rw [hmap E, hmap D] at key
  exact key

end Work.RiemannRoch.RR
