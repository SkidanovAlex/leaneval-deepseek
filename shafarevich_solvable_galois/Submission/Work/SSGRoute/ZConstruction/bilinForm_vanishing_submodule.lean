import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open Module

/-- A **finite-dimensional** `ZMod p`-vector space `V` with a submodule `U` of dimension at most half
of `dim V` carries a bilinear form which is non-degenerate in its first variable and vanishes on
`U × U`.  (The finite-dimensionality is needed: `Module.finrank` vanishes on infinite-dimensional
modules, so without it `U = ⊤` would be a counterexample.) -/
theorem bilinForm_vanishing_submodule (p : ℕ) [Fact p.Prime]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (U : Submodule (ZMod p) V)
    (hdim : 2 * Module.finrank (ZMod p) U ≤ Module.finrank (ZMod p) V) :
    ∃ F : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p,
      (∀ x : V, (∀ y : V, F x y = 0) → x = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, F x y = 0) := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  have hadd : Module.finrank (ZMod p) U + Module.finrank (ZMod p) W
      = Module.finrank (ZMod p) V := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hW.sup_eq_top, hW.inf_eq_bot] at h
    simpa using h.symm
  have hle : Module.finrank (ZMod p) U ≤ Module.finrank (ZMod p) W := by omega
  let R := Fin (Module.finrank (ZMod p) W - Module.finrank (ZMod p) U) → ZMod p
  have hRfin : Module.finrank (ZMod p) R
      = Module.finrank (ZMod p) W - Module.finrank (ZMod p) U :=
    Module.finrank_fin_fun (ZMod p)
  have hUR : Module.finrank (ZMod p) (U × R) = Module.finrank (ZMod p) W := by
    rw [Module.finrank_prod, hRfin]
    omega
  obtain ⟨ψ0⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hUR
  let ψ : W ≃ₗ[ZMod p] (U × R) := ψ0.symm
  let eW : V ≃ₗ[ZMod p] U × W := (Submodule.prodEquivOfIsCompl U W hW).symm
  let Φ : V ≃ₗ[ZMod p] (U × (U × R)) :=
    eW.trans (LinearEquiv.prodCongr (LinearEquiv.refl (ZMod p) U) ψ)
  let φ : U ≃ₗ[ZMod p] Module.Dual (ZMod p) U := (Module.finBasis (ZMod p) U).toDualEquiv
  let φ₃ : R ≃ₗ[ZMod p] Module.Dual (ZMod p) R := (Module.finBasis (ZMod p) R).toDualEquiv
  let π₁ : (U × (U × R)) →ₗ[ZMod p] U := LinearMap.fst (ZMod p) U (U × R)
  let π₂ : (U × (U × R)) →ₗ[ZMod p] U :=
    (LinearMap.fst (ZMod p) U R).comp (LinearMap.snd (ZMod p) U (U × R))
  let π₃ : (U × (U × R)) →ₗ[ZMod p] R :=
    (LinearMap.snd (ZMod p) U R).comp (LinearMap.snd (ZMod p) U (U × R))
  let T₁ : (U × (U × R)) →ₗ[ZMod p] (U × (U × R)) →ₗ[ZMod p] ZMod p :=
    π₂.dualMap.comp (φ.toLinearMap.comp π₁)
  let B₃ : (U × (U × R)) →ₗ[ZMod p] (U × (U × R)) →ₗ[ZMod p] ZMod p :=
    π₃.dualMap.comp (φ₃.toLinearMap.comp π₃)
  let F₀ : (U × (U × R)) →ₗ[ZMod p] (U × (U × R)) →ₗ[ZMod p] ZMod p := T₁ + T₁.flip + B₃
  let F : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p := F₀.compl₁₂ Φ.toLinearMap Φ.toLinearMap
  have hF_def : ∀ a b : V, F a b = F₀ (Φ a) (Φ b) := fun a b => rfl
  have hF0_apply : ∀ x y : U × (U × R), F₀ x y
      = φ x.1 (y.2.1) + φ y.1 (x.2.1) + φ₃ x.2.2 (y.2.2) := by
    intro x y
    have hT : T₁ x y = φ x.1 (y.2.1) := by
      simp only [T₁, LinearMap.comp_apply, LinearMap.dualMap_apply, π₁, π₂,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap]
    have hTf : T₁.flip x y = φ y.1 (x.2.1) := by
      rw [LinearMap.flip_apply]
      simp only [T₁, LinearMap.comp_apply, LinearMap.dualMap_apply, π₁, π₂,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap]
    have hB : B₃ x y = φ₃ x.2.2 (y.2.2) := by
      simp only [B₃, LinearMap.comp_apply, LinearMap.dualMap_apply, π₃,
        LinearMap.snd_apply, LinearEquiv.coe_toLinearMap]
    simp only [F₀, LinearMap.add_apply, hT, hTf, hB]
  have hΦU : ∀ u : U, Φ (u : V) = (u, (0 : U × R)) := by
    intro u
    have h1 : eW (u : V) = (u, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U W hW u
    show (LinearEquiv.prodCongr (LinearEquiv.refl (ZMod p) U) ψ) (eW (u : V)) = (u, (0 : U × R))
    rw [h1]
    simp
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    have hF0' : ∀ Y : U × (U × R), F₀ (Φ x) Y = 0 := by
      intro Y
      have h := hx (Φ.symm Y)
      rw [hF_def, LinearEquiv.apply_symm_apply] at h
      exact h
    have ha : (Φ x).1 = 0 := by
      have hφ1 : φ (Φ x).1 = 0 := by
        apply LinearMap.ext
        intro b
        have h2 := hF0' ((0 : U), (b, 0))
        rw [hF0_apply] at h2
        simpa using h2
      exact φ.injective (by simpa using hφ1)
    have hb1 : (Φ x).2.1 = 0 := by
      have h3 : ∀ a' : U, φ a' ((Φ x).2.1) = 0 := by
        intro a'
        have h2 := hF0' ((a', (0, 0)) : U × (U × R))
        rw [hF0_apply] at h2
        simpa using h2
      apply (Module.finBasis (ZMod p) U).eval_injective
      apply LinearMap.ext
      intro ψ'
      simp only [Module.Dual.eval_apply, map_zero]
      obtain ⟨a', ha'⟩ := φ.surjective ψ'
      rw [← ha']
      exact h3 a'
    have hb2 : (Φ x).2.2 = 0 := by
      have hφ3 : φ₃ (Φ x).2.2 = 0 := by
        apply LinearMap.ext
        intro c
        have h2 := hF0' ((0, (0, c)) : U × (U × R))
        rw [hF0_apply] at h2
        simpa using h2
      exact φ₃.injective (by simpa using hφ3)
    have hP : Φ x = 0 := Prod.ext ha (Prod.ext hb1 hb2)
    have hxx : x = Φ.symm (Φ x) := (Φ.symm_apply_apply x).symm
    rw [hxx, hP]
    simp
  · intro x hxU y hyU
    rw [hF_def x y]
    have hx' : Φ x = ((⟨x, hxU⟩ : U), (0 : U × R)) := hΦU ⟨x, hxU⟩
    have hy' : Φ y = ((⟨y, hyU⟩ : U), (0 : U × R)) := hΦU ⟨y, hyU⟩
    rw [hx', hy', hF0_apply]
    simp

end Work.SSGRoute.ZConstruction
