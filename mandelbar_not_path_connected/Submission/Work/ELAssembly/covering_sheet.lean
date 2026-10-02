import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Sheet independence for coverings

Auxiliary topological facts for `Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre`.

Given a homeomorphism `H : E ≃ₜ ↥W₀ × I` (the local trivialisation of a covering map over
the base set `W₀`), and a set `A ⊆ E` whose indicator is locally constant, the membership of
`H.symm (w, i)` in `A` is independent of `w` as long as `w` ranges over a *preconnected* subset
of the base.  This is the "same fibre over a connected parameter" phenomenon.

We also record:
* membership in a clopen set is locally constant;
* restriction of `H` to a smaller base set `W ⊆ W₀`, still compatible with `f`.
-/

namespace Work.ELAssembly

open Set

/-- Membership in a clopen set is locally constant. -/
lemma isLocallyConstant_mem_of_isClopen {E : Type*} [TopologicalSpace E] {A : Set E}
    (hA : IsClopen A) : IsLocallyConstant (fun e : E => e ∈ A) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ A
  · exact ⟨A, hA.isOpen, hx, fun x' hx' => propext (iff_of_true hx' hx)⟩
  · exact ⟨Aᶜ, hA.isClosed.isOpen_compl, hx, fun x' hx' => propext (iff_of_false hx' hx)⟩

/-- **Sheet independence.**  Let `H : E ≃ₜ ↥W₀ × I` be a product homeomorphism, `A ⊆ E` a set
whose indicator is locally constant, and `W ⊆ W₀` a preconnected subset of the base.  Then for
every index `i : I`, membership of `H.symm (w, i)` in `A` does not depend on `w ∈ W`. -/
lemma sheet_independence
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {I : Type*} [TopologicalSpace I]
    {W₀ W : Set X} (hW : IsPreconnected W) (hWW₀ : W ⊆ W₀)
    (H : E ≃ₜ ↥W₀ × I) {A : Set E} (hA : IsLocallyConstant (fun e : E => e ∈ A))
    (w₁ w₂ : ↥W) (i : I) :
    H.symm ((⟨w₁.1, hWW₀ w₁.2⟩ : ↥W₀), i) ∈ A ↔
      H.symm ((⟨w₂.1, hWW₀ w₂.2⟩ : ↥W₀), i) ∈ A := by
  haveI := Subtype.preconnectedSpace hW
  have hχ : IsLocallyConstant (fun p : ↥W₀ × I => H.symm p ∈ A) :=
    hA.comp_continuous H.symm.continuous
  have hcont : Continuous (fun w : ↥W => ((⟨w.1, hWW₀ w.2⟩ : ↥W₀), i)) := by fun_prop
  exact Iff.of_eq ((hχ.comp_continuous hcont).apply_eq_of_preconnectedSpace w₁ w₂)

/-- Restriction of a product homeomorphism `↥(f ⁻¹' W₀) ≃ₜ ↥W₀ × I` that is compatible with `f`
to a smaller base set `W ⊆ W₀`. -/
noncomputable def restrictHomeo {f : ℂ → ℂ} (hf : Continuous f) {W W' : Set ℂ} (hW : W ⊆ W')
    {I : Type*} [TopologicalSpace I] (H : ↥(f ⁻¹' W') ≃ₜ ↥W' × I)
    (hH : ∀ e, (H e).1.1 = f e.1) : ↥(f ⁻¹' W) ≃ₜ ↥W × I where
  toFun e := (⟨f e.1, e.2⟩, (H ⟨e.1, hW e.2⟩).2)
  invFun p := ⟨(H.symm (⟨p.1.1, hW p.1.2⟩, p.2)).1, by
    have h1 := hH (H.symm (⟨p.1.1, hW p.1.2⟩, p.2))
    rw [Homeomorph.apply_symm_apply] at h1
    change f (H.symm (⟨p.1.1, hW p.1.2⟩, p.2)).1 ∈ W
    rw [← h1]; exact p.1.2⟩
  left_inv e := by
    simp only []
    apply Subtype.ext
    simp only [Subtype.coe_mk]
    have hpair : ((⟨f e.1, hW e.2⟩ : ↥W'), (H ⟨e.1, hW e.2⟩).2) = H ⟨e.1, hW e.2⟩ :=
      Prod.ext (Subtype.ext (by rw [hH])) rfl
    have hsymm : H.symm ((⟨f e.1, hW e.2⟩ : ↥W'), (H ⟨e.1, hW e.2⟩).2) = ⟨e.1, hW e.2⟩ := by
      rw [hpair, Homeomorph.symm_apply_apply]
    rw [hsymm]
  right_inv p := by
    simp only []
    apply Prod.ext
    · apply Subtype.ext
      have h1 := hH (H.symm (⟨p.1.1, hW p.1.2⟩, p.2))
      rw [Homeomorph.apply_symm_apply] at h1
      exact h1.symm
    · rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The restricted homeomorphism is still compatible with `f`. -/
lemma restrictHomeo_apply {f : ℂ → ℂ} (hf : Continuous f) {W W' : Set ℂ} (hW : W ⊆ W')
    {I : Type*} [TopologicalSpace I] (H : ↥(f ⁻¹' W') ≃ₜ ↥W' × I)
    (hH : ∀ e, (H e).1.1 = f e.1) (e : ↥(f ⁻¹' W)) :
    (restrictHomeo hf hW H hH e).1.1 = f e.1 := rfl

end Work.ELAssembly
