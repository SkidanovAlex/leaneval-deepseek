import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

theorem finrank_quot_eq_of_retract {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (ψ : N →ₗ[ℂ] M) (T : M →ₗ[ℂ] N)
    (A : Submodule ℂ M) (B : Submodule ℂ N) (J : Submodule ℂ M) (J' : Submodule ℂ N)
    (hψA : ∀ b ∈ B, ψ b ∈ A) (hTB : ∀ a ∈ A, T a ∈ B)
    (hψJ' : ∀ b, b ∈ J' → ψ b ∈ J) (hTJ : ∀ a, a ∈ J → T a ∈ J')
    (hTψ : ∀ b ∈ B, T (ψ b) = b)
    (hψT : ∀ a ∈ A, ψ (T a) - a ∈ J) :
    Module.finrank ℂ (↥A ⧸ Submodule.comap A.subtype J) =
      Module.finrank ℂ (↥B ⧸ Submodule.comap B.subtype J') := by
  -- The compatible restrictions of `ψ` and `T` to `B` resp. `A`.
  let f : ↥B →ₗ[ℂ] ↥A := LinearMap.codRestrict A (ψ.domRestrict B) (fun b => hψA b.1 b.2)
  let g : ↥A →ₗ[ℂ] ↥B := LinearMap.codRestrict B (T.domRestrict A) (fun a => hTB a.1 a.2)
  have hf_coe : ∀ b : ↥B, (f b : M) = ψ (b : N) := fun b => rfl
  have hg_coe : ∀ a : ↥A, (g a : N) = T (a : M) := fun a => rfl
  -- `g` maps `A ∩ J` into `B ∩ J'` ...
  have hle1 : Submodule.comap A.subtype J ≤ Submodule.comap g (Submodule.comap B.subtype J') := by
    intro a ha
    change (a : M) ∈ J at ha
    change (g a : N) ∈ J'
    rw [hg_coe]
    exact hTJ a.1 ha
  -- ... and conversely `g⁻¹(B ∩ J') ⊆ A ∩ J`.
  have hle2 : Submodule.comap g (Submodule.comap B.subtype J') ≤ Submodule.comap A.subtype J := by
    intro a ha
    change (g a : N) ∈ J' at ha
    rw [hg_coe] at ha
    change (a : M) ∈ J
    have h1 : ψ (T (a : M)) ∈ J := hψJ' (T (a : M)) ha
    have h2 : ψ (T (a : M)) - (a : M) ∈ J := hψT a.1 a.2
    simpa using J.sub_mem h1 h2
  -- `g ∘ f = id` on `B`, because `T ∘ ψ = id` there.
  have hgf : ∀ b : ↥B, g (f b) = b := by
    intro b
    apply Subtype.ext
    rw [hg_coe, hf_coe]
    exact hTψ b.1 b.2
  -- the induced map on quotients
  set φ : ↥A ⧸ Submodule.comap A.subtype J →ₗ[ℂ] ↥B ⧸ Submodule.comap B.subtype J' :=
    (Submodule.comap A.subtype J).mapQ (Submodule.comap B.subtype J') g hle1 with hφ
  -- it is injective, since `comap g B' = A'`
  have hker : LinearMap.ker φ = ⊥ := by
    rw [hφ, Submodule.ker_mapQ]
    have heq : Submodule.comap g (Submodule.comap B.subtype J') = Submodule.comap A.subtype J :=
      le_antisymm hle2 hle1
    rw [heq, Submodule.mkQ_map_self]
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker
  -- it is surjective, since `g ∘ f = id`
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H b =>
      refine ⟨Submodule.Quotient.mk (f b), ?_⟩
      rw [hφ]
      simp only [Submodule.mapQ_apply]
      rw [hgf b]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)

end Work.RB
