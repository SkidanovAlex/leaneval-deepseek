import Mathlib
import Submission.Work.SSGRoute.ZDataMup.orthogonal_le_sup_of_ker_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open LinearMap Module Submodule

theorem orthogonal_le_sup_of_ker_le_quotient {K' V : Type} [Field K'] [AddCommGroup V]
    [Module K' V] (V₀ : Submodule K' V) [Module.Finite K' (V ⧸ V₀)]
    (B : LinearMap.BilinForm K' V) (W : Submodule K' V)
    (hkerL : B.ker ≤ V₀) (hkerL' : V₀ ≤ B.ker) (hkerR : V₀ ≤ B.orthogonal ⊤)
    (hiso : W ≤ (B.flip).orthogonal W)
    (hcount : Module.finrank K' (V ⧸ V₀) ≤
      2 * Module.finrank K' ((W ⊔ V₀).map (Submodule.mkQ V₀))) :
    (B.flip).orthogonal W ≤ W ⊔ V₀ := by
  -- `V₀` lies in the right radical, so `B` descends to the quotient `V ⧸ V₀`.
  have hright : V₀ ≤ B.flip.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    rw [LinearMap.BilinForm.flip_apply, LinearMap.zero_apply]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (hkerR hx) y mem_top
  let BQ : LinearMap.BilinForm K' (V ⧸ V₀) := LinearMap.liftQ₂ V₀ V₀ B hkerL' hright
  have hBQ : ∀ x y : V, BQ (Submodule.mkQ V₀ x) (Submodule.mkQ V₀ y) = B x y := by
    intro x y
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact LinearMap.liftQ₂_mk hkerL' hright x y
  -- The left radical of the descended form is trivial.
  have hBQker : BQ.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ā hā
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective V₀ ā
    have hā' : BQ (Submodule.mkQ V₀ z) = 0 := LinearMap.mem_ker.mp hā
    have hz : ∀ y : V, B z y = 0 := by
      intro y
      have h := LinearMap.congr_fun hā' (Submodule.mkQ V₀ y)
      rw [LinearMap.zero_apply, hBQ z y] at h
      exact h
    have hzker : z ∈ B.ker := by
      rw [LinearMap.mem_ker]
      ext y
      exact hz y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkerL hzker
  -- `W ⊔ V₀` is totally isotropic.
  have hW'W' : ∀ x ∈ W ⊔ V₀, ∀ y ∈ W ⊔ V₀, B x y = 0 := by
    intro x hx y hy
    obtain ⟨wa, hwa, va, hva, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨wb, hwb, vb, hvb, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : B wa wb = 0 := by
      rw [← LinearMap.BilinForm.flip_apply B wb wa]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp (hiso hwa) wb hwb
    have h2 : B wa vb = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp (hkerR hvb) wa mem_top
    have h3 : B va = 0 := LinearMap.mem_ker.mp (hkerL' hva)
    have h4 : B va wb = 0 := by rw [h3, LinearMap.zero_apply]
    have h5 : B va vb = 0 := by rw [h3, LinearMap.zero_apply]
    simp only [map_add, LinearMap.add_apply, h1, h2, h4, h5, add_zero]
  -- Isotropy descends to the quotient.
  have hiso' : (W ⊔ V₀).map (Submodule.mkQ V₀) ≤
      (BQ.flip).orthogonal ((W ⊔ V₀).map (Submodule.mkQ V₀)) := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    rw [LinearMap.BilinForm.flip_apply, hBQ]
    exact hW'W' x hx y hy
  -- The right radical of the descended form is its right orthogonal, computed by rank-nullity.
  have hflip_eq : (BQ.flip).ker = BQ.orthogonal ⊤ := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hx y _
      have h := LinearMap.congr_fun hx y
      rwa [LinearMap.zero_apply, LinearMap.BilinForm.flip_apply] at h
    · intro hx
      exact LinearMap.ext (fun y => by
        rw [LinearMap.BilinForm.flip_apply, LinearMap.zero_apply]
        exact hx y mem_top)
  have hflipker : (BQ.flip).ker = ⊥ := by
    rw [hflip_eq]
    have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BQ)
      (⊤ : Submodule K' (V ⧸ V₀))
    rw [finrank_top, hBQker, top_inf_eq, finrank_bot, add_zero] at h1
    have h2 : Module.finrank K' ↥(BQ.orthogonal ⊤) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h2
  -- Maximality of the isotropic subspace in the quotient.
  have key : (BQ.flip).orthogonal ((W ⊔ V₀).map (Submodule.mkQ V₀)) =
      (W ⊔ V₀).map (Submodule.mkQ V₀) := by
    have h2 : Module.finrank K' ↥((BQ.flip).orthogonal ((W ⊔ V₀).map (Submodule.mkQ V₀))) ≤
        Module.finrank K' ↥((W ⊔ V₀).map (Submodule.mkQ V₀)) := by
      have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := BQ.flip)
        ((W ⊔ V₀).map (Submodule.mkQ V₀))
      rw [hflipker, inf_bot_eq, finrank_bot, add_zero] at h1
      omega
    exact (Submodule.eq_of_le_of_finrank_le hiso' h2).symm
  -- Transport back along `V → V ⧸ V₀`.
  intro y hy
  have hy0 : ∀ z ∈ W ⊔ V₀, B y z = 0 := by
    intro z hz
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    have h1 : B y w = 0 := by
      rw [← LinearMap.BilinForm.flip_apply B w y]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp hy w hw
    have h2 : B y v = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp (hkerR hv) y mem_top
    rw [map_add, h1, h2, add_zero]
  have hy' : Submodule.mkQ V₀ y ∈ (W ⊔ V₀).map (Submodule.mkQ V₀) := by
    rw [← key, LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hb
    rw [LinearMap.BilinForm.flip_apply, hBQ]
    exact hy0 z hz
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
  have hsub : Submodule.mkQ V₀ (z - y) = 0 := by
    rw [map_sub, hzy, sub_self]
  have hzy_mem : z - y ∈ V₀ := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hsub
    exact hsub
  have hyz : y - z ∈ V₀ := by
    rw [← neg_sub z y]
    exact neg_mem hzy_mem
  have hmem : z + (y - z) ∈ W ⊔ V₀ := add_mem hz (Submodule.mem_sup_right hyz)
  rwa [add_sub_cancel] at hmem

end Work.SSGRoute.ZDataMup
