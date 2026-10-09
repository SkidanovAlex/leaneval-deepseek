import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open LinearMap Module Submodule

namespace Work.SSGRoute.ZDataMup

/-- Helper: the left radical `B.ker` and the right radical `B.orthogonal ⊤` have equal
dimension, by the rank–nullity identity `finrank_add_finrank_orthogonal'` applied to `⊤`. -/
theorem finrank_ker_eq_finrank_orthogonal_top {K' V : Type} [Field K'] [AddCommGroup V]
    [Module K' V] [FiniteDimensional K' V] (B : LinearMap.BilinForm K' V) :
    finrank K' ↥(B.orthogonal ⊤) = finrank K' ↥(B.ker) := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) (⊤ : Submodule K' V)
  rw [finrank_top K' V, top_inf_eq] at h
  omega

/-- Helper: dimension of the image of `U` in `V ⧸ V₀` when `V₀ ≤ U`. -/
theorem finrank_map_mkQ_eq {K' V : Type} [Field K'] [AddCommGroup V] [Module K' V]
    [FiniteDimensional K' V] (V₀ U : Submodule K' V) (h : V₀ ≤ U) :
    finrank K' ↥(U.map (Submodule.mkQ V₀)) = finrank K' ↥U - finrank K' ↥V₀ := by
  have hkey := LinearMap.finrank_range_add_finrank_ker ((Submodule.mkQ V₀).domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hkey
  have hkerfin : finrank K' ↥(Submodule.comap U.subtype V₀) = finrank K' ↥V₀ := by
    have h' := Submodule.finrank_map_subtype_eq U (Submodule.comap U.subtype V₀)
    rw [Submodule.map_comap_subtype] at h'
    rw [inf_eq_right.mpr h] at h'
    exact h'.symm
  rw [hkerfin] at hkey
  exact Nat.eq_sub_of_add_eq hkey

theorem orthogonal_le_sup_of_ker_le {K' V : Type} [Field K'] [AddCommGroup V] [Module K' V]
    [FiniteDimensional K' V] (B : LinearMap.BilinForm K' V) (V₀ W : Submodule K' V)
    (hkerL : B.ker ≤ V₀) (hkerR : V₀ ≤ B.orthogonal ⊤) (hiso : W ≤ B.orthogonal W)
    (hcount : Module.finrank K' (V ⧸ V₀) ≤
      2 * Module.finrank K' ((W ⊔ V₀).map (Submodule.mkQ V₀))) :
    B.orthogonal W ≤ W ⊔ V₀ := by
  -- The hypotheses force `V₀` to be the two-sided radical `B.ker = B.orthogonal ⊤`.
  have hker_eq : B.ker = V₀ := by
    have h1 : finrank K' ↥V₀ ≤ finrank K' ↥(B.ker) :=
      (finrank_ker_eq_finrank_orthogonal_top B) ▸ Submodule.finrank_mono hkerR
    have h2 : finrank K' ↥(B.ker) ≤ finrank K' ↥V₀ := Submodule.finrank_mono hkerL
    exact Submodule.eq_of_le_of_finrank_eq hkerL (le_antisymm h2 h1)
  -- `W ⊔ V₀` is contained in the orthogonal complement of `W`.
  have hge : W ⊔ V₀ ≤ B.orthogonal W :=
    sup_le hiso (hkerR.trans (LinearMap.BilinForm.orthogonal_le le_top))
  -- Dimension count: `finrank (B.orthogonal W) ≤ finrank (W ⊔ V₀)`.
  have hle : finrank K' ↥(B.orthogonal W) ≤ finrank K' ↥(W ⊔ V₀) := by
    have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) W
    rw [hker_eq] at h1
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq W V₀
    have h3 := Submodule.finrank_quotient_add_finrank V₀
    have h4 := finrank_map_mkQ_eq V₀ (W ⊔ V₀) le_sup_right
    have hInf_le : finrank K' ↥(W ⊓ V₀) ≤ finrank K' ↥W := Submodule.finrank_mono inf_le_left
    have hV₀_le : finrank K' ↥V₀ ≤ finrank K' ↥(W ⊔ V₀) := Submodule.finrank_mono le_sup_right
    have hW_le : finrank K' ↥W ≤ finrank K' V :=
      (Submodule.finrank_mono (s := W) (t := ⊤) le_top).trans (le_of_eq (finrank_top K' V))
    omega
  have heq : W ⊔ V₀ = B.orthogonal W :=
    Submodule.eq_of_le_of_finrank_eq hge (le_antisymm (Submodule.finrank_mono hge) hle)
  exact heq.ge

end Work.SSGRoute.ZDataMup
