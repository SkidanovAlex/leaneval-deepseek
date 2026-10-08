import Mathlib
import Submission.Work.Hering.Wagner.card_inv_hyp_eq_card_inv_line
import Submission.Work.Hering.Wagner.map_eq_iff_mapQ_map_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.Wagner

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Rank–nullity for the quotient map `V → V ⧸ W`: if `W ≤ T` then
`finrank (T.map W.mkQ) + finrank W = finrank T`. -/
private theorem finrank_map_mkQ_add (W T : Submodule (ZMod 2) V) (hWT : W ≤ T) :
    Module.finrank (ZMod 2) (T.map W.mkQ) + Module.finrank (ZMod 2) W
      = Module.finrank (ZMod 2) T := by
  have hfin := LinearMap.finrank_range_add_finrank_ker ((W.mkQ).domRestrict T)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hfin
  rw [← hfin]; congr 1
  rw [← Submodule.finrank_map_subtype_eq T (Submodule.comap T.subtype W.mkQ.ker), Submodule.ker_mkQ,
      Submodule.map_comap_subtype, inf_eq_right.mpr hWT]

theorem card_fixed_hyp_above_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Module.Finite (ZMod 2) V] (X : Submodule (ZMod 2) V) (h : V ≃ₗ[ZMod 2] V)
    (hX : X.map (h : V →ₗ[ZMod 2] V) = X) :
    Nat.card {Z : Submodule (ZMod 2) V //
        X ≤ Z ∧ Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
          Z.map (h : V →ₗ[ZMod 2] V) = Z}
      = Nat.card {Y : Submodule (ZMod 2) V //
        X ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
          Y.map (h : V →ₗ[ZMod 2] V) = Y} := by
  classical
  haveI : Finite (V ⧸ X) := Finite.of_surjective X.mkQ (Submodule.mkQ_surjective X)
  -- The automorphism of `V ⧸ X` induced by `h`.
  have hle : X ≤ Submodule.comap (h : V →ₗ[ZMod 2] V) X :=
    Submodule.map_le_iff_le_comap.mp (le_of_eq hX)
  let T₀ : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X) := X.mapQ X (h : V →ₗ[ZMod 2] V) hle
  have hT₀ : ∀ x : V, T₀ (X.mkQ x) = X.mkQ (h x) := fun x => Submodule.mapQ_apply _ _ _ x
  have hsurj : Function.Surjective T₀ := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective X y
    exact ⟨X.mkQ (h.symm v), by rw [hT₀]; simp⟩
  have hinj : Function.Injective T₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hsurj
  let T : (V ⧸ X) ≃ₗ[ZMod 2] (V ⧸ X) := LinearEquiv.ofBijective T₀ ⟨hinj, hsurj⟩
  have hT : ∀ x : V, T (X.mkQ x) = X.mkQ (h x) := by
    intro x; change T₀ (X.mkQ x) = X.mkQ (h x); exact hT₀ x
  have hfinW : Module.finrank (ZMod 2) (V ⧸ X) + Module.finrank (ZMod 2) X
      = Module.finrank (ZMod 2) V := Submodule.finrank_quotient_add_finrank X
  have hmap : ∀ H : Submodule (ZMod 2) (V ⧸ X),
      Submodule.map X.mkQ (Submodule.comap X.mkQ H) = H := fun H =>
    Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
  -- Codimension-one invariant subspaces containing `X` correspond to invariant hyperplanes
  -- of `V ⧸ X`.
  have eA : {H : Submodule (ZMod 2) (V ⧸ X) //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (V ⧸ X) ∧
          H.map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = H} ≃
      {Z : Submodule (ZMod 2) V //
        X ≤ Z ∧ Module.finrank (ZMod 2) Z + 1 = Module.finrank (ZMod 2) V ∧
          Z.map (h : V →ₗ[ZMod 2] V) = Z} :=
    { toFun := fun H => ⟨Submodule.comap X.mkQ H.1, by
        refine ⟨Submodule.le_comap_mkQ X H.1, ?_, ?_⟩
        · have h1 := finrank_map_mkQ_add X (Submodule.comap X.mkQ H.1)
            (Submodule.le_comap_mkQ X H.1)
          rw [hmap H.1] at h1
          omega
        · rw [map_eq_iff_mapQ_map_eq X h T hT (Submodule.comap X.mkQ H.1)
            (Submodule.le_comap_mkQ X H.1)]
          rw [hmap H.1]
          exact H.2.2⟩
      invFun := fun Z => ⟨Z.1.map X.mkQ, by
        refine ⟨?_, ?_⟩
        · have h1 := finrank_map_mkQ_add X Z.1 Z.2.1
          omega
        · rw [← map_eq_iff_mapQ_map_eq X h T hT Z.1 Z.2.1]
          exact Z.2.2.2⟩
      left_inv := fun H => Subtype.ext (hmap H.1)
      right_inv := fun Z => Subtype.ext (by
        show Submodule.comap X.mkQ (Z.1.map X.mkQ) = Z.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr Z.2.1]) }
  -- One-dimensional invariant subspaces containing `X` correspond to invariant lines of `V ⧸ X`.
  have eB : {Y : Submodule (ZMod 2) V //
        X ≤ Y ∧ Module.finrank (ZMod 2) Y = Module.finrank (ZMod 2) X + 1 ∧
          Y.map (h : V →ₗ[ZMod 2] V) = Y} ≃
      {P : Submodule (ZMod 2) (V ⧸ X) //
        Module.finrank (ZMod 2) P = 1 ∧
          P.map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = P} :=
    { toFun := fun Y => ⟨Y.1.map X.mkQ, by
        refine ⟨?_, ?_⟩
        · have h1 := finrank_map_mkQ_add X Y.1 Y.2.1
          omega
        · rw [← map_eq_iff_mapQ_map_eq X h T hT Y.1 Y.2.1]
          exact Y.2.2.2⟩
      invFun := fun P => ⟨Submodule.comap X.mkQ P.1, by
        refine ⟨Submodule.le_comap_mkQ X P.1, ?_, ?_⟩
        · have h1 := finrank_map_mkQ_add X (Submodule.comap X.mkQ P.1)
            (Submodule.le_comap_mkQ X P.1)
          rw [hmap P.1] at h1
          omega
        · rw [map_eq_iff_mapQ_map_eq X h T hT (Submodule.comap X.mkQ P.1)
            (Submodule.le_comap_mkQ X P.1)]
          rw [hmap P.1]
          exact P.2.2⟩
      left_inv := fun Y => Subtype.ext (by
        show Submodule.comap X.mkQ (Y.1.map X.mkQ) = Y.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr Y.2.1])
      right_inv := fun P => Subtype.ext (hmap P.1) }
  rw [← Nat.card_congr eA, Nat.card_congr eB]
  exact card_inv_hyp_eq_card_inv_line T

end Work.Hering.Wagner
