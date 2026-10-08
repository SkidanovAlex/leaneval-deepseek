import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

theorem map_eq_iff_mapQ_map_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (X : Submodule (ZMod 2) V) (h : V ≃ₗ[ZMod 2] V)
    (T : (V ⧸ X) ≃ₗ[ZMod 2] (V ⧸ X)) (hT : ∀ x : V, T (X.mkQ x) = X.mkQ (h x))
    (Z : Submodule (ZMod 2) V) (hZ : X ≤ Z) :
    Z.map (h : V →ₗ[ZMod 2] V) = Z ↔
      (Z.map X.mkQ).map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) = Z.map X.mkQ := by
  -- `mkQ` vanishes exactly on `X`.
  have mkQ_eq_zero_iff : ∀ y : V, X.mkQ y = 0 ↔ y ∈ X := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- `T` intertwines `h` with the quotient map.
  have hcomm : (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)).comp (X.mkQ)
      = (X.mkQ).comp (h : V →ₗ[ZMod 2] V) := by
    apply LinearMap.ext
    intro x
    exact hT x
  -- the same relation for the inverses.
  have hcomm' : (T.symm : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)).comp (X.mkQ)
      = (X.mkQ).comp (h.symm : V →ₗ[ZMod 2] V) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    have hx : T (X.mkQ (h.symm x)) = X.mkQ x := by
      rw [hT (h.symm x), LinearEquiv.apply_symm_apply]
    rw [← hx]
    exact LinearEquiv.symm_apply_apply T (X.mkQ ((h.symm : V →ₗ[ZMod 2] V) x))
  -- If an endomorphism `f` of `V` descends to the quotient, it maps `X` into `X`.
  have key_lem : ∀ (U : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) (f : V →ₗ[ZMod 2] V),
      U.comp (X.mkQ) = (X.mkQ).comp f → X.map f ≤ X := by
    intro U f hU
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    have h1 : U (X.mkQ x) = X.mkQ (f x) := LinearMap.congr_fun hU x
    have hz : X.mkQ (f x) = 0 := by
      rw [← h1, (mkQ_eq_zero_iff x).mpr hx]
      simp
    exact (mkQ_eq_zero_iff (f x)).mp hz
  have hXle : X.map (h : V →ₗ[ZMod 2] V) ≤ X :=
    key_lem (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) (h : V →ₗ[ZMod 2] V) hcomm
  have hXle' : X.map (h.symm : V →ₗ[ZMod 2] V) ≤ X :=
    key_lem (T.symm : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) (h.symm : V →ₗ[ZMod 2] V) hcomm'
  -- hence `h` preserves `X`.
  have hXmap : X.map (h : V →ₗ[ZMod 2] V) = X := by
    refine le_antisymm hXle ?_
    intro x hx
    rw [Submodule.mem_map]
    refine ⟨(h.symm : V →ₗ[ZMod 2] V) x, ?_, ?_⟩
    · exact hXle' (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    · show (h : V →ₗ[ZMod 2] V) (h.symm x) = x
      exact h.apply_symm_apply x
  -- the quotient map kills `X`.
  have hmkQker : X.map (X.mkQ) = ⊥ := by
    have h1 := Submodule.map_comap_eq (X.mkQ) (⊥ : Submodule (ZMod 2) (V ⧸ X))
    rw [Submodule.comap_bot, Submodule.range_mkQ, top_inf_eq, Submodule.ker_mkQ] at h1
    exact h1
  -- push `T` through the composite `mkQ ∘ h`.
  have hmap : (Z.map (X.mkQ)).map (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X))
      = (Z.map (h : V →ₗ[ZMod 2] V)).map (X.mkQ) := by
    rw [← Submodule.map_comp (X.mkQ) (T : (V ⧸ X) →ₗ[ZMod 2] (V ⧸ X)) Z, hcomm,
      Submodule.map_comp (h : V →ₗ[ZMod 2] V) (X.mkQ) Z]
  -- `T` fixes `Z ⧸ X` exactly when `h` fixes `Z` modulo `X`.
  have hkey : (Z.map (h : V →ₗ[ZMod 2] V)).map (X.mkQ) = Z.map (X.mkQ)
      ↔ Z.map (h : V →ₗ[ZMod 2] V) ⊔ X = Z ⊔ X := by
    constructor
    · intro hQ
      have hcomap1 : Submodule.comap (X.mkQ) (Submodule.map (X.mkQ) (Z.map (h : V →ₗ[ZMod 2] V)))
          = Z.map (h : V →ₗ[ZMod 2] V) ⊔ X := by
        rw [Submodule.comap_map_eq, Submodule.ker_mkQ]
      have hcomap2 : Submodule.comap (X.mkQ) (Submodule.map (X.mkQ) Z) = Z ⊔ X := by
        rw [Submodule.comap_map_eq, Submodule.ker_mkQ]
      have h1 := congrArg (Submodule.comap (X.mkQ)) hQ
      rw [hcomap1, hcomap2] at h1
      exact h1
    · intro hH
      have h1 := congrArg (Submodule.map (X.mkQ)) hH
      simpa [Submodule.map_sup, hmkQker] using h1
  -- since `h X = X` and `X ≤ Z`, the condition `h Z ⊔ X = Z ⊔ X` is `h Z = Z`.
  have hsupmap : Z.map (h : V →ₗ[ZMod 2] V) ⊔ X = Z.map (h : V →ₗ[ZMod 2] V) := by
    rw [← hXmap, ← Submodule.map_sup, sup_eq_left.mpr hZ]
  have hsupZ : Z ⊔ X = Z := sup_eq_left.mpr hZ
  have hmid : ((Z.map (h : V →ₗ[ZMod 2] V)).map (X.mkQ) = Z.map (X.mkQ))
      ↔ Z.map (h : V →ₗ[ZMod 2] V) = Z := by
    rw [hkey, hsupmap, hsupZ]
  rw [hmap]
  exact hmid.symm

end Work.Hering.Wagner
