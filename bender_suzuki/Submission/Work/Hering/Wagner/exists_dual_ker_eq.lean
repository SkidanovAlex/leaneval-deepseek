import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

theorem exists_dual_ker_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (hV : 0 < Module.finrank (ZMod 2) V)
    (L : Submodule (ZMod 2) V)
    (hL : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) V - 1) :
    ∃ φ : Module.Dual (ZMod 2) V, φ ≠ 0 ∧ LinearMap.ker φ = L := by
  -- The quotient `V ⧸ L` has dimension `1` over `ZMod 2`.
  have hdim : Module.finrank (ZMod 2) (V ⧸ L) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank L
    omega
  -- Hence it is linearly isomorphic to `ZMod 2` itself.
  let e : (V ⧸ L) ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq (V ⧸ L) (ZMod 2) (by rw [hdim, Module.finrank_self])
  refine ⟨(e : (V ⧸ L) →ₗ[ZMod 2] ZMod 2).comp L.mkQ, ?_, ?_⟩
  · -- The composite is surjective, hence nonzero.
    rintro hφ
    obtain ⟨x, hx⟩ : ∃ x : V, ((e : (V ⧸ L) →ₗ[ZMod 2] ZMod 2).comp L.mkQ) x = 1 := by
      obtain ⟨y, hy⟩ := e.surjective 1
      obtain ⟨x, rfl⟩ := L.mkQ_surjective y
      exact ⟨x, by rw [LinearMap.comp_apply]; exact hy⟩
    rw [hφ] at hx
    simp at hx
  · -- The kernel is `L`: `mkQ L` has kernel `L` and `e` is injective.
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

end Work.Hering.Wagner
