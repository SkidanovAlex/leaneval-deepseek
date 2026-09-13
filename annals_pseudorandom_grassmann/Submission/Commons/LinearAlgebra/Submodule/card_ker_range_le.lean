import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.LinearAlgebra.Submodule.card_hom_subtype
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le

namespace Commons.LinearAlgebra.Submodule

open LinearMap

/-- The linear map `M ⧸ p →ₗ Q` attached to a linear map `f : M →ₗ N` that vanishes on `p`
and whose range lies in `Q`: factor out `p` and corestrict the codomain to `Q`. -/
private noncomputable def liftQCodRestrict {𝕜 : Type*} [Field 𝕜] {M N : Type*}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    (p : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (f : M →ₗ[𝕜] N)
    (h : p ≤ LinearMap.ker f) (h' : LinearMap.range f ≤ Q) : M ⧸ p →ₗ[𝕜] Q :=
  LinearMap.codRestrict Q (p.liftQ f h) (fun c => by
    have h2 : (p.liftQ f h).range ≤ Q := by
      rw [Submodule.range_liftQ]; exact h'
    exact h2 (LinearMap.mem_range_self _ c))

/-- Linear maps `M →ₗ N` that vanish on a submodule `p` and whose range lies in a submodule `Q`
are the same thing as linear maps `M ⧸ p →ₗ Q`. -/
private noncomputable def kerRangeEquiv {𝕜 : Type*} [Field 𝕜] {M N : Type*}
    [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
    (p : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    {f : M →ₗ[𝕜] N // p ≤ LinearMap.ker f ∧ LinearMap.range f ≤ Q} ≃
      ((M ⧸ p) →ₗ[𝕜] Q) where
  toFun f := liftQCodRestrict p Q f.1 f.2.1 f.2.2
  invFun g :=
    ⟨Q.subtype.comp (g.comp p.mkQ), by
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [LinearMap.mem_ker]
        have hx0 : p.mkQ x = 0 := by
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact hx
        simp only [LinearMap.comp_apply, hx0, map_zero]
      · exact (LinearMap.range_comp_le_range (g.comp p.mkQ) Q.subtype).trans
          (le_of_eq (Submodule.range_subtype Q))⟩
  left_inv f := by
    apply Subtype.ext
    change Q.subtype.comp ((liftQCodRestrict p Q f.1 f.2.1 f.2.2).comp p.mkQ) = f.1
    have h1 : Q.subtype.comp (liftQCodRestrict p Q f.1 f.2.1 f.2.2) = p.liftQ f.1 f.2.1 := by
      ext c
      simp [liftQCodRestrict]
    rw [← LinearMap.comp_assoc, h1, Submodule.liftQ_mkQ]
  right_inv g := by
    apply LinearMap.ext
    intro c
    refine Submodule.Quotient.induction_on p c (fun x => ?_)
    apply Subtype.ext
    simp only [liftQCodRestrict, LinearMap.codRestrict_apply, Submodule.liftQ_apply,
      LinearMap.comp_apply, Submodule.mkQ_apply]
    rfl

theorem card_ker_range_le {m n : ℕ} (V₁ V₂ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (W₁ W₂ : Submodule (ZMod 2) (Fin m → ZMod 2)) (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂) :
    Nat.card {X : ↥W₂ →ₗ[ZMod 2] ((Fin n → ZMod 2) ⧸ V₂) //
        Submodule.comap W₂.subtype W₁ ≤ LinearMap.ker X ∧
        LinearMap.range X ≤ Submodule.map (Submodule.mkQ V₂) V₁} ≤
      2 ^ (Module.finrank (ZMod 2) V₁ * (m - Module.finrank (ZMod 2) W₁)) := by
  classical
  set K : Submodule (ZMod 2) ↥W₂ := Submodule.comap W₂.subtype W₁ with hK
  set P : Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ V₂) :=
    Submodule.map (Submodule.mkQ V₂) V₁ with hP
  have hcard : Nat.card {X : ↥W₂ →ₗ[ZMod 2] ((Fin n → ZMod 2) ⧸ V₂) //
        K ≤ LinearMap.ker X ∧ LinearMap.range X ≤ P} =
      Nat.card ((↥W₂ ⧸ K) →ₗ[ZMod 2] P) :=
    Nat.card_congr (kerRangeEquiv K P)
  rw [hcard]
  rw [natCard_linearMap (ZMod 2) (↥W₂ ⧸ K) P, Nat.card_zmod]
  apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
  have hKfin : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) W₁ := by
    rw [hK]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hW)
  have hW2le : Module.finrank (ZMod 2) ↥W₂ ≤ m := by
    have h := Submodule.finrank_le W₂
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact h
  have hQfin : Module.finrank (ZMod 2) (↥W₂ ⧸ K) ≤ m - Module.finrank (ZMod 2) W₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) K
    rw [hKfin] at h
    have heq : Module.finrank (ZMod 2) (↥W₂ ⧸ K)
        = Module.finrank (ZMod 2) ↥W₂ - Module.finrank (ZMod 2) W₁ := by omega
    rw [heq]
    exact Nat.sub_le_sub_right hW2le _
  have hPfin : Module.finrank (ZMod 2) P ≤ Module.finrank (ZMod 2) V₁ := by
    rw [hP, finrank_map_mkQ_of_le V₂ V₁ hV]
    exact Nat.sub_le _ _
  calc Module.finrank (ZMod 2) (↥W₂ ⧸ K) * Module.finrank (ZMod 2) P
      ≤ (m - Module.finrank (ZMod 2) W₁) * Module.finrank (ZMod 2) V₁ :=
        Nat.mul_le_mul hQfin hPfin
    _ = Module.finrank (ZMod 2) V₁ * (m - Module.finrank (ZMod 2) W₁) := by rw [Nat.mul_comm]

end Commons.LinearAlgebra.Submodule