import Mathlib
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Kunneth.HomValue
import Submission.Work.ThomBordism.PontryaginThom.Torsion

/-!
# Rational cycles are rational multiples of rationalised integral cycles

For a chain complex `K` of `ℤ`-modules and `n : ℕ`, every cycle of the base changed complex
`K ⊗[ℤ] ℚ` is a rational multiple of `1 ⊗ x` for some genuine cycle `x` of `K`.

The proof has three ingredients:
* every element of `ℚ ⊗[ℤ] M` is a rational multiple of `1 ⊗ w` (clearing denominators);
* `1 ⊗ m = 0` in `ℚ ⊗[ℤ] M` implies that `m` is a torsion element
  (`Work.ThomBordism.PontryaginThom.torsion_of_tmul_one_eq_zero`);
* hence, if `q • (1 ⊗ w)` is a cycle with `q ≠ 0`, then a positive multiple `N • w` is a cycle and
  `1 ⊗ (N • w) = N • (1 ⊗ w)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

/-! ## Rational multiples of integral tensors -/

/-- **An integral multiple of `1 ⊗ m` on the other side.**  For `a : ℤ` and `m : M`,
`(a : ℚ) • (1 ⊗ m) = 1 ⊗ (a • m)`. -/
private theorem rat_smul_one_tmul {M : Type*} [AddCommGroup M] [Module ℤ M] (a : ℤ) (m : M) :
    (a : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (a • m) := by
  rcases Int.eq_nat_or_neg a with ⟨n, h | h⟩
  · rw [h, Int.cast_natCast, Nat.cast_smul_eq_nsmul (R := ℚ) n ((1 : ℚ) ⊗ₜ[ℤ] m),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) m, natCast_zsmul]
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_smul,
      Nat.cast_smul_eq_nsmul (R := ℚ) n ((1 : ℚ) ⊗ₜ[ℤ] m),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) m, ← TensorProduct.tmul_neg]
    congr 1
    rw [neg_zsmul, natCast_zsmul]

/-- **Clearing denominators.**  Every element of `ℚ ⊗[ℤ] M` has a positive integer multiple which
is `1 ⊗ w` for some `w : M`. -/
private theorem exists_nat_smul_tmul_one (M : Type*) [AddCommGroup M] [Module ℤ M]
    (z : ℚ ⊗[ℤ] M) :
    ∃ (k : ℕ) (w : M), 0 < k ∧ (k : ℚ) • z = (1 : ℚ) ⊗ₜ[ℤ] w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, Nat.one_pos, by simp⟩
  | tmul q m =>
      refine ⟨q.den, q.num • m, q.den_pos, ?_⟩
      rw [TensorProduct.tmul_eq_smul_one_tmul (R := ℤ) q m, smul_smul]
      have hden : ((q.den : ℚ)) ≠ 0 := by exact_mod_cast Rat.den_nz q
      have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
        have h : (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) = (q.num : ℚ) :=
          mul_div_cancel₀ _ hden
        rwa [Rat.num_div_den q] at h
      rw [hq, rat_smul_one_tmul q.num m]
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨k₁, w₁, hk₁, hz₁⟩ := h₁
      obtain ⟨k₂, w₂, hk₂, hz₂⟩ := h₂
      refine ⟨k₁ * k₂, (k₂ : ℤ) • w₁ + (k₁ : ℤ) • w₂, Nat.mul_pos hk₁ hk₂, ?_⟩
      have h1 : ((k₁ * k₂ : ℕ) : ℚ) • (z₁ + z₂)
          = (k₂ : ℚ) • ((k₁ : ℚ) • z₁) + (k₁ : ℚ) • ((k₂ : ℚ) • z₂) := by
        rw [Nat.cast_mul, mul_smul, smul_add, smul_add, smul_comm (k₁ : ℚ) (k₂ : ℚ) z₁]
      rw [h1, hz₁, hz₂, (Int.cast_natCast (R := ℚ) k₂).symm, (Int.cast_natCast (R := ℚ) k₁).symm,
        rat_smul_one_tmul (k₂ : ℤ) w₁, rat_smul_one_tmul (k₁ : ℤ) w₂, ← TensorProduct.tmul_add]

/-- Every element of `ℚ ⊗[ℤ] M` is a rational multiple of `1 ⊗ w` for some `w : M`. -/
private theorem exists_smul_tmul_one (M : Type*) [AddCommGroup M] [Module ℤ M]
    (z : ℚ ⊗[ℤ] M) : ∃ (q : ℚ) (w : M), z = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
  obtain ⟨k, w, hk, hz⟩ := exists_nat_smul_tmul_one M z
  refine ⟨((k : ℚ))⁻¹, w, ?_⟩
  rw [← hz, inv_smul_smul₀ (by exact_mod_cast hk.ne')]

/-- `1 ⊗ (k • w) = k • (1 ⊗ w)` for a natural number `k`. -/
private theorem one_tmul_nsmul {M : Type*} [AddCommGroup M] [Module ℤ M] (k : ℕ) (w : M) :
    (1 : ℚ) ⊗ₜ[ℤ] (k • w) = (k : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
  rw [Nat.cast_smul_eq_nsmul (R := ℚ) k ((1 : ℚ) ⊗ₜ[ℤ] w),
    ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) k (1 : ℚ) w]

/-! ## The main statement -/

theorem ratCycleExists (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (c : ↥((Work.StemsB.IntRatCM.obj K).cycles n)) :
    ∃ (q : ℚ) (x : ↥(K.cycles n)),
      (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).iCycles n)) c
        = q • TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom (K.iCycles n)) x) := by
  set z : ↥((Work.StemsB.IntRatCM.obj K).X n) :=
    (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).iCycles n)) c with hz
  -- `z` is a cycle
  have hcyc : (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).d n (n - 1))) z = 0 := by
    rw [hz]
    have h := HomologicalComplex.iCycles_d (Work.StemsB.IntRatCM.obj K) n (n - 1)
    have h2 := congrArg (fun (g : (Work.StemsB.IntRatCM.obj K).cycles n ⟶
        (Work.StemsB.IntRatCM.obj K).X (n - 1)) => (ModuleCat.Hom.hom g) c) h
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply] using h2
  obtain ⟨q, w, hw⟩ := exists_smul_tmul_one ↥(K.X n) z
  by_cases hq : q = 0
  · refine ⟨0, 0, ?_⟩
    rw [hw, hq, zero_smul, zero_smul]
  · set dw : ↥(K.X (n - 1)) := (ModuleCat.Hom.hom (K.d n (n - 1))) w with hdw
    have hqdw : q • ((1 : ℚ) ⊗ₜ[ℤ] dw) = 0 := by
      have hd1 : (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).d n (n - 1)))
          (q • ((1 : ℚ) ⊗ₜ[ℤ] w)) = 0 := by
        rw [← hw]; exact hcyc
      rwa [map_smul] at hd1
    have hdw0 : (1 : ℚ) ⊗ₜ[ℤ] dw = 0 := by
      have hY : (1 : ℚ) ⊗ₜ[ℤ] dw = q⁻¹ • (q • ((1 : ℚ) ⊗ₜ[ℤ] dw)) := by
        rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
      rw [hY, hqdw, smul_zero]
    have hdw0' : dw ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
      refine (TensorProduct.comm ℤ ↥(K.X (n - 1)) ℚ).injective.eq_iff.mp ?_
      rw [map_zero, TensorProduct.comm_tmul]
      exact hdw0
    obtain ⟨N, hN, hNdw⟩ :=
      Work.ThomBordism.PontryaginThom.torsion_of_tmul_one_eq_zero dw (by
        have h := hdw0'
        rw [show (K.X (n - 1)).isModule = AddCommGroup.toIntModule ↥(K.X (n - 1))
          from Subsingleton.elim _ _] at h
        exact h)
    have hNdw' : N • dw = 0 := by rwa [natCast_zsmul] at hNdw
    have hmem : (ModuleCat.Hom.hom (K.d n (n - 1))) (N • w) = 0 := by
      rw [map_nsmul, ← hdw, hNdw']
    refine ⟨q / N, Work.Kunneth.cycleOf K n ⟨N • w, ?_⟩, ?_⟩
    · rw [Work.Kunneth.cycKer, LinearMap.mem_ker]
      exact hmem
    · rw [Work.Kunneth.iCycles_cycleOf, hw, one_tmul_nsmul N w, smul_smul]
      congr 1
      rw [div_mul_cancel₀ q (by exact_mod_cast hN.ne')]

end

end Work.Serre.Surj
