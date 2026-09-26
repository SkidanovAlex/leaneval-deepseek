/-
# The residue theorem of CKMRV Theorem 4.9(3) for `K_+`

This file derives the full residue theorem for the kernel `K_+^{(d)}` from the three
computations of the residues at the points `z`, `Tz`, `TS·z` of the orbit of `z`, using the
linearity of the residue in the group-algebra element `r` and the fact that the residue
functional is annihilated by `𝓘_+ = (S+I)R + (T-I)²R + (z-1)R` (the functional equations of
Theorem 4.9(2)).

## Main results

* `Work.Residues.slash_Rneg_sub_one`, `slash_mem_augIdeal` : at even weight the collapse ideal
  `(z-1)R` acts by zero.
* `Work.Residues.KPlus_slash_eq_zero_of_mem_idealIp` : `K_+ |^τ r = 0` for `r ∈ 𝓘_+`.
* `Work.Residues.hasResidue_slash_KPlus` : for every `r : R` and every `z` with
  `j'(z) ≠ 0`, the function `τ ↦ (K_+^{(d)} |^τ_{d/2} r)(τ,z)` has at `τ = z` at most a simple
  pole with residue `-(1/2π)·φ_+(r)` (paper Theorem 4.9(3)).
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Kernels.TildeFacts.KMinus_z_tildeB
import Submission.Work.Kernels.KernelSlash
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Kernels.AlgebraFacts.slash_mul
import Submission.Work.Kernels.AlgebraFacts.slash_smul
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## The collapse ideal acts by zero at even weight -/

lemma jFun_neg_one (z : ℂ) : jFun (-1 : SL(2,ℤ)) z = -1 := by
  rw [jFun_apply]
  have hcoe : ((-1 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -(1 : Matrix (Fin 2) (Fin 2) ℤ) :=
    Matrix.SpecialLinearGroup.coe_neg _
  rw [hcoe]
  simp

lemma slash_single_neg_one (k : ℤ) (hk : Even k) (F : ℍ → ℂ) :
    slash k (MonoidAlgebra.single (-1 : SL(2,ℤ)) (1 : ℂ)) F = F := by
  rw [slash_single]
  ext τ
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  have hτ : (-1 : SL(2,ℤ)) • τ = τ := by simp
  rw [slash_apply', jFun_neg_one, hτ, _root_.zpow_neg, hk.neg_one_zpow, inv_one, mul_one]

lemma slash_Rneg_sub_one (k : ℤ) (hk : Even k) (F : ℍ → ℂ) : slash k (Rneg - 1) F = 0 := by
  have h1 : slash k Rneg F = F := by
    rw [Rneg]
    exact slash_single_neg_one k hk F
  rw [sub_eq_add_neg, slash_add, slash_neg, h1, slash_one, add_neg_cancel]

lemma slash_mem_augIdeal {k : ℤ} (hk : Even k) {x : R} (hx : x ∈ augIdeal) (F : ℍ → ℂ) :
    slash k x F = 0 := by
  refine Submodule.span_induction (p := fun y _ => slash k y F = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a, b, rfl⟩
    rw [mul_assoc, AlgebraFacts.slash_mul, AlgebraFacts.slash_mul,
      slash_Rneg_sub_one k hk, AlgebraFacts.slash_mul_aux_zero]
  · rw [slash_zero]
  · intro y z _ _ hy hz; rw [slash_add, hy, hz, add_zero]
  · intro c y _ hy; rw [AlgebraFacts.slash_smul, hy, smul_zero]

lemma even_div_two (d : ℕ) (hd : d = 8 ∨ d = 24) : Even ((d : ℤ) / 2) := by
  rcases hd with rfl | rfl <;> norm_num

/-! ## `K_+` is annihilated by `𝓘_+` -/

lemma KPlus_slash_eq_zero_of_mem_idealIp (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) {x : R}
    (hx : x ∈ idealIp) : slash ((d : ℤ) / 2) x (fun σ : ℍ => KPlus d σ z) = 0 := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p, q, hp⟩ := mem_span2.mp ha
  rw [hp, slash_add, slash_add, AlgebraFacts.slash_mul, AlgebraFacts.slash_mul,
    KPlus_slash_S_add d hd z, KPlus_slash_T2 d hd z,
    AlgebraFacts.slash_mul_aux_zero, AlgebraFacts.slash_mul_aux_zero,
    slash_mem_augIdeal (even_div_two d hd) hc, add_zero, add_zero]

/-! ## The slashed residues on the basis -/

/-- `(T*S) · z = Tz`-analogue: the point `TS·z` as `1 +ᵥ (S·z)`. -/
lemma T_mul_S_smul (z : ℍ) :
    (ModularGroup.T * ModularGroup.S) • z = (1 : ℝ) +ᵥ (ModularGroup.S • z) := by
  rw [mul_smul]
  simpa using UpperHalfPlane.modular_T_zpow_smul (ModularGroup.S • z) (1 : ℤ)

/-- The `S`-slash in coordinates. -/
lemma slash_S_apply'' (k : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[k] ModularGroup.S) z = F (ModularGroup.S • z) * (z : ℂ) ^ (-k) := by
  rw [Work.Kernels.slash_apply', jFun_apply]
  have h0 : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by decide
  have h1 : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by decide
  rw [h0, h1]
  ring

lemma jFun_S (z : ℂ) : jFun ModularGroup.S z = z := by
  rw [jFun_apply]
  have h0 : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by decide
  have h1 : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by decide
  rw [h0, h1]
  ring

lemma E4Fun_S_smul (z : ℍ) : E4Fun (ModularGroup.S • z) = (z : ℂ) ^ 4 * E4Fun z := by
  rw [TildeFacts.Kzb.smul_of_slash (k := (4 : ℤ)) (γ := ModularGroup.S)
    KernelFacts.E4Fun_S_slash z, jFun_S]
  rfl

lemma E6Fun_S_smul (z : ℍ) : E6Fun (ModularGroup.S • z) = (z : ℂ) ^ 6 * E6Fun z := by
  rw [TildeFacts.Kzb.smul_of_slash (k := (6 : ℤ)) (γ := ModularGroup.S)
    KernelFacts.E6Fun_S_slash z, jFun_S]
  rfl

/-- The residue of `K_+^{(d)}(·,z)` at `τ = TS·z` is `0 = -(1/2π)φ_+(TS)`. -/
theorem hasResidue_KPlus_TS (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KPlus d τ z) ((ModularGroup.T * ModularGroup.S) • z) 0 := by
  have hTS : (ModularGroup.T * ModularGroup.S) • z = (1 : ℝ) +ᵥ (ModularGroup.S • z) :=
    T_mul_S_smul z
  have hj : jInvariantFun ((ModularGroup.T * ModularGroup.S) • z) = jInvariantFun z := by
    rw [hTS, KernelFacts.jInvariantFun_vadd_one, KernelFacts.jInvariantFun_S_smul]
  have hne' : jprime ((ModularGroup.T * ModularGroup.S) • z) ≠ 0 := by
    rw [hTS, jprime_vadd_one]
    rw [jprime_ne_zero_iff] at hne ⊢
    rw [E4Fun_S_smul, E6Fun_S_smul]
    have hz : (z : ℂ) ≠ 0 := by exact_mod_cast z.ne_zero
    rw [mul_ne_zero_iff] at hne
    rw [mul_ne_zero_iff]
    exact ⟨mul_ne_zero (pow_ne_zero _ hz) hne.1, mul_ne_zero (pow_ne_zero _ hz) hne.2⟩
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KPlus d τ z) (A := AfunPlus d z)
    (z₀ := (ModularGroup.T * ModularGroup.S) • z) (z := z) (c := jprime _)
    (mdifferentiableAt_AfunPlus d hd z _) hj (tendsto_slope_jprime _) hne' ?_
  · have hA0 : AfunPlus d z ((ModularGroup.T * ModularGroup.S) • z) = 0 := by
      rw [hTS, AfunPlus, KPlusClear_TS d hd z, zero_div]
    rw [hA0, zero_div] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime _).eventually
      (eventually_ne_nhds hne')] with τ hτ hτne
    have hτ' : τ ≠ (ModularGroup.T * ModularGroup.S) • z := by simpa using hτ
    have hslope : (jInvariantFun τ - jInvariantFun ((ModularGroup.T * ModularGroup.S) • z)) /
        ((τ : ℂ) - (((ModularGroup.T * ModularGroup.S) • z : ℍ) : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun ((ModularGroup.T * ModularGroup.S) • z) ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hjnz' : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      have hh := hjnz
      rw [hj] at hh
      exact hh
    exact mul_slope_eq_AfunPlus d hd z τ (sub_ne_zero.mp hjnz')

/-- `slash k (T*S) F` is `j(T*S,·)^{-k}·F((T*S)·)`. -/
lemma slash_mul_T_S (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    slash k (R_T * R_S) F τ
      = (jFun (ModularGroup.T * ModularGroup.S) (τ : ℂ)) ^ (-k)
        * F ((ModularGroup.T * ModularGroup.S) • τ) := by
  rw [show R_T * R_S = MonoidAlgebra.single (ModularGroup.T * ModularGroup.S) (1 : ℂ) by
    rw [R_T, R_S, MonoidAlgebra.single_mul_single]; simp, slash_single,
    Pi.smul_apply, smul_eq_mul, one_mul, slash_apply', mul_comm]

/-- `slash k R_T F` in terms of the Möbius action. -/
lemma slash_R_T_eq (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    slash k R_T F τ = (jFun ModularGroup.T (τ : ℂ)) ^ (-k) * F (ModularGroup.T • τ) := by
  rw [show R_T = MonoidAlgebra.single ModularGroup.T (1 : ℂ) by rw [R_T], slash_single,
    Pi.smul_apply, smul_eq_mul, one_mul, slash_apply', mul_comm]

/-- The residue of the `r = 1` slashed kernel at `τ = z` is `0 = -(1/2π)φ_+(1)`. -/
theorem hasResidue_slash_KPlus_one (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) 1 (fun σ : ℍ => KPlus d σ z)) z 0 := by
  have h : slash ((d : ℤ) / 2) (1 : R) (fun σ : ℍ => KPlus d σ z)
      = fun τ : ℍ => KPlus d τ z := by
    funext τ
    rw [slash_one]
  rw [h]
  exact hasResidue_KPlus_self d hd z hne

/-- The residue of the `r = T` slashed kernel at `τ = z` is `-1/(2π) = -(1/2π)φ_+(T)`. -/
theorem hasResidue_slash_KPlus_T (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) R_T (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi))) := by
  have hres := hasResidue_KPlus_T d hd z hne
  rw [show (1 : ℝ) +ᵥ z = ModularGroup.T • z by
    simpa using (UpperHalfPlane.modular_T_zpow_smul z (1 : ℤ)).symm] at hres
  have h := hasResidue_smul_SL (f := fun σ : ℍ => KPlus d σ z)
    (z := z) (c := -(1 / (2 * Real.pi))) ModularGroup.T ((d : ℤ) / 2) hres
  have hj : (jFun ModularGroup.T (z : ℂ)) ^ (2 - (d : ℤ) / 2) = 1 := by
    have h1 : jFun ModularGroup.T (z : ℂ) = 1 := by
      rw [jFun_apply]
      have hcoe : ((ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by decide
      have hcoe' : ((ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by decide
      rw [hcoe, hcoe']; ring
    rw [h1, _root_.one_zpow]
  rw [hj, one_mul] at h
  have hfun : (fun τ : ℍ => (jFun ModularGroup.T (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
      (fun σ : ℍ => KPlus d σ z) (ModularGroup.T • τ))
      = (fun τ : ℍ => slash ((d : ℤ) / 2) R_T (fun σ : ℍ => KPlus d σ z) τ) := by
    funext τ
    rw [slash_R_T_eq]
  rwa [hfun] at h

/-- The residue of the `r = TS` slashed kernel at `τ = z` is `0 = -(1/2π)φ_+(TS)`. -/
theorem hasResidue_slash_KPlus_TS (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) (R_T * R_S) (fun σ : ℍ => KPlus d σ z)) z 0 := by
  have h := hasResidue_smul_SL (f := fun σ : ℍ => KPlus d σ z)
    (z := z) (c := 0) (ModularGroup.T * ModularGroup.S) ((d : ℤ) / 2)
    (hasResidue_KPlus_TS d hd z hne)
  rw [mul_zero] at h
  have hf : slash ((d : ℤ) / 2) (R_T * R_S) (fun σ : ℍ => KPlus d σ z)
      = fun τ : ℍ => (jFun (ModularGroup.T * ModularGroup.S) (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
          (fun σ : ℍ => KPlus d σ z) ((ModularGroup.T * ModularGroup.S) • τ) := by
    funext τ
    rw [slash_mul_T_S]
  rw [hf]
  exact h

/-! ## The residue theorem for `K_+` -/

/-- **Theorem 4.9(3) for `K_+`.**  For every `r : R` and every `z` with `j'(z) ≠ 0`, the
function `τ ↦ (K_+^{(d)} |^τ_{d/2} r)(τ,z)` has at `τ = z` at most a simple pole, with
residue `-(1/2π)·φ_+(r)`. -/
theorem hasResidue_slash_KPlus (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0)
    (r : R) :
    HasResidue (slash ((d : ℤ) / 2) r (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi)) * phiPlus r) := by
  obtain ⟨c, hc⟩ := exists_sub_sum_smul_M3_mem_idealIp r
  have hexp : (∑ i : Fin 3, c i • M3 i) = c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S) := by
    rw [Fin.sum_univ_three, M3_zero, M3_one, M3_two]
  have hφ : phiPlus r = phiPlus (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S)) := by
    have h0 : phiPlus (r - ∑ i : Fin 3, c i • M3 i) = 0 :=
      phiPlus_eq_zero_of_mem_idealIp hc
    have hsr : r = (r - ∑ i : Fin 3, c i • M3 i) + ∑ i : Fin 3, c i • M3 i := by abel
    rw [hsr, map_add, h0, zero_add, hexp]
  have h0 : HasResidue (slash ((d : ℤ) / 2) (r - ∑ i : Fin 3, c i • M3 i)
      (fun σ : ℍ => KPlus d σ z)) z 0 := by
    rw [KPlus_slash_eq_zero_of_mem_idealIp d hd z hc, HasResidue]
    simpa using tendsto_const_nhds (x := (0 : ℂ))
  have t0 : HasResidue (slash ((d : ℤ) / 2) (c 0 • (1 : R)) (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi)) * phiPlus (c 0 • (1 : R))) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiPlus_one, smul_zero, mul_zero]
    have h := (hasResidue_slash_KPlus_one d hd z hne).const_mul (c 0)
    rw [mul_zero] at h
    convert h using 1
    all_goals (ext τ; rw [Pi.smul_apply, smul_eq_mul])
  have t1 : HasResidue (slash ((d : ℤ) / 2) (c 1 • R_T) (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi)) * phiPlus (c 1 • R_T)) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiPlus_R_T, smul_eq_mul, mul_one]
    have h := (hasResidue_slash_KPlus_T d hd z hne).const_mul (c 1)
    convert h using 1
    all_goals first | (ext τ; rw [Pi.smul_apply, smul_eq_mul]) | ring
  have t2 : HasResidue (slash ((d : ℤ) / 2) (c 2 • (R_T * R_S)) (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi)) * phiPlus (c 2 • (R_T * R_S))) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiPlus_TS, smul_zero, mul_zero]
    have h := (hasResidue_slash_KPlus_TS d hd z hne).const_mul (c 2)
    rw [mul_zero] at h
    convert h using 1
    all_goals (ext τ; rw [Pi.smul_apply, smul_eq_mul])
  have hthree : HasResidue (slash ((d : ℤ) / 2)
      (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S)) (fun σ : ℍ => KPlus d σ z)) z
      (-(1 / (2 * Real.pi)) * phiPlus (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S))) := by
    rw [slash_add, slash_add, map_add, map_add]
    convert (t0.add t1).add t2 using 1
    ring
  have hfun : slash ((d : ℤ) / 2) r (fun σ : ℍ => KPlus d σ z)
      = slash ((d : ℤ) / 2) (r - ∑ i : Fin 3, c i • M3 i) (fun σ : ℍ => KPlus d σ z)
        + slash ((d : ℤ) / 2) (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S))
            (fun σ : ℍ => KPlus d σ z) := by
    rw [← slash_add, ← hexp]
    congr 1
    abel
  rw [hfun, hφ]
  convert h0.add hthree using 1
  ring

end Work.Residues
