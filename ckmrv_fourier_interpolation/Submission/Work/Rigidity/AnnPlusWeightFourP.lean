/-
# The weight-four rigidity lemma at eigenvalue `-1`, with the moderate-growth hypothesis

This file proves `Work.Rigidity.SingleRigidityP 4 (-1 : ℂ) 0`: there is no nonzero
holomorphic `f : ℍ → ℂ` of moderate growth (`f ∈ 𝒫`, `Work.Kernels.InP`) that is annihilated by
`(T - I)²`, is an eigenfunction of the weight-`4` slash action of `S` with eigenvalue `-1`,
and decays like `o(1)` along the strip `-1 ≤ Re τ ≤ 1`.

The proof follows CKMRV Proposition `prop: HFE plus` (arXiv 1902.05438, Section 3.3) at `k = 4`,
where the description of `Ann₄(𝓘₊, 𝒫)` degenerates because `M₂ = 0`, and then evaluates the
resulting explicit two-dimensional space at the cusp `i∞`.
-/
import Mathlib
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.AnnPlusWeightFourPDefs
import Submission.Work.Modular.All
import Submission.Work.Kernels.All
import Submission.Work.Rigidity.hasSum_qExpansion_cusp_decay
import Submission.Work.Rigidity.G_slash_S
import Submission.Work.Rigidity.G2_vadd
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-! ## The slash action of `T` -/

/-- The slash action of `T` at any weight: the automorphy factor is `1`. -/
lemma slash_T_apply' (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.T) τ = F ((1 : ℝ) +ᵥ τ) := by
  rw [Work.Kernels.slash_apply', UpperHalfPlane.modular_T_smul]
  have h1 : Work.Kernels.jFun ModularGroup.T (τ : ℂ) = 1 := by
    rw [Work.Kernels.jFun_apply]
    have h10 : (ModularGroup.T : SL(2, ℤ)) 1 0 = 0 := by decide
    have h11 : (ModularGroup.T : SL(2, ℤ)) 1 1 = 1 := by decide
    rw [h10, h11]; ring
  rw [h1]
  simp

/-- `g_0` is the first difference of `f`. -/
lemma G0_eq_fstDiff (f : ℍ → ℂ) : G0 f = fstDiff f := by
  funext τ
  simp only [G0, Pi.sub_apply, fstDiff, slash_T_apply']

/-! ## Decay of modular forms at the cusp -/

/-- The constant `q`-coefficient (value at the cusp `i∞`) of a level-one modular form. -/
noncomputable def cterm {k : ℤ} (F : ModularForm 𝒮ℒ k) : ℂ :=
  (UpperHalfPlane.qExpansion 1 (⇑F)).coeff 0

/-- A level-one modular form differs from its constant `q`-coefficient by `O(q)`. -/
lemma modularForm_cusp_decay {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ τ : ℍ, A ≤ τ.im →
      ‖F τ - cterm F‖ ≤ B * Real.exp (-(2 * Real.pi * τ.im)) :=
  hasSum_qExpansion_cusp_decay fun τ =>
    ModularForm.hasSum_qExpansion F (by norm_num : (0:ℝ) < 1) one_mem_strictPeriods_SL τ

/-- `E₂ - 1` is `O(q)` at the cusp. -/
lemma E2Fun_sub_one_decay :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ τ : ℍ, A ≤ τ.im →
      ‖Work.Kernels.E2Fun τ - 1‖ ≤ B * Real.exp (-(2 * Real.pi * τ.im)) := by
  refine hasSum_qExpansion_cusp_decay (F := Work.Kernels.E2Fun)
    (c := fun m : ℕ => if m = 0 then 1 else -24 * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ)) ?_
  intro τ
  simpa only [Work.Kernels.E2Fun, Function.Periodic.qParam, Complex.ofReal_one, div_one,
    smul_eq_mul] using EisensteinSeries.hasSum_qExpansion_E2 τ

/-- A level-one modular form of weight `< 12` whose constant `q`-coefficient vanishes is
identically zero. -/
lemma modularForm_eq_zero_of_constTerm_eq_zero {k : ℤ} (F : ModularForm 𝒮ℒ k) (hk : k < 12)
    (h : (UpperHalfPlane.qExpansion 1 (⇑F)).coeff 0 = 0) : ⇑F = 0 := by
  have hcf : ModularForm.toCuspForm F h = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  have h1 : ((ModularForm.toCuspForm F h : CuspForm 𝒮ℒ k) : ℍ → ℂ) = 0 := by rw [hcf]; rfl
  funext z
  rw [← ModularForm.toCuspForm_apply F h z]
  exact congrFun h1 z

/-! ## The `T`- and `S`-relations satisfied by `g_0, g_1, g_2` -/

/-- `g_0` is `T`-periodic when `(T-I)² f = 0`. -/
lemma G0_vadd {f : ℍ → ℂ} (hT2 : AnnT2 f) (τ : ℍ) :
    G0 f ((1 : ℝ) +ᵥ τ) = G0 f τ := by
  rw [G0_eq_fstDiff]
  exact (fstDiff_vadd_one_iff f).mp hT2 τ

/-- `g_1 (τ+1) = g_0 τ + g_1 τ`. -/
lemma G1_vadd (f : ℍ → ℂ) (τ : ℍ) :
    G1 f ((1 : ℝ) +ᵥ τ) = G0 f τ + G1 f τ := by
  simp only [G1, G0_eq_fstDiff, fstDiff]
  ring

/-- The eigenrelation `f ∣[4] S = -f` at a point: `f (S • σ) = -(σ : ℂ)^4 f σ`. -/
lemma S_smul_apply {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    f (ModularGroup.S • σ) = -((σ : ℂ) ^ (4 : ℤ) * f σ) := by
  have h := congrFun hS σ
  rw [Work.Kernels.slash_S_apply] at h
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  have h4 : (σ : ℂ) ^ (-4 : ℤ) * (σ : ℂ) ^ (4 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc f (ModularGroup.S • σ)
      = (f (ModularGroup.S • σ) * (σ : ℂ) ^ (-4 : ℤ)) * (σ : ℂ) ^ (4 : ℤ) := by
        rw [mul_assoc, h4, mul_one]
    _ = (-f) σ * (σ : ℂ) ^ (4 : ℤ) := by rw [h]
    _ = -((σ : ℂ) ^ (4 : ℤ) * f σ) := by
        change -(f σ) * (σ : ℂ) ^ (4 : ℤ) = -((σ : ℂ) ^ (4 : ℤ) * f σ)
        ring

/-- Pointwise `S`-relation for `g_1`. -/
lemma G1_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    G1 f (ModularGroup.S • σ) = (σ : ℂ) ^ (4 : ℤ) * (-(G1 f σ)) := by
  simp only [G1]
  rw [S_smul_apply hS σ]
  ring

/-- Pointwise `S`-relation for `g_0`: `g_0 (S • σ) = σ^4 g_2 σ`. -/
lemma G0_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    G0 f (ModularGroup.S • σ) = (σ : ℂ) ^ (4 : ℤ) * G2 f σ := by
  have h := congrFun (G_slash_S hS).1 σ
  rw [Work.Kernels.slash_S_apply] at h
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  have h4 : (σ : ℂ) ^ (-4 : ℤ) * (σ : ℂ) ^ (4 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc G0 f (ModularGroup.S • σ)
      = (G0 f (ModularGroup.S • σ) * (σ : ℂ) ^ (-4 : ℤ)) * (σ : ℂ) ^ (4 : ℤ) := by
        rw [mul_assoc, h4, mul_one]
    _ = G2 f σ * (σ : ℂ) ^ (4 : ℤ) := by rw [h]
    _ = (σ : ℂ) ^ (4 : ℤ) * G2 f σ := by ring

/-- Pointwise `S`-relation for `g_2`: `g_2 (S • σ) = σ^4 g_0 σ`. -/
lemma G2_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    G2 f (ModularGroup.S • σ) = (σ : ℂ) ^ (4 : ℤ) * G0 f σ := by
  have h := congrFun (G_slash_S hS).2 σ
  rw [Work.Kernels.slash_S_apply] at h
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  have h4 : (σ : ℂ) ^ (-4 : ℤ) * (σ : ℂ) ^ (4 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc G2 f (ModularGroup.S • σ)
      = (G2 f (ModularGroup.S • σ) * (σ : ℂ) ^ (-4 : ℤ)) * (σ : ℂ) ^ (4 : ℤ) := by
        rw [mul_assoc, h4, mul_one]
    _ = G0 f σ * (σ : ℂ) ^ (4 : ℤ) := by rw [h]
    _ = (σ : ℂ) ^ (4 : ℤ) * G0 f σ := by ring

/-! ## The combinations `h_0, h_1, h_2` -/

/-- `h_2 (S • σ) = σ² h_2 σ` (weight two). -/
lemma H2_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    H2 f (ModularGroup.S • σ) = (σ : ℂ) ^ (2 : ℤ) * H2 f σ := by
  simp only [H2]
  rw [coe_S_smul, G0_S_smul hS σ, G1_S_smul hS σ, G2_S_smul hS σ]
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  field_simp
  ring

/-- `h_2 ∣[2] S = h_2`. -/
lemma H2_slash_S {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) :
    H2 f ∣[(2 : ℤ)] ModularGroup.S = H2 f := by
  funext τ
  rw [Work.Kernels.slash_S_apply, H2_S_smul hS τ]
  have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h4 : (τ : ℂ) ^ (2 : ℤ) * (τ : ℂ) ^ (-2 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc (((τ : ℂ) ^ (2 : ℤ) * H2 f τ) * (τ : ℂ) ^ (-2 : ℤ))
      = ((τ : ℂ) ^ (2 : ℤ) * (τ : ℂ) ^ (-2 : ℤ)) * H2 f τ := by ring
    _ = H2 f τ := by rw [h4, one_mul]

/-- `h_1 (τ+1) = h_1 τ`. -/
lemma H1_vadd {f : ℍ → ℂ} (hT2 : AnnT2 f) (τ : ℍ) :
    H1 f ((1 : ℝ) +ᵥ τ) = H1 f τ := by
  simp only [H1, Work.Kernels.coe_vadd_one]
  rw [G0_vadd hT2 τ, G1_vadd]
  ring

/-- `h_1 (S • σ) = σ^4 (h_1 σ + 2 σ^{-1} h_2 σ)`. -/
lemma H1_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    H1 f (ModularGroup.S • σ)
      = (σ : ℂ) ^ (4 : ℤ) * (H1 f σ + 2 * (σ : ℂ) ^ (-1 : ℤ) * H2 f σ) := by
  simp only [H1, H2]
  rw [coe_S_smul, G0_S_smul hS σ, G1_S_smul hS σ]
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  field_simp
  ring

/-- `h_1 ∣[4] S = h_1 + 2 τ^{-1} h_2`. -/
lemma H1_slash_S_add {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) :
    H1 f ∣[(4 : ℤ)] ModularGroup.S
      = H1 f + fun σ : ℍ => 2 * ((σ : ℂ) ^ (-1 : ℤ) * H2 f σ) := by
  funext τ
  rw [Work.Kernels.slash_S_apply, H1_S_smul hS τ]
  have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h4 : (τ : ℂ) ^ (4 : ℤ) * (τ : ℂ) ^ (-4 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  have hassoc : H1 f τ + (2 * (τ : ℂ) ^ (-1 : ℤ)) * H2 f τ
      = H1 f τ + 2 * ((τ : ℂ) ^ (-1 : ℤ) * H2 f τ) := by ring
  rw [hassoc]
  calc ((τ : ℂ) ^ (4 : ℤ) * (H1 f τ + 2 * ((τ : ℂ) ^ (-1 : ℤ) * H2 f τ))
        * (τ : ℂ) ^ (-4 : ℤ))
      = ((τ : ℂ) ^ (4 : ℤ) * (τ : ℂ) ^ (-4 : ℤ))
        * (H1 f τ + 2 * ((τ : ℂ) ^ (-1 : ℤ) * H2 f τ)) := by ring
    _ = H1 f τ + 2 * ((τ : ℂ) ^ (-1 : ℤ) * H2 f τ) := by rw [h4, one_mul]

/-- `h_0 (S • σ) = σ^6 (h_0 σ + σ^{-1} h_1 σ + σ^{-2} h_2 σ)`. -/
lemma H0_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    G0 f (ModularGroup.S • σ) = (σ : ℂ) ^ (6 : ℤ) *
      (G0 f σ + (σ : ℂ) ^ (-1 : ℤ) * H1 f σ + (σ : ℂ) ^ (-2 : ℤ) * H2 f σ) := by
  rw [G0_S_smul hS σ]
  simp only [H1, H2]
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  field_simp
  ring

/-- `E₂` is `T`-invariant. -/
lemma E2Fun_vadd (τ : ℍ) : Work.Kernels.E2Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E2Fun τ := by
  have h : Work.Kernels.E2Fun (ModularGroup.T • τ) = Work.Kernels.E2Fun τ :=
    Work.Modular.E2_T_smul τ
  rwa [UpperHalfPlane.modular_T_smul] at h

/-- The `S`-transformation law of `E₂` at a point. -/
lemma E2Fun_S_smul (σ : ℍ) : Work.Kernels.E2Fun (ModularGroup.S • σ)
    = (σ : ℂ) ^ 2 * Work.Kernels.E2Fun σ - 6 * Complex.I * (σ : ℂ) / Real.pi :=
  Work.Modular.E2_S_smul σ

/-- `m (τ+1) = m τ`. -/
lemma Mmod_vadd {f : ℍ → ℂ} (hT2 : AnnT2 f) (τ : ℍ) :
    Mmod f ((1 : ℝ) +ᵥ τ) = Mmod f τ := by
  simp only [Mmod, H0, Work.Kernels.coe_vadd_one]
  rw [G0_vadd hT2 τ, H1_vadd hT2 τ, E2Fun_vadd τ]

/-- `m (S • σ)` differs from `σ^6 m σ` by a multiple of `h_2 σ`; hence `m` is `S`-invariant
once `h_2 = 0`. -/
lemma Mmod_S_smul {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (σ : ℍ) :
    Mmod f (ModularGroup.S • σ) = (σ : ℂ) ^ (6 : ℤ) * (Mmod f σ -
      ((σ : ℂ) ^ (-2 : ℤ) + (Real.pi * Complex.I / 3) * (σ : ℂ) ^ (-1 : ℤ)
        * Work.Kernels.E2Fun σ) * H2 f σ) := by
  simp only [Mmod, H0]
  rw [G0_S_smul hS σ, H1_S_smul hS σ, E2Fun_S_smul σ]
  have hz : (σ : ℂ) ≠ 0 := coe_ne_zero σ
  field_simp
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) from Complex.I_sq]
  simp only [H1, H2]
  ring

/-! ## The `T`- and `S`-relations for `h_2`, `h_1` and `m` -/

/-- `h_2 (τ+1) = h_2 τ`. -/
lemma H2_vadd {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (hT2 : AnnT2 f) (τ : ℍ) :
    H2 f ((1 : ℝ) +ᵥ τ) = H2 f τ := by
  simp only [H2, Work.Kernels.coe_vadd_one]
  rw [G0_vadd hT2 τ, G1_vadd, G2_vadd hS hT2 τ]
  ring

/-- `h_2 ∣[2] T = h_2`. -/
lemma H2_slash_T {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (hT2 : AnnT2 f) :
    H2 f ∣[(2 : ℤ)] ModularGroup.T = H2 f := by
  funext τ
  rw [slash_T_apply']
  exact H2_vadd hS hT2 τ

/-- `h_1 ∣[4] T = h_1`. -/
lemma H1_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) : H1 f ∣[(4 : ℤ)] ModularGroup.T = H1 f := by
  funext τ
  rw [slash_T_apply']
  exact H1_vadd hT2 τ

/-- `m ∣[6] T = m`. -/
lemma Mmod_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) : Mmod f ∣[(6 : ℤ)] ModularGroup.T = Mmod f := by
  funext τ
  rw [slash_T_apply']
  exact Mmod_vadd hT2 τ

/-- `h_1 ∣[4] S = h_1` when `h_2 = 0`. -/
lemma H1_slash_S {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (h2 : H2 f = 0) :
    H1 f ∣[(4 : ℤ)] ModularGroup.S = H1 f := by
  rw [H1_slash_S_add hS]
  have : (fun σ : ℍ => 2 * ((σ : ℂ) ^ (-1 : ℤ) * H2 f σ)) = 0 := by
    funext σ
    rw [h2]
    simp
  rw [this, add_zero]

/-- `m ∣[6] S = m` when `h_2 = 0`. -/
lemma Mmod_slash_S {f : ℍ → ℂ} (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (h2 : H2 f = 0) :
    Mmod f ∣[(6 : ℤ)] ModularGroup.S = Mmod f := by
  funext τ
  rw [Work.Kernels.slash_S_apply, Mmod_S_smul hS τ]
  have h2τ : H2 f τ = 0 := by rw [h2]; rfl
  rw [h2τ]
  simp only [mul_zero, sub_zero]
  have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h6 : (τ : ℂ) ^ (6 : ℤ) * (τ : ℂ) ^ (-6 : ℤ) = 1 := by
    rw [← zpow_add₀ hz]; norm_num
  calc ((τ : ℂ) ^ (6 : ℤ) * Mmod f τ * (τ : ℂ) ^ (-6 : ℤ))
      = ((τ : ℂ) ^ (6 : ℤ) * (τ : ℂ) ^ (-6 : ℤ)) * Mmod f τ := by ring
    _ = Mmod f τ := by rw [h6, one_mul]

/-! ## Membership in `𝒫` -/

lemma InP_G0 {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (G0 f) := by
  rw [G0]
  exact (hP.slash (4 : ℤ) ModularGroup.T).sub hP

lemma InP_G1 {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (G1 f) := hP

lemma InP_G2 {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (G2 f) := by
  rw [G2]
  exact (hP.slash (4 : ℤ) (ModularGroup.T * ModularGroup.S)).add hP

lemma InP_H2 {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (H2 f) := by
  have h1 : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ) ^ 2 * G0 f τ) :=
    (Work.Kernels.KernelGrowth.InP_coe.pow 2).mul (InP_G0 hP)
  have h2 : Work.Kernels.InP (fun τ : ℍ => (2 : ℂ) * (τ : ℂ) * G1 f τ) :=
    (Work.Kernels.InP.const_mul 2 Work.Kernels.KernelGrowth.InP_coe).mul (InP_G1 hP)
  have h3 : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ) ^ 2 * G0 f τ - (2 : ℂ) * (τ : ℂ) * G1 f τ
      + G2 f τ) := (h1.sub h2).add (InP_G2 hP)
  unfold H2
  exact h3

lemma InP_H1 {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (H1 f) := by
  have h1 : Work.Kernels.InP (fun τ : ℍ => (-2 : ℂ) * (τ : ℂ) * G0 f τ) :=
    (Work.Kernels.InP.const_mul (-2) Work.Kernels.KernelGrowth.InP_coe).mul (InP_G0 hP)
  have h2 : Work.Kernels.InP (fun τ : ℍ => (2 : ℂ) * G1 f τ) :=
    Work.Kernels.InP.const_mul 2 (InP_G1 hP)
  unfold H1
  exact h1.add h2

lemma InP_Mmod {f : ℍ → ℂ} (hP : Work.Kernels.InP f) : Work.Kernels.InP (Mmod f) := by
  have h1 : Work.Kernels.InP (fun τ : ℍ => H0 f τ) := InP_G0 hP
  have h2 : Work.Kernels.InP
      (fun τ : ℍ => ((Real.pi * Complex.I / 6) * Work.Kernels.E2Fun τ) * H1 f τ) :=
    (Work.Kernels.InP.const_mul (Real.pi * Complex.I / 6)
      Work.Kernels.ClassicalFacts.E2Fun_mem_InP).mul (InP_H1 hP)
  unfold Mmod
  exact h1.sub h2

/-! ## The modular forms `h_2`, `h_1` and `m` -/

/-- **`h_2 = 0`**: the weight-two invariant function `h_2` is a modular form of weight two,
and there are none. -/
lemma H2_eq_zero {f : ℍ → ℂ} (hP : Work.Kernels.InP f)
    (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (hT2 : AnnT2 f) : H2 f = 0 := by
  obtain ⟨G, hG⟩ := Work.Modular.modularForm_of_slash_invariant (k := (2 : ℤ))
    (SlashInvariantForm.slash_action_generators_SL2Z (H2_slash_S hS) (H2_slash_T hS hT2))
    (InP_H2 hP).1
    (boundedAtImInfty_of_periodic_inP (InP_H2 hP) (H2_vadd hS hT2))
  have hG0 : G = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero G
  rw [hG0] at hG
  simpa using hG.symm

/-- `h_1` is a modular form of weight four. -/
lemma H1_modular {f : ℍ → ℂ} (hP : Work.Kernels.InP f)
    (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (hT2 : AnnT2 f) (h2 : H2 f = 0) :
    ∃ H : ModularForm 𝒮ℒ 4, ⇑H = H1 f :=
  Work.Modular.modularForm_of_slash_invariant
    (SlashInvariantForm.slash_action_generators_SL2Z (H1_slash_S hS h2) (H1_slash_T hT2))
    (InP_H1 hP).1
    (boundedAtImInfty_of_periodic_inP (InP_H1 hP) (H1_vadd hT2))

/-- `m` is a modular form of weight six. -/
lemma Mmod_modular {f : ℍ → ℂ} (hP : Work.Kernels.InP f)
    (hS : f ∣[(4 : ℤ)] ModularGroup.S = -f) (hT2 : AnnT2 f) (h2 : H2 f = 0) :
    ∃ M : ModularForm 𝒮ℒ 6, ⇑M = Mmod f :=
  Work.Modular.modularForm_of_slash_invariant
    (SlashInvariantForm.slash_action_generators_SL2Z (Mmod_slash_S hS h2) (Mmod_slash_T hT2))
    (InP_Mmod hP).1
    (boundedAtImInfty_of_periodic_inP (InP_Mmod hP) (Mmod_vadd hT2))

/-! ## Limits along the imaginary axis -/

lemma tendsto_exp_decay (B : ℝ) :
    Tendsto (fun t : ℝ => B * Real.exp (-(2 * Real.pi * t))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => -(2 * Real.pi * t)) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / (2 * Real.pi))] with t ht
    have hpi : 0 < 2 * Real.pi := by positivity
    have h2 : -b ≤ t * (2 * Real.pi) := by
      have h3 := mul_le_mul_of_nonneg_right ht (le_of_lt hpi)
      rwa [div_mul_cancel₀ (-b) (ne_of_gt hpi)] at h3
    linarith
  simpa using (Real.tendsto_exp_atBot.comp h1).const_mul B

lemma tendsto_t_mul_exp_decay :
    Tendsto (fun t : ℝ => t * Real.exp (-(2 * Real.pi * t))) atTop (𝓝 0) := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have h1 : Tendsto (fun t : ℝ => (2 * Real.pi * t) ^ 1 * Real.exp (-(2 * Real.pi * t)))
      atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop h2pi)
  have h2 := h1.div_const (2 * Real.pi)
  have h3 : (fun t : ℝ => ((2 * Real.pi * t) ^ 1 * Real.exp (-(2 * Real.pi * t))) / (2 * Real.pi))
      = fun t : ℝ => t * Real.exp (-(2 * Real.pi * t)) := by
    funext t
    rw [pow_one]
    field_simp
  rw [h3] at h2
  simpa using h2

lemma tendsto_t_mul_exp_decay_mul (B : ℝ) :
    Tendsto (fun t : ℝ => t * (B * Real.exp (-(2 * Real.pi * t)))) atTop (𝓝 0) := by
  have h := tendsto_t_mul_exp_decay.const_mul B
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- Squeeze for complex-valued sequences. -/
lemma tendsto_zero_of_norm_le {g : ℝ → ℂ} {u : ℝ → ℝ}
    (hb : ∀ᶠ t in atTop, ‖g t‖ ≤ u t) (hu : Tendsto u atTop (𝓝 0)) : Tendsto g atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) hb hu

/-- A sequence that is `O (exp (-2π t))` off its limit converges to that limit. -/
lemma tendsto_of_decay {g : ℝ → ℂ} {a : ℂ} {A B : ℝ}
    (h : ∀ t : ℝ, A ≤ t → ‖g t - a‖ ≤ B * Real.exp (-(2 * Real.pi * t))) :
    Tendsto g atTop (𝓝 a) := by
  have h1 : Tendsto (fun t : ℝ => g t - a) atTop (𝓝 0) :=
    tendsto_zero_of_norm_le (Filter.eventually_atTop.mpr ⟨A, h⟩) (tendsto_exp_decay B)
  have h2 := h1.add_const a
  simpa using h2

/-- The corresponding statement for `t` times the deviation. -/
lemma tendsto_imagPoint_mul_of_decay {g : ℝ → ℂ} {a : ℂ} {A B : ℝ}
    (h : ∀ t : ℝ, A ≤ t → ‖g t - a‖ ≤ B * Real.exp (-(2 * Real.pi * t))) :
    Tendsto (fun t : ℝ => (Work.Modular.imagPoint t : ℂ) * (g t - a)) atTop (𝓝 0) := by
  refine tendsto_zero_of_norm_le ?_ (tendsto_t_mul_exp_decay_mul B)
  filter_upwards [Filter.eventually_ge_atTop (max (max A 1) 1)] with t ht
  have htA : A ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
  have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
  have hcoe : (Work.Modular.imagPoint t : ℂ) = (t : ℂ) * Complex.I :=
    Work.Modular.coe_imagPoint ht1
  have hnorm : ‖(Work.Modular.imagPoint t : ℂ)‖ = t := by
    rw [hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt ht1)]
  calc ‖(Work.Modular.imagPoint t : ℂ) * (g t - a)‖
      = t * ‖g t - a‖ := by rw [norm_mul, hnorm]
    _ ≤ t * (B * Real.exp (-(2 * Real.pi * t))) :=
        mul_le_mul_of_nonneg_left (h t htA) (le_of_lt ht1)

/-- `E₂ · h₁ - a` decays like `exp (-2π t)` when `h₁` is bounded and `E₂ - 1 = O(q)`. -/
lemma tendsto_imagPoint_mul_E2_sub (f : ℍ → ℂ) {A' AE BE C : ℝ} (hBE : 0 ≤ BE)
    (hA' : max AE 1 ≤ A')
    (hdE : ∀ t : ℝ, max AE 1 ≤ t →
      ‖Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1‖ ≤ BE * Real.exp (-(2 * Real.pi * t)))
    (hb : ∀ t : ℝ, A' ≤ t → ‖H1 f (Work.Modular.imagPoint t)‖ ≤ C) :
    Tendsto (fun t : ℝ => (Work.Modular.imagPoint t : ℂ) *
      ((Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1) * H1 f (Work.Modular.imagPoint t)))
      atTop (𝓝 0) := by
  refine tendsto_zero_of_norm_le
    (u := fun t : ℝ => (max C 0) * (t * (BE * Real.exp (-(2 * Real.pi * t))))) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (max A' 1) 1)] with t ht
    have htA' : A' ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
    have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
    have hcoe : (Work.Modular.imagPoint t : ℂ) = (t : ℂ) * Complex.I :=
      Work.Modular.coe_imagPoint ht1
    have hnorm : ‖(Work.Modular.imagPoint t : ℂ)‖ = t := by
      rw [hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt ht1)]
    have hb' : ‖H1 f (Work.Modular.imagPoint t)‖ ≤ max C 0 :=
      le_trans (hb t htA') (le_max_left _ _)
    have hdec := hdE t (le_trans hA' htA')
    calc ‖(Work.Modular.imagPoint t : ℂ) *
          ((Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1) * H1 f (Work.Modular.imagPoint t))‖
        = t * (‖Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1‖ *
            ‖H1 f (Work.Modular.imagPoint t)‖) := by
          rw [norm_mul, norm_mul, hnorm]
      _ ≤ t * ((BE * Real.exp (-(2 * Real.pi * t))) * max C 0) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt ht1)
          calc ‖Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1‖
                * ‖H1 f (Work.Modular.imagPoint t)‖
              ≤ (BE * Real.exp (-(2 * Real.pi * t))) * ‖H1 f (Work.Modular.imagPoint t)‖ :=
                mul_le_mul_of_nonneg_right hdec (norm_nonneg _)
            _ ≤ (BE * Real.exp (-(2 * Real.pi * t))) * max C 0 :=
                mul_le_mul_of_nonneg_left hb' (mul_nonneg hBE (Real.exp_nonneg _))
      _ = (max C 0) * (t * (BE * Real.exp (-(2 * Real.pi * t)))) := by ring
  · simpa using (tendsto_t_mul_exp_decay_mul BE).const_mul (max C 0)

/-! ## The endgame: `Ann₄(𝓘₊, 𝒫)` is two-dimensional and nothing in it is `o(1)` -/

theorem AnnPlusWeightFourP : Work.Rigidity.SingleRigidityP 4 (-1 : ℂ) 0 := by
  intro f hP hAnnT2 hSlash hDecay
  have hS : f ∣[(4 : ℤ)] ModularGroup.S = -f := by
    funext τ
    have h := hSlash τ
    simpa using h
  have h2z : H2 f = 0 := H2_eq_zero hP hS hAnnT2
  obtain ⟨H, hH⟩ := H1_modular hP hS hAnnT2 h2z
  obtain ⟨M, hM⟩ := Mmod_modular hP hS hAnnT2 h2z
  have hH' : ∀ τ : ℍ, H τ = H1 f τ := fun τ => congrFun hH τ
  have hM' : ∀ τ : ℍ, M τ = Mmod f τ := fun τ => congrFun hM τ
  obtain ⟨A1, B1, hB1, hd1⟩ := modularForm_cusp_decay H
  obtain ⟨A0, B0, hB0, hd0⟩ := modularForm_cusp_decay M
  obtain ⟨AE, BE, hBE, hdE⟩ := E2Fun_sub_one_decay
  have hd1i : ∀ t : ℝ, max A1 1 ≤ t →
      ‖H1 f (Work.Modular.imagPoint t) - cterm H‖ ≤ B1 * Real.exp (-(2 * Real.pi * t)) := by
    intro t ht
    have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
    have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
    have h := hd1 (Work.Modular.imagPoint t) (by rw [him]; exact le_trans (le_max_left _ _) ht)
    simpa only [hH', him] using h
  have hd0i : ∀ t : ℝ, max A0 1 ≤ t →
      ‖Mmod f (Work.Modular.imagPoint t) - cterm M‖ ≤ B0 * Real.exp (-(2 * Real.pi * t)) := by
    intro t ht
    have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
    have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
    have h := hd0 (Work.Modular.imagPoint t) (by rw [him]; exact le_trans (le_max_left _ _) ht)
    simpa only [hM', him] using h
  have hdEi : ∀ t : ℝ, max AE 1 ≤ t →
      ‖Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1‖
        ≤ BE * Real.exp (-(2 * Real.pi * t)) := by
    intro t ht
    have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
    have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
    simpa only [him] using hdE (Work.Modular.imagPoint t)
      (by rw [him]; exact le_trans (le_max_left _ _) ht)
  -- boundedness of `h_1` along the imaginary axis
  obtain ⟨C1, A1b, hC1⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp
    (ModularFormClass.bdd_at_infty H)
  have hH1bdd : ∀ t : ℝ, max (max A1b 1) (max AE 1) ≤ t →
      ‖H1 f (Work.Modular.imagPoint t)‖ ≤ max C1 0 := by
    intro t ht
    have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ht))
    have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
    have hA : A1b ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ht)
    have h := hC1 (Work.Modular.imagPoint t) (by rw [him]; exact hA)
    have h' : ‖H1 f (Work.Modular.imagPoint t)‖ ≤ C1 := by simpa only [hH'] using h
    exact le_trans h' (le_max_left _ _)
  -- the explicit form of `f`
  have hf_eq : ∀ τ : ℍ, f τ = (τ : ℂ) * Mmod f τ
      + (Real.pi * Complex.I / 6) * (τ : ℂ) * Work.Kernels.E2Fun τ * H1 f τ + H1 f τ / 2 := by
    intro τ
    have h0 : H0 f τ = fstDiff f τ := by simp only [H0, G0_eq_fstDiff]
    have h1 : H1 f τ = -2 * (τ : ℂ) * fstDiff f τ + 2 * f τ := by
      simp only [H1, G1, G0_eq_fstDiff]
    have hM0 : H0 f τ = Mmod f τ
        + (Real.pi * Complex.I / 6) * Work.Kernels.E2Fun τ * H1 f τ := by
      simp only [Mmod]
      ring
    have h2 : f τ = (τ : ℂ) * H0 f τ + H1 f τ / 2 := by
      rw [h0]
      linear_combination (-1 / 2) * h1
    rw [h2, hM0]
    ring
  -- Equation 1: the limit of `f / τ`
  have hEq1 : cterm M + (Real.pi * Complex.I / 6) * cterm H = 0 := by
    have heq : ∀ t : ℝ, f (Work.Modular.imagPoint t) / (Work.Modular.imagPoint t : ℂ)
        = Mmod f (Work.Modular.imagPoint t)
          + (Real.pi * Complex.I / 6) * Work.Kernels.E2Fun (Work.Modular.imagPoint t)
              * H1 f (Work.Modular.imagPoint t)
          + H1 f (Work.Modular.imagPoint t) / (2 * (Work.Modular.imagPoint t : ℂ)) := by
      intro t
      rw [hf_eq]
      have hτ : (Work.Modular.imagPoint t : ℂ) ≠ 0 := coe_ne_zero _
      field_simp
    have hlim0 : Tendsto (fun t : ℝ => f (Work.Modular.imagPoint t)
        / (Work.Modular.imagPoint t : ℂ)) atTop (𝓝 0) := by
      obtain ⟨φ, hφ, hφ'⟩ := hDecay
      refine tendsto_zero_of_norm_le (u := fun t : ℝ => φ t / t) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with t ht
        have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one ht
        have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
        have hcoe : (Work.Modular.imagPoint t : ℂ) = (t : ℂ) * Complex.I :=
          Work.Modular.coe_imagPoint ht1
        have hstrip : InStrip (Work.Modular.imagPoint t) := by
          constructor <;> · rw [← UpperHalfPlane.coe_re, hcoe, Complex.mul_re]; simp
        have hfb : ‖f (Work.Modular.imagPoint t)‖ ≤ φ t := by
          have h := hφ' (Work.Modular.imagPoint t) hstrip
          rw [him] at h
          simpa using h
        have hnorm : ‖(Work.Modular.imagPoint t : ℂ)‖ = t := by
          rw [hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt ht1)]
        rw [norm_div, hnorm]
        exact div_le_div_of_nonneg_right hfb (le_of_lt ht1)
      · rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun t => abs_nonneg _) ?_
          (by simpa using hφ.abs)
        filter_upwards [Filter.eventually_ge_atTop 1] with t ht
        have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one ht
        rw [Real.norm_eq_abs, abs_div, abs_of_pos ht1, div_le_iff₀ ht1]
        nlinarith [abs_nonneg (φ t), ht]
    have hlimH2 : Tendsto (fun t : ℝ => H1 f (Work.Modular.imagPoint t)
        / (2 * (Work.Modular.imagPoint t : ℂ))) atTop (𝓝 0) := by
      refine tendsto_zero_of_norm_le (u := fun t : ℝ => (max C1 0) / (2 * t)) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (max (max (max A1b 1) (max AE 1)) 1)]
          with t ht
        have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
        have hcoe : (Work.Modular.imagPoint t : ℂ) = (t : ℂ) * Complex.I :=
          Work.Modular.coe_imagPoint ht1
        have hb : ‖H1 f (Work.Modular.imagPoint t)‖ ≤ max C1 0 :=
          hH1bdd t (le_trans (le_max_left _ _) ht)
        have hcoeC : ‖(Work.Modular.imagPoint t : ℂ)‖ = t := by
          rw [hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt ht1)]
        have hdn : ‖(2 * (Work.Modular.imagPoint t : ℂ))‖ = 2 * t := by
          rw [norm_mul, hcoeC]
          norm_num
        rw [norm_div, hdn]
        exact div_le_div_of_nonneg_right hb (by linarith)
      · simpa using tendsto_const_nhds.div_atTop
          (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have hlim1 : Tendsto (fun t : ℝ => Mmod f (Work.Modular.imagPoint t)
        + (Real.pi * Complex.I / 6) * Work.Kernels.E2Fun (Work.Modular.imagPoint t)
            * H1 f (Work.Modular.imagPoint t)
        + H1 f (Work.Modular.imagPoint t) / (2 * (Work.Modular.imagPoint t : ℂ)))
        atTop (𝓝 (cterm M + (Real.pi * Complex.I / 6) * 1 * cterm H)) := by
      have hlimM : Tendsto (fun t : ℝ => Mmod f (Work.Modular.imagPoint t))
          atTop (𝓝 (cterm M)) := tendsto_of_decay hd0i
      have hlimE : Tendsto (fun t : ℝ => Work.Kernels.E2Fun (Work.Modular.imagPoint t))
          atTop (𝓝 1) := tendsto_of_decay hdEi
      have hlimH : Tendsto (fun t : ℝ => H1 f (Work.Modular.imagPoint t))
          atTop (𝓝 (cterm H)) := tendsto_of_decay hd1i
      have hmain := (hlimM.add ((hlimE.const_mul (Real.pi * Complex.I / 6)).mul hlimH)).add hlimH2
      simpa only [add_zero] using hmain
    have h := tendsto_nhds_unique hlim0
      (hlim1.congr' (Eventually.of_forall fun t => (heq t).symm))
    simpa using h.symm
  -- Equation 2: the limit of `f` itself
  have hEq2 : cterm H = 0 := by
    have heq : ∀ t : ℝ, f (Work.Modular.imagPoint t)
        = (Work.Modular.imagPoint t : ℂ) * (Mmod f (Work.Modular.imagPoint t) - cterm M)
          + (Real.pi * Complex.I / 6) * (Work.Modular.imagPoint t : ℂ)
              * (Work.Kernels.E2Fun (Work.Modular.imagPoint t)
                  * H1 f (Work.Modular.imagPoint t) - cterm H)
          + H1 f (Work.Modular.imagPoint t) / 2 := by
      intro t
      have h5 : (Work.Modular.imagPoint t : ℂ) * (cterm M
          + (Real.pi * Complex.I / 6) * cterm H) = 0 := by rw [hEq1, mul_zero]
      rw [hf_eq (Work.Modular.imagPoint t)]
      linear_combination h5
    have hlimf : Tendsto (fun t : ℝ => f (Work.Modular.imagPoint t)) atTop (𝓝 0) := by
      obtain ⟨φ, hφ, hφ'⟩ := hDecay
      refine tendsto_zero_of_norm_le (u := φ) ?_ hφ
      filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      have ht1 : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have him : (Work.Modular.imagPoint t).im = t := Work.Modular.imagPoint_im ht1
      have hcoe : (Work.Modular.imagPoint t : ℂ) = (t : ℂ) * Complex.I :=
        Work.Modular.coe_imagPoint ht1
      have hstrip : InStrip (Work.Modular.imagPoint t) := by
        constructor <;> · rw [← UpperHalfPlane.coe_re, hcoe, Complex.mul_re]; simp
      have h := hφ' (Work.Modular.imagPoint t) hstrip
      rw [him] at h
      simpa using h
    have hlimrhs : Tendsto (fun t : ℝ => (Work.Modular.imagPoint t : ℂ)
          * (Mmod f (Work.Modular.imagPoint t) - cterm M)
        + (Real.pi * Complex.I / 6) * (Work.Modular.imagPoint t : ℂ)
            * (Work.Kernels.E2Fun (Work.Modular.imagPoint t)
                * H1 f (Work.Modular.imagPoint t) - cterm H)
        + H1 f (Work.Modular.imagPoint t) / 2) atTop (𝓝 (0 + 0 + cterm H / 2)) := by
      have h1 : Tendsto (fun t : ℝ => (Work.Modular.imagPoint t : ℂ)
          * (Mmod f (Work.Modular.imagPoint t) - cterm M)) atTop (𝓝 0) :=
        tendsto_imagPoint_mul_of_decay hd0i
      have hmid : Tendsto (fun t : ℝ => (Real.pi * Complex.I / 6) * (Work.Modular.imagPoint t : ℂ)
          * (Work.Kernels.E2Fun (Work.Modular.imagPoint t) * H1 f (Work.Modular.imagPoint t)
              - cterm H)) atTop (𝓝 0) := by
        have hA' : max AE 1 ≤ max (max A1b 1) (max AE 1) := le_max_right _ _
        have hE := tendsto_imagPoint_mul_E2_sub f hBE hA' hdEi hH1bdd
        have hH1 := tendsto_imagPoint_mul_of_decay hd1i
        have hsum := (hE.add hH1).const_mul (Real.pi * Complex.I / 6)
        have heq2 : (fun t : ℝ => (Real.pi * Complex.I / 6)
              * ((Work.Modular.imagPoint t : ℂ)
                  * ((Work.Kernels.E2Fun (Work.Modular.imagPoint t) - 1)
                      * H1 f (Work.Modular.imagPoint t))
                + (Work.Modular.imagPoint t : ℂ) * (H1 f (Work.Modular.imagPoint t) - cterm H)))
            = fun t : ℝ => (Real.pi * Complex.I / 6) * (Work.Modular.imagPoint t : ℂ)
              * (Work.Kernels.E2Fun (Work.Modular.imagPoint t) * H1 f (Work.Modular.imagPoint t)
                  - cterm H) := by
          funext t; ring
        rw [heq2] at hsum
        simpa using hsum
      have hH : Tendsto (fun t : ℝ => H1 f (Work.Modular.imagPoint t) / 2)
          atTop (𝓝 (cterm H / 2)) := (tendsto_of_decay hd1i).div_const 2
      exact (h1.add hmid).add hH
    have h := tendsto_nhds_unique hlimf
      (hlimrhs.congr' (Eventually.of_forall fun t => (heq t).symm))
    have h2 : cterm H / 2 = 0 := by simpa using h.symm
    exact (div_eq_zero_iff.mp h2).resolve_right (by norm_num : (2 : ℂ) ≠ 0)
  -- `h_1` and `m` are cusp forms of weight `< 12`, hence vanish
  have hH1zero : H1 f = 0 := by
    have h := modularForm_eq_zero_of_constTerm_eq_zero H (by norm_num : (4 : ℤ) < 12) hEq2
    rw [← hH]
    exact h
  have hMzero : Mmod f = 0 := by
    have ha0 : cterm M = 0 := by
      have h := hEq1
      rw [hEq2] at h
      simpa using h
    have h := modularForm_eq_zero_of_constTerm_eq_zero M (by norm_num : (6 : ℤ) < 12) ha0
    rw [← hM]
    exact h
  have hf0 : f = 0 := by
    funext τ
    have h := hf_eq τ
    rw [hMzero, hH1zero] at h
    simpa using h
  exact hf0

end Work.Rigidity
