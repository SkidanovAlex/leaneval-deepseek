import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.All
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.ThetaAux
import Submission.Work.Rigidity.bounded_on_lt_im_of_periodic

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-- The cusp parameter `e^{πi z}` of the `z`-variable. -/
def Ecusp (z : ℍ) : ℂ := Complex.exp (Real.pi * Complex.I * (z : ℂ))

/-- The `z`-basis `P_0 = 𝓛_S`, `P_1 = -V`, `P_2 = U² - W²` (cf. `z^{-2j}ψ̃_j(S·z)`). -/
def Pcusp (ℓ : Work.Kernels.LogLambdaData) (m : Fin 3) (z : ℍ) : ℂ :=
  if m = 0 then ℓ.L_S z
  else if m = 1 then - Work.Kernels.VFun z
  else Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2

/-- The `τ`-weights `(f_{v_0}, f_{v_1}, f_{v_2})` of `f_k` in the `τ`-factor. -/
def vlen (d : ℕ) : Fin 3 → ℤ := if d = 8 then ![4, 2, 0] else ![12, 10, 8]

/-- The `z`-weights `(f_{u_0}, f_{u_1}, f_{u_2})` of `f_k` in the `z`-factor. -/
def ulen (d : ℕ) : Fin 3 → ℤ := if d = 8 then ![10, 8, 6] else ![2, 0, -2]

/-- The coefficient matrix `B^{(d)}` of `Υ_-^{(d)}` (CKMRV Section 4.4). -/
def Mcusp (d : ℕ) (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  if d = 8 then
    !![(-2 : ℂ) * Work.Kernels.c1728, 0, 0;
       0, 1, -1;
       0, Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ, Work.Kernels.jInvariantFun τ]
  else
    !![(-2 : ℂ) * Work.Kernels.c1728,
         (-2 : ℂ) * Work.Kernels.c1728 *
           (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), 0;
       0, Work.Kernels.jInvariantFun τ +
             2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -1;
       0, Work.Kernels.c1728 -
             2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) -
             Work.Kernels.jInvariantFun τ, 1]

/-- The cleared cusp numerator `N₀ = Δ(z)(jτ-jz)·z^{-(2-d/2)}K_-^{(d)}(τ,S·z)`, written as a
holomorphic function of `z`. -/
def Ncusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ *
    ∑ m : Fin 3,
      (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
        Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) * Pcusp ℓ m z


/-! ## Elementary properties of the cusp numerator -/

lemma Pcusp_zero (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : Pcusp ℓ 0 z = ℓ.L_S z := by
  simp [Pcusp]

lemma Pcusp_one (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Pcusp ℓ 1 z = - Work.Kernels.VFun z := by
  simp [Pcusp]

lemma Pcusp_two (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Pcusp ℓ 2 z = Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2 := by
  simp [Pcusp]


lemma norm_Ecusp (z : ℍ) : ‖Ecusp z‖ = Real.exp (-(Real.pi * z.im)) := by
  rw [Ecusp, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (z : ℂ)
      = ((Real.pi : ℝ) : ℂ) * (Complex.I * (z : ℂ)) by ring,
    Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

lemma Ecusp_vadd_one (z : ℍ) : Ecusp ((1 : ℝ) +ᵥ z) = - Ecusp z := by
  rw [Ecusp, Ecusp, UpperHalfPlane.coe_vadd]
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I * (1 + ↑z)
      = (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I * ↑z by ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma Ecusp_sq_vadd_one (z : ℍ) : (Ecusp ((1 : ℝ) +ᵥ z)) ^ 2 = (Ecusp z) ^ 2 := by
  rw [Ecusp_vadd_one]; ring

lemma Pcusp_vadd_one (ℓ : Work.Kernels.LogLambdaData) (m : Fin 3) (z : ℍ) :
    Pcusp ℓ m ((1 : ℝ) +ᵥ z) = - Pcusp ℓ m z := by
  fin_cases m
  · change Pcusp ℓ (0 : Fin 3) ((1 : ℝ) +ᵥ z) = - Pcusp ℓ (0 : Fin 3) z
    rw [Pcusp_zero, Pcusp_zero]
    exact Work.Kernels.KernelFacts.L_S_vadd_one ℓ z
  · change Pcusp ℓ (1 : Fin 3) ((1 : ℝ) +ᵥ z) = - Pcusp ℓ (1 : Fin 3) z
    simp only [Pcusp_one, Work.Kernels.KernelFacts.VFun_vadd_one, neg_neg]
  · change Pcusp ℓ (2 : Fin 3) ((1 : ℝ) +ᵥ z) = - Pcusp ℓ (2 : Fin 3) z
    simp only [Pcusp_two, Work.Kernels.KernelFacts.UFun_vadd_one,
      Work.Kernels.KernelFacts.WFun_vadd_one]
    ring

lemma fk_ulen_vadd_one (d : ℕ) (m : Fin 3) (z : ℍ) :
    Work.Kernels.fk (ulen d m) ((1 : ℝ) +ᵥ z) = Work.Kernels.fk (ulen d m) z :=
  Work.Kernels.KernelFacts.fk_vadd_one _ z

lemma Mcusp_vadd_one (d : ℕ) (τ z : ℍ) : Mcusp d τ ((1 : ℝ) +ᵥ z) = Mcusp d τ z := by
  unfold Mcusp
  split_ifs <;>
    simp only [Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

lemma Ncusp_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) :
    Ncusp ℓ d τ ((1 : ℝ) +ᵥ z) = - Ncusp ℓ d τ z := by
  have hsum : (∑ m : Fin 3,
        (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
          Mcusp d τ ((1 : ℝ) +ᵥ z) i m * Work.Kernels.fk (ulen d m) ((1 : ℝ) +ᵥ z)) *
          Pcusp ℓ m ((1 : ℝ) +ᵥ z))
      = -(∑ m : Fin 3,
        (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
          Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) * Pcusp ℓ m z) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hm : (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
          Mcusp d τ ((1 : ℝ) +ᵥ z) i m * Work.Kernels.fk (ulen d m) ((1 : ℝ) +ᵥ z))
        = (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
          Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) :=
      Finset.sum_congr rfl (fun i _ => by rw [Mcusp_vadd_one, fk_ulen_vadd_one])
    rw [hm, Pcusp_vadd_one, mul_neg]
  unfold Ncusp
  rw [hsum, mul_neg]

/-! ## The `z`-transformation laws of the basis vectors -/

lemma psitVec_S_zero (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Work.Kernels.psitVec ℓ (ModularGroup.S • z) (0 : Fin 3) = Pcusp ℓ (0 : Fin 3) z := by
  rw [Pcusp_zero]
  have h := congr_fun ℓ.slash_S z
  rw [Work.Kernels.KernelFacts.kpc_slash_S_apply] at h
  simpa [Work.Kernels.psitVec] using h

lemma psitVec_S_one (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Work.Kernels.psitVec ℓ (ModularGroup.S • z) (1 : Fin 3) =
      (z : ℂ) ^ 2 * Pcusp ℓ (1 : Fin 3) z := by
  rw [Pcusp_one]
  rw [show Work.Kernels.psitVec ℓ (ModularGroup.S • z) (1 : Fin 3)
      = Work.Kernels.WFun (ModularGroup.S • z) by simp [Work.Kernels.psitVec]]
  rw [Work.Kernels.KernelFacts.WFun_S_smul]
  ring

lemma psitVec_S_two (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Work.Kernels.psitVec ℓ (ModularGroup.S • z) (2 : Fin 3) =
      (z : ℂ) ^ 4 * Pcusp ℓ (2 : Fin 3) z := by
  rw [Pcusp_two]
  rw [show Work.Kernels.psitVec ℓ (ModularGroup.S • z) (2 : Fin 3)
      = Work.Kernels.UFun (ModularGroup.S • z) ^ 2 -
        Work.Kernels.VFun (ModularGroup.S • z) ^ 2 by simp [Work.Kernels.psitVec]]
  rw [Work.Kernels.KernelFacts.UFun_S_smul, Work.Kernels.KernelFacts.VFun_S_smul]
  ring

lemma psitVec_S (ℓ : Work.Kernels.LogLambdaData) (m : Fin 3) (z : ℍ) :
    Work.Kernels.psitVec ℓ (ModularGroup.S • z) m =
      (z : ℂ) ^ (2 * ((m : ℕ) : ℤ)) * Pcusp ℓ m z := by
  fin_cases m
  · change Work.Kernels.psitVec ℓ (ModularGroup.S • z) (0 : Fin 3) =
      (z : ℂ) ^ (2 * (((0 : Fin 3) : ℕ) : ℤ)) * Pcusp ℓ (0 : Fin 3) z
    rw [psitVec_S_zero]
    simp
  · change Work.Kernels.psitVec ℓ (ModularGroup.S • z) (1 : Fin 3) =
      (z : ℂ) ^ (2 * (((1 : Fin 3) : ℕ) : ℤ)) * Pcusp ℓ (1 : Fin 3) z
    rw [psitVec_S_one]
    norm_num
  · change Work.Kernels.psitVec ℓ (ModularGroup.S • z) (2 : Fin 3) =
      (z : ℂ) ^ (2 * (((2 : Fin 3) : ℕ) : ℤ)) * Pcusp ℓ (2 : Fin 3) z
    rw [psitVec_S_two]
    norm_num

/-! ## The decomposition of `K_-(τ, S·z)` -/

lemma KMinus_S_decomp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) :
    Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z) =
      (z : ℂ) ^ (2 - (d : ℤ) / 2) * ∑ m : Fin 3,
        Work.Kernels.TildeFacts.KMinusCol ℓ d τ m z * Pcusp ℓ m z := by
  rw [Work.Kernels.TildeFacts.KMinus_colsum_kza, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Work.Kernels.TildeFacts.KMinusCol_S_smul_kza ℓ d hd τ m z, psitVec_S ℓ m z]
  have hz : (z : ℂ) ≠ 0 := Work.Kernels.KernelFacts.kpc_tau_ne_zero z
  have hzb : (z : ℂ) ^ (2 - (d : ℤ) / 2 - 2 * ((m : ℕ) : ℤ)) *
        (z : ℂ) ^ (2 * ((m : ℕ) : ℤ)) = (z : ℂ) ^ (2 - (d : ℤ) / 2) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  rw [← hzb]
  ring

/-! ## The identification of `Ncusp` with `Δ(z)(jτ - jz) z^{-(2-d/2)} K_-(τ, S·z)` -/

open Work.Kernels.TildeFacts (KMinusCol) in
lemma vlen_eight : vlen 8 = Work.Kernels.TildeFacts.Kzb.v8 := rfl

lemma ulen_eight : ulen 8 = Work.Kernels.TildeFacts.Kzb.w8 := rfl

lemma vlen_twentyfour : vlen 24 = Work.Kernels.TildeFacts.Kzb.v24 := rfl

lemma ulen_twentyfour : ulen 24 = Work.Kernels.TildeFacts.Kzb.w24 := rfl

lemma Mcusp_eight (τ z : ℍ) : Mcusp 8 τ z = Work.Kernels.TildeFacts.Kzb.AMat8 τ := rfl

lemma Mcusp_twentyfour (τ z : ℍ) :
    Mcusp 24 τ z = Work.Kernels.TildeFacts.Kzb.AMat24 τ z := rfl

lemma C0_eq : Work.Kernels.TildeFacts.Kzb.C0 =
    (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ := rfl

/-- `D * (X * D⁻¹ * Y) = X * Y` for `D ≠ 0`. -/
lemma mul_inv_mul_cancel {D X Y : ℂ} (hD : D ≠ 0) : D * (X * D⁻¹ * Y) = X * Y := by
  rw [show D * (X * D⁻¹ * Y) = X * (D * D⁻¹) * Y from by ring, mul_inv_cancel₀ hD]
  ring

/-- Clearing the denominators of `Υ_-^{(d)}`: for `jτ ≠ jz`,
`Δ(z)(jτ - jz)·Υ_-^{(d)}(τ,z)_{im}` is the holomorphic entry
`C0·f_{v_i}(τ)·B^{(d)}(τ,z)_{im}·f_{u_m}(z)`. -/
lemma UpsilonMinus_clear (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) (i m : Fin 3)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        Work.Kernels.UpsilonMinus d τ z i m
      = Work.Kernels.TildeFacts.Kzb.C0 * Work.Kernels.fk (vlen d i) τ * Mcusp d τ z i m *
          Work.Kernels.fk (ulen d m) z := by
  have hD : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr h)
  rcases hd with rfl | rfl
  · rw [Work.Kernels.TildeFacts.Kzb.UpsilonMinus_eight_entry]
    rw [vlen_eight, ulen_eight, Mcusp_eight, Work.Kernels.TildeFacts.Kzb.Hfun,
      Work.Kernels.TildeFacts.Kzb.Jfun]
    exact mul_inv_mul_cancel hD
  · rw [Work.Kernels.TildeFacts.Kzb.UpsilonMinus_twentyfour_entry]
    rw [vlen_twentyfour, ulen_twentyfour, Mcusp_twentyfour, Work.Kernels.TildeFacts.Kzb.Hfun,
      Work.Kernels.TildeFacts.Kzb.Jfun]
    exact mul_inv_mul_cancel hD

/-- The column sum of `K_-^{(d)}(τ,·)` cleared by `Δ(z)(jτ - jz)`. -/
lemma KMinusCol_clear (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) (m : Fin 3) :
    Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        Work.Kernels.TildeFacts.KMinusCol ℓ d τ m z
      = Work.Kernels.TildeFacts.Kzb.C0 * (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i *
          Work.Kernels.fk (vlen d i) τ * Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) := by
  simp only [Work.Kernels.TildeFacts.KMinusCol]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        (Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinus d τ z i m)
      = Work.Kernels.psiVec ℓ τ i * (Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        Work.Kernels.UpsilonMinus d τ z i m) from by ring,
    UpsilonMinus_clear d hd τ z i m h]
  ring

/-- **The key identification.**  The holomorphic numerator `Ncusp` equals
`Δ(z)(jτ - jz) z^{-(2-d/2)} K_-^{(d)}(τ, S·z)` wherever `jτ ≠ jz`. -/
theorem Ncusp_ident (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Ncusp ℓ d τ z =
      Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        ((z : ℂ) ^ (-(2 - (d : ℤ) / 2)) *
          Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)) := by
  have hz : (z : ℂ) ≠ 0 := Work.Kernels.KernelFacts.kpc_tau_ne_zero z
  have hK : (z : ℂ) ^ (-(2 - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)
      = ∑ m : Fin 3, Work.Kernels.TildeFacts.KMinusCol ℓ d τ m z * Pcusp ℓ m z := by
    rw [KMinus_S_decomp ℓ d hd τ z, ← mul_assoc,
      show (z : ℂ) ^ (-(2 - (d : ℤ) / 2)) * (z : ℂ) ^ (2 - (d : ℤ) / 2) = 1 by
        rw [← zpow_add₀ hz, neg_add_cancel, zpow_zero],
      one_mul]
  rw [hK]
  unfold Ncusp
  rw [Finset.mul_sum, Finset.mul_sum, ← C0_eq]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        (Work.Kernels.TildeFacts.KMinusCol ℓ d τ m z * Pcusp ℓ m z)
      = (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) *
        Work.Kernels.TildeFacts.KMinusCol ℓ d τ m z) * Pcusp ℓ m z from by ring,
    KMinusCol_clear ℓ d hd τ z h m]
  ring

/-! ## Uniform exponential decay at the cusp -/

/-- **Uniform exponential decay at the cusp.**  A `1`-periodic holomorphic function which is
bounded on the upper half plane and tends to `0` at `i∞` decays like `exp (-2π Im)` on `Im ≥ 1`,
the constant being `B exp (2π)` where `B` bounds the function.  (The proof is the Schwarz lemma
applied to the descent of `F` to the punctured `q`-disc.) -/
theorem periodic_zero_cusp_decay {F : ℂ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hper : Function.Periodic F 1)
    (hhol : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hB : ∀ z : ℂ, 1 ≤ z.im → ‖F z‖ ≤ B)
    (hzero : Filter.Tendsto F (Filter.comap Complex.im Filter.atTop) (𝓝 0)) :
    ∀ z : ℂ, 1 ≤ z.im →
      ‖F z‖ ≤ B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)) := by
  have him_ev : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, 1 ≤ z.im := by
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    exact ⟨1, fun b hb z hz => by rw [hz]; exact hb⟩
  have him_pos : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, 0 < z.im :=
    him_ev.mono fun z hz => lt_of_lt_of_le one_pos hz
  set φ : ℂ → ℂ := Function.Periodic.cuspFunction 1 F with hφ
  have hbdf : (Filter.comap Complex.im Filter.atTop).BoundedAtFilter F :=
    Asymptotics.IsBigO.of_bound B (by
      filter_upwards [him_ev] with z hz
      simpa using hB z hz)
  have hhol' : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ F z := by
    filter_upwards [him_ev] with z hz
    exact hhol.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (lt_of_lt_of_le one_pos hz))
  have hφ0 : φ 0 = 0 := by
    rw [hφ]; exact Function.Periodic.cuspFunction_zero_of_zero_at_inf one_pos hzero
  have hφdiff0 : DifferentiableAt ℂ φ 0 := by
    rw [hφ]; exact Function.Periodic.differentiableAt_cuspFunction_zero one_pos hper hhol' hbdf
  have him_invQ : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → 0 < (Function.Periodic.invQParam 1 q).im := by
    intro q hq0 hq1
    rw [Function.Periodic.im_invQParam]
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by norm_num) (by positivity))
      (Real.log_neg (norm_pos_iff.mpr hq0) hq1)
  have hφdiff : DifferentiableOn ℂ φ (Metric.ball 0 1) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · exact hφdiff0.differentiableWithinAt
    · have him := him_invQ q hq0 hq
      have hdq : DifferentiableAt ℂ F (Function.Periodic.invQParam 1 q) :=
        hhol.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds him)
      have h1 : DifferentiableAt ℂ (Function.Periodic.cuspFunction 1 F)
          (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q)) :=
        Function.Periodic.differentiableAt_cuspFunction (h := 1) one_ne_zero hper hdq
      rw [Function.Periodic.qParam_right_inv (h := 1) one_ne_zero hq0] at h1
      rw [hφ]; exact h1.differentiableWithinAt
  set R₁ : ℝ := Real.exp (-(2 * Real.pi)) with hR₁
  have hR₁le : R₁ ≤ 1 := by rw [hR₁, Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have hmap : Set.MapsTo φ (Metric.ball 0 R₁) (Metric.closedBall (φ 0) B) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [hφ0, Metric.mem_closedBall, dist_self]; exact hB0
    · rw [Metric.mem_closedBall, hφ0, dist_eq_norm, sub_zero]
      have him : (1 : ℝ) ≤ (Function.Periodic.invQParam 1 q).im := by
        rw [Function.Periodic.im_invQParam]
        have hlog : Real.log ‖q‖ ≤ Real.log R₁ :=
          Real.log_le_log (norm_pos_iff.mpr hq0) (le_of_lt hq)
        have hR₁val : Real.log R₁ = -(2 * Real.pi) := by rw [hR₁, Real.log_exp]
        rw [hR₁val] at hlog
        have key : (-1 : ℝ) / (2 * Real.pi) * Real.log ‖q‖
            = -(Real.log ‖q‖ / (2 * Real.pi)) := by ring
        rw [key]
        have h2 : Real.log ‖q‖ / (2 * Real.pi) ≤ -1 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        linarith
      have h1 : φ q = F (Function.Periodic.invQParam 1 q) := by
        rw [hφ]; exact Function.Periodic.cuspFunction_eq_of_nonzero 1 F hq0
      rw [h1]
      exact hB _ him
  have hn : (fun x : ℂ => φ x - φ 0) =o[𝓝 0] (fun w : ℂ => ‖w - (0 : ℂ)‖ ^ (0 : ℕ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h0 : Filter.Tendsto (fun x : ℂ => φ x - φ 0) (𝓝 0) (𝓝 0) := by
      have hcont : Filter.Tendsto φ (𝓝 0) (𝓝 (φ 0)) := hφdiff0.continuousAt.tendsto
      have hc : Filter.Tendsto (fun _ : ℂ => φ 0) (𝓝 0) (𝓝 (φ 0)) := tendsto_const_nhds
      simpa using hcont.sub hc
    have h := (Metric.tendsto_nhds.mp h0) c hc
    filter_upwards [h] with w hw
    have hw' : ‖φ w - φ 0‖ < c := by simpa [dist_eq_norm] using hw
    calc ‖φ w - φ 0‖ ≤ c := le_of_lt hw'
      _ = c * ‖(‖w - (0 : ℂ)‖ ^ (0 : ℕ) : ℝ)‖ := by simp
  intro z hz1
  have hqnorm : ‖Function.Periodic.qParam 1 z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [Function.Periodic.norm_qParam]; norm_num
  have hR₁inv : R₁⁻¹ = Real.exp (2 * Real.pi) := by rw [hR₁, Real.exp_neg, inv_inv]
  have hqdiv : ‖Function.Periodic.qParam 1 z‖ / R₁
      = Real.exp (-(2 * Real.pi * z.im)) * Real.exp (2 * Real.pi) := by
    rw [div_eq_mul_inv, hqnorm, hR₁inv]
  rcases eq_or_lt_of_le hz1 with hy | hy
  · have h1 : ‖F z‖ ≤ B := hB z (le_of_eq hy)
    rw [← hy]
    have hBexp : B * Real.exp (2 * Real.pi) * (Real.exp (2 * Real.pi))⁻¹ = B := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _)), mul_one]
    calc ‖F z‖ ≤ B := h1
      _ = B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * (1 : ℝ))) := by
          rw [show -(2 * Real.pi * (1 : ℝ)) = -(2 * Real.pi) by ring, Real.exp_neg]
          exact hBexp.symm
  · have hqlt : ‖Function.Periodic.qParam 1 z‖ < R₁ := by
      rw [hqnorm, hR₁]
      exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, hy])
    have hmem : Function.Periodic.qParam 1 z ∈ Metric.ball (0 : ℂ) R₁ := by
      rwa [Metric.mem_ball, dist_zero_right]
    have h1 := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (f := φ) (c := 0) (R₁ := R₁) (R₂ := B) (n := 0)
      (hφdiff.mono (Metric.ball_subset_ball hR₁le)) hmap hn hmem
    rw [hφ0, dist_zero_right, dist_zero_right, pow_one] at h1
    rw [hφ, Function.Periodic.eq_cuspFunction (h := 1) one_ne_zero hper z] at h1
    rw [hqdiv] at h1
    calc ‖F z‖ ≤ B * (Real.exp (-(2 * Real.pi * z.im)) * Real.exp (2 * Real.pi)) := h1
      _ = B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)) := by ring

/-- The `ℍ`-version of `periodic_zero_cusp_decay`: a `1`-periodic holomorphic function on `ℍ`
which is bounded on `Im ≥ 1` and tends to `0` at `i∞` decays like `exp (-2π Im)`. -/
theorem periodic_zero_cusp_decay_uhp {f : ℍ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hper : ∀ z : ℍ, f ((1 : ℝ) +ᵥ z) = f z) (hhol : MDiff f)
    (hB : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ B)
    (hzero : Filter.Tendsto f atImInfty (𝓝 0)) :
    ∀ z : ℍ, 1 ≤ z.im →
      ‖f z‖ ≤ B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z.im)) := by
  set F : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 with hF
  have hFval : ∀ (w : ℂ) (hw : 0 < w.im), F w = f ⟨w, hw⟩ := by
    intro w hw; rw [hF]; exact dif_pos hw
  have hperC : Function.Periodic F 1 := by
    intro w
    by_cases hw : 0 < w.im
    · have hw' : 0 < (w + 1).im := by rw [Complex.add_im, Complex.one_im, add_zero]; exact hw
      rw [hFval (w + 1) hw', hFval w hw]
      have hcoe : (⟨w + 1, hw'⟩ : ℍ) = (1 : ℝ) +ᵥ (⟨w, hw⟩ : ℍ) := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_vadd]
        push_cast
        ring
      rw [hcoe, hper]
    · have hw' : ¬ 0 < (w + 1).im := by rw [Complex.add_im, Complex.one_im, add_zero]; exact hw
      simp only [hF]
      rw [dif_neg hw, dif_neg hw']
  have hholC : DifferentiableOn ℂ F {w : ℂ | 0 < w.im} := by
    have h1 : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w : ℂ | 0 < w.im} :=
      (UpperHalfPlane.mdifferentiable_iff).mp hhol
    refine DifferentiableOn.congr h1 (fun w hw => ?_)
    rw [hFval w hw]
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hBC : ∀ w : ℂ, 1 ≤ w.im → ‖F w‖ ≤ B := by
    intro w hw
    have hw0 : 0 < w.im := lt_of_lt_of_le one_pos hw
    rw [hFval w hw0]
    exact hB ⟨w, hw0⟩ (by simpa using hw)
  have hzeroC : Filter.Tendsto F (Filter.comap Complex.im Filter.atTop) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun w : ℂ => UpperHalfPlane.ofComplex w)
        (Filter.comap Complex.im Filter.atTop) UpperHalfPlane.atImInfty := by
      rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
      refine Filter.tendsto_atTop.mpr (fun b => ?_)
      filter_upwards [Filter.tendsto_comap.eventually (Filter.Ici_mem_atTop (max b 1))] with w hw
      have hw1 : 0 < w.im := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hw)
      have hb : b ≤ (UpperHalfPlane.ofComplex w).im := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw1]
        exact le_trans (le_max_left _ _) hw
      simpa only [Function.comp_apply] using hb
    have h2 : Filter.Tendsto (fun w : ℂ => f (UpperHalfPlane.ofComplex w))
        (Filter.comap Complex.im Filter.atTop) (𝓝 0) := hzero.comp h1
    refine Filter.Tendsto.congr' ?_ h2
    filter_upwards [Filter.tendsto_comap.eventually (Filter.Ici_mem_atTop (1 : ℝ))] with w hw
    have hw0 : 0 < w.im := lt_of_lt_of_le one_pos hw
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw0]
    exact (hFval w hw0).symm
  intro z hz
  have h := periodic_zero_cusp_decay hB0 hperC hholC hBC hzeroC (z : ℂ) (by simpa using hz)
  rwa [hFval (z : ℂ) z.im_pos] at h

end

