import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.orbit_classification
import Submission.Work.CKFinal.LineDecay.model_identity
import Submission.Work.CKFinal.LineDecay.vertical_ray_shift
import Submission.Work.CKFinal.LineDecay.Kfun_second_limits
import Submission.Work.CKFinal.LineDecay.Khat_second_residue
import Submission.Work.CKFinal.LineDecay.F1Half.Basic
import Submission.Work.CKFinal.LineDecay.HatLayer
import Submission.Work.Asymptotics.CuspExp.kernelKfun_cuspExp
import Submission.Work.Asymptotics.CuspExp.cuspModel_bound
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Kernels.KMinusSlash

/-!
# The model-subtracted ("D-shift") contour-shift identity: shared definitions

The model-subtracted kernel `D(τ,z) = K(τ, ofComplex z) - 𝒢_G(τ,z)` of the contour-shift
computation on the two lines `Re τ = ±1/2`, together with the ray/edge integrals `R₀, R±, J₁, J₂`
in which the shifted representation is expressed, and the elementary pointwise identities for the
cusp model `𝒢_G` (`Gmodel`).
-/

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-! ## The model-subtracted kernel and the pieces of the shift -/

/-- The model-subtracted kernel in the `ℂ`-coordinate of the second variable:
`D(τ,z) = K(τ, ofComplex z) - 𝒢_G(τ,z)`, where `𝒢_G = Gmodel G τ` is the cusp model. -/
def Dfun (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (z : ℂ) : ℂ :=
  K τ (UpperHalfPlane.ofComplex z) - Work.CKFinal.Gmodel G τ z

/-- `R₀ = ∫_H^∞ D(τ,i t)e^{-λt}dt`. -/
def R0 (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ t in Set.Ioi Work.CKFinal.hsplit,
    Dfun K G τ ((t : ℂ) * Complex.I) * Work.Asymptotics.gaussWeight r t

/-- `R₋ = ∫_H^∞ D(τ,i t - 1)e^{-λt}dt`. -/
def Rm (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ t in Set.Ioi Work.CKFinal.hsplit,
    Dfun K G τ ((t : ℂ) * Complex.I - 1) * Work.Asymptotics.gaussWeight r t

/-- `R₊ = ∫_H^∞ D(τ,i t + 1)e^{-λt}dt`. -/
def Rp (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ t in Set.Ioi Work.CKFinal.hsplit,
    Dfun K G τ ((t : ℂ) * Complex.I + 1) * Work.Asymptotics.gaussWeight r t

/-- `J₁(K) = ∫_0^1 K(τ,(x-1)+iH)e^{iλ(x+iH)}dx` for a general kernel `K`. -/
def J1K (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  ∫ x in (0 : ℝ)..Work.CKFinal.hsplit,
    Work.CKFinal.Kax K τ (x - 1) Work.CKFinal.hsplit
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- `J₂(K) = ∫_{-1}^0 K(τ,(x+1)+iH)e^{iλ(x+iH)}dx` for a general kernel `K`. -/
def J2K (K : ℍ → ℍ → ℂ) (r : ℝ) (τ : ℍ) : ℂ :=
  ∫ x in (-1 : ℝ)..0,
    Work.CKFinal.Kax K τ (x + 1) Work.CKFinal.hsplit
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- `J₁(D) = ∫_0^1 D(τ,(x-1)+iH)e^{iλ(x+iH)}dx`. -/
def J1D (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..Work.CKFinal.hsplit,
    Dfun K G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) - 1)
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- `J₂(D) = ∫_{-1}^0 D(τ,(x+1)+iH)e^{iλ(x+iH)}dx`. -/
def J2D (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..0,
    Dfun K G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) + 1)
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- `J₁(𝒢) = ∫_0^1 𝒢(τ,(x-1)+iH)e^{iλ(x+iH)}dx`: the model part of the first edge integral. -/
def J1model (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..Work.CKFinal.hsplit,
    Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) - 1)
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- `J₂(𝒢) = ∫_{-1}^0 𝒢(τ,(x+1)+iH)e^{iλ(x+iH)}dx`: the model part of the second edge integral. -/
def J2model (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..0,
    Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) + 1)
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
          * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))

/-- The shifted contour integrand `f₁(z) = D(τ,z-1)e^{iλz}` of the right rectangle. -/
def f1D (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ → ℂ :=
  fun z => Dfun K G τ (z - 1) * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * z)

/-- The shifted contour integrand `f₂(z) = D(τ,z+1)e^{iλz}` of the left rectangle. -/
def f2D (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ → ℂ :=
  fun z => Dfun K G τ (z + 1) * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * z)

/-! ## Elementary pointwise identities for the cusp model -/

/-- On `ℍ`, the model `Gmodel` is `AexpZ`. -/
lemma Gmodel_eq_AexpZ (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ z : ℍ) :
    Work.CKFinal.Gmodel G τ (z : ℂ) = Work.Asymptotics.AexpZ G τ z := by
  rw [Work.Asymptotics.AexpZ, Work.CKFinal.Gmodel]
  simp only [Work.Asymptotics.mq, Work.Kernels.qParamFun]
  rw [Complex.exp_neg]

/-- `𝒢_G(τ, i t) = Aexp G τ t`. -/
lemma Gmodel_mul_I (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    Work.CKFinal.Gmodel G τ ((t : ℂ) * Complex.I) = Work.Asymptotics.Aexp G τ t := by
  have hAz : Work.CKFinal.Gmodel G τ ((t : ℂ) * Complex.I)
      = Work.Asymptotics.AexpZ G τ (Work.Kernels.imagAxis t ht) := by
    show Work.CKFinal.Gmodel G τ (((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
      = Work.Asymptotics.AexpZ G τ (Work.Kernels.imagAxis t ht)
    rw [Work.Asymptotics.AexpZ, Work.CKFinal.Gmodel]
    simp only [Work.Asymptotics.mq, Work.Kernels.qParamFun]
    rw [Complex.exp_neg]
  rw [hAz]
  exact Work.Asymptotics.AexpZ_imagAxis G τ t ht

/-- The second difference `z ↦ 2f(z) - f(z-1) - f(z+1)` kills the cusp model. -/
lemma Gmodel_secondDiff (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (z : ℂ) :
    2 * Work.CKFinal.Gmodel G τ z - Work.CKFinal.Gmodel G τ (z - 1)
      - Work.CKFinal.Gmodel G τ (z + 1) = 0 := by
  simp only [Work.CKFinal.Gmodel]
  have h1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (z - 1)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * z)) := by
    have : -(2 * (Real.pi : ℂ) * Complex.I * (z - 1))
        = -(2 * (Real.pi : ℂ) * Complex.I * z) + 2 * (Real.pi : ℂ) * Complex.I := by ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (z + 1)))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * z)) := by
    have : -(2 * (Real.pi : ℂ) * Complex.I * (z + 1))
        = -(2 * (Real.pi : ℂ) * Complex.I * z) - 2 * (Real.pi : ℂ) * Complex.I := by ring
    rw [this, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [h1, h2]
  ring

/-- `Kax K τ j t = D(τ, i t + j) + 𝒢_G(τ, i t + j)` for `0 < t`. -/
lemma Kax_eq_Dfun_add (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (j t : ℝ)
    (ht : 0 < t) :
    Work.CKFinal.Kax K τ j t
      = Dfun K G τ ((j : ℂ) + (t : ℂ) * Complex.I)
        + Work.CKFinal.Gmodel G τ ((j : ℂ) + (t : ℂ) * Complex.I) := by
  rw [Kax_eq_K_ofComplex K τ j t ht, Dfun]
  ring

/-- The second difference `Phi` of `K` is the second difference of the *model-subtracted*
kernel `D` (the model is annihilated). -/
lemma Phi_eq_Dfun (K : ℍ → ℍ → ℂ) (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (t : ℝ) (ht : 0 < t) :
    Work.CKFinal.Phi K τ t
      = 2 * Dfun K G τ ((t : ℂ) * Complex.I) - Dfun K G τ ((t : ℂ) * Complex.I - 1)
        - Dfun K G τ ((t : ℂ) * Complex.I + 1) := by
  rw [Work.CKFinal.Phi]
  rw [Kax_eq_Dfun_add K G τ 0 t ht, Kax_eq_Dfun_add K G τ (-1) t ht,
    Kax_eq_Dfun_add K G τ 1 t ht]
  have e1 : ((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I := by push_cast; ring
  have e2 : ((-1 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I - 1 := by push_cast; ring
  have e3 : ((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I + 1 := by push_cast; ring
  rw [e1, e2, e3]
  have h := Gmodel_secondDiff G τ ((t : ℂ) * Complex.I)
  linear_combination h



/-! ## The cusp expansion of the kernel on a strip (the decay of the model-subtracted kernel) -/

/-- **The strip form of the cusp expansion of `K^{(d)}(τ,·)`.**  For fixed `τ ∈ ℍ` and
`d ∈ {8,24}`, the deviation of the kernel `K^{(d)}(τ,z)` from its cusp model
`AexpZ (Gcusp ℓ d) τ z` is `O((1+|Re z|+Im z)^M e^{-π Im z})` uniformly in the half-plane
`Im z ≥ T`.  This is `kernelKfun_cuspExp` combined with `cuspModel_bound`. -/
theorem strip_dev_cusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    ∃ C M T : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < T ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
      ‖Work.Kernels.Kfun ℓ d τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) τ z‖
        ≤ C * (Work.Asymptotics.cuspW z) ^ M * ‖Work.Residues.Ept z‖ := by
  have hcpt : IsCompact ({τ} : Set UpperHalfPlane) := isCompact_singleton
  obtain ⟨T, hT, C, hC, hb⟩ := Work.Asymptotics.CuspExp.kernelKfun_cuspExp ℓ (K := {τ}) hcpt
  obtain ⟨C', M', hC', hM', hb'⟩ :=
    Work.Asymptotics.CuspExp.cuspModel_bound ℓ d hd (K := {τ}) hcpt
  refine ⟨C + C', max 3 M', T, by positivity, by positivity, hT, fun z hz => ?_⟩
  have h1 := hb τ (Set.mem_singleton τ) z hz
  have h2 := hb' τ (Set.mem_singleton τ) z
  have hstep : ∀ (D : ℂ), ‖D‖ ≤ C * Work.Asymptotics.cuspG z 3 1
        + C' * (Work.Asymptotics.cuspW z) ^ M' * ‖Work.Residues.Ept z‖ →
      ‖D‖ ≤ (C + C') * (Work.Asymptotics.cuspW z) ^ (max 3 M') * ‖Work.Residues.Ept z‖ := by
    intro D hD
    rw [Work.Asymptotics.cuspG, zpow_one, Real.rpow_ofNat] at hD
    have hW1 : (1 : ℝ) ≤ Work.Asymptotics.cuspW z := Work.Asymptotics.cuspW_one_le z
    have hE : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
    have h3 : Work.Asymptotics.cuspW z ^ 3 ≤ Work.Asymptotics.cuspW z ^ (max 3 M') := by
      rw [← Real.rpow_natCast (Work.Asymptotics.cuspW z) 3]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (le_max_left 3 M')
    have hM : Work.Asymptotics.cuspW z ^ M' ≤ Work.Asymptotics.cuspW z ^ (max 3 M') :=
      Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right 3 M')
    have hA : C * (Work.Asymptotics.cuspW z ^ 3 * ‖Work.Residues.Ept z‖)
        + C' * Work.Asymptotics.cuspW z ^ M' * ‖Work.Residues.Ept z‖
        ≤ (C + C') * Work.Asymptotics.cuspW z ^ (max 3 M') * ‖Work.Residues.Ept z‖ := by
      have h1 : C * (Work.Asymptotics.cuspW z ^ 3 * ‖Work.Residues.Ept z‖)
          ≤ C * (Work.Asymptotics.cuspW z ^ (max 3 M') * ‖Work.Residues.Ept z‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hE) hC.le
      have h2 : C' * Work.Asymptotics.cuspW z ^ M' * ‖Work.Residues.Ept z‖
          ≤ C' * (Work.Asymptotics.cuspW z ^ (max 3 M') * ‖Work.Residues.Ept z‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hE) hC'.le
      linarith [h1, h2]
    linarith [hD, hA]
  rcases hd with h8 | h24
  · subst h8
    refine hstep _ ?_
    calc ‖Work.Kernels.Kfun ℓ 8 τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 8) τ z‖
        = ‖(Work.Kernels.Kfun ℓ 8 τ z - Work.Asymptotics.MK ℓ 8 τ z)
            + (Work.Asymptotics.MK ℓ 8 τ z
                - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 8) τ z)‖ := by ring_nf
      _ ≤ C * Work.Asymptotics.cuspG z 3 1
            + C' * (Work.Asymptotics.cuspW z) ^ M' * ‖Work.Residues.Ept z‖ :=
          le_trans (norm_add_le _ _) (add_le_add h1.1 h2)
  · subst h24
    refine hstep _ ?_
    calc ‖Work.Kernels.Kfun ℓ 24 τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 24) τ z‖
        = ‖(Work.Kernels.Kfun ℓ 24 τ z - Work.Asymptotics.MK ℓ 24 τ z)
            + (Work.Asymptotics.MK ℓ 24 τ z
                - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 24) τ z)‖ := by ring_nf
      _ ≤ C * Work.Asymptotics.cuspG z 3 1
            + C' * (Work.Asymptotics.cuspW z) ^ M' * ‖Work.Residues.Ept z‖ :=
          le_trans (norm_add_le _ _) (add_le_add h1.2 h2)


/-! ## The `S`-transport of `K̂` and the strip expansion of the hatted kernel -/

/-- `K̂(τ,z) = -τ^{-d/2}K(S•τ, z)` pointwise (the `S`-transport in the first variable). -/
theorem Khat_eq_neg_slash_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ τ z : ℍ, Work.Kernels.Khat ℓ d τ z
      = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z := by
  intro τ z
  have h := congr_fun (Work.Kernels.Khat_eq_neg_slash ℓ d hd z) τ
  rw [h, Work.Kernels.slash_apply']
  have hj : Work.Kernels.jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [Work.Kernels.jFun_apply]
    simp
  rw [hj]
  ring

/-- `AexpZ (Ĝ) τ z = -τ^{-d/2} AexpZ (𝒢) (S•τ) z` (the same `S`-law at the level of the models,
which follows from the definition of `Ĝ = Ghat`). -/
theorem AexpZ_Ghat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ z : ℍ) :
    Work.Asymptotics.AexpZ (Work.CKFinal.Ghat ℓ d) τ z
      = - (τ : ℂ) ^ (-((d : ℤ) / 2))
          * Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • τ) z := by
  simp only [Work.Asymptotics.AexpZ, Work.CKFinal.Ghat]
  ring

/-- **The strip form of the cusp expansion of `K̂^{(d)}(τ,·)`.**  For fixed `τ ∈ ℍ` and
`d ∈ {8,24}`, the deviation of `K̂^{(d)}(τ,z)` from its cusp model `AexpZ (Ĝ) τ z` is
`O((1+|Re z|+Im z)^M e^{-π Im z})` uniformly in the half-plane `Im z ≥ T`.  This is
`strip_dev_cusp` transported by `K̂(τ,z) = -τ^{-d/2}K(S•τ,z)`. -/
theorem strip_dev_ghat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    ∃ C M T : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < T ∧ ∀ z : UpperHalfPlane, T ≤ z.im →
      ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Work.CKFinal.Ghat ℓ d) τ z‖
        ≤ C * (Work.Asymptotics.cuspW z) ^ M * ‖Work.Residues.Ept z‖ := by
  obtain ⟨C, M, T, hC, hM, hT, hb⟩ := strip_dev_cusp ℓ d hd (ModularGroup.S • τ)
  refine ⟨C * ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖, M, T,
    mul_pos hC (norm_pos_iff.mpr (zpow_ne_zero _ (UpperHalfPlane.ne_zero τ))), hM, hT,
    fun z hz => ?_⟩
  have hb' := hb z hz
  have key : ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Work.CKFinal.Ghat ℓ d) τ z‖
      = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖
        * ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
            - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • τ) z‖ := by
    rw [Khat_eq_neg_slash_pointwise ℓ d hd τ z, AexpZ_Ghat ℓ d τ z,
      show - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
          - - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d)
              (ModularGroup.S • τ) z
        = - (τ : ℂ) ^ (-((d : ℤ) / 2))
            * (Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
                - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • τ) z)
        from by ring]
    rw [norm_mul, norm_neg]
  calc ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Work.CKFinal.Ghat ℓ d) τ z‖
      = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖
        * ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
            - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) (ModularGroup.S • τ) z‖ := key
    _ ≤ ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖
        * (C * (Work.Asymptotics.cuspW z) ^ M * ‖Work.Residues.Ept z‖) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg ((τ : ℂ) ^ (-((d : ℤ) / 2))))
    _ = C * ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ * (Work.Asymptotics.cuspW z) ^ M
          * ‖Work.Residues.Ept z‖ := by ring

end Work.CKFinal.LineDecay
