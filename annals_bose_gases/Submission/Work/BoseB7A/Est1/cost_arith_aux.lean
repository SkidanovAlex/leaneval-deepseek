import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Est1.estR1_defs
import Submission.Work.BoseB7A.errA_pre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.cost_arith_aux` — the scalar arithmetic of `costTa`, `costB2`, `costB3`

The error brackets of the `R1` estimate are dominated by `e1A`:

`costTa + costB2 + costB3 ≤ C·e1A`,

with `C` an absolute constant times `K₀`-powers.  Everything rests on the *exact*
identity (with `t = μa³`, `ℓ = K_ℓ(μa)^{-1/2}`, `𝓁 = μa³K_H²`, `z² = ρ_zℓ³`)

`μ³·(ℓ²K_ℓ³K_L⁵z²𝓁⁴K_H²tρ_z²a²) = ρ_z³·(μ²aℓ³)·K_ℓ⁵K_L⁵𝓁⁵`,

i.e. `ℓ²K_ℓ³K_L⁵z²𝓁⁴K_H²tρ²a² = (ρ_z/μ)³·E₀·K_ℓ⁵K_L⁵𝓁⁵`: the `θ`-word therefore
costs `800·1024²(1+K₀²)²K₀⁷(ρ_z/μ)³ ≤ 800·1024²(1+K₀²)²K₀⁷(3/2)³` times the
`E₀K_ℓ⁵K_L⁵𝓁⁵/b` summand of `e1A`; and the squeezed words, whose brackets are
`∝ 𝓁⁴η²ρ_z a·(K_ℓK_L)⁶`, are dominated by the `E₀(μa³)^{1/2}K_ℓ³K_L⁶η²` summand
of `e1A` (via `K_ℓ³𝓁⁴ρ_z ≤ (3/2)μK_ℓ³`, which is `ρ_z ≤ (3/2)μ` and `𝓁⁴ ≤ 1`).
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-! ## 1. Nonnegativity of the elementary factors -/

theorem lille_nn (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ E.lille := by
  rw [lille_val E hv]
  exact fsXp_nonneg hv.t_pos.le

theorem eta_nn (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ eta E := by
  rw [errA_eta E hv]
  exact fsXp_nonneg hv.t_pos.le

theorem lille4_le_one (E : Q3Env Mode) (hv : FSParamsView E) : E.lille ^ 4 ≤ 1 := by
  calc E.lille ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ (lille_nn E hv) (lille_le_one E hv) 4
    _ = 1 := by norm_num

theorem Kl_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ E.Kl := by linarith [hv.one_le_Kl]

theorem KL_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ E.KL := by linarith [hv.one_le_KL]

/-! ## 2. The identity -/

/-- **The identity behind the `θ`-word arithmetic** (in cleared form, without the
`ρ_z/μ` division). -/
theorem arith_identity (E : Q3Env Mode) (hv : FSParamsView E) :
    E.mu ^ 3 * (E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.z ^ 2 * E.lille ^ 4
        * E.KH ^ 2 * hv.t * E.rho ^ 2 * E.aScat ^ 2)
      = E.rho ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3) * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5 := by
  have hmu : 0 < E.mu := mu_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  have hmua : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hℓ2 : E.ell ^ 2 * (E.mu * E.aScat) = E.Kl ^ 2 := by
    rw [hv.ell_eq, Work.BoseB7.side]
    have hsq : ((E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) ^ 2 = (E.mu * E.aScat)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmua.le]
      norm_num
      rw [Real.rpow_neg_one, mul_inv, mul_comm]
    rw [mul_pow, hsq, mul_assoc, inv_mul_cancel₀ (ne_of_gt hmua), mul_one]
  have h𝓁 : E.lille = hv.t * E.KH ^ 2 := by
    rw [Q3Env.lille, Work.BoseB7.lille, ← hv.mu_eq]
  have hz : E.z ^ 2 = E.rho * E.ell ^ 3 := zsq_eq E hv
  rw [hz, h𝓁]
  linear_combination
    (E.rho ^ 3 * E.KL ^ 5 * hv.t ^ 5 * E.KH ^ 10 * E.mu ^ 2 * E.aScat * E.ell ^ 3
      * E.Kl ^ 3) * hℓ2

/-- The identity in the form used by the `θ`-word comparison:
`ℓ²K_ℓ³K_L⁵z²𝓁⁴K_H²tρ²a² = (ρ_z/μ)³·μ²aℓ³K_ℓ⁵K_L⁵𝓁⁵`. -/
theorem arith_identity' (E : Q3Env Mode) (hv : FSParamsView E) :
    E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.z ^ 2 * E.lille ^ 4 * E.KH ^ 2 * hv.t
        * E.rho ^ 2 * E.aScat ^ 2
      = (E.rho / E.mu) ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
          * E.lille ^ 5) := by
  have hmu0 : E.mu ≠ 0 := ne_of_gt (mu_pos E hv)
  have h := arith_identity E hv
  refine mul_left_cancel₀ (pow_ne_zero 3 hmu0) ?_
  rw [h, div_pow]
  field_simp

/-! ## 3. `e1A` dominates its two summands -/

/-- `e1A ≥ 0` (`b > 0`). -/
theorem e1A_nn (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) : 0 ≤ e1A E := by
  have hKl := Kl_nonneg E hv
  have hKL := KL_nonneg E hv
  have h𝓁 := lille_nn E hv
  have hη := eta_nn E hv
  have hb0 : 0 ≤ E.b := hb.le
  have hd1 := dil_nonneg E hv (1 / 2)
  have hd4 := dil_nonneg E hv (1 / 4)
  have hE0 : 0 ≤ E0 E := (errA_E0_pos E hv).le
  have h1 : 0 ≤ dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hd1 (pow_nonneg hKl 3)) (pow_nonneg hKL 6))
      (sq_nonneg _)
  have h2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 :=
    mul_nonneg (mul_nonneg hd1 (pow_nonneg hKL 3)) (pow_nonneg h𝓁 2)
  have h3 : 0 ≤ E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b :=
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hKl 5) (pow_nonneg hKL 5))
      (pow_nonneg h𝓁 5)) hb0
  have h4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKl _)
      (pow_nonneg hKL 3)) hd4) (pow_nonneg h𝓁 2)) hη
  rw [e1A]
  exact mul_nonneg hE0 (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4)

/-- `e1A` dominates its `E₀K_ℓ⁵K_L⁵𝓁⁵/b` summand. -/
theorem e1A_ge_K (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b ≤ e1A E := by
  have hKl := Kl_nonneg E hv
  have hKL := KL_nonneg E hv
  have h𝓁 := lille_nn E hv
  have hη := eta_nn E hv
  have hb0 : 0 ≤ E.b := hb.le
  have hd1 := dil_nonneg E hv (1 / 2)
  have hd4 := dil_nonneg E hv (1 / 4)
  have hE0 : 0 ≤ E0 E := (errA_E0_pos E hv).le
  have h1 : 0 ≤ dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hd1 (pow_nonneg hKl 3)) (pow_nonneg hKL 6))
      (sq_nonneg _)
  have h2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 :=
    mul_nonneg (mul_nonneg hd1 (pow_nonneg hKL 3)) (pow_nonneg h𝓁 2)
  have h4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKl _)
      (pow_nonneg hKL 3)) hd4) (pow_nonneg h𝓁 2)) hη
  have hshape : E0 E * (E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b)
      = E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b := by ring
  rw [← hshape, e1A]
  refine mul_le_mul_of_nonneg_left ?_ hE0
  have hle : E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b
      ≤ dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2
        + dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2
        + E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b
        + E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E := by
    linarith
  exact le_trans (le_refl _) hle

/-- `e1A` dominates its `E₀(μa³)^{1/2}K_ℓ³K_L⁶η²` summand. -/
theorem e1A_ge_eta (E : Q3Env Mode) (hv : FSParamsView E) (hb : 0 < E.b) :
    E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 ≤ e1A E := by
  have hKl := Kl_nonneg E hv
  have hKL := KL_nonneg E hv
  have h𝓁 := lille_nn E hv
  have hη := eta_nn E hv
  have hb0 : 0 ≤ E.b := hb.le
  have hd1 := dil_nonneg E hv (1 / 2)
  have hd4 := dil_nonneg E hv (1 / 4)
  have hE0 : 0 ≤ E0 E := (errA_E0_pos E hv).le
  have h2 : 0 ≤ dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 :=
    mul_nonneg (mul_nonneg hd1 (pow_nonneg hKL 3)) (pow_nonneg h𝓁 2)
  have h3 : 0 ≤ E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b :=
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hKl 5) (pow_nonneg hKL 5))
      (pow_nonneg h𝓁 5)) hb0
  have h4 : 0 ≤ E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hKl _)
      (pow_nonneg hKL 3)) hd4) (pow_nonneg h𝓁 2)) hη
  have hshape : E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2)
      = E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2 := by ring
  rw [← hshape, e1A]
  refine mul_le_mul_of_nonneg_left ?_ hE0
  have hle : dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2
      ≤ dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * (eta E) ^ 2
        + dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2
        + E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b
        + E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E := by
    linarith
  exact le_trans (le_refl _) hle

/-! ## 4. The two cost comparisons -/

/-- `(ρ_z/μ)³ ≤ 27/8`. -/
theorem rho_div_cube_le (E : Q3Env Mode) (hv : FSParamsView E) :
    (E.rho / E.mu) ^ 3 ≤ 27 / 8 := by
  have hμ : 0 < E.mu := mu_pos E hv
  have hρ : E.rho ≤ 3 * E.mu / 2 := rho_le E hv
  have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < E.mu ^ 3)]
  calc E.rho ^ 3 ≤ (3 * E.mu / 2) ^ 3 := pow_le_pow_left₀ hρ0 hρ 3
    _ = 27 / 8 * E.mu ^ 3 := by ring

/-- **The `θ`-word bracket is dominated by `e1A`.** -/
theorem costTa_le_e1A (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (E : Q3Env Mode) (hv : FSParamsView E)
    (hb : b₀ ≤ E.b) (hK₀ : 0 ≤ K₀) :
    costTa K₀ E hv ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) * e1A E := by
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hb0 : 0 ≤ E.b := hbpos.le
  have hKl := Kl_nonneg E hv
  have hKL := KL_nonneg E hv
  have h𝓁 := lille_nn E hv
  have hel : 0 ≤ E.ell := (ell_pos E hv).le
  have hMc : (Mc K₀ E hv) ^ 2 = (1 + K₀ ^ 2) ^ 2 * 1024 ^ 2 * E.z ^ 2 * K₀ ^ 6
      * E.lille ^ 4 * E.KH ^ 2 * E.KL ^ 2 * hv.t * E.rho ^ 2 * E.aScat ^ 2 := by
    have h1 : (Mc K₀ E hv) ^ 2 = (1 + K₀ ^ 2) ^ 2 * 1024 ^ 2 * |E.z| ^ 2 * K₀ ^ 6
        * E.lille ^ 4 * E.KH ^ 2 * E.KL ^ 2 * (Real.sqrt hv.t) ^ 2 * E.rho ^ 2
        * E.aScat ^ 2 := by
      unfold Mc
      ring
    rw [h1, sq_abs, Real.sq_sqrt hv.t_pos.le]
  have hident := arith_identity' E hv
  have hρ3 := rho_div_cube_le E hv
  have hQ : 0 ≤ E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 := by
    have := (mu_pos E hv).le
    have := hv.a_pos.le
    positivity
  have hC : 0 ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 := by
    have h1 : 0 ≤ (1 + K₀ ^ 2) ^ 2 := by positivity
    have h2 : 0 ≤ K₀ ^ 7 := pow_nonneg hK₀ 7
    positivity
  have h1 : costTa K₀ E hv * E.b
      = 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
        * (E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.z ^ 2 * E.lille ^ 4 * E.KH ^ 2 * hv.t
            * E.rho ^ 2 * E.aScat ^ 2) := by
    rw [costTa, hMc]
    field_simp
  have h2 : E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.z ^ 2 * E.lille ^ 4 * E.KH ^ 2 * hv.t
        * E.rho ^ 2 * E.aScat ^ 2
      = (E.rho / E.mu) ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
          * E.lille ^ 5) := hident
  have h3 : (E.rho / E.mu) ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5) ≤ (27 / 8) * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
        * E.lille ^ 5) :=
    mul_le_mul_of_nonneg_right hρ3 hQ
  have h4 : (27 / 8) * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5)
      = (27 / 8) * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5) := by
    rw [E0]
  have h5 : (27 / 8) * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5)
      ≤ (27 / 8) * (e1A E * E.b) := by
    have h := e1A_ge_K E hv hbpos
    have h27 : 0 < (27 / 8 : ℝ) := by norm_num
    have hkey : E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 ≤ e1A E * E.b := by
      have := mul_le_mul_of_nonneg_right h hb0
      rw [div_mul_cancel₀ _ (ne_of_gt hbpos)] at this
      exact this
    exact mul_le_mul_of_nonneg_left hkey h27.le
  have h6 : costTa K₀ E hv * E.b
      ≤ (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) * e1A E) * E.b :=
    calc costTa K₀ E hv * E.b
        = 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
          * (E.ell ^ 2 * E.Kl ^ 3 * E.KL ^ 5 * E.z ^ 2 * E.lille ^ 4 * E.KH ^ 2 * hv.t
              * E.rho ^ 2 * E.aScat ^ 2) := h1
      _ = 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
          * ((E.rho / E.mu) ^ 3 * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
              * E.lille ^ 5)) := by rw [h2]
      _ ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
          * ((27 / 8) * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * E.Kl ^ 5 * E.KL ^ 5
              * E.lille ^ 5)) := mul_le_mul_of_nonneg_left h3 hC
      _ = 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
          * ((27 / 8) * (E0 E * E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5)) := by rw [h4]
      _ ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7
          * ((27 / 8) * (e1A E * E.b)) := mul_le_mul_of_nonneg_left h5 hC
      _ = (800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) * e1A E) * E.b := by ring
  exact le_of_mul_le_mul_right h6 hbpos

/-- **The two squeezed-word brackets are dominated by `e1A`.** -/
theorem costB_le_e1A (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (E : Q3Env Mode) (hv : FSParamsView E)
    (hb : b₀ ≤ E.b) (hK₀ : 0 ≤ K₀) :
    costB2 K₀ E + costB3 K₀ E ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * e1A E := by
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hKl := Kl_nonneg E hv
  have hKL := KL_nonneg E hv
  have h𝓁 := lille_nn E hv
  have hη := eta_nn E hv
  have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
  have ha0 : 0 ≤ E.aScat := hv.a_pos.le
  have hsum : costB2 K₀ E + costB3 K₀ E
      = 2560 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho * E.aScat := by
    rw [costB2, costB3]; ring
  -- the scalar core: `K_ℓ³𝓁⁴ρ_z ≤ (3/2)μ²ℓ³·dil(1/2)`
  have hcore : E.Kl ^ 3 * E.lille ^ 4 * E.rho
      ≤ (3 / 2) * E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2) := by
    have hX : E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2) = E.mu * E.Kl ^ 3 := by
      have h1 : E.mu ^ 2 * E.ell ^ 3 = E.mu * (E.mu * E.ell ^ 3) := by ring
      rw [h1, errA_mue E hv, errA_dil E hv (1 / 2), errA_Kl E hv,
        show (fsXp hv.t (-(3 / 2))) ^ 3 = fsXp hv.t (-(3 / 2) * 3) from
          fsXp_pow hv.t_pos.le _ 3,
        mul_assoc, fsXp_mul hv.t_pos]
      congr 1
      norm_num
    rw [show (3 : ℝ) / 2 * E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)
        = (3 / 2) * (E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) by ring, hX]
    have hρ : E.rho ≤ 3 * E.mu / 2 := rho_le E hv
    have h𝓁4 := lille4_le_one E hv
    have hK3 : 0 ≤ E.Kl ^ 3 := pow_nonneg hKl 3
    have hμ0 : 0 ≤ E.mu := (mu_pos E hv).le
    have h4nn : 0 ≤ E.lille ^ 4 := pow_nonneg h𝓁 4
    have step1 : E.lille ^ 4 * E.rho ≤ 3 * E.mu / 2 := by
      calc E.lille ^ 4 * E.rho ≤ E.lille ^ 4 * (3 * E.mu / 2) :=
            mul_le_mul_of_nonneg_left hρ h4nn
        _ ≤ 1 * (3 * E.mu / 2) := mul_le_mul_of_nonneg_right h𝓁4 (by linarith)
        _ = 3 * E.mu / 2 := by ring
    calc E.Kl ^ 3 * E.lille ^ 4 * E.rho = E.Kl ^ 3 * (E.lille ^ 4 * E.rho) := by ring
      _ ≤ E.Kl ^ 3 * (3 * E.mu / 2) := mul_le_mul_of_nonneg_left step1 hK3
      _ = 3 / 2 * (E.mu * E.Kl ^ 3) := by ring
  have hmult : 0 ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (eta E) ^ 2 * E.KL ^ 6 * E.aScat * E.Kl ^ 3 := by
    have h1 : 0 ≤ K₀ ^ 11 := pow_nonneg hK₀ 11
    have h2 : 0 ≤ (eta E) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ 2560 * 64 ^ 6 * K₀ ^ 11 := by positivity
    positivity
  have hgoal : 2560 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho * E.aScat
      ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6
          * (eta E) ^ 2) := by
    have hstep := mul_le_mul_of_nonneg_left hcore hmult
    calc 2560 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
          * E.rho * E.aScat
        = 2560 * 64 ^ 6 * K₀ ^ 11 * (eta E) ^ 2 * E.KL ^ 6 * E.aScat * E.Kl ^ 3
          * (E.Kl ^ 3 * E.lille ^ 4 * E.rho) := by ring
      _ ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (eta E) ^ 2 * E.KL ^ 6 * E.aScat * E.Kl ^ 3
          * ((3 / 2) * E.mu ^ 2 * E.ell ^ 3 * dil E (1 / 2)) := hstep
      _ = 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6
          * (eta E) ^ 2) := by
        rw [E0]; ring
  calc costB2 K₀ E + costB3 K₀ E
      = 2560 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho * E.aScat := hsum
    _ ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * (E0 E * dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6
          * (eta E) ^ 2) := hgoal
    _ ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) * e1A E := by
        refine mul_le_mul_of_nonneg_left (e1A_ge_eta E hv hbpos) ?_
        have h1 : 0 ≤ K₀ ^ 11 := pow_nonneg hK₀ 11
        positivity

/-! ## 5. The arithmetic statement -/

/-- **The `cost_arith` statement.** -/
theorem cost_arith_aux (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
        (E : Q3Env Mode) (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b →
        costTa K₀ E hv + costB2 K₀ E + costB3 K₀ E ≤ C * e1A E := by
  by_cases hK : 0 ≤ K₀
  · refine ⟨800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8)
      + 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2), 1, ?_, one_pos, ?_⟩
    · have h1 : 0 ≤ K₀ ^ 7 := pow_nonneg hK 7
      have h2 : 0 ≤ K₀ ^ 11 := pow_nonneg hK 11
      have h3 : 0 ≤ (1 + K₀ ^ 2) ^ 2 := by positivity
      positivity
    · intro Mode _ _ E hv _ hb
      have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
      have h1 := costTa_le_e1A K₀ b₀ hb₀ E hv hb hK
      have h2 := costB_le_e1A K₀ b₀ hb₀ E hv hb hK
      have h3 := e1A_nn E hv hbpos
      have h4 : 0 ≤ 800 * 1024 ^ 2 * (1 + K₀ ^ 2) ^ 2 * K₀ ^ 7 * (27 / 8) := by
        have h1 : 0 ≤ K₀ ^ 7 := pow_nonneg hK 7
        have h3 : 0 ≤ (1 + K₀ ^ 2) ^ 2 := by positivity
        positivity
      have h5 : 0 ≤ 2560 * 64 ^ 6 * K₀ ^ 11 * (3 / 2) := by
        have h2 : 0 ≤ K₀ ^ 11 := pow_nonneg hK 11
        positivity
      nlinarith [h1, h2, h3, h4, h5]
  · push_neg at hK
    refine ⟨1, 1, by norm_num, one_pos, ?_⟩
    intro Mode _ _ E hv _ hb
    have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
    have h3 := e1A_nn E hv hbpos
    have hKl := Kl_nonneg E hv
    have hKL := KL_nonneg E hv
    have h𝓁 := lille_nn E hv
    have hη := eta_nn E hv
    have hρ0 : 0 ≤ E.rho := (rho_pos E hv).le
    have ha0 : 0 ≤ E.aScat := hv.a_pos.le
    have hTa : costTa K₀ E hv ≤ 0 := by
      have hnn : 0 ≤ 800 / E.b * E.ell ^ 2 * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2 := by
        have h1 : 0 ≤ 800 / E.b := div_nonneg (by norm_num) hbpos.le
        have h2 : 0 ≤ (E.Kl * E.KL) ^ 3 :=
          pow_nonneg (mul_nonneg hKl hKL) 3
        have h4 : 0 ≤ E.ell ^ 2 := pow_nonneg (ell_pos E hv).le 2
        have h5 : 0 ≤ (Mc K₀ E hv) ^ 2 := sq_nonneg _
        positivity
      have hEq : costTa K₀ E hv
          = K₀ * (800 / E.b * E.ell ^ 2 * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2) := by
        rw [costTa]; ring
      rw [hEq]
      exact mul_nonpos_of_nonpos_of_nonneg hK.le hnn
    have hB2 : costB2 K₀ E ≤ 0 := by
      have hnn : 0 ≤ 512 * 64 ^ 6 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
          * E.rho * E.aScat :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (pow_nonneg (mul_nonneg hKl hKL) 6)) (pow_nonneg h𝓁 4)) (sq_nonneg _))
          hρ0) ha0
      have hEq : costB2 K₀ E
          = K₀ ^ 11 * (512 * 64 ^ 6 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
              * E.rho * E.aScat) := by
        rw [costB2]; ring
      rw [hEq]
      have hK11 : K₀ ^ 11 ≤ 0 := by
        have h10 : 0 ≤ K₀ ^ 10 := by
          have hsq : K₀ ^ 10 = (K₀ ^ 5) ^ 2 := by ring
          rw [hsq]; exact sq_nonneg _
        have : K₀ ^ 11 = K₀ ^ 10 * K₀ := by ring
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos h10 hK.le
      exact mul_nonpos_of_nonpos_of_nonneg hK11 hnn
    have hB3 : costB3 K₀ E ≤ 0 := by
      have hnn : 0 ≤ 2048 * 64 ^ 6 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
          * E.rho * E.aScat :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (pow_nonneg (mul_nonneg hKl hKL) 6)) (pow_nonneg h𝓁 4)) (sq_nonneg _))
          hρ0) ha0
      have hEq : costB3 K₀ E
          = K₀ ^ 11 * (2048 * 64 ^ 6 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
              * E.rho * E.aScat) := by
        rw [costB3]; ring
      rw [hEq]
      have hK11 : K₀ ^ 11 ≤ 0 := by
        have h10 : 0 ≤ K₀ ^ 10 := by
          have hsq : K₀ ^ 10 = (K₀ ^ 5) ^ 2 := by ring
          rw [hsq]; exact sq_nonneg _
        have : K₀ ^ 11 = K₀ ^ 10 * K₀ := by ring
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos h10 hK.le
      exact mul_nonpos_of_nonpos_of_nonneg hK11 hnn
    nlinarith [hTa, hB2, hB3, h3]

end Est1

end Work.BoseB7A
