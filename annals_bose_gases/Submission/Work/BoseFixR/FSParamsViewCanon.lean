import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Work.BoseFixR.Canon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FSParamsViewCanon` — the canonical environment is FS's parameter point

`Work.BoseFixR.KzEnvFs v h μ F fc` (`Submission/Work/BoseFixR/Canon.lean`) is the
canonical FS §8/§10 environment: FS's scalars at the diluteness `μa³`, the box side
`ℓ = K_ℓ(μa)^{-1/2} = sideAt μ (a v)`, the window `𝓜 = bigM (paramsAt μ (a v)) (a v) μ`,
the `c`-number `z = √(μℓ³)` (so that `ρ_z = μ`, FS `eq:Close` *with equality*), `δ = 1`
and FS §4's kernels.

The view conjunct of the residual `R-B4box` requires
`Nonempty (Work.BoseB7.FSParamsView (KzEnvFs v h μ F fc))`: the environment really is
FS's parameter point.  This module proves exactly that, i.e. that the residual is not
vacuous.

Every numeric field of `KzEnvFs` is one of FS's monomials `fsXp t c = t^{c/323}` at
`t = μa³`, hence the `FSParamsView` fields are

* the definitional identities (`mu * aScat³ = t`, `Kl = X^{-3/2}`,
  `KH = K̃_H(μa³)^{-5/12}`, `KL = (K_ℓd²)^{-1}`, `ℓ = K_ℓ(μa)^{-1/2}`,
  `𝓜 = K_M(μa³)^{-1/4}`, `M = mValue`, `δ = 1`),
* the four closed forms `K_L = X^{-21/2}`, `K_H = X^{-549/4}`, `𝓜 = X^{-327/4}`,
  `𝓁 = (μa³)K_H² = X^{97/2}` (exponent arithmetic in the `fsXp`-calculus),
* `ρ_z = z²/ℓ³ = μ` (`eq:Close` with equality), and
* FS's `sec:params` block, which is `Work.BoseB7.paramsOK_fsParams_le_one`.

The one-sided bounds `1 ≤ K_ℓ, K_L, K_H, 𝓜` and `𝓁 ≤ δ = 1` are then the single
antitonicity statement `fsXp_le_fsXp` for `0 < t ≤ 1`.
-/

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseB7

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false

section Aux

variable {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
variable {F : Work.BoseB7.FockData.{0, 0} Mode} {fc : Work.BoseBoxFix.LowCut}

/-! ## 1. The definitional fields of `KzEnvFs` -/

lemma KzEnvFs_mu : (KzEnvFs v h μ F fc).mu = μ := rfl

lemma KzEnvFs_aScat : (KzEnvFs v h μ F fc).aScat = BoseGases.a v := rfl

/-- `(μa³)` of the canonical environment. -/
lemma KzEnvFs_mu_aScat_cube :
    (KzEnvFs v h μ F fc).mu * (KzEnvFs v h μ F fc).aScat ^ 3
      = μ * BoseGases.a v ^ 3 := rfl

lemma KzEnvFs_Kl_val :
    (KzEnvFs v h μ F fc).Kl = fsXp (μ * BoseGases.a v ^ 3) (-(3 / 2 : ℝ)) := rfl

lemma KzEnvFs_d_val :
    (KzEnvFs v h μ F fc).d = fsXp (μ * BoseGases.a v ^ 3) 6 := rfl

lemma KzEnvFs_s_val :
    (KzEnvFs v h μ F fc).s = fsXp (μ * BoseGases.a v ^ 3) 1 := rfl

lemma KzEnvFs_eT_val :
    (KzEnvFs v h μ F fc).eT = fsXp (μ * BoseGases.a v ^ 3) (23 / 4 : ℝ) := rfl

lemma KzEnvFs_intM_val : (KzEnvFs v h μ F fc).intM = mValue := rfl

lemma KzEnvFs_delta_val : (KzEnvFs v h μ F fc).delta = 1 := rfl

lemma KzEnvFs_b_val : (KzEnvFs v h μ F fc).b = bValue := rfl

lemma KzEnvFs_KL_def :
    (KzEnvFs v h μ F fc).KL =
      ((KzEnvFs v h μ F fc).Kl * (KzEnvFs v h μ F fc).d ^ 2) ^ (-(1 : ℝ)) := rfl

lemma KzEnvFs_KH_def :
    (KzEnvFs v h μ F fc).KH =
      fsXp (μ * BoseGases.a v ^ 3) (-(8 / 3 : ℝ)) * (μ * BoseGases.a v ^ 3) ^ (-(5 / 12 : ℝ)) :=
  rfl

lemma KzEnvFs_bigM_def :
    (KzEnvFs v h μ F fc).bigM =
      fsXp (μ * BoseGases.a v ^ 3) (-(1 : ℝ)) * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ)) :=
  rfl

lemma KzEnvFs_ell_def :
    (KzEnvFs v h μ F fc).ell =
      Work.BoseB7.side (KzEnvFs v h μ F fc).Kl (KzEnvFs v h μ F fc).mu
        (KzEnvFs v h μ F fc).aScat := rfl

lemma KzEnvFs_ell_val :
    (KzEnvFs v h μ F fc).ell =
      fsXp (μ * BoseGases.a v ^ 3) (-(3 / 2 : ℝ)) * (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) :=
  rfl

lemma KzEnvFs_lille_def :
    (KzEnvFs v h μ F fc).lille =
      (μ * BoseGases.a v ^ 3) * (KzEnvFs v h μ F fc).KH ^ 2 := rfl

lemma KzEnvFs_z_def :
    (KzEnvFs v h μ F fc).z = Real.sqrt (μ * (KzEnvFs v h μ F fc).ell ^ 3) := rfl

lemma KzEnvFs_rho_def :
    (KzEnvFs v h μ F fc).rho =
      (KzEnvFs v h μ F fc).z ^ 2 / (KzEnvFs v h μ F fc).ell ^ 3 := rfl

/-! ## 2. The closed forms of the `K` parameters

All are exponent arithmetic in the `fsXp`-calculus (`fsXp t c = t^{c/323}`,
`t^c = X^{323c}`, `X^aX^b = X^{a+b}`). -/

/-- `K_H = K̃_H(μa³)^{-5/12} = X^{-8/3}X^{-1615/12} = X^{-549/4}`. -/
lemma KzEnvFs_KH_val (h0 : 0 < μ * BoseGases.a v ^ 3) :
    (KzEnvFs v h μ F fc).KH = fsXp (μ * BoseGases.a v ^ 3) (-(549 / 4)) := by
  rw [KzEnvFs_KH_def, rpow_eq_fsXp h0.le, fsXp_mul h0]
  congr 1
  norm_num

/-- `K_L = (K_ℓd²)^{-1} = (X^{-3/2}X^{12})^{-1} = X^{-21/2}`. -/
lemma KzEnvFs_KL_val (h0 : 0 < μ * BoseGases.a v ^ 3) :
    (KzEnvFs v h μ F fc).KL = fsXp (μ * BoseGases.a v ^ 3) (-(21 / 2)) := by
  rw [KzEnvFs_KL_def, KzEnvFs_Kl_val, KzEnvFs_d_val, Real.rpow_neg_one, fsXp_pow h0.le,
    fsXp_mul h0, fsXp_inv h0]
  norm_num

/-- `𝓜 = K_M(μa³)^{-1/4} = X^{-1}X^{-323/4} = X^{-327/4}`. -/
lemma KzEnvFs_bigM_val (h0 : 0 < μ * BoseGases.a v ^ 3) :
    (KzEnvFs v h μ F fc).bigM = fsXp (μ * BoseGases.a v ^ 3) (-(327 / 4)) := by
  rw [KzEnvFs_bigM_def, rpow_eq_fsXp h0.le, fsXp_mul h0]
  norm_num

/-- `𝓁 = (μa³)K_H² = X^{323}X^{-549/2} = X^{97/2}` (FS `eq:DefLille`). -/
lemma KzEnvFs_lille_val (h0 : 0 < μ * BoseGases.a v ^ 3) :
    (KzEnvFs v h μ F fc).lille = fsXp (μ * BoseGases.a v ^ 3) (97 / 2) := by
  have h2 : (fsXp (μ * BoseGases.a v ^ 3) (-(549 / 4))) ^ 2
      = fsXp (μ * BoseGases.a v ^ 3) (-(549 / 2)) := by
    rw [← Real.rpow_natCast, fsXp_rpow h0.le]
    congr 1
    norm_num
  rw [KzEnvFs_lille_def, KzEnvFs_KH_val h0, h2]
  nth_rewrite 1 [delta_eq_fsXp h0.le]
  rw [fsXp_mul h0]
  congr 1
  norm_num

/-! ## 3. Positivity and the two derived scalars -/

/-- `ℓ > 0`: `ℓ = K_ℓ(μa)^{-1/2}` with `K_ℓ > 0` and `μa > 0`. -/
lemma KzEnvFs_ell_pos (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < (KzEnvFs v h μ F fc).ell := by
  have h0 : 0 < μ * BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  rw [KzEnvFs_ell_val]
  exact mul_pos (fsXp_pos h0) (Real.rpow_pos_of_pos (mul_pos hμ hav) _)

/-- `z ≠ 0`: `z = √(μℓ³)` and `μℓ³ > 0`. -/
lemma KzEnvFs_z_ne (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (KzEnvFs v h μ F fc).z ≠ 0 := by
  have hell := KzEnvFs_ell_pos (h := h) (F := F) (fc := fc) hμ hav
  rw [KzEnvFs_z_def]
  exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos hμ (pow_pos hell 3)))

/-- `z² = μℓ³`. -/
lemma KzEnvFs_z_sq (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (KzEnvFs v h μ F fc).z ^ 2 = μ * (KzEnvFs v h μ F fc).ell ^ 3 := by
  have hell := KzEnvFs_ell_pos (h := h) (F := F) (fc := fc) hμ hav
  rw [KzEnvFs_z_def]
  exact Real.sq_sqrt (le_of_lt (mul_pos hμ (pow_pos hell 3)))

/-- `ρ_z = z²/ℓ³ = μ` (FS `eq:Close` with equality). -/
lemma KzEnvFs_rho_val (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    (KzEnvFs v h μ F fc).rho = μ := by
  have hell := KzEnvFs_ell_pos (h := h) (F := F) (fc := fc) hμ hav
  rw [KzEnvFs_rho_def, KzEnvFs_z_sq (F := F) (fc := fc) hμ hav, mul_div_assoc,
    div_self (pow_ne_zero 3 (ne_of_gt hell)), mul_one]

end Aux

/-! ## 4. The view -/

theorem FSParamsViewCanon {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (ht1 : μ * BoseGases.a v ^ 3 ≤ 1)
    (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData.{0, 0} Mode) (fc : Work.BoseBoxFix.LowCut) :
    Nonempty (Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvFs v h μ F fc)) := by
  have h0 : 0 < μ * BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  refine ⟨{ t := μ * BoseGases.a v ^ 3
            t_pos := h0
            t_le_one := ht1
            mu_eq := KzEnvFs_mu_aScat_cube (F := F) (fc := fc)
            a_pos := hav
            Kl_eq := KzEnvFs_Kl_val (F := F) (fc := fc)
            KH_eq := rfl
            d_eq := KzEnvFs_d_val (F := F) (fc := fc)
            s_eq := KzEnvFs_s_val (F := F) (fc := fc)
            eT_eq := KzEnvFs_eT_val (F := F) (fc := fc)
            KL_eq := KzEnvFs_KL_def (F := F) (fc := fc)
            ell_eq := KzEnvFs_ell_def (F := F) (fc := fc)
            bigM_eq := KzEnvFs_bigM_def (F := F) (fc := fc)
            intM_eq := KzEnvFs_intM_val (F := F) (fc := fc)
            paramsOK := paramsOK_fsParams_le_one h0 ht1
            z_ne := KzEnvFs_z_ne (F := F) (fc := fc) hμ hav
            rho_close := ?_
            one_le_Kl := ?_
            one_le_KL := ?_
            one_le_KH := ?_
            one_le_bigM := ?_
            lille_le_delta := ?_
            delta_le_one := le_refl 1 }⟩
  · rw [KzEnvFs_rho_val (F := F) (fc := fc) hμ hav, KzEnvFs_mu, sub_self, abs_zero]
    linarith
  · rw [KzEnvFs_Kl_val (F := F) (fc := fc)]
    exact one_le_fsXp_of_nonpos h0 ht1 (by norm_num)
  · rw [KzEnvFs_KL_val (F := F) (fc := fc) h0]
    exact one_le_fsXp_of_nonpos h0 ht1 (by norm_num)
  · rw [KzEnvFs_KH_val (F := F) (fc := fc) h0]
    exact one_le_fsXp_of_nonpos h0 ht1 (by norm_num)
  · rw [KzEnvFs_bigM_val (F := F) (fc := fc) h0]
    exact one_le_fsXp_of_nonpos h0 ht1 (by norm_num)
  · rw [KzEnvFs_lille_val (F := F) (fc := fc) h0, KzEnvFs_delta_val (F := F) (fc := fc)]
    exact fsXp_le_one h0 ht1 (by norm_num)

end

end Work.BoseFixR
