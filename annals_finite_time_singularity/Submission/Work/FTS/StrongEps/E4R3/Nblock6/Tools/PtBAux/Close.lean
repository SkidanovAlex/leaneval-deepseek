/-
# `ptBoundDz` tools: the per-term closing shapes

Part of the `ptBoundDz` development (see `Tools/ptBoundDz.lean` for the statement and the
overall route).  Everything here lives in the sub-namespace `...Tools.PtB`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.ProdDefs6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools
namespace PtB

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
/-! ## The closures of the `(γ-1)⁻¹`-block -/

/-- The `(γ-1)⁻¹·ℋ⁶(A)·I⁶_f` shape is dominated by `Maj2`. -/
theorem inv_hksqA_I6f_le_Maj2 {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkIntegrand α 6 f z θ)
      ≤ Maj2 α A f z θ := by
  have hγ := gam_sub_one_pos_ptb hα
  have hinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  have hSf : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hSA : 0 ≤ Work.Spaces.HkSq α 6 A := Work.Spaces.HkSq_nonneg α 6 A
  have hIf : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hIA : 0 ≤ Work.Spaces.HkIntegrand α 6 A z θ := Work.Spaces.HkIntegrand_nonneg α 6 A z θ
  have hY : 0 ≤ Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f := add_nonneg hSA hSf
  have hZ : 0 ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
    add_nonneg hIA hIf
  have hstep : (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkIntegrand α 6 f z θ)
      ≤ (Work.Spaces.gam α - 1)⁻¹
        * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hinv
    exact mul_le_mul (le_add_of_nonneg_right hSf) (le_add_of_nonneg_left hIA) hIf hY
  have hstep2 : (Work.Spaces.gam α - 1)⁻¹
        * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      ≤ Maj2 α A f z θ := by
    rw [Maj2]
    have h1 : (1 + (Work.Spaces.gam α - 1)⁻¹ * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
        = (Work.Spaces.gam α - 1)⁻¹
            * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          + (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
      ring
    rw [h1]
    exact le_add_of_nonneg_right hZ
  exact le_trans hstep hstep2

/-- The symmetric `(γ-1)⁻¹·ℋ⁶(f)·I⁶_A` shape is dominated by `Maj2`. -/
theorem inv_hksqf_I6A_le_Maj2 {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 f * Work.Spaces.HkIntegrand α 6 A z θ)
      ≤ Maj2 α A f z θ := by
  have hγ := gam_sub_one_pos_ptb hα
  have hinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  have hSf : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hSA : 0 ≤ Work.Spaces.HkSq α 6 A := Work.Spaces.HkSq_nonneg α 6 A
  have hIf : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hIA : 0 ≤ Work.Spaces.HkIntegrand α 6 A z θ := Work.Spaces.HkIntegrand_nonneg α 6 A z θ
  have hY : 0 ≤ Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f := add_nonneg hSA hSf
  have hZ : 0 ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
    add_nonneg hIA hIf
  have hstep : (Work.Spaces.gam α - 1)⁻¹
        * (Work.Spaces.HkSq α 6 f * Work.Spaces.HkIntegrand α 6 A z θ)
      ≤ (Work.Spaces.gam α - 1)⁻¹
        * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hinv
    exact mul_le_mul (le_add_of_nonneg_left hSA) (le_add_of_nonneg_right hIf) hIA hY
  have hstep2 : (Work.Spaces.gam α - 1)⁻¹
        * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      ≤ Maj2 α A f z θ := by
    rw [Maj2]
    have h1 : (1 + (Work.Spaces.gam α - 1)⁻¹ * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
          * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
        = (Work.Spaces.gam α - 1)⁻¹
            * ((Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          + (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
      ring
    rw [h1]
    exact le_add_of_nonneg_right hZ
  exact le_trans hstep hstep2

/-! ## The closure lemmas for the per-term estimates -/

/-- Closing shape: `X` is priced *pointwise* by the Agmon bound for `A` and the weighted
slot `Y` by the `f`-integrand. -/
theorem close_supA_localf {α CPw : ℝ} {A f : ℝ → ℝ → ℝ} {MA KA z θ X Y W : ℝ}
    (hα : 0 < α) (hCPw : 0 < CPw)
    (hX : X ^ 2 ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A)
    (hY : (Y * W) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    (X * Y * W) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
  have hγ := gam_sub_one_pos_ptb hα
  have hCM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPw (le_max_left _ _)
  have h1 : (X * Y * W) ^ 2 = X ^ 2 * (Y * W) ^ 2 := by ring
  rw [h1]
  calc X ^ 2 * (Y * W) ^ 2
      ≤ (CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A)
          * Work.Spaces.HkIntegrand α 6 f z θ :=
        mul_le_mul hX hY (sq_nonneg _) (mul_nonneg (div_nonneg hCPw.le hγ.le)
          (Work.Spaces.HkSq_nonneg α 6 A))
    _ = CPw * ((Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkIntegrand α 6 f z θ)) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ CPw * Maj2 α A f z θ :=
        mul_le_mul_of_nonneg_left (inv_hksqA_I6f_le_Maj2 hα A f z θ) hCPw.le
    _ ≤ max CPw 1 * Maj2 α A f z θ := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Maj2_nonneg hα A f z θ)
    _ ≤ max CPw 1 * Maj α A f MA KA z θ :=
        mul_le_mul_of_nonneg_left (Maj2_le_Maj hα A f MA KA z θ) hCMpos.le

/-- Closing shape: the weighted slot `X` is priced by the `A`-integrand and `Y` pointwise by
the Agmon bound for `f`. -/
theorem close_locA_supf {α CPw : ℝ} {A f : ℝ → ℝ → ℝ} {MA KA z θ X Y W : ℝ}
    (hα : 0 < α) (hCPw : 0 < CPw)
    (hX : (X * W) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 A z θ)
    (hY : Y ^ 2 ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) :
    (X * Y * W) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
  have hγ := gam_sub_one_pos_ptb hα
  have hCM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPw (le_max_left _ _)
  have h1 : (X * Y * W) ^ 2 = (X * W) ^ 2 * Y ^ 2 := by ring
  rw [h1]
  calc (X * W) ^ 2 * Y ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 A z θ
          * (CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul hX hY (sq_nonneg _) (Work.Spaces.HkIntegrand_nonneg α 6 A z θ)
    _ = CPw * ((Work.Spaces.gam α - 1)⁻¹
          * (Work.Spaces.HkSq α 6 f * Work.Spaces.HkIntegrand α 6 A z θ)) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ CPw * Maj2 α A f z θ :=
        mul_le_mul_of_nonneg_left (inv_hksqf_I6A_le_Maj2 hα A f z θ) hCPw.le
    _ ≤ max CPw 1 * Maj2 α A f z θ := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Maj2_nonneg hα A f z θ)
    _ ≤ max CPw 1 * Maj α A f MA KA z θ :=
        mul_le_mul_of_nonneg_left (Maj2_le_Maj hα A f MA KA z θ) hCMpos.le

/-- Closing shape: the undifferentiated coefficient `A` is bounded by `MA` and the weighted
slot `Y` by the top (`ℋ⁷`) integrand of `f`. -/
theorem close_MA {α CPw : ℝ} {A f : ℝ → ℝ → ℝ} {MA KA z θ Y W : ℝ}
    (hα : 0 < α) (hCPw : 0 < CPw) (hAz : (A z θ) ^ 2 ≤ MA ^ 2)
    (hY : (Y * W) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ) :
    (A z θ * Y * W) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
  have hCM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  have h1 : (A z θ * Y * W) ^ 2 = (A z θ) ^ 2 * (Y * W) ^ 2 := by ring
  rw [h1]
  calc (A z θ) ^ 2 * (Y * W) ^ 2
      ≤ MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ :=
        mul_le_mul hAz hY (sq_nonneg _) (sq_nonneg MA)
    _ = Maj1 α f MA z θ := rfl
    _ ≤ Maj α A f MA KA z θ := Maj1_le_Maj hα A f MA KA z θ
    _ ≤ max CPw 1 * Maj α A f MA KA z θ :=
        le_mul_of_one_le_left (Maj_nonneg hα A f MA KA z θ) hCM

/-- Closing shape: the term `D_θ A · Y · W` with `Y` a slot of `f` of order `≤ 6` is closed by
the hypothesis `|∂_θA| ≤ KA`: `D_θA = sin(2θ)·∂_θA` and `sin(2θ)^{2-γ+η} ≤ 1`. -/
theorem close_KA {α CPw : ℝ} {A f : ℝ → ℝ → ℝ} {MA KA z θ Y W : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCPw : 0 < CPw)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hDth : (Work.Spaces.Dth A z θ) ^ 2 ≤ KA ^ 2 * (Real.sin (2 * θ)) ^ 2)
    (hW : W = Work.Spaces.Wt α z θ)
    (hY : (Y * Hv z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    (Work.Spaces.Dth A z θ * Y * W) ^ 2 ≤ max CPw 1 * Maj α A f MA KA z θ := by
  have hCM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  have hspos : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam := gam_le_two_add_eta hα1
  -- `sin^{-γ} = sin^{-η}·sin^{η-γ}`
  have hsplit : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  -- `sin²·sin^{η-γ} = sin^{2+η-γ} ≤ 1`
  have hexp : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) + (Work.Spaces.eta - Work.Spaces.gam α) := by
    have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2c]
    linarith
  have h2 : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α)
      ≤ (1 : ℝ) := by
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2, ← Real.rpow_add hspos]
    exact Real.rpow_le_one hspos.le hs1 hexp
  -- `∂_θ A`-bound made homogeneous: `(D_θA)²·sin^{η-γ} ≤ KA²`
  have hkey : (Work.Spaces.Dth A z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α) ≤ KA ^ 2 := by
    have h1 : (Work.Spaces.Dth A z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α)
        ≤ (KA ^ 2 * (Real.sin (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α) :=
      mul_le_mul_of_nonneg_right hDth (Real.rpow_nonneg hspos.le _)
    refine le_trans h1 ?_
    have h2' : (KA ^ 2 * (Real.sin (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α)
        = KA ^ 2 * (((Real.sin (2 * θ)) ^ 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α)) := by ring
    rw [h2']
    calc KA ^ 2 * (((Real.sin (2 * θ)) ^ 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α))
        ≤ KA ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg KA)
      _ = KA ^ 2 := by ring
  -- the identity `T = (Y·Hv)²·((D_θA)²·sin^{η-γ})`
  have hid : (Work.Spaces.Dth A z θ * Y * W) ^ 2
      = (Y * Hv z θ) ^ 2
        * ((Work.Spaces.Dth A z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α)) := by
    rw [hW]
    simp only [mul_pow]
    rw [Wt_sq_eq hθ, hsplit, Hv_sq_eq hθ]
    ring
  rw [hid]
  calc (Y * Hv z θ) ^ 2
        * ((Work.Spaces.Dth A z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - Work.Spaces.gam α))
      ≤ (Y * Hv z θ) ^ 2 * KA ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = KA ^ 2 * (Y * Hv z θ) ^ 2 := by ring
    _ ≤ KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
        mul_le_mul_of_nonneg_left hY (sq_nonneg KA)
    _ = Maj3 α f KA z θ := rfl
    _ ≤ Maj α A f MA KA z θ := Maj3_le_Maj hα A f MA KA z θ
    _ ≤ max CPw 1 * Maj α A f MA KA z θ :=
        le_mul_of_one_le_left (Maj_nonneg hα A f MA KA z θ) hCM


end

end PtB

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
