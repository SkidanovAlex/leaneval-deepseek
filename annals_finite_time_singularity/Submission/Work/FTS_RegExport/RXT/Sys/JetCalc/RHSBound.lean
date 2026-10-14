import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_system
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.RHSBound` — the uniform jet bound of `RHS`

On a closed box of the open quadrant, all mixed jets of `RHS σ` of order `≤ 2` are bounded by a
constant independent of `σ ∈ (0,S]`: coefficient jets by the `dbnd` constant of `CoeffJets`,
profile jets by `Ftau_mixed_bound`/`FtauS_mixed_bound`, combined through `abs_mixed_mul_bound`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Small arithmetic helpers (the Nat inequalities of the index bookkeeping) -/

/-- `a + b ≤ n` gives `b + a ≤ n`. -/
theorem add_swap_le {a b n : ℕ} (h : a + b ≤ n) : b + a ≤ n := by rwa [Nat.add_comm] at h

/-- `a + b ≤ n` gives `b + a + 1 ≤ n + 1`. -/
theorem add_swap_succ_le {a b n : ℕ} (h : a + b ≤ n) : b + a + 1 ≤ n + 1 :=
  Nat.succ_le_succ (add_swap_le h)

/-- `a + b ≤ n` gives `b + 1 + a ≤ n + 1`. -/
theorem add_one_swap_le {a b n : ℕ} (h : a + b ≤ n) : b + 1 + a ≤ n + 1 := by
  rw [Nat.add_right_comm]
  exact Nat.succ_le_succ (add_swap_le h)

/-- `a + b ≤ n` gives `b + (a + 1) ≤ n + 1`. -/
theorem add_succ_right_le {a b n : ℕ} (h : a + b ≤ n) : b + (a + 1) ≤ n + 1 := by
  rw [← Nat.add_assoc, Nat.add_comm b a]
  exact Nat.succ_le_succ h

theorem RHS_mixed_bound {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      ∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (RHS α Φs E g σ) z θ| ≤ C := by
  obtain ⟨M₀, hM₀⟩ := hVP.dbnd
  obtain ⟨Cq, hCq0, hCq⟩ := FtauS_mixed_bound
    (α := α) (C₀ := C₀) (S := S) hα hα13 hS hOK ha hab hc hcd hd
  set M : ℝ := |M₀| with hMdef
  have hMnn : 0 ≤ M := abs_nonneg M₀
  refine ⟨12 * (M * Cq) + 1, by positivity, ?_⟩
  intro σ hσ z hz θ hθ j i hji
  have hσI : σ ∈ Set.Icc (0:ℝ) S := ⟨hσ.1.le, hσ.2⟩
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hd
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hzpos, hθpos, hθlt⟩
  have hji2 : j + i ≤ 2 := hji
  -- the profile is `C³` on the open quadrant
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1.le
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    hQ3.of_le (by norm_num)
  have hDz2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  -- jet bounds of the profile
  have hQjets : ∀ m n : ℕ, m + n ≤ 3 →
      |Work.Spaces.mixed m n (FtauS α g σ) z θ| ≤ Cq :=
    fun m n hmn => hCq σ hσ m n hmn z hz θ hθ
  -- jet bounds of the three coefficients (the `dbnd` clause of `CoeffJets`)
  have hVj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ) z θ|
        ≤ M := by
    intro a' b' hab
    exact le_trans (hM₀ σ hσI b' a' (le_trans (add_swap_le hab) hji2) z θ hzpos hθpos hθlt).1
      (le_abs_self M₀)
  have hbj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ) z θ|
        ≤ M := by
    intro a' b' hab
    exact le_trans (hM₀ σ hσI b' a' (le_trans (add_swap_le hab) hji2) z θ hzpos hθpos hθlt).2.1
      (le_abs_self M₀)
  have hcj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ) z θ|
        ≤ M := by
    intro a' b' hab
    exact le_trans (hM₀ σ hσI b' a' (le_trans (add_swap_le hab) hji2) z θ hzpos hθpos hθlt).2.2.1
      (le_abs_self M₀)
  -- jet bounds of `D_zF`, `D_θF` and `F`
  have hDzj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (Work.Spaces.Dz (FtauS α g σ)) z θ| ≤ Cq := by
    intro a' b' hab
    have hshift := mixed_Dz_shift Work.FTS.EllipticEst.isOpen_Q0 hQ3 (k := b') (l := a')
      (add_swap_succ_le (le_trans hab hji2))
    have h1 := hshift hp
    have h2 : Work.Spaces.mixed b' a' (Work.Spaces.Dz (FtauS α g σ)) z θ
        = Work.Spaces.mixed (b' + 1) a' (FtauS α g σ) z θ := h1
    rw [h2]
    exact hQjets (b' + 1) a' (add_one_swap_le (le_trans hab hji2))
  have hDthj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (Work.Spaces.Dth (FtauS α g σ)) z θ| ≤ Cq := by
    intro a' b' hab
    rw [mixed_Dth_shift b' a' (FtauS α g σ)]
    exact hQjets b' (a' + 1) (add_succ_right_le (le_trans hab hji2))
  have hQj : ∀ a' b' : ℕ, a' + b' ≤ j + i →
      |Work.Spaces.mixed b' a' (FtauS α g σ) z θ| ≤ Cq :=
    fun a' b' hab => hQjets b' a' (le_trans (add_swap_le hab) (le_trans hji2 (by norm_num)))
  -- the three products
  have hA : |Work.Spaces.mixed j i (Afun α Φs E g σ) z θ| ≤ (2 : ℝ) ^ (j + i) * (M * Cq) :=
    abs_mixed_mul_bound Work.FTS.EllipticEst.isOpen_Q0
      ((hC2 σ hσ.1.le).1.of_le (Nat.cast_le.mpr hji2)) (hDz2.of_le (Nat.cast_le.mpr hji2))
      hp hMnn hCq0 hVj hDzj
  have hB : |Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ| ≤ (2 : ℝ) ^ (j + i) * (M * Cq) :=
    abs_mixed_mul_bound Work.FTS.EllipticEst.isOpen_Q0
      ((hC2 σ hσ.1.le).2.1.of_le (Nat.cast_le.mpr hji2)) (hDth2.of_le (Nat.cast_le.mpr hji2))
      hp hMnn hCq0 hbj hDthj
  have hC : |Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ| ≤ (2 : ℝ) ^ (j + i) * (M * Cq) :=
    abs_mixed_mul_bound Work.FTS.EllipticEst.isOpen_Q0
      ((hC2 σ hσ.1.le).2.2.of_le (Nat.cast_le.mpr hji2)) (hQ2.of_le (Nat.cast_le.mpr hji2))
      hp hMnn hCq0 hcj hQj
  -- assemble
  rw [mixed_RHS_eq hα hα13 hOK hC2 hσ hji hzpos hθpos hθlt, abs_neg]
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    have h2 : (2 : ℝ) ^ (j + i) ≤ (2 : ℝ) ^ 2 :=
      pow_le_pow_right₀ (by norm_num) hji2
    norm_num at h2
    exact h2
  have hM4 : (2 : ℝ) ^ (j + i) * (M * Cq) ≤ 4 * (M * Cq) :=
    mul_le_mul_of_nonneg_right hpow (mul_nonneg hMnn hCq0)
  calc |Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ|
      ≤ |Work.Spaces.mixed j i (Afun α Φs E g σ) z θ|
        + |Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ|
        + |Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ| := by
          have h1 := abs_add_le (Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
            + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ)
            (Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ)
          have h2 := abs_add_le (Work.Spaces.mixed j i (Afun α Φs E g σ) z θ)
            (Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ)
          have h3 := abs_nonneg (Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ)
          linarith [h1, h2, h3]
    _ ≤ 4 * (M * Cq) + 4 * (M * Cq) + 4 * (M * Cq) := by
          linarith [le_trans hA hM4, le_trans hB hM4, le_trans hC hM4]
    _ ≤ 12 * (M * Cq) + 1 := by linarith [mul_nonneg hMnn hCq0]

end Work.FTS_RegExport.RXT.Sys
