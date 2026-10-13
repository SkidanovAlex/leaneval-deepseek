import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.WAngEnergyLe
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densIntegralLe
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row8
import Submission.Work.FTS.H2.L12densIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `ℋ^k`-membership is closed under multiplication by a constant: the weighted integrand is
`2`-homogeneous (`RowsN0Aux.HkIntegrand_const_mul`), so both conjuncts of `HkMem` follow from the
corresponding ones for `f` by multiplying the integrands with `c²`. -/
theorem HkMem_const_mul_of {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ =>
        Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkIntegrand_const_mul α k c f z θ)
    rw [hfun]
    exact h2.const_mul _

theorem EggBound {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      MeasureTheory.IntegrableOn
          (fun s => ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖) (Set.Ioi (0 : ℝ)) ∧
      (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖)
        ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  classical
  -- the `ℋ⁴`-norm bound `|N₁^{gg}| ≤ K₈ α^{-1/2}X²` is the (already proved) row 8 of the table
  obtain ⟨K₈, hK₈pos, hK₈⟩ := Work.FTS.Nonlinear.Pieces.RNP.row8 (Ct := 0) hN
  have hsqrt6pos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hKpos : 0 < Real.sqrt 6 * K₈ + 1 := by
    nlinarith [mul_pos hsqrt6pos hK₈pos]
  refine ⟨Real.sqrt 6 * K₈ + 1, hKpos, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ### The memberships of the two factors
  have hg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hgsm : Work.FTS.LocData.SmoothQuad g := hg4.1
  have hRreg : Work.FTS.Nonlin.RegQ α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1
  have hRsm : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hRreg.1
  -- ### `N₁^{gg} = 2·(ℛ(Φ̃_g)·g)`
  have hfeq : Work.FTS.Nonlin.N1gg α g Φg
      = fun z θ => 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gg]
    ring
  have hsm_f : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.N1gg α g Φg) := by
    rw [hfeq]
    exact Work.FTS.LocData.smoothQuad_const_mul 2
      (Work.FTS.LocData.smoothQuad_mul hRsm hgsm)
  have hprod := hN.prod α hαIoc (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) g
    hRreg hg4
  have hmem_f : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1gg α g Φg) := by
    rw [hfeq]
    exact HkMem_const_mul_of 2 hprod.1
  -- ### The weighted angular energy of `N₁^{gg}`
  obtain ⟨hAESM, hWEint, hWEle⟩ :=
    Work.FTS.Nonlinear.Pieces.Rl1.WAngEnergyLe hsm_f hmem_f
  -- ### The slice square-integrability a.e. in `s`
  have hcont : ContinuousOn (Function.uncurry (Work.FTS.Nonlin.N1gg α g Φg))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.FTS.Nonlin.N1gg α g Φg))
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) from hsm_f).continuousOn.mono
      (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) (subset_refl _))
  have hsl : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Work.FTS.Nonlin.N1gg α g Φg s θ) ^ 2)
        Work.Spaces.Iθ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hsI : (0 : ℝ) < s := hs
    have hsIz : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hsI.le
    have haesm : AEStronglyMeasurable (fun θ => Work.FTS.Nonlin.N1gg α g Φg s θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hsI
    refine MeasureTheory.Integrable.mono'
      (g := fun θ => Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N1gg α g Φg) s θ
        / (Work.Spaces.w s) ^ 2) ?_ (haesm.pow 2) ?_
    · exact (hmem_f.1 s hsIz).div_const _
    · have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖(Work.FTS.Nonlin.N1gg α g Φg s θ) ^ 2‖
            ≤ Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N1gg α g Φg) s θ
              / (Work.Spaces.w s) ^ 2 :=
        Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact Work.FTS.CoercivityFix.Coer1T.slice_sq_le_HkIntegrand_div_w_sq α hsI h0 h1)
      exact hkey
  -- ### Cauchy–Schwarz in `s`
  have hCS := Work.FTS.Nonlinear.Pieces.Rl1.L12densIntegralLe (f := Work.FTS.Nonlin.N1gg α g Φg)
    hsl hWEint
  have hstep1 : (∫ s in Set.Ioi (0 : ℝ),
        ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖)
      ≤ Real.sqrt 6 * Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg) := by
    refine hCS.trans ?_
    have h1 : Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s
          * (∫ θ in Work.Spaces.Iθ, (Work.FTS.Nonlin.N1gg α g Φg s θ) ^ 2))
        ≤ Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1gg α g Φg)) :=
      Real.sqrt_le_sqrt hWEle
    have h2 : Real.sqrt 6 * Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1gg α g Φg))
        = Real.sqrt 6 * Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg) := rfl
    calc Real.sqrt 6 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s
            * (∫ θ in Work.Spaces.Iθ, (Work.FTS.Nonlin.N1gg α g Φg s θ) ^ 2))
        ≤ Real.sqrt 6 * Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1gg α g Φg)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 6)
      _ = Real.sqrt 6 * Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg) := h2
  -- ### The `ℋ⁴`-norm of `N₁^{gg}` (row 8) and the power comparison
  have hstep2 := hK₈ hgal hstar hell hα hα1 hαα₂
  have hpow : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have hrw : α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) * α ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hα]; norm_num
    have hinv1 : 1 ≤ α ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      exact (one_le_inv₀ hα).mpr hα1
    rw [hrw]
    calc α ^ (-(1 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) * 1 := (mul_one _).symm
      _ ≤ α ^ (-(1 / 2 : ℝ)) * α ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left hinv1 (Real.rpow_nonneg hα.le _)
  have hX2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
  have hpowX : α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_le_mul_of_nonneg_right hpow hX2
  have hK₈nn : 0 ≤ Real.sqrt 6 * K₈ := mul_nonneg (Real.sqrt_nonneg 6) hK₈pos.le
  refine ⟨?_, ?_⟩
  · -- the `L¹`-integrability of the density, from `HkMem` and `SmoothQuad` alone
    have h1 : MeasureTheory.IntegrableOn
        (Work.Elliptic.L12dens (Work.FTS.Nonlin.N1gg α g Φg)) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.L12densIntegrable α (Work.FTS.Nonlin.N1gg α g Φg) hα hα1 hsm_f hmem_f
    have h2 : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K (Work.FTS.Nonlin.N1gg α g Φg)) (Set.Ioi (0 : ℝ)) :=
      h1.congr_fun (fun s _ => Work.FTS.H2.L12dens_eq_FM_K (Work.FTS.Nonlin.N1gg α g Φg) s)
        measurableSet_Ioi
    exact h2.norm
  · calc (∫ s in Set.Ioi (0 : ℝ),
          ‖Work.Construction.L12dens (Work.FTS.Nonlin.N1gg α g Φg) s‖)
        ≤ Real.sqrt 6 * Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg) := hstep1
      _ ≤ Real.sqrt 6 * (K₈ * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep2 (Real.sqrt_nonneg 6)
      _ ≤ (Real.sqrt 6 * K₈ + 1) * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
          have h3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
            mul_nonneg (Real.rpow_nonneg hα.le _) hX2
          calc Real.sqrt 6 * (K₈ * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2))
              = (Real.sqrt 6 * K₈) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
                ring
            _ ≤ (Real.sqrt 6 * K₈) * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
                mul_le_mul_of_nonneg_left hpowX hK₈nn
            _ ≤ (Real.sqrt 6 * K₈ + 1) * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
                mul_le_mul_of_nonneg_right (by linarith) h3

end Work.FTS.Nonlinear.Pieces.Rl1
