import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.SummBounds
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Deleg.psiExpansion
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.psiSeries_bslOp
import Submission.Work.FTS.PhiStar.Series.psiSeries_solves_rem
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam2DiffId =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

theorem Fam2DiffId (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z')
    (hchiasm : ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ n : ℕ,
      ContDiffOn ℝ n (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2)))
    (hWtDeriv : ∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ θ' : ℝ,
      θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ'
        = Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ (j - 1)) θ') :
    ∀ k i : ℕ, k + i + 1 ≤ 7 →
      (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter i (Work.Spaces.pth (fun z' θ' => (z' + 1) / z'
            * (Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z' θ'
              / Work.Construction.s2 θ')))) z θ
        = α ^ 2 * ((∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
              α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
                * ((Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv
                    (Work.FTS.PhiStar.FlatWAux.chia ψ j)) θ))
            + α ^ Work.FTS.PhiStar.FlatWAux.J
              * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                  * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
                  * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                      * Work.FTS.PhiStar.Radial.radGreen α m
                          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                            (Work.FTS.VocabO.phiA α)) z'') z)
                  * ((Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ))) := by
  intro k i hki
  have hi6 : i ≤ 6 := by omega
  -- the radial profiles and the angular numbers
  let radj : ℕ → ℝ → ℝ := fun j z' => (z' + 1) / z' * Ajit α j (VocabO.phiA α) z'
  let radJ : ℕ → ℝ → ℝ := fun m z' => (z' + 1) / z'
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
  let aa : ℕ → ℝ := fun j => (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ
  let cc : ℕ → ℝ := fun m => (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ
  let Vsum : ℝ → ℝ := fun z' => ∑' m : ℕ,
      (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m) * radJ m z'
  let Psi : ℝ → ℝ := fun z' => α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * aa j * radj j z')
      + α ^ J * Vsum z')
  have hz2 : 0 < z / 2 := by linarith
  have hz2lt : z / 2 < 2 * z := by linarith
  have hzmid : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  obtain ⟨CrJ, hCrJ0, hrbJ'⟩ := hrbJ
  have hrbJ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ C / Gegenbauer.lam m := ⟨CrJ, hCrJ0, hrbJ'⟩
  -- a crude bound for the `m = 0` mode on the compact interval
  have hK0 : ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ r : ℕ, r ≤ k → ∀ y : ℝ, y ∈ Set.Icc (z / 2) (2 * z) →
      |iteratedDeriv r (radJ 0) y| ≤ K0 := by
    have hcont : ∀ r : ℕ, ContinuousOn (fun y => iteratedDeriv r (radJ 0) y)
        (Set.Icc (z / 2) (2 * z)) := by
      intro r
      have h1 : ContDiffOn ℝ 1 (iteratedDeriv r (radJ 0)) (Set.Ioi 0) := by
        refine contDiffOn_iteratedDeriv isOpen_Ioi r 1 ?_
        have : 1 + r = r + 1 := by omega
        rw [this]
        exact contDiffOn_radJ α 0 (r + 1)
      exact h1.continuousOn.mono (fun y hy => lt_of_lt_of_le hz2 hy.1)
    choose Kr hKr using fun r => IsCompact.exists_bound_of_continuousOn isCompact_Icc (hcont r)
    refine ⟨∑ r ∈ Finset.range (k + 1), |Kr r|,
      Finset.sum_nonneg (fun r _ => abs_nonneg _), fun r hr y hy => ?_⟩
    have h1 : |Kr r| ≤ ∑ r' ∈ Finset.range (k + 1), |Kr r'| :=
      Finset.single_le_sum (fun r' _ => abs_nonneg (Kr r'))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    exact le_trans (le_trans (hKr r y hy) (le_abs_self (Kr r))) h1
  obtain ⟨K0, hK0nn, hK0⟩ := hK0
  -- the `z`-side majorant (on the interval one has `(y+1)^r ≥ 1`)
  let Bz : ℕ → ℝ := fun m => CrJ / Gegenbauer.lam m + (if m = 0 then K0 else 0)
  have hBz0 : ∀ m : ℕ, 0 ≤ Bz m := by
    intro m
    change (0 : ℝ) ≤ CrJ / Gegenbauer.lam m + (if m = 0 then K0 else 0)
    have h1 : (0 : ℝ) ≤ CrJ / Gegenbauer.lam m := div_nonneg hCrJ0.le (lam_nonneg m)
    split_ifs with hm
    · linarith
    · linarith
  have hBzbound : ∀ (m r : ℕ), r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo (z / 2) (2 * z) →
      |iteratedDeriv r (radJ m) y| ≤ Bz m := by
    intro m r hr y hy
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · change |iteratedDeriv r (radJ 0) y| ≤
        CrJ / Gegenbauer.lam 0 + (if (0 : ℕ) = 0 then K0 else 0)
      rw [if_pos rfl]
      have h := hK0 r hr y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have h1 : (0 : ℝ) ≤ CrJ / Gegenbauer.lam 0 := div_nonneg hCrJ0.le (lam_nonneg 0)
      linarith
    · have hy0 : 0 < y := lt_of_lt_of_le hz2 hy.1.le
      change |iteratedDeriv r (radJ m) y| ≤
        CrJ / Gegenbauer.lam m + (if m = 0 then K0 else 0)
      rw [if_neg (by omega : ¬ m = 0), add_zero]
      have h1 : |(y + 1) ^ r * iteratedDeriv r (radJ m) y| ≤ CrJ / Gegenbauer.lam m := by
        simpa using hrbJ' m hm r (by omega) y hy0
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ y + 1) r)] at h1
      have hy1 : (1 : ℝ) ≤ (y + 1) ^ r := one_le_pow₀ (by linarith)
      have h2 : |iteratedDeriv r (radJ m) y|
          ≤ (y + 1) ^ r * |iteratedDeriv r (radJ m) y| := by
        nlinarith [abs_nonneg (iteratedDeriv r (radJ m) y), hy1]
      linarith
  -- summability of the `z`-side majorant
  have hcBz : Summable (fun m : ℕ => |(Series.bmode m ψ
      * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)| * Bz m) := by
    have h2 := (Fam2Diff.SummBounds hi6 hz hθ hb0 hdec hrbJ0).2
    have h2' : Summable (fun m : ℕ => CrJ *
        (|Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ J * |cc m| / Gegenbauer.lam m)) :=
      h2.mul_left _
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (hBz0 m))
      (fun m => ?_) h2'
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hl0 : Gegenbauer.lam 0 = 0 := by simp [Gegenbauer.lam]
      have hJ : J ≠ 0 := by norm_num [J]
      change |(Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ J * cc 0)| * Bz 0 ≤ _
      rw [hb0, hl0, inv_zero, zero_pow hJ]
      simp
    · have hlam : 0 < Gegenbauer.lam m := lam_pos hm
      change |(Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)| *
        (CrJ / Gegenbauer.lam m + (if m = 0 then K0 else 0)) ≤ _
      rw [if_neg (by omega : ¬ m = 0), add_zero]
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (lam_nonneg m)) J)]
      field_simp
      linarith
  -- smoothness of the two pieces of `Psi`
  have hUsm : ContDiffOn ℝ k (fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z')
      (Set.Ioo (z / 2) (2 * z)) := by
    refine ContDiffOn.sum (fun j _ => ?_)
    exact contDiffOn_const.mul ((contDiffOn_radj α j k).mono (fun y hy =>
      lt_trans hz2 hy.1))
  have hUcd : ContDiffAt ℝ k (fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z') z :=
    (hUsm.contDiffWithinAt hzmid).contDiffAt (isOpen_Ioo.mem_nhds hzmid)
  have hVTA := Fam2Diff.TsumContDiff (k := k)
    (c := fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)
    (q := radJ) (B := Bz) (a := z / 2) (b := 2 * z) hz2lt hBz0 hcBz
    (fun m => (contDiffOn_radJ α m k).mono (fun y hy => lt_trans hz2 hy.1))
    (fun m r hr y hy => by
      change |iteratedDeriv r (radJ m) y| ≤ Bz m
      exact hBzbound m r hr y hy)
  have hVsm : ContDiffOn ℝ k Vsum (Set.Ioo (z / 2) (2 * z)) := hVTA.1
  have hVcd : ContDiffAt ℝ k Vsum z :=
    (hVsm.contDiffWithinAt hzmid).contDiffAt (isOpen_Ioo.mem_nhds hzmid)
  have hVval : ∀ r : ℕ, r ≤ k → ∀ y ∈ Set.Ioo (z / 2) (2 * z),
      iteratedDeriv r Vsum y = ∑' m : ℕ, (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)
        * iteratedDeriv r (radJ m) y := hVTA.2
  -- the `z`-derivatives
  have h1 : iteratedDeriv k Psi z = α ^ 2 *
      (iteratedDeriv k (fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z') z
        + α ^ J * iteratedDeriv k Vsum z) := by
    show iteratedDeriv k (fun z' => α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * aa j * radj j z')
      + α ^ J * Vsum z')) z = _
    rw [iteratedDeriv_const_mul_field]
    congr 1
    show iteratedDeriv k ((fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z')
      + fun z' => α ^ J * Vsum z') z = _
    rw [iteratedDeriv_add hUcd (contDiffAt_const.mul hVcd), iteratedDeriv_const_mul (α ^ J) hVcd]
  have hU_e : (fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z')
      = ∑ j ∈ Finset.range J, (fun y : ℝ => α ^ j * aa j * radj j y) := by
    funext y
    show (∑ j ∈ Finset.range J, α ^ j * aa j * radj j y) = _
    rw [Finset.sum_apply]
  have h2 : iteratedDeriv k (fun z' => ∑ j ∈ Finset.range J, α ^ j * aa j * radj j z') z
      = ∑ j ∈ Finset.range J, α ^ j * aa j * iteratedDeriv k (radj j) z := by
    have hcd : ∀ j ∈ Finset.range J, ContDiffAt ℝ k
        (fun y : ℝ => α ^ j * aa j * radj j y) z := by
      intro j hj
      exact (contDiffOn_const.mul (contDiffOn_radj α j k)).contDiffAt (isOpen_Ioi.mem_nhds hz)
    have hsum := iteratedDeriv_sum (n := k) (x := z) (I := Finset.range J)
      (f := fun j y => α ^ j * aa j * radj j y) hcd
    rw [hU_e, hsum]
    exact Finset.sum_congr rfl (fun j _ => by rw [iteratedDeriv_const_mul_field])
  have h3 : iteratedDeriv k Vsum z = ∑' m : ℕ, (Series.bmode m ψ
      * ((Gegenbauer.lam m)⁻¹) ^ J * cc m) * iteratedDeriv k (radJ m) z :=
    hVval k le_rfl z hzmid
  -- the `(z+1)^k` is distributed over the sums
  have hS : (z + 1) ^ k * (∑ j ∈ Finset.range J, α ^ j * aa j * iteratedDeriv k (radj j) z)
      = ∑ j ∈ Finset.range J, α ^ j * ((z + 1) ^ k * iteratedDeriv k (radj j) z) * aa j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hT : (z + 1) ^ k * (∑' m : ℕ, (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)
        * iteratedDeriv k (radJ m) z)
      = ∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
          * ((z + 1) ^ k * iteratedDeriv k (radJ m) z) * cc m := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun m => by ring)
  have hZ : (z + 1) ^ k * iteratedDeriv k Psi z
      = α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * ((z + 1) ^ k * iteratedDeriv k (radj j) z) * aa j)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (radJ m) z) * cc m)) := by
    rw [h1, h2, h3]
    rw [show (z + 1) ^ k * (α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * aa j * iteratedDeriv k (radj j) z)
          + α ^ J * (∑' m : ℕ, (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)
              * iteratedDeriv k (radJ m) z)))
        = α ^ 2 * ((z + 1) ^ k * (∑ j ∈ Finset.range J,
              α ^ j * aa j * iteratedDeriv k (radj j) z)
          + α ^ J * ((z + 1) ^ k * (∑' m : ℕ,
              (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J * cc m)
                * iteratedDeriv k (radJ m) z))) from by ring]
    rw [hS, hT]
  -- the identification of the left-hand side
  have hLHS : (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter i (Work.Spaces.pth (fun z' θ' => (z' + 1) / z'
          * (Series.psiSeries α (RemSource α ψ) z' θ' / Work.Construction.s2 θ')))) z θ
      = (z + 1) ^ k * iteratedDeriv k (fun z' => (Work.Spaces.Lop^[i])
          (deriv (fun θ'' => (z' + 1) / z'
            * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ) z := by
    congr 1
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    refine congrArg (fun g => iteratedDeriv k g z) ?_
    funext z'
    have h := congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (Work.Spaces.pth (fun z' θ' =>
      (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ' / Work.Construction.s2 θ'))) z') θ
    have hfun : (fun θ' => Work.Spaces.pth (fun z' θ' => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' θ' / Work.Construction.s2 θ')) z' θ')
        = deriv (fun θ'' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ''
            / Work.Construction.s2 θ'')) := rfl
    rw [h, hfun]
  have hBridge : (fun z' => (Work.Spaces.Lop^[i]) (deriv (fun θ'' => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ)
      =ᶠ[𝓝 z] Psi := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Lop_angle_id α ψ θ i hi6 hθ hb0 hdec hgr hrb hrbJ0 hexp hchiasm hWtDeriv z' hz']
    exact psi_alg α ψ θ i z'
  rw [hLHS]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hBridge]
  exact hZ


end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.bslSolExists_moment_of_node_hyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-- Two angle functions which agree on the *open* interval `(0,π/2)` agree a.e. on
`Iθ = [0,π/2]` (the two endpoints are a null set). -/
private lemma ae_imp_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    ∀ᵐ θ ∂volume, θ ∈ Iθ → f θ = g θ := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.ae_restrict_iff' (s := Iθ)
    (show MeasurableSet Iθ from measurableSet_Icc), ← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))


end Work.FTS.PhiStar.Honesty
end
end
