import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
/-! ## The requested piece -/

theorem fkThetaIbpPiece : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn} {M : ℝ},
    0 < α → α ≤ 1 →
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.FK f z
          * (∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)|
        ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fk_radial_shift
  refine ⟨C₁ * (4 * Real.sqrt C₀) + 1, by positivity, ?_⟩
  intro α f M hα hα1 hdd a b ρ hab hρ
  obtain ⟨hO, hmem6, hmem7, _hvanish, haxis, hM⟩ := hdd
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hO 4 (by norm_num) hmem6
  have hsq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  -- the `θ`-Cauchy–Schwarz bound on the angular moment
  have haesm : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hO.continuousOn hz
  have hgA : ∀ z : ℝ, 0 < z → |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := by
    intro z hz
    have hsqint : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
      have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
        one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
      refine MeasureTheory.Integrable.mono' (hmem4.1 z (Set.mem_Ici.mpr (le_of_lt hz)))
        ((haesm z hz).pow 2) ?_
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hh := Work.FTS.StrongPersist.H6Pair6Aux.leafdom_rpow (α := α) (h := f) hα
        (q := 0) (a := 0) (b := 0) (k := 4) (by norm_num)
        (by rw [Work.Spaces.gam]; linarith)
        (fun _ => by rw [Work.Spaces.eta]; norm_num)
        (Set.mem_Ici.mpr (le_of_lt hz)) hθ
      rw [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, neg_zero,
        Real.rpow_zero, mul_one] at hh
      calc (f z θ) ^ 2 = 1 * (f z θ) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
        _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hh
    have hslice := hC₀ α f 0 hα hα1 hO hmem4 (by norm_num) z hz
    have hslice' : (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        ≤ C₀ * Work.Spaces.HkSq α 4 f := by simpa using hslice
    have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hz hsqint (haesm z hz)
    refine hFK.trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hslice') (by norm_num)
  have hcont : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) :=
    fk_cont_FK hO hmem4
  have hAnn : 0 ≤ 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := by positivity
  have hbound := hC₁ (g := fun z => Work.Construction.FK f z) hα hα1 hO hmem6 hmem7
    hcont hAnn hgA a b ρ hab hρ
  -- the arithmetic
  have hsqrt : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
  have hAeq : 4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)
      = 4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hC₀pos.le, hsqrt]
    ring
  have hAM : 4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f ≤ 4 * Real.sqrt C₀ * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hAM' : C₁ * (4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f)
      ≤ C₁ * (4 * Real.sqrt C₀ * M) := mul_le_mul_of_nonneg_left hAM hC₁pos.le
  have hMS : M * Work.Spaces.HkSq α 6 f
      ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : M ≤ 1 + M := by linarith
    have h2 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    have h3 : (1 : ℝ) + M ≤ (1 + M) * (1 + M) := by nlinarith [hMnn, sq_nonneg M]
    calc M * Work.Spaces.HkSq α 6 f
        ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul h1 h2 hsq6nn (by linarith)
      _ ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right h3 (by linarith)
  have hgoal : (C₁ * (4 * Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)))
        * Work.Spaces.HkSq α 6 f
      ≤ (C₁ * (4 * Real.sqrt C₀) + 1) * (1 + M) * (1 + M)
        * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [hAeq]
    calc (C₁ * (4 * Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f)) * Work.Spaces.HkSq α 6 f
        ≤ (C₁ * (4 * Real.sqrt C₀ * M)) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_right hAM' hsq6nn
      _ = C₁ * (4 * Real.sqrt C₀) * (M * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ C₁ * (4 * Real.sqrt C₀)
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left hMS (by positivity)
      _ ≤ (C₁ * (4 * Real.sqrt C₀) + 1)
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (C₁ * (4 * Real.sqrt C₀) + 1) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  exact hbound.trans hgoal


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowZSliceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- The `η`-weighted radial half of the level-`m` slice sum, `m ≤ 2`, bounded uniformly in `z > 0`
by `9 · HkSq α 4 f`.  Route: `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded`
at `k = 4` applied to the slots `(j,i) = (i,0)` gives `∫_θ sin(2θ)^{-η}(D_z^if z θ)² ≤ 3·HkSq α 4 f`
(`i ≤ 2`, so `i + 0 + 1 ≤ 4`), and
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable` gives the
integrability needed to split the integral of the `Finset.range (m+1)`-sum with
`MeasureTheory.integral_finsetSum`; there are `m + 1 ≤ 3` summands, which are nonnegative. -/
theorem lowZSliceLe {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      ≤ 9 * Work.Spaces.HkSq α 4 f := by
  -- each summand `θ ↦ sin(2θ)^{-η}(D_z^i f z θ)²` (`i ≤ m ≤ 2`) is integrable on `Iθ`
  have hint : ∀ i ∈ Finset.range (m + 1), MeasureTheory.Integrable
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro i hi
    have hi2 : i ≤ 2 := by
      have := Finset.mem_range.mp hi
      omega
    exact fkSliceSup_slice_integrable hα hF hmem (j := i) (i := 0) (by omega) hz
  -- and each of them is bounded by `3 · HkSq α 4 f` (the graded slice bound at `k = 4`)
  have hper : ∀ i ∈ Finset.range (m + 1),
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed i 0 f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro i hi
    have hi2 : i ≤ 2 := by
      have := Finset.mem_range.mp hi
      omega
    exact fkSliceSup_sliceSupGraded hα hF hmem i 0 (by omega) z hz
  have hsplit : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      = ∑ i ∈ Finset.range (m + 1),
          ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed i 0 f z θ) ^ 2 :=
    MeasureTheory.integral_finsetSum (Finset.range (m + 1)) hint
  rw [hsplit]
  have h2 : (∑ i ∈ Finset.range (m + 1),
        ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      ≤ ∑ _i ∈ Finset.range (m + 1), (3 * Work.Spaces.HkSq α 4 f) :=
    Finset.sum_le_sum hper
  have h3 : (∑ _i ∈ Finset.range (m + 1), (3 * Work.Spaces.HkSq α 4 f))
      ≤ 9 * Work.Spaces.HkSq α 4 f := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard : ((m + 1 : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (by omega : m + 1 ≤ 3)
    nlinarith [Work.Spaces.HkSq_nonneg α 4 f]
  linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.XiOpsplit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux (nzs_pz_PhiTil nzs_pth_PhiTil L12add)

theorem XiOpsplit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.VocabO2.PhiTs α Φs z θ + Work.Construction.PhiTil α f Ef z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Uop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ) := by
  -- ## the analytic inputs about `L₁₂`
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hadm.reg.2
  obtain ⟨hadd, hdiffl, hdiffF⟩ := L12add hα hα1 hso hmem4
  have hdiffFs : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ
      (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z :=
    fun z hz => Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz
  -- ## the value split
  have hsplit : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.VocabO2.PhiTs α Φs z θ + Work.Construction.PhiTil α f Ef z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hadd z hz.le]
    ring
  -- ## the `∂_z`-split
  have hpz_all : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α f Ef) z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq.2
    have hdΦs : DifferentiableAt ℝ (fun z' => Φs z' θ) z :=
      (hΦs.hasDerivAt_slice hθ hz).differentiableAt
    have hdEf : DifferentiableAt ℝ (fun z' => Ef z' θ) z :=
      (hEf.hasDerivAt_slice hθ hz).differentiableAt
    have hpzP : Work.Spaces.pz (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.Spaces.pz Φs z θ + Work.Spaces.pz Ef z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_diff hdΦs hdEf
    have hder : deriv (fun z' => Work.Construction.L12
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z') z
        = deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
          + deriv (fun z' => Work.Construction.L12 f z') z := by
      have hev : (fun z' => Work.Construction.L12
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z') =ᶠ[𝓝 z]
          (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z'
            + Work.Construction.L12 f z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact hadd z' hz'.le
      rw [hev.deriv_eq]
      exact deriv_add (hdiffFs z hz) (hdiffl z hz)
    rw [nzs_pz_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ (hdΦs.add hdEf) (hdiffF z hz),
      nzs_pz_PhiTil α (Work.Construction.Fstar α) Φs z θ hdΦs (hdiffFs z hz),
      nzs_pz_PhiTil α f Ef z θ hdEf (hdiffl z hz),
      hpzP, hder]
    ring
  -- ## the `∂_θ`-split
  have hpth_all : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Spaces.pth (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α f Ef) z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq.2
    have hdθ : ∀ {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
        DifferentiableAt ℝ (fun θ' => g z θ') θ :=
      fun hg => (((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ))
    have hpthP : Work.Spaces.pth (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.Spaces.pth Φs z θ + Work.Spaces.pth Ef z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_diff (hdθ hΦs) (hdθ hEf)
    rw [nzs_pth_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ ((hdθ hΦs).add (hdθ hEf)),
      nzs_pth_PhiTil α (Work.Construction.Fstar α) Φs z θ (hdθ hΦs),
      nzs_pth_PhiTil α f Ef z θ (hdθ hEf),
      hpthP, hadd z hz.le]
    ring
  refine ⟨hsplit, ?_, ?_, ?_⟩
  · -- ## `ℛ`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpz := hpz_all z θ hq
    have hpth := hpth_all z θ hq
    simp only [Work.Construction.Rop]
    rw [hval, hpz, hpth]
    ring
  · -- ## `𝒰/sin 2θ`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpz := hpz_all z θ hq
    simp only [Work.Construction.Uop]
    rw [hval, hpz]
    ring
  · -- ## `𝒱`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpth := hpth_all z θ hq
    simp only [Work.Construction.Vop]
    rw [hval, hpth]
    ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.Pieces.ang_moment_sup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

open MeasureTheory

set_option linter.unusedVariables false

/-- **Pointwise (in `z`) bound for the angular moment of a class-`C` datum.**

`Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ` is bounded by `4√3·|g|_{ℋ⁶}` for **every** `z > 0`
(not merely a.e.), as soon as `m ≤ 3` and `α ∈ (0,1]`.

Route.  Weighted angular Cauchy–Schwarz (`FKAbsLeSqrtEta`, constant `4` against the weight
`sin(2θ)^{-η}`) reduces the claim to the *uniform-in-`z`* slice bound
`∫_θ sin(2θ)^{-η}(D_z^m g(z,θ))² ≤ 3·HkSq α 6 g` (`fkSliceSup_sliceSupGraded`, constant `3`,
slots with `i + j + 1 ≤ k`).  Since `m ≤ 3`, the slot `(m,0)` satisfies `m + 1 ≤ 6`, and taking
the square root gives `4·√(3·HkSq α 6 g) = 4√3·Xn6 α g`. -/
theorem ang_moment_sup {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    |Work.Elliptic.Qang g m z| ≤ 4 * Real.sqrt 3 * Work.FTS.StrongGlobal.Xn6 α g := by
  -- `ℋ⁶`-honesty of `g` (the class supplies `ℋ⁷` and `ℋ⁸`)
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  -- integrability of the weighted slice of `D_z^m g` at the given `z > 0`
  have hInt : IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter m g z θ) ^ 2) Work.Spaces.Iθ := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable
      hα hg.reg hmem6 (j := m) (i := 0) (by omega) hz
    simp only [Work.Spaces.mixed_zero_right] at h
    exact h
  -- weighted angular Cauchy–Schwarz (constant `4`)
  have hFK := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
    (Y := fun z θ => Work.Spaces.DzIter m g z θ) hInt
  -- `Qang g m z` is the angular moment of the slice `θ ↦ D_z^m g (z,θ)`
  have hQeq : Work.Elliptic.Qang g m z
      = Work.Construction.FK (fun z θ => Work.Spaces.DzIter m g z θ) z := by
    rw [Work.Elliptic.Qang, Work.Construction.FK, Work.Elliptic.Ktheta_eq_K]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => mul_comm _ _)
  -- the uniform-in-`z` slice bound (constant `3`), at level `6`
  have hslice : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter m g z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 6 g := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded
      hα hg.reg hmem6 m 0 (by omega) z hz
    simpa only [Work.Spaces.mixed_zero_right, Nat.add_zero] using h
  calc |Work.Elliptic.Qang g m z|
      = |Work.Construction.FK (fun z θ => Work.Spaces.DzIter m g z θ) z| := by rw [hQeq]
    _ ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter m g z θ) ^ 2) := hFK
    _ ≤ 4 * Real.sqrt (3 * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hslice) (by norm_num)
    _ = 4 * Real.sqrt 3 * Work.FTS.StrongGlobal.Xn6 α g := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        simp only [Work.FTS.StrongGlobal.Xn6, Work.Spaces.HkNorm]
        ring

end Work.FTS_EllLimOK.PkgJets.Pieces
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)
open Work.FTS_MuLamOK.Rows

set_option autoImplicit false

/-! ## The row constants -/

/-- The constant of `Rows/Rl0Open`. -/
noncomputable def KMu0 : ℝ := Classical.choose Rl0Open

/-- The constant of `Rows/Rl1Open` at the elliptic/star constants `Ce`, `Cs`. -/
noncomputable def KMu1 (Ce Cs : ℝ) : ℝ := Classical.choose (Rl1Open Ce Cs)

/-- The constant of `Rows/Rl2Open`. -/
noncomputable def KMu2 : ℝ := Classical.choose Rl2Open

theorem KMu0_pos : 0 < KMu0 := (Classical.choose_spec Rl0Open).1

theorem KMu0_pos' : 0 ≤ KMu0 := le_of_lt KMu0_pos

theorem KMu1_pos (Ce Cs : ℝ) : 0 < KMu1 Ce Cs := (Classical.choose_spec (Rl1Open Ce Cs)).1

theorem KMu1_pos' (Ce Cs : ℝ) : 0 ≤ KMu1 Ce Cs := le_of_lt (KMu1_pos Ce Cs)

theorem KMu2_pos : 0 < KMu2 := (Classical.choose_spec Rl2Open).1

theorem KMu2_pos' : 0 ≤ KMu2 := le_of_lt KMu2_pos

theorem KMu0_row : ∀ {α : ℝ} {f : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ KMu0 * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) :=
  fun hα hα1 hso hmem => (Classical.choose_spec Rl0Open).2 hα hα1 hso hmem

theorem KMu1_row (Ce Cs : ℝ) : ∀ {α : ℝ} {f Φs Φg : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce f Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ KMu1 Ce Cs * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) :=
  fun hα hα1 hso hmem hs hell => (Classical.choose_spec (Rl1Open Ce Cs)).2 hα hα1 hso hmem hs hell

theorem KMu2_row : ∀ {α : ℝ} {f : Fn}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ KMu2 * Work.FTS.Nonlin.Xn α f :=
  fun hα hα1 hso hmem => (Classical.choose_spec Rl2Open).2 hα hα1 hso hmem

/-- The combined constant of the μ/λ clause: `max (K₀(1+C₀+C₀²)) (max (K₁(1+C₀+C₀²)) (K₂C₀))`. -/
def KMu (C₀ Ce Cs : ℝ) : ℝ := KRow C₀ KMu0 (KMu1 Ce Cs) KMu2

theorem KMu_pos {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) : 0 < KMu C₀ Ce Cs := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  exact mul_pos KMu0_pos (by nlinarith [sq_nonneg C₀])

/-! ## The clause -/

/-- The `ℋ⁴`-honesty of a `ClassC` profile at level `4` (the fragment of the class used by the
three rows). -/
theorem ClassC_hkMem_four {α : ℝ} {f : Fn} (hf : Work.FTS.ClassC.ClassC α f) :
    Work.Spaces.HkMem α 4 f :=
  Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hf.reg hf.mem

/-- **The μ/λ clause, at a fixed exponent.**  `KMu C₀ Ce Cs` is the combined row constant; the
hypothesis `9·KMu·α ≤ 2` is the smallness of `α` relative to `C₀`, `Ce`, `Cs`. -/
theorem MuLamOK_proved {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    (hsmall : 9 * KMu C₀ Ce Cs * α ≤ 2) :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  refine MuLamOK_of_rowEnvelopes (Φs := Φs) (E := E) hα hα1 KMu0_pos' (KMu1_pos' Ce Cs)
    KMu2_pos' ?_ ?_ ?_ hsmall
  · intro f hf
    exact KMu0_row hα hα1 hf.reg (ClassC_hkMem_four hf)
  · intro f hf
    exact KMu1_row Ce Cs hα hα1 hf.reg (ClassC_hkMem_four hf) hstar.toStarPkgo (hell f hf)
  · intro f hf
    exact KMu2_row hα hα1 hf.reg (ClassC_hkMem_four hf)

/-- **`MuLamOK` is monotone in `C₀`** (in the decreasing direction, which is the useful one):
the clause at the larger size constant `C₀'` gives it at the smaller constant `C₀ ≤ C₀'`, since
the class and the bounds do not depend on `C₀`. -/
theorem MuLamOK_mono_C₀ {α C₀ C₀' : ℝ} {Φs : Fn} {E : Fn → Fn}
    (h : Work.FTS.StrongEps.MuLamOK α C₀' Φs E) (hCC : C₀ ≤ C₀') :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E :=
  fun f hf hX => h f hf (le_trans hX (mul_le_mul_of_nonneg_right hCC (sq_nonneg α)))

/-- **The μ/λ clause, "for `α` small".**  The threshold `min 1 (2/(9·KMu C₀ Ce Cs))` depends on
the constants `C₀`, `Ce`, `Cs` but not on `α`; this is the form in which the clause is consumed
by the assembly at `pExp α ≤ α₂`. -/
theorem MuLamOK_proved_eventually {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn → Fn},
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f)) →
      Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  have hK : 0 < KMu C₀ Ce Cs := KMu_pos hC₀
  refine ⟨min 1 (2 / (9 * KMu C₀ Ce Cs)), lt_min one_pos (by positivity), ?_⟩
  intro α hα hΦs E hstar hell
  have hα1 : α ≤ 1 := le_trans hα.2 (min_le_left _ _)
  have hαc : α ≤ 2 / (9 * KMu C₀ Ce Cs) := le_trans hα.2 (min_le_right _ _)
  refine MuLamOK_proved hα.1 hα1 hC₀ hstar hell ?_
  have h9 : (0 : ℝ) < 9 * KMu C₀ Ce Cs := by positivity
  rw [le_div_iff₀ h9] at hαc
  linarith

/-! ## The clause at the profile exponent `pExp α = 3α` -/

/-- **The μ/λ clause at the profile exponent**, i.e. with `α` replaced by `pExp α = 3α` of
`Work.FTS.Regularity`: this is the instance consumed by the final assembly
(`Final/Defs.Inputs` conjunct (1b), `exists_limH` at `pExp α`).  The threshold is
`min (1/3) (2/(27·KMu C₀ Ce Cs))`, so that both `pExp α ≤ 1` and `9·KMu·(3α) ≤ 2` hold. -/
theorem MuLamOK_proved_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn → Fn},
      Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) f →
        Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce f (E f)) →
      Work.FTS.StrongEps.MuLamOK (Work.FTS.Regularity.pExp α) C₀ Φs E := by
  have hK : 0 < KMu C₀ Ce Cs := KMu_pos hC₀
  refine ⟨min (1 / 3) (2 / (27 * KMu C₀ Ce Cs)),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro α hα hΦs E hstar hell
  have hα0 : 0 < α := hα.1
  have hα3 : α ≤ 1 / 3 := le_trans hα.2 (min_le_left _ _)
  have hαc : α ≤ 2 / (27 * KMu C₀ Ce Cs) := le_trans hα.2 (min_le_right _ _)
  refine MuLamOK_proved (Work.FTS.Regularity.pExp_pos hα0)
    (Work.FTS.Regularity.pExp_le_one hα3) hC₀ hstar hell ?_
  have h27 : (0 : ℝ) < 27 * KMu C₀ Ce Cs := by positivity
  rw [le_div_iff₀ h27] at hαc
  rw [Work.FTS.Regularity.pExp_eq]
  nlinarith [hαc]

end Work.FTS_MuLamOK
end
end
