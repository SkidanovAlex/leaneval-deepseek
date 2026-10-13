/-
Copyright: work module for the Elgindi finite-time singularity project.

# `RX-A1` — the interior `L^∞`–`ℋ⁴` trade-off for a `C⁴` datum

This is the proof of `Work.FTS_RegExport.abs_mixed_le_HkNorm_C4_proved`, the `C⁴` form of
Elgindi's Corollary `SecondDerivativesBounded` (tex 1094):

    |D_z^b D_θ^a f (z,θ)| ≤ 10 / √(γ-1) · |f|_{ℋ⁴}      (a + b ≤ 2, z > 0, 0 < θ < π/2),

for a datum which is only `C⁴` on the *open* quadrant (`ContDiffOn ℝ 4 (uncurry f) Q0`) and
honestly in `ℋ⁴` (`HkMem β 4 f`), with the boundary traces `BdryTraces β 4 f`.

The chain is the one of `Work.FTS.RegPkgGal.Der.mixed_le_ten_sqrt_gam` /
`Work.FTS.StrongEps.SupPort.mixedSup_pt_le_of_smoothOpen`, re-run with every occurrence of the
`C^∞`-on-the-open-quadrant class `SmoothOpen` replaced by the finite-order hypothesis
`ContDiffOn ℝ 4 (Function.uncurry f) Q0`:

1. the angular Hardy inequality `Work.FTS_RegExport.C4.hardyTheta_slice_C1` at the `θ`-slice of
   the slot `D_z^bD_θ^af` (its `θ → 0⁺` boundary value vanishes by `BdryTraces`, and the Hardy
   integrand is `θ`-integrable by
   `Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4`);
2. the identity `sin(2θ)·∂_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f` (`Dth_mixed_eq_C4`) rewrites the
   Hardy integral as the `γ`-weighted angular slice of the next slot;
3. the radial Hardy inequality `Work.FTS.H2.HQ.HardyZQ` on a.e. angular slice, whose a.e.
   integrability is `Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4` and whose decay at
   `z → ∞` is the radial clause of `BdryTraces`;
4. Tonelli for the `ℋ⁴`-integrand (`HkSqSwap_C4`) bounds the resulting double integral by
   `HkSq β 4 f` (`Work.FTS_RegExport.RXA1.mixed_T_le_HkSq_C4`);
5. taking square roots (`Real.sqrt_sq_eq_abs`, `Real.sqrt_mul`) gives the stated constant.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS_RegExport.C4.hardyTheta_slice_C1
import Submission.Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4
import Submission.Work.FTS_RegExport.RXA1.mixed_T_le_HkSq_C4
import Submission.Work.FTS.H2.SupMixedLeH4
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.STMeas
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Finite-order slices of an open-quadrant datum -/

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ_C4 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `z`-slice of a finite-order `ContDiffOn` datum on a product set. -/
private theorem contDiffOn_slice_z_fin_RXA1 {G : ℝ → ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ n (fun z => G z θ) s :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) s)).prodMk
    (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a finite-order `ContDiffOn` datum on a product set. -/
private theorem contDiffOn_slice_θ_fin_RXA1 {G : ℝ → ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ n (fun θ => G z θ) t :=
  (hG.comp ((contDiffOn_const (c := z)).prodMk
    ((contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) t)))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- **The slot and its `θ`-derivative at the finite order `4`.**  For a datum `C⁴` on the open
quadrant and `a + b ≤ 2`, the uncurried slot `D_z^bD_θ^af` is `C²` and its `θ`-derivative is
`C¹` on the open quadrant.  (`a + b + 2 ≤ 4` is exactly the order consumed.) -/
private theorem contDiffOn_mixed_C4 {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {b a : ℕ}
    (hab : a + b ≤ 2) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed b a f)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed b a f)))
        Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (2 + b + a) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by exact_mod_cast (by omega : 2 + b + a ≤ 4))
  have h2 : ContDiffOn ℝ (2 + b) (Function.uncurry (Work.Spaces.DthIter a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 a (2 + b) h1
  have h3 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 b 2 h2
  exact ⟨h3, Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin
    Work.FTS.EllipticEst.isOpen_Q0 h3⟩

/-- **The radial slice of the next slot.**  For a datum `C⁴` on the open quadrant and
`a + b ≤ 2`, the `z`-slice `z ↦ D_z^bD_θ^{a+1}f (z,σ)` at an interior angle is `C¹` on
`(0,∞)` — the regularity needed by the radial Hardy inequality. -/
private theorem contDiffOn_slice_succ_C4 {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {b a : ℕ}
    (hab : a + b ≤ 2) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ 1 (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ (1 + b + (a + 1)) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by exact_mod_cast (by omega : 1 + b + (a + 1) ≤ 4))
  have h2 : ContDiffOn ℝ (1 + b) (Function.uncurry (Work.Spaces.DthIter (a + 1) f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 (a + 1) (1 + b) h1
  have h3 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed b (a + 1) f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 b 1 h2
  exact contDiffOn_slice_z_fin_RXA1 h3 hσ

/-! ## The target -/

theorem abs_mixed_le_HkNorm_C4_proved {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {f : Work.FTS.Galerkin.Fn}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) *
      Work.Spaces.HkNorm β 4 f := by
  have hγ1 : 0 < Work.Spaces.gam β - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  -- finite-order regularity of the slot and of its `θ`-derivative on the open quadrant
  obtain ⟨hg2, hpg1⟩ := contDiffOn_mixed_C4 h4 hab
  have hzI : z ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hz
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ'⟩
  -- the two `θ`-slices required by the `C¹` angular Hardy inequality
  have hslice : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.mixed b a f z θ')
      (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_slice_θ_fin_RXA1 hg2 hzI).of_le (by norm_num)
  have hpth : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.pth (Work.Spaces.mixed b a f) z θ')
      (Set.Ioo 0 (π / 2)) := contDiffOn_slice_θ_fin_RXA1 hpg1 hzI
  -- the vanishing of the slice at `θ = 0⁺`, from the angular clause of `BdryTraces`
  have h0 : Filter.Tendsto (fun θ' => Work.Spaces.mixed b a f z θ')
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces β hβ
      ((htr a b (by omega)).2 z hzI |>.1)
  -- `θ`-integrability of the Hardy integrand, at the fixed `z`
  have hAint : MeasureTheory.IntegrableOn (fun σ =>
      (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)) Work.Spaces.Iθ :=
    integrableOn_pth_mixed_sq_sin_C4 (α := β) hβ hβ1 h4 hmem b a hab hz
  -- the angular Hardy inequality at `(z,θ)`
  have hHT := Work.FTS_RegExport.C4.hardyTheta_slice_C1 (α := β) hβ hβ1
    (g := Work.Spaces.mixed b a f) (z := z) hz hslice hpth h0 hAint θ hθI
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β) with hAdef
  set B : ℝ → ℝ := fun σ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 with hBdef
  set T : ℝ := ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * B σ
    with hTdef
  -- the Hardy integrand is the `γ`-weighted square of the next slot, a.e. in `σ`
  have hAeq : A = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    rw [hAdef]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    rw [Work.FTS.H2.pth_sq_mul_sin_eq β hβ hβ1 (Work.Spaces.mixed b a f) z σ
      ⟨hσ.1.le, hσ.2.le⟩]
    rw [Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ]
    ring
  -- the radial Hardy inequality, a.e. in `σ`
  have hHardyZ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * B σ := by
    filter_upwards [Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 hβ h4 hmem
        (b + 1) (a + 1) (by omega) (by omega), Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hintσ hσ
    have hint' : MeasureTheory.IntegrableOn
        (fun s => (s * deriv (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) s) ^ 2
          * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz :=
      hintσ.congr (Filter.Eventually.of_forall fun s => by rfl)
    have hcd : ContDiffOn ℝ 1 (fun z' => Work.Spaces.mixed b (a + 1) f z' σ)
        (Set.Ioi 0) := contDiffOn_slice_succ_C4 h4 hab hσ
    have hdec : Filter.Tendsto (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) Filter.atTop
        (nhds 0) :=
      Work.FTS.H2.tendsto_atTop_zero_of_traces ((htr (a + 1) b (by omega)).1 σ hσ |>.2)
    have hZQ := Work.FTS.H2.HQ.HardyZQ (fun z' => Work.Spaces.mixed b (a + 1) f z' σ)
      hcd hdec hint' z (Set.mem_Ioi.mpr hz)
    rw [hBdef]
    exact mul_le_mul_of_nonneg_left hZQ
      (Real.rpow_nonneg (sin_two_nonneg_Iθ_C4 ⟨hσ.1.le, hσ.2.le⟩) _)
  -- Tonelli for the `ℋ⁴`-integrand: the radial-slice energy of the next slot is bounded by
  -- `HkSq β 4 f`
  have hTint : MeasureTheory.IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * B σ) Work.Spaces.Iθ :=
    (Work.FTS_RegExport.RXA1.mixed_T_le_HkSq_C4 (α := β) hβ h4 hmem b a hab).1
  have hTle : T ≤ Work.Spaces.HkSq β 4 f :=
    (Work.FTS_RegExport.RXA1.mixed_T_le_HkSq_C4 (α := β) hβ h4 hmem b a hab).2
  have hmono : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
      * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) ≤ T := by
    rw [hTdef]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hTint ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun σ hσ => ?_)
      exact mul_nonneg
        (Real.rpow_nonneg (sin_two_nonneg_Iθ_C4 hσ) _) (sq_nonneg _)
    · exact hHardyZ
  have hc : (0 : ℝ) ≤ 100 / (Work.Spaces.gam β - 1) := div_nonneg (by norm_num) hγ1.le
  have h1 : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (100 / (Work.Spaces.gam β - 1)) * Work.Spaces.HkSq β 4 f := by
    calc (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (100 / (Work.Spaces.gam β - 1)) * A := hHT
      _ ≤ (100 / (Work.Spaces.gam β - 1)) * T :=
          mul_le_mul_of_nonneg_left (hAeq.trans_le hmono) hc
      _ ≤ (100 / (Work.Spaces.gam β - 1)) * Work.Spaces.HkSq β 4 f :=
          mul_le_mul_of_nonneg_left hTle hc
  have h2 : |Work.Spaces.mixed b a f z θ| ≤ Real.sqrt ((100 / (Work.Spaces.gam β - 1))
      * Work.Spaces.HkSq β 4 f) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt ((100 / (Work.Spaces.gam β - 1)) * Work.Spaces.HkSq β 4 f)
      = 10 / Real.sqrt (Work.Spaces.gam β - 1) * Work.Spaces.HkNorm β 4 f := by
    rw [Real.sqrt_mul hc]
    simp only [Work.Spaces.HkNorm]
    congr 1
    have h10 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h10]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  exact le_trans h2 (le_of_eq h3)

end Work.FTS_RegExport.RXA1
