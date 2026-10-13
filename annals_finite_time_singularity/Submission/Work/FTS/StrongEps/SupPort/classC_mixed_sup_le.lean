/-
Copyright: work module for the Elgindi finite-time singularity project.

# `classC_mixed_sup_le` — the interior `L^∞`–`ℋ⁴` trade-off on the class `ClassC`

Elgindi's Corollary `SecondDerivativesBounded` (tex 1094) bounds every mixed derivative
`D_z^b D_θ^a f` of order `a + b ≤ 2` pointwise inside the quadrant by

  `10 / √(γ-1) · |f|_{ℋ⁴}`.

The existing statements of that trade-off in the tree are stated for classes that constrain
`f` on a *neighbourhood* of the quadrant: `Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ`
asks `Work.FTS.Nonlin.RegQ α 4 f = SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`, and
`SmoothQuad` requires smoothness of `f` on the strip `(-1,∞) × (0,π/2)`, i.e. **across**
`z = 0`.  The class `Work.FTS.ClassC.ClassC` of the elliptic solution operator constrains
`f` only on the *open* quadrant (`SmoothOpen f`), together with the honesty `HkMem α 7 f`
and the boundary traces `BdryTraces α 6 f`.  Since the conclusion of the corollary is a
pointwise statement at points `(z,θ)` with `z > 0`, `0 < θ < π/2`, it is the open-quadrant
statement that is needed here.

This module supplies it, by re-running the proof of `abs_mixed_le_HkNorm_RegQ` in the open
class:

* `mixedSup_Dth_eq`: the commutation identity `D_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1} f` on the
  open quadrant, which turns the angular Hardy integrand of `D_z^bD_θ^a f` into the mixed
  slot `D_z^bD_θ^{a+1}f` (from `Work.Blocks.pth_DzIter_eqOn_Q0` — `∂_θ` commutes with the
  radial iterates — and `sda_DzIter_const_mul_th`);
* `mixedSup_pt_le_of_smoothOpen`: the chain

  `(D_z^bD_θ^a f(z,θ))²
     ≤ (100/(γ-1)) ∫_θ (∂_θD_z^bD_θ^a f)² σ^{2-γ}`      (angular Hardy, `HardyThetaOpen`)
   `= (100/(γ-1)) ∫_θ σ^{-γ} (D_z^bD_θ^{a+1}f)²`
   `≤ (100/(γ-1)) ∫_θ σ^{-γ} ∫_z (D_z^{b+1}D_θ^{a+1}f)² w²`  (radial Hardy, `HardyZQ`)
   `≤ (100/(γ-1)) |f|²_{ℋ⁴}`,

  the last step being Tonelli for the `ℋ⁴`-integrand (`sda_HkSqSwap_open`); the four
  ingredients are the sibling lemmas `HardyThetaOpen`, `integrableOn_pth_mixed_sq_sin`
  (integrability of the angular Hardy integrand), `ae_integrableOn_mixed_sq_w` (the a.e.
  radial-slice integrability needed by `HardyZQ`) and `mixed_T_le_HkSq` (the angular
  integral of the radial-slice energy, and its `ℋ⁴`-bound);
* `classC_mixed_sup_le`: the target, reading the open-class data off the fields of
  `ClassC` (`reg`, `mem` at level `7` ⟹ level `4`, and `tr` at level `6` ⟹ level `4`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.ae_integrableOn_mixed_sq_w
import Submission.Work.FTS.StrongEps.SupPort.integrableOn_pth_mixed_sq_sin
import Submission.Work.FTS.StrongEps.SupPort.mixed_T_le_HkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.SupPort

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The commutation identity -/

/-- **`D_θ` of a mixed slot is the next mixed slot**, on the open quadrant, for a datum of
class `C^∞` on the open quadrant: `D_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1}f`.

On the open quadrant `∂_θ` commutes with the radial iterates `D_z^b`
(`Work.Blocks.pth_DzIter_eqOn_Q0`), and an angular multiplier passes through `D_z^b`
(`sda_DzIter_const_mul_th`); combining the two with `D_θ g = sin(2θ)·∂_θg` gives the
identity. -/
theorem mixedSup_Dth_eq {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ.1, hθ.2⟩
  have hid : Work.Spaces.pth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)) z θ
      = Work.Spaces.DzIter b (Work.Spaces.pth (Work.Spaces.DthIter a f)) z θ :=
    Work.Blocks.pth_DzIter_eqOn_Q0 (hF.DthIter a) b hQ
  have hcm := Work.FTS.TransportS.SupDzAux.sda_DzIter_const_mul_th (fun θ => Real.sin (2 * θ))
      (Work.Spaces.pth (Work.Spaces.DthIter a f)) b z θ
  show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)) z θ = _
  rw [hid, ← hcm]
  rfl

/-! ## The pointwise bound in the open class -/

/-- **The interior `L^∞`–`ℋ⁴` trade-off for data smooth on the open quadrant.**  For `f` of
class `C^∞` on the open quadrant, honestly in `ℋ⁴`, with the `θ`-limits and the decay at
`z → ∞` of `BdryTraces α 4 f`, every mixed slot `D_z^b D_θ^a f` of order `a + b ≤ 2` is
bounded at each point of the open quadrant by `10/√(γ-1)·|f|_{ℋ⁴}`.

This is the open-class form of `Work.FTS.RegPkgGal.Der.mixed_le_ten_sqrt_gam`; the only
difference is that `SmoothQuad` (smoothness on `(-1,∞) × (0,π/2)`) is weakened to
`SmoothOpen` (smoothness on `(0,∞) × (0,π/2)`), which is what the class `ClassC` supplies. -/
theorem mixedSup_pt_le_of_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 f) (b a : ℕ) (hab : a + b ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.Spaces.HkNorm α 4 f := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  -- the limit of the `θ`-slice at `0⁺`, from the angular clause of `BdryTraces`
  have h0 : Filter.Tendsto (fun θ' => Work.Spaces.mixed b a f z θ')
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces α hα
      ((hbd a b (by omega)).2 z (Set.mem_Ioi.mpr hz) |>.1)
  -- integrability of the angular Hardy integrand
  have hAint := integrableOn_pth_mixed_sq_sin hα hα1 hF hmem b a hab hz
  -- the angular Hardy inequality at the point `(z,θ)`
  have hHT := HardyThetaOpen α hα hα1 (Work.Spaces.mixed b a f) z (hF.mixed b a) hz h0 hAint
    θ ⟨hθ0, hθ1⟩
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  set B : ℝ → ℝ := fun σ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 with hBdef
  set T : ℝ := ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ
    with hTdef
  -- the angular Hardy integrand is the weighted square of the next mixed slot, a.e. in `σ`
  have hAeq : A = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    rw [hAdef]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (Work.Spaces.mixed b a f) z σ
      ⟨hσ.1.le, hσ.2.le⟩]
    rw [mixedSup_Dth_eq hF b a hz hσ]
    ring
  -- the radial Hardy inequality, a.e. in `σ`
  have hHardyZ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [ae_integrableOn_mixed_sq_w hα hF hmem (b + 1) (a + 1) (by omega) (by omega),
      Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hintσ hσ
    have hint' : MeasureTheory.IntegrableOn
        (fun s => (s * deriv (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) s) ^ 2
          * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz :=
      hintσ.congr (Filter.Eventually.of_forall fun s => by rfl)
    have hcd : ContDiffOn ℝ 1 (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) (Set.Ioi 0) :=
      ((hF.mixed b (a + 1)).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
    have hdec : Filter.Tendsto (fun z' => Work.Spaces.mixed b (a + 1) f z' σ) Filter.atTop
        (nhds 0) :=
      Work.FTS.H2.tendsto_atTop_zero_of_traces ((hbd (a + 1) b (by omega)).1 σ hσ |>.2)
    have hZQ := Work.FTS.H2.HQ.HardyZQ (fun z' => Work.Spaces.mixed b (a + 1) f z' σ)
      hcd hdec hint' z (Set.mem_Ioi.mpr hz)
    rw [hBdef]
    exact mul_le_mul_of_nonneg_left hZQ
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ ⟨hσ.1.le, hσ.2.le⟩) _)
  obtain ⟨hTint, hTle⟩ := mixed_T_le_HkSq hα hF hmem b a hab
  have hmono : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) ≤ T := by
    rw [hTdef]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hTint ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun σ hσ => ?_)
      exact mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_Iθ hσ) _) (sq_nonneg _)
    · exact hHardyZ
  have hc : (0 : ℝ) ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  have h1 : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
    calc (Work.Spaces.mixed b a f z θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) * A := hHT
      _ ≤ (100 / (Work.Spaces.gam α - 1)) * T :=
          mul_le_mul_of_nonneg_left (hAeq.trans_le hmono) hc
      _ ≤ (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
          mul_le_mul_of_nonneg_left hTle hc
  have h2 : |Work.Spaces.mixed b a f z θ| ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1))
      * Work.Spaces.HkSq α 4 f) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f)
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul hc]
    simp only [Work.Spaces.HkNorm]
    congr 1
    have h4 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h4]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  exact le_trans h2 (le_of_eq h3)

/-! ## The target -/

theorem classC_mixed_sup_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.ClassC.ClassC α f) (b a : ℕ) (hab : a + b ≤ 2)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.mixed b a f z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hF 4 (by norm_num) hf.mem
  have hbd4 : Work.FTS.Nonlin.BdryTraces α 4 f :=
    fun a b hab' => hf.tr a b (le_trans hab' (by norm_num))
  exact mixedSup_pt_le_of_smoothOpen hα hα1 hF hmem4 hbd4 b a hab hz hθ.1 hθ.2

end Work.FTS.StrongEps.SupPort
