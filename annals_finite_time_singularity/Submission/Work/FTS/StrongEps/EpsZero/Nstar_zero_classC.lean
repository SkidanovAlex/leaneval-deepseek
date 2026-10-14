import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.A1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary closures -/

/-- `F_*` depends only on the pointwise values (the Bochner integral is total). -/
theorem Fstar_congr_pt {f h : ℝ → ℝ → ℝ} (hp : ∀ z θ, f z θ = h z θ) (z : ℝ) :
    Work.Elliptic.Fstar f z = Work.Elliptic.Fstar h z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [hp])

/-- `(x+y)² ≤ 2x² + 2y²`. -/
theorem sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : 2 * a ^ 2 + 2 * b ^ 2 - (a + b) ^ 2 = (a - b) ^ 2 := by ring
  linarith [h, sq_nonneg (a - b)]

/-- The angular slice `θ ↦ g z θ · sinθcos²θ` is integrable for every `z > 0` (`HkMem α 0` plus
open-quadrant continuity). -/
theorem slice_sinCos2_integrable {α : ℝ} {g : Fn} (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hreg.continuousOn hmem hz

/-- The `ℋ⁰`-membership obtained by descending `ClassC.mem`. -/
theorem classC_hkMem_zero {α : ℝ} {g : Fn} (h : ClassC α g) : Work.Spaces.HkMem α 0 g :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 7) (by norm_num)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp h.reg) h.mem

/-- The `ℋ⁴`-membership obtained by descending `ClassC.mem`. -/
theorem classC_hkMem_four {α : ℝ} {g : Fn} (h : ClassC α g) : Work.Spaces.HkMem α 4 g :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 4) (l := 7) (by norm_num)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp h.reg) h.mem

/-- The angular weight `sin(2θ)^{1-γ}` is nonnegative on `(0,π/2)`. -/
theorem sin_rpow_nonneg {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
  Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) _

/-- `(0,π/2)` is an open set. -/
theorem eventually_lt_pi_two : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < π / 2 :=
  (eventually_lt_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)).filter_mono
    nhdsWithin_le_nhds

/-- `0 < θ` eventually for `θ → (π/2)⁻`. -/
theorem eventually_gt_zero : ∀ᶠ θ in 𝓝[<] (π / 2), 0 < θ :=
  (eventually_gt_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)).filter_mono
    nhdsWithin_le_nhds

/-! ## `BdryTraces` is linear -/

/-- **`BdryTraces` is closed under addition** on open-quadrant smooth data.  On the open quadrant
the mixed operators are additive (`SmoothOpen.mixed_add`), and every point queried by
`BdryTraces` (`θ ∈ (0,π/2)` with `z → 0⁺` or `z → ∞`, and `z > 0` with `θ → 0⁺` or `θ → (π/2)⁻`)
lies in the open quadrant.  The square is controlled by `(x+y)² ≤ 2x² + 2y²`. -/
theorem bdryTraces_add {α : ℝ} {k : ℕ} {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf' : Work.FTS.Nonlin.BdryTraces α k f) (hg' : Work.FTS.Nonlin.BdryTraces α k g) :
    Work.FTS.Nonlin.BdryTraces α k (f + g) := by
  intro a b hab
  have hmix : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (f + g) z θ
        = Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ :=
    fun z θ hz h1 h2 => Work.FTS.EllipticEst.SmoothOpen.mixed_add hf hg b a z θ hz h1 h2
  obtain ⟨hfz, hfth⟩ := hf' a b hab
  obtain ⟨hgz, hgth⟩ := hg' a b hab
  -- the two pointwise dominations
  have keyR : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z : ℝ, 0 < z →
      z * (Work.Spaces.mixed b a (f + g) z θ * Work.Spaces.w z) ^ 2
        ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
          + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2) := by
    intro θ hθ z hz
    rw [hmix z θ hz hθ.1 hθ.2]
    have hexp : (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) * Work.Spaces.w z
        = Work.Spaces.mixed b a f z θ * Work.Spaces.w z
          + Work.Spaces.mixed b a g z θ * Work.Spaces.w z := by ring
    rw [hexp]
    nlinarith [sq_add_le_two (Work.Spaces.mixed b a f z θ * Work.Spaces.w z)
      (Work.Spaces.mixed b a g z θ * Work.Spaces.w z), hz]
  have keyA : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a f z θ) ^ 2)
          + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z hz θ hθ0 hθ1
    rw [hmix z θ hz hθ0 hθ1]
    have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sin_rpow_nonneg ⟨hθ0, hθ1⟩
    have hkey := mul_le_mul_of_nonneg_left
      (sq_add_le_two (Work.Spaces.mixed b a f z θ) (Work.Spaces.mixed b a g z θ)) hsin
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed b a f z θ) ^ 2
              + 2 * (Work.Spaces.mixed b a g z θ) ^ 2) := hkey
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a f z θ) ^ 2)
          + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · intro θ hθ
    refine ⟨?_, ?_⟩
    · have hnn : ∀ᶠ z in 𝓝[>] (0 : ℝ),
          0 ≤ (fun z => z * (Work.Spaces.mixed b a (f + g) z θ * Work.Spaces.w z) ^ 2) z := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      have hle : ∀ᶠ z in 𝓝[>] (0 : ℝ),
          (fun z => z * (Work.Spaces.mixed b a (f + g) z θ * Work.Spaces.w z) ^ 2) z
            ≤ (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
                + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) z := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact keyR θ hθ z hz
      have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ
              * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2))
          (𝓝[>] 0) (𝓝 0) := by
        simpa using ((hfz θ hθ).1.const_mul 2).add ((hgz θ hθ).1.const_mul 2)
      exact squeeze_zero' hnn hle hlim
    · have hnn : ∀ᶠ z in atTop,
          0 ≤ (fun z => z * (Work.Spaces.mixed b a (f + g) z θ * Work.Spaces.w z) ^ 2) z := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact mul_nonneg (le_of_lt hz) (sq_nonneg _)
      have hle : ∀ᶠ z in atTop,
          (fun z => z * (Work.Spaces.mixed b a (f + g) z θ * Work.Spaces.w z) ^ 2) z
            ≤ (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
                + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) z := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact keyR θ hθ z hz
      have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ
              * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) atTop (𝓝 0) := by
        simpa using ((hfz θ hθ).2.const_mul 2).add ((hgz θ hθ).2.const_mul 2)
      exact squeeze_zero' hnn hle hlim
  · intro z hz
    refine ⟨?_, ?_⟩
    · have hnn : ∀ᶠ θ' in 𝓝[>] (0 : ℝ),
          0 ≤ (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (f + g) z θ') ^ 2) θ' := by
        filter_upwards [self_mem_nhdsWithin, eventually_lt_pi_two] with θ' h0 h1
        exact mul_nonneg (sin_rpow_nonneg ⟨h0, h1⟩) (sq_nonneg _)
      have hle : ∀ᶠ θ' in 𝓝[>] (0 : ℝ),
          (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (f + g) z θ') ^ 2) θ'
            ≤ (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                  * (Work.Spaces.mixed b a f z θ') ^ 2)
                + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                  * (Work.Spaces.mixed b a g z θ') ^ 2)) θ' := by
        filter_upwards [self_mem_nhdsWithin, eventually_lt_pi_two] with θ' h0 h1
        exact keyA z hz θ' h0 h1
      have hlim : Tendsto (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ') ^ 2)
            + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ') ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        simpa using ((hfth z hz).1.const_mul 2).add ((hgth z hz).1.const_mul 2)
      exact squeeze_zero' hnn hle hlim
    · have hnn : ∀ᶠ θ' in 𝓝[<] (π / 2),
          0 ≤ (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (f + g) z θ') ^ 2) θ' := by
        filter_upwards [eventually_gt_zero, self_mem_nhdsWithin] with θ' h0 h1
        exact mul_nonneg (sin_rpow_nonneg ⟨h0, h1⟩) (sq_nonneg _)
      have hle : ∀ᶠ θ' in 𝓝[<] (π / 2),
          (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (f + g) z θ') ^ 2) θ'
            ≤ (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                  * (Work.Spaces.mixed b a f z θ') ^ 2)
                + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                  * (Work.Spaces.mixed b a g z θ') ^ 2)) θ' := by
        filter_upwards [eventually_gt_zero, self_mem_nhdsWithin] with θ' h0 h1
        exact keyA z hz θ' h0 h1
      have hlim : Tendsto (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ') ^ 2)
            + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ') ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
        simpa using ((hfth z hz).2.const_mul 2).add ((hgth z hz).2.const_mul 2)
      exact squeeze_zero' hnn hle hlim

/-- **`BdryTraces` is closed under scalar multiplication.** -/
theorem bdryTraces_smul {α : ℝ} {k : ℕ} {f : Fn}
    (hf' : Work.FTS.Nonlin.BdryTraces α k f) (c : ℝ) :
    Work.FTS.Nonlin.BdryTraces α k (c • f) := by
  intro a b hab
  have hcf : (c • f) = fun z θ => c * f z θ := by funext z θ; simp
  have hmix : ∀ z θ, Work.Spaces.mixed b a (c • f) z θ
      = c * Work.Spaces.mixed b a f z θ := by
    intro z θ
    rw [hcf]
    exact congr_fun (congr_fun
      (Work.FTS.Nonlinear.Pieces.RowsN0Aux.mixed_const_mul b a c f) z) θ
  have heqz : ∀ θ z : ℝ,
      z * (Work.Spaces.mixed b a (c • f) z θ * Work.Spaces.w z) ^ 2
        = c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) := by
    intro θ z; rw [hmix]; ring
  have heqθ : ∀ z θ : ℝ,
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (c • f) z θ) ^ 2
        = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    intro z θ; rw [hmix]; ring
  obtain ⟨hfz, hfth⟩ := hf' a b hab
  refine ⟨?_, ?_⟩
  · intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [show (fun z => z * (Work.Spaces.mixed b a (c • f) z θ * Work.Spaces.w z) ^ 2)
          = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) from
        funext (heqz θ)]
      simpa using (hfz θ hθ).1.const_mul (c ^ 2)
    · rw [show (fun z => z * (Work.Spaces.mixed b a (c • f) z θ * Work.Spaces.w z) ^ 2)
          = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) from
        funext (heqz θ)]
      simpa using (hfz θ hθ).2.const_mul (c ^ 2)
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [show (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (c • f) z θ) ^ 2)
          = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2) from funext (heqθ z)]
      simpa using (hfth z hz).1.const_mul (c ^ 2)
    · rw [show (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (c • f) z θ) ^ 2)
          = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2) from funext (heqθ z)]
      simpa using (hfth z hz).2.const_mul (c ^ 2)

/-! ## `ThetaTraces` is linear (lead install R6, 2026-10-11) -/

/-- **`ThetaTraces` is closed under addition** on open-quadrant smooth data (the θ-part of
`bdryTraces_add`). -/
theorem thetaTraces_add {α : ℝ} {k : ℕ} {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf' : Work.FTS.PhiStar.ThetaTraces α k f) (hg' : Work.FTS.PhiStar.ThetaTraces α k g) :
    Work.FTS.PhiStar.ThetaTraces α k (f + g) := by
  intro s hs z hz
  have hz0 : 0 < z := hz
  obtain ⟨hf0, hf1⟩ := hf' s hs z hz
  obtain ⟨hg0, hg1⟩ := hg' s hs z hz
  have keyA : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed s 0 (f + g) z θ) ^ 2
        ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 f z θ) ^ 2)
          + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 g z θ) ^ 2) := by
    intro θ hθ0 hθ1
    have hmix : Work.Spaces.mixed s 0 (f + g) z θ
        = Work.Spaces.mixed s 0 f z θ + Work.Spaces.mixed s 0 g z θ :=
      Work.FTS.EllipticEst.SmoothOpen.mixed_add hf hg s 0 z θ hz0 hθ0 hθ1
    rw [hmix]
    have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sin_rpow_nonneg ⟨hθ0, hθ1⟩
    have hkey := mul_le_mul_of_nonneg_left
      (sq_add_le_two (Work.Spaces.mixed s 0 f z θ) (Work.Spaces.mixed s 0 g z θ)) hsin
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed s 0 f z θ + Work.Spaces.mixed s 0 g z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed s 0 f z θ) ^ 2
              + 2 * (Work.Spaces.mixed s 0 g z θ) ^ 2) := hkey
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 f z θ) ^ 2)
          + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 g z θ) ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · have hnn : ∀ᶠ θ' in 𝓝[>] (0 : ℝ),
        0 ≤ (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 (f + g) z θ') ^ 2) θ' := by
      filter_upwards [self_mem_nhdsWithin, eventually_lt_pi_two] with θ' h0 h1
      exact mul_nonneg (sin_rpow_nonneg ⟨h0, h1⟩) (sq_nonneg _)
    have hle : ∀ᶠ θ' in 𝓝[>] (0 : ℝ),
        (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 (f + g) z θ') ^ 2) θ'
          ≤ (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed s 0 f z θ') ^ 2)
              + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed s 0 g z θ') ^ 2)) θ' := by
      filter_upwards [self_mem_nhdsWithin, eventually_lt_pi_two] with θ' h0 h1
      exact keyA θ' h0 h1
    have hlim : Tendsto (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 f z θ') ^ 2)
          + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 g z θ') ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hf0.const_mul 2).add (hg0.const_mul 2)
    exact squeeze_zero' hnn hle hlim
  · have hnn : ∀ᶠ θ' in 𝓝[<] (π / 2),
        0 ≤ (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 (f + g) z θ') ^ 2) θ' := by
      filter_upwards [eventually_gt_zero, self_mem_nhdsWithin] with θ' h0 h1
      exact mul_nonneg (sin_rpow_nonneg ⟨h0, h1⟩) (sq_nonneg _)
    have hle : ∀ᶠ θ' in 𝓝[<] (π / 2),
        (fun θ' => Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 (f + g) z θ') ^ 2) θ'
          ≤ (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed s 0 f z θ') ^ 2)
              + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
                * (Work.Spaces.mixed s 0 g z θ') ^ 2)) θ' := by
      filter_upwards [eventually_gt_zero, self_mem_nhdsWithin] with θ' h0 h1
      exact keyA θ' h0 h1
    have hlim : Tendsto (fun θ' => 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 f z θ') ^ 2)
          + 2 * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 g z θ') ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      simpa using (hf1.const_mul 2).add (hg1.const_mul 2)
    exact squeeze_zero' hnn hle hlim

/-- **`ThetaTraces` is closed under scalar multiplication.** -/
theorem thetaTraces_smul {α : ℝ} {k : ℕ} {f : Fn}
    (hf' : Work.FTS.PhiStar.ThetaTraces α k f) (c : ℝ) :
    Work.FTS.PhiStar.ThetaTraces α k (c • f) := by
  intro s hs z hz
  have hcf : (c • f) = fun z θ => c * f z θ := by funext z θ; simp
  have hmix : ∀ z θ, Work.Spaces.mixed s 0 (c • f) z θ
      = c * Work.Spaces.mixed s 0 f z θ := by
    intro z θ
    rw [hcf]
    exact congr_fun (congr_fun
      (Work.FTS.Nonlinear.Pieces.RowsN0Aux.mixed_const_mul s 0 c f) z) θ
  have heqθ : ∀ θ : ℝ,
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed s 0 (c • f) z θ) ^ 2
        = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed s 0 f z θ) ^ 2) := by
    intro θ; rw [hmix]; ring
  obtain ⟨h0, h1⟩ := hf' s hs z hz
  rw [show (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed s 0 (c • f) z θ) ^ 2)
      = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed s 0 f z θ) ^ 2) from funext heqθ]
  exact ⟨by simpa using h0.const_mul (c ^ 2), by simpa using h1.const_mul (c ^ 2)⟩

/-! ## The two closure theorems -/

/-- **A1(a): `ClassC` is closed under addition.** -/
theorem classC_add {α : ℝ} {g g' : Fn} (h : ClassC α g) (h' : ClassC α g') :
    ClassC α (g + g') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext z θ
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · simp only [normTh, hθ, ↓reduceIte, Pi.add_apply]
    · have h0 : g z θ = 0 := by
        have hthis := congr_fun (congr_fun h.norm z) θ
        rw [normTh_apply_of_not_mem hθ] at hthis
        exact hthis.symm
      have h0' : g' z θ = 0 := by
        have hthis := congr_fun (congr_fun h'.norm z) θ
        rw [normTh_apply_of_not_mem hθ] at hthis
        exact hthis.symm
      simp only [normTh, hθ, ↓reduceIte, Pi.add_apply, h0, h0', add_zero]
  · exact Work.FTS.EllipticEst.smoothOpen_add h.reg h'.reg
  · exact Work.FTS.EllipticEst.HkMem_add_open h.reg h'.reg h.mem h'.mem
  · exact Work.FTS.EllipticEst.HkMem_add_open h.reg h'.reg h.mem8 h'.mem8
  · exact Work.FTS.EllipticEst.HkMem_add_open h.reg h'.reg h.mem10 h'.mem10
  · exact bdryTraces_add h.reg h'.reg h.tr h'.tr
  · exact bdryTraces_add h.reg h'.reg h.tr7 h'.tr7
  · intro m
    refine (contDiffOn_congr ?_).mpr ((h.fsm m).add (h'.fsm m))
    intro z hz
    have hc : Work.Elliptic.Fstar (g + g') z
        = Work.Elliptic.Fstar (fun z θ => g z θ + 1 * g' z θ) z :=
      Fstar_congr_pt (fun z θ => by simp) z
    rw [hc, Work.FTS.EllSol.Fstar_add_mul (c := 1)
      (slice_sinCos2_integrable h.reg (classC_hkMem_zero h) hz)
      (slice_sinCos2_integrable h'.reg (classC_hkMem_zero h') hz)]
    ring
  · intro θ hθ
    have heq : (fun z => (g + g') z θ / z) = fun z => g z θ / z + g' z θ / z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [heq]
    simpa using (h.axis θ hθ).add (h'.axis θ hθ)
  · have hcong : (g + g') = fun z θ => g z θ + g' z θ := by funext z θ; rfl
    rw [hcong, Work.FTS.GalBasis.cc.L12_add_of_HkMem (α := α) h.reg h'.reg
      (classC_hkMem_four h) (classC_hkMem_four h'), h.l12, h'.l12, add_zero]
  · exact thetaTraces_add h.reg h'.reg h.thTr h'.thTr

/-- **A1(b): `ClassC` is closed under scalar multiplication.** -/
theorem classC_smul {α : ℝ} (c : ℝ) {g : Fn} (h : ClassC α g) :
    ClassC α (c • g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext z θ
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · simp only [normTh, hθ, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    · have h0 : g z θ = 0 := by
        have hthis := congr_fun (congr_fun h.norm z) θ
        rw [normTh_apply_of_not_mem hθ] at hthis
        exact hthis.symm
      simp only [normTh, hθ, ↓reduceIte, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
  · exact h.reg.const_mul' c
  · exact Work.FTS.LocData.HkMem_const_mul α 7 c h.mem
  · exact Work.FTS.LocData.HkMem_const_mul α 8 c h.mem8
  · exact Work.FTS.LocData.HkMem_const_mul α 10 c h.mem10
  · exact bdryTraces_smul h.tr c
  · exact bdryTraces_smul h.tr7 c
  · intro m
    refine (contDiffOn_congr ?_).mpr
      ((contDiffOn_const (c := c)).mul (h.fsm m))
    intro z _
    have hc : Work.Elliptic.Fstar (c • g) z
        = Work.Elliptic.Fstar (fun z θ => c * g z θ) z :=
      Fstar_congr_pt (fun z θ => by simp) z
    rw [hc, Work.FTS.EllSol.Fstar_const_mul g c z]
  · intro θ hθ
    have heq : (fun z => (c • g) z θ / z) = fun z => c * (g z θ / z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [heq]
    simpa using (h.axis θ hθ).const_mul c
  · have hcong : (c • g) = fun z θ => c * g z θ := by funext z θ; simp
    rw [hcong, Work.FTS.GalBasis.L12_const_mul c g 0, h.l12, mul_zero]
  · exact thetaTraces_smul h.thTr c

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.rhoC_meas_nonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr




end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsZero

set_option linter.unusedVariables false

/-- **The zero mode of `D_z` on the class `C`.**

For a profile `f` of the class `C` (`SmoothOpen` on the open quadrant, `ℋ⁷`-honest, with the
`BdryTraces` boundary vanishing at level `6`) which vanishes outside the open quadrant, the
`L₁₂` zero mode of `D_z f = z ∂_z f` vanishes:

  `L₁₂(D_z f)(0) = 0`.

Route.  `ClassC` gives `SmoothOpen f` (`ClassC.reg`), `HkMem α 7 f` (`ClassC.mem`) and the
boundary traces `BdryTraces α 6 f` (`ClassC.tr`); `hzero` gives the point values at `z = 0` and
the (identically zero) slices at `θ = 0, π/2`.  Then

* `slice_facts_of_classC` produces the three *radial* slice facts: differentiability of the
  `z`-slices on `(0,∞)`, continuity of the slices on `[0,∞)` (the right limit at `0⁺` is
  `f 0 θ = 0`, from the `(a,b) = (0,0)` boundary trace `z (f w)² → 0`), and decay at `+∞`;
* `pz_prod_integrable_of_smoothOpen` gives the joint integrability of `K(θ)·∂_z f(z,θ)` on
  `(0,∞) × Iθ`, which is the Fubini input (it needs only `HkMem α 1 f`, a downward-monotonicity
  of `HkMem α 7 f`);
* `L12_Dz_zero_of_slices` concludes, by the FTC `∫_0^∞ ∂_z f(s,θ) ds = f(∞,θ) - f(0,θ) = 0`
  for a.e. `θ` and one Fubini swap. -/
theorem L12_Dz_zero_classC {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := by
  obtain ⟨hdiff, hcont0, hdec⟩ := slice_facts_of_classC hC.reg hC.tr hzero
  have hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 := fun θ _ => hzero 0 θ (by simp)
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    pz_prod_integrable_of_smoothOpen hC.reg
      (Work.FTS.IPGen.HkMem_mono_le hC.reg 1 (by norm_num) hC.mem)
  exact L12_Dz_zero_of_slices hdiff hcont0 hdec hvan hint

/-- **The zero mode of `N_*` at the paper's `λ = lamfun μ`, on the class `C`.**

At `λ = lamfun μ` the coefficient of `D_z g` in `N_* μ λ g = -μ g - (μ + λ + μλ)·D_z g`
collapses: `μ + lamfun μ + μ·lamfun μ = -μ`, so that (for `μ ≠ -1`)

  `N_* μ (lamfun μ) f = μ·(D_z f - f)`.

Hence `L₁₂(N_* μ (lamfun μ) f)(0) = μ·(L₁₂(D_z f)(0) - L₁₂(f)(0)) = -μ·L₁₂(f)(0)`, the
`D_z`-zero-mode being `L12_Dz_zero_classC` and the additivity of `L₁₂(·)(0)` on the two
summands being `GalBasis.cc.L12_add_of_HkMem` (both summands are `HkMem α 4` and `SmoothOpen`:
scalar multiples of `f`, resp. of `D_z f`, the latter descending from `HkMem α 7 f` via
`IPGen.HkMem_Dz_le`). -/
theorem Nstar_zero_classC {α μ : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hμ : μ ≠ -1) :
    Work.Construction.L12 (Work.Construction.Nstar μ (Work.Construction.lamfun μ) f) 0
      = - μ * Work.Construction.L12 f 0 := by
  -- ## the collapse of `N_*` at `λ = lamfun μ`
  have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    have hμ1 : (1 : ℝ) + μ ≠ 0 := by
      intro h
      exact hμ (by linarith)
    rw [Work.Construction.lamfun]
    field_simp
    ring
  have hcollapse : Work.Construction.Nstar μ (Work.Construction.lamfun μ) f
      = fun z θ => -μ * f z θ + μ * Work.Spaces.Dz f z θ := by
    funext z θ
    simp only [Work.Construction.Nstar]
    rw [hcoef]
    ring
  -- ## smoothness and `ℋ⁴`-honesty of the two summands
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hC.reg
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hsmf.Dz
  have hsm_a : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -μ * f z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h : (Function.uncurry fun z θ => -μ * f z θ)
        = fun p : ℝ × ℝ => (-μ) • Function.uncurry f p := rfl
    rw [h]
    exact ContDiffOn.const_smul _ hsmf
  have hsm_b : Work.FTS.EllipticEst.SmoothOpen (fun z θ => μ * Work.Spaces.Dz f z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h : (Function.uncurry fun z θ => μ * Work.Spaces.Dz f z θ)
        = fun p : ℝ × ℝ => μ • Function.uncurry (Work.Spaces.Dz f) p := rfl
    rw [h]
    exact ContDiffOn.const_smul _ hsmDz
  have hmem_A : Work.Spaces.HkMem α 4 (fun z θ => -μ * f z θ) :=
    Work.FTS.GalBasis.HkMem_const_mul_all (-μ)
      (Work.FTS.IPGen.HkMem_mono_le hsmf 4 (by norm_num) hC.mem)
  have hmem_B : Work.Spaces.HkMem α 4 (fun z θ => μ * Work.Spaces.Dz f z θ) :=
    Work.FTS.GalBasis.HkMem_const_mul_all μ
      (Work.FTS.IPGen.HkMem_Dz_le hsmf
        (Work.FTS.IPGen.HkMem_mono_le hsmf 5 (by norm_num) hC.mem))
  -- ## additivity of `L₁₂(·)(0)` on the two summands
  have hadd := Work.FTS.GalBasis.cc.L12_add_of_HkMem hsm_a hsm_b hmem_A hmem_B
  -- ## the two homogeneous pieces, and the `D_z`-zero-mode
  have hDz : Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := L12_Dz_zero_classC hC hzero
  rw [hcollapse, hadd]
  simp only [Work.Construction.L12] at hDz ⊢
  rw [Work.FM.L12_const_mul, Work.FM.L12_const_mul, hDz]
  ring

end Work.FTS.StrongEps.EpsZero
end
