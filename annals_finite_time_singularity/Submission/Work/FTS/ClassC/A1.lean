/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.A1` — `ClassC` is a subspace (design (A), item A1)

The first obligation of the area is that the new source class `ClassC`
(`Submission/Work/FTS/ClassC/Defs.lean`) is closed under `+` and `c • ·`: this is what makes the
Hamel step (item A6) applicable and what replaces the false `galClass_lin` (`EllSol/Refute`).

Every field of `ClassC` is an open-quadrant value, a limit, or an integral of the profile, so each
one is inherited by the linear combination:

* `norm` — `normTh` is linear and `normTh g = g` forces `g z θ = 0` off the open angle interval;
* `reg` — `SmoothOpen` is closed under `+` (`smoothOpen_add`) and under constants
  (`SmoothOpen.const_mul'`);
* `mem` — `HkMem α 7` is closed under `+` (`HkMem_add_open`) and constants
  (`LocData.HkMem_const_mul`);
* `tr` — `BdryTraces α 6` is closed under `+` and `c • ·` (`bdryTraces_add`, `bdryTraces_smul`
  below): the defining quantities are quadratic in the mixed derivatives, so `(x+y)² ≤ 2x²+2y²`
  transfers the four limit families;
* `fsm` — `F_*` is additive (`EllSol.Fstar_add_mul`) and homogeneous
  (`EllSol.Fstar_const_mul`) on the slices, and `ContDiffOn` is closed under these operations;
* `axis` — the limit `g(z,θ)/z → 0` is linear;
* `l12` — `L₁₂(g)(0) = 0` is linear (`GalBasis.cc.L12_add_of_HkMem`,
  `GalBasis.L12_const_mul`).

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Uop_bound_reg
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllSol.EllAux1
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.PhiStar.ThetaTracesBdry

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
