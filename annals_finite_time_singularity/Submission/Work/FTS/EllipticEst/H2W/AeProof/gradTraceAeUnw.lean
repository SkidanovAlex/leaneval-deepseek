import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe
import Submission.Work.FTS.EllipticEst.AngAWeak.GradTraceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z` — *unweighted* version

`Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw` is the statement
`Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe` with the *unweighted* third hypothesis: the radial
weight `w(z)² = ((1+z)/z)⁴` is dropped, so the hypothesis asks only that
`z ↦ ∫_θ (z ∂_θ∂_z u(z,θ))² σ(θ)` be integrable on `Iz = [0,∞)` (and it is written with the
mixed derivative in the order `∂_z∂_θ` rather than `∂_θ∂_z`).

The two halves of the proof are the two halves of that module (`aeGradTraceLeft`,
`aeGradTraceRightMine`), replayed with the unweighted hypothesis.  The weighted case used the
weight only to obtain the *local* integrability in `z` of the dominating function
`boundU u K = |∂_z u(·,1)| + M √(sliceE u ·)/·` of its dominated-convergence step; here that
local integrability is obtained directly from the unweighted hypothesis, because on `Iz` that
hypothesis *is* the defining integral of the slice energy `sliceE u` (Clairaut's theorem,
`sliceE_eq`), while `√(sliceE u) ≤ 1 + sliceE u` upgrades local `L¹` to local `L¹` of the root.

The only other difference is notational: the hypotheses of the target carry the mixed derivative
as `∂_z∂_θ u = pz (pth u)`, whereas the machinery of `AngAWeak` is phrased with `∂_θ∂_z u =
pth (pz u)`; the two agree on the open quadrant by Clairaut's theorem and both integrands vanish
at the two endpoints because `σ` does (`mixed_order_eq`, `mixed_order_integral_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngAWeak

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. The two orders of the mixed derivative give the same weighted square -/

/-- Clairaut's theorem in the weighted square, in the orientation of the target: on the open
quadrant `z ∂_z∂_θ u` and `z ∂_θ∂_z u` have the same weighted square; at the two endpoints
`θ = 0, π/2` both sides vanish, `σ` being `0` there. -/
theorem mixed_order_eq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2 * σ θ
      = (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.FTS.EllipticEst.AngSecond.sig, hsin,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · have hne0 : θ ≠ 0 := by intro hh; exact hsin (by subst hh; norm_num)
    have hne1 : θ ≠ Real.pi / 2 := by
      intro hh
      exact hsin (by rw [hh]; rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hne0), lt_of_le_of_ne hθ.2 hne1⟩
    have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
      (hS.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))
    rw [Work.Spaces.pz_pth_comm (f := u) hcd]

/-- The same, integrated: the two orientations give the same `sliceE`-like `θ`-integral, for
every `z ∈ Iz` (at `z = 0` both integrands are identically zero). -/
theorem mixed_order_integral_eq {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2 * σ θ)
      = (∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) := by
  by_cases hz0 : z = 0
  · subst hz0
    have h : (fun θ => (0 * Work.Spaces.pz (Work.Spaces.pth u) 0 θ) ^ 2 * σ θ)
        = fun θ => (0 * Work.Spaces.pth (Work.Spaces.pz u) 0 θ) ^ 2 * σ θ := by
      funext θ
      ring
    rw [h]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => mixed_order_eq hS hzpos hθ)

/-! ## 2. The local integrability inputs, from the *unweighted* hypothesis

In the weighted case (`GradTraceAux`) the hypothesis `hint` was used only through
`integrableOn_sliceE_of_hint` / `integrableOn_sqrtSliceE_of_hint` / `integrableOn_boundU`, whose
sole purpose is the local integrability in `z` of the slice energy and of its square root.  Here
the unweighted hypothesis *is* the local integrability of the slice energy, and the AM–GM bound
`√x ≤ 1 + x` transfers it to the square root. -/

/-- The slice energy is locally integrable in `z` from the *unweighted* hypothesis. -/
theorem sliceE_integrableOn_unw {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Iz := fun s hs => le_trans ha.le hs.1
  exact MeasureTheory.IntegrableOn.congr_fun (hint.mono_set hsub)
    (fun z hz => (sliceE_eq hS (hsub hz)).symm) measurableSet_Icc

/-- The square root of the slice energy is locally integrable in `z` from the *unweighted*
hypothesis (`√x ≤ 1 + x`). -/
theorem sqrtSliceE_integrableOn_unw {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (sliceE u s)) (Set.Icc a b) := by
  have hΦ := sliceE_integrableOn_unw hS hint ha hab
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Integrable.mono' (hΦ.add hone) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hΦ.1
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h0 : 0 ≤ sliceE u s := sliceE_nonneg u s
    have hle : Real.sqrt (sliceE u s) ≤ 1 + sliceE u s :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [h0, sq_nonneg (sliceE u s)]⟩
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Pi.add_apply]
    linarith [hle]

/-- `boundU` is locally integrable on `(0,∞)`, from `hint`. -/
theorem boundU_integrableOn_unw {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2 * σ θ) Iz)
    {K : ℝ} (hK : 0 < K) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) := by
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hMnn : 0 ≤ Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
    have := Real.sqrt_nonneg K
    have := Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
    linarith
  have hsqrt := sqrtSliceE_integrableOn_unw hS hint ha hab
  have hboundcont : ContinuousOn (fun s : ℝ => |Work.Spaces.pz u s 1|) (Set.Icc a b) :=
    (((hS.pz).curry_z hθ1).continuousOn.abs).mono (fun s hs => lt_of_lt_of_le ha hs.1)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hboundcont
  have hdom : ∀ s ∈ Set.Icc a b, boundU u K s ≤ C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : |Work.Spaces.pz u s 1| ≤ C₁ := by
      simpa only [Real.norm_eq_abs, abs_abs] using hC₁ s hs
    have h2 : Real.sqrt (sliceE u s) / s ≤ Real.sqrt (sliceE u s) / a := by
      gcongr
      exact hs.1
    have h4 : 0 ≤ Real.sqrt (sliceE u s) := Real.sqrt_nonneg _
    have h5 : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (by positivity)
    rw [boundU]
    have h6 : (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s)
        ≤ ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
          * Real.sqrt (sliceE u s) := by
      rw [show ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
            * Real.sqrt (sliceE u s)
          = (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / a) by ring]
      exact mul_le_mul_of_nonneg_left h2 hMnn
    linarith
  have haesm : AEStronglyMeasurable (boundU u K) (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun s : ℝ => |Work.Spaces.pz u s 1|)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hboundcont.aestronglyMeasurable measurableSet_Icc
    have hsqrt_ae : AEStronglyMeasurable (fun s => Real.sqrt (sliceE u s))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (sliceE_integrableOn_unw hS hint ha hab).1
    have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc a b) :=
      ContinuousOn.inv₀ continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1))
    have h2 : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (sliceE u s) * s⁻¹)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hsqrt_ae.mul (hinv.aestronglyMeasurable measurableSet_Icc)
    have h3 : AEStronglyMeasurable (fun s : ℝ => (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) * s⁻¹))
        (MeasureTheory.volume.restrict (Set.Icc a b)) := h2.const_mul _
    refine AEStronglyMeasurable.congr (h1.add h3) ?_
    filter_upwards with s
    simp only [Pi.add_apply, boundU]
    ring
  refine Integrable.mono' (g := fun s : ℝ => C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s)) ?_ haesm ?_
  · have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    simpa using (hone.const_mul C₁).add (hsqrt.const_mul
      ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h2 : 0 ≤ boundU u K s := by
      rw [boundU]
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (div_nonneg (Real.sqrt_nonneg _) hs0.le)
      linarith [abs_nonneg (Work.Spaces.pz u s 1)]
    rw [Real.norm_of_nonneg h2]
    exact hdom s hs



/-- **The left endpoint.**  `z ∂_z u(z,·) → 0` at `0⁺` for a.e. `z > 0`. -/
theorem gradTraceLeftUnw (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Iθ)
    (hint : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Iz) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hsm := Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- the a.e. per-slice honesty, in terms of `∂_θ(z ∂_z u)`
  have hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ :=
    ae_integrableOn_sliceE_of_hae hS hae
  obtain ⟨K, hKpos, hraw⟩ := sliceBoundaryLeftRaw
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hmemθ : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hden0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    refine ⟨?_, ?_⟩
    · exact div_pos (by norm_num) hden0
    · have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_iff₀ hden0]
        simpa using hden1
      linarith [Real.pi_gt_three]
  have hθn : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun n => by rw [Set.mem_Ioi]; positivity⟩
  -- the candidate trace, as the limsup along the diagonal sequence
  set c0 : ℝ → ℝ := fun s =>
    Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1))) Filter.atTop
    with hc0def
  set f : ℝ → ℝ := fun s => c0 s / s with hfdef
  have hc0_apply : ∀ s : ℝ, c0 s =
      Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1))) Filter.atTop :=
    fun s => by simp only [hc0def]
  have hf_apply : ∀ s : ℝ, f s = c0 s / s := fun s => by simp only [hfdef]
  -- ## Step 1: measurability of `c0`
  have hγaesm : ∀ n : ℕ, AEMeasurable
      (fun s : ℝ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact ContinuousOn.aemeasurable
      (continuousOn_id.mul ((hS.pz).curry_z (hmemθ n)).continuousOn) measurableSet_Ioi
  have hc0aesm : AEMeasurable c0 (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    AEMeasurable.limsup hγaesm
  -- ## Step 2: the one-sided limit and the quadratic bound, on the honest set
  have hmain : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0 s)) ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.Dz u s θ - c0 s) ^ 2
          ≤ K * θ ^ (1 + Work.Spaces.eta) * sliceE u s := by
    intro s hE hs
    obtain ⟨c, hc, hb⟩ := sliceBoundaryLeft hS hs hKpos.le hraw hE
    have hseq : Filter.Tendsto (fun n : ℕ => s * Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds c) := by
      simpa only [Work.Spaces.Dz, Function.comp_def] using hc.comp hθn
    have hc0 : c0 s = c := by
      rw [hc0_apply s]
      exact Filter.Tendsto.limsup_eq hseq
    constructor
    · rw [hc0]; exact hc
    · intro θ hθ
      rw [hc0]
      exact hb θ hθ
  -- ## Step 3: the pointwise domination of `|∂_z u(s,θ)|`
  have hΦnn : ∀ s : ℝ, 0 ≤ sliceE u s := sliceE_nonneg u
  have hbd : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.pz u s θ| ≤ boundU u K s := by
    intro s hE hs θ hθ
    have h1 : (Work.Spaces.Dz u s 1 - c0 s) ^ 2 ≤ K * sliceE u s := by
      simpa using (hmain s hE hs).2 1 hθ1
    have h2 : (Work.Spaces.Dz u s θ - c0 s) ^ 2
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s := by
      refine le_trans ((hmain s hE hs).2 θ hθ) ?_
      have hpow : θ ^ (1 + Work.Spaces.eta) ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
        Real.rpow_le_rpow hθ.1.le (le_of_lt hθ.2) (by norm_num [Work.Spaces.eta])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKpos.le) (hΦnn s)
    exact pz_le_of_slice_bounds hs hθ hKpos (hΦnn s) h1 h2
  -- ## Step 4: the integrability of `√sliceE`, `boundU` and `f`
  have hsqrtPhiint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (fun s => Real.sqrt (sliceE u s)) (Set.Icc a b) :=
    fun a b ha hab => sqrtSliceE_integrableOn_unw hS hint ha hab
  have hboundint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) :=
    fun a b ha hab => boundU_integrableOn_unw hS hint hKpos ha hab
  have hfint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn f (Set.Icc a b) := by
    intro a b ha hab
    have hbnd := hboundint a b ha hab
    have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    refine Integrable.mono' hbnd ?_ ?_
    · have h1 : AEMeasurable (fun s : ℝ => c0 s / s)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
        hc0aesm.div (ContinuousOn.aemeasurable continuousOn_id measurableSet_Ioi)
      refine (h1.aestronglyMeasurable.mono_measure
        (MeasureTheory.Measure.restrict_mono hsub le_rfl)).congr ?_
      filter_upwards with s
      exact (hf_apply s).symm
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hGsub]
        with s hs hsG
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have hΦ0 : 0 ≤ sliceE u s := hΦnn s
      have h1 : (Work.Spaces.Dz u s 1 - c0 s) ^ 2 ≤ K * sliceE u s := by
        simpa using (hmain s hsG hs0).2 1 hθ1
      have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hKpos.le hΦ0
      have hc0bd : |c0 s| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
        have h2abs : |Work.Spaces.Dz u s 1 - c0 s| ≤ Real.sqrt (K * sliceE u s) :=
          abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
        calc |c0 s| = |c0 s - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
          _ ≤ |c0 s - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
          _ = |Work.Spaces.Dz u s 1 - c0 s| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
          _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
          _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
      have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
      have hsqrtK : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
        Real.sqrt_mul hKpos.le _
      have hMle : Real.sqrt K ≤ Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
        linarith [Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))]
      rw [hf_apply s, Real.norm_eq_abs, abs_div, abs_of_pos hs0, boundU]
      have h4 : |c0 s| / s ≤ (|Work.Spaces.Dz u s 1|
          + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s := by
        refine div_le_div_of_nonneg_right ?_ hs0.le
        rw [hsqrtK] at hc0bd
        have := mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (sliceE u s))
        linarith [hc0bd, this]
      have h5 : (|Work.Spaces.Dz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s
          = |Work.Spaces.pz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / s) := by
        rw [hDz1, abs_mul, abs_of_pos hs0, add_div, mul_div_cancel_left₀ _ (ne_of_gt hs0),
          mul_div_assoc]
      rw [← h5]
      exact h4
  -- ## Step 5: the left trace of `u`
  have hex : ∀ z : ℝ, 0 < z → ∃ L : ℝ,
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    intro z hz
    refine Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ)
      (fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n) ?_
    have h0 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem
      (Ψ := u) (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hAe) hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  set g : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (hex z hz) else 0 with hgdef
  have hg_apply : ∀ z : ℝ, (hz : 0 < z) → g z = Classical.choose (hex z hz) := by
    intro z hz
    simp only [hgdef, dif_pos hz]
  have hglim : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (g z)) := by
    intro z hz
    rw [hg_apply z hz]
    exact Classical.choose_spec (hex z hz)
  have hgzero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), g z = 0 := by
    filter_upwards [Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G hAe,
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hzlim hzpos
    exact tendsto_nhds_unique (hglim z hzpos) hzlim
  -- ## Step 6: the integral relation `∫_a^b f = g b - g a`
  have hrel : ∀ a b : ℝ, 0 < a → a < b → ∫ t in a..b, f t = g b - g a := by
    intro a b ha hab
    have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    have hbndIoc : MeasureTheory.IntegrableOn (boundU u K) (Set.Ioc a b) :=
      (integrableOn_Icc_iff_integrableOn_Ioc (f := boundU u K) (a := a) (b := b)
        (by simp)).mp (hboundint a b ha hab)
    have hDCT : Filter.Tendsto
        (fun n : ℕ => ∫ s in Set.Ioc a b, Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ s in Set.Ioc a b, f s)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
        (F := fun n : ℕ => fun s : ℝ => Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
        (f := f) (bound := boundU u K) ?_ hbndIoc ?_ ?_
      · intro n
        exact (((hS.pz).curry_z (hmemθ n)).continuousOn.aestronglyMeasurable
          measurableSet_Ioi).mono_measure
          (MeasureTheory.Measure.restrict_mono hsub le_rfl)
      · intro n
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        rw [Real.norm_eq_abs]
        exact hbd s hsG hs0 _ (hmemθ n)
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        have h1 : Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c0 s)) := (hmain s hsG hs0).1
        have h2 : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)))
            Filter.atTop (nhds (c0 s)) := h1.comp hθn
        have h3 : Filter.Tendsto (fun n : ℕ =>
            Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)) / s) Filter.atTop (nhds (c0 s / s)) :=
          h2.div_const s
        have hfun : (fun n : ℕ => Work.Spaces.pz u s (1 / ((n : ℝ) + 1)))
            = fun n : ℕ => Work.Spaces.Dz u s (1 / ((n : ℝ) + 1)) / s := by
          funext n
          rw [Work.Spaces.Dz, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
        rw [hfun, hf_apply s]
        exact h3
    have hFTC : ∀ n : ℕ, u b (1 / ((n : ℝ) + 1)) - u a (1 / ((n : ℝ) + 1))
        = ∫ s in Set.Ioc a b, Work.Spaces.pz u s (1 / ((n : ℝ) + 1)) := by
      intro n
      have h := Work.FTS.EllipticEst.pzIter_slice_FTC_open hS 0 ha hab.le (hmemθ n)
      simpa only [Work.Spaces.pzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
        intervalIntegral.integral_of_le hab.le] using h
    have hlimL : Filter.Tendsto
        (fun n : ℕ => u b (1 / ((n : ℝ) + 1)) - u a (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (g b - g a)) :=
      ((hglim b (ha.trans hab)).comp hθn).sub ((hglim a ha).comp hθn)
    have hEqIoc : (∫ s in Set.Ioc a b, f s) = g b - g a := by
      refine tendsto_nhds_unique ?_ hlimL
      simpa only [hFTC] using hDCT
    rw [intervalIntegral.integral_of_le hab.le]
    exact hEqIoc
  -- ## Step 7: `f` vanishes a.e.
  have hintI : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hfint a b ha hab
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Ioi (1 / ((n : ℝ) + 1)))), f z = 0 := by
    intro n
    have hz0 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact div_pos (by norm_num) (by linarith)
    refine Work.FTS.EllipticEst.Mine.CutoffPieces.ae_zero_of_primitive_const
      (f := f) (g := g) (z₀ := 1 / ((n : ℝ) + 1)) hz0 ?_ ?_ ?_
    · intro a b ha hab
      exact hintI a b (lt_of_lt_of_le hz0 ha) hab
    · have hle : MeasureTheory.volume.restrict (Set.Ioi (1 / ((n : ℝ) + 1)))
          ≤ MeasureTheory.volume.restrict (Set.Ioi 0) :=
        MeasureTheory.Measure.restrict_mono (fun z hz => hz0.trans hz) le_rfl
      exact MeasureTheory.ae_mono hle hgzero
    · intro a b ha hab
      exact hrel a b (lt_of_lt_of_le hz0 ha) hab
  have hunion : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    show ∀ᵐ z ∂MeasureTheory.volume, 0 < z → f z = 0
    rw [MeasureTheory.ae_iff]
    show MeasureTheory.volume {z : ℝ | ¬(0 < z → f z = 0)} = 0
    have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0} = 0 := by
      refine le_antisymm ?_ bot_le
      have hsub : {z : ℝ | 0 < z ∧ f z ≠ 0} ⊆ ⋃ n : ℕ,
          {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0} := by
        intro z hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz.1
        exact Set.mem_iUnion.mpr ⟨n, hn, hz.2⟩
      calc MeasureTheory.volume {z : ℝ | 0 < z ∧ f z ≠ 0}
          ≤ MeasureTheory.volume (⋃ n : ℕ,
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0}) :=
            MeasureTheory.measure_mono hsub
        _ ≤ ∑' n : ℕ, MeasureTheory.volume
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f z ≠ 0} :=
            MeasureTheory.measure_iUnion_le _
        _ = 0 := by
            refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
            have hn := hstep n
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff] at hn
            convert hn using 2
            ext z
            simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
            tauto
    convert hbad using 2
    ext z
    simp only [Set.mem_ofPred_eq]
    tauto
  -- ## Step 8: conclude
  have hc0zero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), c0 z = 0 := by
    filter_upwards [hunion, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    have hdiv : c0 z / z = 0 := by rw [← hf_apply z]; exact hz
    rcases div_eq_zero_iff.mp hdiv with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hzpos)
  filter_upwards [hc0zero, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hGae]
    with z hz hzpos hzG
  have h1 := (hmain z hzG hzpos).1
  rw [hz] at h1
  simpa only [Work.Spaces.Dz] using h1


/-- **The right endpoint.**  `z ∂_z u(z,·) → 0` at `(π/2)⁻` for a.e. `z > 0`. -/
theorem gradTraceRightUnw (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Iθ)
    (hint : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Iz) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hsm := Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hGae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ :=
    ae_integrableOn_sliceE_of_hae hS hae
  obtain ⟨K, hKpos, hraw⟩ := sliceBoundaryRightRaw
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hmemθ : ∀ n : ℕ, (Real.pi / 2 - 1 / ((n : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hden0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hsmall : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hden0]
      simpa using hden1
    refine ⟨?_, ?_⟩
    · linarith [Real.pi_gt_three, hsmall]
    · exact sub_lt_self _ (div_pos (by norm_num) hden0)
  have hθn : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.sub h
    · rw [Set.mem_Iio]
      exact sub_lt_self _ (div_pos (by norm_num) (by positivity))
  set c1 : ℝ → ℝ := fun s =>
    Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
    Filter.atTop with hc1def
  set f1 : ℝ → ℝ := fun s => c1 s / s with hf1def
  have hc1_apply : ∀ s : ℝ, c1 s =
      Filter.limsup (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
      Filter.atTop := fun s => by simp only [hc1def]
  have hf1_apply : ∀ s : ℝ, f1 s = c1 s / s := fun s => by simp only [hf1def]
  -- ## Step 1: measurability of `c1`
  have hγaesm : ∀ n : ℕ, AEMeasurable
      (fun s : ℝ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact ContinuousOn.aemeasurable
      (continuousOn_id.mul ((hS.pz).curry_z (hmemθ n)).continuousOn) measurableSet_Ioi
  have hc1aesm : AEMeasurable c1 (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    AEMeasurable.limsup hγaesm
  -- ## Step 2: the one-sided limit and the quadratic bound, on the honest set
  have hmain : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz u s θ - c1 s) ^ 2
            ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * sliceE u s := by
    intro s hE hs
    obtain ⟨c, hc, hb⟩ := sliceBoundaryRight hS hs hKpos.le hraw hE
    have hseq : Filter.Tendsto
        (fun n : ℕ => s * Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds c) := by
      simpa only [Work.Spaces.Dz, Function.comp_def] using hc.comp hθn
    have hc1 : c1 s = c := by
      rw [hc1_apply s]
      exact Filter.Tendsto.limsup_eq hseq
    constructor
    · rw [hc1]; exact hc
    · intro θ hθ
      rw [hc1]
      exact hb θ hθ
  -- ## Step 3: the pointwise domination of `|∂_z u(s,θ)|`
  have hΦnn : ∀ s : ℝ, 0 ≤ sliceE u s := sliceE_nonneg u
  -- the reference angle `1` obeys `(π/2 - 1)^{1+η} ≤ 1`
  have href : ∀ s : ℝ, K * (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s
      ≤ K * sliceE u s := by
    intro s
    have h0 : (0 : ℝ) ≤ Real.pi / 2 - 1 := by linarith [Real.pi_gt_three]
    have h1 : Real.pi / 2 - 1 ≤ 1 := by linarith [Real.pi_lt_four]
    have hpow : (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) ≤ 1 := by
      calc (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta)
          ≤ (1 : ℝ) ^ (1 + Work.Spaces.eta) :=
            Real.rpow_le_rpow h0 h1 (by norm_num [Work.Spaces.eta])
        _ = 1 := Real.one_rpow _
    calc K * (Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s
        = K * ((Real.pi / 2 - 1) ^ (1 + Work.Spaces.eta) * sliceE u s) := by ring
      _ ≤ K * (1 * sliceE u s) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (hΦnn s)) hKpos.le
      _ = K * sliceE u s := by ring
  have hbd : ∀ s : ℝ,
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Iθ → 0 < s →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.pz u s θ| ≤ boundU u K s := by
    intro s hE hs θ hθ
    have h1 : (Work.Spaces.Dz u s 1 - c1 s) ^ 2 ≤ K * sliceE u s :=
      le_trans ((hmain s hE hs).2 1 hθ1) (href s)
    have h2 : (Work.Spaces.Dz u s θ - c1 s) ^ 2
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * sliceE u s := by
      refine le_trans ((hmain s hE hs).2 θ hθ) ?_
      have hpow : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
        Real.rpow_le_rpow (by linarith [hθ.2]) (by linarith [hθ.1])
          (by norm_num [Work.Spaces.eta])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKpos.le) (hΦnn s)
    exact pz_le_of_slice_bounds hs hθ hKpos (hΦnn s) h1 h2
  -- ## Step 4: the integrability of `boundU` and `f1`
  have hboundint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (boundU u K) (Set.Icc a b) :=
    fun a b ha hab => boundU_integrableOn_unw hS hint hKpos ha hab
  have hfint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn f1 (Set.Icc a b) := by
    intro a b ha hab
    have hbnd := hboundint a b ha hab
    have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    refine Integrable.mono' hbnd ?_ ?_
    · have h1 : AEMeasurable (fun s : ℝ => c1 s / s)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
        hc1aesm.div (ContinuousOn.aemeasurable continuousOn_id measurableSet_Ioi)
      refine (h1.aestronglyMeasurable.mono_measure
        (MeasureTheory.Measure.restrict_mono hsub le_rfl)).congr ?_
      filter_upwards with s
      exact (hf1_apply s).symm
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hGsub]
        with s hs hsG
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have hΦ0 : 0 ≤ sliceE u s := hΦnn s
      have h1 : (Work.Spaces.Dz u s 1 - c1 s) ^ 2 ≤ K * sliceE u s :=
        le_trans ((hmain s hsG hs0).2 1 hθ1) (href s)
      have hKΦ : 0 ≤ K * sliceE u s := mul_nonneg hKpos.le hΦ0
      have hc1bd : |c1 s| ≤ |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by
        have h2abs : |Work.Spaces.Dz u s 1 - c1 s| ≤ Real.sqrt (K * sliceE u s) :=
          abs_le_of_sq_le_sq (by rw [Real.sq_sqrt hKΦ]; exact h1) (Real.sqrt_nonneg _)
        calc |c1 s| = |c1 s - Work.Spaces.Dz u s 1 + Work.Spaces.Dz u s 1| := by ring_nf
          _ ≤ |c1 s - Work.Spaces.Dz u s 1| + |Work.Spaces.Dz u s 1| := abs_add_le _ _
          _ = |Work.Spaces.Dz u s 1 - c1 s| + |Work.Spaces.Dz u s 1| := by rw [abs_sub_comm]
          _ ≤ Real.sqrt (K * sliceE u s) + |Work.Spaces.Dz u s 1| := by linarith
          _ = |Work.Spaces.Dz u s 1| + Real.sqrt (K * sliceE u s) := by ring
      have hDz1 : Work.Spaces.Dz u s 1 = s * Work.Spaces.pz u s 1 := rfl
      have hsqrtK : Real.sqrt (K * sliceE u s) = Real.sqrt K * Real.sqrt (sliceE u s) :=
        Real.sqrt_mul hKpos.le _
      have hMle : Real.sqrt K ≤ Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
        linarith [Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))]
      rw [hf1_apply s, Real.norm_eq_abs, abs_div, abs_of_pos hs0, boundU]
      have h4 : |c1 s| / s ≤ (|Work.Spaces.Dz u s 1|
          + (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s := by
        refine div_le_div_of_nonneg_right ?_ hs0.le
        rw [hsqrtK] at hc1bd
        have := mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (sliceE u s))
        linarith [hc1bd, this]
      have h5 : (|Work.Spaces.Dz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * Real.sqrt (sliceE u s)) / s
          = |Work.Spaces.pz u s 1| + (Real.sqrt K
            + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / s) := by
        rw [hDz1, abs_mul, abs_of_pos hs0, add_div, mul_div_cancel_left₀ _ (ne_of_gt hs0),
          mul_div_assoc]
      rw [← h5]
      exact h4
  -- ## Step 5: the right trace of `u` vanishes identically
  have hglim : ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hAe z hz).1
  -- ## Step 6: the integral relation `∫_a^b f1 = 0`
  have hrel : ∀ a b : ℝ, 0 < a → a < b → ∫ t in a..b, f1 t = 0 := by
    intro a b ha hab
    have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
    have hGsub : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.Dz (Work.Spaces.pth u) s θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Iθ :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono_set volume hsub) hGae
    have hbndIoc : MeasureTheory.IntegrableOn (boundU u K) (Set.Ioc a b) :=
      (integrableOn_Icc_iff_integrableOn_Ioc (f := boundU u K) (a := a) (b := b)
        (by simp)).mp (hboundint a b ha hab)
    have hDCT : Filter.Tendsto
        (fun n : ℕ => ∫ s in Set.Ioc a b,
          Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (∫ s in Set.Ioc a b, f1 s)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
        (F := fun n : ℕ => fun s : ℝ =>
          Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        (f := f1) (bound := boundU u K) ?_ hbndIoc ?_ ?_
      · intro n
        exact (((hS.pz).curry_z (hmemθ n)).continuousOn.aestronglyMeasurable
          measurableSet_Ioi).mono_measure
          (MeasureTheory.Measure.restrict_mono hsub le_rfl)
      · intro n
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        rw [Real.norm_eq_abs]
        exact hbd s hsG hs0 _ (hmemθ n)
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc, hGsub]
          with s hs hsG
        have hs0 : 0 < s := lt_trans ha hs.1
        have h1 : Filter.Tendsto (fun θ => Work.Spaces.Dz u s θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (c1 s)) :=
          (hmain s hsG hs0).1
        have h2 : Filter.Tendsto
            (fun n : ℕ => Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
            Filter.atTop (nhds (c1 s)) := h1.comp hθn
        have h3 : Filter.Tendsto (fun n : ℕ =>
            Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) / s)
            Filter.atTop (nhds (c1 s / s)) := h2.div_const s
        have hfun : (fun n : ℕ => Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
            = fun n : ℕ => Work.Spaces.Dz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) / s := by
          funext n
          rw [Work.Spaces.Dz, mul_div_cancel_left₀ _ (ne_of_gt hs0)]
        rw [hfun, hf1_apply s]
        exact h3
    have hFTC : ∀ n : ℕ, u b (Real.pi / 2 - 1 / ((n : ℝ) + 1))
        - u a (Real.pi / 2 - 1 / ((n : ℝ) + 1))
        = ∫ s in Set.Ioc a b, Work.Spaces.pz u s (Real.pi / 2 - 1 / ((n : ℝ) + 1)) := by
      intro n
      have h := Work.FTS.EllipticEst.pzIter_slice_FTC_open hS 0 ha hab.le (hmemθ n)
      simpa only [Work.Spaces.pzIter_zero, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero,
        intervalIntegral.integral_of_le hab.le] using h
    have hlimL : Filter.Tendsto
        (fun n : ℕ => u b (Real.pi / 2 - 1 / ((n : ℝ) + 1))
          - u a (Real.pi / 2 - 1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds (0 - 0)) :=
      ((hglim b (ha.trans hab)).comp hθn).sub ((hglim a ha).comp hθn)
    have hEqIoc : (∫ s in Set.Ioc a b, f1 s) = 0 := by
      refine tendsto_nhds_unique
        (Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hFTC n).symm) hDCT) ?_
      simpa using hlimL
    rw [intervalIntegral.integral_of_le hab.le]
    exact hEqIoc
  -- ## Step 7: `f1` vanishes a.e.
  have hintI : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable f1 MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hfint a b ha hab
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict
      (Set.Ioi (1 / ((n : ℝ) + 1)))), f1 z = 0 := by
    intro n
    have hz0 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact div_pos (by norm_num) (by linarith)
    refine Work.FTS.EllipticEst.Mine.CutoffPieces.ae_zero_of_primitive_const
      (f := f1) (g := fun _ => (0 : ℝ)) (z₀ := 1 / ((n : ℝ) + 1)) hz0 ?_ ?_ ?_
    · intro a b ha hab
      exact hintI a b (lt_of_lt_of_le hz0 ha) hab
    · filter_upwards with z
      rfl
    · intro a b ha hab
      have h := hrel a b (lt_of_lt_of_le hz0 ha) hab
      simpa using h
  have hunion : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f1 z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    show ∀ᵐ z ∂MeasureTheory.volume, 0 < z → f1 z = 0
    rw [MeasureTheory.ae_iff]
    show MeasureTheory.volume {z : ℝ | ¬(0 < z → f1 z = 0)} = 0
    have hbad : MeasureTheory.volume {z : ℝ | 0 < z ∧ f1 z ≠ 0} = 0 := by
      refine le_antisymm ?_ bot_le
      have hsub : {z : ℝ | 0 < z ∧ f1 z ≠ 0} ⊆ ⋃ n : ℕ,
          {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0} := by
        intro z hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz.1
        exact Set.mem_iUnion.mpr ⟨n, hn, hz.2⟩
      calc MeasureTheory.volume {z : ℝ | 0 < z ∧ f1 z ≠ 0}
          ≤ MeasureTheory.volume (⋃ n : ℕ,
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0}) :=
            MeasureTheory.measure_mono hsub
        _ ≤ ∑' n : ℕ, MeasureTheory.volume
              {z : ℝ | z ∈ Set.Ioi (1 / ((n : ℝ) + 1)) ∧ f1 z ≠ 0} :=
            MeasureTheory.measure_iUnion_le _
        _ = 0 := by
            refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
            have hn := hstep n
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff] at hn
            convert hn using 2
            ext z
            simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
            tauto
    convert hbad using 2
    ext z
    simp only [Set.mem_ofPred_eq]
    tauto
  -- ## Step 8: conclude
  have hc1zero : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), c1 z = 0 := by
    filter_upwards [hunion, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    have hdiv : c1 z / z = 0 := by rw [← hf1_apply z]; exact hz
    rcases div_eq_zero_iff.mp hdiv with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hzpos)
  filter_upwards [hc1zero, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hGae]
    with z hz hzpos hzG
  have h1 := (hmain z hzG hzpos).1
  rw [hz] at h1
  simpa only [Work.Spaces.Dz] using h1


theorem gradTraceAeUnw : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz u z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
    := by
  intro α u G hAe hae hint
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe)
  -- rewrite the two hypotheses in the `∂_θ∂_z u` orientation used by the `AngAWeak` machinery
  have hae' : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    filter_upwards [hae, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
    exact hz.congr_fun (fun θ hθ => mixed_order_eq hS hzpos hθ) measurableSet_Icc
  have hint' : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz :=
    hint.congr_fun (fun z hz => mixed_order_integral_eq hS hz) measurableSet_Ici
  filter_upwards [gradTraceLeftUnw α u G hAe hae' hint',
    gradTraceRightUnw α u G hAe hae' hint'] with z h1 h2
  exact ⟨h1, h2⟩

end Work.FTS.EllipticEst.H2W.AeProof
