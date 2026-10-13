import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.HkSq_mono
import Submission.Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Vop_bound_reg
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le`

The local part `locOp f = -𝓛 f + Transport f` of the linearised operator `𝓛_Γ^T` is a
*first-order* differential operator with smooth bounded coefficients,

  `locOp f z θ = -f z θ - D_z f z θ + (2/(1+z))·f z θ + (3/(1+z))·D_θ f z θ`,

and the module proves that it preserves the class `SmoothOpen` and `ℋ³`, with a norm
estimate against `ℋ⁴`:

  `HkSq α 3 (locOp f) ≤ C · HkSq α 4 f`.

The pointwise skeleton is the `ℋ³`-integrand bound

  `HkIntegrand α 3 (locOp f) z θ ≤ C · HkIntegrand α 4 f z θ`

on the closed quadrant.  It is assembled from

* subadditivity of `HkIntegrand` on the open quadrant
  (`Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn`);
* the shift estimate `HkIntegrand α 3 (D_z^b D_θ^a f) ≤ HkIntegrand α 4 f`
  (`Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift`, for `a + b ≤ 1`);
* the radial-multiplier estimate
  `HkIntegrand α 3 (φ·g) ≤ C(1+K)² HkIntegrand α 3 g` for a `z`-only multiplier `φ` with
  `|Zop^b φ| ≤ K` (`Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le`), applied with
  `φ z = 3/(1+z)`, whose iterates are bounded by `100`
  (`Work.FTS.FinalClock.PhiZopBound`).

The membership `HkMem α 3 (locOp f)` and the integrated estimate follow from the pointwise
bound by the majorant criterion `Work.FTS.LocData.HkMem_of_majorant` and monotonicity of the
integral.
-/

/-! ## Elementary smoothness helpers -/

/-- `SmoothOpen` of a function of `z` alone which is `C^∞` on `(-1,∞)`. -/
private lemma smoothOpen_radial {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => φ z) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiff_fst.contDiffOn
  exact hφ.comp hfst (fun p hp => by
    have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    exact show (-1 : ℝ) < p.1 from by linarith)

/-- `SmoothOpen` is closed under addition. -/
private lemma smoothOpen_add' {g h : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ + h z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg hh ⊢
  have hfun : Function.uncurry (fun z θ => g z θ + h z θ)
      = fun p : ℝ × ℝ => Function.uncurry g p + Function.uncurry h p := by
    funext p; rfl
  rw [hfun]
  exact hg.add hh

/-- `SmoothOpen` is closed under multiplication. -/
private lemma smoothOpen_mul' {g h : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ * h z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg hh ⊢
  have hfun : Function.uncurry (fun z θ => g z θ * h z θ)
      = fun p : ℝ × ℝ => Function.uncurry g p * Function.uncurry h p := by
    funext p; rfl
  rw [hfun]
  exact hg.mul hh

/-- `SmoothOpen` is closed under multiplication by a constant. -/
private lemma smoothOpen_const_mul' (c : ℝ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have hfun : Function.uncurry (fun z θ => c * g z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry g p := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul hg

/-! ## Pointwise domination of different levels integrates -/

/-- The pointwise domination of the `ℋ^k`-integrand of `f` by a multiple of the
`ℋ^l`-integrand of `g` (`k ≠ l` allowed) integrates to the corresponding domination of the
squared norms, provided the dominating datum is honest (`HkMem α l g`). -/
private lemma HkSq_le_of_pointwise_levels (α : ℝ) (k l : ℕ) {f g : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hmg : Work.Spaces.HkMem α l g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ C * Work.Spaces.HkIntegrand α l g z θ) :
    Work.Spaces.HkSq α k f ≤ C * Work.Spaces.HkSq α l g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (g := fun θ => C * Work.Spaces.HkIntegrand α l g z θ)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      ((hmg.1 z hz).const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ))
    rwa [MeasureTheory.integral_const_mul] at hmono
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
    (g := fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ)
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (hmg.2.const_mul C)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rw [MeasureTheory.integral_const_mul] at houter
  exact houter

/-! ## The estimate -/

theorem locOp_HkSq_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) ∧
    Work.Spaces.HkMem α 3
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) ∧
    Work.Spaces.HkSq α 3
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zmul_le 3
  refine ⟨4 * (2 + 2 * (Cz * 101 ^ 2)) + 1, by nlinarith [hCzpos], ?_⟩
  intro α f hα _hα1 hf hmem
  -- the multiplier `φ z = 3/(1+z)` and its iterate bound `K = 100`
  have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
      (Set.Ioi (-1)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m)
  have hφZop : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ 100 := fun b hb z hz =>
    Work.FTS.FinalClock.PhiZopBound b (by omega) z (le_of_lt hz)
  -- the four summands of `locOp`
  set A1 : ℝ → ℝ → ℝ := fun z θ => -f z θ with hA1
  set A2 : ℝ → ℝ → ℝ := fun z θ => -(Work.Spaces.Dz f z θ) with hA2
  set A3 : ℝ → ℝ → ℝ := fun z θ => (2 / 3) * ((fun z : ℝ => 3 / (1 + z)) z * f z θ)
    with hA3
  set A4 : ℝ → ℝ → ℝ := fun z θ => (fun z : ℝ => 3 / (1 + z)) z * (Work.Spaces.Dth f z θ)
    with hA4
  set A12 : ℝ → ℝ → ℝ := fun z θ => A1 z θ + A2 z θ with hA12
  set A34 : ℝ → ℝ → ℝ := fun z θ => A3 z θ + A4 z θ with hA34
  set E : ℝ → ℝ → ℝ := fun z θ => A12 z θ + A34 z θ with hE
  -- `locOp` is exactly `E`
  have hlocOp :
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) = E := by
    rw [hE, hA12, hA34, hA1, hA2, hA3, hA4]
    funext z θ
    simp only [Work.Coercivity.L, Work.Coercivity.Transport]
    ring
  -- smoothness of the pieces
  have hA1sm : Work.FTS.EllipticEst.SmoothOpen A1 := by
    have h1 : A1 = fun z θ => (-1 : ℝ) * f z θ := by
      rw [hA1]; funext z θ; ring
    rw [h1]
    exact smoothOpen_const_mul' (-1) hf
  have hA2sm : Work.FTS.EllipticEst.SmoothOpen A2 := by
    have h2 : A2 = fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ := by
      rw [hA2]; funext z θ; ring
    rw [h2]
    exact smoothOpen_const_mul' (-1) hf.Dz
  have hA3sm : Work.FTS.EllipticEst.SmoothOpen A3 := by
    rw [hA3]
    exact smoothOpen_const_mul' (2 / 3)
      (smoothOpen_mul' (smoothOpen_radial hφsm) hf)
  have hA4sm : Work.FTS.EllipticEst.SmoothOpen A4 := by
    rw [hA4]
    exact smoothOpen_mul' (smoothOpen_radial hφsm) hf.Dth
  have hA12sm : Work.FTS.EllipticEst.SmoothOpen A12 := by
    rw [hA12]; exact smoothOpen_add' hA1sm hA2sm
  have hA34sm : Work.FTS.EllipticEst.SmoothOpen A34 := by
    rw [hA34]; exact smoothOpen_add' hA3sm hA4sm
  have hEsm : Work.FTS.EllipticEst.SmoothOpen E := by
    rw [hE]; exact smoothOpen_add' hA12sm hA34sm
  -- the four piecewise bounds
  have hA1bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A1 z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have h1 : A1 = fun z θ => (-1 : ℝ) * f z θ := by
      rw [hA1]; funext z θ; ring
    have h2 : Work.Spaces.HkIntegrand α 3 f z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using Work.Spaces.HkIntegrand_mono α 3 f z θ
    rw [h1, Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (-1) f z θ]
    have hneg : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [hneg, one_mul]
    exact h2
  have hA2bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A2 z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have h1 : A2 = fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ := by
      rw [hA2]; funext z θ; ring
    rw [h1, Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (-1)
      (Work.Spaces.Dz f) z θ]
    have hneg : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [hneg, one_mul]
    have h2 : Work.Spaces.HkIntegrand α 3 (Work.Spaces.mixed 1 0 f) z θ
        ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using HkIntegrand_mixed_shift α hα 3 0 1 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero] using h2
  have hA3bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A3 z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have hpt := (hCz α (fun z : ℝ => 3 / (1 + z)) 100 (by norm_num) hφZop hφsm f hf).1
      z hz θ hθ
    have hmono : Work.Spaces.HkIntegrand α 3 f z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using Work.Spaces.HkIntegrand_mono α 3 f z θ
    have hpt' : Work.Spaces.HkIntegrand α 3
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
      calc Work.Spaces.HkIntegrand α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
          ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 3 f z θ := hpt
        _ ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
            mul_le_mul_of_nonneg_left hmono (by nlinarith [hCzpos])
        _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by norm_num
    have h3 : A3 = fun z θ => (2 / 3) *
        ((fun z : ℝ => 3 / (1 + z)) z * f z θ) := hA3
    have hkey := Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (2 / 3)
      (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
    have hnn : 0 ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
      mul_nonneg (mul_nonneg hCzpos.le (by norm_num))
        (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
    have h23 : ((2 : ℝ) / 3) ^ 2 ≤ 1 := by norm_num
    calc Work.Spaces.HkIntegrand α 3 A3 z θ
        = ((2 : ℝ) / 3) ^ 2 * Work.Spaces.HkIntegrand α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ := by
          rw [h3, hkey]
      _ ≤ 1 * (Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          refine mul_le_mul h23 hpt' ?_ (by norm_num)
          exact Work.Spaces.HkIntegrand_nonneg α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
      _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring
  have hA4bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A4 z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have hpt := (hCz α (fun z : ℝ => 3 / (1 + z)) 100 (by norm_num) hφZop hφsm
      (Work.Spaces.Dth f) hf.Dth).1 z hz θ hθ
    have hD : Work.Spaces.HkIntegrand α 3 (Work.Spaces.Dth f) z θ
        ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      have h := HkIntegrand_mixed_shift α hα 3 1 0 hf z hz θ hθ
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero] using h
    have h4 : A4 = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := hA4
    rw [h4]
    calc Work.Spaces.HkIntegrand α 3
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ) z θ
        ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 3 (Work.Spaces.Dth f) z θ := hpt
      _ ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_le_mul_of_nonneg_left hD (by nlinarith [hCzpos])
      _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by norm_num
  -- the pointwise bound on the closed quadrant
  have hptE : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 E z θ
        ≤ (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
    · rw [← hz0, hE, hA12, hA34, hA1, hA2, hA3, hA4]
      rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
      simp
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [hE, hA12, hA34, hA1, hA2, hA3, hA4,
          Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 3 _ hα hs,
          Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 4 f hα hs]
        rw [mul_zero]
      · have hθ0 : 0 < θ := by
          rcases eq_or_lt_of_le hθ.1 with h | h
          · exact absurd (by rw [← h]; simp) hs
          · exact h
        have hθ1 : θ < π / 2 := by
          rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hs
        have h12 := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA1sm hA2sm
          z hz θ hθ
        have h34 := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA3sm hA4sm
          z hz θ hθ
        have hTop := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA12sm hA34sm
          z hz θ hθ
        have h12' : Work.Spaces.HkIntegrand α 3 A12 z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A1 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A2 z θ := by
          rw [hA12]; exact h12
        have h34' : Work.Spaces.HkIntegrand α 3 A34 z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A3 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A4 z θ := by
          rw [hA34]; exact h34
        have hTop' : Work.Spaces.HkIntegrand α 3 E z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A12 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A34 z θ := by
          rw [hE]; exact hTop
        have e1 := hA1bd z hz θ hθ
        have e2 := hA2bd z hz θ hθ
        have e3 := hA3bd z hz θ hθ
        have e4 := hA4bd z hz θ hθ
        have hH4 : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
          Work.Spaces.HkIntegrand_nonneg α 4 f z θ
        have hC101 : (0 : ℝ) ≤ Cz * 101 ^ 2 :=
          mul_nonneg hCzpos.le (by norm_num)
        linarith [hTop', h12', h34', e1, e2, e3, e4, hH4, hC101,
          mul_nonneg hC101 hH4, mul_nonneg hC101 (mul_nonneg hC101 hH4)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlocOp]; exact hEsm
  · rw [hlocOp]
    refine Work.FTS.LocData.HkMem_of_majorant α 3 (f := E)
      (M := fun z θ => (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) *
        Work.Spaces.HkIntegrand α 4 f z θ)
      ?_ ?_ ?_ hptE
    · exact hEsm.continuousOn_HkIntegrand α 3
    · intro z hz
      exact (hmem.1 z hz).const_mul _
    · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
            (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) * Work.Spaces.HkIntegrand α 4 f z θ)
          = fun z => (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) *
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [h]
      exact hmem.2.const_mul _
  · rw [hlocOp]
    exact HkSq_le_of_pointwise_levels α 3 4 (by nlinarith [hCzpos]) hmem hptE

end Work.FTS.StrongPersist.L3Aux
