/-
# `Work.FTS.StrongPersist.IP6_lo_coeffs` — the `lo` clause of `H6Coer` for the concrete `IP6`

The clause `H6Coer.lo` of `Defs.lean` asks for the domination of the squared `ℋ⁶`-norm by the
diagonal of the concrete pairing,

  `Sq6 α f ≤ IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f`,

on the coercivity class `H6Adm α f`.  This file proves the **coefficient-wise** form: for
*arbitrary* coefficients `≥ 1` the domination holds on the honest class `HQo α 6 f`
(interior `C^∞` plus `ℋ⁶`-honesty, the `reg` field of `H6Adm` alone — no `VanishTheta`, no axis
conditions, no projector condition).

## Why the bound is coefficient-free at level six

`IP6` is the recursion `HkIPStep c₁ c₂ IP f g = IP f g + c₁ IP (D_θf) (D_θg) + c₂ IP (D_zf) (D_zg)`
applied five times on top of `H1IP`, and each application of `HkIPStep` *adds* the two shifted
diagonals.  The mandatory input is the coercivity of the `ℋ^k`-norm along the recursion,

  `HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (D_θf) + HkSq α k (D_zf)`,

which, together with the induction hypothesis at the three slots and `c₁, c₂ ≥ 1`
(so that the shifted diagonals, nonnegative by the induction hypothesis, may be enlarged),
gives the level-`(k+1)` statement with the *same* constant.  Since the base
`HkSq α 1 f ≤ H1IP α f f` holds with constant one (the four coefficients of `H1IP` are
`10, 10^10, 10^17, 10^21`), the five steps produce constant one.

## What is new here

The coercivity of the `ℋ^k`-norm exists in the tree only in the *analytic* class `SmoothNbhd`
(`Work.Coercivity.HkSq_succ_le_of_smooth`) or in the class `SmoothQuad` with the *closed*
quadrant replaced by the strip `(-1,∞) × (0,π/2)`
(`CoercivityFix.Assembly.HkSq_succ_le_Q`).  The honest solutions of the strong route are only
`C^∞` on the *open* quadrant, so this file re-proves

* the pointwise integrand comparison `HkIntegrand α (k+1) f ≤ Σ_{slots} HkIntegrand α k`
  in the open class (`Q0Sm`, finite-order `C^k` on the open quadrant), first on the open
  quadrant and then on the closed quadrant, where both sides vanish on the two exceptional
  lines (`z = 0` and `sin 2θ = 0`);
* its integrated form `HkSq_succ_le_SO`;
* the base `HkSq α 1 f ≤ H1IP α f f` in the open class;
* the recursion step `lo_step_SO`, with the constant `1`;
* the five-fold iteration, ending in `IP6`.

All the descent and domination input is the `Q0Sm`-layer of
`Submission/Work/FTS/CoercivityFix/Transfer/` (`HkMem_descent_Q0Sm`,
`HkIntegrand_Dz_le_succ_Q0Sm`, `mixed_Dz_shift_Q0Sm`) together with the open-quadrant API of
`Submission/Work/FTS/EllipticEst/OpenQDefs.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.ClauseFields
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkIntegrand_Dz_le_succ_Q0Sm
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Coercivity.HkSq_succ_le_of_smooth
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.HkIntegrand_succ_le_sum
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The smoothness bridge -/

/-- **`SmoothOpen` is `Q0Sm` at every order.**  `Q0Sm k X` is finite-order `C^k`-smoothness on
the open quadrant `(0,∞) × (0,π/2)`, and `SmoothOpen X` is `C^∞` on the same set. -/
theorem q0Sm_of_smoothOpen {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm k f :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf k

/-! ## The pointwise comparison of consecutive `ℋ`-integrands in the open class -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`
(the extra term being `F 0`). -/
private lemma sumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- The pure `D_z`-family grows by one summand: the sum over `range (k+2)` is dominated by the
sum over `range (k+1)` plus the shifted sum. -/
private lemma sum_range_succ_le_self_add_shift (te : ℕ → ℝ) (h : ∀ i, 0 ≤ te i) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 2), te i)
      ≤ (∑ i ∈ Finset.range (k + 1), te i) + ∑ i ∈ Finset.range (k + 1), te (i + 1) := by
  rw [Finset.sum_range_succ (f := te) (n := k + 1)]
  have h1 : te (k + 1) ≤ ∑ i ∈ Finset.range (k + 1), te (i + 1) :=
    Finset.single_le_sum (f := fun i => te (i + 1)) (fun i _ => h (i + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  linarith

/-- **Coercivity of the `ℋ^k`-integrand on the open quadrant.**  For `k ≥ 1` and `f` of class
`Q0Sm (k+1)` (finite-order `C^{k+1}` on the open quadrant) the `(k+1)`-st `ℋ`-integrand is
pointwise dominated at every point of the open quadrant by the sum of the `k`-th integrands of
`f`, `D_θ f` and `D_z f`.

This is `CoercivityFix.Assembly.HkIntegrand_succ_le_sum_Q` with the `SmoothQuad`-hypothesis (and
its two closed-quadrant commutation inputs) replaced by their open-quadrant counterparts
`mixed_Dz_shift_Q0Sm` and `QuadPorts.mixed_Dth_shift`. -/
theorem HkIntegrand_succ_le_sum_Qd (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f : Fn}
    (hf : Work.FTS.CoercivityFix.Transfer.Q0Sm (k + 1) f) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.HkIntegrand α (k + 1) f z θ
      ≤ Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ := by
  simp only [Work.Spaces.HkIntegrand]
  -- the two fixed weights, isolated so that the sums of squares are honest
  set A : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hA
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  -- the curvilinear derivatives pick up exactly one more factor
  have hDzIter : ∀ i, Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
      = Work.Spaces.DzIter (i + 1) f z θ :=
    fun i => by
      show Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter i f) z θ
      rw [show Work.Spaces.DzIter i (Work.Spaces.Dz f)
            = Work.Spaces.Dz (Work.Spaces.DzIter i f) from by
          simpa using (Work.Spaces.DzIter_add_right i 1 f).symm]
  have hmixDz : ∀ j i : ℕ, i + 1 ≤ k + 1 →
      Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
        = Work.Spaces.mixed (j + 1) i f z θ :=
    fun j i hi => Work.FTS.CoercivityFix.Transfer.mixed_Dz_shift_Q0Sm hf (a := i) hi j z θ hzθ
  have hmixDth : ∀ j i : ℕ, Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ :=
    fun j i => by rw [Work.FTS.CoercivityFix.QuadPorts.mixed_Dth_shift j i f]
  -- rewrite the three summands of the right-hand side into the common index form
  have hBpure : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * A) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * A) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [hDzIter i]
  have hBmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDz j i (by have := Finset.mem_range.mp hi; omega)]
  have hCmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDth j i]
  rw [hBpure, hBmixed, hCmixed]
  -- pure part: two consecutive levels of `D_z` cover `P_{k+1}`
  have hI := sum_range_succ_le_self_add_shift
    (fun i => (Work.Spaces.DzIter i f z θ * A) ^ 2) (fun i => sq_nonneg _) k
  -- mixed part: the combinatorial triangle inequality
  have hII := Work.Coercivity.mixed_index_sum_le k hk
    (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  -- the pure family of `D_θ f` only helps
  have hDthnonneg : 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * A) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- `HkIntegrand` vanishes at every angle with `sin(2θ) = 0`, for every function: the pure
weight carries the factor `sin(2θ)^{-η/2}` and the mixed weight the factor `sin(2θ)^{-γ/2}`,
both of which are `0` at `sin(2θ) = 0` (`η/2 > 0`, `γ/2 > 0`). -/
theorem HkIntegrand_eq_zero_of_sin_zero {α : ℝ} (hα : 0 < α) {k : ℕ} {g : Fn}
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k g z θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs]
    exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
  have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hs]
    refine Real.zero_rpow ?_
    have hg : 0 < Work.Spaces.gam α := by
      simp only [Work.Spaces.gam]
      linarith
    linarith
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, h1, h2, div_zero,
    mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

/-- **Coercivity of the `ℋ^k`-integrand on the closed quadrant**, in the open smoothness class.
The pointwise comparison holds at every point of `Iz × Iθ`: in the interior it is
`HkIntegrand_succ_le_sum_Qd`, and on the two exceptional lines `z = 0` and `sin 2θ = 0` both
sides vanish. -/
theorem HkIntegrand_succ_le_sum_SO (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : Fn}
    (hf : Work.FTS.CoercivityFix.Transfer.Q0Sm (k + 1) f) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α (k + 1) f z θ
      ≤ Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    rw [Work.Spaces.HkIntegrand_zero_z, Work.Spaces.HkIntegrand_zero_z,
      Work.Spaces.HkIntegrand_zero_z, Work.Spaces.HkIntegrand_zero_z]
    norm_num
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact HkIntegrand_succ_le_sum_Qd α k hk hf ⟨hzpos, hθin⟩
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rw [HkIntegrand_eq_zero_of_sin_zero hα hs, HkIntegrand_eq_zero_of_sin_zero hα hs,
        HkIntegrand_eq_zero_of_sin_zero hα hs, HkIntegrand_eq_zero_of_sin_zero hα hs]
      norm_num

/-! ## The integrated form on the honest class -/

/-- **`HkSq α (k+1) f ≤ HkSq α k f + HkSq α k (D_θf) + HkSq α k (D_zf)`**, for `k ≥ 1`, `0 < α`
and `f` of the class `C^{k+1}`-on-the-open-quadrant and honest `ℋ^{k+1}`-integral.  The
integration is `Work.Coercivity.HkSq_le_sum_of_integrand_le`, whose three membership hypotheses
on the right are supplied by the `Q0Sm`-descent `HkMem_descent_Q0Sm`. -/
theorem HkSq_succ_le_SO {α : ℝ} (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k) {f : Fn}
    (hf : Work.FTS.CoercivityFix.Transfer.Q0Sm (k + 1) f)
    (hm : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkSq α (k + 1) f
      ≤ Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k (Work.Spaces.Dth f)
        + Work.Spaces.HkSq α k (Work.Spaces.Dz f) := by
  obtain ⟨hm0, hm1, hm2⟩ :=
    Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα k hf hm
  exact Work.Coercivity.HkSq_le_sum_of_integrand_le α (k + 1) k hm hm0 hm1 hm2
    (fun z hz θ hθ => HkIntegrand_succ_le_sum_SO α hα k hk hf hz hθ)

/-! ## The base of the recursion: `HkSq α 1 f ≤ H1IP α f f` -/

/-- Continuity of the angular weight `Wt α` on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Set.mem_prod.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-- **The `ℋ¹`-identity in the open class**: `|f|²_{ℋ¹} = E_{z,θ}¹(f)`.  This is
`CoercivityFix.Coer1.HkSq_one_eq` with the `SmoothQuad`-hypothesis replaced by `SmoothOpen`, the
only use of smoothness being the continuity (hence a.e. strong measurability) of the three
summands of the `ℋ¹`-integrand on the open quadrant. -/
theorem HkSq_one_eq_SO (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.HkSq α 1 f
      = Work.Coercivity.EfEta f + Work.Coercivity.EDz f + Work.Coercivity.EDth α f := by
  -- continuity of the three summands on the open quadrant
  have hU0c : ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hs.continuousOn_summand 0).pow 2)
  have hU1c : ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U1 f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hs.continuousOn_summand 1).pow 2)
  have hU2c : ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U2 α f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (((hs.mixed 0 1).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
  have hL0 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U0 f z θ) ^ 2) :=
    Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 1 hm hU0c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))
  have hL1 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U1 f z θ) ^ 2) :=
    Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 1 hm hU1c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 1 (by norm_num))
  have hL2 : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U2 α f z θ) ^ 2) :=
    Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 1 hm hU2c
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num)
        (by norm_num))
  have hsplit : Work.Spaces.HkSq α 1 f
      = Work.Spaces.L2Sq (Work.Coercivity.U0 f) + Work.Spaces.L2Sq (Work.Coercivity.U1 f)
        + Work.Spaces.L2Sq (Work.Coercivity.U2 α f) := by
    rw [Work.Spaces.HkSq]
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ((Work.Coercivity.U0 f z θ) ^ 2 + (Work.Coercivity.U1 f z θ) ^ 2
              + (Work.Coercivity.U2 α f z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      exact Work.Coercivity.hkIntegrand_one_split α f z θ
    rw [h1]
    have hadd := Work.Coercivity.iterated_integral_add3
      (A := fun z θ => (Work.Coercivity.U0 f z θ) ^ 2)
      (B := fun z θ => (Work.Coercivity.U1 f z θ) ^ 2)
      (C := fun z θ => (Work.Coercivity.U2 α f z θ) ^ 2) hL0 hL1 hL2
    rw [hadd]
    simp only [Work.Spaces.L2Sq]
  rw [hsplit, Work.Coercivity.L2Sq_U0_eq_EfEta, Work.Coercivity.L2Sq_U1_eq_EDz,
    Work.Coercivity.L2Sq_U2_eq_EDth]

/-- **The base of the recursion**: the `ℋ¹` inner product `H1IP α` dominates the squared
`ℋ¹`-norm on the open honest class.  The proof is that of `Assembly.H1IP_le_self_Q` with the
`ℋ¹`-identity taken from the open class (`HkSq_one_eq_SO`). -/
theorem H1IP_le_self_SO {α : ℝ} {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.HkSq α 1 f ≤ Work.Coercivity.H1IP α f f := by
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Work.Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hA : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hB : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hC : 0 ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f :=
    Work.Coercivity.wip_self_nonneg (fun z _ _ => sq_nonneg _)
  have hD : 0 ≤ Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    Work.Coercivity.wip_self_nonneg
      (fun z θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  rw [HkSq_one_eq_SO α hs hm, Work.Coercivity.EDz_eq_wip, Work.Coercivity.EfEta_eq_wip,
    Work.Coercivity.EDth_eq_wip]
  unfold Work.Coercivity.H1IP
  linarith [hA, hB, hC, hD]

/-! ## The recursion step -/

/-- **One step of the recursion, with coefficients `≥ 1`.**  If the level-`k` pairing dominates
the squared `ℋ^k`-norm on the open honest class, then `HkIPStep c₁ c₂ IP` dominates the squared
`ℋ^{k+1}`-norm there, *with the same constant*, as soon as `c₁, c₂ ≥ 1`: the two shifted
diagonals are nonnegative (they dominate the two shifted norms, by the induction hypothesis). -/
theorem lo_step_SO {α : ℝ} (hα : 0 < α) {k : ℕ} (hk : 1 ≤ k) {IP : Fn → Fn → ℝ}
    {c₁ c₂ : ℝ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hIP : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α k g →
      Work.Spaces.HkSq α k g ≤ IP g g) :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 1) f →
      Work.Spaces.HkSq α (k + 1) f ≤ Work.Coercivity.HkIPStep c₁ c₂ IP f f := by
  intro f hs hm
  obtain ⟨hm0, hm1, hm2⟩ :=
    Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα k (q0Sm_of_smoothOpen hs (k + 1)) hm
  have hsucc := HkSq_succ_le_SO hα k hk (q0Sm_of_smoothOpen hs (k + 1)) hm
  have e0 := hIP f hs hm0
  have e1 := hIP (Work.Spaces.Dth f) hs.Dth hm1
  have e2 := hIP (Work.Spaces.Dz f) hs.Dz hm2
  have n1 : 0 ≤ IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) :=
    le_trans (Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dth f)) e1
  have n2 : 0 ≤ IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) :=
    le_trans (Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz f)) e2
  have m1 : IP (Work.Spaces.Dth f) (Work.Spaces.Dth f)
      ≤ c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) := le_mul_of_one_le_left n1 hc₁
  have m2 : IP (Work.Spaces.Dz f) (Work.Spaces.Dz f)
      ≤ c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) := le_mul_of_one_le_left n2 hc₂
  rw [Work.Coercivity.HkIPStep]
  linarith [hsucc, e0, e1, e2, m1, m2]

/-! ## The five-fold iteration and the target -/

/-- The five recurrences with explicit coefficient pairs, in the order in which `IP6` nests
them: `(c₁,c₂)` at level two, `(c₁',c₂')` at level three, `(c₁'',c₂'')` at level four,
`(f₁,f₂)` at level five and `(e₁,e₂)` at level six. -/
theorem lo_six {e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ} (hα : 0 < α)
    (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hf₁ : 1 ≤ f₁) (hf₂ : 1 ≤ f₂)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hc₁' : 1 ≤ c₁') (hc₂' : 1 ≤ c₂') (hc₁'' : 1 ≤ c₁'')
    (hc₂'' : 1 ≤ c₂'') :
    ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkSq α 6 f
        ≤ Work.Coercivity.HkIPStep e₁ e₂
            (Work.Coercivity.HkIPStep f₁ f₂
              (Work.Coercivity.HkIPStep c₁'' c₂''
                (Work.Coercivity.HkIPStep c₁' c₂'
                  (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))))) f f := by
  have b1 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 1 g →
      Work.Spaces.HkSq α 1 g ≤ Work.Coercivity.H1IP α g g :=
    fun g hg hmg => H1IP_le_self_SO hg hmg
  have b2 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 2 g →
      Work.Spaces.HkSq α 2 g
        ≤ Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α) g g :=
    lo_step_SO hα (k := 1) le_rfl hc₁ hc₂ b1
  have b3 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkSq α 3 g
        ≤ Work.Coercivity.HkIPStep c₁' c₂'
            (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)) g g :=
    lo_step_SO hα (k := 2) (by norm_num) hc₁' hc₂' b2
  have b4 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkSq α 4 g
        ≤ Work.Coercivity.HkIPStep c₁'' c₂''
            (Work.Coercivity.HkIPStep c₁' c₂'
              (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))) g g :=
    lo_step_SO hα (k := 3) (by norm_num) hc₁'' hc₂'' b3
  have b5 : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g →
      Work.Spaces.HkSq α 5 g
        ≤ Work.Coercivity.HkIPStep f₁ f₂
            (Work.Coercivity.HkIPStep c₁'' c₂''
              (Work.Coercivity.HkIPStep c₁' c₂'
                (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))) g g :=
    lo_step_SO hα (k := 4) (by norm_num) hf₁ hf₂ b4
  exact lo_step_SO hα (k := 5) (by norm_num) he₁ he₂ b5

/-- **The `lo` clause of `H6Coer` for the concrete `IP6`, coefficient-free.**  For arbitrary
coefficients `≥ 1` the squared `ℋ⁶`-norm of an honest `C^∞`-on-the-open-quadrant profile is
dominated by the diagonal of `IP6`. -/
theorem IP6_lo_coeffs {e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ : ℝ}
    (hα₂ : 0 < α₂) (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hf₁ : 1 ≤ f₁) (hf₂ : 1 ≤ f₂)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hc₁' : 1 ≤ c₁') (hc₂' : 1 ≤ c₂') (hc₁'' : 1 ≤ c₁'')
    (hc₂'' : 1 ≤ c₂'') :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 6 f →
      Work.Spaces.HkSq α 6 f
        ≤ Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f f := by
  intro α hα f hQo
  obtain ⟨hs, hm⟩ := hQo
  have h := lo_six (α := α) hα.1 he₁ he₂ hf₁ hf₂ hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂'' f hs hm
  simpa only [Work.FTS.StrongPersist.IP6, Work.FTS.CoercivityFix.Assembly.IP4] using h

end Work.FTS.StrongPersist
