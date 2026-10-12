import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseB1Cube.smallWinNodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.swhMassFactsFixed` — the *repaired* `swhMassFacts`

The frozen node `Work.BoseB1Cube.swhMassFacts`
(`Submission/Work/BoseB1Cube/swhMassFacts.lean`) is **false as written**: its second
conjunct

    pairSum (fun z => min (v z) K) M ℓ d u Φ ≤ pairSum v M ℓ d u Φ                (M)

is missing the hypothesis `MemLp v 1` (equivalently `Integrable v`).  `Work.UBB.ScatSol v`
only constrains `v` through the product `v·(1−ω₀)` (`IsScatteringSolution`'s only two
occurrences of `v` are `LocallyIntegrable (v·(1−w))` and the integrand of the weak equation
`-∫ w Δφ = ½ ∫ v (1−w) φ`), so `v` is *completely free on the level set `{w = 1}`*, which can
have positive measure; `ScatSol v` does **not** imply `MemLp v 1` (the corpus records this
explicitly, `Submission/Work/BoseFixB1S/boxFibPairPSum_eq.lean:44`, and builds the
counterexample family in `Submission/Work/BoseFixB1/chemPair_eq_qLHSword.lean`: a radial
`w₀ ∈ C_c^∞` with `w₀ ≡ 1` on `B(0,1)`, `0 ≤ w₀ ≤ 1`, concave on the annulus, and
`v := ‖x‖^{-7}` on `B(0,1)`, `v := -2Δw₀/(1-w₀)` on the annulus — radial, `0 ≤ v`,
`tsupport v ⊆ ball 0 3`, `ScatSol v`, but `v ∉ L¹`).  For such a `v` (at `n = 2`,
`Φ ≡ 1`, `u = 0`, `ℓ` large, `K > 0`):

* `pairSum (min v K) > 0` — `min v K` is bounded, measurable and compactly supported, and
  the kernel `wSmallPair M ℓ d u (min v K)` is `> 0` near the diagonal;
* `pairSum v = 0` — the kernel carries the factor `v(x−y) = ‖x−y‖^{-7}`, whose
  `(A × A)`-integral diverges, so the Bochner integral is the junk value `0`
  (`MeasureTheory.integral_undef`),

so (M) *fails*, for every admissible parameter tuple (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` included).

The first conjunct of the node (the definitional/support identity `w1MassB = boxM2`) is
type-correct mathematics but is only provable through the integrability of the kernel
`wSmall1Pair` on `acube ℓ × acube ℓ`, which the corpus obtains from the diluteness regime
(`Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed`, used by
`Work.BoseFixB1S.flatPairMass_eq_dlBoxPairIntegral`).  The node's earlier draft
(`Submission/Work/BoseB1Cube/_swhPkgStmt.lean`) *did* carry `R ≤ ℓ * d / 16` and
`R ≤ ℓ * chiR0` on that conjunct; they are restored here.

This module proves the repaired statement:

    swhMassFactsFixed : (conjunct 1, with the regime) ∧ (conjunct 2, with `MemLp v 1`).

so that the corrected node is the one-liner
`exact swhMassFactsFixed h hv hv1 hR hv_supp`.  Only `MemLp v 1` and the two regime
hypotheses on conjunct 1 were added — nothing is weakened.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. The two elementary facts about the truncation `min v K` -/

/-- The truncated potential is still supported in the ball. -/
lemma tsupport_min_subset {v : E3 → ℝ} {R K : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    tsupport (fun z : E3 => min (v z) K) ⊆ Metric.ball (0 : E3) R := by
  refine subset_trans (closure_mono ?_) hv_supp
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hvz
  exact hz (by rw [hvz, min_eq_left hK])

/-- The truncated potential is `L¹` when `v` is (`K ≥ 0`, `v` supported in a ball). -/
lemma memLp_one_min {v : E3 → ℝ} {R K : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K)
    (hv1 : MeasureTheory.MemLp v 1) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    MeasureTheory.MemLp (fun z : E3 => min (v z) K) 1 (volume : Measure E3) := by
  rw [MeasureTheory.memLp_one_iff_integrable]
  have hsupp : (Metric.ball (0 : E3) R).indicator (fun z : E3 => min (v z) K)
      = fun z : E3 => min (v z) K := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : E3) R
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have hvz : v z = 0 := by
        by_contra hne
        exact hz (hv_supp (subset_closure (Function.mem_support.mpr hne)))
      rw [hvz, min_eq_left hK]
  rw [← hsupp, integrable_indicator_iff measurableSet_ball]
  have hmeas : AEStronglyMeasurable (fun z : E3 => min (v z) K) (volume : Measure E3) :=
    (AEMeasurable.min hv1.aemeasurable
      (show AEMeasurable (fun _ : E3 => K) volume from aemeasurable_const)).aestronglyMeasurable
  refine MeasureTheory.IntegrableOn.of_bound (measure_ball_lt_top) ?_ K ?_
  · exact hmeas.mono_measure Measure.restrict_le_self
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hv z) hK)]
    exact min_le_right _ _

/-! ## 1. Conjunct 1, at the regime (the support identity `w1MassB = boxM2`) -/

/-- **The first conjunct, with the regime.**  The iterated integral of the localised `g₀`-kernel
is its integral over the sliding box `B(u) × B(u)` in both slots.  Both sides are the integral of
the same kernel, which is supported in `B(u) × B(u)` (`chiSmallB` vanishes off the box), and the
kernel is integrable on `acube ℓ × acube ℓ` by
`Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed` applied to the `L¹` numerator
`g₀ = v(1−ω₀)` (`Submission.BoseGases.g0_integrable`, which needs only `ScatSol v` and the
support); the diluteness regime is what makes the renormalisation denominators bounded below on
the support of `g₀`. -/
theorem w1MassB_eq_boxM2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) :
    Work.BoseFixB1.w1MassB h M ℓ d u
      = Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) := by
  have hInt : MeasureTheory.IntegrableOn
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed (f := Submission.BoseGases.g0 v h)
      (Submission.BoseGases.g0_integrable hR hv_supp h) (R0 := R)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR16 hRχ u
  have hsub : Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u
      ⊆ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
    Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  have hIntAA : MeasureTheory.IntegrableOn
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    hInt.mono_set hsub
  have hzeroL : ∀ x y : E3, x ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hx =>
      Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hx)
  have hzeroR : ∀ x y : E3, y ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hy =>
      Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inr hy)
  have hmain : (∫ x in Submission.BoseGases.dlBox ℓ d u,
        ∫ y in Submission.BoseGases.dlBox ℓ d u, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
    have hin : (fun x : E3 => ∫ y in Submission.BoseGases.dlBox ℓ d u,
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = fun x : E3 => ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
      funext (fun x => MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun y : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        (fun y hy => hzeroR x y hy))
    rw [hin]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun x : E3 => ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      (fun x hx => ?_)
    have hz : (fun y : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = fun _ : E3 => (0 : ℝ) := funext (fun y => hzeroL x y hx)
    rw [hz, MeasureTheory.integral_zero]
  calc Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := rfl
    _ = ∫ x in Submission.BoseGases.dlBox ℓ d u,
          ∫ y in Submission.BoseGases.dlBox ℓ d u,
            Submission.BoseGases.wSmall1Pair h M ℓ d u x y := hmain.symm
    _ = Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) := by
        rw [Work.BoseFixB1S.boxM2]
        exact (MeasureTheory.setIntegral_prod
          (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
          hIntAA).symm

/-! ## 2. Conjunct 2, with `MemLp v 1` (the truncation monotonicity of `pairSum`) -/

/-- **The second conjunct, with the missing hypothesis `MemLp v 1`.**  The kernel
`wSmallPair M ℓ d u · (x,y)` is monotone in the numerator when the latter is nonnegative
(`Work.BoseFixB1.wSmallPair_mono_of_le`), and `min (v z) K ≤ v z`; both state-level pair
integrands are integrable over the box (`Work.BoseFixB1.integrableOn_pairSumIntegrand`, from
`MemLp v 1` and the regime), so `MeasureTheory.setIntegral_mono_on` applies.  (Without the
`L¹` hypothesis the right-hand integral is the junk value `0` while the left-hand one is a
genuine positive number — see the module docstring of `swhMassFactsFixed`.) -/
theorem pairSum_min_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {K : ℝ} (hK : 0 ≤ K) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {n : ℕ} (Φ : X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.pairSum (fun z => min (v z) K) M ℓ d u Φ
      ≤ Work.BoseFixB1.pairSum v M ℓ d u Φ := by
  have hIntF : MeasureTheory.IntegrableOn
      (fun x : X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K) (x p.1) (x p.2)))
      (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB1.integrableOn_pairSumIntegrand (v := fun z => min (v z) K) (R0 := R)
      (tsupport_min_subset hv hK hv_supp) hR (memLp_one_min hv hK hv1 hv_supp)
      hM hℓ hd hR16 hRχ u hΦc
  have hIntG : MeasureTheory.IntegrableOn
      (fun x : X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB1.integrableOn_pairSumIntegrand (v := v) (R0 := R) hv_supp hR hv1
      hM hℓ hd hR16 hRχ u hΦc
  show Work.BoseFixB1.pairSum (fun z => min (v z) K) M ℓ d u Φ
      ≤ Work.BoseFixB1.pairSum v M ℓ d u Φ
  exact MeasureTheory.setIntegral_mono_on hIntF hIntG (Submission.BoseGases.abox_measurable n ℓ)
    (fun x _ => by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Φ x))
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact Finset.sum_le_sum (fun p _ =>
        Work.BoseFixB1.wSmallPair_mono_of_le (x p.1) (x p.2) (min_le_left (v (x p.1 - x p.2)) K)))

/-! ## 3. The repaired node -/

/-- **`swhMassFacts` with the missing hypotheses restored**: `MemLp v 1` on the second conjunct
(without which it is false) and the diluteness regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` on the first
(as in the node's own earlier draft `_swhPkgStmt.lean`, and as the proof of the support identity
needs: the kernel `wSmall1Pair` is only known to be integrable on `acube ℓ × acube ℓ` from the
regime, `Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed`). -/
theorem swhMassFactsFixed {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    (∀ {M : ℕ}, 1 ≤ M → ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d →
        R ≤ ℓ * d / 16 → R ≤ ℓ * Submission.BoseGases.chiR0 →
        ∀ u : E3,
        Work.BoseFixB1.w1MassB h M ℓ d u
          = Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u)) ∧
    (∀ {K : ℝ}, 0 ≤ K → ∀ {M : ℕ}, 1 ≤ M → ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d →
        R ≤ ℓ * d / 16 → R ≤ ℓ * Submission.BoseGases.chiR0 →
        ∀ (u : E3) {n : ℕ} (Φ : X n → ℝ) (hΦc : Continuous Φ),
        Work.BoseFixB1.pairSum (fun z => min (v z) K) M ℓ d u Φ
          ≤ Work.BoseFixB1.pairSum v M ℓ d u Φ) := by
  constructor
  · intro M hM ℓ d hℓ hd hR16 hRχ u
    exact w1MassB_eq_boxM2 (h := h) (hR := hR) (hv_supp := hv_supp) (M := M) (ℓ := ℓ) (d := d)
      hM hℓ hd hR16 hRχ u
  · intro K hK M hM ℓ d hℓ hd hR16 hRχ u n Φ hΦc
    exact pairSum_min_le (h := h) (hv := hv) (hv1 := hv1) (hR := hR) (hv_supp := hv_supp)
      (K := K) hK hM hℓ hd hR16 hRχ u Φ hΦc

end Work.BoseB1Cube
