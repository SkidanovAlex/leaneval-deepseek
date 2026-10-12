import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.BoseSym.Bridge.aemeas_indicator_of_aesm_on_box
import Submission.Work.BoseSym.Bridge.integrable_and_integral_le_of_tendsto_monotone
import Submission.Work.BoseSym.Form.tendsto_potSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Liminf — the `liminf` bound for the weighted box integral

The main statement of this file, `Work.BoseSym.Liminf.potSq_liminf_box`, is the
lower semicontinuity of the weighted quadratic form along an `L²`-convergent
sequence, for a monotone family of weights `W n ↑ Wlim` with uniformly bounded
box integrals.

The proof does not use Fatou's lemma.  Instead it truncates: for a *bounded*
weight the form `u ↦ ∫ W u²` is continuous on `L²` (this is
`Work.BoseSym.Form.tendsto_potSq`), so for every `n` the truncated weight
`min (W n) n` compares the *limit* integral `∫ min (W n) n · v²` with the
*liminf* of the sequence `k ↦ ∫ W k · (u k)²` (this is the algebraic core,
`key` below).  Monotone convergence (`integrable_and_integral_le_of_tendsto_monotone`)
along the diagonal `k ↦ min (W k) k` then passes to `Wlim`.

## Main results

* `integral_indicator_mul_eq_integralOn` / `intC_indicator_mul_eq_integralOn` :
  the whole-space integral of the box-indicator of a function against another
  function is the integral over the box;
* `potSq_liminf_box` : the target statement.
-/

namespace Work.BoseSym.Liminf

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The whole-space integral of the product of `(box N L).indicator f` with `g` is the
integral of `f * g` over the box. -/
lemma integral_indicator_mul_eq_integralOn {N : ℕ} {L : ℝ} (f g : Work.BoseSym.Conf N → ℝ) :
    ∫ x, (BoseGases.box N L).indicator f x * g x ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseSym.Conf N))
      = ∫ x in BoseGases.box N L, f x * g x := by
  have h := integral_indicator
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseSym.Conf N)))
    (s := BoseGases.box N L)
    (f := fun x : Work.BoseSym.Conf N => f x * g x) (Work.BoseSym.Bridge.measurableSet_box N L)
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_mul])

/-- `intC`-version of `integral_indicator_mul_eq_integralOn`. -/
lemma intC_indicator_mul_eq_integralOn {N : ℕ} {L : ℝ} (f g : Work.BoseSym.Conf N → ℝ) :
    Work.BoseSym.intC N (fun x => (BoseGases.box N L).indicator f x * g x)
      = ∫ x in BoseGases.box N L, f x * g x := by
  rw [Work.BoseSym.intC]
  exact integral_indicator_mul_eq_integralOn f g

theorem potSq_liminf_box {N : ℕ} {L : ℝ} {C' : ℝ}
    {W : ℕ → Work.BoseSym.Conf N → ℝ} {Wlim : Work.BoseSym.Conf N → ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWlim0 : 0 ≤ Wlim)
    (hWm : ∀ n, MeasureTheory.AEStronglyMeasurable (W n)
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWlimm : MeasureTheory.AEStronglyMeasurable Wlim
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWmono : ∀ n x, W n x ≤ W (n + 1) x)
    (hWtend : ∀ x, Filter.Tendsto (fun n => W n x) Filter.atTop (nhds (Wlim x)))
    {u : ℕ → Work.BoseSym.L2 N} {v : Work.BoseSym.L2 N}
    (hu : Work.BoseSym.TendstoL2 N u v)
    (hC'i : ∀ n, MeasureTheory.IntegrableOn
      (fun x => W n x * ((u n : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    (hC'b : ∀ n, ∫ x in BoseGases.box N L,
        W n x * ((u n : Work.BoseSym.Conf N → ℝ) x) ^ 2 ≤ C') :
    MeasureTheory.IntegrableOn
        (fun x => Wlim x * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        (BoseGases.box N L) MeasureTheory.volume ∧
      ∫ x in BoseGases.box N L, Wlim x * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2
        ≤ Filter.liminf (fun n => ∫ x in BoseGases.box N L,
            W n x * ((u n : Work.BoseSym.Conf N → ℝ) x) ^ 2) Filter.atTop := by
  classical
  -- ## Notation
  set A : ℕ → ℝ := fun n => ∫ x in BoseGases.box N L,
      W n x * ((u n : Work.BoseSym.Conf N → ℝ) x) ^ 2 with hA
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    rw [hA]
    exact integral_nonneg fun x => mul_nonneg (hW0 n x) (sq_nonneg _)
  have hAc : ∀ n, A n ≤ C' := by
    intro n
    rw [hA]
    exact hC'b n
  -- ## Step A
  have key : ∀ n : ℕ, ∫ x in BoseGases.box N L,
      min (W n x) (n : ℝ) * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2
      ≤ Filter.liminf A Filter.atTop := by
    intro n
    have hWnsm : MeasureTheory.AEStronglyMeasurable
        (fun x : Work.BoseSym.Conf N => min (W n x) (n : ℝ))
        (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
      ((hWm n).aemeasurable.min aestronglyMeasurable_const.aemeasurable).aestronglyMeasurable
    have hindm : AEMeasurable (fun x : Work.BoseSym.Conf N =>
        (BoseGases.box N L).indicator (fun y => min (W n y) (n : ℝ)) x)
        (Work.BoseSym.volC N) :=
      Work.BoseSym.Bridge.aemeas_indicator_of_aesm_on_box hWnsm
    have hbdd : Work.BoseSym.BddBy N (fun x : Work.BoseSym.Conf N =>
        (BoseGases.box N L).indicator (fun y => min (W n y) (n : ℝ)) x) (n : ℝ) := by
      intro x
      by_cases hx : x ∈ BoseGases.box N L
      · simp only [Set.indicator_of_mem hx]
        rw [abs_of_nonneg (le_min (hW0 n x) (Nat.cast_nonneg n))]
        exact min_le_right _ _
      · simp only [Set.indicator_of_notMem hx]
        rw [abs_zero]
        exact Nat.cast_nonneg n
    have hcv := Work.BoseSym.Form.tendsto_potSq (N := N) hbdd hindm hu
    have hcv' : Filter.Tendsto (fun k : ℕ => ∫ x in BoseGases.box N L,
          min (W n x) (n : ℝ) * ((u k : Work.BoseSym.Conf N → ℝ) x) ^ 2) Filter.atTop
        (nhds (∫ x in BoseGases.box N L,
          min (W n x) (n : ℝ) * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2)) := by
      simpa only [Work.BoseSym.TendstoR, intC_indicator_mul_eq_integralOn] using hcv
    have hlim1 : Filter.liminf (fun k : ℕ => ∫ x in BoseGases.box N L,
          min (W n x) (n : ℝ) * ((u k : Work.BoseSym.Conf N → ℝ) x) ^ 2) Filter.atTop
        = ∫ x in BoseGases.box N L,
          min (W n x) (n : ℝ) * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2 :=
      hcv'.liminf_eq
    -- eventual domination by `A k`
    have hleW : ∀ k, n ≤ k → ∀ x : Work.BoseSym.Conf N, min (W n x) (n : ℝ) ≤ W k x :=
      fun k hk x => le_trans (min_le_left _ _)
        (monotone_nat_of_le_succ (fun i => hWmono i x) hk)
    have hev : ∀ᶠ k in Filter.atTop, (∫ x in BoseGases.box N L,
        min (W n x) (n : ℝ) * ((u k : Work.BoseSym.Conf N → ℝ) x) ^ 2) ≤ A k := by
      refine Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
      rw [hA]
      have hminint : MeasureTheory.IntegrableOn (fun x : Work.BoseSym.Conf N =>
          min (W n x) (n : ℝ) * ((u k : Work.BoseSym.Conf N → ℝ) x) ^ 2)
          (BoseGases.box N L) MeasureTheory.volume := by
        refine Integrable.mono' (hC'i k) ?_ ?_
        · exact (((hWm n).aemeasurable.min aestronglyMeasurable_const.aemeasurable).aestronglyMeasurable.mul
            (((Lp.aestronglyMeasurable (u k)).mono_measure MeasureTheory.Measure.restrict_le_self).pow 2))
        · filter_upwards with x
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (le_min (hW0 n x) (Nat.cast_nonneg n)) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hleW k hk x) (sq_nonneg _)
      exact integral_mono hminint (hC'i k) fun x =>
        mul_le_mul_of_nonneg_right (hleW k hk x) (sq_nonneg _)
    have hmon := Filter.liminf_le_liminf hev
      (by
        simp only [Filter.IsBoundedUnder, Filter.IsBounded, Filter.eventually_map]
        exact ⟨0, Filter.Eventually.of_forall fun k => integral_nonneg fun x =>
          mul_nonneg (le_min (hW0 n x) (Nat.cast_nonneg n)) (sq_nonneg _)⟩)
      (by
        simp only [Filter.IsCoboundedUnder, Filter.IsCobounded, Filter.eventually_map]
        refine ⟨C', fun a ha => ?_⟩
        obtain ⟨k, hk⟩ := (ha.and (Filter.Eventually.of_forall hAc)).exists
        exact le_trans hk.1 hk.2)
    calc ∫ x in BoseGases.box N L,
          min (W n x) (n : ℝ) * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2
        = Filter.liminf (fun k : ℕ => ∫ x in BoseGases.box N L,
            min (W n x) (n : ℝ) * ((u k : Work.BoseSym.Conf N → ℝ) x) ^ 2) Filter.atTop :=
          hlim1.symm
      _ ≤ Filter.liminf A Filter.atTop := hmon
  -- ## Step B: monotone convergence along the diagonal `k ↦ (k, k)`
  have hmct := Work.BoseSym.Bridge.integrable_and_integral_le_of_tendsto_monotone (N := N)
    (f := fun k x => (BoseGases.box N L).indicator (fun y => min (W k y) (k : ℝ)) x
      * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2)
    (g := fun x => (BoseGases.box N L).indicator Wlim x
      * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2)
    (c := Filter.liminf A Filter.atTop)
    (fun k => Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ BoseGases.box N L
      · simp only [Set.indicator_of_mem hx]
        exact mul_nonneg (le_min (hW0 k x) (Nat.cast_nonneg k)) (sq_nonneg _)
      · simp only [Set.indicator_of_notMem hx, zero_mul, le_refl])
    (fun k x => by
      by_cases hx : x ∈ BoseGases.box N L
      · simp only [Set.indicator_of_mem hx]
        exact mul_le_mul_of_nonneg_right
          (min_le_min (hWmono k x) (by push_cast; linarith)) (sq_nonneg _)
      · simp only [Set.indicator_of_notMem hx, zero_mul, le_refl])
    ((AEMeasurable.mul (Work.BoseSym.Bridge.aemeas_indicator_of_aesm_on_box hWlimm)
      (((Lp.aestronglyMeasurable v).pow 2).aemeasurable)).congr
        (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.pow_apply]))
    (fun x => by
      by_cases hx : x ∈ BoseGases.box N L
      · simp only [Set.indicator_of_mem hx]
        have hle : ∀ k, W k x ≤ Wlim x := fun k =>
          le_of_tendsto_of_tendsto tendsto_const_nhds (hWtend x)
            (Filter.eventually_atTop.mpr ⟨k, fun m hm =>
              monotone_nat_of_le_succ (fun i => hWmono i x) hm⟩)
        obtain ⟨K, hK⟩ := exists_nat_ge (Wlim x)
        have heq : (fun k : ℕ => min (W k x) ((k : ℕ) : ℝ)) =ᶠ[Filter.atTop]
            (fun k : ℕ => W k x) := by
          filter_upwards [Filter.eventually_ge_atTop K] with k hk
          exact min_eq_left (le_trans (hle k) (le_trans hK (by exact_mod_cast hk)))
        exact (Tendsto.congr' heq.symm (hWtend x)).mul_const _
      · simp only [Set.indicator_of_notMem hx, zero_mul]
        exact tendsto_const_nhds)
    (fun k => by
      have hbase : Integrable (fun x : Work.BoseSym.Conf N =>
          ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2) (Work.BoseSym.volC N) :=
        (Lp.memLp v).integrable_sq
      have hdom : Integrable (fun x : Work.BoseSym.Conf N =>
          (k : ℝ) * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2) (Work.BoseSym.volC N) :=
        hbase.const_mul (k : ℝ)
      refine Integrable.mono' hdom ?_ ?_
      · exact ((Work.BoseSym.Bridge.aemeas_indicator_of_aesm_on_box
          (((hWm k).aemeasurable.min aestronglyMeasurable_const.aemeasurable).aestronglyMeasurable)).aestronglyMeasurable).mul
          ((Lp.aestronglyMeasurable v).pow 2)
      · filter_upwards with x
        by_cases hx : x ∈ BoseGases.box N L
        · simp only [Set.indicator_of_mem hx]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (le_min (hW0 k x) (Nat.cast_nonneg k)) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        · simp only [Set.indicator_of_notMem hx, zero_mul]
          rw [Real.norm_eq_abs, abs_zero]
          exact mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _))
    (fun k => by
      show (∫ x, (BoseGases.box N L).indicator (fun y => min (W k y) ((k : ℕ) : ℝ)) x
          * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2 ∂(Work.BoseSym.volC N))
        ≤ Filter.liminf A Filter.atTop
      rw [integral_indicator_mul_eq_integralOn]
      exact key k)
  obtain ⟨hIntg, hIntle⟩ := hmct
  -- ## Step C: back to the box
  refine ⟨?_, ?_⟩
  · rw [← MeasureTheory.integrable_indicator_iff
      (Work.BoseSym.Bridge.measurableSet_box N L)]
    refine hIntg.congr (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  · calc ∫ x in BoseGases.box N L, Wlim x * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2
        = ∫ x, (BoseGases.box N L).indicator
            (fun x : Work.BoseSym.Conf N => Wlim x * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2) x :=
          (integral_indicator (Work.BoseSym.Bridge.measurableSet_box N L)).symm
      _ = ∫ x, (BoseGases.box N L).indicator Wlim x
            * ((v : Work.BoseSym.Conf N → ℝ) x) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ BoseGases.box N L
          · simp only [Set.indicator_of_mem hx]
          · simp only [Set.indicator_of_notMem hx, zero_mul]
      _ ≤ Filter.liminf A Filter.atTop := hIntle

end

end Work.BoseSym.Liminf
