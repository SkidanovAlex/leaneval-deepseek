import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Submission.NeumannBasics
import Submission.Work.BoseSym.Abs.exists_abs_point
import Submission.Work.BoseSym.Bridge.gSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.l2Sq_graphPoint_box
import Submission.Work.BoseSym.Bridge.potSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.tendsto_dirForm
import Submission.Work.BoseSym.Form.gSq_eq_integral
import Submission.Work.BoseSym.Form.l2Sq_eq_integral
import Submission.Work.BoseSym.Trunc.potBox_eventually_le
import Submission.Work.BoseSym.Trunc.smooth_cutoff_family_bounded
import Submission.Work.BoseSym.Trunc.tendsto_toLp_comp
import Submission.Work.BoseSym.Trunc.tendsto_weighted_truncSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — a test function whose Dirichlet quotient is at most that of an
energy-space vector, up to `eta`

Given `p : Hsub N L` with `l2Sq p = 1`, a nonnegative potential `V` integrable on
the box (and with `V * p ^ 2` integrable), and `eta > 0`, there is a smooth test
function `F` supported in the open box with

`(gSq (graphPoint F) + potSq V (graphPoint F)) / l2Sq (graphPoint F)
   ≤ gSq p + ∫_{box} (V * p ^ 2 + eta)`   (the trailing `eta` sits inside the
box integral, as in the statement).

## The argument

`Hsub N L` is the closure of the graph points `F ↦ (F, ∇F)` of the test
functions, so take `G n` with `graphPoint G n → p` in the ambient norm.  The
naive sequence `G n` need not have potential energy converging to that of `p`
(the weight `V` is only assumed integrable, hence unbounded).  The remedy is to
apply a *bounded smooth truncation* `ψ = ψ_{n₀}` (with `|ψ| ≤ min (|·|, n₀+1)`,
`|ψ'| ≤ 1`, `ψ 0 = 0`) to the approximants, i.e. to use `F n := ψ ∘ G n`:

* `gSq (graphPoint (F n)) ≤ gSq (graphPoint (G n))` by the chain rule and
  `|ψ'| ≤ 1` (Abs.gSq_graphPoint_le);
* `l2Sq (graphPoint (F n)) → ∫ (ψ ∘ p)²`, which tends to `l2Sq p = 1` as the
  truncation level grows (Trunc.tendsto_toLp_comp, Trunc.tendsto_weighted_truncSq);
* `∫_{box} V (ψ ∘ G n)² ≲ ∫_{box} V (ψ ∘ p)² ≤ ∫_{box} V p²`: split the box at
  the level `{V ≤ M'}`; there `V` is bounded so `L²`-convergence transfers by
  Cauchy–Schwarz, while the tail `{V > M'}` is small by integrability of `V`
  (Trunc.potBox_eventually_le).

The level `n₀` is chosen so that `∫ (ψ ∘ p)² ≥ 1/2` and
`(gSq p + ∫ V p²) (1 - ∫ (ψ ∘ p)²) ≤ epsilon/8`; the remaining slack
`eps = eta * |box|` (which is positive as `0 < L`) closes the estimate.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The bridge lemma.**  An element `p` of the Dirichlet energy space with
`l2Sq p = 1` can be approximated, in the sense of the Dirichlet quotient, by a
test function, up to any `eta > 0` — where the slack `eta` sits inside the box
integral of the potential, as in the statement below. -/
theorem exists_testSub_quot_le {N : ℕ} {L : ℝ} (hL : 0 < L) {V : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V)
    (p : Work.BoseSym.Hsub N L) (hp1 : Work.BoseSym.l2Sq ((p : Work.BoseSym.Amb N)) = 1)
    (hint : MeasureTheory.IntegrableOn
      (fun x => V x * (((p : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : Work.BoseSym.testSub N L, Work.BoseSym.l2Sq (Work.BoseSym.graphPoint N L F) ≠ 0 ∧
      (Work.BoseSym.gSq (Work.BoseSym.graphPoint N L F)
          + Work.BoseSym.potSq V (Work.BoseSym.graphPoint N L F))
        / Work.BoseSym.l2Sq (Work.BoseSym.graphPoint N L F)
        ≤ Work.BoseSym.gSq (p : Work.BoseSym.Amb N) + ∫ x in BoseGases.box N L,
            V x * (((p : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 + η := by
  obtain ⟨ψ, hψcd, hψderiv, hψ0, hψle, hψlip, hψbd, hψtend⟩ := Trunc.smooth_cutoff_family_bounded
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = gSq (p : Amb N) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∫ x in BoseGases.box N L,
      (V x * (((p : Amb N).1 : Conf N → ℝ) x) ^ 2 + η) := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = ∫ x in BoseGases.box N L,
      V x * (((p : Amb N).1 : Conf N → ℝ) x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η * (volume (BoseGases.box N L)).toReal := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hεpos : 0 < ε := by
    rw [hε]
    exact mul_pos hη (volume_box_pos (N := N) hL)
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB00 : 0 ≤ B₀ := by
    rw [hB₀]
    exact integral_nonneg fun x => mul_nonneg (hV0 x) (sq_nonneg _)
  -- B = B₀ + ε
  have hvol_lt : volume (BoseGases.box N L) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hpos : 0 < (volume (BoseGases.box N L)).toReal := volume_box_pos (N := N) hL
    rw [htop] at hpos
    simp at hpos
  have hconst_int : IntegrableOn (fun _ : Conf N => η) (BoseGases.box N L) volume := by
    rw [IntegrableOn]
    refine integrable_const_iff.mpr (Or.inr ?_)
    rw [isFiniteMeasure_iff, Measure.restrict_apply_univ]
    exact hvol_lt
  have hBsplit : B = B₀ + ε := by
    rw [hB, hB₀, hε]
    rw [integral_add hint hconst_int, setIntegral_const, measureReal_def]
    ring
  have hAB0 : 0 ≤ A + B₀ := by linarith
  -- ============ Step 1: the level n₀
  have hβlim : Tendsto (fun n => ∫ x, (ψ n (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) atTop
      (nhds 1) := by
    have hbase : (∫ x, (((p : Amb N).1) : Conf N → ℝ) x ^ 2) = 1 := by
      change intC N (fun x => (((p : Amb N).1) : Conf N → ℝ) x ^ 2) = 1
      rw [← Form.l2Sq_eq_integral (p : Amb N), hp1]
    have hint1 : IntegrableOn
        (fun x : Conf N => (fun _ : Conf N => (1 : ℝ)) x
          * ((((p : Amb N).1) : Conf N → ℝ) x) ^ 2) Set.univ volume := by
      rw [IntegrableOn, Measure.restrict_univ]
      simpa using (Lp.memLp ((p : Amb N).1)).integrable_sq
    have h := Trunc.tendsto_weighted_truncSq (N := N) (ψ := ψ)
      (hψc := fun n => (hψcd n).continuous) (hψb := hψle) (hψt := hψtend)
      (s := Set.univ) (W := fun _ : Conf N => (1 : ℝ))
      (f := (((p : Amb N).1) : Conf N → ℝ))
      (hW0 := fun _ => zero_le_one) (hWm := aemeasurable_const)
      (hf := (Lp.aestronglyMeasurable ((p : Amb N).1)).mono_measure Measure.restrict_le_self)
      (hint := hint1)
    simpa [setIntegral_univ, hbase] using h
  have hev1 : ∀ᶠ n in Filter.atTop,
      (1 : ℝ) / 2 ≤ ∫ x, (ψ n (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2 :=
    ((tendsto_order.1 hβlim).1 (1 / 2) (by norm_num)).mono fun n hn => hn.le
  have hev2 : ∀ᶠ n in Filter.atTop,
      (A + B₀) * (1 - ∫ x, (ψ n (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) ≤ ε / 8 := by
    have hδ : 0 < ε / (8 * (A + B₀ + 1)) := by
      apply div_pos hεpos
      linarith [hAB0]
    filter_upwards [hβlim.eventually (Metric.ball_mem_nhds (1 : ℝ) hδ)] with n hn
    rw [Real.dist_eq] at hn
    have hlt : 1 - (∫ x, (ψ n (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) < ε / (8 * (A + B₀ + 1)) := by
      linarith [(abs_lt.mp hn).1]
    calc (A + B₀) * (1 - ∫ x, (ψ n (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
        ≤ (A + B₀) * (ε / (8 * (A + B₀ + 1))) := mul_le_mul_of_nonneg_left hlt.le hAB0
      _ ≤ ε / 8 := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith [hAB0] : (0 : ℝ) < 8 * (A + B₀ + 1))]
          nlinarith [hεpos.le, hAB0]
  obtain ⟨n₀, hβ1, hβ2⟩ := (hev1.and hev2).exists
  -- ============ Step 2: the approximating sequence
  have hG : ∀ n : ℕ, ∃ F : testSub N L,
      hSq (graphPoint N L F - (p : Amb N)) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => Basic.exists_graphPoint_close p (by
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact one_div_pos.mpr (by linarith))
  choose G hGspec using hG
  have hnorm : ∀ n, ‖graphPoint N L (G n) - (p : Amb N)‖ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := by
    intro n
    calc ‖graphPoint N L (G n) - (p : Amb N)‖
        = Real.sqrt (‖graphPoint N L (G n) - (p : Amb N)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hSq (graphPoint N L (G n) - (p : Amb N))) :=
          Real.sqrt_le_sqrt (Abs.norm_sq_le_hSq _)
      _ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := Real.sqrt_le_sqrt (hGspec n)
  have hgtend : Tendsto (fun n => graphPoint N L (G n)) atTop (nhds (p : Amb N)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hnorm ?_
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def] using h1
  have hu_lim : Tendsto (fun n => (graphPoint N L (G n)).1) atTop (nhds ((p : Amb N).1)) :=
    (continuous_fst.tendsto (p : Amb N)).comp hgtend
  -- ============ Step 3: the truncated test functions
  let F : ℕ → testSub N L := fun n =>
    ⟨fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x),
     by
       have hω : ContDiff ℝ ∞ (ψ n₀) := (hψcd n₀).of_le (le_top : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ ⊤)
       have hcd : ContDiff ℝ ∞ (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x)) := by
         simpa [Function.comp_def] using hω.comp (G n).2.1
       exact hcd,
     by
       have hsupp : Function.support (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x))
           ⊆ Function.support (G n : Conf N → ℝ) := by
         intro x hx
         rw [Function.mem_support] at hx ⊢
         intro h0
         exact hx (by rw [h0, hψ0 n₀])
       exact (closure_mono hsupp).trans (G n).2.2⟩
  have hFcoe : ∀ n, ((F n : testSub N L) : Conf N → ℝ)
      = fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x) := fun n => rfl
  -- ============ Step 4a: the chain rule bound
  have hchain : ∀ (n : ℕ) (j : GIdx N) (x : Conf N),
      ‖fderiv ℝ (F n : Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)‖
        ≤ ‖fderiv ℝ (G n : Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)‖ := by
    intro n j x
    rw [hFcoe n]
    have hψd : DifferentiableAt ℝ (ψ n₀) ((G n : Conf N → ℝ) x) :=
      ((hψcd n₀).differentiable (by simp)).differentiableAt
    have hGd : DifferentiableAt ℝ (G n : Conf N → ℝ) x :=
      ((G n).2.1.differentiable (by simp)).differentiableAt
    have hL : fderiv ℝ (ψ n₀) ((G n : Conf N → ℝ) x)
        = (deriv (ψ n₀) ((G n : Conf N → ℝ) x)) • (1 : ℝ →L[ℝ] ℝ) := by
      refine ContinuousLinearMap.ext_ring ?_
      simp
    have hcomp : fderiv ℝ (fun y : Conf N => ψ n₀ ((G n : Conf N → ℝ) y)) x
        (Submission.BoseGases.kcDir N j.1 j.2)
        = (deriv (ψ n₀) ((G n : Conf N → ℝ) x))
            * ((fderiv ℝ (G n : Conf N → ℝ) x) (Submission.BoseGases.kcDir N j.1 j.2)) := by
      have h1 : fderiv ℝ (fun y : Conf N => ψ n₀ ((G n : Conf N → ℝ) y)) x
          = (fderiv ℝ (ψ n₀) ((G n : Conf N → ℝ) x)) ∘SL (fderiv ℝ (G n : Conf N → ℝ) x) := by
        rw [show (fun y : Conf N => ψ n₀ ((G n : Conf N → ℝ) y))
              = (ψ n₀) ∘ (G n : Conf N → ℝ) from rfl]
        exact fderiv_comp x hψd hGd
      rw [h1, ContinuousLinearMap.comp_apply, hL]
      simp [smul_apply]
    rw [hcomp, norm_mul, Real.norm_eq_abs]
    nlinarith [hψderiv n₀ ((G n : Conf N → ℝ) x), norm_nonneg ((fderiv ℝ (G n : Conf N → ℝ) x)
      (Submission.BoseGases.kcDir N j.1 j.2))]
  -- ============ Step 4b: gSq bound and limit
  have hgSq_le : ∀ n, gSq (graphPoint N L (F n)) ≤ gSq (graphPoint N L (G n)) :=
    fun n => Abs.gSq_graphPoint_le (G n) (F n) (hchain n)
  have hgSqlim : Tendsto (fun n => gSq (graphPoint N L (G n))) atTop (nhds A) := by
    have h := (continuous_gSq (N := N)).tendsto (p : Amb N)
    have h2 := h.comp hgtend
    simpa [hA, Function.comp_def] using h2
  -- ============ Step 4c: the denominator
  have hmem_all : ∀ n, MemLp (fun x => ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) 2
      (volC N) := by
    intro n
    refine (Lp.memLp ((graphPoint N L (G n)).1)).mono ?_ ?_
    · exact (hψlip n₀).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hψle n₀ _
  have hmem_v : MemLp (fun x => ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) 2 (volC N) := by
    refine (Lp.memLp ((p : Amb N).1)).mono ?_ ?_
    · exact (hψlip n₀).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hψle n₀ _
  have htoLp := Trunc.tendsto_toLp_comp (ψ := ψ n₀) (hψ0 n₀) (hψlip n₀) hu_lim hmem_all hmem_v
  have htoLp' : Tendsto (fun n => ((graphPoint N L (F n)).1 : L2 N)) atTop
      (nhds (MemLp.toLp (fun x => ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) hmem_v)) := by
    have hcongr : (fun n => ((graphPoint N L (F n)).1 : L2 N))
        = (fun n => MemLp.toLp (fun x => ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x))
            (hmem_all n)) := by
      funext n
      have hmemG : MemLp (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x)) 2 (volC N) :=
        (hψlip n₀).comp_memLp (hψ0 n₀)
          (memLp_of_contDiff_hasCompactSupport (G n).2.1 (hasCompactSupport_of_testFun (G n).2))
      show MemLp.toLp (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x)) hmemG
          = MemLp.toLp (fun x : Conf N =>
              ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) (hmem_all n)
      refine MemLp.toLp_congr _ _ ?_
      have hg : (((graphPoint N L (G n)).1 : Conf N → ℝ)) =ᵐ[volC N] (G n : Conf N → ℝ) :=
        MemLp.coeFn_toLp (memLp_of_contDiff_hasCompactSupport (G n).2.1
          (hasCompactSupport_of_testFun (G n).2))
      exact hg.symm.fun_comp (ψ n₀)
    rw [hcongr]
    exact htoLp
  have hden_lim : Tendsto (fun n => l2Sq (graphPoint N L (F n))) atTop
      (nhds (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)) := by
    have hnorm_conv : Tendsto (fun n => ‖((graphPoint N L (F n)).1 : L2 N)‖) atTop
        (nhds ‖MemLp.toLp (fun x => ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) hmem_v‖) :=
      (continuous_norm.tendsto _).comp htoLp'
    have h2 := hnorm_conv.pow 2
    have hnorm_sq : ‖MemLp.toLp (fun x => ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) hmem_v‖ ^ 2
        = ∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2 := by
      rw [Form.lp_norm_sq_eq_integral_sq]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hmem_v] with x hx
      rw [hx]
    rw [hnorm_sq] at h2
    simpa only [l2Sq] using h2
  -- ============ Step 4d: the potential
  have hBψ_le : (∫ x in BoseGases.box N L, V x * (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
      ≤ B₀ := by
    rw [hB₀]
    have hsqle : ∀ t : ℝ, (ψ n₀ t) ^ 2 ≤ t ^ 2 := by
      intro t
      calc (ψ n₀ t) ^ 2 = |ψ n₀ t| ^ 2 := (sq_abs _).symm
        _ ≤ |t| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hψle n₀ t) 2
        _ = t ^ 2 := sq_abs t
    have hmeas' : AEStronglyMeasurable
        (fun x : Conf N => ψ n₀ ((((p : Amb N).1) : Conf N → ℝ) x) ^ 2) (volC N) :=
      ((hψlip n₀).continuous.pow 2).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable ((p : Amb N).1))
    refine setIntegral_mono_ae ?_ hint ?_
    · refine Integrable.mono' hint ?_ ?_
      · exact hVint.aestronglyMeasurable.mul
          (hmeas'.mono_measure Measure.restrict_le_self)
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hV0 x) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hsqle _) (hV0 x)
    · filter_upwards with x
      exact mul_le_mul_of_nonneg_left (hsqle _) (hV0 x)
  have hpot_lim : ∀ᶠ n in Filter.atTop, potSq V (graphPoint N L (F n)) ≤ B₀ + ε / 16 := by
    have hψm : Measurable (ψ n₀) := (hψlip n₀).continuous.measurable
    have hC : (0 : ℝ) ≤ (n₀ : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
      linarith
    have hψC : ∀ t, |ψ n₀ t| ≤ (n₀ : ℝ) + 1 := hψbd n₀
    have hψlip' : ∀ a b, |ψ n₀ a - ψ n₀ b| ≤ |a - b| := by
      intro a b
      have h := (hψlip n₀).dist_le_mul a b
      rw [Real.dist_eq, Real.dist_eq] at h
      simpa using h
    have hD2 := Trunc.potBox_eventually_le (N := N) (L := L) (V := V) hV0 hVint hψm hC hψC hψlip'
      hu_lim (ε := ε / 16) (by linarith [hεpos])
    filter_upwards [hD2] with n hn
    rw [potSq_graphPoint_box]
    show (∫ x in BoseGases.box N L, V x * ((F n : Conf N → ℝ) x) ^ 2) ≤ B₀ + ε / 16
    calc (∫ x in BoseGases.box N L, V x * ((F n : Conf N → ℝ) x) ^ 2)
        = ∫ x in BoseGases.box N L,
            V x * (ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) ^ 2 := by
          refine setIntegral_congr_ae (box_closed L).measurableSet ?_
          have hg : (((graphPoint N L (G n)).1 : Conf N → ℝ)) =ᵐ[volC N] (G n : Conf N → ℝ) :=
            MemLp.coeFn_toLp (memLp_of_contDiff_hasCompactSupport (G n).2.1
              (hasCompactSupport_of_testFun (G n).2))
          filter_upwards [hg] with x hx
          intro _
          simp only [hFcoe n, hx]
      _ ≤ (∫ x in BoseGases.box N L, V x * (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
            + ε / 16 := hn
      _ ≤ B₀ + ε / 16 := by linarith [hBψ_le]
  -- ============ Step 5: assembly
  have hc : 0 < ε / (16 * (A + B₀ + ε + 1)) := by
    apply div_pos hεpos
    linarith [hAB0, hεpos.le]
  have hev_l2 : ∀ᶠ n in Filter.atTop,
      (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) - ε / (16 * (A + B₀ + ε + 1))
        ≤ l2Sq (graphPoint N L (F n)) := by
    filter_upwards [hden_lim.eventually (Metric.ball_mem_nhds
      (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) hc)] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).1]
  have hev_g : ∀ᶠ n in Filter.atTop, gSq (graphPoint N L (F n)) ≤ A + ε / 16 := by
    filter_upwards [hgSqlim.eventually (Metric.ball_mem_nhds A (by linarith [hεpos] : (0 : ℝ) < ε / 16))]
      with n hn
    rw [Real.dist_eq] at hn
    have hlt : gSq (graphPoint N L (G n)) < A + ε / 16 := by linarith [(abs_lt.mp hn).2]
    exact le_trans (hgSq_le n) hlt.le
  obtain ⟨n, hn1, hn2, hn3⟩ := (hev_l2.and (hev_g.and hpot_lim)).exists
  refine ⟨F n, ?_, ?_⟩
  · have h2 : ε / (16 * (A + B₀ + ε + 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith [hAB0, hεpos.le] : (0 : ℝ) < 16 * (A + B₀ + ε + 1))]
      linarith [hAB0, hεpos.le]
    have hpos : 0 < l2Sq (graphPoint N L (F n)) := by linarith [hβ1, hn1, h2]
    exact ne_of_gt hpos
  · have h2 : ε / (16 * (A + B₀ + ε + 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith [hAB0, hεpos.le] : (0 : ℝ) < 16 * (A + B₀ + ε + 1))]
      linarith [hAB0, hεpos.le]
    have hpos : 0 < l2Sq (graphPoint N L (F n)) := by linarith [hβ1, hn1, h2]
    rw [div_le_iff₀ hpos]
    rw [hBsplit]
    have hmain : A + B₀ + ε / 8 ≤ (A + (B₀ + ε)) * l2Sq (graphPoint N L (F n)) := by
      have hexp : (A + B₀ + ε) * ((∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
            - ε / (16 * (A + B₀ + ε + 1)))
          = (A + B₀ + ε) * (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
            - (A + B₀ + ε) * (ε / (16 * (A + B₀ + ε + 1))) := by ring
      have hsmall : (A + B₀ + ε) * (ε / (16 * (A + B₀ + ε + 1))) ≤ ε / 16 := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith [hAB0, hεpos.le] : (0 : ℝ) < 16 * (A + B₀ + ε + 1))]
        nlinarith [hεpos.le, hA0, hB00]
      have hslack : A + B₀ + 3 * ε / 8
          ≤ (A + B₀ + ε) * (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) := by
        have h2' : ε * (∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2) ≥ ε / 2 := by
          nlinarith [hβ1, hεpos.le]
        nlinarith [hβ2, h2']
      have hRHS : A + B₀ + ε / 8
          ≤ (A + B₀ + ε) * ((∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
            - ε / (16 * (A + B₀ + ε + 1))) := by
        rw [hexp]
        linarith [hslack, hsmall]
      have hstep : (A + B₀ + ε) * ((∫ x, (ψ n₀ (((p : Amb N).1 : Conf N → ℝ) x)) ^ 2)
            - ε / (16 * (A + B₀ + ε + 1)))
          ≤ (A + (B₀ + ε)) * l2Sq (graphPoint N L (F n)) := by
        rw [show (A + (B₀ + ε)) = (A + B₀ + ε) from by ring]
        exact mul_le_mul_of_nonneg_left hn1 (by linarith [hAB0, hεpos.le])
      linarith [hRHS, hstep]
    linarith [hn2, hn3, hmain]
end

end Work.BoseSym.Bridge
