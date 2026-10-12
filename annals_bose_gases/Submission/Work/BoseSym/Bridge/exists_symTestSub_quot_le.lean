import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Abs.exists_abs_point
import Submission.Work.BoseSym.Bridge.ae_eq_zero_off_box
import Submission.Work.BoseSym.Bridge.gSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.integral_Vpot_symAvgF_sq_le_meas
import Submission.Work.BoseSym.Bridge.integral_symAvgF_mul_sq_eq
import Submission.Work.BoseSym.Bridge.l2Sq_graphPoint_box
import Submission.Work.BoseSym.Bridge.potSq_graphPoint_box
import Submission.Work.BoseSym.Bridge.symLp_fixed_of_aeEq
import Submission.Work.BoseSym.Bridge.tendsto_dirForm
import Submission.Work.BoseSym.Bridge.tendsto_integral_sq_sub_trunc
import Submission.Work.BoseSym.Perm.gSq_symAvgAmb_le
import Submission.Work.BoseSym.Trunc.potBox_eventually_le
import Submission.Work.BoseSym.Trunc.smooth_cutoff_family_bounded
import Submission.Work.BoseSym.Trunc.tendsto_toLp_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — the symmetric bridge: an energy-space vector bounds a symmetric test quotient

Given a vector `q` of the Dirichlet energy space `Hsub N L` with `l2Sq q = 1`,
whose function part is almost everywhere equal to its symmetrisation average
(`hqsym`) — i.e. `q` is a bosonic (permutation invariant) state — a nonnegative
pair interaction `v` with `Vpot N v` integrable on the box, `Vpot N v * q²`
integrable on the box, and the bound

  `gSq q + ∫_box (Vpot N v) q² ≤ Q`,

there is a *symmetric* smooth test function `G` supported in the open box with

  `(gSq (graphPoint G) + potSq (Vpot N v) (graphPoint G)) / l2Sq (graphPoint G) ≤ Q + δ`.

This is the bosonic (Perron–Frobenius symmetric) counterpart of
`Bridge.exists_testSub_quot_le`; it is the bridge that lets the fixed-`n`
operator bounds be tested on symmetric trial states.

## Structure of the proof

* `W := symAvgF N (Vpot N v)` is the symmetrisation of the pair interaction; it
  is nonnegative and integrable on the box (`intOnBox_symAvgF`), and for an
  a.e. permutation invariant `f` the identity
  `∫_box W f² = ∫_box (Vpot N v) f²` holds (`integral_symAvgF_mul_sq_eq`),
  while `∫_box V (symAvgF f)² ≤ ∫_box (symAvgF V) f²` always
  (`integral_Vpot_symAvgF_sq_le_meas`).

* As in `exists_testSub_quot_le`, a sequence `G n` of test functions with
  `graphPoint G n → q` is truncated by a smooth bounded cutoff `ψ = ψ_{n₀}`
  (level `n₀` chosen by `exists_cutoff_level` so that the symmetrised
  truncation has large `L²` norm), and the trial state is
  `symTest N L (ψ ∘ G n)`.  Its symmetry is `symAvg_sym`, its denominator is
  controlled by `tendsto_l2Sq_graphPoint_symTest` and its quotient by the
  three estimates above together with `Trunc.potBox_eventually_le`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem aeInvariant_of_aeEq_symAvgF {N : ℕ} {f : Work.BoseSym.Conf N → ℝ}
    (h : Work.BoseSym.AEEq N f (Work.BoseSym.symAvgF N f)) :
    ∀ᵐ x ∂(Work.BoseSym.volC N), ∀ σ : Equiv.Perm (Fin N),
      f (Submission.BoseGases.actPerm N σ x) = f x := by
  rw [Work.BoseSym.AEEq] at h
  rw [Filter.eventually_all]
  intro σ
  have hcomp : (fun x => f (Work.BoseSym.tauPerm N σ x)) =ᵐ[Work.BoseSym.volC N]
      (fun x => Work.BoseSym.symAvgF N f (Work.BoseSym.tauPerm N σ x)) :=
    (Work.BoseSym.measurePreserving_tauPerm N σ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h, hcomp] with x hx hxc
  have hsym : Work.BoseSym.symAvgF N f (Work.BoseSym.tauPerm N σ x)
      = Work.BoseSym.symAvgF N f x := Submission.BoseGases.symAvg_sym (N := N) f σ x
  rw [show Submission.BoseGases.actPerm N σ x = Work.BoseSym.tauPerm N σ x from rfl, hxc, hsym, ← hx]

lemma nonneg_symAvgF {N : ℕ} {f : Work.BoseSym.Conf N → ℝ} (hf : 0 ≤ f) :
    0 ≤ Work.BoseSym.symAvgF N f := by
  intro x
  simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => hf _)

theorem tendsto_l2Sq_graphPoint_symTest {N : ℕ} {L : ℝ} {F : ℕ → Work.BoseSym.testSub N L}
    {w : Work.BoseSym.L2 N}
    (h : Filter.Tendsto (fun n => Work.BoseSym.toLpTest (F n)) Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => Work.BoseSym.l2Sq (Work.BoseSym.graphPoint N L
      (Work.BoseSym.symTest N L (F n)))) Filter.atTop
      (nhds (‖Work.BoseSym.symLp N w‖ ^ 2)) := by
  have h1 : Filter.Tendsto (fun n => Work.BoseSym.symLp N (Work.BoseSym.toLpTest (F n)))
      Filter.atTop (nhds (Work.BoseSym.symLp N w)) :=
    ((Work.BoseSym.symLp N).continuous.tendsto w).comp h
  have h2 : Filter.Tendsto (fun n => ‖Work.BoseSym.symLp N (Work.BoseSym.toLpTest (F n))‖ ^ 2)
      Filter.atTop (nhds (‖Work.BoseSym.symLp N w‖ ^ 2)) :=
    (continuous_norm.pow 2).tendsto _ |>.comp h1
  refine h2.congr' ?_
  filter_upwards with n
  exact (Work.BoseSym.l2Sq_graphPoint_symTest (F n)).symm

lemma exists_cutoff_level {N : ℕ} {f : Work.BoseSym.Conf N → ℝ}
    (hf : MeasureTheory.MemLp f 2 (Work.BoseSym.volC N)) {ψ : ℕ → ℝ → ℝ}
    (hψc : ∀ n, Continuous (ψ n)) (hψb : ∀ n t, |ψ n t| ≤ |t|)
    (hψt : ∀ t, Filter.Tendsto (fun n => ψ n t) Filter.atTop (nhds t))
    (hmem : ∀ n, MeasureTheory.MemLp (fun x => ψ n (f x)) 2 (Work.BoseSym.volC N))
    {u : Work.BoseSym.L2 N} (hu : MeasureTheory.MemLp.toLp f hf = u) (hunu : ‖u‖ = 1)
    (hsym : Work.BoseSym.symLp N u = u) {κ : ℝ} (hκ : 0 < κ) :
    ∃ n₀ : ℕ, 1 - κ ≤ ‖Work.BoseSym.symLp N
      (MeasureTheory.MemLp.toLp (fun x => ψ n₀ (f x)) (hmem n₀))‖ := by
  have hconv := tendsto_integral_sq_sub_trunc hf hψc hψb hψt
  have hnorm2 : ∀ n, ‖MeasureTheory.MemLp.toLp (fun x => ψ n (f x)) (hmem n)
      - MeasureTheory.MemLp.toLp f hf‖ ^ 2 = ∫ x, (ψ n (f x) - f x) ^ 2 := by
    intro n
    have hsub : MeasureTheory.MemLp.toLp (fun x => ψ n (f x)) (hmem n)
        - MeasureTheory.MemLp.toLp f hf
        = MeasureTheory.MemLp.toLp (fun x => ψ n (f x) - f x) ((hmem n).sub hf) := by
      rw [← MeasureTheory.MemLp.toLp_sub (hmem n) hf]
      exact MeasureTheory.MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by
        funext x
        rfl))
    rw [hsub]
    exact norm_sq_toLp_eq_integral _ _
  have hnormlim : Filter.Tendsto (fun n => ‖MeasureTheory.MemLp.toLp (fun x => ψ n (f x))
      (hmem n) - MeasureTheory.MemLp.toLp f hf‖) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n => Real.sqrt (∫ x, (ψ n (f x) - f x) ^ 2))
        Filter.atTop (nhds 0) := by
      have h3 := (Real.continuous_sqrt.tendsto 0).comp hconv
      simpa [Function.comp_def] using h3
    have h1 : Filter.Tendsto (fun n => Real.sqrt (‖MeasureTheory.MemLp.toLp
        (fun x => ψ n (f x)) (hmem n) - MeasureTheory.MemLp.toLp f hf‖ ^ 2))
        Filter.atTop (nhds 0) :=
      h2.congr' (Filter.Eventually.of_forall fun n => by simp only [hnorm2 n])
    refine h1.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ‖MeasureTheory.MemLp.toLp (fun x => ψ n₀ (f x)) (hmem n₀)
      - MeasureTheory.MemLp.toLp f hf‖ ≤ κ / 4 := by
    obtain ⟨n₀, hn₀⟩ := (hnormlim.eventually (Iio_mem_nhds (by linarith : (0:ℝ) < κ/4))).exists
    exact ⟨n₀, hn₀.le⟩
  refine ⟨n₀, ?_⟩
  set w := MeasureTheory.MemLp.toLp (fun x => ψ n₀ (f x)) (hmem n₀) with hwdef
  have hdw : ‖w - u‖ ≤ κ / 4 := by
    rw [← hu, hwdef]
    exact hn₀
  have hsplit : Work.BoseSym.symLp N u - Work.BoseSym.symLp N w
      = Work.BoseSym.symLp N (u - w) := (map_sub _ _ _).symm
  have hb : ‖Work.BoseSym.symLp N u - Work.BoseSym.symLp N w‖ ≤ κ / 4 := by
    rw [hsplit]
    refine le_trans (Work.BoseSym.norm_symLp_le _) ?_
    rw [norm_sub_rev]
    exact hdw
  have hb' : |‖Work.BoseSym.symLp N u‖ - ‖Work.BoseSym.symLp N w‖| ≤ κ / 4 :=
    le_trans (abs_norm_sub_norm_le _ _) hb
  rw [hsym, hunu] at hb'
  have h2 : (1 : ℝ) - ‖Work.BoseSym.symLp N w‖ ≤ κ / 4 := (abs_le.mp hb').2
  have h3 : (1 : ℝ) - κ ≤ ‖Work.BoseSym.symLp N w‖ := by linarith [hκ.le]
  rw [hwdef] at h3
  exact h3


theorem exists_symTestSub_quot_le {N : ℕ} {L : ℝ} (hL : 0 < L) {v : Work.BoseSym.E3 → ℝ}
    (hv : 0 ≤ v) (hV : Work.BoseSym.IntOnBox N L (Work.BoseSym.Vpot N v))
    (q : Work.BoseSym.Hsub N L) (hq1 : Work.BoseSym.l2Sq ((q : Work.BoseSym.Amb N)) = 1)
    (hqsym : Work.BoseSym.AEEq N (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ))
      (Work.BoseSym.symAvgF N (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ))))
    (hqint : MeasureTheory.IntegrableOn
      (fun x => Work.BoseSym.Vpot N v x * ((((q : Work.BoseSym.Amb N).1) : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    {Q δ : ℝ} (hQ : Work.BoseSym.gSq ((q : Work.BoseSym.Amb N)) +
        ∫ x in BoseGases.box N L, Work.BoseSym.Vpot N v x *
          ((((q : Work.BoseSym.Amb N).1) : Work.BoseSym.Conf N → ℝ) x) ^ 2 ≤ Q)
    (hδ : 0 < δ) :
    ∃ G : Work.BoseSym.testSub N L,
      (G : Work.BoseSym.Conf N → ℝ) ≠ 0 ∧
      Work.BoseSym.PermInv N (G : Work.BoseSym.Conf N → ℝ) ∧
      (Work.BoseSym.gSq (Work.BoseSym.graphPoint N L G)
        + Work.BoseSym.potSq (Work.BoseSym.Vpot N v) (Work.BoseSym.graphPoint N L G))
        / Work.BoseSym.l2Sq (Work.BoseSym.graphPoint N L G) ≤ Q + δ := by
  classical
  have vnonneg : ∀ x : Conf N, 0 ≤ Vpot N v x := fun x => Vpot_nonneg hv x
  have hfq : MemLp (((q : Amb N).1) : Conf N → ℝ) 2 (volC N) := Lp.memLp ((q : Amb N).1)
  have hqv : MemLp.toLp (((q : Amb N).1) : Conf N → ℝ) hfq = (q : Amb N).1 :=
    Lp.toLp_coeFn _ _
  -- ## constants
  have hA0 : 0 ≤ gSq (q : Amb N) := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB00 : 0 ≤ (∫ x in BoseGases.box N L,
      Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) :=
    integral_nonneg fun x => mul_nonneg (vnonneg x) (sq_nonneg _)
  have hQ0 : 0 ≤ Q := le_trans (add_nonneg hA0 hB00) hQ
  have hQd : 0 < Q + δ := by linarith
  set κ : ℝ := 7 * δ / (16 * (Q + δ)) with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hκle : κ ≤ 7 / 16 := by
    rw [hκdef, div_le_iff₀ (by positivity : (0:ℝ) < 16 * (Q + δ))]
    nlinarith [hδ.le, hQ0]
  have hκQ : κ * (Q + δ) ≤ 3 * δ / 4 := by
    have h : κ * (Q + δ) = 7 * δ / 16 := by
      rw [hκdef]
      field_simp
    rw [h]
    linarith [hδ.le]
  -- ## the cutoff family and the truncation level
  obtain ⟨ψ, hψcd, hψderiv, hψ0, hψle, hψlip, hψbd, hψtend⟩ := Trunc.smooth_cutoff_family_bounded
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψlip n).continuous
  have hmemψ : ∀ n, MemLp (fun x => ψ n (((q : Amb N).1 : Conf N → ℝ) x)) 2 (volC N) := by
    intro n
    refine hfq.mono ((hψc n).comp_aestronglyMeasurable hfq.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hψle n _
  have hsymfix : symLp N ((q : Amb N).1) = (q : Amb N).1 := by
    have h := symLp_fixed_of_aeEq hfq hqsym
    rwa [hqv] at h
  have hnorm_q : ‖((q : Amb N).1)‖ = 1 := by
    have h := hq1
    simp only [l2Sq] at h
    nlinarith [norm_nonneg (((q : Amb N).1))]
  have hκhalf_lt : κ / 2 < 1 := by linarith [hκle]
  have hsqrt_lt : Real.sqrt (1 - κ / 2) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
    linarith
  have hη1 : 0 < 1 - Real.sqrt (1 - κ / 2) := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_cutoff_level (ψ := ψ) hfq hψc hψle hψtend hmemψ hqv hnorm_q hsymfix
    (κ := 1 - Real.sqrt (1 - κ / 2)) hη1
  have hβ : 1 - κ / 2 ≤ ‖symLp N (MemLp.toLp (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x))
      (hmemψ n₀))‖ ^ 2 := by
    have h1 : Real.sqrt (1 - κ / 2) ≤ ‖symLp N (MemLp.toLp
        (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) (hmemψ n₀))‖ := by linarith [hn₀]
    calc 1 - κ / 2 = (Real.sqrt (1 - κ / 2)) ^ 2 := (Real.sq_sqrt (by linarith [hκle])).symm
      _ ≤ ‖symLp N (MemLp.toLp (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x))
            (hmemψ n₀))‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  -- ## the approximating sequence
  have hG : ∀ n : ℕ, ∃ F : testSub N L, hSq (graphPoint N L F - (q : Amb N)) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => Basic.exists_graphPoint_close q (by
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact one_div_pos.mpr (by linarith))
  choose G hGspec using hG
  have hnorm : ∀ n, ‖graphPoint N L (G n) - (q : Amb N)‖ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := by
    intro n
    calc ‖graphPoint N L (G n) - (q : Amb N)‖
        = Real.sqrt (‖graphPoint N L (G n) - (q : Amb N)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hSq (graphPoint N L (G n) - (q : Amb N))) :=
          Real.sqrt_le_sqrt (Abs.norm_sq_le_hSq _)
      _ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := Real.sqrt_le_sqrt (hGspec n)
  have hgtend : Tendsto (fun n => graphPoint N L (G n)) atTop (nhds (q : Amb N)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hnorm ?_
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def] using h1
  have hu_lim : Tendsto (fun n => (graphPoint N L (G n)).1) atTop (nhds ((q : Amb N).1)) :=
    (continuous_fst.tendsto (q : Amb N)).comp hgtend
  -- ## the truncated test functions
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
  -- ## the chain rule and the gradient bound
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
  have hgSq_le : ∀ n, gSq (graphPoint N L (F n)) ≤ gSq (graphPoint N L (G n)) :=
    fun n => Abs.gSq_graphPoint_le (G n) (F n) (hchain n)
  have hgSq_sym : ∀ n, gSq (graphPoint N L (symTest N L (F n))) ≤ gSq (graphPoint N L (G n)) :=
    fun n => by
      rw [← Perm.symAvgAmb_graphPoint (F n)]
      exact le_trans (Perm.gSq_symAvgAmb_le _) (hgSq_le n)
  have hgSqlim : Tendsto (fun n => gSq (graphPoint N L (G n))) atTop (nhds (gSq (q : Amb N))) :=
    ((continuous_gSq (N := N)).tendsto (q : Amb N)).comp hgtend
  have hev_g : ∀ᶠ n in atTop,
      gSq (graphPoint N L (symTest N L (F n))) ≤ gSq (q : Amb N) + δ / 8 := by
    filter_upwards [hgSqlim.eventually (Metric.ball_mem_nhds (gSq (q : Amb N))
      (by linarith : (0:ℝ) < δ / 8))] with n hn
    rw [Real.dist_eq] at hn
    have hlt : gSq (graphPoint N L (G n)) < gSq (q : Amb N) + δ / 8 := by
      linarith [(abs_lt.mp hn).2]
    linarith [hgSq_sym n, hlt]
  -- ## the potential energy bound
  have hev_pot : ∀ᶠ n in atTop,
      potSq (Vpot N v) (graphPoint N L (symTest N L (F n)))
        ≤ (∫ x in BoseGases.box N L, Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2)
          + δ / 8 := by
    have hW0 : 0 ≤ symAvgF N (Vpot N v) := nonneg_symAvgF vnonneg
    have hWint : IntOnBox N L (symAvgF N (Vpot N v)) := intOnBox_symAvgF hV
    have hC0 : (0 : ℝ) ≤ (n₀ : ℝ) + 1 := by positivity
    have hψC : ∀ t, |ψ n₀ t| ≤ (n₀ : ℝ) + 1 := hψbd n₀
    have hψlip' : ∀ a b, |ψ n₀ a - ψ n₀ b| ≤ |a - b| := by
      intro a b
      have h := (hψlip n₀).dist_le_mul a b
      rw [Real.dist_eq, Real.dist_eq] at h
      simpa using h
    have hD2 := Trunc.potBox_eventually_le (N := N) (L := L) (V := symAvgF N (Vpot N v))
      hW0 hWint ((hψc n₀).measurable) hC0 hψC hψlip' hu_lim (ε := δ / 8) (by linarith)
    have hinvψ : ∀ᵐ x ∂(volC N), ∀ σ : Equiv.Perm (Fin N),
        (fun y => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) y)) (actPerm N σ x)
          = (fun y => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) y)) x := by
      filter_upwards [aeInvariant_of_aeEq_symAvgF hqsym] with x hx
      intro σ
      simp only [hx σ]
    have hintψ : IntegrableOn (fun x => Vpot N v x * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2)
        (BoseGases.box N L) volume := by
      have hm1 : AEStronglyMeasurable (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x))
          (volume.restrict (BoseGases.box N L)) :=
        (hψc n₀).comp_aestronglyMeasurable
          ((Lp.aestronglyMeasurable ((q : Amb N).1)).mono_measure Measure.restrict_le_self)
      have hm2 : AEStronglyMeasurable
          (fun x => Vpot N v x * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2)
          (volume.restrict (BoseGases.box N L)) :=
        hV.aestronglyMeasurable.mul (hm1.pow 2)
      refine Integrable.mono' (hV.const_mul (((n₀ : ℝ) + 1) ^ 2)) hm2 ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (vnonneg x) (sq_nonneg _))]
      have hsq : (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2 ≤ ((n₀ : ℝ) + 1) ^ 2 :=
        calc (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2
            = |ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)| ^ 2 := (sq_abs _).symm
          _ ≤ ((n₀ : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hψC _) 2
      calc Vpot N v x * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2
          ≤ Vpot N v x * ((n₀ : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hsq (vnonneg x)
        _ = ((n₀ : ℝ) + 1) ^ 2 * Vpot N v x := by ring
    have hD4 := integral_symAvgF_mul_sq_eq (N := N) (L := L) (V := Vpot N v)
      (f := fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) vnonneg hV hintψ hinvψ
    have hcmp : (∫ x in BoseGases.box N L,
        Vpot N v x * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2)
        ≤ ∫ x in BoseGases.box N L,
            Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2 := by
      refine integral_mono_of_nonneg ?_ hqint ?_
      · filter_upwards with x
        exact mul_nonneg (vnonneg x) (sq_nonneg _)
      · filter_upwards with x
        refine mul_le_mul_of_nonneg_left ?_ (vnonneg x)
        calc (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2
            = |ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)| ^ 2 := (sq_abs _).symm
          _ ≤ |(((q : Amb N).1 : Conf N → ℝ) x)| ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) (hψle n₀ _) 2
          _ = (((q : Amb N).1 : Conf N → ℝ) x) ^ 2 := sq_abs _
    filter_upwards [hD2] with n hn
    have hbnd : ∀ x, |((F n : testSub N L) : Conf N → ℝ) x| ≤ (n₀ : ℝ) + 1 := by
      intro x
      rw [hFcoe n]
      exact hψC _
    have hfmF : AEStronglyMeasurable ((F n : testSub N L) : Conf N → ℝ)
        (volume.restrict (BoseGases.box N L)) :=
      ((F n).2.1.continuous.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hC3 := integral_Vpot_symAvgF_sq_le_meas (N := N) (L := L) (V := Vpot N v)
      (hV0 := vnonneg) (hVint := hV) (hfm := hfmF) (hC := hC0) (hf := hbnd)
    have hcoee : ((symTest N L (F n) : testSub N L) : Conf N → ℝ)
        = symAvgF N ((F n : testSub N L) : Conf N → ℝ) := rfl
    have hn' : (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
          * (ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) ^ 2)
        ≤ (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
            * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2) + δ / 8 := hn
    have hiff : (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
          * (ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) ^ 2)
        = ∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
            * ((F n : testSub N L) : Conf N → ℝ) x ^ 2 := by
      refine setIntegral_congr_ae (box_closed L).measurableSet ?_
      have hg : (((graphPoint N L (G n)).1 : Conf N → ℝ)) =ᵐ[volC N] (G n : Conf N → ℝ) :=
        MemLp.coeFn_toLp (memLp_of_contDiff_hasCompactSupport (G n).2.1
          (hasCompactSupport_of_testFun (G n).2))
      filter_upwards [hg] with x hx
      intro _
      simp only [hFcoe n, hx]
    rw [potSq_graphPoint_box]
    simp only [hcoee]
    calc (∫ x in BoseGases.box N L, Vpot N v x
            * (symAvgF N ((F n : testSub N L) : Conf N → ℝ) x) ^ 2)
        ≤ (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
            * ((F n : testSub N L) : Conf N → ℝ) x ^ 2) := hC3
      _ = (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
            * (ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x)) ^ 2) := hiff.symm
      _ ≤ (∫ x in BoseGases.box N L, (symAvgF N (Vpot N v)) x
            * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2) + δ / 8 := hn'
      _ = (∫ x in BoseGases.box N L, Vpot N v x
            * (ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) ^ 2) + δ / 8 := by rw [hD4]
      _ ≤ (∫ x in BoseGases.box N L, Vpot N v x
            * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) + δ / 8 := by linarith [hcmp]
  -- ## the denominator
  have hmem_all : ∀ n, MemLp (fun x => ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x))
      2 (volC N) := by
    intro n
    refine (Lp.memLp ((graphPoint N L (G n)).1)).mono
      ((hψc n₀).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hψle n₀ _
  have htoLp := Trunc.tendsto_toLp_comp (ψ := ψ n₀) (hψ0 n₀) (hψlip n₀) hu_lim hmem_all (hmemψ n₀)
  have htoLp' : Tendsto (fun n => toLpTest (F n)) atTop
      (nhds (MemLp.toLp (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) (hmemψ n₀))) := by
    have hcongr : (fun n => toLpTest (F n))
        = fun n => MemLp.toLp (fun x => ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x))
            (hmem_all n) := by
      funext n
      have hmemG : MemLp (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x)) 2 (volC N) :=
        (hψlip n₀).comp_memLp (hψ0 n₀)
          (memLp_of_contDiff_hasCompactSupport (G n).2.1 (hasCompactSupport_of_testFun (G n).2))
      have h1 : toLpTest (F n) = MemLp.toLp (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x))
          hmemG :=
        MemLp.toLp_congr _ hmemG (Filter.EventuallyEq.of_eq (hFcoe n))
      have h2 : MemLp.toLp (fun x : Conf N => ψ n₀ ((G n : Conf N → ℝ) x)) hmemG
          = MemLp.toLp (fun x => ψ n₀ (((graphPoint N L (G n)).1 : Conf N → ℝ) x))
              (hmem_all n) := by
        refine MemLp.toLp_congr _ _ ?_
        have hg : (((graphPoint N L (G n)).1 : Conf N → ℝ)) =ᵐ[volC N] (G n : Conf N → ℝ) :=
          MemLp.coeFn_toLp (memLp_of_contDiff_hasCompactSupport (G n).2.1
            (hasCompactSupport_of_testFun (G n).2))
        exact (hg.fun_comp (ψ n₀)).symm
      exact h1.trans h2
    rw [hcongr]
    exact htoLp
  have hdenlim : Tendsto (fun n => l2Sq (graphPoint N L (symTest N L (F n)))) atTop
      (nhds (‖symLp N (MemLp.toLp (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x))
        (hmemψ n₀))‖ ^ 2)) :=
    tendsto_l2Sq_graphPoint_symTest htoLp'
  have hev_den : ∀ᶠ n in atTop, 1 - κ ≤ l2Sq (graphPoint N L (symTest N L (F n))) := by
    filter_upwards [hdenlim.eventually (Metric.ball_mem_nhds
      (‖symLp N (MemLp.toLp (fun x => ψ n₀ (((q : Amb N).1 : Conf N → ℝ) x)) (hmemψ n₀))‖ ^ 2)
      (by linarith : (0:ℝ) < κ / 4))] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).1, hβ]
  -- ## assembly
  obtain ⟨n, hn1, hn2, hn3⟩ := (hev_g.and (hev_pot.and hev_den)).exists
  refine ⟨symTest N L (F n), ?_, ?_, ?_⟩
  · intro hzero
    have h0 : l2Sq (graphPoint N L (symTest N L (F n))) = 0 := by
      rw [l2Sq_graphPoint_box, hzero]
      simp [intBox]
    have hpos : 0 < 1 - κ := by linarith [hκle]
    linarith [hn3, h0, hpos]
  · exact Submission.BoseGases.symAvg_sym (N := N) ((F n : testSub N L) : Conf N → ℝ)
  · have hden_pos : 0 < l2Sq (graphPoint N L (symTest N L (F n))) := by
      have hpos : 0 < 1 - κ := by linarith [hκle]
      linarith [hn3, hpos]
    rw [div_le_iff₀ hden_pos]
    have hnum : gSq (graphPoint N L (symTest N L (F n)))
        + potSq (Vpot N v) (graphPoint N L (symTest N L (F n)))
        ≤ (gSq (q : Amb N)
            + ∫ x in BoseGases.box N L, Vpot N v x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2)
          + δ / 4 := by linarith [hn1, hn2]
    have hstep : Q + δ / 4 ≤ (Q + δ) * l2Sq (graphPoint N L (symTest N L (F n))) := by
      have h1 : (Q + δ) * (1 - κ) = (Q + δ) - κ * (Q + δ) := by ring
      have h2 : Q + δ / 4 ≤ (Q + δ) * (1 - κ) := by
        rw [h1]
        linarith [hκQ]
      have h3 : (Q + δ) * (1 - κ) ≤ (Q + δ) * l2Sq (graphPoint N L (symTest N L (F n))) :=
        mul_le_mul_of_nonneg_left hn3 hQd.le
      linarith [h2, h3]
    linarith [hnum, hQ, hstep]


end

end Work.BoseSym.Bridge
