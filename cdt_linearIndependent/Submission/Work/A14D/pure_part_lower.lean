import Mathlib
import Submission.Work.A14D.LC_A_defs
import Submission.Work.A14D.pure_pullback_cont
import Submission.Work.A14.defs
import Submission.Work.A14D.jump_G_ident
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.wC_maps_ball
import Submission.Work.A14D.wC_im_neg
import Submission.Work.Pure.pure_facts
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.OdeCont.uniqueness
import Submission.Work.A14D.pure_sys_disc
import Submission.Work.A14D.exists_sol_Om1_of_sol_SU

/-!
# `Work.A14D.pure_part_lower`

The *pure part* of the jump relation of Theorem A is the function

`Φ z = Σ_{j : Fin 7} pⱼ(yC z) · (BUp j z − BUp j (wC z))`

on the wedge `SU ∩ SL` (the sum over the seven pure slots), where `BUp j` is the `SU`-branch of
the `j`-th pure pullback `B_{j+1}(y(x))`.

This file proves that `Φ` is the restriction of a holomorphic function `PJ` on the slit plane
`Om1 = ℂ ∖ (−∞,1]`, whose germ at `1/9` (from below) is holomorphic on a disc — the statement that
the pure part contributes neither a logarithm nor a pole at `1/9`, which is what the
log-coefficient extraction (`Work.A14D.extract_log_half`) needs.

## Route

* The seven pure functions satisfy the first-order system `dq(y)·V' = y'·dA(y)·V` on the `y`-line
  (`Work.Pure.dclosed`, with the explicit data `Work.Pure.dq = 2X(4−X)` and `Work.Pure.dA`); pulled
  back to the `x`-variable (delegated: `Work.A14D.pure_sys_disc`) this reads
  `dq(yC z)·V'(z) = dyC z·dA(yC z)·V(z)`, i.e. `V' = psysA z · V`.
* Hence the vector `PV z j = BUp j z` solves `V' = psysA z · V` on `SU ∖ {2}` (identity theorem),
  and that solution extends to `Om1 ∖ {2}` (delegated: `Work.A14D.exists_sol_Om1_of_sol_SU`).
* Since `2 ∈ SU`, the `SU`-branch already controls a neighbourhood of `2`; gluing the extension
  with `BUp` gives functions `G j` holomorphic on all of `Om1` solving the system off `2`.
* `PJ := Σ_j pⱼ(yC ·)·(G j − G j ∘ wC)` is holomorphic on `Om1` (as `wC` preserves `Om1`) and
  agrees with `Φ` on the wedge.
* Near `1/9` the coefficients of the system are holomorphic on `ball (1/9) (1/10)`, so the germ of
  `G` on `halfL δ` extends to that ball (linear ODE continuation, `exists_sol_of_sol_convex`);
  the same holds near `−1/8 = wC (1/9)`, and `wC` maps `ball (1/9) δ` into `ball (−1/8) (1/10)`,
  which covers the second factor.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ## 1. The pure system in the `x`-variable -/

/-- The coefficient matrix of the pure system `dq(yC z)·V' = dyC z·dA(yC z)·V`. -/
def psysA (z : ℂ) (i j : Fin 7) : ℂ :=
  dyC z * pAtY (Work.Pure.dA i j) z / pAtY (Work.Pure.dq) z

/-- The vector of the seven `SU`-branches of the pure pullbacks. -/
def PV (z : ℂ) : Fin 7 → ℂ := fun j => BUp j z

/-! ## 2. Elementary geometry of `wC`, `yC` and the discs around `1/9` and `−1/8` -/

lemma wC_sub_one {z : ℂ} (hz : z ≠ 1) : wC z - 1 = (z - 1)⁻¹ := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  simp only [wC]
  field_simp
  ring

lemma wC_eq_one_add_inv {z : ℂ} (hz : z ≠ 1) : wC z = 1 + (z - 1)⁻¹ := by
  have h := wC_sub_one hz
  linear_combination h

lemma yC_wC {z : ℂ} (hz : z ≠ 1) : yC (wC z) = yC z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have h2 : wC z = z * (z - 1)⁻¹ := by simp only [wC, div_eq_mul_inv]
  have h : wC z - 1 = (z - 1)⁻¹ := wC_sub_one hz
  simp only [yC, h2, h]
  field_simp
  ring

lemma dyC_wC {z : ℂ} (hz : z ≠ 1) : dyC (wC z) * deriv wC z = dyC z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have h2 : wC z = z * (z - 1)⁻¹ := by simp only [wC, div_eq_mul_inv]
  rw [deriv_wC z hz, h2]
  simp only [dyC]
  field_simp
  ring

lemma one_notMem_Om1 : (1 : ℂ) ∉ Om1 := by
  intro h
  rcases h with h | h
  · exact h (by simp)
  · norm_num at h

lemma isOpen_Om1_pure_part_lower : IsOpen Om1 := by
  rw [show Om1 = {z : ℂ | z.im ≠ 0} ∪ {z : ℂ | 1 < z.re} from rfl]
  exact (isClosed_eq continuous_im continuous_const).isOpen_compl.union
    (isOpen_lt continuous_const continuous_re)

lemma wC_mem_Om1 {z : ℂ} (hz : z ∈ Om1) : wC z ∈ Om1 := by
  have hz1 : z ≠ 1 := fun h => one_notMem_Om1 (by rwa [h] at hz)
  have h := wC_eq_one_add_inv hz1
  have him : (wC z).im = -(z.im) / ‖z - 1‖ ^ 2 := by
    rw [h, Complex.add_im, Complex.one_im, zero_add, Complex.inv_im,
      Complex.normSq_eq_norm_sq, Complex.sub_im, Complex.one_im, sub_zero]
  have hre : (wC z).re - 1 = (z.re - 1) / ‖z - 1‖ ^ 2 := by
    rw [h, Complex.add_re, Complex.one_re, Complex.inv_re, Complex.normSq_eq_norm_sq,
      Complex.sub_re, Complex.one_re]
    ring
  have hpos : 0 < ‖z - 1‖ ^ 2 := by
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have := norm_pos_iff.mpr hne
    positivity
  rcases hz with him0 | hre1
  · left
    rw [him]
    exact div_ne_zero (neg_ne_zero.mpr him0) (ne_of_gt hpos)
  · right
    have hd : 0 < (z.re - 1) / ‖z - 1‖ ^ 2 := div_pos (by linarith) hpos
    linarith

lemma wC_im_pos_of_neg {z : ℂ} (hz : z.im < 0) : 0 < (wC z).im := by
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
  have h := wC_eq_one_add_inv hz1
  have him : (wC z).im = -(z.im) / ‖z - 1‖ ^ 2 := by
    rw [h, Complex.add_im, Complex.one_im, zero_add, Complex.inv_im,
      Complex.normSq_eq_norm_sq, Complex.sub_im, Complex.one_im, sub_zero]
  rw [him]
  have hpos : 0 < ‖z - 1‖ ^ 2 := by
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have := norm_pos_iff.mpr hne
    positivity
  exact div_pos (by linarith) hpos

lemma yC_ne_zero {z : ℂ} (h1 : z ≠ 1) (h0 : z ≠ 0) : yC z ≠ 0 := by
  intro h
  rw [yC, div_eq_zero_iff] at h
  rcases h with h' | h'
  · exact h0 (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h')
  · exact h1 (sub_eq_zero.mp h')

lemma yC_ne_four {z : ℂ} (h1 : z ≠ 1) (h2 : z ≠ 2) : yC z ≠ 4 := by
  intro h
  rw [yC, div_eq_iff (sub_ne_zero.mpr h1)] at h
  have h' : (z - 2) ^ 2 = 0 := by linear_combination h
  have h3 : z - 2 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h'
  exact h2 (sub_eq_zero.mp h3)

lemma pAtY_eq_eval (p : Polynomial ℚ) (z : ℂ) :
    pAtY p z = ((p.map (algebraMap ℚ ℂ)).eval (yC z)) := by
  rw [pAtY, Polynomial.eval₂_eq_eval_map]

lemma pAtY_dq_eq (z : ℂ) : pAtY (Work.Pure.dq) z = 2 * yC z * (4 - yC z) := by
  have h : (Work.Pure.dq).map (algebraMap ℚ ℂ)
      = Polynomial.C 2 * Polynomial.X * (Polynomial.C 4 - Polynomial.X) := by
    simp [Work.Pure.dq]
  rw [pAtY, Polynomial.eval₂_eq_eval_map, h]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] <;> ring

lemma one_notMem_ball_ninth : (1 : ℂ) ∉ Metric.ball ninth (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq]
  norm_num [ninth]

lemma two_notMem_ball_ninth : (2 : ℂ) ∉ Metric.ball ninth (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq]
  norm_num [ninth]

lemma zero_notMem_ball_ninth : (0 : ℂ) ∉ Metric.ball ninth (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq, zero_sub, norm_neg]
  norm_num [ninth]

lemma one_notMem_ball_neg_eighth : (1 : ℂ) ∉ Metric.ball (-(1/8)) (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq]
  norm_num

lemma two_notMem_ball_neg_eighth : (2 : ℂ) ∉ Metric.ball (-(1/8)) (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq]
  norm_num

lemma zero_notMem_ball_neg_eighth : (0 : ℂ) ∉ Metric.ball (-(1/8)) (1/10) := by
  rw [Metric.mem_ball, Complex.dist_eq, zero_sub, norm_neg]
  norm_num

lemma pAtY_dq_ne_zero_ball {z : ℂ} (hz : z ∈ Metric.ball ninth (1/10)) :
    pAtY (Work.Pure.dq) z ≠ 0 := by
  have hz1 : z ≠ 1 := fun h => one_notMem_ball_ninth (by rwa [h] at hz)
  have hz2 : z ≠ 2 := fun h => two_notMem_ball_ninth (by rwa [h] at hz)
  have hz0 : z ≠ 0 := fun h => zero_notMem_ball_ninth (by rwa [h] at hz)
  rw [pAtY_dq_eq]
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · norm_num at h''
    · exact yC_ne_zero hz1 hz0 h''
  · exact yC_ne_four hz1 hz2 (sub_eq_zero.mp h').symm

lemma pAtY_dq_ne_zero_ball_neg {z : ℂ} (hz : z ∈ Metric.ball (-(1/8)) (1/10)) :
    pAtY (Work.Pure.dq) z ≠ 0 := by
  have hz1 : z ≠ 1 := fun h => one_notMem_ball_neg_eighth (by rwa [h] at hz)
  have hz2 : z ≠ 2 := fun h => two_notMem_ball_neg_eighth (by rwa [h] at hz)
  have hz0 : z ≠ 0 := fun h => zero_notMem_ball_neg_eighth (by rwa [h] at hz)
  rw [pAtY_dq_eq]
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · norm_num at h''
    · exact yC_ne_zero hz1 hz0 h''
  · exact yC_ne_four hz1 hz2 (sub_eq_zero.mp h').symm

/-- `dq(yC z) ≠ 0` for `z ∈ Om1`, `z ≠ 2`. -/
lemma pAtY_dq_ne_zero_of_Om1 {z : ℂ} (hz : z ∈ Om1) (hz2 : z ≠ 2) :
    pAtY (Work.Pure.dq) z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h0
    rcases hz with h | h
    · exact h (by rw [h0]; simp)
    · rw [h0] at h; norm_num at h
  have hz1 : z ≠ 1 := fun h => one_notMem_Om1 (by rwa [h] at hz)
  rw [pAtY_dq_eq]
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · norm_num at h''
    · exact yC_ne_zero hz1 hz0 h''
  · exact yC_ne_four hz1 hz2 (sub_eq_zero.mp h').symm

/-! ## 3. Holomorphy of the coefficients -/

lemma yC_differentiableAt {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ yC z := by
  unfold yC
  exact (differentiableAt_id.pow 2).div (differentiableAt_id.sub (differentiableAt_const 1))
    (sub_ne_zero.mpr hz)

lemma dyC_differentiableAt {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ dyC z := by
  unfold dyC
  exact ((differentiableAt_id.pow 2).sub
      ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)).div
    ((differentiableAt_id.sub (differentiableAt_const 1)).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hz))

lemma pAtY_differentiableAt {p : Polynomial ℚ} {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ (pAtY p) z := by
  have h : pAtY p = fun w => ((p.map (algebraMap ℚ ℂ)).eval (yC w)) := by
    funext w; rw [pAtY_eq_eval]
  rw [h]
  exact (Polynomial.differentiable (p.map (algebraMap ℚ ℂ))).differentiableAt.comp z
    (yC_differentiableAt hz)

lemma yC_diffOn_Om1 : DifferentiableOn ℂ yC Om1 := by
  intro z hz
  exact (yC_differentiableAt (fun h => one_notMem_Om1 (by rwa [h] at hz))).differentiableWithinAt

lemma pAtY_diffOn_Om1 (p : Polynomial ℚ) : DifferentiableOn ℂ (pAtY p) Om1 := by
  intro z hz
  exact (pAtY_differentiableAt (p := p)
    (fun h => one_notMem_Om1 (by rwa [h] at hz))).differentiableWithinAt

lemma yC_diffOn_SU : DifferentiableOn ℂ yC SU := by
  intro z hz
  exact (yC_differentiableAt (fun h => one_notMem_SU (by rwa [h] at hz))).differentiableWithinAt

lemma pAtY_diffOn_SU (p : Polynomial ℚ) : DifferentiableOn ℂ (pAtY p) SU := by
  intro z hz
  exact (pAtY_differentiableAt (p := p)
    (fun h => one_notMem_SU (by rwa [h] at hz))).differentiableWithinAt

lemma dyC_diffOn_SU : DifferentiableOn ℂ dyC SU := by
  intro z hz
  exact (dyC_differentiableAt (fun h => one_notMem_SU (by rwa [h] at hz))).differentiableWithinAt

lemma psysA_differentiableAt {z : ℂ} (h1 : z ≠ 1) (hdq : pAtY (Work.Pure.dq) z ≠ 0)
    (i j : Fin 7) : DifferentiableAt ℂ (fun w => psysA w i j) z := by
  simp only [psysA]
  exact ((dyC_differentiableAt h1).mul (pAtY_differentiableAt (p := Work.Pure.dA i j) h1)).div
    (pAtY_differentiableAt (p := Work.Pure.dq) h1) hdq

/-- The system's coefficients are holomorphic on `Om1 ∖ {2}`. -/
lemma psysA_diffOn_Om1 : ∀ i j : Fin 7,
    DifferentiableOn ℂ (fun z => psysA z i j) (Om1 \ ({2} : Set ℂ)) := by
  intro i j z hz
  obtain ⟨hzOm, hznot⟩ := hz
  have hz2 : z ≠ 2 := fun h => hznot (by simpa [h])
  have hz1 : z ≠ 1 := fun h => one_notMem_Om1 (by rwa [h] at hzOm)
  exact (psysA_differentiableAt hz1 (pAtY_dq_ne_zero_of_Om1 hzOm hz2) i j).differentiableWithinAt

lemma psysA_diffOn_ball (i j : Fin 7) :
    DifferentiableOn ℂ (fun z => psysA z i j) (Metric.ball ninth (1/10)) := by
  intro z hz
  exact (psysA_differentiableAt (fun h => one_notMem_ball_ninth (by rwa [h] at hz))
    (pAtY_dq_ne_zero_ball hz) i j).differentiableWithinAt

lemma psysA_diffOn_ball_neg (i j : Fin 7) :
    DifferentiableOn ℂ (fun z => psysA z i j) (Metric.ball (-(1/8)) (1/10)) := by
  intro z hz
  exact (psysA_differentiableAt (fun h => one_notMem_ball_neg_eighth (by rwa [h] at hz))
    (pAtY_dq_ne_zero_ball_neg hz) i j).differentiableWithinAt

/-! ## 4. The system for the `SU`-branches on `SU` -/

lemma BUp_eq_evp (j : Fin 7) {z : ℂ} (hz : ‖z‖ < 1) :
    BUp j z = Work.CPull.evp ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) z := by
  rw [BUp_series j hz]
  rfl

/-- The cleared system identity on `SU`: `dq(y)·(BUp i)' = y'·Σ_m dA i m(y)·BUp m`. -/
lemma cleared_system_SU (i : Fin 7) {z : ℂ} (hz : z ∈ SU) :
    pAtY (Work.Pure.dq) z * deriv (fun u => BUp i u) z
      - dyC z * ∑ m : Fin 7, pAtY (Work.Pure.dA i m) z * BUp m z = 0 := by
  set L : ℂ → ℂ := fun w => pAtY (Work.Pure.dq) w * deriv (fun u => BUp i u) w
    - dyC w * ∑ m : Fin 7, pAtY (Work.Pure.dA i m) w * BUp m w with hL
  have hana : AnalyticOnNhd ℂ L SU := by
    have h1 : DifferentiableOn ℂ
        (fun w => pAtY (Work.Pure.dq) w * deriv (fun u => BUp i u) w) SU :=
      (pAtY_diffOn_SU _).mul
        ((((BUp_analytic_SU i).analyticOnNhd isOpen_SU_H_cont).deriv).differentiableOn)
    have h2 : DifferentiableOn ℂ
        (fun w => dyC w * ∑ m : Fin 7, pAtY (Work.Pure.dA i m) w * BUp m w) SU :=
      dyC_diffOn_SU.mul
        (DifferentiableOn.fun_sum fun m _ => (pAtY_diffOn_SU _).mul (BUp_analytic_SU m))
    exact (h1.sub h2).analyticOnNhd isOpen_SU_H_cont
  have hz₀ : ((1 / 4 : ℂ) * Complex.I) ∈ SU := by
    rw [mem_SU_iff]; simp; norm_num
  have hev : L =ᶠ[𝓝 (((1 / 4 : ℂ) * Complex.I))] 0 := by
    have hmem : Metric.ball (((1 / 4 : ℂ) * Complex.I)) (1 / 4)
        ∈ 𝓝 (((1 / 4 : ℂ) * Complex.I)) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num))
    filter_upwards [hmem] with w hw
    have hw1 : ‖w‖ < 1 := by
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have hz0n : ‖((1 / 4 : ℂ) * Complex.I)‖ = 1 / 4 := by
        rw [norm_mul, Complex.norm_I, mul_one]
        rw [show ((1 / 4 : ℂ)) = (((1 : ℝ) / 4 : ℝ) : ℂ) by norm_num,
          Complex.norm_of_nonneg (by norm_num)]
      calc ‖w‖ = ‖(w - ((1 / 4 : ℂ) * Complex.I)) + ((1 / 4 : ℂ) * Complex.I)‖ := by ring_nf
        _ ≤ ‖w - ((1 / 4 : ℂ) * Complex.I)‖ + ‖((1 / 4 : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ < 1 / 4 + 1 / 4 := by rw [hz0n]; linarith
        _ = 1 / 2 := by norm_num
        _ < 1 := by norm_num
    have hder : deriv (fun u => BUp i u) w
        = deriv (fun u => Work.CPull.evp
            ((Submission.CDTPlan.pureB i).subst Submission.CDT.sympY) u) w := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (show w ∈ Metric.ball (0 : ℂ) 1 by rwa [Metric.mem_ball, dist_zero_right])] with u hu
      exact BUp_eq_evp i (by rwa [Metric.mem_ball, dist_zero_right] at hu)
    have hsum : (∑ m : Fin 7, pAtY (Work.Pure.dA i m) w * BUp m w)
        = ∑ m : Fin 7, pAtY (Work.Pure.dA i m) w * Work.CPull.evp
            ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) w :=
      Finset.sum_congr rfl fun m _ => by rw [BUp_eq_evp m hw1]
    rw [hL]
    simp only
    rw [hder, hsum]
    exact sub_eq_zero.mpr (pure_sys_disc i hw1)
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_SU.isPreconnected hz₀ hev
  exact hzero hz

/-- The seven pure pullbacks solve the pure linear system on `SU ∖ {2}`. -/
theorem PV_system_SU : ∀ z ∈ SU \ ({2} : Set ℂ),
    HasDerivAt PV (fun i : Fin 7 => ∑ j : Fin 7, psysA z i j * PV z j) z := by
  intro z hz
  have hzSU : z ∈ SU := hz.1
  have hz2 : z ≠ 2 := fun h => hz.2 (by simpa [h])
  have hdq : pAtY (Work.Pure.dq) z ≠ 0 := pAtY_dq_ne_zero_of_Om1 (SU_subset_Om1 hzSU) hz2
  refine hasDerivAt_pi.mpr fun i => ?_
  have hd : HasDerivAt (fun u => BUp i u) (deriv (fun u => BUp i u) z) z :=
    ((BUp_analytic_SU i).differentiableAt (isOpen_SU_H_cont.mem_nhds hzSU)).hasDerivAt
  have hval : deriv (fun u => BUp i u) z
      = (dyC z * ∑ m : Fin 7, pAtY (Work.Pure.dA i m) z * BUp m z) / pAtY (Work.Pure.dq) z := by
    have h := cleared_system_SU i hzSU
    rw [sub_eq_zero] at h
    rw [← h, mul_div_cancel_left₀ _ hdq]
  have hR : (∑ j : Fin 7, psysA z i j * PV z j)
      = (dyC z / pAtY (Work.Pure.dq) z)
        * ∑ j : Fin 7, pAtY (Work.Pure.dA i j) z * BUp j z := by
    simp only [psysA, PV]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_eq_mul_div]
    ring
  refine hd.congr_deriv ?_
  rw [hval, hR, div_mul_eq_mul_div]

/-! ## 5. Extension of the `SU`-branch vector to `Om1` -/

/-- Glue the `SU`-branch `PV` with its extension `Ĝ` off `SU`. -/
noncomputable def glueG (Ĝ : ℂ → Fin 7 → ℂ) : ℂ → Fin 7 → ℂ := by
  classical
  exact fun z => if z ∈ SU then PV z else Ĝ z

lemma glueG_of_mem (Ĝ : ℂ → Fin 7 → ℂ) {z : ℂ} (hz : z ∈ SU) : glueG Ĝ z = PV z := by
  classical
  simp only [glueG, if_pos hz]

lemma glueG_of_not_mem (Ĝ : ℂ → Fin 7 → ℂ) {z : ℂ} (hz : z ∉ SU) : glueG Ĝ z = Ĝ z := by
  classical
  simp only [glueG, if_neg hz]

theorem exists_G_Om1 : ∃ G : ℂ → Fin 7 → ℂ, DifferentiableOn ℂ G Om1 ∧
    (∀ z ∈ SU, G z = PV z) ∧
    (∀ z ∈ Om1, z ≠ 2 → HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j) z) := by
  classical
  have hPVd : DifferentiableOn ℂ PV SU :=
    differentiableOn_pi.mpr fun j => BUp_analytic_SU j
  have hPVode : ∀ z ∈ SU \ ({2} : Set ℂ),
      HasDerivAt PV (fun i => Finset.univ.sum (fun j => psysA z i j * PV z j)
        + (fun _ (_ : Fin 7) => (0 : ℂ)) z i) z := by
    intro z hz
    simpa using PV_system_SU z hz
  obtain ⟨Ĝ, hĜd, hĜode, hĜeq⟩ := exists_sol_Om1_of_sol_SU psysA (fun _ _ => 0)
    (fun i j => psysA_diffOn_Om1 i j)
    (fun i => by simpa using (differentiableOn_const (0 : ℂ) : DifferentiableOn ℂ (fun _ : ℂ => (0:ℂ)) (Om1 \ ({2} : Set ℂ))))
    (hPVd.mono Set.sdiff_subset) hPVode
  have hO2 : IsOpen (Om1 \ ({2} : Set ℂ)) := isOpen_Om1_pure_part_lower.sdiff isClosed_singleton
  refine ⟨glueG Ĝ, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzSU : z ∈ SU
    · have hnb : glueG Ĝ =ᶠ[𝓝 z] PV := by
        filter_upwards [isOpen_SU_H_cont.mem_nhds hzSU] with w hw
        exact glueG_of_mem Ĝ hw
      exact ((hPVd.differentiableAt (isOpen_SU_H_cont.mem_nhds hzSU)).congr_of_eventuallyEq hnb).differentiableWithinAt
    · have hz2 : z ≠ 2 := fun h => hzSU (by rw [h]; exact two_mem_SU)
      have hzO : z ∈ Om1 \ ({2} : Set ℂ) := ⟨hz, by simpa using hz2⟩
      have hnb : glueG Ĝ =ᶠ[𝓝 z] Ĝ := by
        filter_upwards [hO2.mem_nhds hzO] with w hw
        by_cases hwSU : w ∈ SU
        · rw [glueG_of_mem Ĝ hwSU]
          exact (hĜeq ⟨hwSU, hw.2⟩).symm
        · exact glueG_of_not_mem Ĝ hwSU
      exact ((hĜd.differentiableAt (hO2.mem_nhds hzO)).congr_of_eventuallyEq hnb).differentiableWithinAt
  · intro z hz
    exact glueG_of_mem Ĝ hz
  · intro z hz hz2
    by_cases hzSU : z ∈ SU
    · have hnb : glueG Ĝ =ᶠ[𝓝 z] PV := by
        filter_upwards [isOpen_SU_H_cont.mem_nhds hzSU] with w hw
        exact glueG_of_mem Ĝ hw
      have h := (PV_system_SU z ⟨hzSU, by simpa using hz2⟩).congr_of_eventuallyEq hnb
      refine h.congr_deriv ?_
      rw [glueG_of_mem Ĝ hzSU] <;> simp
    · have hzO : z ∈ Om1 \ ({2} : Set ℂ) := ⟨hz, by simpa using hz2⟩
      have hnb : glueG Ĝ =ᶠ[𝓝 z] Ĝ := by
        filter_upwards [hO2.mem_nhds hzO] with w hw
        by_cases hwSU : w ∈ SU
        · rw [glueG_of_mem Ĝ hwSU]
          exact (hĜeq ⟨hwSU, hw.2⟩).symm
        · exact glueG_of_not_mem Ĝ hwSU
      have h := (hĜode z hzO).congr_of_eventuallyEq hnb
      refine h.congr_deriv ?_
      rw [glueG_of_not_mem Ĝ hzSU] <;> simp

/-! ## 6. The pure part `PJ` -/

/-- The pure part of the jump relation, built from the extended pure branches. -/
def PJfun (P : Fin 14 → Polynomial ℚ) (G : ℂ → Fin 7 → ℂ) (z : ℂ) : ℂ :=
  ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (G z j - G (wC z) j)

/-- `wC` is holomorphic on `Om1`. -/
lemma wC_diffOn_Om1 : DifferentiableOn ℂ wC Om1 := by
  intro z hz
  have hz1 : z ≠ 1 := fun h => one_notMem_Om1 (by rwa [h] at hz)
  exact (differentiableAt_wC z hz1).differentiableWithinAt

theorem PJfun_diffOn (P : Fin 14 → Polynomial ℚ) (G : ℂ → Fin 7 → ℂ)
    (hG : DifferentiableOn ℂ G Om1) : DifferentiableOn ℂ (PJfun P G) Om1 := by
  refine DifferentiableOn.fun_sum fun j _ => ?_
  refine DifferentiableOn.mul ?_ ?_
  · intro z hz
    exact (pAtY_differentiableAt (p := P (pureIdxA j))
      (fun h => one_notMem_Om1 (by rwa [h] at hz))).differentiableWithinAt
  · refine DifferentiableOn.sub ?_ ?_
    · exact (differentiableOn_pi.mp hG) j
    · exact (differentiableOn_pi.mp (hG.comp wC_diffOn_Om1 (fun z hz => wC_mem_Om1 hz))) j

theorem PJfun_wedge (P : Fin 14 → Polynomial ℚ) (G : ℂ → Fin 7 → ℂ)
    (hG : ∀ z ∈ SU, G z = PV z) {z : ℂ} (hz : z ∈ SU ∩ SL) :
    PJfun P G z = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z)) := by
  have hzSU : z ∈ SU := hz.1
  have hw : wC z ∈ SU := (wC_mem_SU_SL hz).1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hG z hzSU, hG (wC z) hw]
  simp only [PV]

/-! ## 7. Local extension on convex sets -/

lemma isOpen_halfL_pure_part_lower (δ : ℝ) : IsOpen (halfL δ) :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

lemma convex_halfL_pure_part_lower (δ : ℝ) : Convex ℝ (halfL δ) :=
  (convex_ball ninth δ).inter (convex_halfSpace_im_lt 0)

lemma halfL_subset_Om1_pure_part_lower {δ : ℝ} {z : ℂ} (hz : z ∈ halfL δ) : z ∈ Om1 :=
  Or.inl (ne_of_lt hz.2)

lemma halfL_subset_bigball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ} (hz : z ∈ halfL δ) :
    z ∈ Metric.ball ninth (1/10) :=
  Metric.ball_subset_ball (by linarith) hz.1

lemma im_sub_ofReal_mul_I (x y : ℝ) : ((x : ℂ) - (y : ℂ) * Complex.I).im = -y := by
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
    Complex.ofReal_re, mul_one, mul_zero, add_zero, sub_zero]
  ring

lemma im_add_ofReal_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by
  simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
    Complex.ofReal_re, mul_one, mul_zero, add_zero]
  ring

lemma halfL_pt {δ : ℝ} (hδ : 0 < δ) : ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I ∈ halfL δ := by
  have hpt : ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I
      = (((1 / 9 : ℝ)) : ℂ) - (((δ / 2 : ℝ)) : ℂ) * Complex.I := by
    simp [ninth]
  have hnorm : ‖ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I - ninth‖ = δ / 2 := by
    have h : ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I - ninth
        = -((((δ / 2 : ℝ)) : ℂ) * Complex.I) := by ring
    rw [h, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ δ / 2)]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq, hnorm]
    linarith
  · show (ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I).im < 0
    rw [hpt, im_sub_ofReal_mul_I]
    linarith

/-- The upper half of the disc of radius `1/10` around `−1/8`. -/
def uball : Set ℂ := Metric.ball (-(1/8)) (1/10) ∩ {z : ℂ | 0 < z.im}

lemma isOpen_uball : IsOpen uball :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma convex_uball : Convex ℝ uball :=
  (convex_ball _ _).inter (convex_halfSpace_im_gt 0)

lemma uball_subset_Om1 {z : ℂ} (hz : z ∈ uball) : z ∈ Om1 := Or.inl (ne_of_gt hz.2)

lemma uball_pt : (-(1/8) + (((1 / 20 : ℝ)) : ℂ) * Complex.I) ∈ uball := by
  have hnorm : ‖-(1/8) + (((1 / 20 : ℝ)) : ℂ) * Complex.I - (-(1/8))‖ = 1 / 20 := by
    have h : -(1/8) + (((1 / 20 : ℝ)) : ℂ) * Complex.I - (-(1/8))
        = (((1 / 20 : ℝ)) : ℂ) * Complex.I := by ring
    rw [h, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20)]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq, hnorm]
    norm_num
  · show 0 < (-(1/8) + (((1 / 20 : ℝ)) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
      Complex.ofReal_re, mul_one, mul_zero, add_zero]
    norm_num

lemma wC_mem_uball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ} (hz : z ∈ halfL δ) : wC z ∈ uball :=
  ⟨wC_maps_ball hδ20 hz.1, wC_im_pos_of_neg hz.2⟩

/-- A solution of a linear system on a convex set extends to any convex open superset. -/
theorem exists_sol_of_sol_convex {k : ℕ} {U V : Set ℂ} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hUV : U ⊆ V)
    {A : ℂ → Fin k → Fin k → ℂ} {b : ℂ → Fin k → ℂ}
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) V)
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) V)
    {Y : ℂ → Fin k → ℂ} (hYd : DifferentiableOn ℂ Y U)
    (hY : ∀ z ∈ U, HasDerivAt Y (fun i => ∑ j, A z i j * Y z j + b z i) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ F : ℂ → Fin k → ℂ, DifferentiableOn ℂ F V ∧ Set.EqOn F Y U := by
  obtain ⟨F, hFd, hFz₀, hFode⟩ := Work.C17g.linear_ode_convex hVc hVo A b
    (differentiableOn_pi.mpr fun i => differentiableOn_pi.mpr fun j => hA i j)
    (differentiableOn_pi.mpr fun i => hb i) z₀ (hUV hz₀) (Y z₀)
  refine ⟨F, hFd, ?_⟩
  refine Work.OdeCont.uniqueness hUo hUc.isPreconnected A b
    (fun i j => (hA i j).mono hUV) (fun i => (hb i).mono hUV) F Y (hFd.mono hUV) hYd
    ?_ ?_ hz₀ hFz₀
  · intro z hz; exact hFode z (hUV hz)
  · intro z hz; exact hY z hz

/-! ## 8. The germ at `1/9` -/

theorem exists_PB (P : Fin 14 → Polynomial ℚ) (G : ℂ → Fin 7 → ℂ)
    (hGd : DifferentiableOn ℂ G Om1)
    (hGode : ∀ z ∈ Om1, z ≠ 2 → HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j) z)
    {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    ∃ PB : ℂ → ℂ, DifferentiableOn ℂ PB (Metric.ball ninth δ) ∧
      ∀ z ∈ halfL δ, PB z = PJfun P G z := by
  have hne1 : ∀ z ∈ Metric.ball ninth δ, z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    exact one_notMem_ball_ninth (Metric.ball_subset_ball (by linarith) hz)
  have hwCball : DifferentiableOn ℂ wC (Metric.ball ninth δ) := by
    intro z hz
    exact (differentiableAt_wC z (hne1 z hz)).differentiableWithinAt
  have hz0 : ninth - (((δ / 2 : ℝ)) : ℂ) * Complex.I ∈ halfL δ := halfL_pt hδ
  have hodeHalfL : ∀ z ∈ halfL δ,
      HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j
        + (fun _ (_ : Fin 7) => (0 : ℂ)) z i) z := by
    intro z hz
    have hz2 : z ≠ 2 := by
      intro h
      rw [h] at hz
      exact two_notMem_ball_ninth (Metric.ball_subset_ball (by linarith) hz.1)
    simpa using hGode z (halfL_subset_Om1_pure_part_lower hz) hz2
  obtain ⟨F, hFd, hFeq⟩ := exists_sol_of_sol_convex (convex_halfL_pure_part_lower δ) (isOpen_halfL_pure_part_lower δ)
    (convex_ball _ _) Metric.isOpen_ball (fun z hz => halfL_subset_bigball hδ20 hz)
    (fun i j => psysA_diffOn_ball i j)
    (fun i => by
      have h : (fun z : ℂ => (fun _ (_ : Fin 7) => (0 : ℂ)) z i) = fun _ => (0 : ℂ) := by
        funext z; rfl
      rw [h]
      exact differentiableOn_const 0)
    (hGd.mono (fun z hz => halfL_subset_Om1_pure_part_lower hz)) hodeHalfL hz0
  have hodeUball : ∀ z ∈ uball,
      HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j
        + (fun _ (_ : Fin 7) => (0 : ℂ)) z i) z := by
    intro z hz
    have hz2 : z ≠ 2 := by
      intro h
      rw [h] at hz
      exact two_notMem_ball_neg_eighth hz.1
    simpa using hGode z (uball_subset_Om1 hz) hz2
  obtain ⟨H, hHd, hHeq⟩ := exists_sol_of_sol_convex convex_uball isOpen_uball
    (convex_ball _ _) Metric.isOpen_ball (fun z hz => hz.1)
    (fun i j => psysA_diffOn_ball_neg i j)
    (fun i => by
      have h : (fun z : ℂ => (fun _ (_ : Fin 7) => (0 : ℂ)) z i) = fun _ => (0 : ℂ) := by
        funext z; rfl
      rw [h]
      exact differentiableOn_const 0)
    (hGd.mono (fun z hz => uball_subset_Om1 hz)) hodeUball uball_pt
  refine ⟨fun z => ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (F z j - H (wC z) j), ?_, ?_⟩
  · refine DifferentiableOn.fun_sum fun j _ => ?_
    refine DifferentiableOn.mul ?_ ?_
    · intro z hz
      exact (pAtY_differentiableAt (p := P (pureIdxA j)) (hne1 z hz)).differentiableWithinAt
    · refine DifferentiableOn.sub ?_ ?_
      · exact (differentiableOn_pi.mp (hFd.mono (Metric.ball_subset_ball (by linarith)))) j
      · exact (differentiableOn_pi.mp (hHd.comp hwCball
          (fun z hz => wC_maps_ball hδ20 hz))) j
  · intro z hz
    have hw : wC z ∈ uball := wC_mem_uball hδ20 hz
    show (∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (F z j - H (wC z) j))
        = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (G z j - G (wC z) j)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq hz, hHeq hw]

/-! ## 9. Assembly -/

theorem pure_part_lower (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (P : Fin 14 → Polynomial ℚ)
    {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    ∃ (PJ : ℂ → ℂ) (PB : ℂ → ℂ) (m : ℕ),
      DifferentiableOn ℂ PJ Om1 ∧
      (∀ z ∈ SU ∩ SL, PJ z = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z))) ∧
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * PB z) (Metric.ball ninth δ) ∧
      (∀ z ∈ halfL δ, PB z = PJ z) := by
  obtain ⟨G, hGd, hGSU, hGode⟩ := exists_G_Om1
  obtain ⟨PB, hPBd, hPBeq⟩ := exists_PB P G hGd hGode hδ hδ20
  exact ⟨PJfun P G, PB, 0, PJfun_diffOn P G hGd,
    fun z hz => PJfun_wedge P G hGSU hz, by simpa using hPBd, hPBeq⟩

end

end Work.A14D
