/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{k,α}` Schauder (Riesz) estimate for the Bochner–Martinelli potential

The main result of this file is `Work.NN.Core.bmPot_riesz_Ck`: for `0 < α < 1`, a centre `c`,
positive multi-radii `r` and every `k`, there is `C > 0` such that for every family
`f : Fin n → (Fin n → ℂ) → ℂ` whose components are of class `C^k`, have finite `C^{k,α}`-norm
and vanish off the half-size polydisc `polydisc c (r/2)`, the Bochner–Martinelli potential
`bmPotential f` is of class `C^{k+1,α}` on `polydisc c (r/2)` with

  `‖bmPotential f‖_{C^{k+1,α}(polydisc c (r/2))} ≤ C · Sm_j ‖f_j‖_{C^{k,α}(ℂⁿ)}`.

## Route

* `k = 0` is exactly `Work.NN.Core.bmPot_holder_C0a` (the pointwise Vekua argument: `C^{0,α}`
  data give a `C^{1,α}` potential, with the candidate derivative `bmDerivData` obtained as the
  limit of the derivatives of the potentials of the smooth mollifications of the data).
* The inductive step splits `holderNorm (k+2) = holderNorm (k+1) + (order (k+2) part)`
  (`Work.CR.Flat.Cauchy.holderNorm_succ`): the first summand is the induction hypothesis at level
  `k`, the second is `bmPotential_top_gain` below.
* `bmPotential_top_gain` bounds the *top* order `k+1` of `bmPotential f` for `C^k` data.  By the
  commutation identity `bmPotential_iteratedFDeriv`, for every tuple `u : Fin k → ℂⁿ` the slice
  `z ↦ D^k (bmPotential f)(z)[u]` equals `bmPotential (D^k f · u)`, whose datum is continuous,
  compactly supported and `C^{0,α}` with norm `≤ ‖u‖^k · Sm_j ‖f_j‖_{C^{k,α}}`; the `k = 0`
  estimate `bmPot_holder_C0a` (applied with the doubled radii) therefore bounds the `C^{1,α}` norm
  of every slice, uniformly in `u` with the factor `∏ ‖u_i‖`.  Feeding those uniform slice bounds
  into `Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds` (differentiability of the
  multilinear-map-valued function `z ↦ D^k (bmPotential f)(z)` plus the two bounds) gives the
  top-order estimate.  The differentiability of the slices themselves is
  `Work.NN.Core.bmPot_diff_continuous`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup

import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.bmPotential_iter_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_top_bound
import Submission.Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le
import Submission.Work.CR.Flat.Cauchy.exists_multilinearMap_curryLeft
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.NN.Core.bmPot_diff_continuous

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

/-- Decomposition of the Hölder norm: the `C^{k+1,α}`-norm is the `C^{k,α}`-norm plus the
top order `k+1` terms. -/
lemma holderNorm_succ_eq {n : ℕ} (k : ℕ) (α : ℝ) (g : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm (k + 1) α g Ω
      = Work.CR.Flat.holderNorm k α g Ω
        + (Work.CR.Flat.iterDerivNorm (k + 1) g Ω
            + Work.CR.Flat.holderSeminorm (k + 1) α g Ω) := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.sum_range_succ]


/-- If the derivative of `g` is `α`-Hölder on the convex set `Ω`, then `g` is `C^{1,α}` on `Ω`:
`‖g y - g x - fderiv g x (y - x)‖ ≤ K ‖y - x‖ ^ (1 + α)`. -/
private lemma norm_sub_sub_fderiv_le_of_holder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {Ω : Set E} {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hΩ : Convex ℝ Ω)
    (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ g x)
    (hholder : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ K * ‖x - y‖ ^ α)
    {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ K * ‖y - x‖ ^ (1 + α) := by
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω := by
    intro t ht
    have h1 : (1 - t) • x + t • y ∈ Ω := hΩ hx hy (by linarith [ht.1, ht.2]) ht.1 (by ring)
    have h2 : x + t • (y - x) = (1 - t) • x + t • y := by module
    rwa [h2]
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => g (x + t • (y - x)) - t • (fderiv ℝ g x (y - x)))
        ((fderiv ℝ g (x + t • (y - x)) - fderiv ℝ g x) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hcurve : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have h1 : HasDerivAt (fun t : ℝ => g (x + t • (y - x)))
        ((fderiv ℝ g (x + t • (y - x))) (y - x)) t :=
      ((hdiff _ (hmem t ht)).hasFDerivAt).comp_hasDerivAt t hcurve
    have h2 : HasDerivAt (fun t : ℝ => t • (fderiv ℝ g x (y - x))) (fderiv ℝ g x (y - x)) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ g x (y - x))
    have h3 : HasDerivAt (fun t : ℝ => g (x + t • (y - x)) - t • (fderiv ℝ g x (y - x)))
        ((fderiv ℝ g (x + t • (y - x))) (y - x) - (fderiv ℝ g x) (y - x)) t := h1.sub h2
    rw [sub_apply]
    exact h3.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖((fderiv ℝ g (x + t • (y - x)) - fderiv ℝ g x) (y - x))‖ ≤ K * ‖y - x‖ ^ (1 + α) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hHt := hholder (x + t • (y - x)) (hmem t ⟨ht.1, ht1⟩) x hx
    rw [show (x + t • (y - x)) - x = t • (y - x) from by abel,
      show ‖t • (y - x)‖ = t * ‖y - x‖ from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]] at hHt
    calc ‖((fderiv ℝ g (x + t • (y - x)) - fderiv ℝ g x) (y - x))‖
        ≤ ‖fderiv ℝ g (x + t • (y - x)) - fderiv ℝ g x‖ * ‖y - x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (t * ‖y - x‖) ^ α) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hHt (norm_nonneg _)
      _ ≤ (K * ‖y - x‖ ^ α) * ‖y - x‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK) (norm_nonneg _)
          rw [Real.mul_rpow ht0 (norm_nonneg _)]
          exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_le_one ht0 ht1 hα.le)
      _ = K * ‖y - x‖ ^ (1 + α) := by
          rw [Work.NN.Core.rpow_one_add_mul hα (norm_nonneg _)]; ring
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => g (x + t • (y - x)) - t • (fderiv ℝ g x (y - x))) hderiv hbound 1
    (by norm_num)
  rw [show x + (1 : ℝ) • (y - x) = y from by rw [one_smul]; abel,
    show x + (0 : ℝ) • (y - x) = x from by rw [zero_smul, add_zero],
    show (1 : ℝ) • (fderiv ℝ g x (y - x)) = fderiv ℝ g x (y - x) from by rw [one_smul],
    show (0 : ℝ) • (fderiv ℝ g x (y - x)) = 0 from by rw [zero_smul],
    sub_zero, sub_zero, mul_one] at hseg
  convert hseg using 2
  abel

/-- **Top iterated derivative bounds from uniform bounds on the derivatives of the slices.**

The `(k+1)`-st iterated derivative of `F` is, by definition, the uncurried Fréchet derivative of
the multilinear-map-valued function `z ↦ D^k F z`, whose slices `z ↦ D^k F z u` are assumed
differentiable on the open convex set `Ω` with derivatives bounded by `K · ∏ ‖u_i‖` and uniformly
`α`-Hölder with the same bound.  Then `z ↦ D^k F z` is differentiable on `Ω` — its curried
derivative is built from the slice derivatives by
`Work.CR.Flat.Cauchy.exists_multilinearMap_curryLeft` — and both the pointwise bound and the
`α`-Hölder bound for `D^{k+1} F` on `Ω` follow.

(For `k = 0` the hypotheses are the differentiability, boundedness and `α`-Hölder continuity of
`fderiv ℝ F` on `Ω`, and the conclusion is the corresponding statement for `fderiv ℝ F`.) -/
private lemma iteratedFDeriv_succ_of_slice_bounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {F : E → ℂ} {Ω : Set E} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ u : Fin k → E, ∀ z ∈ Ω,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k F y u) z)
    (hbound : ∀ u : Fin k → E, ∀ z ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ K * ∏ i, ‖u i‖)
    (hholder : ∀ u : Fin k → E, ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ K * (∏ i, ‖u i‖) * ‖z - z'‖ ^ α) :
    (∀ z ∈ Ω, ∀ w : Fin (k + 1) → E,
      ‖iteratedFDeriv ℝ (k + 1) F z w‖ ≤ K * ∏ i, ‖w i‖) ∧
    (∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖iteratedFDeriv ℝ (k + 1) F z - iteratedFDeriv ℝ (k + 1) F z'‖
        ≤ K * ‖z - z'‖ ^ α) := by
  classical
  -- the value of the top derivative at every point of `Ω`
  have hval : ∀ z ∈ Ω, ∀ w : Fin (k + 1) → E,
      iteratedFDeriv ℝ (k + 1) F z w
        = fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z (w 0) := by
    intro z hz w
    let φ : (Fin k → E) → (E →L[ℝ] ℂ) :=
      fun u => fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
    have hadd : ∀ (u : Fin k → E) (i : Fin k) (x y : E),
        φ (Function.update u i (x + y)) = φ (Function.update u i x) + φ (Function.update u i y) := by
      intro u i x y
      have hfun : (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i (x + y)))
          = (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i x))
            + (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i y)) := by
        funext y'
        exact ContinuousMultilinearMap.map_update_add (iteratedFDeriv ℝ k F y') u i x y
      show fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i (x + y))) z
          = fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i x)) z
            + fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i y)) z
      rw [hfun]
      exact fderiv_add (hdiff _ z hz) (hdiff _ z hz)
    have hsmul : ∀ (u : Fin k → E) (i : Fin k) (a : ℝ) (x : E),
        φ (Function.update u i (a • x)) = a • φ (Function.update u i x) := by
      intro u i a x
      have hfun : (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i (a • x)))
          = a • (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i x)) := by
        funext y'
        exact ContinuousMultilinearMap.map_update_smul (iteratedFDeriv ℝ k F y') u i a x
      show fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i (a • x))) z
          = a • fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' (Function.update u i x)) z
      rw [hfun]
      exact fderiv_const_smul (hdiff _ z hz) a
    obtain ⟨M, hMval, -⟩ :=
      Work.CR.Flat.Cauchy.exists_multilinearMap_curryLeft hK hadd hsmul
        (fun u => hbound u z hz)
    have hHas : HasFDerivAt (fun y => iteratedFDeriv ℝ k F y) M.curryLeft z := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
      have htay : ∀ h, z + h ∈ Ω →
          ‖(fun y => iteratedFDeriv ℝ k F y) (z + h) - (fun y => iteratedFDeriv ℝ k F y) z
            - M.curryLeft h‖ ≤ K * ‖h‖ ^ (1 + α) := by
        intro h hzh
        refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
        have hMcons : (M.curryLeft h) v = φ v h := by
          rw [ContinuousMultilinearMap.curryLeft_apply, hMval, Fin.tail_cons, Fin.cons_zero]
        show ‖(fun y => iteratedFDeriv ℝ k F y) (z + h) v - (fun y => iteratedFDeriv ℝ k F y) z v
            - (M.curryLeft h) v‖ ≤ (K * ‖h‖ ^ (1 + α)) * ∏ i, ‖v i‖
        rw [hMcons]
        have hslice := norm_sub_sub_fderiv_le_of_holder (g := fun y => iteratedFDeriv ℝ k F y v)
          hα (mul_nonneg hK (Finset.prod_nonneg fun i _ => norm_nonneg _)) hΩconv
          (fun x hx => hdiff v x hx) (fun x hx y hy => hholder v x hx y hy) hz hzh
        rw [add_sub_cancel_left] at hslice
        calc ‖(fun y => iteratedFDeriv ℝ k F y) (z + h) v - (fun y => iteratedFDeriv ℝ k F y) z v
              - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y v) z h‖
            = ‖(fun y => iteratedFDeriv ℝ k F y v) (z + h) - (fun y => iteratedFDeriv ℝ k F y v) z
                - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y v) z h‖ := rfl
          _ ≤ K * (∏ i, ‖v i‖) * ‖h‖ ^ (1 + α) := hslice
          _ = (K * ‖h‖ ^ (1 + α)) * ∏ i, ‖v i‖ := by ring
      have hseg : ∀ᶠ h in 𝓝 (0 : E), z + h ∈ Ω := by
        have hz' : Tendsto (fun h : E => z + h) (𝓝 0) (𝓝 z) := by
          simpa using (tendsto_const_nhds.add
            (tendsto_id : Tendsto (fun h : E => h) (𝓝 0) (𝓝 0)))
        exact hz'.eventually (hΩopen.mem_nhds hz)
      have hcont : Tendsto (fun h : E => K * ‖h‖ ^ α) (𝓝 0) (𝓝 0) := by
        have h1 : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_norm.tendsto (0 : E))
        have h2 : Tendsto (fun h : E => ‖h‖ ^ α) (𝓝 0) (𝓝 (0 ^ α)) :=
          (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h1
        rw [Real.zero_rpow (ne_of_gt hα)] at h2
        simpa using h2.const_mul K
      have hev : ∀ᶠ h in 𝓝 (0 : E), K * ‖h‖ ^ α < ε := (tendsto_order.1 hcont).2 ε hε
      filter_upwards [hseg, hev] with h hzh hlt
      calc ‖(fun y => iteratedFDeriv ℝ k F y) (z + h) - (fun y => iteratedFDeriv ℝ k F y) z
              - M.curryLeft h‖
          ≤ K * ‖h‖ ^ (1 + α) := htay h hzh
        _ = (K * ‖h‖ ^ α) * ‖h‖ := by
            rw [Work.NN.Core.rpow_one_add_mul hα (norm_nonneg h), mul_assoc]
        _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg h)
    rw [iteratedFDeriv_succ_apply_left, hHas.fderiv,
      ContinuousMultilinearMap.curryLeft_apply, hMval, Fin.cons_self_tail]
  constructor
  · intro z hz w
    rw [hval z hz w]
    calc ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z (w 0)‖
        ≤ ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z‖ * ‖w 0‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * ∏ i, ‖Fin.tail w i‖) * ‖w 0‖ :=
          mul_le_mul_of_nonneg_right (hbound (Fin.tail w) z hz) (norm_nonneg _)
      _ = K * ∏ i, ‖w i‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring
  · intro z hz z' hz'
    refine ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) α)) fun w => ?_
    rw [sub_apply, hval z hz w, hval z' hz' w]
    calc ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z (w 0)
            - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z' (w 0)‖
        = ‖(fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z
            - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z') (w 0)‖ := rfl
      _ ≤ ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z
            - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z'‖ * ‖w 0‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (∏ i, ‖Fin.tail w i‖) * ‖z - z'‖ ^ α) * ‖w 0‖ :=
          mul_le_mul_of_nonneg_right (hholder (Fin.tail w) z hz z' hz') (norm_nonneg _)
      _ = (K * ‖z - z'‖ ^ α) * ∏ i, ‖w i‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring

/-- **Top-order Schauder bound for the Bochner–Martinelli potential of `C^{k,α}` data.**

For `0 < α < 1`, a centre `c`, positive multi-radii `r` and `k : ℕ` there is `C > 0` such that
for every family `f` with `C^k` components, finite `C^{k,α}`-norm and supported in the half-size
polydisc `polydisc c (r/2)`, the `(k+1)`-st iterated derivative of `bmPotential f` is bounded on
`polydisc c (r/2)` together with its `α`-Hölder seminorm:

  `‖D^{k+1} (bmPotential f)‖_{sup} + ‖D^{k+1} (bmPotential f)‖_{α} ≤ C Sm_j ‖f_j‖_{C^{k,α}}`. -/
theorem bmPotential_top_gain {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ k (f j)) →
      (∀ j, Work.CR.Flat.holderNorm k α (f j) Set.univ < ⊤) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
      Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c (fun j => r j / 2))
        + Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
  classical
  -- the `C^{0,α}` estimate for the datum, on the doubled polydisc `polydisc c (2r)`
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.NN.Core.bmPot_holder_C0a (n := n) hn (c := c)
    (r := fun j => 2 * r j) hα hα1 (fun j => by linarith [hr j])
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro f hf hffin hfsup
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc c (fun j => r j / 2) with hPdef
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc c _
  have hPconv : Convex ℝ P := Work.NN.Core.convex_polydisc c _
  have hsub : P ⊆ Work.CR.Flat.polydisc c r := by
    rw [hPdef]
    exact Work.CR.Flat.polydisc_mono (fun j => by linarith [hr j])
  -- the total size of the data, as a real number
  set Sm : ℝ := ∑ j, (Work.CR.Flat.holderNorm k α (f j) Set.univ).toReal with hSmdef
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hsumlt : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) < ⊤ := by
    rw [ENNReal.sum_lt_top]
    exact fun j _ => hffin j
  have hsum_eq : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) = ENNReal.ofReal Sm := by
    rw [hSmdef, ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (ne_of_lt (hffin j))).symm
  -- ### the derived datum `ψ u = D^k f · u`
  set ψ : (Fin k → (Fin n → ℂ)) → Fin n → (Fin n → ℂ) → ℂ :=
    fun u j y => iteratedFDeriv ℝ k (f j) y u with hψdef
  have hψcont : ∀ u j, Continuous (ψ u j) := by
    intro u j
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ u).continuous).comp
      ((hf j).continuous_iteratedFDeriv (m := k) le_rfl)
  -- the derived datum vanishes outside the polydisc of radii `r`
  have hψsupp : ∀ u j z, (∃ i, r i ≤ ‖z i - c i‖) → ψ u j z = 0 := by
    intro u j z hz
    obtain ⟨i, hi⟩ := hz
    have hev : f j =ᶠ[𝓝 z] (0 : (Fin n → ℂ) → ℂ) := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds z (half_pos (hr i))) ?_
      intro w hw
      apply hfsup j w
      refine ⟨i, ?_⟩
      have h1 : ‖w i - z i‖ ≤ dist w z := by
        rw [dist_eq_norm]
        exact norm_le_pi_norm (w - z) i
      have h2 : ‖z i - c i‖ ≤ ‖w i - c i‖ + ‖w i - z i‖ := by
        have h4 : ‖z i - c i‖ ≤ ‖z i - w i‖ + ‖w i - c i‖ := by
          calc ‖z i - c i‖ = ‖(z i - w i) + (w i - c i)‖ := by ring_nf
            _ ≤ ‖z i - w i‖ + ‖w i - c i‖ := norm_add_le _ _
        rw [norm_sub_rev (z i) (w i)] at h4
        linarith
      have h3 : dist w z < r i / 2 := by
        simpa only [Metric.mem_ball, dist_comm] using hw
      linarith
    have h2 : iteratedFDeriv ℝ k (f j) z = iteratedFDeriv ℝ k (0 : (Fin n → ℂ) → ℂ) z :=
      (hev.iteratedFDeriv ℝ k).eq_of_nhds
    show iteratedFDeriv ℝ k (f j) z u = 0
    rw [h2]
    simp
  -- the `C^{0,α}`-norm of the derived datum
  have hψnorm : ∀ u j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖u i‖) * Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    intro u j
    exact Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le (m := k) le_rfl (α := α) u
  have hψfin : ∀ u j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ < ⊤ := by
    intro u j
    refine lt_of_le_of_lt (hψnorm u j) ?_
    rw [ENNReal.mul_lt_top_iff]
    exact Or.inl ⟨ENNReal.ofReal_lt_top, hffin j⟩
  have hψsum : ∀ u, (∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ)
      ≤ ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm := by
    intro u
    calc (∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ)
        ≤ ∑ j, ENNReal.ofReal (∏ i, ‖u i‖) * Work.CR.Flat.holderNorm k α (f j) Set.univ :=
          Finset.sum_le_sum fun j _ => hψnorm u j
      _ = ENNReal.ofReal (∏ i, ‖u i‖) * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm := by rw [hsum_eq]
  -- ### the `C^{1,α}` bound for the potential of the derived datum, on `polydisc c r`
  have h1α : ∀ u, Work.CR.Flat.holderNorm 1 α
        (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z) (Work.CR.Flat.polydisc c r)
      ≤ ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
    intro u
    have hsupp2 : ∀ j z, (∃ i, (2 * r i) / 2 ≤ ‖z i - c i‖) → ψ u j z = 0 := by
      intro j z hz
      obtain ⟨i, hi⟩ := hz
      exact hψsupp u j z ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩
    have hmain := hC₀ (ψ u) hsupp2 (fun j => ne_of_lt (hψfin u j))
    have hpd : (fun j : Fin n => (2 * r j) / 2) = r := by funext j; ring
    calc Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z)
          (Work.CR.Flat.polydisc c r)
        = Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.Cauchy.bmPot (ψ u) z)
          (Work.CR.Flat.polydisc c (fun j => (2 * r j) / 2)) := by rw [hpd]
      _ ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm 0 α (ψ u j) Set.univ := hmain
      _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm) :=
          mul_le_mul_right (hψsum u) _
      _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
          calc ENNReal.ofReal C₀ * (ENNReal.ofReal (∏ i, ‖u i‖) * ENNReal.ofReal Sm)
              = (ENNReal.ofReal C₀ * ENNReal.ofReal (∏ i, ‖u i‖)) * ENNReal.ofReal Sm := by
                rw [mul_assoc]
            _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖)) * ENNReal.ofReal Sm := by
                rw [← ENNReal.ofReal_mul hC₀pos.le]
            _ = ENNReal.ofReal (C₀ * (∏ i, ‖u i‖) * Sm) := by
                rw [← ENNReal.ofReal_mul (mul_nonneg hC₀pos.le
                  (Finset.prod_nonneg fun i _ => norm_nonneg _))]
  -- ### the slice bounds required by the top-order currying lemma
  have hslice_bound : ∀ u, ∀ z ∈ P,
      ‖fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z‖ ≤ (C₀ * Sm) * ∏ i, ‖u i‖ := by
    intro u z hz
    have hfun : (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y)
        = fun y => Work.CR.Flat.Cauchy.bmPot (ψ u) y :=
      funext fun y => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (ψ u) y
    rw [hfun]
    have hC : 0 ≤ C₀ * (∏ i, ‖u i‖) * Sm := by
      refine mul_nonneg (mul_nonneg hC₀pos.le (Finset.prod_nonneg fun i _ => norm_nonneg _)) hSm0
    have h4 := Work.NN.Core.holderNorm_one_bounds (Work.CR.Flat.isOpen_polydisc c r) hC (h1α u)
    have hz' := h4.2.2.1 z (hsub hz)
    rwa [show C₀ * (∏ i, ‖u i‖) * Sm = (C₀ * Sm) * ∏ i, ‖u i‖ from by ring] at hz'
  have hslice_holder : ∀ u, ∀ z ∈ P, ∀ z' ∈ P,
      ‖fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z
        - fderiv ℝ (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y) z'‖
      ≤ ((C₀ * Sm) * ∏ i, ‖u i‖) * ‖z - z'‖ ^ α := by
    intro u z hz z' hz'
    have hfun : (fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y)
        = fun y => Work.CR.Flat.Cauchy.bmPot (ψ u) y :=
      funext fun y => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (ψ u) y
    rw [hfun]
    have hC : 0 ≤ C₀ * (∏ i, ‖u i‖) * Sm := by
      refine mul_nonneg (mul_nonneg hC₀pos.le (Finset.prod_nonneg fun i _ => norm_nonneg _)) hSm0
    have h4 := Work.NN.Core.holderNorm_one_bounds (Work.CR.Flat.isOpen_polydisc c r) hC (h1α u)
    have hz'' := h4.2.2.2 z (hsub hz) z' (hsub hz')
    rwa [show C₀ * (∏ i, ‖u i‖) * Sm = (C₀ * Sm) * ∏ i, ‖u i‖ from by ring] at hz''
  -- ### the slices of `D^k (bmPotential f)` are the potentials of the derived data
  have hslice : ∀ u, (fun y => iteratedFDeriv ℝ k (Work.CR.Flat.Cauchy.bmPotential f) y u)
      = fun y => Work.CR.Flat.Cauchy.bmPotential (ψ u) y := by
    intro u
    funext y
    exact Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv (n := n) hn (c := c) (R := r) hr
      (G := f) hf hfsup u y
  have hslice_diff : ∀ u, ∀ z ∈ P,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k (Work.CR.Flat.Cauchy.bmPotential f) y u) z := by
    intro u z hz
    rw [hslice u]
    exact Work.NN.Core.bmPot_diff_continuous (n := n) hn (c := c) (r := fun j => 2 * r j) hα hα1
      (fun j => by linarith [hr j]) (hψcont u) (fun j => hψfin u j)
      (fun j w hw => by
        obtain ⟨i, hi⟩ := hw
        exact hψsupp u j w ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩)
      z (by
        rw [show (fun j : Fin n => (2 * r j) / 2) = r from funext fun j => by ring]
        exact hsub hz)
  -- ### the top-order estimate via the currying lemma
  have htop := iteratedFDeriv_succ_of_slice_bounds (F := Work.CR.Flat.Cauchy.bmPotential f)
    (Ω := P) hPopen hPconv hα (mul_nonneg hC₀pos.le hSm0)
    hslice_diff
    (fun u z hz => by rw [hslice u]; exact hslice_bound u z hz)
    (fun u z hz z' hz' => by rw [hslice u]; exact hslice_holder u z hz z' hz')
  -- ### extract the two top-order bounds and add them
  have htop1 : Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    rw [show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z
        = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z from
        iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz]
    calc ENNReal.ofReal ‖iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z‖
        ≤ ENNReal.ofReal (C₀ * Sm) := ENNReal.ofReal_le_ofReal
          (ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC₀pos.le hSm0)
            (fun w => htop.1 z hz w))
      _ = ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
          rw [hsum_eq, ENNReal.ofReal_mul hC₀pos.le]
  have htop2 : Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz => ?_
    rw [show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z
          = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z from
          iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz,
        show iteratedFDerivWithin ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P z'
          = iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z' from
          iteratedFDerivWithin_of_isOpen (k + 1) hPopen hz']
    have hb : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
    calc ENNReal.ofReal (‖iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z
            - iteratedFDeriv ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) z'‖ / ‖z - z'‖ ^ α)
        ≤ ENNReal.ofReal (((C₀ * Sm) * ‖z - z'‖ ^ α) / ‖z - z'‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (htop.2 z hz z' hz') hb.le)
      _ = ENNReal.ofReal (C₀ * Sm) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hb)]
      _ = ENNReal.ofReal C₀ * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
          rw [hsum_eq, ENNReal.ofReal_mul hC₀pos.le]
  calc Work.CR.Flat.iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential f) P
        + Work.CR.Flat.holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f) P
      ≤ ENNReal.ofReal C₀ * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ)
        + ENNReal.ofReal C₀ * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) :=
        add_le_add htop1 htop2
    _ = ENNReal.ofReal (2 * C₀)
          * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) := by
        rw [← add_mul, ← ENNReal.ofReal_add hC₀pos.le hC₀pos.le]
        congr 1
        ring

/-- **The `C^{k,α}` Schauder estimate for the Bochner–Martinelli potential** (top-level statement,
the lemma requested for the Newlander–Nirenberg development). -/
theorem bmPot_riesz_Ck {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ k (f j)) →
      (∀ j, Work.CR.Flat.holderNorm k α (f j) Set.univ < ⊤) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
      Work.CR.Flat.holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
        (Work.CR.Flat.polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
  classical
  induction k with
  | zero =>
    obtain ⟨C, hCpos, hC⟩ := Work.NN.Core.bmPot_holder_C0a (n := n) hn (c := c) (r := r)
      hα hα1 hr
    refine ⟨C, hCpos, fun f hf hffin hfsup => ?_⟩
    have hfun : (fun z => Work.CR.Flat.Cauchy.bmPot f z)
        = Work.CR.Flat.Cauchy.bmPotential f :=
      funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f z).symm
    rw [← hfun]
    exact hC f hfsup (fun j => ne_of_lt (hffin j))
  | succ k ih =>
    obtain ⟨C₁, hC₁pos, hC₁⟩ := ih
    obtain ⟨C₂, hC₂pos, hC₂⟩ :=
      Work.NN.Core.bmPotential_top_gain (n := n) hn (c := c) (r := r) hα hα1 hr (k + 1)
    refine ⟨C₁ + C₂, by positivity, fun f hf hffin hfsup => ?_⟩
    have hf' : ∀ j, ContDiff ℝ k (f j) := fun j => (hf j).of_le (by exact_mod_cast Nat.le_succ k)
    have hffin' : ∀ j, Work.CR.Flat.holderNorm k α (f j) Set.univ < ⊤ := fun j =>
      lt_of_le_of_lt (Work.CR.Flat.holderNorm_mono_k (Nat.le_succ k) α (f j) Set.univ) (hffin j)
    have hlow := hC₁ f hf' hffin' hfsup
    have htop := hC₂ f hf hffin hfsup
    have hsummono : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ)
        ≤ ∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ :=
      Finset.sum_le_sum fun j _ =>
        Work.CR.Flat.holderNorm_mono_k (Nat.le_succ k) α (f j) Set.univ
    show Work.CR.Flat.holderNorm (k + 1 + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
        (Work.CR.Flat.polydisc c (fun j => r j / 2))
      ≤ ENNReal.ofReal (C₁ + C₂) * ∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ
    rw [Work.NN.Core.holderNorm_succ_eq (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
      (Work.CR.Flat.polydisc c (fun j => r j / 2))]
    calc Work.CR.Flat.holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
            (Work.CR.Flat.polydisc c (fun j => r j / 2))
          + (Work.CR.Flat.iterDerivNorm (k + 1 + 1) (Work.CR.Flat.Cauchy.bmPotential f)
              (Work.CR.Flat.polydisc c (fun j => r j / 2))
            + Work.CR.Flat.holderSeminorm (k + 1 + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
              (Work.CR.Flat.polydisc c (fun j => r j / 2)))
        ≤ ENNReal.ofReal C₁ * (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ)
          + ENNReal.ofReal C₂ * (∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ) :=
          add_le_add hlow htop
      _ ≤ ENNReal.ofReal C₁ * (∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ)
          + ENNReal.ofReal C₂ * (∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ) :=
          add_le_add (mul_le_mul_right hsummono _) le_rfl
      _ = ENNReal.ofReal (C₁ + C₂)
            * (∑ j, Work.CR.Flat.holderNorm (k + 1) α (f j) Set.univ) := by
          rw [← add_mul, ← ENNReal.ofReal_add hC₁pos.le hC₂pos.le]

end Work.NN.Core
