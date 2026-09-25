import Mathlib
import Submission.Work.Core.Std
import Submission.Work.Core.Solvable
import Submission.Work.CR.Flat.Cauchy.exists_dbarC_solution_disc
import Submission.Work.CR.Flat.Cauchy.exists_dbarC_solution_disc_Ck
import Submission.Work.CR.Flat.Cauchy.contDiff_cauchyTransform
import Submission.Work.CR.Flat.Cauchy.holderNorm_one_cauchyTransform_le
import Submission.Work.Beltrami.CauchyEstimatesInstance
import Submission.Work.Beltrami.smooth_of_beurling_fixed

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

noncomputable section

/-! ## The proof as implemented

The argument below follows the *Beltrami* route to the planar `∂̄`-equation rather than the
contraction in `C^{k,α}` sketched above: the estimates of the Beltrami argument are collected in
`Work.Beltrami.CauchyEstimates` (`Work/Beltrami/Solve.lean`), and `Work.Beltrami.LocalHolInput`
provides a `C^∞` `J`-holomorphic function with nowhere vanishing differential near any point of a
smooth complex structure on `ℂ`.  `exists_jHol_at_of_cauchy` transfers it to `E 1 = ℝ²` along the
linear isometry `eC` (so that the standard-form hypothesis never has to be unfolded explicitly),
and `dbarSolvable_of_jHol` converts a `J`-holomorphic function with invertible differential into
the `∂̄`-solvability statement `DbarSolvable`.

The one gap in `Work.Beltrami.CauchyEstimatesInstance` — the smoothness `smoothFixed` of the fixed
point of the Beltrami equation, whose proof
`Work.Beltrami.smooth_of_beurling_fixed` is not available in the workspace — is filled here by
`smooth_of_beurling_fixed_aux` (which reduces smoothness to the `L²`-boundedness of the Beurling
transform) applied to `Work.Beltrami.beurling_isometry_L2`. -/

/-- The smoothness input of the Beltrami argument, obtained from
`Work.Beltrami.smooth_of_beurling_fixed_aux` together with the `L²`-boundedness of the Beurling
transform `Work.Beltrami.beurling_isometry_L2`.  This is the statement left unproved in
`Work.Beltrami.CauchyEstimatesInstance`. -/
theorem smoothFixedNN : ∀ R α K R' : ℝ, 0 < α → α < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ (μ f u : ℂ → ℂ),
    ContDiff ℝ ∞ μ → HasCompactSupport μ → (∀ z, ‖μ z‖ ≤ δ) →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ z, ‖f z‖ ≤ R) → (∀ z, ‖u z‖ ≤ R) →
    (∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α) → (∀ z, R' < ‖z‖ → u z = 0) →
    (∀ z, u z = f z + μ z * Work.Beltrami.beurling u z) → ContDiff ℝ ∞ u :=
  Work.Beltrami.smooth_of_beurling_fixed_aux (by
    obtain ⟨C, hC, h⟩ := Work.Beltrami.beurling_isometry_L2
    exact ⟨C, hC, fun {α M K r} {g} hα hα1 hg hM hK hsupp =>
      h hα hα1 (le_max_right r 0) hg hM hK
        (fun z hz => hsupp z (lt_of_le_of_lt (le_max_left r 0) hz))⟩)

/-- The associated smallness window. -/
noncomputable def smoothDeltaNN (R α K R' : ℝ) : ℝ :=
  if h : 0 < α ∧ α < 1 then (smoothFixedNN R α K R' h.1 h.2).choose else 1

theorem smoothDeltaNN_pos (R α K R' : ℝ) : 0 < smoothDeltaNN R α K R' := by
  unfold smoothDeltaNN
  split_ifs with h
  · exact (smoothFixedNN R α K R' h.1 h.2).choose_spec.1
  · norm_num

/-- **The analytic estimates of the Beltrami argument, with the smoothness step discharged.**
`Work.Beltrami.cauchyEstimates` differs from this instance only in the fields `smoothDelta`,
`smoothDelta_pos` and `smoothFixed`: there they come from `Work.Beltrami.smooth_of_beurling_fixed`
(whose proof is not available in the workspace), while here they come from `smoothFixedNN`
above. -/
noncomputable def cauchyEstimatesNN : Work.Beltrami.CauchyEstimates :=
  { Work.Beltrami.cauchyEstimates with
    smoothDelta := smoothDeltaNN
    smoothDelta_pos := smoothDeltaNN_pos
    smoothFixed := by
      intro R α K R' hα hα1 μ f u hμs hμc hμb hfs hfc hfb hub hKu hsupp heq
      have hδ : smoothDeltaNN R α K R' = (smoothFixedNN R α K R' hα hα1).choose := by
        unfold smoothDeltaNN
        exact dif_pos (show 0 < α ∧ α < 1 from ⟨hα, hα1⟩)
      exact (smoothFixedNN R α K R' hα hα1).choose_spec.2 μ f u hμs hμc
        (by rw [← hδ]; exact hμb) hfs hfc hfb hub hKu hsupp heq }

/-- **Local existence of a `J`-holomorphic function with nowhere vanishing differential**, for a
smooth almost complex structure `J` on `E 1 = ℝ²`, from the analytic estimates `H` of the Beltrami
argument.  This is the purely analytic core of the `n = 1` case of Newlander–Nirenberg, stated
without the standard-form hypothesis; the proof is the transfer of the planar Beltrami solution to
`E 1 = ℝ²` along the linear isometry `eC`, exactly as in
`Work.Beltrami.newlander_nirenberg_one_of_hol`. -/
theorem exists_jHol_at_of_cauchy (H : Work.Beltrami.CauchyEstimates)
    {U : Set (E 1)} (hU : IsOpen U) {J : E 1 → E 1 →L[ℝ] E 1}
    (hJ : IsAlmostComplexOn J U) {x : E 1} (hx : x ∈ U) :
    ∃ V : Set (E 1), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ u : E 1 → ℂ,
      ContDiffOn ℝ ∞ u V ∧
      (∀ y ∈ V, ∀ v : E 1, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v) ∧
      (∀ y ∈ V, fderiv ℝ u y ≠ 0) := by
  have Hsolve : Work.Beltrami.LocalHolInput :=
    Work.Beltrami.localHolInput_of_cauchyEstimates H
  classical
  obtain ⟨hJsm, hJJ2⟩ := hJ
  obtain ⟨δ₀, hδ₀pos, hδ₀U⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  -- the structure pulled back to `ℂ`
  let J₁ : ℂ → ℂ →L[ℝ] ℂ := Work.Beltrami.pullback Work.Beltrami.eC x J
  have hJ₁apply : ∀ z v : ℂ, J₁ z v
      = Work.Beltrami.eC (J (x + (Work.Beltrami.eC).symm z) ((Work.Beltrami.eC).symm v)) := by
    intro z v; simp [J₁, Work.Beltrami.pullback]
  -- a radius on which the pulled-back structure is defined
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.continuousAt_iff.mp
      ((continuous_iff_continuousAt.mp (Work.Beltrami.eC).symm.continuous) (0 : ℂ)) δ₀ hδ₀pos
  have himg : ∀ z : ℂ, dist z 0 < δ₁ → x + (Work.Beltrami.eC).symm z ∈ U := by
    intro z hz
    apply hδ₀U
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h1 := hδ₁ hz
    rw [dist_eq_norm] at h1
    have h2 : (Work.Beltrami.eC).symm (0 : ℂ) = (0 : E 1) := map_zero (Work.Beltrami.eC).symm
    rw [h2, sub_zero] at h1
    simpa using h1
  have hJ₁sm : ContDiffOn ℝ ∞ J₁ (Metric.ball 0 δ₁) := by
    rw [contDiffOn_clm_apply]
    intro v
    have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => J (x + (Work.Beltrami.eC).symm z))
        (Metric.ball 0 δ₁) :=
      hJsm.comp (by fun_prop) (fun z hz => himg z (by simpa [Metric.mem_ball] using hz))
    have h3 : ContDiffOn ℝ ∞ (fun z : ℂ => (J (x + (Work.Beltrami.eC).symm z))
        ((Work.Beltrami.eC).symm v)) (Metric.ball 0 δ₁) :=
      h2.clm_apply contDiffOn_const
    exact (ContinuousLinearMap.contDiff (n := ∞)
      ((Work.Beltrami.eC : E 1 →L[ℝ] ℂ))).comp_contDiffOn h3
  have hJ₁2 : ∀ z ∈ Metric.ball 0 δ₁, ∀ v : ℂ, J₁ z (J₁ z v) = -v := by
    intro z hz v
    have hzU : x + (Work.Beltrami.eC).symm z ∈ U := himg z (by simpa [Metric.mem_ball] using hz)
    rw [hJ₁apply, hJ₁apply]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rw [hJJ2 _ hzU ((Work.Beltrami.eC).symm v)]
    simp
  -- apply the local input
  obtain ⟨w, σ, hσpos, hwsm, hwhol, hwne⟩ := Hsolve 0 hδ₁pos hJ₁sm hJ₁2
  -- a radius around `x` on which everything holds
  obtain ⟨ε, hεpos, hε⟩ :=
    Metric.continuousAt_iff.mp
      ((continuous_iff_continuousAt.mp (Work.Beltrami.eC : E 1 →L[ℝ] ℂ).continuous)
        (0 : E 1)) σ hσpos
  set V : Set (E 1) := Metric.ball x (min ε (min δ₁ δ₀)) with hV
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hxV : x ∈ V := by
    simp only [hV, Metric.mem_ball, dist_self]
    exact lt_min hεpos (lt_min hδ₁pos hδ₀pos)
  have hVU : V ⊆ U := by
    intro y hy
    apply hδ₀U
    simp only [hV, Metric.mem_ball, dist_eq_norm] at hy ⊢
    linarith [hy, min_le_right ε (min δ₁ δ₀), min_le_right δ₁ δ₀]
  have hball : ∀ y ∈ V, Work.Beltrami.eC (y - x) ∈ Metric.ball 0 σ := by
    intro y hy
    have h1 : dist (y - x) 0 < ε := by
      simp only [hV, Metric.mem_ball, dist_eq_norm] at hy
      rw [dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le hy (min_le_left ε (min δ₁ δ₀))
    have h2 := hε h1
    rw [dist_eq_norm] at h2
    have h3 : (Work.Beltrami.eC : E 1 →L[ℝ] ℂ) 0 = (0 : ℂ) := map_zero (Work.Beltrami.eC : E 1 →L[ℝ] ℂ)
    rw [h3, sub_zero] at h2
    simpa [Metric.mem_ball, dist_eq_norm] using h2
  have hdiff : ∀ y ∈ V, DifferentiableAt ℝ w (Work.Beltrami.eC (y - x)) := by
    intro y hy
    exact (hwsm.differentiableOn (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hball y hy))
  have hu_sm : ContDiffOn ℝ ∞ (fun y : E 1 => w (Work.Beltrami.eC (y - x))) V := by
    have h1 : ContDiffOn ℝ ∞ (fun y : E 1 => Work.Beltrami.eC (y - x)) V := by
      have h2 : ContDiff ℝ ∞ (fun y : E 1 => (Work.Beltrami.eC : E 1 →L[ℝ] ℂ) y
          - Work.Beltrami.eC x) := by fun_prop
      exact h2.contDiffOn
    exact hwsm.comp h1 (fun y hy => hball y hy)
  have hu_hol : ∀ y ∈ V, ∀ v : E 1,
      fderiv ℝ (fun y : E 1 => w (Work.Beltrami.eC (y - x))) y (J y v)
        = Complex.I * fderiv ℝ (fun y : E 1 => w (Work.Beltrami.eC (y - x))) y v := by
    intro y hy v
    exact Work.Beltrami.isJHolAt_comp Work.Beltrami.eC x y (hdiff y hy)
      (fun u => hwhol _ (hball y hy) u) v
  have hu_ne : ∀ y ∈ V, fderiv ℝ (fun y : E 1 => w (Work.Beltrami.eC (y - x))) y ≠ 0 := by
    intro y hy
    exact Work.Beltrami.fderiv_ne_zero_comp Work.Beltrami.eC x y (hdiff y hy) (hwne _ (hball y hy))
  exact ⟨V, hVopen, hxV, hVU, (fun y => w (Work.Beltrami.eC (y - x))), hu_sm, hu_hol, hu_ne⟩

/-- From a `J`-holomorphic function with nowhere vanishing differential on a neighbourhood of `0`,
the `∂̄`-equation for the standard coordinate functions is solvable in the sense of
`Submission.DbarSolvable`.  The correction is `v = z₀ - u`: since both `z₀` and `u` are
`J`-holomorphic up to the perturbation term, `∂̄_J v = ∂̄_J z₀`, and the differential of the
corrected coordinate `u` is bijective by `Work.Beltrami.bijective_of_ne_zero` (a non-zero
`J`-complex-linear map `ℝ² → ℂ` is bijective). -/
theorem dbarSolvable_of_jHol {U V : Set (E 1)} (hVopen : IsOpen V) (hVU : V ⊆ U)
    (h0V : (0 : E 1) ∈ V) {J : E 1 → E 1 →L[ℝ] E 1} (hJ : IsAlmostComplexOn J U)
    {T : E 1 ≃L[ℝ] F 1} {u : E 1 → ℂ}
    (hu_sm : ContDiffOn ℝ ∞ u V)
    (hu_hol : ∀ y ∈ V, ∀ v : E 1, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (hu_ne : ∀ y ∈ V, fderiv ℝ u y ≠ 0) :
    DbarSolvable J U 0 T := by
  refine ⟨V, hVopen, h0V, hVU, (fun j y => zcoord T j y - u y), ?_, ?_, ?_⟩
  · intro j
    exact (contDiff_zcoord T j).contDiffOn.sub hu_sm
  · intro j y hy
    have hz : DifferentiableAt ℝ (zcoord T j) y :=
      ((contDiff_zcoord T j).differentiable (by simp)).differentiableAt
    have hu : DifferentiableAt ℝ u y :=
      ((hu_sm.contDiffAt (hVopen.mem_nhds hy)).differentiableAt (by simp))
    rw [dbar_sub J _ _ y hz hu, dbar_linearization T J (zcoord T j) y]
    have hzero : dbar (stdOf T) (zcoord T j) y = 0 := by
      rw [dbar_eq_zero_iff]
      intro w
      exact zcoord_hol T j y w
    have hug : dbar J u y = 0 := (dbar_eq_zero_iff J u y).mpr (hu_hol y hy)
    rw [hzero, hug, zero_add, sub_zero]
  · intro y hy
    have hfun : (fun y : E 1 => fun j : Fin 1 => zcoord T j y - (zcoord T j y - u y))
        = fun y : E 1 => fun _ : Fin 1 => u y := by
      funext y j
      ring
    rw [hfun]
    have hfd : fderiv ℝ (fun y : E 1 => fun _ : Fin 1 => u y) y
        = ContinuousLinearMap.pi (fun _ : Fin 1 => fderiv ℝ u y) := by
      rw [fderiv_pi]
      intro j
      exact ((hu_sm.contDiffAt (hVopen.mem_nhds hy)).differentiableAt (by simp))
    rw [hfd]
    have hbij := Work.Beltrami.bijective_of_ne_zero (hJ.2 y (hVU hy)) (hu_hol y hy) (hu_ne y hy)
    constructor
    · intro a b hab
      have h := congrFun hab 0
      simp only [ContinuousLinearMap.pi_apply] at h
      exact hbij.1 h
    · intro c
      obtain ⟨v, hv⟩ := hbij.2 (c 0)
      refine ⟨v, ?_⟩
      funext i
      simp only [ContinuousLinearMap.pi_apply]
      rw [Subsingleton.elim i 0]
      exact hv

/-- The local holomorphic input of the Beltrami argument, in the form produced by the
(unsorried) estimates `H`. -/
theorem localHolInput_of_cauchyEstimates' (H : Work.Beltrami.CauchyEstimates) :
    Work.Beltrami.LocalHolInput :=
  Work.Beltrami.localHolInput_of_cauchyEstimates H

/-- **The Newlander–Nirenberg analytic input in complex dimension one, unconditionally.**

For `n = 1` there is no integrability obstruction: every smooth field `J` with `J y ∘ J y = -1` on
an open `U ∋ 0` in `E 1 ≅ ℝ²` admits, near `0`, a `J`-holomorphic function with nowhere vanishing
differential — equivalently, the `∂̄_J`-equation is solvable in the sense of
`Submission.DbarSolvable J U 0 T`.  This is the case `n = 1` of the analytic core of this directory,
in the exact shape consumed by `Submission.nn_core_of_dbar`; together with that reduction it gives
the Newlander–Nirenberg conclusion in complex dimension one (no Nijenhuis hypothesis is needed: for
`n = 1` every almost complex structure is integrable).

Route.  Transport the problem to the plane by `T : E 1 ≃L[ℝ] F 1` composed with evaluation at `0`
of `F 1 = EuclideanSpace ℂ (Fin 1) ≅ ℂ`, so that the transported structure `J'` is smooth near
`0` with `J' 0` = multiplication by `i`; write `A = J' - i`, so `A 0 = 0`.  On a small disc write
the unknown as `w = z + v`; the equation `∂̄_{J'} w = 0` becomes the fixed point equation

  `v = T₀(χ · (g - L_A v))`,   `g = (i/2)·dz ∘ A`,   `L_A v = (i/2)·dv ∘ A`,

where `T₀` is the Cauchy transform on the disc
(`Work.CR.Flat.Cauchy.exists_dbarC_solution_disc`: `∂̄ T₀ f = f` and
`‖T₀ f‖_{C^{1,α}} ≤ C ‖f‖_{C^{0,α}}`, with `contDiff_cauchyTransform` for smoothness) and `χ` is a
smooth cutoff equal to `1` near `0` and supported in the disc.  Since `A 0 = 0`, both `g` and `A`
are small in `C^{0,α}` on a small disc, so `T₀ ∘ L_A` is a contraction of norm `O(sup|A|) < 1`
there; the Picard sequence is smooth at every step and converges in `C^{k,α}` for every `k` (using
the `C^{k,α}` estimates `exists_dbarC_solution_disc_Ck`, whose contraction constant is uniform in
`k`), so the limit `v` is `C^∞`.  Finally `∂̄_{J'} w = 0`, `dw = 1 + dv ≠ 0` when `sup|dv| < 1`, and
the composite `w ∘ e` is the required `J`-holomorphic function on a neighbourhood of `0` in
`E 1`. -/
theorem dbarSolvable_one {U : Set (E 1)} (hU : IsOpen U) {J : E 1 → E 1 →L[ℝ] E 1}
    (hJ : IsAlmostComplexOn J U) (h0 : (0 : E 1) ∈ U) {T : E 1 ≃L[ℝ] F 1}
    (hT : ∀ v : E 1, T (J 0 v) = Complex.I • T v) : DbarSolvable J U 0 T := by
  have _ := hT
  obtain ⟨V, hVopen, h0V, hVU, u, hu_sm, hu_hol, hu_ne⟩ :=
    exists_jHol_at_of_cauchy cauchyEstimatesNN hU hJ h0
  exact dbarSolvable_of_jHol hVopen hVU h0V hJ hu_sm hu_hol hu_ne

end

end Work.NN.Core
