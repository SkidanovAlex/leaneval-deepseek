import Mathlib
import Submission.Work.Escape.exists_differentiableOn_ball_clog

/-!
# Maximum modulus for a periodic holomorphic function on a half-plane

If `D` is holomorphic on the half-plane `{w | w.im ≤ -y}`, `1`-periodic, has a limit at `-i∞`,
and satisfies `‖D w‖ < δ` on the boundary line `{w | w.im = -y}`, then `‖D w‖ < δ` on the whole
half-plane.

The proof reflects to the upper half-plane, pushes the function to the punctured unit disc by the
`q`-parameter `q = exp (2 π i w)` and applies the maximum modulus principle there.  The point
`-i∞` becomes the *interior* point `q = 0` of the disc, which is what makes the strict inequality
work.
-/

open Filter
open scoped Topology

namespace Work.Pert

/-- `Tendsto` implies `BoundedAtFilter`. -/
private lemma boundedAtFilter_of_tendsto {l : Filter ℂ} {f : ℂ → ℂ} {L : ℂ}
    (h : Filter.Tendsto f l (𝓝 L)) : l.BoundedAtFilter f := by
  rw [Filter.BoundedAtFilter, Asymptotics.isBigO_iff]
  refine ⟨‖L‖ + 1, ?_⟩
  have h1 : ∀ᶠ x in l, ‖f x - L‖ ≤ 1 := by
    have hb := h (Metric.ball_mem_nhds L (by norm_num : (0:ℝ) < 1))
    filter_upwards [hb] with x hx
    simp only [Set.mem_preimage] at hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    exact le_of_lt hx
  filter_upwards [h1] with x hx
  simp only [Pi.one_apply, norm_one, mul_one]
  calc ‖f x‖ = ‖(f x - L) + L‖ := by ring_nf
    _ ≤ ‖f x - L‖ + ‖L‖ := norm_add_le _ _
    _ ≤ 1 + ‖L‖ := by linarith
    _ = ‖L‖ + 1 := by ring

private lemma eventually_im_ge (Y : ℝ) :
    {z : ℂ | Y ≤ z.im} ∈ Filter.comap Complex.im Filter.atTop := by
  rw [Filter.mem_comap]
  exact ⟨Set.Ici Y, Filter.Ici_mem_atTop Y, fun x hx => hx⟩

private lemma eventually_im_gt (Y : ℝ) :
    {z : ℂ | Y < z.im} ∈ Filter.comap Complex.im Filter.atTop := by
  rw [Filter.mem_comap]
  exact ⟨Set.Ioi Y, Filter.Ioi_mem_atTop Y, fun x hx => hx⟩

/-- **Maximum modulus principle for a periodic holomorphic function on an upper half-plane.**
If `φ` is `1`-periodic, holomorphic on `{w | Y ≤ w.im}` and has a limit at `+i∞`, and if
`‖φ‖ < δ` on the boundary line `{w | w.im = Y}`, then `‖φ w‖ < δ` for all `w` with `Y ≤ w.im`. -/
theorem norm_lt_of_periodic_upper (φ : ℂ → ℂ) {Y δ : ℝ} (_hδ : 0 < δ)
    (hper : ∀ w : ℂ, φ (w + 1) = φ w)
    (hdiff : DifferentiableOn ℂ φ {w : ℂ | Y ≤ w.im})
    (hend : ∃ L : ℂ, Filter.Tendsto φ (Filter.comap Complex.im Filter.atTop) (𝓝 L))
    (hline : ∀ w : ℂ, w.im = Y → ‖φ w‖ < δ) :
    ∀ w : ℂ, Y ≤ w.im → ‖φ w‖ < δ := by
  have hperC : Function.Periodic φ ((1:ℝ):ℂ) := by simpa using hper
  set r : ℝ := Real.exp (-2 * Real.pi * Y) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  have hrne : r ≠ 0 := ne_of_gt hrpos
  set F : ℂ → ℂ := Function.Periodic.cuspFunction (1:ℝ) φ with hFdef
  -- differentiability near `+i∞`
  have hhol : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ φ z := by
    refine (Filter.eventually_iff_exists_mem).mpr
      ⟨{z : ℂ | Y < z.im}, eventually_im_gt Y, ?_⟩
    intro z hz
    exact hdiff.differentiableAt (Filter.mem_of_superset
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      (fun w hw => by simpa using le_of_lt hw))
  have hbd : (Filter.comap Complex.im Filter.atTop).BoundedAtFilter φ := by
    obtain ⟨L, hL⟩ := hend
    exact boundedAtFilter_of_tendsto hL
  -- `F` is complex differentiable on the closed disc of radius `r`
  have hFdiff : DifferentiableOn ℂ F (Metric.closedBall (0:ℂ) r) := by
    intro q hq
    rw [Metric.mem_closedBall, dist_zero_right] at hq
    by_cases hq0 : q = 0
    · subst hq0
      exact (Function.Periodic.differentiableAt_cuspFunction_zero (h := (1:ℝ)) (f := φ)
        one_pos hperC hhol hbd).differentiableWithinAt
    · -- local holomorphic logarithm on a small ball around `q`, avoiding `0`
      set ε : ℝ := ‖q‖ / 2 with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      have hzero_not : (0:ℂ) ∉ Metric.ball q ε := by
        intro h0
        rw [Metric.mem_ball, dist_eq_norm] at h0
        rw [zero_sub, norm_neg] at h0
        rw [hεdef] at h0
        linarith [norm_nonneg q]
      obtain ⟨L, hLdiff, hLexp, _hLre⟩ :=
        _root_.Work.Escape.exists_differentiableOn_ball_clog
          (g := fun z : ℂ => z) (c := q) (r := ε)
          differentiable_id.differentiableOn
          (fun z hz => by
            intro hz0
            exact hzero_not (hz0 ▸ hz))
      set M : ℂ → ℂ := fun z => L z / (2 * Real.pi * Complex.I) with hMdef
      have hMdiff : DifferentiableOn ℂ M (Metric.ball q ε) := hLdiff.div_const _
      have hqmem : q ∈ Metric.ball q ε := Metric.mem_ball_self hεpos
      have hMat : DifferentiableAt ℂ M q :=
        hMdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hqmem)
      -- `qParam 1` inverts `M`
      have hi : ∀ z ∈ Metric.ball q ε, Function.Periodic.qParam (1:ℝ) (M z) = z := by
        intro z hz
        have h2 : (2:ℂ) * (Real.pi:ℂ) * Complex.I * (L z / (2 * (Real.pi:ℂ) * Complex.I)) = L z := by
          field_simp
        rw [Function.Periodic.qParam]
        rw [show (2:ℂ) * (Real.pi:ℂ) * Complex.I * (L z / (2 * (Real.pi:ℂ) * Complex.I))
              / (((1:ℝ)):ℂ) = L z by
          rw [Complex.ofReal_one, div_one]; exact h2]
        exact hLexp z hz
      -- `M` maps the part of the closed disc inside the ball into the half-plane
      have him : ∀ z ∈ Metric.ball q ε, ‖z‖ ≤ r → Y ≤ (M z).im := by
        intro z hz hzr
        have hqz := hi z hz
        have hnorm := Function.Periodic.norm_qParam (h := (1:ℝ)) (z := M z)
        rw [hqz] at hnorm
        have hexp : Real.exp (-2 * Real.pi * (M z).im) = ‖z‖ := by
          rw [hnorm]; simp
        have hle : -2 * Real.pi * (M z).im ≤ -2 * Real.pi * Y :=
          Real.exp_le_exp.mp (by rw [hexp, ← hrdef]; exact hzr)
        nlinarith [Real.pi_pos, hle]
      -- and `F = φ ∘ M` there
      have hiii : ∀ z ∈ Metric.ball q ε, z ≠ 0 → F z = φ (M z) := by
        intro z hz hz0
        have hcusp := Function.Periodic.cuspFunction_eq_of_nonzero (1:ℝ) φ hz0
        obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := (1:ℝ)) one_ne_zero (M z)
        have hqz := hi z hz
        rw [hqz] at hm
        simp only [Complex.ofReal_one, mul_one] at hm
        rw [hFdef, hcusp, hm]
        have hperz := (hperC.int_mul m) (M z)
        simp only [Complex.ofReal_one, mul_one] at hperz
        exact hperz
      set s : Set ℂ := Metric.closedBall (0:ℂ) r ∩ Metric.ball q ε with hsdef
      have hqmem_s : q ∈ s := ⟨by rwa [Metric.mem_closedBall, dist_zero_right], hqmem⟩
      have hMs : Set.MapsTo M s {w : ℂ | Y ≤ w.im} := by
        intro z hz
        rw [hsdef, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right] at hz
        exact him z hz.2 hz.1
      have hφM : DifferentiableWithinAt ℂ φ {w : ℂ | Y ≤ w.im} (M q) :=
        hdiff (M q) (hMs hqmem_s)
      have hMsat : DifferentiableWithinAt ℂ M s q := hMat.differentiableWithinAt
      have hcomp : DifferentiableWithinAt ℂ (φ ∘ M) s q := hφM.comp q hMsat hMs
      have heq : F =ᶠ[𝓝[s] q] (φ ∘ M) := by
        refine eventually_nhdsWithin_of_forall ?_
        intro z hz
        simp only [Function.comp_apply]
        exact hiii z hz.2 (by intro hz0; exact hzero_not (hz0 ▸ hz.2))
      have hval : F q = (φ ∘ M) q := by
        simp only [Function.comp_apply]
        exact hiii q hqmem (by intro h; exact hzero_not (h ▸ hqmem))
      have hres : DifferentiableWithinAt ℂ F s q := hcomp.congr_of_eventuallyEq heq hval
      have hsets : s =ᶠ[𝓝 q] Metric.closedBall (0:ℂ) r := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hqmem] with z hz
        simp only [hsdef, Set.mem_inter_iff, hz, and_true]
      exact (differentiableWithinAt_congr_set hsets).mp hres
  have hFcont : ContinuousOn F (Metric.closedBall (0:ℂ) r) := hFdiff.continuousOn
  have hdC : DiffContOnCl ℂ F (Metric.ball (0:ℂ) r) := by
    refine ⟨hFdiff.mono Metric.ball_subset_closedBall, ?_⟩
    rw [closure_ball (0:ℂ) hrne]
    exact hFcont
  -- the strict bound on the boundary circle
  have hsphere : ∀ z ∈ Metric.sphere (0:ℂ) r, ‖F z‖ < δ := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hrpos]
    have hcusp := Function.Periodic.cuspFunction_eq_of_nonzero (1:ℝ) φ hz0
    have himz : (Function.Periodic.invQParam (1:ℝ) z).im = Y := by
      rw [Function.Periodic.im_invQParam]
      rw [hz, hrdef, Real.log_exp]
      field_simp
    rw [hFdef, hcusp]
    exact hline _ himz
  -- maximum on the boundary circle
  have hne_sphere : (Metric.sphere (0:ℂ) r).Nonempty := NormedSpace.sphere_nonempty.mpr hrpos.le
  have hcont_sphere : ContinuousOn (fun z => ‖F z‖) (Metric.sphere (0:ℂ) r) :=
    (hFcont.mono Metric.sphere_subset_closedBall).norm
  obtain ⟨z₀, hz₀mem, hz₀max⟩ :=
    (isCompact_sphere (0:ℂ) r).exists_isMaxOn hne_sphere hcont_sphere
  have hz₀lt : ‖F z₀‖ < δ := hsphere z₀ hz₀mem
  intro w hw
  have hqmem2 : Function.Periodic.qParam (1:ℝ) w ∈ closure (Metric.ball (0:ℂ) r) := by
    rw [closure_ball (0:ℂ) hrne, Metric.mem_closedBall, dist_zero_right,
      Function.Periodic.norm_qParam, hrdef, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hw])
  have hfinal : ‖F (Function.Periodic.qParam (1:ℝ) w)‖ ≤ ‖F z₀‖ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hdC
      (fun z hz => by
        rw [frontier_ball (0:ℂ) hrne] at hz
        exact hz₀max hz)
      hqmem2
  have hw' := Function.Periodic.eq_cuspFunction (h := (1:ℝ)) (f := φ) one_ne_zero hperC w
  rw [hFdef] at hfinal hz₀lt
  rw [hw'] at hfinal
  linarith

/-- **The Hausdorff-dimension estimate (Shishikura, Lemma A.2).**  A `1`-periodic holomorphic
function on the lower half-plane `{w | w.im ≤ -y}` with a limit at `-i∞` whose modulus is `< δ`
on the boundary line is `< δ` on the whole half-plane. -/
theorem norm_le_periodic_lowerHalfplane2 (D : ℂ → ℂ) {y δ : ℝ} (hδ : 0 < δ)
    (hper : ∀ w : ℂ, D (w + 1) = D w)
    (hdiff : DifferentiableOn ℂ D {w : ℂ | w.im ≤ -y})
    (hend : ∃ L : ℂ, Filter.Tendsto D (Filter.comap Complex.im Filter.atBot) (nhds L))
    (hline : ∀ w : ℂ, w.im = -y → ‖D w‖ < δ) :
    ∀ w : ℂ, w.im ≤ -y → ‖D w‖ < δ := by
  -- reflect: `E w = D (-w)` is a periodic function on the upper half-plane
  have hperE : ∀ w : ℂ, (fun z => D (-z)) (w + 1) = (fun z => D (-z)) w := by
    intro w
    show D (-(w + 1)) = D (-w)
    have h := hper (-w - 1)
    rw [show -w - 1 + 1 = -w by ring] at h
    rw [show -(w+1) = -w - 1 by ring]
    exact h.symm
  have hdiffE : DifferentiableOn ℂ (fun z => D (-z)) {w : ℂ | y ≤ w.im} := by
    have hMaps : Set.MapsTo (fun w : ℂ => -w) {w : ℂ | y ≤ w.im} {w : ℂ | w.im ≤ -y} := by
      intro w hw
      have hw' : y ≤ w.im := by simpa using hw
      show (-w).im ≤ -y
      rw [Complex.neg_im]
      linarith
    have hcomp := hdiff.comp (s := {w : ℂ | y ≤ w.im}) (t := {w : ℂ | w.im ≤ -y})
      differentiable_neg.differentiableOn hMaps
    simpa only [Function.comp_def, neg_neg] using hcomp
  have hendE : ∃ L : ℂ,
      Filter.Tendsto (fun z => D (-z)) (Filter.comap Complex.im Filter.atTop) (𝓝 L) := by
    obtain ⟨L, hL⟩ := hend
    refine ⟨L, ?_⟩
    have hneg : Filter.Tendsto (fun w : ℂ => -w)
        (Filter.comap Complex.im Filter.atTop) (Filter.comap Complex.im Filter.atBot) := by
      rw [Filter.tendsto_comap_iff]
      exact tendsto_neg_atTop_atBot.comp tendsto_comap
    exact hL.comp hneg
  have hlineE : ∀ w : ℂ, w.im = y → ‖(fun z => D (-z)) w‖ < δ := by
    intro w hw
    simp only
    exact hline (-w) (by rw [Complex.neg_im, hw])
  have hupper := norm_lt_of_periodic_upper (fun z => D (-z)) hδ hperE hdiffE hendE hlineE
  intro w hw
  have h2 := hupper (-w) (by rw [Complex.neg_im]; linarith)
  simpa only [neg_neg] using h2

end Work.Pert
