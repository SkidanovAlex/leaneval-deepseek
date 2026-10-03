import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Horn.gholo

/-!
# `Work.Horn.endSurj` — surjectivity of a map that is asymptotically the identity at an end

Let `E : ℂ → ℂ` be holomorphic on the half plane `{r < Im w}` and suppose `E w - w → 0` as
`Im w → +∞` (Shishikura's normalisation `(4.1.5)` for the lifted horn map, the field
`ParabData.E_upper`).  Then the image of `E` contains a half plane: for `y` high enough the map
`F w = w + (y - E w)` maps a ball around `y` into itself and is a contraction there, so it has a
fixed point `w` with `E w = y`.

Consequences (`ParabData.Phi_image_ends`): the image of the parabolic basin under the Fatou
coordinate `Φ` contains the far upper *and* the far lower half plane.
-/

namespace Work.Horn

noncomputable section

open _root_.MandelDim Filter Topology Metric Set
open scoped Topology

/-! ## The general contraction lemma -/

/-- **A map which is asymptotically the identity at `+i∞` is onto a half plane.**

If `E` is holomorphic on `{r < Im w}` and `E w - w → 0` as `Im w → +∞`, then there is `R` with
`{y | R < Im y} ⊆ E '' {w | r < Im w}`. -/
theorem exists_preimage_of_im_gt {E : ℂ → ℂ} {r : ℝ}
    (hhol : DifferentiableOn ℂ E {w : ℂ | r < w.im})
    (hlim : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < w.im → ‖E w - w‖ < ε) :
    ∃ R : ℝ, ∀ y : ℂ, R < y.im → ∃ w : ℂ, r < w.im ∧ E w = y := by
  obtain ⟨R₀, hR₀⟩ := hlim (1 / 8) (by norm_num)
  refine ⟨max R₀ r + 3, fun y hy => ?_⟩
  have hy0 : R₀ + 3 < y.im := by
    have : R₀ ≤ max R₀ r := le_max_left _ _; linarith
  have hyr : r + 3 < y.im := by
    have : r ≤ max R₀ r := le_max_right _ _; linarith
  -- the ball `closedBall y (1/2)` lands in the domain of `E`, with `Im` bounded below
  have hBim : ∀ w ∈ closedBall y (1 / 2), R₀ < w.im ∧ r < w.im := by
    intro w hw
    have h1 : ‖w - y‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hw
    have h2 : |w.im - y.im| ≤ 1 / 2 := by
      have h3 := Complex.abs_im_le_norm (w - y)
      have h4 : (w - y).im = w.im - y.im := by simp
      rw [← h4]; linarith
    have h5 := (abs_le.mp h2).1
    exact ⟨by linarith [hy0], by linarith [hyr]⟩
  -- points of `closedBall y 1` are also in the domain, and `‖E - id‖ < 1/8` there
  have hBim1 : ∀ z ∈ closedBall y 1, R₀ < z.im ∧ r < z.im := by
    intro z hz
    have h1 : ‖z - y‖ ≤ 1 := by simpa [dist_eq_norm] using hz
    have h2 : |z.im - y.im| ≤ 1 := by
      have h3 := Complex.abs_im_le_norm (z - y)
      have h4 : (z - y).im = z.im - y.im := by simp
      rw [← h4]; linarith
    have h5 := (abs_le.mp h2).1
    exact ⟨by linarith [hy0], by linarith [hyr]⟩
  set F : ℂ → ℂ := fun w => y - (E w - w) with hFdef
  -- `F` maps the ball into itself
  have hFmap : MapsTo F (closedBall y (1 / 2)) (closedBall y (1 / 2)) := by
    intro w hw
    have h1 : ‖E w - w‖ < 1 / 8 := hR₀ w (hBim w hw).1
    have h2 : F w - y = -(E w - w) := by simp only [hFdef]; ring
    rw [mem_closedBall, dist_eq_norm, h2, norm_neg]
    linarith [h1.le]
  -- derivative estimate on the ball (Cauchy)
  have hGderiv : ∀ w ∈ closedBall y (1 / 2), ‖deriv (fun z : ℂ => E z - z) w‖ ≤ 1 / 4 := by
    intro w hw
    have hsub : closedBall w (1 / 2) ⊆ {z : ℂ | r < z.im} := by
      intro z hz
      have h1 : ‖z - w‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
      have h2 : ‖w - y‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hw
      have h3 : ‖z - y‖ ≤ 1 := by
        calc ‖z - y‖ = ‖(z - w) + (w - y)‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w - y‖ := norm_add_le _ _
          _ ≤ 1 / 2 + 1 / 2 := by linarith
          _ = 1 := by norm_num
      exact (hBim1 z (by simpa [mem_closedBall, dist_eq_norm] using h3)).2
    have hd : DiffContOnCl ℂ (fun z : ℂ => E z - z) (ball w (1 / 2)) := by
      refine ⟨?_, ?_⟩
      · exact (hhol.mono (fun z hz => hsub (ball_subset_closedBall hz))).sub differentiableOn_id
      · rw [closure_ball w (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        exact ((hhol.mono hsub).continuousOn).sub continuousOn_id
    have hs : ∀ z ∈ sphere w (1 / 2), ‖(fun z : ℂ => E z - z) z‖ ≤ 1 / 8 := by
      intro z hz
      have h1 : ‖z - w‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
      have h2 : ‖w - y‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hw
      have h3 : ‖z - y‖ ≤ 1 := by
        calc ‖z - y‖ = ‖(z - w) + (w - y)‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w - y‖ := norm_add_le _ _
          _ ≤ 1 / 2 + 1 / 2 := by rw [h1]; linarith
          _ = 1 := by norm_num
      exact (hR₀ z (hBim1 z (by simpa [mem_closedBall, dist_eq_norm] using h3)).1).le
    have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun z : ℂ => E z - z)
      (c := w) (R := 1 / 2) (C := 1 / 8) (by norm_num) hd hs
    rw [show (1 / 8 : ℝ) / (1 / 2) = 1 / 4 by norm_num] at hmain
    exact hmain
  -- `F` is a contraction on the ball
  have hFcontr : ∀ u ∈ closedBall y (1 / 2), ∀ v ∈ closedBall y (1 / 2),
      ‖F u - F v‖ ≤ (1 / 4) * ‖u - v‖ := by
    intro u hu v hv
    have hconv : Convex ℝ (closedBall y (1 / 2)) := convex_closedBall y (1 / 2)
    have hdiff : ∀ z ∈ closedBall y (1 / 2),
        DifferentiableAt ℂ (fun z : ℂ => E z - z) z := by
      intro z hz
      exact (hhol.differentiableAt
        (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds (hBim z hz).2)).sub
        differentiableAt_id
    have h1 : F u - F v = (fun z : ℂ => E z - z) v - (fun z : ℂ => E z - z) u := by
      simp only [hFdef]; ring
    rw [h1]
    have h3 := hconv.norm_image_sub_le_of_norm_deriv_le hdiff (fun z hz => hGderiv z hz) hu hv
    calc ‖(fun z : ℂ => E z - z) v - (fun z : ℂ => E z - z) u‖ ≤ (1 / 4) * ‖v - u‖ := h3
      _ = (1 / 4) * ‖u - v‖ := by rw [norm_sub_rev]
  -- Banach fixed point on the complete ball
  let U : Set ℂ := closedBall y (1 / 2)
  haveI : IsClosed U := (show IsClosed (closedBall y (1 / 2)) from isClosed_closedBall)
  haveI : Nonempty U := ⟨⟨y, by rw [mem_closedBall, dist_self]; norm_num⟩⟩
  set F' : U → U := fun u => ⟨F u, hFmap u.2⟩
  have hcontr : ContractingWith (1 / 4 : NNReal) F' := by
    refine ⟨by norm_num, fun u v => ?_⟩
    have h := hFcontr u u.2 v v.2
    have key : edist (F (u : ℂ)) (F (v : ℂ)) ≤
        ENNReal.ofReal (1 / 4 : ℝ) * edist (u : ℂ) (v : ℂ) := by
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      calc ENNReal.ofReal ‖F (u : ℂ) - F (v : ℂ)‖
            ≤ ENNReal.ofReal ((1 / 4 : ℝ) * ‖(u : ℂ) - (v : ℂ)‖) :=
            ENNReal.ofReal_le_ofReal h
        _ = ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal ‖(u : ℂ) - (v : ℂ)‖ :=
            ENNReal.ofReal_mul (by norm_num)
    simpa [Subtype.edist_eq, ENNReal.ofReal_coe_nnreal] using key
  obtain ⟨u, hu, -, -⟩ := hcontr.exists_fixedPoint
    (⟨y, by rw [mem_closedBall, dist_self]; norm_num⟩ : U)
    (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  have hu_fix : F (u : ℂ) = (u : ℂ) := congrArg Subtype.val hu
  refine ⟨(u : ℂ), (hBim u u.2).2, ?_⟩
  have h2 : y - (E (u : ℂ) - (u : ℂ)) = (u : ℂ) := hu_fix
  have h4 : y = (u : ℂ) + (E (u : ℂ) - (u : ℂ)) := (sub_eq_iff_eq_add).mp h2
  have h5 : y = E (u : ℂ) := by rw [h4]; ring
  exact h5.symm

/-- **Lower end version.**  If `E` is holomorphic on `{Im w < -r}` and `E w - w → cl` as
`Im w → -∞`, then the image of `E` contains a far lower half plane. -/
theorem exists_preimage_of_im_lt {E : ℂ → ℂ} {r : ℝ} {cl : ℂ}
    (hhol : DifferentiableOn ℂ E {w : ℂ | w.im < -r})
    (hlim : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < -R → ‖E w - w - cl‖ < ε) :
    ∃ R : ℝ, ∀ y : ℂ, y.im < R → ∃ w : ℂ, w.im < -r ∧ E w = y := by
  have hFhol : DifferentiableOn ℂ (fun w : ℂ => cl - E (-w)) {w : ℂ | r < w.im} := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => -w) {w : ℂ | r < w.im} :=
      differentiableOn_id.neg
    refine (differentiableOn_const cl).sub (hhol.comp h1 ?_)
    intro w hw
    simpa using hw
  have hFlim : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < w.im → ‖(cl - E (-w)) - w‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hlim ε hε
    refine ⟨R, fun w hw => ?_⟩
    have hneg : (-w).im < -R := by simpa using hw
    have hthis := hR (-w) hneg
    have hEq : (cl - E (-w)) - w = -(E (-w) - (-w) - cl) := by ring
    rw [hEq, norm_neg]
    exact hthis
  obtain ⟨R, hR⟩ := exists_preimage_of_im_gt hFhol hFlim
  refine ⟨cl.im - R, fun y hy => ?_⟩
  have hy' : R < (cl - y).im := by
    simp only [Complex.sub_im]
    linarith
  obtain ⟨w, hw, hwy⟩ := hR (cl - y) hy'
  refine ⟨-w, by simpa using hw, ?_⟩
  have h3 : E (-w) = y := by linear_combination -hwy
  simpa using h3

end

end Work.Horn
