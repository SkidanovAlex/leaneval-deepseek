import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouL1.taylorTwoIntegral

/-!
# The Taylor remainder of a parabolic germ at the origin

`Work.Pert.parab_germ_taylor_near0`: for a parabolic germ `f₀` (`f₀ z = z + z² + O(z³)`) on an open
set `D₀ ∋ 0` and every `ε > 0` there are `ρ, B` with `0 < ρ`, `ρ ≤ 1`, `0 ≤ B`,
`closedBall 0 ρ ⊆ D₀`, `‖f₀ z - z - z²‖ ≤ B ‖z‖³` for `‖z‖ ≤ ρ`, and the *scaled* smallness
`B ρ ≤ ε`.

The analytic input is the quantitative second-order Taylor estimate
`norm_sub_taylor_two_le`: a function holomorphic on `ball 0 R` is `O(‖z‖³)`-close to its
second-order Taylor polynomial at `0` on `‖z‖ ≤ R/2`.  It is obtained from
`Work.FatouL1.taylorTwoIntegral` (second-order Taylor with the integral form of the remainder)
by applying it to `G z = F z - F 0 - F'(0) z - (F''(0)/2) z²`, whose second derivative vanishes
at `0` and is Lipschitz at `0`.
-/

namespace Work.Pert

/-- The derivative of a quadratic polynomial `a + b w + (d/2) w²`. -/
private lemma quad_deriv (a b d : ℂ) :
    deriv (fun w : ℂ => a + b * w + (d / 2) * w ^ 2) = fun w => b + d * w := by
  funext w
  have hA : HasDerivAt (fun w : ℂ => a + b * w) b w := by
    have h := (hasDerivAt_id w).const_mul b
    simpa using h.const_add a
  have hB : HasDerivAt (fun w : ℂ => (d / 2) * w ^ 2) ((d / 2) * (2 * w)) w := by
    have h := (hasDerivAt_pow 2 w).const_mul (d / 2)
    simpa using h
  have h := hA.add hB
  convert h.deriv using 1
  ring

/-- The second derivative of a quadratic polynomial `a + b w + (d/2) w²` is the constant `d`. -/
private lemma quad_iteratedDeriv_two (a b d : ℂ) :
    iteratedDeriv 2 (fun w : ℂ => a + b * w + (d / 2) * w ^ 2) = fun _ => d := by
  funext u
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, quad_deriv]
  have h2 : HasDerivAt (fun w : ℂ => b + d * w) d u := by
    have h := (hasDerivAt_id u).const_mul d
    simpa using h.const_add b
  simpa using h2.deriv

/-- Local first-order Taylor estimate at a point, in ε-δ form: if `g` is complex differentiable at
`x`, then for every `c > 0` there is `δ > 0` such that `‖g y - g x - (y - x) g'(x)‖ ≤ c ‖y - x‖`
for `‖y - x‖ < δ`. -/
private lemma norm_sub_le_of_differentiableAt {g : ℂ → ℂ} {x : ℂ} {c : ℝ} (hc : 0 < c)
    (hg : DifferentiableAt ℂ g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, ‖y - x‖ < δ →
      ‖g y - g x - (y - x) * deriv g x‖ ≤ c * ‖y - x‖ := by
  have h : (fun y => g y - g x - (y - x) • deriv g x) =o[nhds x] (fun y => y - x) :=
    hg.hasDerivAt.isLittleO
  rw [Asymptotics.isLittleO_iff] at h
  have h' := h hc
  rw [Metric.eventually_nhds_iff] at h'
  obtain ⟨δ, hδ, hδ'⟩ := h'
  exact ⟨δ, hδ, fun y hy => by
    have hy' : dist y x < δ := by simpa [dist_eq_norm] using hy
    simpa [smul_eq_mul] using hδ' hy'⟩

/-- Quantitative second-order Taylor estimate for a function holomorphic on a disc: if `F` is
complex differentiable on the open ball `ball 0 R` (`R > 0`), then on `‖z‖ ≤ R/2` the function `F`
is `O(‖z‖³)`-close to its second-order Taylor polynomial at `0`, with a constant `C ≥ 0`
independent of `z`.

Proof: set `G z = F z - F 0 - F'(0) z - (F''(0)/2) z²`.  Then `G` is holomorphic on the open convex
`ball 0 R`, `G 0 = 0`, `G' 0 = 0`, and `G'' = F'' - F''(0)`, so `G'' 0 = 0`.  The second-order
Taylor formula with the integral form of the remainder (`Work.FatouL1.taylorTwoIntegral`) applied
on `ball 0 R` gives `G z = z² ∫₀¹ (1-t) G''(t z) dt`.  The Lipschitz bound `‖G'' u‖ ≤ C ‖u‖` on
`‖u‖ ≤ R/2` (local Lipschitz at `0` from differentiability of `G''` at `0`, plus boundedness of
`G''` on the compact `closedBall 0 (R/2)`) then yields `‖G z‖ ≤ C ‖z‖³`. -/
private lemma norm_sub_taylor_two_le {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ R / 2 →
      ‖F z - F 0 - deriv F 0 * z - (iteratedDeriv 2 F 0 / 2) * z ^ 2‖ ≤ C * ‖z‖ ^ 3 := by
  set c : ℂ := iteratedDeriv 2 F 0 with hcdef
  set G : ℂ → ℂ := F - fun w => F 0 + deriv F 0 * w + (c / 2) * w ^ 2 with hGdef
  have hG_diff : DifferentiableOn ℂ G (Metric.ball 0 R) := by
    rw [hGdef]; exact hF.sub (by fun_prop)
  have hdF0 : DifferentiableAt ℂ F 0 :=
    hF.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  have hG0 : G 0 = 0 := by rw [hGdef]; simp
  have hG1 : deriv G 0 = 0 := by
    rw [hGdef, deriv_sub hdF0 (by fun_prop), quad_deriv]
    ring
  have hG2 : ∀ u ∈ Metric.ball 0 R, iteratedDeriv 2 G u = iteratedDeriv 2 F u - c := by
    intro u hu
    rw [hGdef]
    have hctF : ContDiffAt ℂ (2:ℕ) F u := (hF.analyticAt (Metric.isOpen_ball.mem_nhds hu)).contDiffAt
    have hctP : ContDiffAt ℂ (2:ℕ)
        (fun w : ℂ => F 0 + deriv F 0 * w + (c / 2) * w ^ 2) u := by fun_prop
    rw [iteratedDeriv_sub hctF hctP, quad_iteratedDeriv_two]
  have hG2_0 : iteratedDeriv 2 G 0 = 0 := by
    rw [hG2 0 (Metric.mem_ball_self hR), hcdef]; ring
  have hiter2 : iteratedDeriv 2 G = deriv (deriv G) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hG2_diffOn : DifferentiableOn ℂ (iteratedDeriv 2 G) (Metric.ball 0 R) := by
    rw [hiter2]
    exact (hG_diff.deriv Metric.isOpen_ball).deriv Metric.isOpen_ball
  have hG2_diffAt0 : DifferentiableAt ℂ (iteratedDeriv 2 G) 0 :=
    hG2_diffOn.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  obtain ⟨δ, hδpos, hδ⟩ := norm_sub_le_of_differentiableAt one_pos hG2_diffAt0
  have hCl : ∀ y : ℂ, ‖y‖ < δ →
      ‖iteratedDeriv 2 G y‖ ≤ (‖deriv (iteratedDeriv 2 G) 0‖ + 1) * ‖y‖ := by
    intro y hy
    have h := hδ y (by simpa using hy)
    rw [hG2_0, sub_zero, sub_zero, one_mul] at h
    rw [show iteratedDeriv 2 G y = (iteratedDeriv 2 G y - y * deriv (iteratedDeriv 2 G) 0)
      + y * deriv (iteratedDeriv 2 G) 0 from by ring]
    calc ‖(iteratedDeriv 2 G y - y * deriv (iteratedDeriv 2 G) 0) + y * deriv (iteratedDeriv 2 G) 0‖
        ≤ ‖iteratedDeriv 2 G y - y * deriv (iteratedDeriv 2 G) 0‖ + ‖y * deriv (iteratedDeriv 2 G) 0‖ :=
          norm_add_le _ _
      _ ≤ ‖y‖ + ‖y‖ * ‖deriv (iteratedDeriv 2 G) 0‖ :=
          add_le_add h (le_of_eq (norm_mul y _))
      _ = (‖deriv (iteratedDeriv 2 G) 0‖ + 1) * ‖y‖ := by ring
  have hcontOn : ContinuousOn (iteratedDeriv 2 G) (Metric.closedBall 0 (R / 2)) :=
    hG2_diffOn.continuousOn.mono (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨K, hK⟩ := (isCompact_closedBall 0 (R / 2)).exists_bound_of_continuousOn hcontOn
  have hK0 : 0 ≤ K := by
    have h := hK 0 (Metric.mem_closedBall_self (by linarith))
    rw [hG2_0, norm_zero] at h
    exact h
  set Cm : ℝ := max (‖deriv (iteratedDeriv 2 G) 0‖ + 1) (K / δ) with hCmdef
  have hCm0 : 0 ≤ Cm := by
    rw [hCmdef]
    exact le_trans (by positivity) (le_max_left _ _)
  have hbound : ∀ u : ℂ, ‖u‖ ≤ R / 2 → ‖iteratedDeriv 2 G u‖ ≤ Cm * ‖u‖ := by
    intro u hu
    rw [hCmdef]
    rcases lt_or_ge ‖u‖ δ with hlt | hge
    · exact le_trans (hCl u hlt) (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))
    · have hKu : ‖iteratedDeriv 2 G u‖ ≤ K := hK u (by
        simpa [Metric.mem_closedBall, dist_zero_right] using hu)
      have hKδ : K ≤ K / δ * ‖u‖ := by
        have h1 : K / δ * δ ≤ K / δ * ‖u‖ := mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [div_mul_cancel₀ K (ne_of_gt hδpos)] at h1
      exact le_trans hKu (le_trans hKδ (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)))
  refine ⟨Cm, hCm0, ?_⟩
  intro z hz
  have hzlt : ‖z‖ < R := by linarith
  have hL : F z - F 0 - deriv F 0 * z - (c / 2) * z ^ 2 = G z := by
    rw [hGdef]; simp only [Pi.sub_apply]; ring
  have hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → (0:ℂ) + t • z ∈ Metric.ball 0 R := by
    intro t ht
    rw [zero_add, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < R := hzlt
  have htay := Work.FatouL1.taylorTwoIntegral (Φ := G) (z := 0) (v := z) (U := Metric.ball 0 R)
      Metric.isOpen_ball (convex_ball 0 R) hseg hG_diff
  have hGz : G z = z ^ 2 * ∫ t in (0:ℝ)..1, ((1 - t : ℝ) : ℂ) * iteratedDeriv 2 G (t • z) := by
    have h := htay
    rw [hG0, hG1] at h
    simpa [zero_add] using h
  have hA : ‖∫ t in (0:ℝ)..1, ((1 - t : ℝ) : ℂ) * iteratedDeriv 2 G (t • z)‖ ≤ Cm * ‖z‖ := by
    have key : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖((1 - t : ℝ) : ℂ) * iteratedDeriv 2 G (t • z)‖ ≤ Cm * ‖z‖ := by
      intro t ht
      have htIcc : t ∈ Set.Icc (0:ℝ) 1 := by
        have h := Set.uIoc_subset_uIcc ht
        rwa [Set.uIcc_of_le zero_le_one] at h
      have habs : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [htIcc.1, htIcc.2]
      have htz : ‖t • z‖ ≤ R / 2 := by
        rw [norm_smul, Real.norm_of_nonneg htIcc.1]
        calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right htIcc.2 (norm_nonneg z)
          _ = ‖z‖ := one_mul _
          _ ≤ R / 2 := hz
      have hnormt : ‖t • z‖ = t * ‖z‖ := by
        rw [norm_smul, Real.norm_of_nonneg htIcc.1]
      calc ‖((1 - t : ℝ) : ℂ) * iteratedDeriv 2 G (t • z)‖
          = |1 - t| * ‖iteratedDeriv 2 G (t • z)‖ := by
            rw [norm_mul, show ‖(((1 - t : ℝ)) : ℂ)‖ = |1 - t| from RCLike.norm_ofReal (1 - t)]
        _ ≤ 1 * (Cm * ‖t • z‖) := mul_le_mul habs (hbound (t • z) htz) (norm_nonneg _) (by norm_num)
        _ = Cm * (t * ‖z‖) := by rw [hnormt]; ring
        _ ≤ Cm * ‖z‖ := by
            apply mul_le_mul_of_nonneg_left _ hCm0
            calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right htIcc.2 (norm_nonneg z)
              _ = ‖z‖ := one_mul _
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const key
    simpa using h2
  rw [hL, hGz, norm_mul, norm_pow]
  calc ‖z‖ ^ 2 * ‖∫ t in (0:ℝ)..1, ((1 - t : ℝ) : ℂ) * iteratedDeriv 2 G (t • z)‖
      ≤ ‖z‖ ^ 2 * (Cm * ‖z‖) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = Cm * ‖z‖ ^ 3 := by ring

/-- Taylor remainder of a parabolic germ at the origin, with the *scaled* smallness `B ρ ≤ ε`:
`0 ∈ D₀` with `D₀` open gives `ρ₀ > 0` with `closedBall 0 ρ₀ ⊆ D₀`; `g z = f₀ z - z - z²` is
holomorphic on `ball 0 ρ₀` with `g 0 = g' 0 = g'' 0 = 0`, so `g z / z³` extends holomorphically to
`0` and is bounded by some `B` on `closedBall 0 ρ₀`; take `ρ := min ρ₀ (ε/(B+1))`. -/
theorem parab_germ_taylor_near0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ B ∧ Metric.closedBall 0 ρ ⊆ D₀ ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → ‖f₀ z - z - z ^ 2‖ ≤ B * ‖z‖ ^ 3) ∧ B * ρ ≤ ε := by
  obtain ⟨hopen, h0mem, hD, hf0, hder1, hder2⟩ := hd
  obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
  have hF : DifferentiableOn ℂ f₀ (Metric.ball 0 r) := hD.mono hrsub
  obtain ⟨C, hC0, hC⟩ := norm_sub_taylor_two_le hrpos hF
  have h2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hder2
  have hC1 : 0 < C + 1 := by linarith
  have hρpos : 0 < min 1 (min (r / 2) (ε / (C + 1))) :=
    lt_min one_pos (lt_min (by positivity) (div_pos hε hC1))
  refine ⟨min 1 (min (r / 2) (ε / (C + 1))), C, hρpos, min_le_left _ _, hC0, ?_, ?_, ?_⟩
  · have hle : min 1 (min (r / 2) (ε / (C + 1))) ≤ r / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact ((Metric.closedBall_subset_closedBall hle).trans
      (Metric.closedBall_subset_ball (by linarith))).trans hrsub
  · intro z hz
    have hz2 : ‖z‖ ≤ r / 2 := le_trans hz (le_trans (min_le_right _ _) (min_le_left _ _))
    have h := hC z hz2
    have heq : f₀ z - f₀ 0 - deriv f₀ 0 * z - (iteratedDeriv 2 f₀ 0 / 2) * z ^ 2
        = f₀ z - z - z ^ 2 := by
      rw [hf0, hder1, h2]; ring
    rwa [heq] at h
  · have hle : min 1 (min (r / 2) (ε / (C + 1))) ≤ ε / (C + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    calc C * min 1 (min (r / 2) (ε / (C + 1)))
        ≤ (C + 1) * min 1 (min (r / 2) (ε / (C + 1))) := by nlinarith [hρpos]
      _ ≤ (C + 1) * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hle (by linarith)
      _ = ε := by field_simp

end Work.Pert
