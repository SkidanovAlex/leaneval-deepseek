import Submission.Work.Fatou.DevH.basic

/-!
# Global properties of `devH`

From the derivative bound `‖D devH - I‖ ≤ 3/32` (proved in `DevH/devH_deriv.lean`) we deduce that
`devH x₀ F : ℂ → ℂ` is a globally expanding homeomorphism of the plane: it satisfies
`‖devH ζ - devH ζ' - (ζ - ζ')‖ ≤ 3/32 ‖ζ-ζ'‖`, hence is injective, surjective and an open map.
These are the properties that make `devH` usable as the basic chart of the Riemann surface `XF`.
-/

namespace Work.Fatou

open MandelDim Filter Set Metric
open scoped Topology

noncomputable section

/-- The quantitative input: `devH` is `C¹` and `‖D devH - I‖ ≤ 3/32` everywhere. -/
structure DevHBound (x₀ : ℝ) (F : ℂ → ℂ) : Prop where
  deriv_bound : ∀ ζ : ℂ, ‖fderiv ℝ (devH x₀ F) ζ - ContinuousLinearMap.id ℝ ℂ‖ ≤ 3 / 32
  contDiff : ContDiff ℝ 1 (devH x₀ F)

variable {x₀ : ℝ} {F : ℂ → ℂ}

theorem devH_expansion (h : DevHBound x₀ F) (ζ ζ' : ℂ) :
    ‖devH x₀ F ζ - devH x₀ F ζ' - (ζ - ζ')‖ ≤ 3 / 32 * ‖ζ - ζ'‖ := by
  have hdiff : ∀ x ∈ (Set.univ : Set ℂ), DifferentiableAt ℝ (devH x₀ F) x :=
    fun x _ => h.contDiff.differentiable_one.differentiableAt
  have := Convex.norm_image_sub_le_of_norm_fderiv_le' (f := devH x₀ F)
    (φ := ContinuousLinearMap.id ℝ ℂ) (C := 3 / 32) (s := Set.univ)
    hdiff (fun x _ => h.deriv_bound x) convex_univ (Set.mem_univ ζ') (Set.mem_univ ζ)
  simpa using this

theorem devH_expanding (h : DevHBound x₀ F) (ζ ζ' : ℂ) :
    (29 / 32) * ‖ζ - ζ'‖ ≤ ‖devH x₀ F ζ - devH x₀ F ζ'‖ := by
  have h1 := devH_expansion h ζ ζ'
  have h2 : ‖ζ - ζ'‖ ≤ (3 / 32) * ‖ζ - ζ'‖ + ‖devH x₀ F ζ - devH x₀ F ζ'‖ := by
    calc ‖ζ - ζ'‖ = ‖(ζ - ζ') - (devH x₀ F ζ - devH x₀ F ζ') +
          (devH x₀ F ζ - devH x₀ F ζ')‖ := by ring_nf
      _ ≤ ‖(ζ - ζ') - (devH x₀ F ζ - devH x₀ F ζ')‖ + ‖devH x₀ F ζ - devH x₀ F ζ'‖ :=
          norm_add_le _ _
      _ = ‖devH x₀ F ζ - devH x₀ F ζ' - (ζ - ζ')‖ + ‖devH x₀ F ζ - devH x₀ F ζ'‖ := by
          rw [show (ζ - ζ') - (devH x₀ F ζ - devH x₀ F ζ') =
            -(devH x₀ F ζ - devH x₀ F ζ' - (ζ - ζ')) by ring, norm_neg]
      _ ≤ (3 / 32) * ‖ζ - ζ'‖ + ‖devH x₀ F ζ - devH x₀ F ζ'‖ := by linarith
  linarith

theorem devH_injective (h : DevHBound x₀ F) : Function.Injective (devH x₀ F) := by
  intro ζ ζ' hζ
  have h2 := devH_expanding h ζ ζ'
  rw [hζ, sub_self, norm_zero] at h2
  have : ‖ζ - ζ'‖ = 0 := by nlinarith [norm_nonneg (ζ - ζ')]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `devH` maps the ball of radius `r` around `x` onto the ball of radius `(29/32) r` around
`devH x`: the image of a ball contains a ball of that radius. -/
theorem exists_preimage_mem_ball (h : DevHBound x₀ F) {x : ℂ} {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hw : ‖w - devH x₀ F x‖ < (29 / 32) * r) :
    ∃ y : ℂ, ‖y - x‖ < r ∧ devH x₀ F y = w := by
  set g : ℂ → ℂ := fun y => y + (w - devH x₀ F y) with hg
  have hfix : ∀ y, g y = y ↔ devH x₀ F y = w := by
    intro y
    simp only [hg]
    constructor
    · intro h
      have h1 : w - devH x₀ F y = 0 := by
        have h2 : (y + (w - devH x₀ F y)) - y = 0 := by rw [h, sub_self]
        simpa using h2
      exact (sub_eq_zero.mp h1).symm
    · intro h
      rw [h]; ring
  have hlip : LipschitzWith (3 / 32 : NNReal) g := by
    refine lipschitzWith_iff_dist_le_mul.2 (fun y y' => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    have hK : ((3 / 32 : NNReal) : ℝ) = 3 / 32 := by norm_num
    rw [hK]
    have hexp := devH_expansion h y y'
    calc ‖(y + (w - devH x₀ F y)) - (y' + (w - devH x₀ F y'))‖
        = ‖(y - y') - (devH x₀ F y - devH x₀ F y')‖ := by ring_nf
      _ = ‖devH x₀ F y - devH x₀ F y' - (y - y')‖ := by
          rw [show (y - y') - (devH x₀ F y - devH x₀ F y') =
            -(devH x₀ F y - devH x₀ F y' - (y - y')) by ring, norm_neg]
      _ ≤ 3 / 32 * ‖y - y'‖ := hexp
  have hcontr : ContractingWith (3 / 32 : NNReal) g := ⟨by norm_num, hlip⟩
  have hmaps : MapsTo g (closedBall x r) (closedBall x r) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    have hexp := devH_expansion h y x
    have hsplit : g y - x = (w - devH x₀ F x) - (devH x₀ F y - devH x₀ F x - (y - x)) := by
      simp only [hg]; ring
    rw [hsplit]
    calc ‖(w - devH x₀ F x) - (devH x₀ F y - devH x₀ F x - (y - x))‖
        ≤ ‖w - devH x₀ F x‖ + ‖devH x₀ F y - devH x₀ F x - (y - x)‖ := norm_sub_le _ _
      _ ≤ (29 / 32) * r + 3 / 32 * ‖y - x‖ := add_le_add hw.le hexp
      _ ≤ (29 / 32) * r + 3 / 32 * r := by linarith
      _ = r := by ring
  obtain ⟨y, hy, hyfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmaps (hcontr.restrict hmaps)
    (mem_closedBall_self hr) (by simp)
  have hwy : devH x₀ F y = w := (hfix y).1 hyfix
  refine ⟨y, ?_, hwy⟩
  have hexp := devH_expansion h y x
  rw [hwy] at hexp
  have h4 : ‖y - x‖ ≤ ‖w - devH x₀ F x‖ + ‖w - devH x₀ F x - (y - x)‖ := by
    calc ‖y - x‖ = ‖(w - devH x₀ F x) - (w - devH x₀ F x - (y - x))‖ := by ring_nf
      _ ≤ ‖w - devH x₀ F x‖ + ‖w - devH x₀ F x - (y - x)‖ := norm_sub_le _ _
  have h5 : ‖w - devH x₀ F x - (y - x)‖ ≤ 3 / 32 * ‖y - x‖ := hexp
  have h6 : ‖y - x‖ < (29 / 32) * r + 3 / 32 * ‖y - x‖ := by linarith
  nlinarith [norm_nonneg (y - x)]

theorem devH_surjective (h : DevHBound x₀ F) : Function.Surjective (devH x₀ F) := by
  intro w
  have hr : 0 ≤ (32 / 29) * ‖w - devH x₀ F 0‖ + 1 := by positivity
  have hw : ‖w - devH x₀ F 0‖ < (29 / 32) * ((32 / 29) * ‖w - devH x₀ F 0‖ + 1) := by
    nlinarith [norm_nonneg (w - devH x₀ F 0)]
  obtain ⟨y, _, hy⟩ := exists_preimage_mem_ball h hr hw
  exact ⟨y, hy⟩

theorem isOpenMap_devH (h : DevHBound x₀ F) : IsOpenMap (devH x₀ F) := by
  intro s hs
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxs, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hxs
  have hsub : ball (devH x₀ F x) ((29 / 32) * r) ⊆ devH x₀ F '' s := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    obtain ⟨z, hz, hzw⟩ := exists_preimage_mem_ball h (le_of_lt hr) hw
    exact ⟨z, hball (by rw [mem_ball, dist_eq_norm]; exact hz), hzw⟩
  exact mem_of_superset (ball_mem_nhds (devH x₀ F x) (by positivity)) hsub

end

end Work.Fatou
