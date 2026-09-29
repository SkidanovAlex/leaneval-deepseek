import Mathlib
import Submission.Work.PureP.basic
import Submission.Work.PureP.evp_B5_facts
import Submission.Work.CPull.pullbackMero_B4
import Submission.Work.CPull.exists_K_lift
import Submission.Work.B5pull.ode_algebra

open Complex Metric Filter PowerSeries
open scoped Topology
open Work.CPull

namespace Work.PureP

/-! The pullback germ of `B₅` along an arbitrary admissible map `φ` with a lift `Φ`.

Generic form of the (still open) `Work.CPull.pullbackMero_B5`, proved exactly as
`Work.CPull/pullbackMero_B4.lean` (proved) handles `B₂`/`B₄`, but with the linear ODE satisfied by
`B₅` (`Work.Pure.b5_rel`: `2X(4-X)·B₅' = (4-X)·B₅ - 2·B₂ + 4X`) instead of the `B₄`-equation.

Work in the `z`-variable with `y z = Φ z^2/(Φ z - 1) = φ (z^2)` (`Work.PureP.basic`:
`lift_zero`, `lift_ne_one`, `phi_sq_eq`, `phi_ne_zero`), `K` a holomorphic square root of `y - 4`
(`Work.CPull.exists_K_lift`), `Th = K`, `y' = 2 K K'`, `u₂ = evp B₂ ∘ y` (facts:
`Work.CPull.evp_B2_facts_ball1`), `u₅ = evp B₅ ∘ y` (facts: `Work.PureP.evp_B5_facts`), and
`V := (u₂ - 2y)/K`.

* `Work.B5pull.ode_algebra` gives, from the two first-order equations for `u₂'` and `u₅'`, the
  explicit linear ODEs `V' = (K K'/y)·V - 2K'` and `u₅' = (y'/(2y))·u₅ + (2K'/y)·V`
  (all on the punctured disc `0 < ‖z‖ < r`, `r` small enough that `‖y‖ < 1` and `K ≠ 0`).
* `V` extends holomorphically to the unit disc by `Work.CPull.linear_ode_extend`
  (this is exactly section 7 of `pullbackMero_B4.lean`); call the extension `Y₂`.
* `u₅` — holomorphic on `ball 0 r` — then extends to the whole disc by `linear_ode_extend`
  applied to `a z = y'/(2y)`, `b z = (2·K'/y)·Y₂ z` (both holomorphic on the punctured disc);
  call the extension `E`.
* `E` is even (`E z = E (-z)` for `‖z‖` small, since both agree with `evp B₅ (φ (z^2))`), so
  `Work.CPull.germ_of_even` / `even_descent` descends it to the required germ along `φ`.
-/
theorem germ_B5 (φ Φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0)
    (hL : Submission.CDTPlan.LiftData φ Φ) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      Filter.Eventually (fun w : ℂ => HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ) * φ w ^ n) (N w)) (nhds 0) := by
  -- ## 0. the data of the lift
  have hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1) := hL.1
  have hΦneq : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ≠ 1 := lift_ne_one hL
  have hPhi0 : Φ 0 = 0 := lift_zero hφ0 hL
  -- ## 2. `φ` has no other zero in the disc
  have hphi_ne : ∀ w ∈ Metric.ball (0:ℂ) 1, φ w = 0 → w = 0 := phi_ne_zero hL
  -- ## 3. the square root `K` of `y - 4` and the symmetrisation coordinate `y`
  obtain ⟨K, hKdiff, hKsq⟩ := exists_K_lift Φ hΦ hΦneq
  let y : ℂ → ℂ := fun z => (Φ z) ^ 2 / (Φ z - 1)
  have hyK : ∀ z ∈ Metric.ball (0:ℂ) 1, y z = (K z) ^ 2 + 4 := by
    intro z hz
    have h := hKsq z hz
    show (Φ z) ^ 2 / (Φ z - 1) = (K z) ^ 2 + 4
    exact h.symm
  have hyphi : ∀ z ∈ Metric.ball (0:ℂ) 1, y z = φ (z ^ 2) := by
    intro z hz
    have h := phi_sq_eq hL z hz
    show (Φ z) ^ 2 / (Φ z - 1) = φ (z ^ 2)
    exact h.symm
  have hy0 : y 0 = 0 := by
    show (Φ 0) ^ 2 / (Φ 0 - 1) = 0
    rw [hPhi0]
    norm_num
  -- ## 4. `K 0 ≠ 0` and the choice of the radius `r`
  have hK0 : K 0 ≠ 0 := by
    intro hc
    have h := hyK 0 (by simp [Metric.mem_ball])
    rw [hc] at h
    rw [hy0] at h
    norm_num at h
  have hyd1 : DifferentiableOn ℂ y (Metric.ball (0:ℂ) 1) := by
    show DifferentiableOn ℂ (fun z : ℂ => (Φ z) ^ 2 / (Φ z - 1)) (Metric.ball 0 1)
    exact (hΦ.pow 2).div (hΦ.sub_const 1) (fun z hz => sub_ne_zero.mpr (hΦneq z hz))
  obtain ⟨r, hr0, hr1, hKr, hyr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ z ∈ Metric.ball (0:ℂ) r, K z ≠ 0) ∧
      (∀ z ∈ Metric.ball (0:ℂ) r, ‖y z‖ < 1) := by
    have hKcont : ContinuousAt K 0 :=
      (hKdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
    have hycont : ContinuousAt y 0 :=
      (hyd1.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), K z ≠ 0 :=
      hKcont.eventually (isOpen_compl_singleton.mem_nhds hK0)
    obtain ⟨r1, hr1pos, hr1sub⟩ := Metric.eventually_nhds_iff.mp h1
    have h2 : ∀ᶠ z in 𝓝 (0:ℂ), ‖y z‖ < 1 := by
      have hyb : Metric.ball (0:ℂ) 1 ∈ 𝓝 (y 0) := by
        rw [hy0]; exact Metric.ball_mem_nhds 0 one_pos
      filter_upwards [hycont.eventually hyb] with z hz
      simpa [Metric.mem_ball, dist_zero_right] using hz
    obtain ⟨r2, hr2pos, hr2sub⟩ := Metric.eventually_nhds_iff.mp h2
    refine ⟨min (min r1 r2) (1/2), lt_min (lt_min hr1pos hr2pos) (by norm_num),
      by linarith [min_le_right (min r1 r2) (1/2)], ?_, ?_⟩
    · intro z hz
      rw [Metric.mem_ball] at hz
      exact hr1sub (lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _)))
    · intro z hz
      rw [Metric.mem_ball] at hz
      exact hr2sub (lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _)))
  -- ## 5. the pullback germs `u₂`, `u₅` and the unknown `V`
  have hydr : DifferentiableOn ℂ y (Metric.ball (0:ℂ) r) :=
    hyd1.mono (Metric.ball_subset_ball (le_of_lt hr1))
  obtain ⟨hU2diff, hU2sum, hU2ode⟩ := evp_B2_facts_ball1
  obtain ⟨hU5diff, hU5sum, hU5ode⟩ := evp_B5_facts
  have hymem : ∀ z ∈ Metric.ball (0:ℂ) r, y z ∈ Metric.ball (0:ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact hyr z hz
  let u2 : ℂ → ℂ := fun z => evp Submission.CDTPlan.B2 (y z)
  let u5 : ℂ → ℂ := fun z => evp Submission.CDTPlan.B5 (y z)
  have hu2d : DifferentiableOn ℂ u2 (Metric.ball (0:ℂ) r) := by
    have h := hU2diff.comp hydr hymem
    simpa [u2, Function.comp_def] using h
  have hu5d : DifferentiableOn ℂ u5 (Metric.ball (0:ℂ) r) := by
    have h := hU5diff.comp hydr hymem
    simpa [u5, Function.comp_def] using h
  let V : ℂ → ℂ := fun z => (u2 z - 2 * y z) / K z
  have hKr1 : DifferentiableOn ℂ K (Metric.ball (0:ℂ) r) :=
    hKdiff.mono (Metric.ball_subset_ball (le_of_lt hr1))
  have hVd : DifferentiableOn ℂ V (Metric.ball (0:ℂ) r) := by
    have h : DifferentiableOn ℂ (fun z : ℂ => (u2 z - 2 * y z) / K z) (Metric.ball (0:ℂ) r) :=
      (hu2d.sub (hydr.const_mul 2)).div hKr1 hKr
    exact h
  -- ## 6. the ODEs for `V` and `u₅` on the punctured ball
  have hyz_ne : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → y z ≠ 0 := by
    intro z hz0 hz1'
    intro h0
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hz1'
    have h1 : φ (z ^ 2) = 0 := by rw [← hyphi z hz1, h0]
    have hzsq1 : z ^ 2 ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_pow]
      exact pow_lt_one₀ (norm_nonneg z) hz1' (by norm_num)
    have h2 : z ^ 2 = 0 := hphi_ne (z ^ 2) hzsq1 h1
    have h3 : z = 0 := by
      have h4 : z * z = 0 := by rwa [pow_two] at h2
      exact mul_self_eq_zero.mp h4
    rw [h3] at hz0
    simp at hz0
  have hODE : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      (deriv V z = (K z * deriv K z / y z) * V z - 2 * deriv K z) ∧
      (deriv u5 z = (deriv y z / (2 * y z)) * u5 z + (2 * deriv K z / y z) * V z) := by
    intro z hzpos hzr
    have hzr' : z ∈ Metric.ball (0:ℂ) r := by rw [Metric.mem_ball, dist_zero_right]; exact hzr
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := Metric.ball_subset_ball (le_of_lt hr1) hzr'
    have hKz : K z ≠ 0 := hKr z hzr'
    have hyzmem : y z ∈ Metric.ball (0:ℂ) 1 := hymem z hzr'
    have hyz : y z ≠ 0 := hyz_ne z hzpos (lt_of_lt_of_le hzr (le_of_lt hr1))
    have hyKz : y z = (K z) ^ 2 + 4 := hyK z hz1
    have hK2z : (K z) ^ 2 = y z - 4 := by rw [hyKz]; ring
    have h4yz : (4 : ℂ) - y z ≠ 0 := by
      rw [hyKz]
      intro h
      have h' : (K z) ^ 2 = 0 := by linear_combination -h
      exact pow_ne_zero 2 hKz h'
    have hyat : HasDerivAt y (deriv y z) z :=
      (hyd1.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)).hasDerivAt
    have hKat : HasDerivAt K (deriv K z) z :=
      (hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)).hasDerivAt
    have hVat : HasDerivAt V (deriv V z) z :=
      (hVd.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt
    have hydz : deriv y z = 2 * K z * deriv K z := by
      have heq : y =ᶠ[𝓝 z] fun w => (K w) ^ 2 + 4 :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz1) (fun w hw => hyK w hw)
      rw [heq.deriv_eq]
      have h2 : HasDerivAt (fun w : ℂ => (K w) ^ 2 + 4) (2 * K z * deriv K z) z := by
        have h3 := (hKat.pow 2).const_add 4
        simpa using h3
      exact h2.deriv
    have hu2at : HasDerivAt u2
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z) * deriv y z) z := by
      have hU2at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B2 w)
          (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z)) (y z) :=
        (hU2diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
      have h := hU2at.comp z hyat
      simpa [u2, Function.comp_def] using h
    have hu5at : HasDerivAt u5
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B5 w) (y z) * deriv y z) z := by
      have hU5at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B5 w)
          (deriv (fun w : ℂ => evp Submission.CDTPlan.B5 w) (y z)) (y z) :=
        (hU5diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
      have h := hU5at.comp z hyat
      simpa [u5, Function.comp_def] using h
    -- the algebraic form of the definition of `V`
    have hVdef : u2 z = 2 * y z + K z * V z := by
      simp only [u2, V]
      rw [mul_div_cancel₀ _ hKz]
      ring
    -- differentiating it
    have hWdiff : deriv u2 z = 2 * deriv y z + deriv K z * V z + K z * deriv V z := by
      have h2at : HasDerivAt (fun w : ℂ => 2 * y w + K w * V w)
          (2 * deriv y z + (deriv K z * V z + K z * deriv V z)) z :=
        (hyat.const_mul 2).add (hKat.mul hVat)
      have heq : u2 =ᶠ[𝓝 z] fun w => 2 * y w + K w * V w :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hzr') (fun w hw => by
          simp only [u2, V]
          rw [mul_div_cancel₀ _ (hKr w hw)]
          ring)
      rw [heq.deriv_eq, h2at.deriv]
      ring
    -- the equation for `u₅'`
    have hneq : 2 * y z * (4 - y z) * deriv u5 z
        = deriv y z * ((4 - y z) * u5 z - 2 * u2 z + 4 * y z) := by
      have h := hU5ode (y z) hyzmem
      rw [hu5at.deriv]
      simp only [u5, u2]
      linear_combination (deriv y z) * h
    -- the equation for `u₂'`
    have h2eq : y z * (4 - y z) * deriv u2 z
        = deriv y z * ((2 - y z) * u2 z + (y z) ^ 2) := by
      have h := hU2ode (y z) hyzmem
      rw [hu2at.deriv]
      simp only [u2]
      linear_combination (deriv y z) * h
    exact Work.B5pull.ode_algebra (Th := K z) (Y := y z) (U := u5 z) (W := u2 z) (V := V z)
      (Y' := deriv y z) (Th' := deriv K z) (U' := deriv u5 z) (W' := deriv u2 z)
      (V' := deriv V z) hKz hyz hK2z hydz hVdef hWdiff hneq h2eq
  -- ## 7. continuation of `V` and of `u₅` to the unit disc
  let c : ℂ → ℂ := fun z => K z * deriv K z / y z
  have hpu : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → z ∈ Metric.ball (0:ℂ) 1 := by
    intro z _ hz
    rw [Metric.mem_ball, dist_zero_right]; exact hz
  have hdc : DifferentiableOn ℂ (deriv K) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hKdiff.deriv Metric.isOpen_ball).mono (fun z hz => hpu z hz.1 hz.2)
  have hKpu : DifferentiableOn ℂ K {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hKdiff.mono (fun z hz => hpu z hz.1 hz.2)
  have hypu : DifferentiableOn ℂ y {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hyd1.mono (fun z hz => hpu z hz.1 hz.2)
  have hdy : DifferentiableOn ℂ (deriv y) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hyd1.deriv Metric.isOpen_ball).mono (fun z hz => hpu z hz.1 hz.2)
  have hc : DifferentiableOn ℂ c {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hKpu.mul hdc).div hypu (fun z hz => hyz_ne z hz.1 hz.2)
  have hb1 : DifferentiableOn ℂ (fun z : ℂ => -(2 * deriv K z)) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hdc.const_mul 2).neg
  have hVode' : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V (c z * V z + -(2 * deriv K z)) z := by
    intro z hz0 hzr
    have hzr' : z ∈ Metric.ball (0:ℂ) r := by rw [Metric.mem_ball, dist_zero_right]; exact hzr
    have h := (hVd.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt
    refine h.congr_deriv ?_
    rw [(hODE z hz0 hzr).1]
    simp only [c]
    ring
  obtain ⟨Y2, hY2diff, hY2eq⟩ :=
    linear_ode_extend (a := c) (b := fun z => -(2 * deriv K z)) (V := V) (r := r)
      hr0 hr1 hc hb1 hVd hVode'
  have ha : DifferentiableOn ℂ (fun z : ℂ => deriv y z / (2 * y z))
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hdy.div (hypu.const_mul 2) (fun z hz => mul_ne_zero (by norm_num) (hyz_ne z hz.1 hz.2))
  have hb2 : DifferentiableOn ℂ (fun z : ℂ => (2 * deriv K z / y z) * Y2 z)
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    ((hdc.const_mul 2).div hypu (fun z hz => hyz_ne z hz.1 hz.2)).mul
      (hY2diff.mono (fun z hz => hpu z hz.1 hz.2))
  have hu5ode' : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt u5 ((deriv y z / (2 * y z)) * u5 z + (2 * deriv K z / y z) * Y2 z) z := by
    intro z hz0 hzr
    have hzr' : z ∈ Metric.ball (0:ℂ) r := by rw [Metric.mem_ball, dist_zero_right]; exact hzr
    have h := (hu5d.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt
    refine h.congr_deriv ?_
    rw [(hODE z hz0 hzr).2, ← hY2eq hzr']
  obtain ⟨E, hEdiff, hEeq⟩ :=
    linear_ode_extend (a := fun z : ℂ => deriv y z / (2 * y z))
      (b := fun z : ℂ => (2 * deriv K z / y z) * Y2 z) (V := u5) (r := r)
      hr0 hr1 ha hb2 hu5d hu5ode'
  -- ## 8. the holomorphic function `E`, its evenness and its germ
  have hevenEv : ∀ᶠ z in 𝓝 (0:ℂ), E z = E (-z) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr0] with z hz
    have hzr' : ‖z‖ < r := by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
    have hzn : -z ∈ Metric.ball (0:ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_neg]; exact hzr'
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := Metric.ball_subset_ball (le_of_lt hr1) hz
    have hzn1 : -z ∈ Metric.ball (0:ℂ) 1 := Metric.ball_subset_ball (le_of_lt hr1) hzn
    have hyneg : y (-z) = y z := by
      rw [hyphi (-z) hzn1, hyphi z hz1, show (-z) ^ 2 = z ^ 2 by ring]
    show E z = E (-z)
    rw [hEeq hz, hEeq hzn]
    simp only [u5]
    rw [hyneg]
  have heven : ∀ z ∈ Metric.ball (0:ℂ) 1, E (-z) = E z := by
    have hneg : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      simpa using hz
    have h2 : DifferentiableOn ℂ (fun z => E (-z)) (Metric.ball (0:ℂ) 1) :=
      hEdiff.comp differentiable_neg.differentiableOn hneg
    have heq : Set.EqOn E (fun z => E (-z)) (Metric.ball (0:ℂ) 1) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        (hEdiff.analyticOnNhd Metric.isOpen_ball) (h2.analyticOnNhd Metric.isOpen_ball)
        (convex_ball (0:ℂ) 1).isPreconnected (by simp [Metric.mem_ball]) hevenEv
    intro z hz
    exact (heq hz).symm
  have hgerm : ∀ᶠ z in 𝓝 (0:ℂ), HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ) *
        φ (z ^ 2) ^ n) (E z) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr0] with z hz
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := Metric.ball_subset_ball (le_of_lt hr1) hz
    have hyzmem : y z ∈ Metric.ball (0:ℂ) 1 := hymem z hz
    have hEz : E z = evp Submission.CDTPlan.B5 (y z) := by
      rw [hEeq hz]
    rw [hEz, ← hyphi z hz1]
    exact hU5sum (y z) hyzmem
  exact Work.CPull.germ_of_even hEdiff heven hgerm

end Work.PureP
