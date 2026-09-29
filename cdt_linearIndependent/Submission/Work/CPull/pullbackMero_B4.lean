import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CPull.defs
import Submission.Work.CLift.basic_aux
import Submission.Work.CPsi.psiC_facts
import Submission.Work.Haupt.haupt_facts
import Submission.Work.CPull.even_descent
import Submission.Work.CPull.evp_B4_facts
import Submission.Work.CPull.evp_B2_facts_ball1
import Submission.Work.CPull.exists_K_lift
import Submission.Work.CPull.v_sys_alg
import Submission.Work.CPull.linear_ode_extend

/-!
# Area CPull — the meromorphic pullback of `B₄` along `φ_C`

`Submission.CDTPlan.PullbackMero B₄ φ_C`.

Route (the `Y_0(2)`-descent of the paper, Lemma `analytic quotient`): for the *even* germ
`z ↦ Σₙ cₙ φ_C(z²)ⁿ` (`cₙ = coeff n B₄`) we produce a holomorphic `E` on the unit disc with
`E z = Σₙ cₙ φ_C(z²)ⁿ` near `0`; the even-descent lemma `pullbackMero_of_even'` then converts
this into `PullbackMero B₄ φ_C`.

Construction of `E`.  Write `Φ` for the given lift and

* `y z = (Φ z)²/(Φ z - 1) = φ_C(z²)` (by the lift relation `hrel`),
* `K` for a holomorphic square root of `y - 4` on the disc, obtained from `K = (Φ-2)/√(Φ-1)`
  (the disc is simply connected and `Φ ≠ 1`); the ramification `y - 4 = K²` is what makes `B₄`
  — whose only singularity is the order-two branch point at `y = 4` — single valued after
  pullback.

The two pullback germs `u₂ = evp B₂ ∘ y`, `u₄ = evp B₄ ∘ y` satisfy, in the variable `z`,
`u₂' = 2y' + (the singular part)`; the substitutions

* `V₂ = (u₂ - 2y)/K`, `V₄ = u₄/K`

kill the singularities at `K = 0`, and the identities `y(4-y) u₂' = ...`, `y(4-y) u₄' = ...`
together with `y' = 2KK'` give the *linear system*

`V₂' = (KK'/y) V₂ - 2 K'`,  `V₄' = (KK'/y) (V₄ + 2 V₂)`,

whose coefficients are holomorphic on the punctured unit disc (`y` vanishes only at `0`).
The continuation theorem `linear_ode_extend` extends `V₂` (then `V₄`, whose source term is the now
global `V₂`) holomorphically to the whole disc, and `E z = K z · Y₄ z` is the desired holomorphic
function.
-/

namespace Work.CPull

open Complex Metric Filter PowerSeries
open scoped Topology

private lemma sq_sqrt_c (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [sqrt_eq_exp hw, pow_two, ← Complex.exp_add,
      show Complex.log w / 2 + Complex.log w / 2 = Complex.log w by ring, Complex.exp_log hw]

/-- Even descent: if the germ at `0` of `z ↦ Σₙ aₙ Ψ(z²)ⁿ` is the even holomorphic function `E`
on the disc, then the pullback of `f = Σ aₙ yⁿ` along `Ψ` is meromorphic (denominator `1`).
Local copy of `Work.CPull.pullbackMero_of_even`. -/
private lemma pullbackMero_of_even' {Ψ : ℂ → ℂ} {f : PowerSeries ℚ} {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E (Metric.ball 0 1))
    (heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z)
    (hgerm : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ (z ^ 2) ^ n) (E z)) :
    Submission.CDTPlan.PullbackMero f Ψ := by
  obtain ⟨N, hN, hNz⟩ := even_descent E hE heven
  refine ⟨1, N, by simp, hN, ?_⟩
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hgerm
  set r : ℝ := min ε 1 with hrdef
  have hrpos : 0 < r := lt_min hεpos one_pos
  refine Filter.Eventually.mono
    (Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0:ℝ) < r ^ 2)) ?_
  intro w hw
  have hwn : ‖w‖ < r ^ 2 := by simpa [dist_eq_norm] using hw
  set z : ℂ := Complex.sqrt w with hzdef
  have hzsq : z ^ 2 = w := by rw [hzdef]; exact sq_sqrt_c w
  have hzn : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hzsq]
  have hzr : ‖z‖ < r := by
    have h1 : ‖z‖ ^ 2 < r ^ 2 := by rw [hzn]; exact hwn
    nlinarith [norm_nonneg z, hrpos, h1]
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_right _ _)
  have hzeps : dist z 0 < ε := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_left _ _)
  have h := hε hzeps
  rw [hzsq] at h
  rw [← hNz z hzmem] at h
  rw [hzsq] at h
  simpa using h

theorem pullbackMero_B4 (Φ : ℂ → ℂ) (hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦneq : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ≠ 1)
    (hrel : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z + Φ (-z) = Submission.CDTPlan.phiC (z^2) ∧
      Φ z * Φ (-z) = Submission.CDTPlan.phiC (z^2)) :
    Submission.CDTPlan.PullbackMero Submission.CDTPlan.B4 Submission.CDTPlan.phiC := by
  -- ## 1. `phiC 0 = 0` and `Φ 0 = 0`
  have hpsi0 : Submission.CDTPlan.psiC 0 = 0 := Work.CPsi.psiC_facts.2.2.1
  have hphiC0 : Submission.CDTPlan.phiC 0 = 0 := by
    show Submission.CDTPlan.hauptH (Submission.CDTPlan.psiC 0) = 0
    rw [hpsi0]
    simp [Submission.CDTPlan.hauptH]
  have hPhi0 : Φ 0 = 0 := by
    have h := (hrel 0 (by simp [Metric.mem_ball])).2
    have h2 : Φ 0 * Φ 0 = 0 := by simpa [hphiC0] using h
    exact mul_self_eq_zero.mp h2
  -- ## 2. `phiC` has no other zero in the disc
  have hphiC_ne : ∀ w ∈ Metric.ball (0:ℂ) 1, Submission.CDTPlan.phiC w = 0 → w = 0 := by
    intro w hw h0
    have hψ : Submission.CDTPlan.psiC w = 0 := by
      have hmem : Submission.CDTPlan.psiC w ∈ Metric.ball (0:ℂ) 1 := by
        have hb := Work.CPsi.psiC_facts.2.2.2.2.1 w (Metric.ball_subset_closedBall hw)
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      exact Work.Haupt.hauptH_ne_zero (Submission.CDTPlan.psiC w) hmem
        (by simpa [Submission.CDTPlan.phiC] using h0)
    exact Work.CPsi.psiC_facts.2.2.2.2.2 w (Metric.ball_subset_closedBall hw) hψ
  -- ## 3. the square root `K` of `y - 4` and the symmetrisation coordinate `y`
  obtain ⟨K, hKdiff, hKsq⟩ := exists_K_lift Φ hΦ hΦneq
  let y : ℂ → ℂ := fun z => (Φ z) ^ 2 / (Φ z - 1)
  have hyK : ∀ z ∈ Metric.ball (0:ℂ) 1, y z = (K z) ^ 2 + 4 := by
    intro z hz
    have h := hKsq z hz
    show (Φ z) ^ 2 / (Φ z - 1) = (K z) ^ 2 + 4
    exact h.symm
  have hyphi : ∀ z ∈ Metric.ball (0:ℂ) 1, y z = Submission.CDTPlan.phiC (z ^ 2) := by
    intro z hz
    have h := Work.CLift.phiC_sq_eq Φ hrel z hz (hΦneq z hz)
    show (Φ z) ^ 2 / (Φ z - 1) = Submission.CDTPlan.phiC (z ^ 2)
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
  -- ## 5. the pullback germs `u₂`, `u₄` and the unknowns `V₂`, `V₄`
  have hydr : DifferentiableOn ℂ y (Metric.ball (0:ℂ) r) :=
    hyd1.mono (Metric.ball_subset_ball (le_of_lt hr1))
  obtain ⟨hU2diff, hU2sum, hU2ode⟩ := evp_B2_facts_ball1
  obtain ⟨hU4diff, hU4sum, hU4ode⟩ := evp_B4_facts
  have hymem : ∀ z ∈ Metric.ball (0:ℂ) r, y z ∈ Metric.ball (0:ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact hyr z hz
  let u2 : ℂ → ℂ := fun z => evp Submission.CDTPlan.B2 (y z)
  let u4 : ℂ → ℂ := fun z => evp Submission.CDTPlan.B4 (y z)
  have hu2d : DifferentiableOn ℂ u2 (Metric.ball (0:ℂ) r) := by
    have h := hU2diff.comp hydr hymem
    simpa [u2, Function.comp_def] using h
  have hu4d : DifferentiableOn ℂ u4 (Metric.ball (0:ℂ) r) := by
    have h := hU4diff.comp hydr hymem
    simpa [u4, Function.comp_def] using h
  let V2 : ℂ → ℂ := fun z => (u2 z - 2 * y z) / K z
  let V4 : ℂ → ℂ := fun z => u4 z / K z
  have hKr1 : DifferentiableOn ℂ K (Metric.ball (0:ℂ) r) :=
    hKdiff.mono (Metric.ball_subset_ball (le_of_lt hr1))
  have hV2d : DifferentiableOn ℂ V2 (Metric.ball (0:ℂ) r) := by
    have h : DifferentiableOn ℂ (fun z : ℂ => (u2 z - 2 * y z) / K z) (Metric.ball (0:ℂ) r) :=
      (hu2d.sub (hydr.const_mul 2)).div hKr1 hKr
    exact h
  have hV4d : DifferentiableOn ℂ V4 (Metric.ball (0:ℂ) r) := by
    have h : DifferentiableOn ℂ (fun z : ℂ => u4 z / K z) (Metric.ball (0:ℂ) r) :=
      hu4d.div hKr1 hKr
    exact h
  -- ## 6. the ODE system on the punctured ball
  have hyz_ne : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → y z ≠ 0 := by
    intro z hz0 hz1'
    intro h0
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hz1'
    have h1 : Submission.CDTPlan.phiC (z ^ 2) = 0 := by rw [← hyphi z hz1, h0]
    have hzsq1 : z ^ 2 ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_pow]
      exact pow_lt_one₀ (norm_nonneg z) hz1' (by norm_num)
    have h2 : z ^ 2 = 0 := hphiC_ne (z ^ 2) hzsq1 h1
    have h3 : z = 0 := by
      have h4 : z * z = 0 := by rwa [pow_two] at h2
      exact mul_self_eq_zero.mp h4
    rw [h3] at hz0
    simp at hz0
  have hV2ode : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V2 ((K z * deriv K z / y z) * V2 z - 2 * deriv K z) z := by
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
    have hydz : deriv y z = 2 * K z * deriv K z := by
      have heq : y =ᶠ[𝓝 z] fun w => (K w) ^ 2 + 4 :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz1) (fun w hw => hyK w hw)
      rw [heq.deriv_eq]
      have hKd : DifferentiableAt ℂ K z := hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
      have h2 : HasDerivAt (fun w : ℂ => (K w) ^ 2 + 4) (2 * K z * deriv K z) z := by
        have h1 : HasDerivAt K (deriv K z) z := hKd.hasDerivAt
        have h3 := (h1.pow 2).const_add 4
        simpa using h3
      exact h2.deriv
    have hU2at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B2 w)
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z)) (y z) :=
      (hU2diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
    have hu2at : HasDerivAt u2
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z) * deriv y z) z := by
      have h := hU2at.comp z hyat
      simpa [u2, Function.comp_def] using h
    have hU2ode_at := hU2ode (y z) hyzmem
    have hderivU2 : deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z)
        = ((2 - y z) * evp Submission.CDTPlan.B2 (y z) + (y z) ^ 2) / (y z * (4 - y z)) := by
      rw [eq_div_iff (mul_ne_zero hyz h4yz)]
      linear_combination hU2ode_at
    have hu2' : deriv u2 z
        = deriv y z * ((2 - y z) * u2 z + (y z) ^ 2) / (y z * (4 - y z)) := by
      rw [hu2at.deriv, hderivU2]
      simp only [u2]
      ring
    have hV2def : u2 z = 2 * y z + K z * V2 z := by
      simp only [V2]
      field_simp
      try ring
    have halg := v_sys_alg (u2 z) (u4 z) (deriv u2 z) (deriv u4 z) (y z) (deriv y z)
      (K z) (deriv K z) (V2 z) (V4 z) hKz hyz hK2z hydz hV2def (by
        simp only [V4]; field_simp; try ring) hu2' (by
        have hU4at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B4 w)
            (deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z)) (y z) :=
          (hU4diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
        have hu4at : HasDerivAt u4
            (deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z) * deriv y z) z := by
          have h := hU4at.comp z hyat
          simpa [u4, Function.comp_def] using h
        have hU4ode_at := hU4ode (y z) hyzmem
        have hderivU4 : deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z)
            = ((2 - y z) * evp Submission.CDTPlan.B4 (y z) + (4 - y z) * evp Submission.CDTPlan.B2 (y z)
                - 2 * y z * (4 - y z)) / (y z * (4 - y z)) := by
          rw [eq_div_iff (mul_ne_zero hyz h4yz)]
          linear_combination hU4ode_at
        rw [hu4at.deriv, hderivU4]
        simp only [u4, u2]
        ring)
    have hnum2 := halg.1
    have hnum4 := halg.2
    have hV2at : HasDerivAt V2
        (((deriv u2 z - 2 * deriv y z) * K z - (u2 z - 2 * y z) * deriv K z) / (K z) ^ 2) z := by
      have hnum : HasDerivAt (fun w : ℂ => u2 w - 2 * y w) (deriv u2 z - 2 * deriv y z) z :=
        ((hu2d.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt).sub
          (hyat.const_mul 2)
      have hKat : HasDerivAt K (deriv K z) z :=
        (hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)).hasDerivAt
      have h : HasDerivAt (fun w : ℂ => (u2 w - 2 * y w) / K w)
          (((deriv u2 z - 2 * deriv y z) * K z - (u2 z - 2 * y z) * deriv K z) / (K z) ^ 2) z :=
        hnum.div hKat hKz
      exact h
    have hgoal2 : ((deriv u2 z - 2 * deriv y z) * K z - (u2 z - 2 * y z) * deriv K z) / (K z) ^ 2
        = (K z * deriv K z / y z) * V2 z - 2 * deriv K z := by
      rw [div_eq_iff (pow_ne_zero 2 hKz), hnum2]
    exact hV2at.congr_deriv hgoal2
  have hV4ode : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V4 ((K z * deriv K z / y z) * V4 z
        + (K z * deriv K z / y z) * (2 * V2 z)) z := by
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
    have hydz : deriv y z = 2 * K z * deriv K z := by
      have heq : y =ᶠ[𝓝 z] fun w => (K w) ^ 2 + 4 :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz1) (fun w hw => hyK w hw)
      rw [heq.deriv_eq]
      have hKd : DifferentiableAt ℂ K z := hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
      have h2 : HasDerivAt (fun w : ℂ => (K w) ^ 2 + 4) (2 * K z * deriv K z) z := by
        have h1 : HasDerivAt K (deriv K z) z := hKd.hasDerivAt
        have h3 := (h1.pow 2).const_add 4
        simpa using h3
      exact h2.deriv
    have hU2at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B2 w)
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z)) (y z) :=
      (hU2diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
    have hu2at : HasDerivAt u2
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z) * deriv y z) z := by
      have h := hU2at.comp z hyat
      simpa [u2, Function.comp_def] using h
    have hU2ode_at := hU2ode (y z) hyzmem
    have hderivU2 : deriv (fun w : ℂ => evp Submission.CDTPlan.B2 w) (y z)
        = ((2 - y z) * evp Submission.CDTPlan.B2 (y z) + (y z) ^ 2) / (y z * (4 - y z)) := by
      rw [eq_div_iff (mul_ne_zero hyz h4yz)]
      linear_combination hU2ode_at
    have hu2' : deriv u2 z
        = deriv y z * ((2 - y z) * u2 z + (y z) ^ 2) / (y z * (4 - y z)) := by
      rw [hu2at.deriv, hderivU2]
      simp only [u2]
      ring
    have hV2def : u2 z = 2 * y z + K z * V2 z := by
      simp only [V2]
      field_simp
      try ring
    have hV4def : u4 z = K z * V4 z := by
      simp only [V4]
      field_simp
      try ring
    have hU4at : HasDerivAt (fun w : ℂ => evp Submission.CDTPlan.B4 w)
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z)) (y z) :=
      (hU4diff.differentiableAt (Metric.isOpen_ball.mem_nhds hyzmem)).hasDerivAt
    have hu4at : HasDerivAt u4
        (deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z) * deriv y z) z := by
      have h := hU4at.comp z hyat
      simpa [u4, Function.comp_def] using h
    have hU4ode_at := hU4ode (y z) hyzmem
    have hderivU4 : deriv (fun w : ℂ => evp Submission.CDTPlan.B4 w) (y z)
        = ((2 - y z) * evp Submission.CDTPlan.B4 (y z) + (4 - y z) * evp Submission.CDTPlan.B2 (y z)
            - 2 * y z * (4 - y z)) / (y z * (4 - y z)) := by
      rw [eq_div_iff (mul_ne_zero hyz h4yz)]
      linear_combination hU4ode_at
    have hu4' : deriv u4 z
        = deriv y z * ((2 - y z) * u4 z + (4 - y z) * u2 z - 2 * y z * (4 - y z))
            / (y z * (4 - y z)) := by
      rw [hu4at.deriv, hderivU4]
      simp only [u4, u2]
      ring
    have halg := v_sys_alg (u2 z) (u4 z) (deriv u2 z) (deriv u4 z) (y z) (deriv y z)
      (K z) (deriv K z) (V2 z) (V4 z) hKz hyz hK2z hydz hV2def hV4def hu2' hu4'
    have hnum4 := halg.2
    have hV4at : HasDerivAt V4 ((deriv u4 z * K z - u4 z * deriv K z) / (K z) ^ 2) z := by
      have hnum : HasDerivAt u4 (deriv u4 z) z :=
        (hu4d.differentiableAt (Metric.isOpen_ball.mem_nhds hzr')).hasDerivAt
      have hKat : HasDerivAt K (deriv K z) z :=
        (hKdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)).hasDerivAt
      have h : HasDerivAt (fun w : ℂ => u4 w / K w)
          ((deriv u4 z * K z - u4 z * deriv K z) / (K z) ^ 2) z := hnum.div hKat hKz
      exact h
    have hgoal4 : (deriv u4 z * K z - u4 z * deriv K z) / (K z) ^ 2
        = (K z * deriv K z / y z) * V4 z + (K z * deriv K z / y z) * (2 * V2 z) := by
      rw [div_eq_iff (pow_ne_zero 2 hKz)]
      linear_combination hnum4
    exact hV4at.congr_deriv hgoal4
  -- ## 7. continuation of `V₂` and `V₄` to the unit disc
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
  have hc : DifferentiableOn ℂ c {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hKpu.mul hdc).div hypu (fun z hz => hyz_ne z hz.1 hz.2)
  have hb1 : DifferentiableOn ℂ (fun z : ℂ => -(2 * deriv K z)) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hdc.const_mul 2).neg
  have hV2ode' : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V2 (c z * V2 z + -(2 * deriv K z)) z := by
    intro z hz0 hzr
    have h := hV2ode z hz0 hzr
    refine h.congr_deriv ?_
    simp only [c]
    ring
  obtain ⟨Y2, hY2diff, hY2eq⟩ :=
    linear_ode_extend (a := c) (b := fun z => -(2 * deriv K z)) (V := V2) (r := r)
      hr0 hr1 hc hb1 hV2d hV2ode'
  have hb2 : DifferentiableOn ℂ (fun z : ℂ => 2 * c z * Y2 z) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hc.const_mul 2).mul (hY2diff.mono (fun z hz => hpu z hz.1 hz.2))
  have hV4ode' : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt V4 (c z * V4 z + 2 * c z * Y2 z) z := by
    intro z hz0 hzr
    have hzr' : z ∈ Metric.ball (0:ℂ) r := by rw [Metric.mem_ball, dist_zero_right]; exact hzr
    have hV2eq : V2 z = Y2 z := (hY2eq hzr').symm
    have h := hV4ode z hz0 hzr
    refine h.congr_deriv ?_
    rw [hV2eq]
    simp only [c]
    ring
  obtain ⟨Y4, hY4diff, hY4eq⟩ :=
    linear_ode_extend (a := c) (b := fun z => 2 * c z * Y2 z) (V := V4) (r := r)
      hr0 hr1 hc hb2 hV4d hV4ode'
  -- ## 8. the holomorphic function `E` and its two properties
  let E : ℂ → ℂ := fun z => K z * Y4 z
  have hEd : DifferentiableOn ℂ E (Metric.ball (0:ℂ) 1) := by
    have h : DifferentiableOn ℂ (fun z : ℂ => K z * Y4 z) (Metric.ball (0:ℂ) 1) :=
      hKdiff.mul hY4diff
    exact h
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
    show K z * Y4 z = K (-z) * Y4 (-z)
    rw [hY4eq hz, hY4eq hzn]
    simp only [V4]
    rw [mul_div_cancel₀ _ (hKr z hz), mul_div_cancel₀ _ (hKr (-z) hzn)]
    simp only [u4]
    rw [hyneg]
  have heven : ∀ z ∈ Metric.ball (0:ℂ) 1, E (-z) = E z := by
    have hneg : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      simpa using hz
    have h2 : DifferentiableOn ℂ (fun z => E (-z)) (Metric.ball (0:ℂ) 1) :=
      hEd.comp differentiable_neg.differentiableOn hneg
    have heq : Set.EqOn E (fun z => E (-z)) (Metric.ball (0:ℂ) 1) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        (hEd.analyticOnNhd Metric.isOpen_ball) (h2.analyticOnNhd Metric.isOpen_ball)
        (convex_ball (0:ℂ) 1).isPreconnected (by simp [Metric.mem_ball]) hevenEv
    intro z hz
    exact (heq hz).symm
  have hgerm : ∀ᶠ z in 𝓝 (0:ℂ), HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ) *
        Submission.CDTPlan.phiC (z ^ 2) ^ n) (E z) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr0] with z hz
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := Metric.ball_subset_ball (le_of_lt hr1) hz
    have hyzmem : y z ∈ Metric.ball (0:ℂ) 1 := hymem z hz
    have hEz : E z = evp Submission.CDTPlan.B4 (y z) := by
      show K z * Y4 z = evp Submission.CDTPlan.B4 (y z)
      rw [hY4eq hz]
      simp only [V4]
      exact mul_div_cancel₀ _ (hKr z hz)
    rw [hEz, ← hyphi z hz1]
    exact hU4sum (y z) hyzmem
  exact pullbackMero_of_even' hEd heven hgerm

end Work.CPull
