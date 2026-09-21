import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.Geometry.Ulam.odd_radial_reconstruction
import Submission.Work.OddRadon.radial_first_deriv_bound
import Submission.Work.OddRadon.radial_second_deriv_bound

/-!
# The radial pair with `C²` bounds (`Work.OddRadon`)

For every `n ≥ 1` there is `ε > 0` such that every perturbation `(A, B)` of the ball's data
which is `C^∞` on `[0, π/2]`, whose values and whose first two derivatives are bounded by `ε`,
and which satisfies the paper's endpoint conditions (`A(π/2) = B(π/2) = 0`,
`A'(0) = B'(0) = 0`), admits `C^∞` radial functions `R, r` on `[0, π/2]` solving
`RadialSystem n ((2+A)cos²) (B cos)` with `R(π/2) = r(π/2) = 1` and

`|R α - 1| < 1/8`, `|r α - 1| < 1/8`, `|R' α| < 1/8`, `|r' α| < 1/8`,
`|R'' α| < 1/8`, `|r'' α| < 1/8`

for every `α ∈ [0, π/2]`.

The construction is the local inverse function theorem for the two-power map
`(R,r) ↦ (R^{2n+2}+r^{2n+2}, R^{2n+1}-r^{2n+1})`, exactly as in
`Commons.Geometry.Ulam.spherical_radon_radial_reconstruction`, with two additions:

* the radial functions are composed with the clamp `clampPi` to `[0, π/2]`, so that they are
  *constant* on `(-∞, 0]` and on `[π/2, ∞)`.  Consequently `deriv R` and `deriv (deriv R)`
  (and similarly for `r`) vanish at the two endpoints whenever they exist at all -- the
  two-sided derivative at an endpoint of a function which is locally constant on one side is
  forced to be `0`.  This removes the endpoint bookkeeping from the `C²` estimates;
* the derivative bounds are read off from the algebraic system by implicit differentiation:
  the pair `(R', r')` and the pair `(R'', r'')` solve explicit linear systems whose
  coefficient matrix has determinant bounded below on `[7/8, 9/8]²`.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped RealInnerProductSpace Pointwise Interval Topology ContDiff

namespace Work.OddRadon

/-! ## The clamp to `[0, π/2]` -/

/-- Clamp a real number to the interval `[0, π/2]`. -/
def clampPi (x : ℝ) : ℝ := min (Real.pi / 2) (max 0 x)

lemma clampPi_of_mem {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 2)) : clampPi x = x := by
  rw [clampPi, max_eq_right hx.1, min_eq_right hx.2]

lemma clampPi_of_nonpos {x : ℝ} (hx : x ≤ 0) : clampPi x = 0 := by
  rw [clampPi, max_eq_left hx,
    min_eq_right (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

lemma clampPi_of_ge {x : ℝ} (hx : Real.pi / 2 ≤ x) : clampPi x = Real.pi / 2 := by
  rw [clampPi, max_eq_right (by linarith [Real.pi_pos] : (0 : ℝ) ≤ x), min_eq_left hx]

lemma clampPi_nonneg (x : ℝ) : 0 ≤ clampPi x :=
  le_min (by linarith [Real.pi_pos]) (le_max_left _ _)

lemma clampPi_le (x : ℝ) : clampPi x ≤ Real.pi / 2 := min_le_left _ _

/-! ## Functions constant on one side of a point have vanishing derivative there -/

lemma deriv_eq_zero_of_eventuallyEq_left {f : ℝ → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝[<] x, f y = f x) : deriv f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hle : 𝓝[<] x ≤ 𝓝[≠] x :=
      nhdsWithin_mono x (fun y hy => by simpa using ne_of_lt hy)
    have h1 : Tendsto (slope f x) (𝓝[<] x) (𝓝 (deriv f x)) :=
      hd.hasDerivAt.tendsto_slope.mono_left hle
    have h2 : Tendsto (slope f x) (𝓝[<] x) (𝓝 0) :=
      Tendsto.congr' (by
        filter_upwards [h] with y hy
        rw [slope_def_field, hy, sub_self, zero_div]) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · exact deriv_zero_of_not_differentiableAt hd

lemma deriv_eq_zero_of_eventuallyEq_right {f : ℝ → ℝ} {x : ℝ}
    (h : ∀ᶠ y in 𝓝[>] x, f y = f x) : deriv f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hle : 𝓝[>] x ≤ 𝓝[≠] x :=
      nhdsWithin_mono x (fun y hy => by simpa using ne_of_gt hy)
    have h1 : Tendsto (slope f x) (𝓝[>] x) (𝓝 (deriv f x)) :=
      hd.hasDerivAt.tendsto_slope.mono_left hle
    have h2 : Tendsto (slope f x) (𝓝[>] x) (𝓝 0) :=
      Tendsto.congr' (by
        filter_upwards [h] with y hy
        rw [slope_def_field, hy, sub_self, zero_div]) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## Derivatives of a clamped function at the two endpoints -/

lemma deriv_comp_clampPi_eq_zero {G : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    deriv (fun t => G (clampPi t)) x = 0 := by
  refine deriv_eq_zero_of_eventuallyEq_left ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  show G (clampPi y) = G (clampPi x)
  rw [clampPi_of_nonpos (le_trans (le_of_lt hy) hx), clampPi_of_nonpos hx]

lemma deriv_comp_clampPi_eq_zero' {G : ℝ → ℝ} {x : ℝ} (hx : Real.pi / 2 ≤ x) :
    deriv (fun t => G (clampPi t)) x = 0 := by
  refine deriv_eq_zero_of_eventuallyEq_right ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  show G (clampPi y) = G (clampPi x)
  rw [clampPi_of_ge (le_trans hx (le_of_lt hy)), clampPi_of_ge hx]

lemma deriv_deriv_comp_clampPi_eq_zero {G : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    deriv (deriv (fun t => G (clampPi t))) x = 0 := by
  have hx0 : deriv (fun t => G (clampPi t)) x = 0 := deriv_comp_clampPi_eq_zero hx
  refine deriv_eq_zero_of_eventuallyEq_left ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [deriv_comp_clampPi_eq_zero (le_trans (le_of_lt hy) hx), hx0]

lemma deriv_deriv_comp_clampPi_eq_zero' {G : ℝ → ℝ} {x : ℝ} (hx : Real.pi / 2 ≤ x) :
    deriv (deriv (fun t => G (clampPi t))) x = 0 := by
  have hx0 : deriv (fun t => G (clampPi t)) x = 0 := deriv_comp_clampPi_eq_zero' hx
  refine deriv_eq_zero_of_eventuallyEq_right ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [deriv_comp_clampPi_eq_zero' (le_trans hx (le_of_lt hy)), hx0]

/-! ## The local inverse, with a `1/8` closeness radius -/

lemma exists_radialLocalInv_close_eighth (n : ℕ) :
    ∃ δ > 0, ∀ y : ℝ × ℝ,
      dist y (Commons.Geometry.Ulam.radialMap n (1, 1)) < δ →
      dist (Commons.Geometry.Ulam.radialLocalInv n y) (1, 1) < 1 / 8 := by
  have hcont : ContinuousAt (Commons.Geometry.Ulam.radialLocalInv n)
      (Commons.Geometry.Ulam.radialMap n (1, 1)) :=
    (Commons.Geometry.Ulam.radialLocalInv_smooth n).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (1 / 8) (by norm_num)
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have h := hδ hy
  rwa [Commons.Geometry.Ulam.radialLocalInv_apply_image n] at h

/-- A `C^∞` function has a differentiable derivative. -/
lemma contDiffAt_deriv_differentiableAt {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) f x) : DifferentiableAt ℝ (deriv f) x :=
  (h.derivWithin (m := 1) (by
    rw [show (1 : WithTop ℕ∞) + 1 = ((1 + 1 : ℕ) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)

theorem radialSystem_exists_C2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε > 0, ∀ A B : ℝ → ℝ,
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Icc 0 (Real.pi / 2)) →
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |B α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv B α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv A) α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv (deriv B) α| < ε) →
      A (Real.pi / 2) = 0 → B (Real.pi / 2) = 0 →
      deriv A 0 = 0 → deriv B 0 = 0 →
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r (Set.Icc 0 (Real.pi / 2)) ∧
        RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
          (fun α => B α * Real.cos α) R r ∧
        R (Real.pi / 2) = 1 ∧ r (Real.pi / 2) = 1 ∧
        (∀ α ∈ Set.Icc 0 (Real.pi / 2),
          |R α - 1| < 1 / 8 ∧ |r α - 1| < 1 / 8 ∧
          |deriv R α| < 1 / 8 ∧ |deriv r α| < 1 / 8 ∧
          |deriv (deriv R) α| < 1 / 8 ∧ |deriv (deriv r) α| < 1 / 8) := by
  have hpi2le : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- the local inverse-function-theorem data at the ball's solution `(1,1)`
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Commons.Geometry.Ulam.exists_radialLocalInv_right_inv_ball n
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_radialLocalInv_close_eighth n
  obtain ⟨u, hu_mem, hu_cont, hu_maps⟩ :=
    Commons.Geometry.Ulam.exists_radialLocalInv_contDiffOn_close n
  obtain ⟨δu, hδupos, hδu⟩ := Metric.mem_nhds_iff.mp hu_mem
  -- the two linear-algebra estimates from the algebraic system
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := radial_first_deriv_bound n hn
  obtain ⟨C₂, hC₂pos, hC₂b⟩ := radial_second_deriv_bound n hn C₁ hC₁pos.le
  set K : ℝ := C₁ + C₂ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hC₁leK : C₁ ≤ K := by rw [hKdef]; linarith [hC₂pos.le]
  have hC₂leK : C₂ ≤ K := by rw [hKdef]; linarith [hC₁pos.le]
  set δ : ℝ := min δ₁ (min δ₂ δu) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδ₁pos (lt_min hδ₂pos hδupos)
  have hδle₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleu : δ ≤ δu := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set ε : ℝ := min δ (1 / (16 * K)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hδpos (by positivity)
  have hεleδ : ε ≤ δ := by rw [hεdef]; exact min_le_left _ _
  have hεsmall : ε ≤ 1 / (16 * K) := by rw [hεdef]; exact min_le_right _ _
  have hεle1 : ε ≤ 1 := by
    have h16 : (1 : ℝ) ≤ 16 * K := by linarith [hKpos]
    calc ε ≤ 1 / (16 * K) := hεsmall
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact h16
  have hC₁ε : C₁ * ε ≤ 1 / 16 := by
    have hmul : ε * (16 * K) ≤ 1 := (le_div_iff₀ (by positivity)).mp hεsmall
    nlinarith [hmul, hεpos.le, hC₁leK]
  have hC₂ε : C₂ * ε ≤ 1 / 16 := by
    have hmul : ε * (16 * K) ≤ 1 := (le_div_iff₀ (by positivity)).mp hεsmall
    nlinarith [hmul, hεpos.le, hC₂leK]
  refine ⟨ε, hεpos, ?_⟩
  intro A B hA hB hAsm hBsm hAd1 hBd1 hAd2 hBd2 hAend hBend hA0 hB0
  -- the perturbed data
  set y : ℝ → ℝ × ℝ := fun α => (2 + A α, B α) with hydef
  set R₀ : ℝ → ℝ := fun α => (Commons.Geometry.Ulam.radialLocalInv n (y α)).1 with hR₀def
  set r₀ : ℝ → ℝ := fun α => (Commons.Geometry.Ulam.radialLocalInv n (y α)).2 with hr₀def
  set R : ℝ → ℝ := fun α => R₀ (clampPi α) with hRdef
  set r : ℝ → ℝ := fun α => r₀ (clampPi α) with hrdef
  have hmap0 : Commons.Geometry.Ulam.radialMap n (1, 1) = ((2 : ℝ), (0 : ℝ)) := by
    simp only [Commons.Geometry.Ulam.radialMap, one_pow]
    norm_num
  have hy_dist (α : ℝ) : dist (y α) (Commons.Geometry.Ulam.radialMap n (1, 1)) =
      max |A α| |B α| := by
    rw [hydef, hmap0, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    congr 1
    · rw [show 2 + A α - 2 = A α by ring]
    · rw [sub_zero]
  have hy_ball : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      dist (y α) (Commons.Geometry.Ulam.radialMap n (1, 1)) < δ := by
    intro α hα
    rw [hy_dist α]
    exact lt_of_lt_of_le (max_lt (hAsm α hα) (hBsm α hα)) hεleδ
  have hy_cont : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Icc 0 (Real.pi / 2)) := by
    rw [hydef]
    exact (contDiffOn_const (c := (2 : ℝ))).add hA |>.prodMk hB
  have hy_maps : Set.MapsTo y (Set.Icc 0 (Real.pi / 2)) u := fun α hα =>
    hδu (lt_of_lt_of_le (hy_ball α hα) hδleu)
  have hcomp_cont : ContDiffOn ℝ (⊤ : ℕ∞)
      (Commons.Geometry.Ulam.radialLocalInv n ∘ y) (Set.Icc 0 (Real.pi / 2)) :=
    hu_cont.comp hy_cont hy_maps
  have hR₀_cont : ContDiffOn ℝ (⊤ : ℕ∞) R₀ (Set.Icc 0 (Real.pi / 2)) := by
    simpa [hR₀def, Function.comp_def] using hcomp_cont.fst
  have hr₀_cont : ContDiffOn ℝ (⊤ : ℕ∞) r₀ (Set.Icc 0 (Real.pi / 2)) := by
    simpa [hr₀def, Function.comp_def] using hcomp_cont.snd
  have hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)) :=
    hR₀_cont.congr (fun α hα => by
      show R₀ (clampPi α) = R₀ α
      rw [clampPi_of_mem hα])
  have hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)) :=
    hr₀_cont.congr (fun α hα => by
      show r₀ (clampPi α) = r₀ α
      rw [clampPi_of_mem hα])
  -- the algebraic system, first for the unclamped pair
  have hsys₀ : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      R₀ α ^ (2 * n + 2) + r₀ α ^ (2 * n + 2) = 2 + A α ∧
      R₀ α ^ (2 * n + 1) - r₀ α ^ (2 * n + 1) = B α := by
    intro α hα
    have hb : dist (y α) (Commons.Geometry.Ulam.radialMap n (1, 1)) < δ₁ :=
      lt_of_lt_of_le (hy_ball α hα) hδle₁
    have h := hδ₁ (y α) hb
    constructor
    · have h1 := congrArg Prod.fst h
      simp only [Commons.Geometry.Ulam.radialMap] at h1
      rw [hR₀def, hr₀def]
      simpa [hydef] using h1
    · have h2 := congrArg Prod.snd h
      simp only [Commons.Geometry.Ulam.radialMap] at h2
      rw [hR₀def, hr₀def]
      simpa [hydef] using h2
  have hsys : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      R α ^ (2 * n + 2) + r α ^ (2 * n + 2) = 2 + A α ∧
      R α ^ (2 * n + 1) - r α ^ (2 * n + 1) = B α := by
    intro α hα
    obtain ⟨h1, h2⟩ := hsys₀ α hα
    constructor
    · show R₀ (clampPi α) ^ (2 * n + 2) + r₀ (clampPi α) ^ (2 * n + 2) = 2 + A α
      rw [clampPi_of_mem hα]
      exact h1
    · show R₀ (clampPi α) ^ (2 * n + 1) - r₀ (clampPi α) ^ (2 * n + 1) = B α
      rw [clampPi_of_mem hα]
      exact h2
  -- `C⁰` closeness
  have hval : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| < 1 / 8 ∧ |r α - 1| < 1 / 8 := by
    intro α hα
    have hb : dist (Commons.Geometry.Ulam.radialLocalInv n (y α)) (1, 1) < 1 / 8 :=
      hδ₂ (y α) (lt_of_lt_of_le (hy_ball α hα) hδle₂)
    rw [Prod.dist_eq] at hb
    have h1 : |R₀ α - 1| < 1 / 8 := by
      have hthis : dist (Commons.Geometry.Ulam.radialLocalInv n (y α)).1 (1 : ℝ) < 1 / 8 :=
        lt_of_le_of_lt (le_max_left _ _) hb
      rwa [hR₀def, ← Real.dist_eq]
    have h2 : |r₀ α - 1| < 1 / 8 := by
      have hthis : dist (Commons.Geometry.Ulam.radialLocalInv n (y α)).2 (1 : ℝ) < 1 / 8 :=
        lt_of_le_of_lt (le_max_right _ _) hb
      rwa [hr₀def, ← Real.dist_eq]
    constructor
    · show |R₀ (clampPi α) - 1| < 1 / 8
      rw [clampPi_of_mem hα]; exact h1
    · show |r₀ (clampPi α) - 1| < 1 / 8
      rw [clampPi_of_mem hα]; exact h2
  -- endpoint values
  have hyend : y (Real.pi / 2) = ((2 : ℝ), (0 : ℝ)) := by
    rw [hydef]
    simp [hAend, hBend]
  have hR_end : R (Real.pi / 2) = 1 := by
    show R₀ (clampPi (Real.pi / 2)) = 1
    rw [clampPi_of_mem ⟨hpi2le, le_refl _⟩]
    show (Commons.Geometry.Ulam.radialLocalInv n (y (Real.pi / 2))).1 = 1
    rw [hyend, ← hmap0, Commons.Geometry.Ulam.radialLocalInv_apply_image n]
  have hr_end : r (Real.pi / 2) = 1 := by
    show r₀ (clampPi (Real.pi / 2)) = 1
    rw [clampPi_of_mem ⟨hpi2le, le_refl _⟩]
    show (Commons.Geometry.Ulam.radialLocalInv n (y (Real.pi / 2))).2 = 1
    rw [hyend, ← hmap0, Commons.Geometry.Ulam.radialLocalInv_apply_image n]
  -- the radial system in cleared form
  have hRadial : RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
      (fun α => B α * Real.cos α) R r := by
    intro α hα
    obtain ⟨h1, h2⟩ := hsys α hα
    exact ⟨by rw [h1], by rw [h2]⟩
  -- ## The algebraic system differentiated once, on the interior
  have hfirst : ∀ α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv R α
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv r α = deriv A α ∧
      ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α
        - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α = deriv B α := by
    intro α hα
    have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 α := Icc_mem_nhds hα.1 hα.2
    have hRd : DifferentiableAt ℝ R α :=
      (hR_cont.contDiffAt hmem).differentiableAt (by simp)
    have hrd : DifferentiableAt ℝ r α :=
      (hr_cont.contDiffAt hmem).differentiableAt (by simp)
    have hev1 : (fun β => R β ^ (2 * n + 2) + r β ^ (2 * n + 2)) =ᶠ[𝓝 α]
        (fun β => 2 + A β) := by
      filter_upwards [hmem] with β hβ
      exact (hsys β hβ).1
    have hd1 : deriv (fun β => R β ^ (2 * n + 2) + r β ^ (2 * n + 2)) α
        = deriv (fun β => 2 + A β) α := hev1.deriv.eq_of_nhds
    have hlhs1 : deriv (fun β => R β ^ (2 * n + 2) + r β ^ (2 * n + 2)) α
        = ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv R α
          + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv r α := by
      change deriv (R ^ (2 * n + 2) + r ^ (2 * n + 2)) α
        = ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv R α
          + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv r α
      rw [deriv_add (hRd.pow _) (hrd.pow _), deriv_pow hRd (2 * n + 2),
        deriv_pow hrd (2 * n + 2)]
      have he : (2 * n + 2 : ℕ) - 1 = 2 * n + 1 := by omega
      rw [he]
    have hev2 : (fun β => R β ^ (2 * n + 1) - r β ^ (2 * n + 1)) =ᶠ[𝓝 α]
        (fun β => B β) := by
      filter_upwards [hmem] with β hβ
      exact (hsys β hβ).2
    have hd2 : deriv (fun β => R β ^ (2 * n + 1) - r β ^ (2 * n + 1)) α = deriv B α :=
      hev2.deriv.eq_of_nhds
    have hlhs2 : deriv (fun β => R β ^ (2 * n + 1) - r β ^ (2 * n + 1)) α
        = ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α
          - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α := by
      change deriv (R ^ (2 * n + 1) - r ^ (2 * n + 1)) α
        = ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α
          - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α
      rw [deriv_sub (hRd.pow _) (hrd.pow _), deriv_pow hRd (2 * n + 1),
        deriv_pow hrd (2 * n + 1)]
      have he : (2 * n + 1 : ℕ) - 1 = 2 * n := by omega
      rw [he]
    exact ⟨by rw [← hlhs1, hd1, deriv_const_add], by rw [← hlhs2, hd2]⟩
  -- ## The same system differentiated twice, on the interior
  have hsecond : ∀ α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((2 * n + 2 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α * deriv R α
            + R α ^ (2 * n + 1) * deriv (deriv R) α)
        + ((2 * n + 2 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α * deriv r α
            + r α ^ (2 * n + 1) * deriv (deriv r) α) = deriv (deriv A) α ∧
      ((2 * n + 1 : ℕ) : ℝ) *
          (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α * deriv R α
            + R α ^ (2 * n) * deriv (deriv R) α)
        - ((2 * n + 1 : ℕ) : ℝ) *
          (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α * deriv r α
            + r α ^ (2 * n) * deriv (deriv r) α) = deriv (deriv B) α := by
    intro α hα
    have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 α := Icc_mem_nhds hα.1 hα.2
    have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 α := isOpen_Ioo.mem_nhds hα
    have hRcd : ContDiffAt ℝ (⊤ : ℕ∞) R α := hR_cont.contDiffAt hmem
    have hrcd : ContDiffAt ℝ (⊤ : ℕ∞) r α := hr_cont.contDiffAt hmem
    have hRd : DifferentiableAt ℝ R α := hRcd.differentiableAt (by simp)
    have hrd : DifferentiableAt ℝ r α := hrcd.differentiableAt (by simp)
    have hRd2 : DifferentiableAt ℝ (deriv R) α := contDiffAt_deriv_differentiableAt hRcd
    have hrd2 : DifferentiableAt ℝ (deriv r) α := contDiffAt_deriv_differentiableAt hrcd
    have hpowR : HasDerivAt (fun β => R β ^ (2 * n + 1))
        (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α) α := by
      have h := hRd.hasDerivAt.pow (2 * n + 1)
      have he : (2 * n + 1 : ℕ) - 1 = 2 * n := by omega
      rw [he] at h
      exact h
    have hpowr : HasDerivAt (fun β => r β ^ (2 * n + 1))
        (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α) α := by
      have h := hrd.hasDerivAt.pow (2 * n + 1)
      have he : (2 * n + 1 : ℕ) - 1 = 2 * n := by omega
      rw [he] at h
      exact h
    have hpowR2 : HasDerivAt (fun β => R β ^ (2 * n))
        (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α) α :=
      hRd.hasDerivAt.pow (2 * n)
    have hpowr2 : HasDerivAt (fun β => r β ^ (2 * n))
        (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α) α :=
      hrd.hasDerivAt.pow (2 * n)
    have htermR : HasDerivAt
        ((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
        ((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α))
            * deriv R α
          + (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1)) * deriv (deriv R) α) α :=
      (hpowR.const_mul _).mul hRd2.hasDerivAt
    have htermr : HasDerivAt
        ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r)
        ((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α))
            * deriv r α
          + (((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)) * deriv (deriv r) α) α :=
      (hpowr.const_mul _).mul hrd2.hasDerivAt
    have htermR2 : HasDerivAt
        ((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
        ((((2 * n + 1 : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α))
            * deriv R α
          + (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)) * deriv (deriv R) α) α :=
      (hpowR2.const_mul _).mul hRd2.hasDerivAt
    have htermr2 : HasDerivAt
        ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r)
        ((((2 * n + 1 : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α))
            * deriv r α
          + (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)) * deriv (deriv r) α) α :=
      (hpowr2.const_mul _).mul hrd2.hasDerivAt
    constructor
    · -- the first equation, differentiated twice
      have hF := htermR.add htermr
      have hev : (((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
            + ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r))
          =ᶠ[𝓝 α] deriv A := by
        filter_upwards [hIoo] with β hβ
        exact (hfirst β hβ).1
      have hdF : deriv ((((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
            + ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r))) α
          = deriv (deriv A) α := hev.deriv.eq_of_nhds
      have hraw := hF.deriv
      have hring : ((((2 * n + 2 : ℕ) : ℝ) *
                (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α)) * deriv R α
              + (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1)) * deriv (deriv R) α)
            + ((((2 * n + 2 : ℕ) : ℝ) *
                (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α)) * deriv r α
              + (((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)) * deriv (deriv r) α)
          = ((2 * n + 2 : ℕ) : ℝ) *
                (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α * deriv R α
                  + R α ^ (2 * n + 1) * deriv (deriv R) α)
              + ((2 * n + 2 : ℕ) : ℝ) *
                (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α * deriv r α
                  + r α ^ (2 * n + 1) * deriv (deriv r) α) := by
        ring
      exact hring.symm.trans (hraw.symm.trans hdF)
    · -- the second equation, differentiated twice
      have hG := htermR2.sub htermr2
      have hev : (((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
            - ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r))
          =ᶠ[𝓝 α] deriv B := by
        filter_upwards [hIoo] with β hβ
        exact (hfirst β hβ).2
      have hdG : deriv ((((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
            - ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r))) α
          = deriv (deriv B) α := hev.deriv.eq_of_nhds
      have hraw := hG.deriv
      have hring : ((((2 * n + 1 : ℕ) : ℝ) *
                (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α)) * deriv R α
              + (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)) * deriv (deriv R) α)
            - ((((2 * n + 1 : ℕ) : ℝ) *
                (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α)) * deriv r α
              + (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)) * deriv (deriv r) α)
          = ((2 * n + 1 : ℕ) : ℝ) *
                (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α * deriv R α
                  + R α ^ (2 * n) * deriv (deriv R) α)
              - ((2 * n + 1 : ℕ) : ℝ) *
                (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α * deriv r α
                  + r α ^ (2 * n) * deriv (deriv r) α) := by
        ring
      exact hring.symm.trans (hraw.symm.trans hdG)
  -- ## The bounds on the derivatives on the interior
  have hbound : ∀ α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv R α| ≤ C₁ * ε ∧ |deriv r α| ≤ C₁ * ε ∧
      |deriv (deriv R) α| ≤ C₂ * ε ∧ |deriv (deriv r) α| ≤ C₂ * ε := by
    intro α hα
    have hαI : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
    obtain ⟨hf1, hf2⟩ := hfirst α hα
    obtain ⟨hg1, hg2⟩ := hsecond α hα
    obtain ⟨hv1, hv2⟩ := hval α hαI
    have hRlo : (7 : ℝ) / 8 ≤ R α := by have := (abs_lt.mp hv1).1; linarith
    have hRhi : R α ≤ 9 / 8 := by have := (abs_lt.mp hv1).2; linarith
    have hrlo : (7 : ℝ) / 8 ≤ r α := by have := (abs_lt.mp hv2).1; linarith
    have hrhi : r α ≤ 9 / 8 := by have := (abs_lt.mp hv2).2; linarith
    have hA' : |deriv A α| < ε := hAd1 α hαI
    have hB' : |deriv B α| < ε := hBd1 α hαI
    have hA'' : |deriv (deriv A) α| < ε := hAd2 α hαI
    have hB'' : |deriv (deriv B) α| < ε := hBd2 α hαI
    have hB'neg : |-(deriv B α)| < ε := by rwa [abs_neg]
    have hB''neg : |-(deriv (deriv B) α)| < ε := by rwa [abs_neg]
    have hcombR : (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) *
          (R α ^ (2 * n + 1) * r α ^ (2 * n) + R α ^ (2 * n) * r α ^ (2 * n + 1)))
            * deriv R α
        = ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv A α
          + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv B α := by
      linear_combination (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)) * hf1
        + (((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)) * hf2
    have hcombr : (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) *
          (r α ^ (2 * n + 1) * R α ^ (2 * n) + r α ^ (2 * n) * R α ^ (2 * n + 1)))
            * deriv r α
        = ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv A α
          + ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * (-(deriv B α)) := by
      linear_combination (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)) * hf1
        - (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1)) * hf2
    have hbR : |deriv R α| ≤ C₁ * ε := hC₁b hRlo hRhi hrlo hrhi hA' hB' hcombR
    have hbr : |deriv r α| ≤ C₁ * ε := hC₁b hrlo hrhi hRlo hRhi hA' hB'neg hcombr
    have hcombR2 : (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) *
          (R α ^ (2 * n + 1) * r α ^ (2 * n) + R α ^ (2 * n) * r α ^ (2 * n + 1)))
            * deriv (deriv R) α
        = ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) *
            (deriv (deriv A) α -
              (((2 * n + 2 : ℕ) : ℝ) *
                  (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α * deriv R α)
                + ((2 * n + 2 : ℕ) : ℝ) *
                  (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α * deriv r α)))
          + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) *
            (deriv (deriv B) α -
              (((2 * n + 1 : ℕ) : ℝ) *
                  (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α * deriv R α)
                - ((2 * n + 1 : ℕ) : ℝ) *
                  (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α * deriv r α))) := by
      linear_combination (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)) * hg1
        + (((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)) * hg2
    have hcombR2' : (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) *
          (r α ^ (2 * n + 1) * R α ^ (2 * n) + r α ^ (2 * n) * R α ^ (2 * n + 1)))
            * deriv (deriv r) α
        = ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) *
            (deriv (deriv A) α -
              (((2 * n + 2 : ℕ) : ℝ) *
                  (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv r α * deriv r α)
                + ((2 * n + 2 : ℕ) : ℝ) *
                  (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv R α * deriv R α)))
          + ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) *
            (-(deriv (deriv B) α) -
              (((2 * n + 1 : ℕ) : ℝ) *
                  (((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * deriv r α * deriv r α)
                - ((2 * n + 1 : ℕ) : ℝ) *
                  (((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * deriv R α * deriv R α))) := by
      linear_combination (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)) * hg1
        - (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1)) * hg2
    have hbR2 : |deriv (deriv R) α| ≤ C₂ * ε :=
      hC₂b hRlo hRhi hrlo hrhi hεpos.le hεle1 hbR hbr hA'' hB'' hcombR2
    have hbr2 : |deriv (deriv r) α| ≤ C₂ * ε :=
      hC₂b hrlo hrhi hRlo hRhi hεpos.le hεle1 hbr hbR hA'' hB''neg hcombR2'
    exact ⟨hbR, hbr, hbR2, hbr2⟩
  refine ⟨R, r, hR_cont, hr_cont, hRadial, hR_end, hr_end, ?_⟩
  intro α hα
  obtain ⟨hv1, hv2⟩ := hval α hα
  have hdR0 : deriv R 0 = 0 := by
    show deriv (fun t => R₀ (clampPi t)) 0 = 0
    exact deriv_comp_clampPi_eq_zero le_rfl
  have hdRπ : deriv R (Real.pi / 2) = 0 := by
    show deriv (fun t => R₀ (clampPi t)) (Real.pi / 2) = 0
    exact deriv_comp_clampPi_eq_zero' le_rfl
  have hdr0 : deriv r 0 = 0 := by
    show deriv (fun t => r₀ (clampPi t)) 0 = 0
    exact deriv_comp_clampPi_eq_zero le_rfl
  have hdrπ : deriv r (Real.pi / 2) = 0 := by
    show deriv (fun t => r₀ (clampPi t)) (Real.pi / 2) = 0
    exact deriv_comp_clampPi_eq_zero' le_rfl
  have hddR0 : deriv (deriv R) 0 = 0 := by
    show deriv (deriv (fun t => R₀ (clampPi t))) 0 = 0
    exact deriv_deriv_comp_clampPi_eq_zero le_rfl
  have hddRπ : deriv (deriv R) (Real.pi / 2) = 0 := by
    show deriv (deriv (fun t => R₀ (clampPi t))) (Real.pi / 2) = 0
    exact deriv_deriv_comp_clampPi_eq_zero' le_rfl
  have hddr0 : deriv (deriv r) 0 = 0 := by
    show deriv (deriv (fun t => r₀ (clampPi t))) 0 = 0
    exact deriv_deriv_comp_clampPi_eq_zero le_rfl
  have hddrπ : deriv (deriv r) (Real.pi / 2) = 0 := by
    show deriv (deriv (fun t => r₀ (clampPi t))) (Real.pi / 2) = 0
    exact deriv_deriv_comp_clampPi_eq_zero' le_rfl
  have key : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv R x| < 1 / 8 ∧ |deriv r x| < 1 / 8 ∧
      |deriv (deriv R) x| < 1 / 8 ∧ |deriv (deriv r) x| < 1 / 8 := by
    intro x hx
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · exact absurd hx.1 (not_le.mpr hlt)
    · subst heq
      exact ⟨by rw [hdR0]; norm_num, by rw [hdr0]; norm_num,
        by rw [hddR0]; norm_num, by rw [hddr0]; norm_num⟩
    · rcases lt_trichotomy x (Real.pi / 2) with hlt2 | heq2 | hgt2
      · have hb := hbound x ⟨hgt, hlt2⟩
        exact ⟨by linarith [hb.1, hC₁ε], by linarith [hb.2.1, hC₁ε],
          by linarith [hb.2.2.1, hC₂ε], by linarith [hb.2.2.2, hC₂ε]⟩
      · subst heq2
        exact ⟨by rw [hdRπ]; norm_num, by rw [hdrπ]; norm_num,
          by rw [hddRπ]; norm_num, by rw [hddrπ]; norm_num⟩
      · exact absurd hx.2 (not_le.mpr hgt2)
  obtain ⟨k1, k2, k3, k4⟩ := key α hα
  exact ⟨hv1, hv2, k1, k2, k3, k4⟩

end Work.OddRadon
