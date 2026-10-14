import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Derivative facts for the shrinking angular cut-off `angCut n`

This file proves `Work.FTS.StrongEps.EComparison.AngCutDerivFacts`: the first two derivatives
of `Real.smoothTransition` vanish on `(-∞, 0]` and on `[1, ∞)`, and the two factors
`Ψ(θ/δ - 1)`, `Ψ((π/2 - θ)/δ - 1)` of the cut-off `angCut n = χ_n` (with `δ = delta n`)
give the uniform bounds

  `|(χ_n)'| ≤ K/δ`,   `|(χ_n)''| ≤ K/δ²`   (all `θ`)

together with the vanishing of both derivatives on the closed plateau `[2δ, π/2 - 2δ]`.

The two ends of the plateau need care: `χ_n` is *not* locally constant there (only the two
factors separately are), and the second derivative at the plateau ends is *not* killed by local
constancy but by `deriv² Ψ (1) = 0`, i.e. by conjuncts 3/4 of the theorem.  That is why the
plateau ends are handled with explicit chain-rule formulas rather than with
`Filter.EventuallyEq`.
-/

noncomputable section

open scoped Real Topology ContDiff
open Filter

namespace Work.FTS.StrongEps.EComparison

/-! ## Part 1: the first two derivatives of `Real.smoothTransition` off `(0, 1)`

The derivative of a `C^∞` function is continuous, so vanishing on the open half-lines
propagates to the closed half-lines by closure. -/

private lemma deriv_psi_eq_zero_of_lt {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma deriv_psi_eq_zero_of_gt {x : ℝ} (hx : 1 < x) : deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma continuous_deriv_psi : Continuous (deriv Real.smoothTransition) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hone : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact hψ.continuous_deriv hone

private lemma continuous_deriv2_psi : Continuous (deriv (deriv Real.smoothTransition)) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hone : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact hψ.deriv'.continuous_deriv hone

private lemma deriv_psi_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) : deriv Real.smoothTransition x = 0 := by
  have hS : IsClosed {y : ℝ | deriv Real.smoothTransition y = 0} :=
    isClosed_eq continuous_deriv_psi continuous_const
  have hleft : Set.Iic (0 : ℝ) ⊆ {y : ℝ | deriv Real.smoothTransition y = 0} := by
    rw [← closure_Iio (a := (0 : ℝ))]
    exact hS.closure_subset_iff.mpr (fun y hy => deriv_psi_eq_zero_of_lt hy)
  exact hleft hx

private lemma deriv_psi_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  have hS : IsClosed {y : ℝ | deriv Real.smoothTransition y = 0} :=
    isClosed_eq continuous_deriv_psi continuous_const
  have hright : Set.Ici (1 : ℝ) ⊆ {y : ℝ | deriv Real.smoothTransition y = 0} := by
    rw [← closure_Ioi (a := (1 : ℝ))]
    exact hS.closure_subset_iff.mpr (fun y hy => deriv_psi_eq_zero_of_gt hy)
  exact hright hx

/-! ## Part 2: uniform bounds for `deriv Ψ` and `deriv (deriv Ψ)`

Both are continuous with support in `[0, 1]`, so they are bounded by compactness plus the
vanishing off `[0, 1]`. -/

private lemma abs_smoothTransition_le_one (y : ℝ) : |Real.smoothTransition y| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg y)]
  exact Real.smoothTransition.le_one y

private lemma exists_bound_deriv_psi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous_deriv_psi.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h1 : ‖deriv Real.smoothTransition x‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [deriv_psi_eq_zero_of_lt h, abs_zero]; exact le_max_right _ _
    · rw [deriv_psi_eq_zero_of_gt h, abs_zero]; exact le_max_right _ _

private lemma exists_bound_deriv2_psi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous_deriv2_psi.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h1 : ‖deriv (deriv Real.smoothTransition) x‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [show deriv (deriv Real.smoothTransition) x = 0 from
          Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat x (Or.inl h.le),
        abs_zero]
      exact le_max_right _ _
    · rw [show deriv (deriv Real.smoothTransition) x = 0 from
          Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat x (Or.inr h.le),
        abs_zero]
      exact le_max_right _ _

/-! ## Part 3: the two factors of the cut-off and their derivatives

`cutFA a θ = Ψ(θ/a - 1)` is `0` for `θ ≤ a` and `1` for `θ ≥ 2a`;
`cutFB a θ = Ψ((π/2 - θ)/a - 1)` is `1` for `θ ≤ π/2 - 2a` and `0` for `θ ≥ π/2 - a`.
Each is a chain rule with an affine inner function, so both derivatives carry the factor `1/a`
and the second derivative the factor `1/a²`. -/

private noncomputable def cutFA (a : ℝ) : ℝ → ℝ := fun θ => Real.smoothTransition (θ / a - 1)

private noncomputable def cutFB (a : ℝ) : ℝ → ℝ :=
  fun θ => Real.smoothTransition ((Real.pi / 2 - θ) / a - 1)

private lemma hasDerivAt_cutFA (a θ : ℝ) :
    HasDerivAt (cutFA a) (deriv Real.smoothTransition (θ / a - 1) * (1 / a)) θ := by
  have h1 : HasDerivAt (fun s : ℝ => s / a - 1) (1 / a) θ := by
    simpa using ((hasDerivAt_id θ).div_const a).sub_const 1
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (θ / a - 1))
      (θ / a - 1) :=
    (by fun_prop : DifferentiableAt ℝ Real.smoothTransition (θ / a - 1)).hasDerivAt
  have h3 : HasDerivAt (fun s : ℝ => Real.smoothTransition (s / a - 1))
      (deriv Real.smoothTransition (θ / a - 1) * (1 / a)) θ := by
    simpa only [Function.comp_def] using h2.comp θ h1
  rw [show cutFA a = fun s : ℝ => Real.smoothTransition (s / a - 1) from rfl]
  exact h3

private lemma deriv_cutFA (a : ℝ) :
    deriv (cutFA a) = fun θ : ℝ => deriv Real.smoothTransition (θ / a - 1) * (1 / a) := by
  funext θ
  exact (hasDerivAt_cutFA a θ).deriv

private lemma deriv_cutFA_apply (a θ : ℝ) :
    deriv (cutFA a) θ = deriv Real.smoothTransition (θ / a - 1) * (1 / a) :=
  congrFun (deriv_cutFA a) θ

private lemma hasDerivAt_cutFB (a θ : ℝ) :
    HasDerivAt (cutFB a) (deriv Real.smoothTransition ((Real.pi / 2 - θ) / a - 1) * (-1 / a)) θ := by
  have hsub : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) θ := by
    have hraw : HasDerivAt ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ)) (0 - 1) θ :=
      (hasDerivAt_const (x := θ) (Real.pi / 2)).sub (hasDerivAt_id θ)
    convert hraw using 1
    · funext s; rfl
    · norm_num
  have h1 : HasDerivAt (fun s : ℝ => (Real.pi / 2 - s) / a - 1) (-1 / a) θ := by
    simpa using (hsub.div_const a).sub_const 1
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((Real.pi / 2 - θ) / a - 1)) ((Real.pi / 2 - θ) / a - 1) :=
    (by fun_prop : DifferentiableAt ℝ Real.smoothTransition ((Real.pi / 2 - θ) / a - 1)).hasDerivAt
  have h3 : HasDerivAt (fun s : ℝ => Real.smoothTransition ((Real.pi / 2 - s) / a - 1))
      (deriv Real.smoothTransition ((Real.pi / 2 - θ) / a - 1) * (-1 / a)) θ := by
    simpa only [Function.comp_def] using h2.comp θ h1
  rw [show cutFB a = fun s : ℝ => Real.smoothTransition ((Real.pi / 2 - s) / a - 1) from rfl]
  exact h3

private lemma deriv_cutFB (a : ℝ) :
    deriv (cutFB a) = fun θ : ℝ =>
      deriv Real.smoothTransition ((Real.pi / 2 - θ) / a - 1) * (-1 / a) := by
  funext θ
  exact (hasDerivAt_cutFB a θ).deriv

private lemma deriv_cutFB_apply (a θ : ℝ) :
    deriv (cutFB a) θ = deriv Real.smoothTransition ((Real.pi / 2 - θ) / a - 1) * (-1 / a) :=
  congrFun (deriv_cutFB a) θ

private lemma deriv2_cutFA (a : ℝ) :
    deriv (deriv (cutFA a))
      = fun θ : ℝ => (deriv (deriv Real.smoothTransition) (θ / a - 1) * (1 / a)) * (1 / a) := by
  rw [deriv_cutFA]
  funext θ
  have hmul : deriv (fun y : ℝ => deriv Real.smoothTransition (y / a - 1) * (1 / a)) θ
      = deriv (fun y : ℝ => deriv Real.smoothTransition (y / a - 1)) θ * (1 / a) :=
    deriv_mul_const (by fun_prop) (1 / a)
  have h4 : deriv (fun y : ℝ => deriv Real.smoothTransition (y / a - 1)) θ
      = deriv (deriv Real.smoothTransition) (θ / a - 1) * (1 / a) := by
    have h1 : HasDerivAt (fun s : ℝ => s / a - 1) (1 / a) θ := by
      simpa using ((hasDerivAt_id θ).div_const a).sub_const 1
    have h2 : HasDerivAt (deriv Real.smoothTransition)
        (deriv (deriv Real.smoothTransition) (θ / a - 1)) (θ / a - 1) :=
      (by fun_prop : DifferentiableAt ℝ (deriv Real.smoothTransition) (θ / a - 1)).hasDerivAt
    simpa only [Function.comp_def, mul_comm] using (h2.comp θ h1).deriv
  rw [hmul, h4]

private lemma deriv2_cutFB (a : ℝ) :
    deriv (deriv (cutFB a))
      = fun θ : ℝ =>
        (deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / a - 1) * (-1 / a)) * (-1 / a) := by
  rw [deriv_cutFB]
  funext θ
  have hmul : deriv (fun y : ℝ => deriv Real.smoothTransition ((Real.pi / 2 - y) / a - 1) * (-1 / a)) θ
      = deriv (fun y : ℝ => deriv Real.smoothTransition ((Real.pi / 2 - y) / a - 1)) θ * (-1 / a) :=
    deriv_mul_const (by fun_prop) (-1 / a)
  have h4 : deriv (fun y : ℝ => deriv Real.smoothTransition ((Real.pi / 2 - y) / a - 1)) θ
      = deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / a - 1) * (-1 / a) := by
    have hsub : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) θ := by
      have hraw : HasDerivAt ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ)) (0 - 1) θ :=
        (hasDerivAt_const (x := θ) (Real.pi / 2)).sub (hasDerivAt_id θ)
      convert hraw using 1
      · funext s; rfl
      · norm_num
    have h1 : HasDerivAt (fun s : ℝ => (Real.pi / 2 - s) / a - 1) (-1 / a) θ := by
      simpa using (hsub.div_const a).sub_const 1
    have h2 : HasDerivAt (deriv Real.smoothTransition)
        (deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / a - 1))
        ((Real.pi / 2 - θ) / a - 1) :=
      (by fun_prop : DifferentiableAt ℝ (deriv Real.smoothTransition)
        ((Real.pi / 2 - θ) / a - 1)).hasDerivAt
    simpa only [Function.comp_def, mul_comm] using (h2.comp θ h1).deriv
  rw [hmul, h4]

private lemma deriv2_cutFA_apply (a θ : ℝ) :
    deriv (deriv (cutFA a)) θ
      = (deriv (deriv Real.smoothTransition) (θ / a - 1) * (1 / a)) * (1 / a) :=
  congrFun (deriv2_cutFA a) θ

private lemma deriv2_cutFB_apply (a θ : ℝ) :
    deriv (deriv (cutFB a)) θ
      = (deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / a - 1) * (-1 / a)) * (-1 / a) :=
  congrFun (deriv2_cutFB a) θ

private lemma differentiable_cutFA (a : ℝ) : Differentiable ℝ (cutFA a) := by
  rw [show cutFA a = fun t : ℝ => Real.smoothTransition (t / a - 1) from rfl]; fun_prop

private lemma differentiable_cutFB (a : ℝ) : Differentiable ℝ (cutFB a) := by
  rw [show cutFB a = fun t : ℝ => Real.smoothTransition ((Real.pi / 2 - t) / a - 1) from rfl]
  fun_prop

private lemma differentiable_deriv_cutFA (a : ℝ) : Differentiable ℝ (deriv (cutFA a)) := by
  rw [deriv_cutFA]; fun_prop

private lemma differentiable_deriv_cutFB (a : ℝ) : Differentiable ℝ (deriv (cutFB a)) := by
  rw [deriv_cutFB]; fun_prop

/-! ## Part 4: the product rule for `angCut n = cutFA (delta n) · cutFB (delta n)` -/

private lemma deriv_cutProd (a : ℝ) :
    deriv ((cutFA a) * (cutFB a))
      = (deriv (cutFA a) * cutFB a) + (cutFA a * deriv (cutFB a)) := by
  funext θ
  rw [deriv_mul (differentiable_cutFA a).differentiableAt (differentiable_cutFB a).differentiableAt]
  simp only [Pi.add_apply, Pi.mul_apply]

private lemma deriv2_cutProd (a θ : ℝ) :
    deriv (deriv ((cutFA a) * (cutFB a))) θ
      = deriv (deriv (cutFA a)) θ * cutFB a θ + 2 * (deriv (cutFA a) θ * deriv (cutFB a) θ)
        + cutFA a θ * deriv (deriv (cutFB a)) θ := by
  rw [deriv_cutProd]
  have h1 : DifferentiableAt ℝ (deriv (cutFA a)) θ := (differentiable_deriv_cutFA a).differentiableAt
  have h2 : DifferentiableAt ℝ (cutFB a) θ := (differentiable_cutFB a).differentiableAt
  have h3 : DifferentiableAt ℝ (cutFA a) θ := (differentiable_cutFA a).differentiableAt
  have h4 : DifferentiableAt ℝ (deriv (cutFB a)) θ := (differentiable_deriv_cutFB a).differentiableAt
  rw [deriv_add (h1.mul h2) (h3.mul h4), deriv_mul h1 h2, deriv_mul h3 h4]
  ring

private lemma deriv_angCut_apply (n : ℕ) (θ : ℝ) :
    deriv (angCut n) θ
      = deriv (cutFA (delta n)) θ * cutFB (delta n) θ
        + cutFA (delta n) θ * deriv (cutFB (delta n)) θ := by
  rw [show angCut n = (cutFA (delta n)) * (cutFB (delta n)) from rfl]
  rw [deriv_mul (differentiable_cutFA (delta n)).differentiableAt
    (differentiable_cutFB (delta n)).differentiableAt]

private lemma deriv2_angCut_apply (n : ℕ) (θ : ℝ) :
    deriv (deriv (angCut n)) θ
      = deriv (deriv (cutFA (delta n))) θ * cutFB (delta n) θ
        + 2 * (deriv (cutFA (delta n)) θ * deriv (cutFB (delta n)) θ)
        + cutFA (delta n) θ * deriv (deriv (cutFB (delta n))) θ := by
  rw [show angCut n = (cutFA (delta n)) * (cutFB (delta n)) from rfl]
  exact deriv2_cutProd (delta n) θ

/-! ## Part 5: elementary numerical facts -/

private lemma delta_pos_prv (n : ℕ) : 0 < delta n := by
  rw [delta]; positivity

private lemma abs_div_neg_one {a : ℝ} (ha : 0 < a) : |(-1) / a| = 1 / a := by
  have h : (-1 : ℝ) / a = -(1 / a) := by ring
  rw [h, abs_neg, abs_of_pos (one_div_pos.mpr ha)]

private lemma mul_inv_sq_eq (K a : ℝ) : K * (1 / a) ^ 2 = K / a ^ 2 := by
  rw [div_pow, one_pow, mul_one_div]

private lemma abs_add3 (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  calc |x + y + z| = |(x + y) + z| := by ring_nf
    _ ≤ |x + y| + |z| := abs_add_le _ _
    _ ≤ (|x| + |y|) + |z| := add_le_add_left (abs_add_le x y) |z|
    _ = |x| + |y| + |z| := by ring

private lemma abs_sum3_eq (A B C D E F : ℝ) :
    |A * B| + |2 * (C * D)| + |E * F| = |A| * |B| + 2 * (|C| * |D|) + |E| * |F| := by
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]

theorem AngCutDerivFacts :
    (∀ x : ℝ, x ≤ 0 → deriv Real.smoothTransition x = 0) ∧
    (∀ x : ℝ, 1 ≤ x → deriv Real.smoothTransition x = 0) ∧
    (∀ x : ℝ, x ≤ 0 → deriv (deriv Real.smoothTransition) x = 0) ∧
    (∀ x : ℝ, 1 ≤ x → deriv (deriv Real.smoothTransition) x = 0) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ θ : ℝ,
      |deriv (Work.FTS.StrongEps.EComparison.angCut n) θ|
          ≤ K / Work.FTS.StrongEps.EComparison.delta n ∧
      |deriv (deriv (Work.FTS.StrongEps.EComparison.angCut n)) θ|
          ≤ K / (Work.FTS.StrongEps.EComparison.delta n) ^ 2 ∧
      (θ ∈ Set.Icc (2 * Work.FTS.StrongEps.EComparison.delta n)
            (Real.pi / 2 - 2 * Work.FTS.StrongEps.EComparison.delta n) →
        deriv (Work.FTS.StrongEps.EComparison.angCut n) θ = 0) ∧
      (θ ∈ Set.Icc (2 * Work.FTS.StrongEps.EComparison.delta n)
            (Real.pi / 2 - 2 * Work.FTS.StrongEps.EComparison.delta n) →
        deriv (deriv (Work.FTS.StrongEps.EComparison.angCut n)) θ = 0)) := by
  obtain ⟨C1, hC1nn, hC1⟩ := exists_bound_deriv_psi
  obtain ⟨C2, hC2nn, hC2⟩ := exists_bound_deriv2_psi
  refine ⟨fun x hx => deriv_psi_eq_zero_of_le hx, fun x hx => deriv_psi_eq_zero_of_one_le hx,
    fun x hx => Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat x (Or.inl hx),
    fun x hx => Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat x (Or.inr hx),
    ?_⟩
  refine ⟨max (max (2 * C1) (2 * C2 + 2 * C1 ^ 2)) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  intro n θ
  have ha : (0 : ℝ) < delta n := delta_pos_prv n
  have hainv : 0 < 1 / delta n := one_div_pos.mpr ha
  have hK1 : 2 * C1 ≤ max (max (2 * C1) (2 * C2 + 2 * C1 ^ 2)) 1 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hK2 : 2 * C2 + 2 * C1 ^ 2 ≤ max (max (2 * C1) (2 * C2 + 2 * C1 ^ 2)) 1 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hb1 : |deriv Real.smoothTransition (θ / delta n - 1)| ≤ C1 := hC1 _
  have hb2 : |deriv Real.smoothTransition ((Real.pi / 2 - θ) / delta n - 1)| ≤ C1 := hC1 _
  have hb3 : |deriv (deriv Real.smoothTransition) (θ / delta n - 1)| ≤ C2 := hC2 _
  have hb4 : |deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / delta n - 1)| ≤ C2 :=
    hC2 _
  have hD1 : |deriv (cutFA (delta n)) θ| ≤ C1 * (1 / delta n) := by
    rw [deriv_cutFA_apply, abs_mul, abs_of_pos hainv]
    exact mul_le_mul_of_nonneg_right hb1 (le_of_lt hainv)
  have hD2 : |deriv (cutFB (delta n)) θ| ≤ C1 * (1 / delta n) := by
    rw [deriv_cutFB_apply, abs_mul, abs_div_neg_one ha]
    exact mul_le_mul_of_nonneg_right hb2 (le_of_lt hainv)
  have hK1' : (0 : ℝ) ≤ C1 * (1 / delta n) := mul_nonneg hC1nn (le_of_lt hainv)
  have hK2' : (0 : ℝ) ≤ C2 * (1 / delta n) ^ 2 := mul_nonneg hC2nn (sq_nonneg _)
  have hF1 : |cutFA (delta n) θ| ≤ 1 := by
    rw [show cutFA (delta n) θ = Real.smoothTransition (θ / delta n - 1) from rfl]
    exact abs_smoothTransition_le_one _
  have hF2 : |cutFB (delta n) θ| ≤ 1 := by
    rw [show cutFB (delta n) θ = Real.smoothTransition ((Real.pi / 2 - θ) / delta n - 1) from rfl]
    exact abs_smoothTransition_le_one _
  have hD1' : |deriv (deriv (cutFA (delta n))) θ| ≤ C2 * (1 / delta n) ^ 2 := by
    rw [deriv2_cutFA_apply, abs_mul, abs_mul, abs_of_pos hainv]
    calc |deriv (deriv Real.smoothTransition) (θ / delta n - 1)| * (1 / delta n) * (1 / delta n)
        = |deriv (deriv Real.smoothTransition) (θ / delta n - 1)| * (1 / delta n) ^ 2 := by ring
      _ ≤ C2 * (1 / delta n) ^ 2 := mul_le_mul_of_nonneg_right hb3 (by positivity)
  have hD2' : |deriv (deriv (cutFB (delta n))) θ| ≤ C2 * (1 / delta n) ^ 2 := by
    rw [deriv2_cutFB_apply, abs_mul, abs_mul, abs_div_neg_one ha]
    calc |deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / delta n - 1)|
            * (1 / delta n) * (1 / delta n)
        = |deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / delta n - 1)|
            * (1 / delta n) ^ 2 := by ring
      _ ≤ C2 * (1 / delta n) ^ 2 := mul_le_mul_of_nonneg_right hb4 (by positivity)
  have hleft : ∀ y : ℝ, (2 : ℝ) * delta n ≤ y → 1 ≤ y / delta n - 1 := by
    intro y hy
    have h2 : (2 : ℝ) ≤ y / delta n := (le_div_iff₀ ha).mpr hy
    linarith
  have hright : ∀ y : ℝ, y ≤ Real.pi / 2 - 2 * delta n →
      1 ≤ (Real.pi / 2 - y) / delta n - 1 := by
    intro y hy
    have h2 : (2 : ℝ) ≤ (Real.pi / 2 - y) / delta n := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [deriv_angCut_apply n θ]
    calc |deriv (cutFA (delta n)) θ * cutFB (delta n) θ
            + cutFA (delta n) θ * deriv (cutFB (delta n)) θ|
        ≤ |deriv (cutFA (delta n)) θ * cutFB (delta n) θ|
            + |cutFA (delta n) θ * deriv (cutFB (delta n)) θ| := abs_add_le _ _
      _ = |deriv (cutFA (delta n)) θ| * |cutFB (delta n) θ|
            + |cutFA (delta n) θ| * |deriv (cutFB (delta n)) θ| := by rw [abs_mul, abs_mul]
      _ ≤ (C1 * (1 / delta n)) * 1 + 1 * (C1 * (1 / delta n)) :=
          add_le_add (mul_le_mul hD1 hF2 (abs_nonneg _) hK1')
            (mul_le_mul hF1 hD2 (abs_nonneg _) zero_le_one)
      _ = 2 * C1 / delta n := by ring
      _ ≤ max (max (2 * C1) (2 * C2 + 2 * C1 ^ 2)) 1 / delta n :=
          div_le_div_of_nonneg_right hK1 (le_of_lt ha)
  · rw [deriv2_angCut_apply n θ]
    calc |deriv (deriv (cutFA (delta n))) θ * cutFB (delta n) θ
            + 2 * (deriv (cutFA (delta n)) θ * deriv (cutFB (delta n)) θ)
            + cutFA (delta n) θ * deriv (deriv (cutFB (delta n))) θ|
        ≤ |deriv (deriv (cutFA (delta n))) θ * cutFB (delta n) θ|
            + |2 * (deriv (cutFA (delta n)) θ * deriv (cutFB (delta n)) θ)|
            + |cutFA (delta n) θ * deriv (deriv (cutFB (delta n))) θ| := abs_add3 _ _ _
      _ = |deriv (deriv (cutFA (delta n))) θ| * |cutFB (delta n) θ|
            + 2 * (|deriv (cutFA (delta n)) θ| * |deriv (cutFB (delta n)) θ|)
            + |cutFA (delta n) θ| * |deriv (deriv (cutFB (delta n))) θ| := abs_sum3_eq _ _ _ _ _ _
      _ ≤ (C2 * (1 / delta n) ^ 2) * 1
            + 2 * ((C1 * (1 / delta n)) * (C1 * (1 / delta n)))
            + 1 * (C2 * (1 / delta n) ^ 2) :=
          add_le_add (add_le_add (mul_le_mul hD1' hF2 (abs_nonneg _) hK2')
            (mul_le_mul_of_nonneg_left (mul_le_mul hD1 hD2 (abs_nonneg _) hK1')
              (by norm_num)))
            (mul_le_mul hF1 hD2' (abs_nonneg _) zero_le_one)
      _ = (2 * C2 + 2 * C1 ^ 2) * (1 / delta n) ^ 2 := by ring
      _ = (2 * C2 + 2 * C1 ^ 2) / (delta n) ^ 2 := mul_inv_sq_eq _ _
      _ ≤ max (max (2 * C1) (2 * C2 + 2 * C1 ^ 2)) 1 / (delta n) ^ 2 :=
          div_le_div_of_nonneg_right hK2 (sq_nonneg _)
  · intro hθ
    rw [deriv_angCut_apply n θ]
    have hd1 : deriv Real.smoothTransition (θ / delta n - 1) = 0 :=
      deriv_psi_eq_zero_of_one_le (hleft θ hθ.1)
    have hd2 : deriv Real.smoothTransition ((Real.pi / 2 - θ) / delta n - 1) = 0 :=
      deriv_psi_eq_zero_of_one_le (hright θ hθ.2)
    have hE1 : deriv (cutFA (delta n)) θ = 0 := by rw [deriv_cutFA_apply, hd1, zero_mul]
    have hE2 : deriv (cutFB (delta n)) θ = 0 := by rw [deriv_cutFB_apply, hd2, zero_mul]
    rw [hE1, hE2]
    ring
  · intro hθ
    rw [deriv2_angCut_apply n θ]
    have hd1 : deriv Real.smoothTransition (θ / delta n - 1) = 0 :=
      deriv_psi_eq_zero_of_one_le (hleft θ hθ.1)
    have hd2 : deriv Real.smoothTransition ((Real.pi / 2 - θ) / delta n - 1) = 0 :=
      deriv_psi_eq_zero_of_one_le (hright θ hθ.2)
    have hd3 : deriv (deriv Real.smoothTransition) (θ / delta n - 1) = 0 :=
      Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat _
        (Or.inr (hleft θ hθ.1))
    have hd4 : deriv (deriv Real.smoothTransition) ((Real.pi / 2 - θ) / delta n - 1) = 0 :=
      Work.FTS.EllipticEst.AngAWeak.FluxAux.deriv2SmoothTransition_flat _
        (Or.inr (hright θ hθ.2))
    have hE1 : deriv (cutFA (delta n)) θ = 0 := by rw [deriv_cutFA_apply, hd1, zero_mul]
    have hE2 : deriv (cutFB (delta n)) θ = 0 := by rw [deriv_cutFB_apply, hd2, zero_mul]
    have hE1' : deriv (deriv (cutFA (delta n))) θ = 0 := by
      rw [deriv2_cutFA_apply, hd3]; ring
    have hE2' : deriv (deriv (cutFB (delta n))) θ = 0 := by
      rw [deriv2_cutFB_apply, hd4]; ring
    rw [hE1', hE2', hE1, hE2]
    ring

end Work.FTS.StrongEps.EComparison
