import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.profileMikhlinBandGe

/-!
# The band-localised Mikhlin bound for the increments of the polynomial profile

Let `P ∈ ℤ[X]` have degree `deg P = d ≥ 2`, and let `ψ : ℝ → ℝ` be a `C²` function with
`0 ≤ ψ ≤ 1` and `ψ t ≠ 0 ⟹ 1 < t < 2^d` (so `ψ` is supported in `(1, 2^d)`).

For the oscillations of the polynomial profile `Φ_N(β) = ∫₀¹ e(β P(N s)) ds` one needs the
*family* of band-localised multipliers

  `F_i(β) = ψ(2^{i d} β) · (Φ_{2^{i+1}}(β) - Φ_{2^i}(β))`,   `i ∈ ℕ`,

to satisfy a Mikhlin condition **uniformly in `i`**, together with the fact that the `F_i` have
essentially disjoint supports (so that the square function `(Σ_i |F_i|²)^{1/2}` telescopes).

This file proves exactly that:

* `‖F_i‖_∞ ≤ A`, `|β| ‖F_i'(β)‖ ≤ A`, `|β|² ‖F_i''(β)‖ ≤ A` uniformly in `i, β`;
* `F_i(β) · F_j(β) = 0` for `i ≠ j`.

The two ingredients are

* the *pointwise* band (Mikhlin) estimate `profileMikhlinBandGe`: on the band
  `N^d |β| ≤ c` one has `|β|^k ‖Φ_N^{(k)}(β)‖ ≤ C(P,k,c)` with `C` independent of `N`, applied
  with `N = 2^i, 2^{i+1}` and `c = 2^{2d}` (the support of `ψ(2^{id}·)` forces
  `2^{id}|β| ≤ 2^d`, hence `N^d|β| ≤ 2^{2d} ≤ c`);
* the weighted bounds `|t| |ψ'(t)| ≤ B₁`, `|t|² |ψ''(t)| ≤ B₂` for the cut-off, plus the fact
  that `ψ, ψ', ψ''` all vanish off the open interval `(1, 2^d)` — so that *outside* the band the
  product `F_i` and its first derivative vanish identically.
-/

namespace Work.BourgainPlan.Maximal

open Filter
open scoped Topology

noncomputable section

/-- The modulus of a real number seen inside `ℂ`. -/
lemma bandMikhlin_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

/-! ## Vanishing and weighted bounds for the cut-off `ψ` -/

/-- A `C²` function whose non-zero set lies in `(1, 2^d)` vanishes off `[1, 2^d]`. -/
lemma psi_zero_of_le_one_or_ge (ψ : ℝ → ℝ) (d : ℕ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) :
    ∀ t, t ≤ 1 ∨ (2 : ℝ) ^ d ≤ t → ψ t = 0 := by
  intro t ht
  by_contra h
  obtain ⟨h1, h2⟩ := hψs t h
  rcases ht with ht | ht
  · linarith
  · linarith

/-- `ψ` is locally zero to the left of `1`, hence so is `ψ'`. -/
lemma deriv_psi_eq_zero_of_lt_one (ψ : ℝ → ℝ) (d : ℕ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) {t : ℝ} (ht : t < 1) :
    deriv ψ t = 0 := by
  have hev : ψ =ᶠ[𝓝 t] (fun _ : ℝ => 0) :=
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht)
      (fun s hs => psi_zero_of_le_one_or_ge ψ d hψs s (Or.inl (le_of_lt hs)))
  rw [hev.deriv_eq, deriv_const]

/-- `ψ` is locally zero to the right of `2^d`, hence so is `ψ'`. -/
lemma deriv_psi_eq_zero_of_gt (ψ : ℝ → ℝ) (d : ℕ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) {t : ℝ}
    (ht : (2 : ℝ) ^ d < t) : deriv ψ t = 0 := by
  have hev : ψ =ᶠ[𝓝 t] (fun _ : ℝ => 0) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
      (fun s hs => psi_zero_of_le_one_or_ge ψ d hψs s (Or.inr (le_of_lt hs)))
  rw [hev.deriv_eq, deriv_const]

/-- `ψ''` vanishes to the left of `1`. -/
lemma deriv2_psi_eq_zero_of_lt_one (ψ : ℝ → ℝ) (d : ℕ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) {t : ℝ} (ht : t < 1) :
    deriv (deriv ψ) t = 0 := by
  have hev : deriv ψ =ᶠ[𝓝 t] (fun _ : ℝ => 0) :=
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht)
      (fun s hs => deriv_psi_eq_zero_of_lt_one ψ d hψs hs)
  rw [hev.deriv_eq, deriv_const]

/-- `ψ''` vanishes to the right of `2^d`. -/
lemma deriv2_psi_eq_zero_of_gt (ψ : ℝ → ℝ) (d : ℕ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) {t : ℝ}
    (ht : (2 : ℝ) ^ d < t) : deriv (deriv ψ) t = 0 := by
  have hev : deriv ψ =ᶠ[𝓝 t] (fun _ : ℝ => 0) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
      (fun s hs => deriv_psi_eq_zero_of_gt ψ d hψs hs)
  rw [hev.deriv_eq, deriv_const]

/-- **Weighted bounds for the cut-off.**  For a `C²` function supported (up to zero sets) in
`(1, 2^d)` there are constants `B₁, B₂ ≥ 0` with `|t| |ψ'(t)| ≤ B₁` and `|t|² |ψ''(t)| ≤ B₂`
for *all* `t`: inside `[1, 2^d]` this is compactness, outside both `ψ'` and `ψ''` vanish. -/
lemma exists_psi_weighted_bounds (ψ : ℝ → ℝ) (d : ℕ) (hψ : ContDiff ℝ 2 ψ)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ d) :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      (∀ t, |t| * |deriv ψ t| ≤ B1) ∧ (∀ t, |t| ^ 2 * |deriv (deriv ψ) t| ≤ B2) := by
  have hcont1 : Continuous (deriv ψ) := (ContDiff.deriv' (n := 1) hψ).continuous
  have hcont2 : Continuous (deriv (deriv ψ)) := by
    have h1 : ContDiff ℝ 1 (deriv ψ) := ContDiff.deriv' (n := 1) hψ
    exact contDiff_zero.mp (ContDiff.deriv' (n := 0) h1)
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := deriv ψ) hcont1.continuousOn
  obtain ⟨C2, hC2⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := deriv (deriv ψ)) hcont2.continuousOn
  refine ⟨max 0 ((2:ℝ)^d * C1), max 0 (((2:ℝ)^d)^2 * C2), le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Set.Icc (1:ℝ) ((2:ℝ)^d)
    · have h1 : |deriv ψ t| ≤ C1 := by
        have := hC1 t ht
        simpa [Real.norm_eq_abs] using this
      have h2 : |t| ≤ (2:ℝ)^d := by
        rw [abs_of_nonneg (le_trans zero_le_one ht.1)]
        exact ht.2
      calc |t| * |deriv ψ t| ≤ (2:ℝ)^d * C1 :=
            mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
        _ ≤ max 0 ((2:ℝ)^d * C1) := le_max_right _ _
    · simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · rw [deriv_psi_eq_zero_of_lt_one ψ d hψs ht, abs_zero, mul_zero]
        exact le_max_left _ _
      · rw [deriv_psi_eq_zero_of_gt ψ d hψs ht, abs_zero, mul_zero]
        exact le_max_left _ _
  · intro t
    by_cases ht : t ∈ Set.Icc (1:ℝ) ((2:ℝ)^d)
    · have h1 : |deriv (deriv ψ) t| ≤ C2 := by
        have := hC2 t ht
        simpa [Real.norm_eq_abs] using this
      have h2 : |t| ^ 2 ≤ ((2:ℝ)^d)^2 := by
        have h3 : |t| ≤ (2:ℝ)^d := by
          rw [abs_of_nonneg (le_trans zero_le_one ht.1)]
          exact ht.2
        nlinarith [abs_nonneg t]
      calc |t| ^ 2 * |deriv (deriv ψ) t| ≤ ((2:ℝ)^d)^2 * C2 :=
            mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
        _ ≤ max 0 (((2:ℝ)^d)^2 * C2) := le_max_right _ _
    · simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · rw [deriv2_psi_eq_zero_of_lt_one ψ d hψs ht, abs_zero, mul_zero]
        exact le_max_left _ _
      · rw [deriv2_psi_eq_zero_of_gt ψ d hψs ht, abs_zero, mul_zero]
        exact le_max_left _ _

/-! ## Derivatives of the dilated, complexified cut-off -/

/-- First derivative of `γ ↦ ψ(cγ)` (complexified). -/
lemma deriv_complexify_const_mul (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (c β : ℝ) :
    deriv (fun γ : ℝ => (ψ (c * γ) : ℂ)) β = (c : ℂ) * ((deriv ψ (c * β) : ℝ) : ℂ) := by
  have hd : HasDerivAt ψ (deriv ψ (c * β)) (c * β) :=
    ((hψ.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun γ : ℝ => (ψ (c * γ) : ℂ)) (((deriv ψ (c * β)) * c : ℝ) : ℂ) β :=
    (hd.comp β (hasDerivAt_const_mul c)).ofReal_comp
  rw [hcomp.deriv]
  push_cast
  ring

/-- Second derivative of `γ ↦ ψ(cγ)` (complexified). -/
lemma iteratedDeriv_two_complexify_const_mul (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (c β : ℝ) :
    iteratedDeriv 2 (fun γ : ℝ => (ψ (c * γ) : ℂ)) β
      = (c : ℂ) ^ 2 * ((deriv (deriv ψ) (c * β) : ℝ) : ℂ) := by
  have hderiv : deriv (fun γ : ℝ => (ψ (c * γ) : ℂ))
      = fun γ : ℝ => (c : ℂ) * ((deriv ψ (c * γ) : ℝ) : ℂ) :=
    funext (fun γ => deriv_complexify_const_mul ψ hψ c γ)
  have hstep : iteratedDeriv 2 (fun γ : ℝ => (ψ (c * γ) : ℂ)) β
      = deriv (fun γ : ℝ => (c : ℂ) * ((deriv ψ (c * γ) : ℝ) : ℂ)) β := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  rw [hstep]
  have hdψ' : DifferentiableAt ℝ (deriv ψ) (c * β) :=
    ((ContDiff.deriv' (n := 1) hψ).differentiable (by norm_num)).differentiableAt
  have hcomp : HasDerivAt (fun γ : ℝ => deriv ψ (c * γ)) (deriv (deriv ψ) (c * β) * c) β :=
    (hdψ'.hasDerivAt).comp β (hasDerivAt_const_mul c)
  have hmain : HasDerivAt (fun γ : ℝ => (c : ℂ) * ((deriv ψ (c * γ) : ℝ) : ℂ))
      ((c : ℂ) * ((deriv (deriv ψ) (c * β) * c : ℝ) : ℂ)) β :=
    hcomp.ofReal_comp.const_mul (c : ℂ)
  rw [hmain.deriv]
  push_cast
  ring

/-! ## The second order Leibniz rule and its weighted consequence -/

/-- Leibniz's rule at order two for complex-valued functions on `ℝ`. -/
lemma iteratedDeriv_two_mul_expand {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ) :
    iteratedDeriv 2 (f * g) x
      = iteratedDeriv 2 f x * g x + 2 * (deriv f x * deriv g x) + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul (n := 2) hf.contDiffAt hg.contDiffAt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSubDiff, Nat.choose_self,
    iteratedDeriv_zero, iteratedDeriv_one]
  norm_num
  ring

/-- **Pointwise weighted bounds for a product.**  The weight `|x|^k` distributes over the
Leibniz expansion: if `‖f‖`, `|x|‖f'‖`, `|x|²‖f''‖` and the same for `g` are bounded then so are
the corresponding quantities for `f g`. -/
lemma weighted_mul_bound_pointwise {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (β : ℝ) :
    ‖f β * g β‖ ≤ ‖f β‖ * ‖g β‖ ∧
      |β| * ‖deriv (f * g) β‖
        ≤ |β| * ‖deriv f β‖ * ‖g β‖ + ‖f β‖ * (|β| * ‖deriv g β‖) ∧
      |β| ^ 2 * ‖iteratedDeriv 2 (f * g) β‖
        ≤ |β| ^ 2 * ‖iteratedDeriv 2 f β‖ * ‖g β‖ +
          2 * (|β| * ‖deriv f β‖) * (|β| * ‖deriv g β‖) +
          ‖f β‖ * (|β| ^ 2 * ‖iteratedDeriv 2 g β‖) := by
  have hfd : DifferentiableAt ℝ f β := (hf.differentiable (by norm_num)).differentiableAt
  have hgd : DifferentiableAt ℝ g β := (hg.differentiable (by norm_num)).differentiableAt
  refine ⟨le_of_eq (norm_mul ..), ?_, ?_⟩
  · calc |β| * ‖deriv (f * g) β‖
        = |β| * ‖deriv f β * g β + f β * deriv g β‖ := by rw [deriv_mul hfd hgd]
      _ ≤ |β| * (‖deriv f β‖ * ‖g β‖ + ‖f β‖ * ‖deriv g β‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul]
      _ = |β| * ‖deriv f β‖ * ‖g β‖ + ‖f β‖ * (|β| * ‖deriv g β‖) := by ring
  · have h1 : ‖iteratedDeriv 2 f β * g β + 2 * (deriv f β * deriv g β)
        + f β * iteratedDeriv 2 g β‖
        ≤ ‖iteratedDeriv 2 f β‖ * ‖g β‖ + 2 * (‖deriv f β‖ * ‖deriv g β‖)
          + ‖f β‖ * ‖iteratedDeriv 2 g β‖ := by
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · refine le_trans (norm_add_le _ _) ?_
        simp only [norm_mul, Complex.norm_ofNat]
        exact le_of_eq (by ring)
      · rw [norm_mul]
    calc |β| ^ 2 * ‖iteratedDeriv 2 (f * g) β‖
        = |β| ^ 2 * ‖iteratedDeriv 2 f β * g β + 2 * (deriv f β * deriv g β)
            + f β * iteratedDeriv 2 g β‖ := by rw [iteratedDeriv_two_mul_expand hf hg]
      _ ≤ |β| ^ 2 * (‖iteratedDeriv 2 f β‖ * ‖g β‖ + 2 * (‖deriv f β‖ * ‖deriv g β‖)
            + ‖f β‖ * ‖iteratedDeriv 2 g β‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |β| ^ 2 * ‖iteratedDeriv 2 f β‖ * ‖g β‖ +
          2 * (|β| * ‖deriv f β‖) * (|β| * ‖deriv g β‖) +
          ‖f β‖ * (|β| ^ 2 * ‖iteratedDeriv 2 g β‖) := by ring

/-! ## The band-localised Mikhlin bound -/

theorem bandLocalizedIncrement_mikhlin (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψs : ∀ t, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ P.natDegree) :
    ∃ A : ℝ, 0 < A ∧
      (∀ (i : ℕ) (β : ℝ), ‖(ψ ((2:ℝ) ^ (i * P.natDegree) * β) : ℂ) *
          (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (i+1)) β
            - Work.BourgainPlan.Maximal.polyProfile P (2 ^ i) β)‖ ≤ A) ∧
      (∀ (i : ℕ) (β : ℝ), |β| * ‖deriv (fun γ : ℝ => (ψ ((2:ℝ) ^ (i * P.natDegree) * γ) : ℂ) *
          (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (i+1)) γ
            - Work.BourgainPlan.Maximal.polyProfile P (2 ^ i) γ)) β‖ ≤ A) ∧
      (∀ (i : ℕ) (β : ℝ), |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => (ψ ((2:ℝ) ^ (i * P.natDegree) * γ) : ℂ) *
          (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (i+1)) γ
            - Work.BourgainPlan.Maximal.polyProfile P (2 ^ i) γ)) β‖ ≤ A) ∧
      (∀ (i j : ℕ), i ≠ j → ∀ β : ℝ,
        (ψ ((2:ℝ) ^ (i * P.natDegree) * β) : ℂ) *
            (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (i+1)) β
              - Work.BourgainPlan.Maximal.polyProfile P (2 ^ i) β) = 0 ∨
        (ψ ((2:ℝ) ^ (j * P.natDegree) * β) : ℂ) *
            (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j+1)) β
              - Work.BourgainPlan.Maximal.polyProfile P (2 ^ j) β) = 0) := by
  obtain ⟨B1, B2, hB1nn, hB2nn, hB1, hB2⟩ :=
    exists_psi_weighted_bounds ψ P.natDegree hψ hψs
  obtain ⟨C1, hC1pos, hC1⟩ := profileMikhlinBandGe P 1 (((2:ℝ) ^ P.natDegree) ^ 2)
  obtain ⟨C2, hC2pos, hC2⟩ := profileMikhlinBandGe P 2 (((2:ℝ) ^ P.natDegree) ^ 2)
  set d : ℕ := P.natDegree with hd_def
  have _hdpos : 0 < d := by omega
  have h2d1 : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hC2nn : 0 ≤ C2 := hC2pos.le
  have hBC : 0 ≤ 4*B1*C1 := by nlinarith [hB1nn, hC1nn]
  let A : ℝ := max 1 (2 + 2*B1 + 2*C1 + (2*B2 + 4*B1*C1 + 2*C2))
  have hApos : 0 < A := lt_of_lt_of_le one_pos (le_max_left 1 _)
  have hAub : ∀ x : ℝ, x ≤ 2 + 2*B1 + 2*C1 + (2*B2 + 4*B1*C1 + 2*C2) → x ≤ A :=
    fun x hx => le_trans hx (le_max_right 1 _)
  have hA2 : (2:ℝ) ≤ A := hAub 2 (by nlinarith [hB1nn, hB2nn, hC1nn, hC2nn, hBC])
  have key : ∀ (i : ℕ) (β : ℝ),
      |β| * ‖deriv (fun γ : ℝ => (ψ ((2:ℝ) ^ (i * d) * γ) : ℂ) *
          (polyProfile P (2 ^ (i+1)) γ - polyProfile P (2 ^ i) γ)) β‖ ≤ A ∧
      |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => (ψ ((2:ℝ) ^ (i * d) * γ) : ℂ) *
          (polyProfile P (2 ^ (i+1)) γ - polyProfile P (2 ^ i) γ)) β‖ ≤ A := by
    intro i β
    set c : ℝ := (2:ℝ) ^ (i * d) with hc_def
    set N1 : ℕ := 2 ^ (i+1) with hN1_def
    set N2 : ℕ := 2 ^ i with hN2_def
    let f : ℝ → ℂ := fun γ : ℝ => (ψ (c * γ) : ℂ)
    let g : ℝ → ℂ := fun γ : ℝ => polyProfile P N1 γ - polyProfile P N2 γ
    have hcpos : 0 < c := by rw [hc_def]; positivity
    have hN1ge : 1 ≤ N1 := by rw [hN1_def]; exact Nat.one_le_two_pow
    have hN2ge : 1 ≤ N2 := by rw [hN2_def]; exact Nat.one_le_two_pow
    have hfcd : ContDiff ℝ 2 f :=
      Complex.ofRealCLM.contDiff.comp (hψ.comp (contDiff_const.mul contDiff_id))
    have hP1 : ContDiff ℝ 2 (fun γ : ℝ => polyProfile P N1 γ) :=
      (contDiff_polyProfile P N1).of_le (WithTop.coe_le_coe.mpr le_top)
    have hP2 : ContDiff ℝ 2 (fun γ : ℝ => polyProfile P N2 γ) :=
      (contDiff_polyProfile P N2).of_le (WithTop.coe_le_coe.mpr le_top)
    have hgcd : ContDiff ℝ 2 g := hP1.sub hP2
    have hP1d : DifferentiableAt ℝ (fun γ : ℝ => polyProfile P N1 γ) β :=
      (hP1.differentiable (by norm_num)).differentiableAt
    have hP2d : DifferentiableAt ℝ (fun γ : ℝ => polyProfile P N2 γ) β :=
      (hP2.differentiable (by norm_num)).differentiableAt
    have hf_deriv : deriv f β = (c : ℂ) * ((deriv ψ (c * β) : ℝ) : ℂ) :=
      deriv_complexify_const_mul ψ hψ c β
    have hf_second : iteratedDeriv 2 f β = (c : ℂ) ^ 2 * ((deriv (deriv ψ) (c * β) : ℝ) : ℂ) :=
      iteratedDeriv_two_complexify_const_mul ψ hψ c β
    have hf_0 : ‖f β‖ ≤ 1 := by
      show ‖(ψ (c * β) : ℂ)‖ ≤ 1
      rw [bandMikhlin_norm_ofReal]
      exact abs_le.mpr ⟨by linarith [hψ0 (c * β)], hψ1 (c * β)⟩
    have hf_w1 : |β| * ‖deriv f β‖ ≤ B1 := by
      rw [hf_deriv, norm_mul, bandMikhlin_norm_ofReal, bandMikhlin_norm_ofReal, abs_of_pos hcpos]
      calc |β| * (c * |deriv ψ (c * β)|) = |c * β| * |deriv ψ (c * β)| := by
            rw [abs_mul, abs_of_pos hcpos]; ring
        _ ≤ B1 := hB1 (c * β)
    have hf_w2 : |β| ^ 2 * ‖iteratedDeriv 2 f β‖ ≤ B2 := by
      rw [hf_second, norm_mul, norm_pow, bandMikhlin_norm_ofReal, bandMikhlin_norm_ofReal, abs_of_pos hcpos]
      calc |β| ^ 2 * (c ^ 2 * |deriv (deriv ψ) (c * β)|)
          = |c * β| ^ 2 * |deriv (deriv ψ) (c * β)| := by
            rw [abs_mul, abs_of_pos hcpos]; ring
        _ ≤ B2 := hB2 (c * β)
    have hg_0 : ‖g β‖ ≤ 2 := by
      show ‖polyProfile P N1 β - polyProfile P N2 β‖ ≤ 2
      have hA := norm_polyProfile_le_one P N1 β
      have hB := norm_polyProfile_le_one P N2 β
      linarith [norm_sub_le (polyProfile P N1 β) (polyProfile P N2 β)]
    have hgeriv : deriv g β = deriv (fun γ : ℝ => polyProfile P N1 γ) β
        - deriv (fun γ : ℝ => polyProfile P N2 γ) β := by
      exact deriv_sub hP1d hP2d
    have hge2 : iteratedDeriv 2 g β = iteratedDeriv 2 (fun γ : ℝ => polyProfile P N1 γ) β
        - iteratedDeriv 2 (fun γ : ℝ => polyProfile P N2 γ) β :=
      iteratedDeriv_sub hP1.contDiffAt hP2.contDiffAt
    by_cases hband : c * |β| ≤ (2:ℝ)^d
    · -- ================= inside the band =================
      have hb1 : ((N1 : ℝ) ^ d) * |β| ≤ ((2:ℝ)^d)^2 := by
        have hcast : (N1 : ℝ) = (2:ℝ)^(i+1) := by rw [hN1_def]; push_cast; ring
        rw [hcast, ← pow_mul]
        have hp : (i+1)*d = i*d + d := by ring
        rw [hp, pow_add]
        calc ((2:ℝ)^(i*d) * (2:ℝ)^d) * |β| = (2:ℝ)^d * ((2:ℝ)^(i*d) * |β|) := by ring
          _ ≤ (2:ℝ)^d * (2:ℝ)^d := mul_le_mul_of_nonneg_left hband (by positivity)
          _ = ((2:ℝ)^d)^2 := by ring
      have hb2 : ((N2 : ℝ) ^ d) * |β| ≤ ((2:ℝ)^d)^2 := by
        have hcast : (N2 : ℝ) = (2:ℝ)^i := by rw [hN2_def]; push_cast; ring
        rw [hcast, ← pow_mul]
        calc (2:ℝ)^(i*d) * |β| ≤ (2:ℝ)^d := hband
          _ ≤ ((2:ℝ)^d)^2 := by nlinarith [h2d1]
      have hC1a : |β| * ‖deriv (fun γ : ℝ => polyProfile P N1 γ) β‖ ≤ C1 := by
        rw [← iteratedDeriv_one]
        simpa using hC1 N1 hN1ge β hb1
      have hC1b : |β| * ‖deriv (fun γ : ℝ => polyProfile P N2 γ) β‖ ≤ C1 := by
        rw [← iteratedDeriv_one]
        simpa using hC1 N2 hN2ge β hb2
      have hC2a : |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N1 γ) β‖ ≤ C2 :=
        hC2 N1 hN1ge β hb1
      have hC2b : |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N2 γ) β‖ ≤ C2 :=
        hC2 N2 hN2ge β hb2
      have hgw1 : |β| * ‖deriv g β‖ ≤ 2 * C1 := by
        calc |β| * ‖deriv g β‖
            = |β| * ‖deriv (fun γ : ℝ => polyProfile P N1 γ) β
                - deriv (fun γ : ℝ => polyProfile P N2 γ) β‖ := by rw [hgeriv]
          _ ≤ |β| * (‖deriv (fun γ : ℝ => polyProfile P N1 γ) β‖
                + ‖deriv (fun γ : ℝ => polyProfile P N2 γ) β‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg β)
          _ = |β| * ‖deriv (fun γ : ℝ => polyProfile P N1 γ) β‖
                + |β| * ‖deriv (fun γ : ℝ => polyProfile P N2 γ) β‖ := by ring
          _ ≤ C1 + C1 := add_le_add hC1a hC1b
          _ = 2 * C1 := by ring
      have hgw2 : |β| ^ 2 * ‖iteratedDeriv 2 g β‖ ≤ 2 * C2 := by
        calc |β| ^ 2 * ‖iteratedDeriv 2 g β‖
            = |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N1 γ) β
                - iteratedDeriv 2 (fun γ : ℝ => polyProfile P N2 γ) β‖ := by rw [hge2]
          _ ≤ |β| ^ 2 * (‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N1 γ) β‖
                + ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N2 γ) β‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
          _ = |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N1 γ) β‖
                + |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => polyProfile P N2 γ) β‖ := by ring
          _ ≤ C2 + C2 := add_le_add hC2a hC2b
          _ = 2 * C2 := by ring
      have hkey := weighted_mul_bound_pointwise (f := f) (g := g) hfcd hgcd β
      constructor
      · calc |β| * ‖deriv (fun γ : ℝ => (ψ (c * γ) : ℂ) *
            (polyProfile P N1 γ - polyProfile P N2 γ)) β‖
            ≤ |β| * ‖deriv f β‖ * ‖g β‖ + ‖f β‖ * (|β| * ‖deriv g β‖) := hkey.2.1
          _ ≤ B1 * 2 + 1 * (2 * C1) := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul hf_w1 hg_0 (norm_nonneg _) hB1nn
              · exact mul_le_mul hf_0 hgw1 (by positivity) zero_le_one
          _ ≤ A := hAub _ (by nlinarith [hB1nn, hB2nn, hC1nn, hC2nn, hBC])
      · calc |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => (ψ (c * γ) : ℂ) *
            (polyProfile P N1 γ - polyProfile P N2 γ)) β‖
            ≤ |β| ^ 2 * ‖iteratedDeriv 2 f β‖ * ‖g β‖
              + 2 * (|β| * ‖deriv f β‖) * (|β| * ‖deriv g β‖)
              + ‖f β‖ * (|β| ^ 2 * ‖iteratedDeriv 2 g β‖) := hkey.2.2
          _ ≤ B2 * 2 + 2 * B1 * (2 * C1) + 1 * (2 * C2) := by
              refine add_le_add (add_le_add ?_ ?_) ?_
              · exact mul_le_mul hf_w2 hg_0 (norm_nonneg _) hB2nn
              · exact mul_le_mul (mul_le_mul_of_nonneg_left hf_w1 (by norm_num)) hgw1
                  (by positivity) (by positivity)
              · exact mul_le_mul hf_0 hgw2 (by positivity) zero_le_one
          _ ≤ A := hAub _ (by nlinarith [hB1nn, hB2nn, hC1nn, hC2nn, hBC])
    · -- ================= outside the band =================
      have hgt : (2:ℝ)^d < c * |β| := lt_of_not_ge hband
      have habs : (2:ℝ)^d < |c * β| := by rw [abs_mul, abs_of_pos hcpos]; exact hgt
      have hcases : (2:ℝ)^d < c * β ∨ c * β < -((2:ℝ)^d) := by
        rcases lt_abs.mp habs with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith)
      have hf0 : ψ (c * β) = 0 := by
        rcases hcases with hc | hc
        · exact psi_zero_of_le_one_or_ge ψ d hψs _ (Or.inr hc.le)
        · exact psi_zero_of_le_one_or_ge ψ d hψs _ (Or.inl (by linarith))
      have hf0' : deriv ψ (c * β) = 0 := by
        rcases hcases with hc | hc
        · exact deriv_psi_eq_zero_of_gt ψ d hψs hc
        · exact deriv_psi_eq_zero_of_lt_one ψ d hψs (by linarith)
      have hfval0 : f β = 0 := by
        show (ψ (c * β) : ℂ) = 0
        rw [hf0]
        norm_num
      have hfderiv0 : deriv f β = 0 := by
        rw [hf_deriv, hf0']
        simp
      have hkey := weighted_mul_bound_pointwise (f := f) (g := g) hfcd hgcd β
      constructor
      · calc |β| * ‖deriv (fun γ : ℝ => (ψ (c * γ) : ℂ) *
            (polyProfile P N1 γ - polyProfile P N2 γ)) β‖
            ≤ |β| * ‖deriv f β‖ * ‖g β‖ + ‖f β‖ * (|β| * ‖deriv g β‖) := hkey.2.1
          _ = 0 := by rw [hfderiv0, hfval0]; simp
          _ ≤ A := le_of_lt hApos
      · calc |β| ^ 2 * ‖iteratedDeriv 2 (fun γ : ℝ => (ψ (c * γ) : ℂ) *
            (polyProfile P N1 γ - polyProfile P N2 γ)) β‖
            ≤ |β| ^ 2 * ‖iteratedDeriv 2 f β‖ * ‖g β‖
              + 2 * (|β| * ‖deriv f β‖) * (|β| * ‖deriv g β‖)
              + ‖f β‖ * (|β| ^ 2 * ‖iteratedDeriv 2 g β‖) := hkey.2.2
          _ = |β| ^ 2 * ‖iteratedDeriv 2 f β‖ * ‖g β‖ := by
              rw [hfderiv0, hfval0]; simp
          _ ≤ B2 * 2 := mul_le_mul hf_w2 hg_0 (norm_nonneg _) hB2nn
          _ ≤ A := hAub _ (by nlinarith [hB1nn, hB2nn, hC1nn, hC2nn, hBC])
  refine ⟨A, hApos, ?_, (fun i β => (key i β).1), (fun i β => (key i β).2), ?_⟩
  · -- the sup bound
    intro i β
    have h1 : ‖(ψ ((2:ℝ) ^ (i * d) * β) : ℂ)‖ ≤ 1 := by
      rw [bandMikhlin_norm_ofReal]
      exact abs_le.mpr ⟨by linarith [hψ0 ((2:ℝ) ^ (i * d) * β)], hψ1 ((2:ℝ) ^ (i * d) * β)⟩
    have h2 : ‖polyProfile P (2 ^ (i+1)) β - polyProfile P (2 ^ i) β‖ ≤ 2 := by
      have hA := norm_polyProfile_le_one P (2 ^ (i+1)) β
      have hB := norm_polyProfile_le_one P (2 ^ i) β
      linarith [norm_sub_le (polyProfile P (2 ^ (i+1)) β) (polyProfile P (2 ^ i) β)]
    calc ‖(ψ ((2:ℝ) ^ (i * d) * β) : ℂ) *
          (polyProfile P (2 ^ (i+1)) β - polyProfile P (2 ^ i) β)‖
        = ‖(ψ ((2:ℝ) ^ (i * d) * β) : ℂ)‖ *
          ‖polyProfile P (2 ^ (i+1)) β - polyProfile P (2 ^ i) β‖ := norm_mul ..
      _ ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
      _ ≤ A := hA2
  · -- disjoint supports
    intro i j hij β
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hi, hj⟩ := hcon
    have hψi : ψ ((2 : ℝ) ^ (i * d) * β) ≠ 0 := by
      intro h0
      exact hi (by simp [h0])
    have hψj : ψ ((2 : ℝ) ^ (j * d) * β) ≠ 0 := by
      intro h0
      exact hj (by simp [h0])
    obtain ⟨hi1, _hi2⟩ := hψs _ hψi
    obtain ⟨hj1, hj2⟩ := hψs _ hψj
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hpos : 0 < (2 : ℝ) ^ ((j - i) * d) := by positivity
      have h3 : (2 : ℝ) ^ ((j - i) * d)
          < (2 : ℝ) ^ ((j - i) * d) * ((2 : ℝ) ^ (i * d) * β) := by
        have := mul_lt_mul_of_pos_left hi1 hpos
        rwa [mul_one] at this
      have hpow : (2 : ℝ) ^ ((j - i) * d) * (2 : ℝ) ^ (i * d) = (2 : ℝ) ^ (j * d) := by
        rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hlt)]
      rw [← mul_assoc, hpow] at h3
      have h5 : (2 : ℝ) ^ ((j - i) * d) < (2 : ℝ) ^ d := lt_trans h3 hj2
      have h6 : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ ((j - i) * d) := by
        refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
        have hone : 1 ≤ j - i := by omega
        calc d = 1 * d := by ring
          _ ≤ (j - i) * d := Nat.mul_le_mul_right d hone
      exact absurd h5 (not_lt.mpr h6)
    · exact absurd heq hij
    · have hpos : 0 < (2 : ℝ) ^ ((i - j) * d) := by positivity
      have h3 : (2 : ℝ) ^ ((i - j) * d)
          < (2 : ℝ) ^ ((i - j) * d) * ((2 : ℝ) ^ (j * d) * β) := by
        have := mul_lt_mul_of_pos_left hj1 hpos
        rwa [mul_one] at this
      have hpow : (2 : ℝ) ^ ((i - j) * d) * (2 : ℝ) ^ (j * d) = (2 : ℝ) ^ (i * d) := by
        rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hgt)]
      rw [← mul_assoc, hpow] at h3
      have h5 : (2 : ℝ) ^ ((i - j) * d) < (2 : ℝ) ^ d := by
        rcases hψs _ hψi with ⟨_, h⟩
        exact lt_trans h3 h
      have h6 : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ ((i - j) * d) := by
        refine pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
        have hone : 1 ≤ i - j := by omega
        calc d = 1 * d := by ring
          _ ≤ (i - j) * d := Nat.mul_le_mul_right d hone
      exact absurd h5 (not_lt.mpr h6)

end

end Work.BourgainPlan.Maximal
