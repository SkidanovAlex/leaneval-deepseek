import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikContract.API.isZ_primitive_facts
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount

open scoped BigOperators

namespace Work.LinnikAreas.A5

/-- Arithmetic core of (13.2): `lam + (s-rho)*log q = (1-rho)*log q` for `s = 1 - lam/log q`. -/
private lemma sub_log_mul (q : ℕ) (hq : Real.log q ≠ 0) (lam : ℝ) (u : ℂ) :
    (lam : ℂ) + ((((1 - lam / Real.log q : ℝ)) : ℂ) - u) * ((Real.log q : ℝ) : ℂ)
      = (1 - u) * ((Real.log q : ℝ) : ℂ) := by
  have hreal : (1 - lam / Real.log q) * Real.log q = Real.log q - lam := by
    field_simp
  have hcast : (((1 - lam / Real.log q : ℝ)) : ℂ) * ((Real.log q : ℝ) : ℂ)
      = ((Real.log q : ℝ) : ℂ) - (lam : ℂ) := by
    rw [← Complex.ofReal_mul, hreal]; push_cast; ring
  rw [sub_mul, hcast]; ring

/-- The real part of the argument of `F`: `((s-rho)*log q).re = lam(rho) - lam`. -/
private lemma sub_log_mul_re (q : ℕ) (hq : Real.log q ≠ 0) (lam : ℝ) (u : ℂ) :
    (((((1 - lam / Real.log q : ℝ)) : ℂ) - u) * ((Real.log q : ℝ) : ℂ)).re
      = Work.LinnikContract.lamOf q u - lam := by
  rw [Work.LinnikContract.lamOf]
  have key : (1 - lam / Real.log q - u.re) * Real.log q = (1 - u.re) * Real.log q - lam := by
    have h1 : (1 - lam / Real.log q - u.re) = (1 - u.re) - lam / Real.log q := by ring
    rw [h1, sub_mul, div_mul_cancel₀ lam hq]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [key]
  ring

/-
(Corrected resubmission of the earlier `LinnikAreas/A5/boxAbs_le_zeroSum`: in the statement as
first submitted the factor `log q` multiplied the VALUE of `F` instead of its ARGUMENT; reviewers
caught it.  Here the argument is `(s - u) * log q` with `s = 1 - lam/log q`, matching (13.2).)

The bookkeeping step of HB 13.3: the per-character box sum is controlled by the (Lemma 5.2)
zero sum over the δ-window.

`Work.LinnikContract.boxAbs q K R χ = ∑ᶠ ρ, if InBox q R ρ then (zeroMult χ ρ : ℝ) * ‖F2 K ((1-ρ)·log q)‖ else 0`
(with `InBox q R ρ ↔ lamOf q ρ ≤ R ∧ |ρ.im|·log q ≤ R`, `lamOf q ρ = (1-ρ.re)·log q`, and
`zeroMult χ ρ` the multiplicity of `ρ` as a zero of the completed L-function of the primitive
character inducing `χ`), while the conclusion of the §5 smoothing estimate is the sum
`∑ᶠ u, ((divisor (completedLFunction χ.primitiveCharacter) (closedBall 0 2)) u) * (Re F((s-u)·log q) restricted to the δ-window)`
with `F` the Laplace transform of the weight.  Hypotheses:

* `hF` (the (13.2) substitute) says that `F` dominates `c·‖F₂(λ + ·)‖` on the closed right
  half-plane;
* `hZ` says that every zero of `χ` with `|Im ρ| ≤ 1` has `lamOf q ρ ≥ lam` (the zero-free
  hypothesis of 13.3);
* `hδge : 2R ≤ δ·log q` puts the box `λ(ρ) ≤ R`, `|γ|log q ≤ R` inside the δ-window
  (`|1-ρ| ≤ √2·R/log q ≤ δ`) and inside the ball `closedBall 0 2`;
* `hδ1 : δ < 1` makes δ-window zeros satisfy `|Im| ≤ 1`, hence `IsZ`, hence `λ ≥ lam` by `hZ`.

Then each box zero `ρ` satisfies `Re((s-ρ)·log q) ≥ 0` (since `lam ≤ lamOf q ρ`), so (13.2) gives
`c·‖F₂((1-ρ)·log q)‖ ≤ Re F((s-ρ)·log q)` because `lam + (s-ρ)·log q = (1-ρ)·log q`; while the
multiplicity matches the divisor in the ball (`divisor_eq_analyticOrderNatAt_cast` on the entire
`completedLFunction χ.primitiveCharacter`, plus `divisor_univ_eq_closedBall`).  A box zero also has
`Re ρ < 1` (strip theorem `completedL_zero_strip` for the primitive `χ.primitiveCharacter`), hence
`|ρ| ≤ 1 + |1-ρ| ≤ 1+δ ≤ 2`.  Every δ-window zero contributes a non-negative amount (same
argument, using `|Im| ≤ δ < 1`), so the box sum is controlled by the full δ-window sum.  Both
sides are finitely supported (the divisor support in the ball, `divisor_real_finiteSupport`), and
`finsum_eq_sum_of_support_subset` + `Finset.sum_le_sum` finish.
-/
theorem boxAbs_le_deltaSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hχ : χ ≠ 1)
    {K R δ lam c : ℝ} {F : ℂ → ℂ} (hK : 0 < K) (hR : 0 < R) (hL : 0 < Real.log q)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδge : 2 * R ≤ δ * Real.log q) (hc : 0 < c)
    (hF : ∀ z : ℂ, 0 ≤ z.re → c * ‖Work.LinnikContract.F2 K ((lam : ℂ) + z)‖ ≤ (F z).re)
    (hZ : ∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam ≤ Work.LinnikContract.lamOf q ρ) :
    Work.LinnikContract.boxAbs q K R χ ≤ c⁻¹ * (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 2)) u : ℝ) *
        (if ‖(1:ℂ) - u‖ ≤ δ then
          (F (((((1 - lam / Real.log q : ℝ)) : ℂ) - u) * ((Real.log q : ℝ) : ℂ))).re else 0)) := by
  classical
  have hLq : Real.log q ≠ 0 := ne_of_gt hL
  have hprim_ne1 : χ.primitiveCharacter ≠ 1 := by
    intro hψ
    have h1 := χ.changeLevel_primitiveCharacter
    rw [hψ, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
    exact hχ h1.symm
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) 2) :=
    Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ.primitiveCharacter hprim_ne1 _
  have hstrip : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → 0 < u.re ∧ u.re < 1 := by
    intro u hz
    have hz0 : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
    exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hprim_ne1
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hz0
  simp only [Work.LinnikContract.boxAbs]
  set Lc : ℂ := ((Real.log q : ℝ) : ℂ) with hLc
  set s0 : ℂ := (((1 - lam / Real.log q : ℝ)) : ℂ) with hs0
  have hdiv_nonneg : ∀ u : ℂ, 0 ≤ ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) 2)) u : ℝ) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0:ℂ) 2
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd hΛan hu
    · rw [MeromorphicOn.divisor_def, if_neg]
      · simp
      · exact fun hc' => hu hc'.2
  have hdiv_cast : ∀ u : ℂ, u ∈ Metric.closedBall (0:ℂ) 2 →
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) 2)) u : ℝ) = (Work.LinnikContract.zeroMult χ u : ℝ) := by
    intro u hu
    have h := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (z := u) hΛan hu
    rw [h, Work.LinnikContract.zeroMult]; norm_num
  have hdiv_pos : ∀ u : ℂ, 0 < ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) 2)) u : ℝ) →
      u ∈ Metric.closedBall (0:ℂ) 2 ∧ Work.LinnikContract.zeroMult χ u ≠ 0 := by
    intro u hpos
    have hball : u ∈ Metric.closedBall (0:ℂ) 2 := by
      by_contra hu
      have h0 : ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall (0:ℂ) 2)) u : ℝ) = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        · simp
        · exact fun hc' => hu hc'.2
      rw [h0] at hpos; exact lt_irrefl _ hpos
    refine ⟨hball, ?_⟩
    intro hz
    rw [hdiv_cast u hball, hz] at hpos
    simp at hpos
  have hbox_facts : ∀ u : ℂ, Work.LinnikContract.InBox q R u → Work.LinnikContract.zeroMult χ u ≠ 0 →
      u ∈ Metric.closedBall (0:ℂ) 2 ∧ ‖(1:ℂ) - u‖ ≤ δ ∧
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) 2)) u : ℝ) = (Work.LinnikContract.zeroMult χ u : ℝ) := by
    intro u hbox hz
    obtain ⟨hre1, hre2⟩ := hstrip u hz
    obtain ⟨hb1, hb2⟩ := hbox
    rw [Work.LinnikContract.lamOf] at hb1
    have hRL : R / Real.log q ≤ δ / 2 := by
      rw [div_le_iff₀ hL]; linarith [hδge]
    have hRLnn : 0 ≤ R / Real.log q := by positivity
    have h1u : 1 - u.re ≤ R / Real.log q := by
      rw [le_div_iff₀ hL]; linarith [hb1]
    have h2u : |u.im| ≤ R / Real.log q := by
      rw [le_div_iff₀ hL]; linarith [hb2]
    have hsq : ‖(1:ℂ) - u‖^2 ≤ δ^2 := by
      have h1 : ‖(1:ℂ) - u‖^2 = (1 - u.re)^2 + u.im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        ring
      rw [h1]
      have hb1sq : (1 - u.re)^2 ≤ (R / Real.log q)^2 := by
        have hnn : 0 ≤ 1 - u.re := by linarith
        nlinarith [h1u, hnn, hRLnn, sq_nonneg (R / Real.log q - (1 - u.re))]
      have hb2abs : |u.im|^2 ≤ (R / Real.log q)^2 := by
        nlinarith [h2u, abs_nonneg u.im, hRLnn, sq_nonneg (R / Real.log q - |u.im|)]
      have hb2sq : u.im^2 ≤ (R / Real.log q)^2 := by rwa [sq_abs] at hb2abs
      have hR2 : 2 * (R / Real.log q)^2 ≤ δ^2 := by
        have h1' : (R / Real.log q)^2 ≤ (δ / 2)^2 :=
          sq_le_sq' (by linarith [hRLnn, hδ0]) hRL
        nlinarith [h1', hδ0]
      nlinarith [hb1sq, hb2sq, hR2]
    have hle_abs : ‖(1:ℂ) - u‖ ≤ δ := by
      have h := (sq_le_sq.mp hsq)
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt hδ0)] at h
    have hu_norm_lt : ‖u‖ < 2 := by
      have htri : ‖u‖ ≤ ‖(1:ℂ) - u‖ + 1 := by
        have := norm_add_le (u - 1) 1
        rw [show u - 1 + 1 = u from by ring] at this
        have h1n : ‖(1:ℂ)‖ = 1 := by simp
        rw [h1n] at this
        have h2 : ‖u - 1‖ = ‖(1:ℂ) - u‖ := norm_sub_rev u 1
        rwa [h2] at this
      linarith
    have hball2 : u ∈ Metric.closedBall (0:ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; simp only [sub_zero]; linarith
    exact ⟨hball2, hle_abs, hdiv_cast u hball2⟩
  have hZ_win : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → ‖(1:ℂ) - u‖ ≤ δ →
      lam ≤ Work.LinnikContract.lamOf q u := by
    intro u hz hwin
    refine hZ u ⟨hχ, hz, ?_⟩
    have h : |u.im| ≤ ‖(1:ℂ) - u‖ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) - u)
      rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    linarith
  have hF_ge : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → ‖(1:ℂ) - u‖ ≤ δ →
      c * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ ≤ (F ((s0 - u) * Lc)).re := by
    intro u hz hwin
    have hlam := hZ_win u hz hwin
    have hzre : 0 ≤ ((s0 - u) * Lc).re := by
      rw [hs0, hLc, sub_log_mul_re q hLq lam u]; linarith
    have h := hF ((s0 - u) * Lc) hzre
    have hid : (lam : ℂ) + (s0 - u) * Lc = (1 - u) * Lc := by
      rw [hs0, hLc]; exact sub_log_mul q hLq lam u
    rw [hid] at h
    exact h
  have hF_re_nonneg : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → ‖(1:ℂ) - u‖ ≤ δ →
      0 ≤ (F ((s0 - u) * Lc)).re := by
    intro u hz hwin
    have h := hF_ge u hz hwin
    have h0 : 0 ≤ c * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ :=
      mul_nonneg (le_of_lt hc) (norm_nonneg _)
    linarith
  have hprod : ∀ u : ℂ, 0 ≤ ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) 2)) u : ℝ) *
      (if ‖(1:ℂ) - u‖ ≤ δ then (F ((s0 - u) * Lc)).re else 0) := by
    intro u
    by_cases hwin : ‖(1:ℂ) - u‖ ≤ δ
    · rw [if_pos hwin]
      rcases eq_or_lt_of_le (hdiv_nonneg u) with h0 | hpos
      · rw [← h0]; simp
      · obtain ⟨-, hz⟩ := hdiv_pos u hpos
        exact mul_nonneg (le_of_lt hpos) (hF_re_nonneg u hz hwin)
    · rw [if_neg hwin, mul_zero]
  have hpt : ∀ u : ℂ,
      (if Work.LinnikContract.InBox q R u then
        (Work.LinnikContract.zeroMult χ u : ℝ) * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ else 0)
      ≤ c⁻¹ * (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall (0:ℂ) 2)) u : ℝ) *
        (if ‖(1:ℂ) - u‖ ≤ δ then (F ((s0 - u) * Lc)).re else 0)) := by
    intro u
    by_cases hbox : Work.LinnikContract.InBox q R u
    · rw [if_pos hbox]
      by_cases hz : Work.LinnikContract.zeroMult χ u = 0
      · rw [hz]
        simp only [Nat.cast_zero, zero_mul]
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt hc)) (hprod u)
      · obtain ⟨hball, hwin, hgg⟩ := hbox_facts u hbox hz
        rw [if_pos hwin, hgg]
        have hge := hF_ge u hz hwin
        have hznn : (0:ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by positivity
        have h1 : c⁻¹ * (c * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖)
            ≤ c⁻¹ * (F ((s0 - u) * Lc)).re :=
          mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr (le_of_lt hc))
        have h2 : c⁻¹ * (c * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖)
            = ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ := by
          field_simp
        calc (Work.LinnikContract.zeroMult χ u : ℝ) * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖
            ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (c⁻¹ * (F ((s0 - u) * Lc)).re) :=
              mul_le_mul_of_nonneg_left (by rw [← h2]; exact h1) hznn
          _ = c⁻¹ * ((Work.LinnikContract.zeroMult χ u : ℝ) * (F ((s0 - u) * Lc)).re) := by ring
    · rw [if_neg hbox]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hc)) (hprod u)
  have hgfin : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) 2)) u : ℝ)) :=
    Commons.NumberTheory.Linnik.divisor_real_finiteSupport χ.primitiveCharacter hprim_ne1 (0:ℂ) 2
  have hgfinF : (Function.support (fun u : ℂ =>
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) 2)) u : ℝ))).Finite := hgfin
  set S : Finset ℂ := Set.Finite.toFinset hgfinF with hS
  have hsl : Function.support (fun u : ℂ =>
      if Work.LinnikContract.InBox q R u then
        (Work.LinnikContract.zeroMult χ u : ℝ) * ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ else 0)
      ⊆ (↑S : Set ℂ) := by
    rw [Function.support_subset_iff]
    intro u hfu
    rw [hS, Set.Finite.coe_toFinset hgfinF, Function.mem_support]
    by_cases hbox : Work.LinnikContract.InBox q R u
    · have hpr : (Work.LinnikContract.zeroMult χ u : ℝ) *
          ‖Work.LinnikContract.F2 K ((1 - u) * Lc)‖ ≠ 0 := by
        rwa [if_pos hbox] at hfu
      have hz : Work.LinnikContract.zeroMult χ u ≠ 0 := by
        intro h
        exact hpr (by rw [h]; ring)
      obtain ⟨-, -, hgg⟩ := hbox_facts u hbox hz
      rw [hgg]; exact_mod_cast hz
    · rw [if_neg hbox] at hfu; exact absurd rfl hfu
  have hsr : Function.support (fun u : ℂ =>
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) 2)) u : ℝ) *
        (if ‖(1:ℂ) - u‖ ≤ δ then (F ((s0 - u) * Lc)).re else 0))
      ⊆ (↑S : Set ℂ) := by
    rw [Function.support_subset_iff]
    intro u hru
    rw [hS, Set.Finite.coe_toFinset hgfinF, Function.mem_support]
    intro hgz
    exact hru (by rw [hgz, zero_mul])
  rw [finsum_eq_sum_of_support_subset _ hsl, finsum_eq_sum_of_support_subset _ hsr]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  exact hpt u

end Work.LinnikAreas.A5
