import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open Complex DirichletCharacter Metric
open scoped BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Weighted zero-sum bound in a height window

For a primitive, non-trivial Dirichlet character `χ mod N`, the sum
`∑_ρ m(ρ) x^ρ/ρ`, taken over the zeros `ρ` of the completed L-function
`Λ(s) = completedLFunction χ s` whose height `|Im ρ|` lies in a window `(T, T']`
(`m(ρ)` the vanishing order), is bounded by

`c * (x/T) * (T' - T + 2) * (log (N (T' + 3)) + log N + 2)`.

This is a crude but unconditional bound: every zero of `Λ` lies in the critical strip
(`zerosInStrip`), so `|x^ρ/ρ| ≤ x/T` for a zero of height `> T ≥ 2`, and the number of
zeros of height in `(T, T']` is controlled by the (log-free) zero count
`windowZeroCountC`.
-/

private lemma cpow_norm_ofReal (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ = x ^ s.re := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.norm_exp]
  have h1 : (Complex.log (x : ℂ) * s).re = Real.log x * s.re := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le,
      Complex.norm_of_nonneg hx.le]
    ring
  rw [h1, Real.rpow_def_of_pos hx]

private lemma divisor_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg]
    intro h
    exact hz h.2

private lemma divisor_real_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U z : ℤ) : ℝ) := by
  exact_mod_cast divisor_nonneg_of_analyticOnNhd hf

private lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]
      simp
    rw [h2, ← hn]
    simp

private lemma completedLFunction_analyticOnNhd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := by
  intro z hz
  exact (differentiable_completedLFunction hχ).analyticAt z

/-- The norm of a `finsum` of complex numbers is bounded by the `finsum` of the norms,
whenever the summand has finite support. -/
private lemma norm_finsum_le_of_finite {f : ℂ → ℂ} (hf : Function.HasFiniteSupport f) :
    ‖∑ᶠ z : ℂ, f z‖ ≤ ∑ᶠ z : ℂ, ‖f z‖ := by
  classical
  have hf_fin : (Function.support f).Finite := hf
  have hf'_fin : (Function.support (fun z : ℂ => ‖f z‖)).Finite := by
    rwa [show Function.support (fun z : ℂ => ‖f z‖) = Function.support f from by
      ext z; simp [Function.mem_support]]
  have hf' : Function.HasFiniteSupport (fun z : ℂ => ‖f z‖) := hf'_fin
  let s : Finset ℂ := hf_fin.toFinset
  have hfs : Function.support f ⊆ (s : Set ℂ) := by
    intro z hz
    rw [Finset.mem_coe, show s = hf_fin.toFinset from rfl, Set.Finite.mem_toFinset hf_fin]
    exact hz
  have hfs' : Function.support (fun z : ℂ => ‖f z‖) ⊆ (s : Set ℂ) := by
    intro z hz
    rw [Finset.mem_coe, show s = hf_fin.toFinset from rfl, Set.Finite.mem_toFinset hf_fin]
    rw [Function.mem_support] at hz ⊢
    exact fun h => hz (by rw [h, norm_zero])
  rw [finsum_eq_sum_of_support_subset f hfs,
    finsum_eq_sum_of_support_subset (fun z : ℂ => ‖f z‖) hfs']
  exact norm_sum_le _ _

theorem zerosInWindow_weighted_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → ∀ T' : ℝ, T ≤ T' →
      ‖∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
        (if T < |ρ.im| ∧ |ρ.im| ≤ T' then (x : ℂ) ^ ρ / ρ else 0)‖ ≤
        c * (x / T) * (T' - T + 2) * (Real.log (N * (T' + 3)) + Real.log (N : ℝ) + 2) := by
  classical
  obtain ⟨c0, hc0pos, hcount⟩ := windowZeroCountC χ hχ hχprim
  refine ⟨c0, hc0pos, ?_⟩
  intro x hx T hT T' hTT'
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hxT_nonneg : 0 ≤ x / T := div_nonneg (le_of_lt hxpos) (le_of_lt hTpos)
  -- finiteness of the divisor support on the covering disc
  have hfinDiv : (Function.support (fun u : ℂ =>
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (T' + 1)) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (T' + 1))).finiteSupport (isCompact_closedBall (0 : ℂ) (T' + 1)))
  let D : Finset ℂ := hfinDiv.toFinset
  have hDfin : ((D : Set ℂ)).Finite := by
    simpa only [D, Set.Finite.coe_toFinset hfinDiv] using hfinDiv
  have memD : ∀ u : ℂ, u ∈ D ↔
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (T' + 1)) u : ℤ) ≠ 0 := by
    intro u
    simp only [D, Set.Finite.mem_toFinset hfinDiv, Function.mem_support]
  let Z : ℂ → ℂ := fun ρ =>
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
        (if T < |ρ.im| ∧ |ρ.im| ≤ T' then (x : ℂ) ^ ρ / ρ else 0)
  let dw : ℂ → ℝ := fun u =>
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (T' + 1)) u : ℤ) : ℝ) *
        (if T ≤ |u.im| ∧ |u.im| ≤ T' then 1 else 0)
  -- zeros in the window lie in the disc of radius `T' + 1`
  have mem_disc : ∀ u : ℂ, T < |u.im| ∧ |u.im| ≤ T' →
      DirichletCharacter.completedLFunction χ u = 0 →
      u ∈ Metric.closedBall (0 : ℂ) (T' + 1) := by
    intro u hind hΛu
    have hstrip := zerosInStrip χ hχ hχprim u hΛu
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ 1 + T' := by
          have hre : |u.re| ≤ 1 := by
            rw [abs_of_pos hstrip.1]; linarith [hstrip.2]
          linarith [hre, hind.2]
      _ = T' + 1 := by ring
  -- support of `Z` is contained in `D`
  have hsubZ : Function.support Z ⊆ (D : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, memD]
    by_cases hind : T < |u.im| ∧ |u.im| ≤ T'
    · have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
        intro h0
        apply hu
        simp only [Z, if_pos hind, h0, Nat.cast_zero, zero_mul]
      have hΛu : DirichletCharacter.completedLFunction χ u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hmem := mem_disc u hind hΛu
      have hdiv := divisor_eq_analyticOrderNatAt
        (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (T' + 1))) hmem
      rw [hdiv]
      intro hcast
      exact hord (by exact_mod_cast hcast)
    · exfalso
      apply hu
      simp only [Z, if_neg hind, mul_zero]
  -- support of `dw` is contained in `D`
  have hsubdw : Function.support dw ⊆ (D : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, memD]
    intro hdiv0
    apply hu
    simp only [dw, hdiv0, Int.cast_zero, zero_mul]
  have hZfin : Function.HasFiniteSupport Z := hDfin.subset hsubZ
  have hdwfin : Function.HasFiniteSupport dw := hDfin.subset hsubdw
  have hnf : Function.HasFiniteSupport (fun ρ : ℂ => ‖Z ρ‖) := by
    rw [Function.HasFiniteSupport]
    rw [show Function.support (fun ρ : ℂ => ‖Z ρ‖) = Function.support Z from by
      ext z; simp [Function.mem_support]]
    exact hZfin
  have hsubW : Function.support (fun ρ : ℂ => (x / T) * dw ρ) ⊆ (D : Set ℂ) := by
    intro u hu
    apply hsubdw
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0, mul_zero])
  have hWfin : Function.HasFiniteSupport (fun ρ : ℂ => (x / T) * dw ρ) := hDfin.subset hsubW
  -- pointwise bound of the complex summand by `(x/T) * dw`
  have hpoint : ∀ u : ℂ, ‖Z u‖ ≤ (x / T) * dw u := by
    intro u
    have hdw_nonneg : 0 ≤ dw u := by
      simp only [dw]
      apply mul_nonneg
      · exact divisor_real_nonneg_of_analyticOnNhd
          (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (T' + 1)))
      · split_ifs <;> norm_num
    by_cases hind : T < |u.im| ∧ |u.im| ≤ T'
    · by_cases hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0
      · rw [show Z u = 0 by simp only [Z, if_pos hind, hord, Nat.cast_zero, zero_mul],
          norm_zero]
        exact mul_nonneg hxT_nonneg hdw_nonneg
      · have hΛu : DirichletCharacter.completedLFunction χ u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
        have hstrip := zerosInStrip χ hχ hχprim u hΛu
        have hmem := mem_disc u hind hΛu
        have hdivu := divisor_eq_analyticOrderNatAt
          (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (T' + 1))) hmem
        have hdw_eq : dw u =
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) := by
          simp only [dw, hdivu]
          have hw : (if T ≤ |u.im| ∧ |u.im| ≤ T' then (1 : ℝ) else 0) = 1 := by
            rw [if_pos]; exact ⟨le_of_lt hind.1, hind.2⟩
          rw [hw, mul_one]
          simp
        have hZval : Z u =
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) *
              ((x : ℂ) ^ u / u) := by
          simp only [Z, if_pos hind]
        rw [hZval, hdw_eq]
        have hnorm :
            ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) *
                ((x : ℂ) ^ u / u)‖ =
              (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
                (x ^ u.re / ‖u‖) := by
          rw [norm_mul, Complex.norm_natCast, Complex.norm_div, cpow_norm_ofReal x hxpos]
        rw [hnorm]
        have hmain : x ^ u.re / ‖u‖ ≤ x / T := by
          refine div_le_div₀ (le_of_lt hxpos) ?_ hTpos ?_
          · have h2 := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hstrip.2)
            rwa [Real.rpow_one] at h2
          · have h1 : T < |u.im| := hind.1
            have h2 : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
            linarith
        have hcoef : (0 : ℝ) ≤
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) := by
          positivity
        calc (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
                (x ^ u.re / ‖u‖)
            ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
                (x / T) := mul_le_mul_of_nonneg_left hmain hcoef
          _ = (x / T) *
                (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) := by ring
    · rw [show Z u = 0 by simp only [Z, if_neg hind, mul_zero], norm_zero]
      exact mul_nonneg hxT_nonneg hdw_nonneg
  -- the zero count
  have hcnt : ∑ᶠ ρ : ℂ, dw ρ ≤
      c0 * (T' - T + 2) * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) := by
    have h := hcount T T' hT1 hTT'
    simpa only [dw] using h
  -- comparison of the logarithmic factors
  have hL1LT : Real.log (T' + 3) + Real.log (N : ℝ) + 2 ≤
      Real.log (N * (T' + 3)) + Real.log (N : ℝ) + 2 := by
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hT'3ne : (T' + 3 : ℝ) ≠ 0 := by linarith
    rw [Real.log_mul (ne_of_gt hNpos) hT'3ne]
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    linarith
  have hba2 : 0 ≤ T' - T + 2 := by linarith
  have hstep2 : c0 * (T' - T + 2) * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) ≤
      c0 * (T' - T + 2) * (Real.log (N * (T' + 3)) + Real.log (N : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hL1LT (mul_nonneg (le_of_lt hc0pos) hba2)
  calc ‖∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
        (if T < |ρ.im| ∧ |ρ.im| ≤ T' then (x : ℂ) ^ ρ / ρ else 0)‖
      = ‖∑ᶠ ρ : ℂ, Z ρ‖ := rfl
    _ ≤ ∑ᶠ ρ : ℂ, ‖Z ρ‖ := norm_finsum_le_of_finite hZfin
    _ ≤ ∑ᶠ ρ : ℂ, (x / T) * dw ρ :=
        finsum_le_finsum' hnf hWfin (fun ρ => hpoint ρ)
    _ = (x / T) * ∑ᶠ ρ : ℂ, dw ρ := (mul_finsum' dw (x / T) hdwfin).symm
    _ ≤ (x / T) * (c0 * (T' - T + 2) *
          (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hcnt hxT_nonneg
    _ ≤ (x / T) * (c0 * (T' - T + 2) *
          (Real.log (N * (T' + 3)) + Real.log (N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hstep2 hxT_nonneg
    _ = c0 * (x / T) * (T' - T + 2) *
          (Real.log (N * (T' + 3)) + Real.log (N : ℝ) + 2) := by ring

end Commons.NumberTheory.DirichletCharacter
