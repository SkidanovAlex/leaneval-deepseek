import Mathlib

/-!
# Auxiliary cutoffs for the Fourier–Mellin separation `separation_ineq`

This file provides the (concrete) smooth cutoffs used in the proof of
`Work.FIArea4.Vflip.separation_ineq`:

* `sepRho a b` — a smooth trapezoid on the `v`-line, equal to `1` on `[a², b²]` and
  vanishing outside `[a²/4, 4b²]`;
* `sepPhi a b ξ = sepRho a b (ξ²)` — the *even* cutoff on `ℝ`, equal to `1` for `|ξ| ∈ [a,b]`
  and vanishing for `|ξ| ≤ a/2` or `|ξ| ≥ 2b` (this is the cutoff `g` of the Friedlander–Iwaniec
  Fourier–Mellin separation);
* `sepA a b α ξ = |ξ|^{iα} · sepPhi a b ξ` — the chirped cutoff whose Fourier transform
  realises the additive character expansion of `|x|^{iα}` on `a ≤ |x| ≤ b`;
* `sepG ψ t = 𝓕 (ψ ∘ exp) t` — the Mellin transform of `ψ` on the critical line, expressed as the
  Fourier transform of `ψ(e^·)`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip

noncomputable section

/-- A smooth trapezoid on the `v`-line: `1` on `[a², b²]`, vanishing for `v ≤ a²/4` and `v ≥ 4b²`. -/
def sepRho (a b v : ℝ) : ℝ :=
  Real.smoothTransition ((4 * v - a ^ 2) / (3 * a ^ 2)) *
    Real.smoothTransition ((4 * b ^ 2 - v) / (3 * b ^ 2))

/-- The even smooth cutoff `Φ(ξ) = ρ(ξ²)`: `1` for `|ξ| ∈ [a,b]`, vanishing for `|ξ| ≤ a/2`
and for `|ξ| ≥ 2b`. -/
def sepPhi (a b ξ : ℝ) : ℝ := sepRho a b (ξ ^ 2)

/-- The chirped cutoff `A_α(ξ) = |ξ|^{iα} Φ(ξ)`. -/
def sepA (a b α : ℝ) : ℝ → ℂ :=
  fun ξ => Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I) * (sepPhi a b ξ : ℂ)

/-- The Fourier/Mellin transform of `ψ` on the critical line, as the Fourier transform of `ψ(e^·)`. -/
def sepG (ψ : ℝ → ℝ) : ℝ → ℂ := 𝓕 (fun u : ℝ => (ψ (Real.exp u) : ℂ))

section Basics

variable {a b : ℝ}

lemma sepRho_nonneg (a b v : ℝ) : 0 ≤ sepRho a b v :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma sepRho_le_one (a b v : ℝ) : sepRho a b v ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma sepRho_eq_one {a b v : ℝ} (ha : 0 < a) (h1 : a ^ 2 ≤ v) (h2 : v ≤ b ^ 2) :
    sepRho a b v = 1 := by
  have ha2 : 0 < 3 * a ^ 2 := by positivity
  have hb2 : 0 < 3 * b ^ 2 := by
    have : 0 < b ^ 2 := by nlinarith
    linarith
  have hA : 1 ≤ (4 * v - a ^ 2) / (3 * a ^ 2) := by
    rw [le_div_iff₀ ha2]; linarith
  have hB : 1 ≤ (4 * b ^ 2 - v) / (3 * b ^ 2) := by
    rw [le_div_iff₀ hb2]; linarith
  rw [sepRho, Real.smoothTransition.one_of_one_le hA, Real.smoothTransition.one_of_one_le hB,
    mul_one]

lemma sepRho_eq_zero_of_le {a b v : ℝ} (h : v ≤ a ^ 2 / 4) : sepRho a b v = 0 := by
  have hnum : 4 * v - a ^ 2 ≤ 0 := by linarith
  have hden : (0 : ℝ) ≤ 3 * a ^ 2 := by positivity
  have hquot : (4 * v - a ^ 2) / (3 * a ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hden
  rw [sepRho, Real.smoothTransition.zero_of_nonpos hquot, zero_mul]

lemma sepRho_eq_zero_of_ge {a b v : ℝ} (h : 4 * b ^ 2 ≤ v) : sepRho a b v = 0 := by
  have hnum : 4 * b ^ 2 - v ≤ 0 := by linarith
  have hden : (0 : ℝ) ≤ 3 * b ^ 2 := by positivity
  have hquot : (4 * b ^ 2 - v) / (3 * b ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hden
  rw [sepRho, Real.smoothTransition.zero_of_nonpos hquot, mul_zero]

lemma contDiff_sepRho (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sepRho a b) := by
  unfold sepRho
  fun_prop

lemma contDiff_sepPhi (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sepPhi a b) := by
  unfold sepPhi
  exact (contDiff_sepRho a b).comp (by fun_prop)

lemma sepPhi_nonneg (a b ξ : ℝ) : 0 ≤ sepPhi a b ξ := sepRho_nonneg a b _

lemma sepPhi_le_one (a b ξ : ℝ) : sepPhi a b ξ ≤ 1 := sepRho_le_one a b _

lemma sepPhi_even (a b ξ : ℝ) : sepPhi a b (-ξ) = sepPhi a b ξ := by
  simp only [sepPhi, neg_sq]

lemma sepPhi_eq_one {a b ξ : ℝ} (ha : 0 < a) (hab : a ≤ b) (h1 : a ≤ |ξ|) (h2 : |ξ| ≤ b) :
    sepPhi a b ξ = 1 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs1 : a ^ 2 ≤ ξ ^ 2 := by
    have h := pow_le_pow_left₀ ha.le h1 2
    rwa [sq_abs] at h
  have hs2 : ξ ^ 2 ≤ b ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg ξ) h2 2
    rwa [sq_abs] at h
  rw [sepPhi]
  exact sepRho_eq_one ha hs1 hs2

lemma sepPhi_eq_zero_of_abs_le {a b ξ : ℝ} (h : |ξ| ≤ a / 2) : sepPhi a b ξ = 0 := by
  have hs : ξ ^ 2 ≤ a ^ 2 / 4 := by
    have h' := pow_le_pow_left₀ (abs_nonneg ξ) h 2
    rw [sq_abs] at h'
    nlinarith
  rw [sepPhi]
  exact sepRho_eq_zero_of_le hs

lemma sepPhi_eq_zero_of_abs_ge {a b ξ : ℝ} (h : 2 * |b| ≤ |ξ|) : sepPhi a b ξ = 0 := by
  have hs : 4 * b ^ 2 ≤ ξ ^ 2 := by
    have h' := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * |b|) h 2
    rw [sq_abs, mul_pow, sq_abs] at h'
    nlinarith
  rw [sepPhi]
  exact sepRho_eq_zero_of_ge hs

lemma sepPhi_support {a b ξ : ℝ} (_ha : 0 < a) (h : sepPhi a b ξ ≠ 0) :
    a / 2 ≤ |ξ| ∧ |ξ| ≤ 2 * |b| := by
  constructor
  · by_contra hc
    exact h (sepPhi_eq_zero_of_abs_le (le_of_lt (not_le.mp hc)))
  · by_contra hc
    exact h (sepPhi_eq_zero_of_abs_ge (le_of_lt (not_le.mp hc)))

lemma hasCompactSupport_sepPhi (a b : ℝ) : HasCompactSupport (sepPhi a b) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * |b|)) (2 * |b|))
    isCompact_Icc ?_
  rw [Function.support_subset_iff]
  intro ξ hξ
  rw [Set.mem_Icc, ← abs_le]
  by_contra hc
  exact hξ (sepPhi_eq_zero_of_abs_ge (le_of_lt (not_le.mp hc)))

end Basics

section DerivBounds

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
lemma iteratedDeriv_two_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_eq_iterate, Function.iterate_succ]
  norm_num [Function.iterate_one, Function.comp_def]

/-- Bounds for `Φ = sepPhi`, its first and second derivative (over all of `ℝ`). -/
theorem sepPhi_deriv_bounds (a b : ℝ) :
    ∃ A B C : ℝ, 0 < A ∧ 0 ≤ B ∧ 0 ≤ C ∧
      (∀ ξ, |sepPhi a b ξ| ≤ A) ∧
      (∀ ξ, |deriv (sepPhi a b) ξ| ≤ B) ∧
      (∀ ξ, |deriv (deriv (sepPhi a b)) ξ| ≤ C) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (sepPhi a b) := contDiff_sepPhi a b
  have hcs : HasCompactSupport (sepPhi a b) := hasCompactSupport_sepPhi a b
  have h1 : Continuous (deriv (sepPhi a b)) := hcd.continuous_deriv (by simp)
  have h2 : Continuous (deriv (deriv (sepPhi a b))) := by
    rw [← iteratedDeriv_two_eq]
    exact hcd.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)
  have hs2 : HasCompactSupport (deriv (deriv (sepPhi a b))) := by
    rw [← iteratedDeriv_two_eq, iteratedDeriv_eq_equiv_comp]
    exact (hcs.iteratedFDeriv (𝕜 := ℝ) 2).comp_left (map_zero _)
  obtain ⟨A₀, hA₀⟩ := hcs.exists_bound_of_continuous hcd.continuous
  obtain ⟨B₀, hB₀⟩ := hcs.deriv.exists_bound_of_continuous h1
  obtain ⟨C₀, hC₀⟩ := hs2.exists_bound_of_continuous h2
  refine ⟨|A₀| + 1, |B₀|, |C₀|, by positivity, abs_nonneg _, abs_nonneg _, ?_, ?_, ?_⟩
  · intro ξ
    have h := hA₀ ξ
    rw [Real.norm_eq_abs] at h
    linarith [abs_nonneg A₀, le_abs_self A₀]
  · intro ξ
    have h := hB₀ ξ
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self B₀]
  · intro ξ
    have h := hC₀ ξ
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self C₀]

end DerivBounds

section SepA

variable {a b α : ℝ}

lemma contDiffAt_log_abs {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => Real.log |ξ|) x := by
  rcases lt_or_gt_of_ne hx.symm with hpos | hneg
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => Real.log ξ) x :=
      Real.contDiffAt_log.mpr hx
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hpos] with ξ hξ
    rw [abs_of_pos hξ]
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => Real.log (-ξ)) x :=
      (Real.contDiffAt_log.mpr (by linarith : -x ≠ 0)).comp x
        (by fun_prop : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => -ξ) x)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Iio hneg] with ξ hξ
    rw [abs_of_neg hξ]

lemma contDiff_sepA (a b α : ℝ) (ha : 0 < a) : ContDiff ℝ (⊤ : ℕ∞) (sepA a b α) := by
  refine contDiff_iff_contDiffAt.mpr (fun ξ => ?_)
  have ha2 : (0:ℝ) < a / 2 := by linarith
  rcases lt_or_ge |ξ| (a / 2) with hlt | hge
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (abs_lt.mp hlt)] with ξ' hξ'
    rw [sepA, sepPhi_eq_zero_of_abs_le (le_of_lt (abs_lt.mpr hξ'))]
    simp
  · have hξ : ξ ≠ 0 := by
      intro h; rw [h, abs_zero] at hge; linarith
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => Real.log |ξ|) ξ := contDiffAt_log_abs hξ
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((Real.log |ξ| : ℝ) : ℂ)) ξ :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt ξ h1
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (α * Real.log |ξ| : ℝ)) ξ :=
      (contDiffAt_const (c := α)).mul h1
    have h4 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun ξ : ℝ => ((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I) ξ := by
      have h6 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((α * Real.log |ξ| : ℝ) : ℂ)) ξ :=
        Complex.ofRealCLM.contDiff.comp_contDiffAt ξ hlog
      exact h6.mul (contDiffAt_const (c := Complex.I))
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun ξ : ℝ => Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I)) ξ := h4.cexp
    have h5 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (sepPhi a b ξ : ℂ)) ξ :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt ξ (contDiff_sepPhi a b).contDiffAt
    refine (h2.mul h5).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ξ => ?_)
    rw [sepA]

theorem hasCompactSupport_sepA (a b α : ℝ) (ha : 0 < a) : HasCompactSupport (sepA a b α) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * |b|)) (2 * |b|))
    isCompact_Icc ?_
  rw [Function.support_subset_iff]
  intro ξ hξ
  rw [Set.mem_Icc, ← abs_le]
  have hphi : sepPhi a b ξ ≠ 0 := by
    intro h
    exact hξ (by rw [sepA, h]; simp)
  exact (sepPhi_support ha hphi).2

lemma norm_exp_chirp (α : ℝ) (ξ : ℝ) :
    ‖Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma norm_sepA_le (a b α : ℝ) (ξ : ℝ) : ‖sepA a b α ξ‖ ≤ 1 := by
  rw [sepA, norm_mul, norm_exp_chirp, one_mul]
  have h2 : ‖(sepPhi a b ξ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sepPhi_nonneg a b ξ)]
    exact sepPhi_le_one a b ξ
  exact h2

end SepA

end

end Work.FIArea4.Vflip
