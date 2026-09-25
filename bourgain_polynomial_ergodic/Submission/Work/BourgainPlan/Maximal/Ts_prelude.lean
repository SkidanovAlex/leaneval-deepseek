import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_decay
import Submission.Work.BourgainPlan.Maximal.Ts_fourierDeps
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.mstThetaOp_fourierInv_multiplier_ae
import Submission.Commons.Analysis.Fourier.separated_real_line_bandpass_maximal_l2
import Submission.Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite

/-!
# `L²` decay of the dyadic Littlewood–Paley block `T_s` (step 3 of `Maximal/DRDF_ROUTE.md`)

Target (the assignment): for a polynomial `P : Polynomial ℤ` of degree `d = P.natDegree ≥ 2`,

`‖∑_{k<K} S̃_{dk+s}(ε_k · S_{dk+s}(D_k h))‖₂ ≤ C · 2^{-|s|/d} ‖h‖₂`,

uniformly in `K`, the signs `‖ε_k‖ ≤ 1`, the shift `s ∈ ℤ` and `h ∈ L²(ℝ)`, where
`D_k = σ_{2^k} - σ_{2^{k+1}}` is the dyadic difference of the curve averages
`σ_N h(x) = ∫₀¹ h(x - P(N t)) dt` and `S_l`, `S̃_l` are the Littlewood–Paley multipliers with
symbols `ψ(2^l ·)`, `ψ̃(2^l ·)`.

The mathematical content is the classical one: the symbol of `D_k` is
`μ_k = conj(Φ_{2^k}) - conj(Φ_{2^{k+1}})` (`Φ_N = polyProfile P N`, the van der Corput profile),
which on the support `{1/2 ≤ |2^{dk+s}ξ| ≤ 2}` of `ψ(2^{dk+s}·)` is `≲ 2^{-|s|/d}` (small `ξ`:
first-order Taylor; large `ξ`: van der Corput), and at most two of the lacunary bands overlap at
any frequency.  Plancherel then gives the decay.

The formalisation splits the identity `𝓕(D_k h) = μ_k · 𝓕 h` through the `L²` multiplier calculus
(`BoundaryLayer.multiplier`) of the corpus: `σ_N` *is* the multiplier with symbol `conj Φ_N`
(`curveSigma_eq_multiplier`), and a `L¹`-input `𝓕⁻(m · 𝓕 g)` is either `0` (junk value, when
`g ∉ L¹`) or the multiplier with symbol `m` (`dyadicProj_dichotomy`).

## Contents

* `polyProfile_sub_one_bound` — the small-frequency Taylor bound `‖Φ_N(β) - 1‖ ≤ C|β|N^d`.
* `dyadPsi_support` — `supp ψ ⊆ {1/2 ≤ |·| ≤ 2}`.
* `muSym_bound_window` — `‖μ_k(ξ)‖ ≤ C 2^{-|s|/d}` on the band `{1/2 ≤ |2^{dk+s}ξ| ≤ 2}`.
* `card_support_le_two` — at most two lacunary bands meet a given frequency.
* `Ts_symbol_bound` — the pointwise bound on the full symbol.
* `dyadicProj_dichotomy` — the junk/multiplier dichotomy for `𝓕⁻(m · 𝓕 g)`.
* `curveSigma_eq_multiplier` — the multiplier of the curve average.
* `Ts_l2_decay` — the target.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory MeasureTheory.Measure FourierTransform Filter
open scoped ENNReal BigOperators Topology

noncomputable section

/-- `‖e^{2πiy} - 1‖ ≤ 4π|y|` for real `y`. -/
lemma norm_exp_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ:ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  rcases le_or_gt |θ| 1 with h | h
  · have hx : ‖(θ:ℂ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]; exact h
    have := Complex.norm_exp_sub_one_le hx
    rwa [norm_mul, Complex.norm_I, mul_one, Complex.norm_real] at this
  · have h2 : ‖Complex.exp ((θ:ℂ) * Complex.I) - 1‖ ≤ 2 := by
      calc ‖Complex.exp ((θ:ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp ((θ:ℂ) * Complex.I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
    nlinarith [abs_nonneg θ]

lemma norm_exp_two_pi_I_sub_one (y : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) - 1‖ ≤ 4 * Real.pi * |y| := by
  have harg : (2 * Real.pi * Complex.I * (y : ℂ)) = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg]
  have h := norm_exp_I_sub_one_le (2 * Real.pi * y)
  have h2 : |2 * Real.pi * y| = 2 * Real.pi * |y| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h2] at h
  linarith

/-- Polynomials grow at most like `N^deg`. -/
lemma eval_toRealPoly_bound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (s : ℝ), 1 ≤ N → s ∈ Set.Icc (0:ℝ) 1 →
      |(toRealPoly P).eval ((N : ℝ) * s)| ≤ C * (N : ℝ) ^ P.natDegree := by
  set d := P.natDegree with hd
  refine ⟨(∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)|) + 1, by positivity, ?_⟩
  intro N s hN hs
  set u : ℝ := (N : ℝ) * s with hu
  have hu_nonneg : 0 ≤ u := mul_nonneg (Nat.cast_nonneg N) hs.1
  have hu_le : u ≤ (N : ℝ) := by
    rw [hu]; nlinarith [hs.2, Nat.cast_nonneg (α := ℝ) N]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hnd : (toRealPoly P).natDegree ≤ d := by
    rw [hd, toRealPoly]; exact Polynomial.natDegree_map_le
  have hd_lt : (toRealPoly P).natDegree < d + 1 := Nat.lt_succ_of_le hnd
  rw [Polynomial.eval_eq_sum_range' hd_lt u]
  have hcoeff : ∀ i, (toRealPoly P).coeff i = ((P.coeff i : ℤ) : ℝ) := fun i => by
    rw [toRealPoly, Polynomial.coeff_map]; rfl
  calc |∑ i ∈ Finset.range (d + 1), (toRealPoly P).coeff i * u ^ i|
      ≤ ∑ i ∈ Finset.range (d + 1), |(toRealPoly P).coeff i * u ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)| * |u| ^ i := by
        apply Finset.sum_congr rfl; intro i hi
        rw [hcoeff i, abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)| * (N : ℝ) ^ d := by
        apply Finset.sum_le_sum; intro i hi
        have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : |u| ^ i ≤ (N : ℝ) ^ i :=
          pow_le_pow_left₀ (abs_nonneg u) (by rw [abs_of_nonneg hu_nonneg]; exact hu_le) i
        have h2 : (N : ℝ) ^ i ≤ (N : ℝ) ^ d := pow_le_pow_right₀ hN1 hi_le
        exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)|) * (N : ℝ) ^ d := by
        rw [Finset.sum_mul]
    _ ≤ ((∑ i ∈ Finset.range (d + 1), |((P.coeff i : ℤ) : ℝ)|) + 1) * (N : ℝ) ^ d := by
        have : (0:ℝ) ≤ (N : ℝ) ^ d := by positivity
        nlinarith

/-- **The profile at small frequency is close to `1`**: `‖Φ_N(β) - 1‖ ≤ C |β| N^d`. -/
lemma polyProfile_sub_one_bound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ β : ℝ,
      ‖polyProfile P N β - 1‖ ≤ C * (|β| * (N : ℝ) ^ P.natDegree) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := eval_toRealPoly_bound P
  refine ⟨4 * Real.pi * C₀ + 1, by positivity, ?_⟩
  intro N hN β
  set E : ℝ → ℂ := fun s => Complex.exp (2 * Real.pi * Complex.I *
    (((β * (toRealPoly P).eval ((N : ℝ) * s)) : ℝ) : ℂ)) with hE
  have hcont : Continuous E := by
    rw [hE]; fun_prop
  have hEeq : ∀ s : ℝ, E s = Complex.exp (2 * Real.pi * Complex.I *
    (((β * (toRealPoly P).eval ((N : ℝ) * s)) : ℝ) : ℂ)) := fun s => rfl
  have hrepr : polyProfile P N β - 1 = ∫ s in (0:ℝ)..1, (E s - 1) := by
    have h3 : (∫ s in (0:ℝ)..1, (E s - 1)) = (∫ s in (0:ℝ)..1, E s) - 1 := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable (0:ℝ) 1)
        (continuous_const.intervalIntegrable (0:ℝ) 1)]
      simp
    rw [h3]
    rfl
  rw [hrepr]
  have hA : (0:ℝ) ≤ |β| * (N : ℝ) ^ P.natDegree :=
    mul_nonneg (abs_nonneg β) (pow_nonneg (Nat.cast_nonneg N) _)
  have hbd : ∀ s ∈ Set.uIoc (0:ℝ) 1, ‖E s - 1‖ ≤ 4 * Real.pi * (C₀ * (|β| * (N : ℝ) ^ P.natDegree)) := by
    intro s hs
    have hsIoc : s ∈ Set.Ioc (0:ℝ) 1 := by
      rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hsIoc.1, hsIoc.2⟩
    have h1 := norm_exp_two_pi_I_sub_one (β * (toRealPoly P).eval ((N : ℝ) * s))
    have h2 := hC₀ N s hN hs'
    have h3 : |β * (toRealPoly P).eval ((N : ℝ) * s)| ≤ |β| * (C₀ * (N : ℝ) ^ P.natDegree) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
    calc ‖E s - 1‖
        = ‖Complex.exp (2 * Real.pi * Complex.I * (((β * (toRealPoly P).eval ((N : ℝ) * s)) : ℝ) : ℂ)) - 1‖ := by
          rw [hEeq s]
      _ ≤ 4 * Real.pi * |β * (toRealPoly P).eval ((N : ℝ) * s)| := h1
      _ ≤ 4 * Real.pi * (|β| * (C₀ * (N : ℝ) ^ P.natDegree)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 * Real.pi * (C₀ * (|β| * (N : ℝ) ^ P.natDegree)) := by ring
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hbd
  rw [show |(1:ℝ) - 0| = 1 by norm_num, mul_one] at hmain
  refine le_trans hmain ?_
  have hC₀' : 0 < 4 * Real.pi * C₀ := by positivity
  nlinarith [hA, hC₀']

/-! ## The symbol `μ_k` of the dyadic difference `D_k` -/

/-- The symbol of `D_k = σ_{2^k} - σ_{2^{k+1}}`: `μ_k = conj(Φ_{2^k}) - conj(Φ_{2^{k+1}})`. -/
noncomputable def muSym (P : Polynomial ℤ) (k : ℕ) : ℝ → ℂ :=
  fun ξ => starRingEnd ℂ (polyProfile P (2^k) ξ)
    - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)

/-- `supp ψ ⊆ {1/2 ≤ |·| ≤ 2}`. -/
lemma dyadPsi_support {ξ : ℝ} (h : dyadPsi ξ ≠ 0) : (1:ℝ)/2 ≤ |ξ| ∧ |ξ| ≤ 2 := by
  have h1 : ∀ η : ℝ, |η| ≤ 1 → dyadTheta η = 1 := fun η hη => dyadTheta_spec.2.2.1 η hη
  have h2 : ∀ η : ℝ, 2 ≤ |η| → dyadTheta η = 0 := fun η hη => dyadTheta_spec.2.2.2.1 η hη
  constructor
  · by_contra hc
    push_neg at hc
    apply h
    have h2ξ : |2 * ξ| ≤ 1 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    simp only [dyadPsi, h1 ξ (by linarith), h1 (2*ξ) h2ξ, sub_self]
  · by_contra hc
    push_neg at hc
    apply h
    have h2ξ : 2 ≤ |2 * ξ| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    simp only [dyadPsi, h2 ξ (by linarith), h2 (2*ξ) h2ξ, sub_self]

/-! ## The exponent bookkeeping `(2^k)^d = 2^{dk}` -/

lemma cast_two_pow_natDegree (P : Polynomial ℤ) (k : ℕ) :
    ((2^k : ℕ) : ℝ) ^ P.natDegree = (2:ℝ) ^ (P.natDegree * k) := by
  rw [Nat.cast_pow, ← pow_mul]
  congr 1
  ring

lemma two_pow_pow_mul (P : Polynomial ℤ) (k : ℕ) :
    ((2:ℝ)^k) ^ P.natDegree = (2:ℝ) ^ (P.natDegree * k) := by
  rw [← pow_mul]
  congr 1
  ring

lemma cast_two_pow_natDegree_succ (P : Polynomial ℤ) (k : ℕ) :
    ((2^(k+1) : ℕ) : ℝ) ^ P.natDegree
      = (2:ℝ) ^ (P.natDegree * k) * (2:ℝ) ^ P.natDegree := by
  rw [Nat.cast_pow, show ((2:ℕ):ℝ) = 2 by norm_num, ← pow_mul]
  rw [show (k + 1) * P.natDegree = P.natDegree * k + P.natDegree by ring, pow_add]

lemma star_polyProfile_sub_one (P : Polynomial ℤ) (N : ℕ) (ξ : ℝ) :
    ‖starRingEnd ℂ (polyProfile P N ξ) - 1‖ = ‖polyProfile P N ξ - 1‖ := by
  have h : starRingEnd ℂ (polyProfile P N ξ) - 1
      = starRingEnd ℂ (polyProfile P N ξ - 1) := by
    rw [map_sub, map_one]
  rw [h, Complex.norm_conj]

/-- **Small-frequency regime**: `‖μ_k(ξ)‖ ≤ C |ξ| 2^{dk}`. -/
lemma muSym_le_small (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (ξ : ℝ),
      ‖muSym P k ξ‖ ≤ C * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := polyProfile_sub_one_bound P
  refine ⟨C₀ * (1 + (2:ℝ) ^ P.natDegree), by positivity, ?_⟩
  intro k ξ
  have hk : 1 ≤ 2^k := Nat.one_le_two_pow
  have hk1 : 1 ≤ 2^(k+1) := Nat.one_le_two_pow
  have hb : (0:ℝ) ≤ |ξ| * (2:ℝ) ^ (P.natDegree * k) :=
    mul_nonneg (abs_nonneg ξ) (by positivity)
  have h1 : ‖starRingEnd ℂ (polyProfile P (2^k) ξ) - 1‖
      ≤ C₀ * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) := by
    have h := hC₀ (2^k) hk ξ
    rw [cast_two_pow_natDegree P k] at h
    rw [star_polyProfile_sub_one]
    exact h
  have h2 : ‖starRingEnd ℂ (polyProfile P (2^(k+1)) ξ) - 1‖
      ≤ C₀ * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) * (2:ℝ) ^ P.natDegree := by
    have h := hC₀ (2^(k+1)) hk1 ξ
    rw [cast_two_pow_natDegree_succ P k] at h
    rw [star_polyProfile_sub_one]
    calc ‖polyProfile P (2^(k+1)) ξ - 1‖
        ≤ C₀ * (|ξ| * ((2:ℝ) ^ (P.natDegree * k) * (2:ℝ) ^ P.natDegree)) := h
      _ = C₀ * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) * (2:ℝ) ^ P.natDegree := by ring
  have hsplit : muSym P k ξ = (starRingEnd ℂ (polyProfile P (2^k) ξ) - 1)
      - (starRingEnd ℂ (polyProfile P (2^(k+1)) ξ) - 1) := by
    simp only [muSym]; ring
  have hBD : (0:ℝ) ≤ (2:ℝ) ^ P.natDegree := by positivity
  calc ‖muSym P k ξ‖
      = ‖(starRingEnd ℂ (polyProfile P (2^k) ξ) - 1)
          - (starRingEnd ℂ (polyProfile P (2^(k+1)) ξ) - 1)‖ := by rw [hsplit]
    _ ≤ ‖starRingEnd ℂ (polyProfile P (2^k) ξ) - 1‖
          + ‖starRingEnd ℂ (polyProfile P (2^(k+1)) ξ) - 1‖ := norm_sub_le _ _
    _ ≤ C₀ * (|ξ| * (2:ℝ) ^ (P.natDegree * k))
          + C₀ * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) * (2:ℝ) ^ P.natDegree := add_le_add h1 h2
    _ ≤ (C₀ * (1 + (2:ℝ) ^ P.natDegree)) * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) := by
        nlinarith [hC₀pos, hb, hBD]

/-- **Large-frequency (van der Corput) regime**: `‖μ_k(ξ)‖ ≤ C X^{-1/d}` for `X = |ξ| 2^{dk} ≥ 1`. -/
lemma muSym_le_large (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (ξ : ℝ),
      1 ≤ |ξ| * (2:ℝ) ^ (P.natDegree * k) →
      ‖muSym P k ξ‖
        ≤ C * (|ξ| * (2:ℝ) ^ (P.natDegree * k)) ^ (-(1 / (P.natDegree : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := polyProfile_step_diff_decay P hdeg
  refine ⟨C₀, hC₀pos, ?_⟩
  intro k ξ hX
  have hX' : 1 ≤ |ξ| * ((2:ℝ)^k) ^ P.natDegree := by
    rw [two_pow_pow_mul P k]; exact hX
  have h := hC₀ k (k+1) (Nat.le_succ k) ξ hX'
  have hmu : muSym P k ξ
      = starRingEnd ℂ (polyProfile P (2^k) ξ - polyProfile P (2^(k+1)) ξ) := by
    simp only [muSym]; rw [map_sub]
  rw [hmu, Complex.norm_conj, norm_sub_rev, ← two_pow_pow_mul P k]
  exact h

/-! ## Elementary `2`-power arithmetic -/

lemma half_mul_inv_two_rpow (r : ℝ) :
    (1/2 : ℝ) * ((2:ℝ)^r)⁻¹ = (2:ℝ)^(-r-1) := by
  rw [show (2:ℝ)^(-r-1) = (2:ℝ)^(-r) * (2:ℝ)^(-(1:ℝ)) by
        rw [show (-r-1) = (-r) + (-(1:ℝ)) by ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)],
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) r,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (1:ℝ), Real.rpow_one]
  ring

lemma two_mul_inv_two_rpow (r : ℝ) : 2 * ((2:ℝ)^r)⁻¹ = (2:ℝ)^(1-r) := by
  rw [show (2:ℝ)^(1-r) = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-r) by
        rw [show (1:ℝ)-r = (1:ℝ) + (-r) by ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)],
      Real.rpow_one, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) r]

lemma mul_le_mul_const' {a b p t : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    a * t ≤ b * p * t := by
  calc a * t ≤ b * t := mul_le_mul_of_nonneg_right hab ht
    _ = b * 1 * t := by ring
    _ ≤ b * p * t := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hb) ht

lemma neg_le_neg_div {r D : ℝ} (hD : 1 ≤ D) (hr : 0 ≤ r) : -r ≤ (-r)/D := by
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD
  rw [le_div_iff₀ hDpos]
  nlinarith

/-- On the Littlewood–Paley band `{1/2 ≤ |2^{dk+s} ξ| ≤ 2}` the symbol difference `μ_k` is
`≲ 2^{-|s|/d}`: this is step 3 of `Maximal/DRDF_ROUTE.md`. -/
lemma muSym_le_window (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (s : ℤ) (ξ : ℝ),
      (1:ℝ)/2 ≤ |(2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ| →
      |(2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ| ≤ 2 →
      ‖muSym P k ξ‖ ≤ C * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) := by
  obtain ⟨Cs, hCspos, hCs⟩ := muSym_le_small P
  obtain ⟨Cl, hClpos, hCl⟩ := muSym_le_large P hdeg
  refine ⟨2 * (max Cs Cl) * (2:ℝ)^(1/(P.natDegree:ℝ)), by positivity, ?_⟩
  intro k s ξ h1 h2
  have hd1 : 1 ≤ P.natDegree := by omega
  have hDpos : (0:ℝ) < (P.natDegree:ℝ) := by positivity
  have hD1 : (1:ℝ) ≤ (P.natDegree:ℝ) := by exact_mod_cast hd1
  have he : (((P.natDegree:ℤ)*(k:ℤ)+s : ℤ) : ℝ)
      = ((P.natDegree * k : ℕ) : ℝ) + (s:ℝ) := by push_cast; ring
  have h2s : (0:ℝ) < (2:ℝ)^(s:ℝ) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have h2dk : (0:ℝ) < (2:ℝ)^(P.natDegree * k) := by positivity
  have hwin1 : (1:ℝ)/2 ≤ |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) := by
    have h := h1
    rw [← Real.rpow_intCast, he, Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_natCast, abs_mul, abs_mul, abs_of_pos h2dk, abs_of_pos h2s] at h
    rw [show (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) * |ξ|
        = |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) from by ring] at h
    exact h
  have hwin2 : |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) ≤ 2 := by
    have h := h2
    rw [← Real.rpow_intCast, he, Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_natCast, abs_mul, abs_mul, abs_of_pos h2dk, abs_of_pos h2s] at h
    rw [show (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) * |ξ|
        = |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) from by ring] at h
    exact h
  have hmul_inv : (|ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ)) * ((2:ℝ)^(s:ℝ))⁻¹
      = |ξ| * (2:ℝ)^(P.natDegree*k) := by
    rw [mul_assoc, mul_inv_cancel₀ h2s.ne', mul_one]
  have hXlo : (2:ℝ)^(-(s:ℝ) - 1) ≤ |ξ| * (2:ℝ)^(P.natDegree*k) := by
    have h := mul_le_mul_of_nonneg_right hwin1 (inv_nonneg.mpr h2s.le)
    rw [hmul_inv, half_mul_inv_two_rpow] at h
    exact h
  have hXhi : (0:ℝ) ≤ (s:ℝ) →
      |ξ| * (2:ℝ)^(P.natDegree*k) ≤ 2 * (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ)) := by
    intro hsd
    have h := mul_le_mul_of_nonneg_right hwin2 (inv_nonneg.mpr h2s.le)
    rw [hmul_inv, two_mul_inv_two_rpow] at h
    refine le_trans h ?_
    rw [show (2:ℝ)^(1-(s:ℝ)) = 2 * (2:ℝ)^(-(s:ℝ)) by
          rw [← two_mul_inv_two_rpow (s:ℝ), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (s:ℝ)]]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 2)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (neg_le_neg_div hD1 hsd)
  rcases le_or_gt (0:ℤ) s with hs | hs
  · have hsd : (0:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    have habs : |(s:ℝ)| = (s:ℝ) := abs_of_nonneg hsd
    calc ‖muSym P k ξ‖ ≤ Cs * (|ξ| * (2:ℝ)^(P.natDegree*k)) := hCs k ξ
      _ ≤ Cs * (2 * (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ))) :=
          mul_le_mul_of_nonneg_left (hXhi hsd) hCspos.le
      _ ≤ 2 * max Cs Cl * (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ)) := by
          have hCsmax : Cs ≤ max Cs Cl := le_max_left _ _
          have hp1 : (1:ℝ) ≤ (2:ℝ)^(1/(P.natDegree:ℝ)) := by
            have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
              (by positivity : (0:ℝ) ≤ 1/(P.natDegree:ℝ))
            simpa using h
          have hpos : (0:ℝ) ≤ (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ)) :=
            (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le
          have hmaxnn : (0:ℝ) ≤ max Cs Cl := le_trans hCspos.le hCsmax
          rw [show Cs * (2 * (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ)))
              = (2*Cs) * (2:ℝ)^(-(s:ℝ)/(P.natDegree:ℝ)) by ring]
          exact mul_le_mul_const' (by linarith) (by linarith) hp1 hpos
      _ = 2 * max Cs Cl * (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) := by
          rw [habs]
  · have hsd : (s:ℝ) < 0 := by exact_mod_cast hs
    have hsle : (s:ℝ) ≤ -1 := by
      have : s ≤ -1 := by omega
      exact_mod_cast this
    have habs : |(s:ℝ)| = -(s:ℝ) := abs_of_neg hsd
    have hX1 : 1 ≤ |ξ| * (2:ℝ)^(P.natDegree*k) := by
      have hone : (1:ℝ) ≤ (2:ℝ)^(-(s:ℝ)-1) := by
        have hexp : (0:ℝ) ≤ -((s:ℝ)) - 1 := by linarith
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
        simpa using h
      linarith [hXlo]
    have hXbound : (|ξ| * (2:ℝ)^(P.natDegree*k))^(-(1/(P.natDegree:ℝ)))
        ≤ (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) := by
      have hconst : (0:ℝ) < (2:ℝ)^(-(s:ℝ)-1) :=
        Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
      have hstep1 : (|ξ| * (2:ℝ)^(P.natDegree*k))^(-(1/(P.natDegree:ℝ)))
          ≤ ((2:ℝ)^(-(s:ℝ)-1))^(-(1/(P.natDegree:ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hconst hXlo (by
          have : (0:ℝ) ≤ 1/(P.natDegree:ℝ) := by positivity
          linarith)
      have hstep2 : ((2:ℝ)^(-(s:ℝ)-1))^(-(1/(P.natDegree:ℝ)))
          = (2:ℝ)^((-(s:ℝ)-1) * (-(1/(P.natDegree:ℝ)))) :=
        (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
      have hstep3 : (-(s:ℝ)-1) * (-(1/(P.natDegree:ℝ)))
          = 1/(P.natDegree:ℝ) + (-(|(s:ℝ)|)/(P.natDegree:ℝ)) := by
        rw [habs]; field_simp; ring
      have hstep4 : (2:ℝ)^(1/(P.natDegree:ℝ) + (-(|(s:ℝ)|)/(P.natDegree:ℝ)))
          = (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) :=
        Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _
      rw [hstep2, hstep3, hstep4] at hstep1
      exact hstep1
    calc ‖muSym P k ξ‖
        ≤ Cl * (|ξ| * (2:ℝ)^(P.natDegree*k))^(-(1/(P.natDegree:ℝ))) := hCl k ξ hX1
      _ ≤ Cl * ((2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ))) :=
          mul_le_mul_of_nonneg_left hXbound hClpos.le
      _ ≤ 2 * max Cs Cl * (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) := by
          have hClmax : Cl ≤ max Cs Cl := le_max_right _ _
          have hp1 : (1:ℝ) ≤ (2:ℝ)^(1/(P.natDegree:ℝ)) := by
            have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
              (by positivity : (0:ℝ) ≤ 1/(P.natDegree:ℝ))
            simpa using h
          have hpos : (0:ℝ) ≤ (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) :=
            (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le
          have hmaxnn : (0:ℝ) ≤ max Cs Cl := le_trans hClpos.le hClmax
          have hle : Cl ≤ 2 * max Cs Cl := by linarith
          calc Cl * ((2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)))
              ≤ (2 * max Cs Cl) * ((2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ))) :=
                mul_le_mul_of_nonneg_right hle (mul_nonneg (by positivity) hpos)
            _ = 2 * max Cs Cl * (2:ℝ)^(1/(P.natDegree:ℝ)) * (2:ℝ)^(-(|(s:ℝ)|)/(P.natDegree:ℝ)) := by ring

/-! ## The support counting: at most two lacunary bands meet a frequency -/

/-- The window condition `1/2 ≤ |2^{dk+s}ξ| ≤ 2` rewritten in terms of `|ξ| 2^{dk}`. -/
lemma window_X (P : Polynomial ℤ) (s : ℤ) (ξ : ℝ) (k : ℕ)
    (h : dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) ≠ 0) :
    (1:ℝ)/2 ≤ |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) ∧
      |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) ≤ 2 := by
  obtain ⟨h1, h2⟩ := dyadPsi_support h
  have he : (((P.natDegree:ℤ)*(k:ℤ)+s : ℤ) : ℝ)
      = ((P.natDegree * k : ℕ) : ℝ) + (s:ℝ) := by push_cast; ring
  have h2s : (0:ℝ) < (2:ℝ)^(s:ℝ) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have h2dk : (0:ℝ) < (2:ℝ)^(P.natDegree * k) := by positivity
  constructor
  · have hh := h1
    rw [← Real.rpow_intCast, he, Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_natCast, abs_mul, abs_mul, abs_of_pos h2dk, abs_of_pos h2s] at hh
    rw [show (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) * |ξ|
        = |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) from by ring] at hh
    exact hh
  · have hh := h2
    rw [← Real.rpow_intCast, he, Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_natCast, abs_mul, abs_mul, abs_of_pos h2dk, abs_of_pos h2s] at hh
    rw [show (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) * |ξ|
        = |ξ| * (2:ℝ)^(P.natDegree*k) * (2:ℝ)^(s:ℝ) from by ring] at hh
    exact hh

/-- **Two bands are at most one unit apart**: if both `2^{dm+s}ξ` and `2^{dk+s}ξ` lie in the
support window `[1/2,2]` then `k ≤ m+1` (because `d ≥ 2`). -/
lemma gap_le_one (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) {s : ℤ} {ξ : ℝ} {m k : ℕ} (hmk : m < k)
    (hm : dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(m:ℤ)+s) * ξ) ≠ 0)
    (hk : dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) ≠ 0) :
    k ≤ m + 1 := by
  obtain ⟨hm1, hm2⟩ := window_X P s ξ m hm
  obtain ⟨hk1, hk2⟩ := window_X P s ξ k hk
  set Xm : ℝ := |ξ| * (2:ℝ)^(P.natDegree*m) with hXmdef
  set Xk : ℝ := |ξ| * (2:ℝ)^(P.natDegree*k) with hXkdef
  have ht : (0:ℝ) < (2:ℝ)^(s:ℝ) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have hXmpos : 0 < Xm := by
    have h3 : (0:ℝ) < Xm * (2:ℝ)^(s:ℝ) := lt_of_lt_of_le (by norm_num) hm1
    nlinarith [h3, ht]
  have hratio : Xk / Xm ≤ 4 := by
    rw [div_le_iff₀ hXmpos]
    have h3 : (1:ℝ) ≤ 2 * (Xm * (2:ℝ)^(s:ℝ)) := by linarith
    have key : Xk * (2:ℝ)^(s:ℝ) ≤ 4 * Xm * (2:ℝ)^(s:ℝ) := by
      calc Xk * (2:ℝ)^(s:ℝ) ≤ 2 := hk2
        _ ≤ 2 * (2 * (Xm * (2:ℝ)^(s:ℝ))) := by linarith
        _ = 4 * Xm * (2:ℝ)^(s:ℝ) := by ring
    exact (mul_le_mul_iff_of_pos_right ht).mp key
  have hp : (2:ℝ)^(P.natDegree*k)
      = (2:ℝ)^(P.natDegree*m) * (2:ℝ)^(P.natDegree*(k-m)) := by
    rw [← pow_add, show P.natDegree*m + P.natDegree*(k-m) = P.natDegree*k by
      rw [← Nat.mul_add]; congr 1; omega]
  have hXk_eq : Xk = Xm * (2:ℝ)^(P.natDegree*(k-m)) := by
    rw [hXmdef, hXkdef, hp]
    ring
  have hrpow : (2:ℝ)^(P.natDegree*(k-m)) ≤ 4 := by
    have h := hXk_eq
    rw [h] at hratio
    -- Xm * 2^n / Xm ≤ 4 → 2^n ≤ 4
    rwa [mul_div_cancel_left₀ _ hXmpos.ne'] at hratio
  have hnat : (2:ℕ)^(P.natDegree*(k-m)) ≤ 4 := by exact_mod_cast hrpow
  have hle2 : P.natDegree * (k-m) ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hnat)
  by_contra hcon
  push_neg at hcon
  have h1 : 2 * (k-m) ≤ P.natDegree * (k-m) := Nat.mul_le_mul_right _ hdeg
  omega

/-- At most two lacunary bands `ψ(2^{dk+s}·)` meet a given frequency. -/
lemma card_support_le_two (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (K : ℕ) (s : ℤ) (ξ : ℝ) :
    ((Finset.range K).filter
      (fun k => dyadPsi ((2:ℝ)^((((P.natDegree * k : ℕ)) : ℤ) + s) * ξ) ≠ 0)).card ≤ 2 := by
  classical
  set S : Finset ℕ := (Finset.range K).filter
    (fun k => dyadPsi ((2:ℝ)^((((P.natDegree * k : ℕ)) : ℤ) + s) * ξ) ≠ 0) with hS
  rcases Finset.eq_empty_or_nonempty S with h | hne
  · rw [h]; simp
  · set m := S.min' hne with hmdef
    have hmS : m ∈ S := Finset.min'_mem S hne
    have hbound : ∀ k ∈ S, k ≤ m + 1 := by
      intro k hk
      rcases lt_or_eq_of_le (Finset.min'_le S k hk) with hlt | heq
      · exact gap_le_one P hdeg hlt (Finset.mem_filter.mp hmS).2 (Finset.mem_filter.mp hk).2
      · omega
    have hsub : S ⊆ {m, m+1} := by
      intro k hk
      have h1 := Finset.min'_le S k hk
      have h2 := hbound k hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc S.card ≤ ({m, m+1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

/-! ## Boundedness of the bump and the final symbol estimate -/

lemma exists_bound_of_continuous_hasCompactSupport {f : ℝ → ℝ} (hc : Continuous f)
    (hs : HasCompactSupport f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  have hcomp : IsCompact (tsupport f) := hs
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rcases em (x ∈ tsupport f) with hx | hx
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

lemma dyadPsi_abs_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, |dyadPsi η| ≤ B := by
  have hc : Continuous dyadTheta := dyadTheta_spec.1.continuous
  have hs : HasCompactSupport dyadTheta := dyadTheta_spec.2.1
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_continuous_hasCompactSupport hc hs
  refine ⟨2 * B, by positivity, fun η => ?_⟩
  have h1 : |dyadPsi η| ≤ |dyadTheta η| + |dyadTheta (2 * η)| := by
    rw [dyadPsi]; exact abs_sub _ _
  have h2 : |dyadTheta (2 * η)| ≤ B := hB (2 * η)
  linarith [hB η, h1, hB0]

/-- **The pointwise symbol bound** (`Maximal/DRDF_ROUTE.md` steps 1 and 3): the symbol of the
operator `T_s` is bounded by `≲ 2^{-|s|/d}`, uniformly in the number of terms, the dyadic signs and
the frequency. -/
theorem Ts_symbol_bound (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (ξ : ℝ),
      ‖∑ k ∈ Finset.range K, ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
        (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))‖
      ≤ C * (2:ℝ) ^ (-(|((s:ℤ):ℝ)|) / (P.natDegree:ℝ)) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := muSym_le_window P hdeg
  obtain ⟨Bψ, hBψ0, hBψ⟩ := dyadPsi_abs_bound
  refine ⟨2 * (2 * Bψ * (2 * Cw)) + 1, by positivity, ?_⟩
  intro K ε hε s ξ
  have hcast : ∀ k : ℕ, ((P.natDegree:ℤ)*(k:ℤ) + s) = (((P.natDegree * k : ℕ)) : ℤ) + s := by
    intro k; rw [← Nat.cast_mul]
  set S : Finset ℕ := (Finset.range K).filter
    (fun k => dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) ≠ 0) with hSdef
  have hcard : S.card ≤ 2 := by
    have hiff : ∀ k : ℕ, (dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) ≠ 0)
        ↔ (dyadPsi ((2:ℝ)^((((P.natDegree * k : ℕ)) : ℤ) + s) * ξ) ≠ 0) := by
      intro k; rw [hcast k]
    rw [hSdef]
    simp only [hiff]
    exact card_support_le_two P hdeg K s ξ
  have hsum : (∑ k ∈ Finset.range K, ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
        (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)))
      = ∑ k ∈ S, ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
        (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) := by
    rw [hSdef, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) = 0
    · simp [hp]
    · simp [hp]
  rw [hsum]
  have hperterm : ∀ k ∈ S, ‖ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
      (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))‖
      ≤ 2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ))) := by
    intro k hk
    have hψne : dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) ≠ 0 := by
      have := hk
      rw [hSdef, Finset.mem_filter] at this
      exact this.2
    obtain ⟨hw1, hw2⟩ := dyadPsi_support hψne
    have hμ := hCw k s ξ hw1 hw2
    have hψb : ‖((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ))‖ ≤ Bψ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hBψ _
    have hεb : ‖ε k‖ ≤ 1 := hε k
    have hb : (0:ℝ) ≤ (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le
    calc ‖ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
          (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))‖
        = ‖ε k‖ * ‖((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ))‖
          * ‖starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * Bψ * (Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ))) := by
          apply mul_le_mul (mul_le_mul hεb hψb (norm_nonneg _) (by norm_num)) hμ (norm_nonneg _) ?_
          positivity
      _ ≤ 2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ))) := by
          have h2 : (0:ℝ) ≤ Bψ * (Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ))) :=
            mul_nonneg hBψ0 (mul_nonneg hCwpos.le hb)
          nlinarith [h2]
  calc ‖∑ k ∈ S, ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
        (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))‖
      ≤ ∑ k ∈ S, ‖ε k * ((dyadPsi ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ)+s) * ξ) : ℂ)) *
          (starRingEnd ℂ (polyProfile P (2^k) ξ) - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ S, (2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)))) :=
        Finset.sum_le_sum hperterm
    _ = S.card * (2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)))) := by
        have hb : (0:ℝ) ≤ 2 * Bψ * (2 * Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ))) := by
          have h1 : (0:ℝ) ≤ Cw * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) :=
            mul_nonneg hCwpos.le ((Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le)
          positivity
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb
    _ = (2 * (2 * Bψ * (2 * Cw))) * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) := by ring
    _ ≤ (2 * (2 * Bψ * (2 * Cw)) + 1) * (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) := by
        have hb : (0:ℝ) ≤ (2:ℝ)^(-(|((s:ℤ):ℝ)|)/(P.natDegree:ℝ)) :=
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le
        nlinarith [hb]

/-! ## The junk-value dichotomy for `𝓕⁻ (m · 𝓕 g)` -/

lemma norm_fourier_le' (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ y : ℝ, ‖f y‖ := by
  rw [show 𝓕 f = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f from rfl]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

lemma continuous_fourier_of_integrable' {f : ℝ → ℂ} (hf : Integrable f (volume : Measure ℝ)) :
    Continuous (𝓕 f) := by
  rw [show 𝓕 f = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f from rfl]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hf

lemma fourierInv_zero : (fun x : ℝ => 𝓕⁻ (fun _ : ℝ => (0:ℂ)) x) = fun _ => 0 := by
  funext x
  rw [Real.fourierInv_eq']
  simp

/-- **The dichotomy.** For an `L¹ ∩ L^∞` symbol `m` and `g ∈ L²`, the pointwise inverse Fourier
integral `𝓕⁻ (m · 𝓕 g)` either vanishes (junk value, when `g ∉ L¹`) or is the `L²` multiplier with
symbol `m` applied to the class of `g`. -/
theorem dyadicProj_dichotomy (m : ℝ → ℂ) (hmi : Integrable m (volume : Measure ℝ))
    (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume : Measure ℝ)) :
    (¬ Integrable g (volume : Measure ℝ) →
        (fun x : ℝ => 𝓕⁻ (fun ξ : ℝ => m ξ * 𝓕 g ξ) x) = fun _ => 0) ∧
      (Integrable g (volume : Measure ℝ) →
        (fun x : ℝ => 𝓕⁻ (fun ξ : ℝ => m ξ * 𝓕 g ξ) x)
          =ᵐ[volume]
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (hg.toLp) : ℝ → ℂ)) := by
  constructor
  · intro hg1
    have hz : 𝓕 g = fun _ => 0 := Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable hg1
    have : (fun ξ : ℝ => m ξ * 𝓕 g ξ) = fun _ => 0 := by
      funext ξ; rw [hz]; simp
    rw [this, fourierInv_zero]
  · intro hg1
    have hgi : MemLp g 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hg1
    have hcont : Continuous (𝓕 g) := continuous_fourier_of_integrable' hg1
    set B : ℝ := ∫ y : ℝ, ‖g y‖ with hBdef
    have hBnn : 0 ≤ B := integral_nonneg (fun y => norm_nonneg _)
    have hFb : ∀ ξ : ℝ, ‖𝓕 g ξ‖ ≤ B := fun ξ => by
      rw [hBdef]; exact norm_fourier_le' g ξ
    set C : ℝ := (eLpNorm m ⊤ (volume : Measure ℝ)).toReal with hCdef
    have hCnn : 0 ≤ C := ENNReal.toReal_nonneg
    have hmB : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖m ξ‖ ≤ C := by
      filter_upwards [ae_le_eLpNormEssSup (μ := (volume : Measure ℝ)) (f := m)] with ξ hξ
      rw [(eLpNorm_exponent_top hm.aestronglyMeasurable).symm] at hξ
      have hne : eLpNorm m ⊤ (volume : Measure ℝ) ≠ ⊤ := (hm.eLpNorm_lt_top).ne
      have hto := ENNReal.toReal_mono hne hξ
      rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at hto
      exact hto
    -- `m ∈ L²`
    have hm2 : MemLp m 2 (volume : Measure ℝ) := by
      rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
      refine Integrable.mono' (hmi.norm.const_mul C) (hmi.aestronglyMeasurable.norm.pow 2) ?_
      filter_upwards [hmB] with ξ hξ
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2), pow_two]
      exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    -- `v := m · 𝓕g ∈ L¹ ∩ L²`
    set v : ℝ → ℂ := fun ξ => m ξ * 𝓕 g ξ with hvdef
    have hv_meas : AEStronglyMeasurable v (volume : Measure ℝ) :=
      hm.aestronglyMeasurable.mul hcont.aestronglyMeasurable
    have hv1 : Integrable v (volume : Measure ℝ) := by
      refine Integrable.mono' (hmi.norm.mul_const B) hv_meas ?_
      filter_upwards with ξ
      rw [hvdef, norm_mul]
      exact mul_le_mul_of_nonneg_left (hFb ξ) (norm_nonneg _)
    have hv2 : MemLp v 2 (volume : Measure ℝ) := by
      rw [memLp_two_iff_integrable_sq_norm hv_meas]
      have hs : Integrable (fun ξ : ℝ => ‖m ξ‖ ^ 2) (volume : Measure ℝ) :=
        (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm2
      refine Integrable.mono' (hs.const_mul (B^2)) (hv_meas.norm.pow 2) ?_
      filter_upwards with ξ
      have hβ : (fun ξ : ℝ => m ξ * 𝓕 g ξ) ξ = m ξ * 𝓕 g ξ := rfl
      rw [hvdef, hβ, norm_mul, mul_pow, Real.norm_of_nonneg (by positivity),
        show B ^ 2 * ‖m ξ‖ ^ 2 = ‖m ξ‖ ^ 2 * B ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (𝓕 g ξ)) (hFb ξ) 2)
        (pow_nonneg (norm_nonneg (m ξ)) 2)
    -- the two `Lp` classes agree
    have hmulLp : Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 (hg.toLp))
        = MemLp.toLp v hv2 := by
      apply Lp.ext (p := 2) (μ := (volume : Measure ℝ))
      filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (𝓕 (hg.toLp)),
        Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hgi hg,
        MemLp.coeFn_toLp hv2] with ξ h1 h2 h3
      simp only [Pi.mul_apply] at h1 ⊢
      rw [h1, h2, h3]
    have hfinal : (𝓕⁻ (MemLp.toLp v hv2) : Lp ℂ 2 (volume : Measure ℝ))
        = Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (hg.toLp) := by
      rw [show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (hg.toLp)
          = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 (hg.toLp))) from rfl,
        hmulLp]
    have hbr := Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
      (memLp_one_iff_integrable.mpr hv1) hv2
    refine hbr.symm.trans ?_
    rw [hfinal]

/-! ## The `L²` multiplier calculus for the assembly -/

lemma memLp_top_of_bound' {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume : Measure ℝ)) (C : ℝ)
    (h : ∀ ξ, ‖f ξ‖ ≤ C) : MemLp f ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound hf C (Filter.Eventually.of_forall h)

lemma continuous_dyadPsi : Continuous dyadPsi := by
  have hθ : Continuous dyadTheta := dyadTheta_spec.1.continuous
  have h : dyadPsi = fun ξ : ℝ => dyadTheta ξ - dyadTheta (2 * ξ) := rfl
  rw [h]
  exact hθ.sub (hθ.comp (continuous_const.mul continuous_id))

lemma continuous_muSym (P : Polynomial ℤ) (k : ℕ) : Continuous (muSym P k) := by
  have h1 : Continuous (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) :=
    Complex.continuous_conj.comp (contDiff_polyProfile P (2^k)).continuous
  have h2 : Continuous (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) :=
    Complex.continuous_conj.comp (contDiff_polyProfile P (2^(k+1))).continuous
  exact h1.sub h2

lemma norm_muSym_le_two (P : Polynomial ℤ) (k : ℕ) (ξ : ℝ) : ‖muSym P k ξ‖ ≤ 2 := by
  have h1 := norm_polyProfile_le_one P (2^k) ξ
  have h2 := norm_polyProfile_le_one P (2^(k+1)) ξ
  calc ‖muSym P k ξ‖
      ≤ ‖starRingEnd ℂ (polyProfile P (2^k) ξ)‖ + ‖starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)‖ :=
        norm_sub_le _ _
    _ = ‖polyProfile P (2^k) ξ‖ + ‖polyProfile P (2^(k+1)) ξ‖ := by
        rw [Complex.norm_conj, Complex.norm_conj]
    _ ≤ 2 := by linarith

lemma mulLp_congr_proof (m : ℝ → ℂ) (h₁ h₂ : MemLp m ⊤ (volume : Measure ℝ))
    (X : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.mulLp m h₁ X
      = Commons.Analysis.Fourier.BoundaryLayer.mulLp m h₂ X := rfl

lemma multiplier_congr {m₁ m₂ : ℝ → ℂ} (h : m₁ = m₂) (h₁ : MemLp m₁ ⊤ (volume : Measure ℝ))
    (h₂ : MemLp m₂ ⊤ (volume : Measure ℝ)) (H : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁ H
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ H := by
  subst h
  rfl

lemma memLp_zero_fun : MemLp (fun _ : ℝ => (0:ℂ)) ⊤ (volume : Measure ℝ) := by
  simpa using (MeasureTheory.MemLp.zero (μ := (volume : Measure ℝ)) (p := ⊤) (E := ℂ))

lemma multiplier_zero (H : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun _ : ℝ => (0:ℂ))
      memLp_zero_fun H = 0 := by
  rw [show Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun _ : ℝ => (0:ℂ))
      memLp_zero_fun H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp (fun _ : ℝ => (0:ℂ))
        memLp_zero_fun (𝓕 H)) from rfl]
  have h : Commons.Analysis.Fourier.BoundaryLayer.mulLp (fun _ : ℝ => (0:ℂ))
      memLp_zero_fun (𝓕 H) = 0 := by
    apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe (fun _ : ℝ => (0:ℂ))
      memLp_zero_fun (𝓕 H)] with ξ e1
    rw [e1]
    simp
  rw [h]
  simp

lemma multiplier_add (m₁ m₂ : ℝ → ℂ) (h₁ : MemLp m₁ ⊤ (volume : Measure ℝ))
    (h₂ : MemLp m₂ ⊤ (volume : Measure ℝ)) (h₁₂ : MemLp (m₁ + m₂) ⊤ (volume : Measure ℝ))
    (H : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁ H
        + Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ H
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (m₁ + m₂) h₁₂ H := by
  have e₁ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁ H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)) := rfl
  have e₂ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H)) := rfl
  have eadd : 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)
        + Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H))
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H))
        + 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H)) :=
    map_add _ _ _
  rw [e₁, e₂, ← eadd]
  congr 1
  have h2 : Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)
        + Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H)
      = Commons.Analysis.Fourier.BoundaryLayer.mulLp (m₁ + m₂) h₁₂ (𝓕 H) := by
    apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [Lp.coeFn_add (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H))
        (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H)),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₁ h₁ (𝓕 H),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₂ h₂ (𝓕 H),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe (m₁ + m₂) h₁₂ (𝓕 H)] with ξ e0 e1 e2 e3
    rw [e0, Pi.add_apply, e1, e2, e3]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [h2]

lemma memLpSum_top {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) ⊤ (volume : Measure ℝ)) :
    MemLp (fun ξ : ℝ => ∑ i ∈ s, f i ξ) ⊤ (volume : Measure ℝ) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using memLp_zero_fun
  | insert a s ha ih =>
      have h1 : (fun ξ : ℝ => ∑ i ∈ insert a s, f i ξ)
          = fun ξ : ℝ => f a ξ + ∑ i ∈ s, f i ξ := by
        funext ξ; rw [Finset.sum_insert ha]
      rw [h1]
      exact (hf a).add ih

lemma multiplier_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) ⊤ (volume : Measure ℝ)) (H : Lp ℂ 2 (volume : Measure ℝ)) :
    ∑ i ∈ s, Commons.Analysis.Fourier.BoundaryLayer.multiplier (f i) (hf i) H
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => ∑ i ∈ s, f i ξ) (memLpSum_top s f hf) H := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      have h : (fun ξ : ℝ => ∑ i ∈ (∅ : Finset ι), f i ξ) = fun _ => (0:ℂ) := by
        funext ξ; simp
      rw [multiplier_congr h (memLpSum_top ∅ f hf) memLp_zero_fun H, multiplier_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      have hsum : MemLp (f a + fun ξ : ℝ => ∑ i ∈ s, f i ξ) ⊤ (volume : Measure ℝ) := by
        have h := memLpSum_top (insert a s) f hf
        rwa [show (fun ξ : ℝ => ∑ i ∈ insert a s, f i ξ)
            = f a + (fun ξ : ℝ => ∑ i ∈ s, f i ξ) from by
              funext ξ; rw [Finset.sum_insert ha]; rfl] at h
      rw [multiplier_add (f a) (fun ξ : ℝ => ∑ i ∈ s, f i ξ) (hf a)
        (memLpSum_top s f hf) hsum H]
      exact multiplier_congr (by
        funext ξ; rw [Finset.sum_insert ha]; rfl) hsum (memLpSum_top (insert a s) f hf) H

/-- **Plancherel for a bounded symbol**: `‖multiplier m H‖₂ ≤ ‖m‖_∞ ‖H‖₂`. -/
lemma eLpNorm_multiplier_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ)) (A : ℝ)
    (hA : ∀ ξ, ‖m ξ‖ ≤ A) (H : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm H : ℝ → ℂ)
        2 (volume : Measure ℝ)
      ≤ ENNReal.ofReal A * eLpNorm H 2 (volume : Measure ℝ) := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg (m 0)) (hA 0)
  rw [← Lp.enorm_def (Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm H),
    ← Lp.enorm_def H]
  exact Commons.Analysis.Fourier.enorm_multiplier_le hm A hA0 hA H

/-! ## The curve average is a contraction on `L²` -/

/-- The reference measure `volume` restricted to `(0,1]` (a probability measure). -/
noncomputable def curveIocMeasure : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

lemma curveIocMeasure_univ : curveIocMeasure Set.univ = 1 := by
  rw [curveIocMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

instance instIsFiniteMeasureCurveIocMeasure : IsFiniteMeasure curveIocMeasure := by
  rw [curveIocMeasure]; infer_instance

/-- Elementary inequality in `ℝ≥0∞`: `a ≤ 1 + a ^ 2`. -/
private lemma ennreal_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  by_cases ha : a ≤ 1
  · exact ha.trans (le_add_right le_rfl)
  · have h1 : 1 ≤ a := (not_le.mp ha).le
    rw [pow_two]
    calc a ≤ a * a := le_mul_of_one_le_right' h1
      _ ≤ 1 + a * a := le_add_left le_rfl

/-- The curve map `(x,t) ↦ x - P(N t)` is quasi-measure-preserving. -/
lemma quasiMeasurePreserving_curve (P : Polynomial ℤ) (N : ℕ) :
    QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - (toRealPoly P).eval ((N:ℝ) * p.2))
      ((volume : Measure ℝ).prod curveIocMeasure) (volume : Measure ℝ) := by
  set ν : Measure ℝ := Measure.map (fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t))
    curveIocMeasure with hνdef
  have hcont : Continuous (fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  have hqmp1 : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - p.2)
      ((volume : Measure ℝ).prod ν) (volume : Measure ℝ) :=
    quasiMeasurePreserving_sub_of_right_invariant volume ν
  have hmap : Measure.map (Prod.map id (fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)))
      ((volume : Measure ℝ).prod curveIocMeasure) = (volume : Measure ℝ).prod ν := by
    rw [← Measure.map_prod_map (volume : Measure ℝ) curveIocMeasure measurable_id hcont.measurable,
      Measure.map_id, hνdef]
  exact hqmp1.comp ⟨Measurable.prodMap measurable_id hcont.measurable, by rw [hmap]⟩

/-- Translation invariance of `eLpNorm`. -/
lemma eLpNorm_comp_sub_right (g : ℝ → ℂ) (c : ℝ) (p : ℝ≥0∞)
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    eLpNorm (fun x : ℝ => g (x - c)) p (volume : Measure ℝ) = eLpNorm g p (volume : Measure ℝ) := by
  simpa [Function.comp_def] using
    (MeasureTheory.eLpNorm_comp_measurePreserving (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) (f := fun x : ℝ => x - c) (g := g) (p := p) hg
      (MeasureTheory.measurePreserving_sub_right (volume : Measure ℝ) c))

/-- For `u ∈ L²(ℝ)` the fibres `t ↦ u (x - Q t)` are integrable on `(0,1]` for almost every `x`. -/
private theorem ae_integrable_sub_comp {Q : ℝ → ℝ} (hQ : Continuous Q) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Integrable (fun t : ℝ => u (x - Q t)) curveIocMeasure := by
  have hqmpS : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - Q p.2)
      ((volume : Measure ℝ).prod curveIocMeasure) (volume : Measure ℝ) := by
    set ν : Measure ℝ := Measure.map Q curveIocMeasure with hνdef
    have hqmp1 : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.1 - p.2)
        ((volume : Measure ℝ).prod ν) (volume : Measure ℝ) :=
      quasiMeasurePreserving_sub_of_right_invariant volume ν
    have hmap : Measure.map (Prod.map id Q) ((volume : Measure ℝ).prod curveIocMeasure)
        = (volume : Measure ℝ).prod ν := by
      rw [← Measure.map_prod_map (volume : Measure ℝ) curveIocMeasure measurable_id hQ.measurable,
        Measure.map_id, hνdef]
    exact hqmp1.comp ⟨Measurable.prodMap measurable_id hQ.measurable, by rw [hmap]⟩
  have hS_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => u (p.1 - Q p.2))
      ((volume : Measure ℝ).prod curveIocMeasure) :=
    (hu.aestronglyMeasurable.mono_ac hqmpS.absolutelyContinuous).comp_measurable hqmpS.measurable
  have hF : AEMeasurable (Function.uncurry (fun x t : ℝ => ‖u (x - Q t)‖ₑ ^ (2:ℕ)))
      ((volume : Measure ℝ).prod curveIocMeasure) := by
    change AEMeasurable (fun p : ℝ × ℝ => ‖u (p.1 - Q p.2)‖ₑ ^ (2:ℕ))
      ((volume : Measure ℝ).prod curveIocMeasure)
    exact hS_aesm.enorm.pow_const 2
  have hGmeas : AEMeasurable (fun x : ℝ => ∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure)
      (volume : Measure ℝ) := hF.lintegral_prod_right
  have hswap : ∫⁻ x : ℝ, (∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure) ∂(volume : Measure ℝ)
      = ∫⁻ t, (∫⁻ x : ℝ, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂(volume : Measure ℝ)) ∂curveIocMeasure :=
    lintegral_lintegral_swap (f := fun x t : ℝ => ‖u (x - Q t)‖ₑ ^ (2:ℕ)) hF
  have hinner : ∀ t : ℝ,
      ∫⁻ x : ℝ, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂(volume : Measure ℝ)
        = ∫⁻ x : ℝ, ‖u x‖ₑ ^ (2:ℕ) := by
    intro t
    have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => ‖u y‖ₑ ^ (2:ℕ)) (-(Q t))
    simpa [sub_eq_add_neg] using h
  have htotal : ∫⁻ x : ℝ, (∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure) ∂(volume : Measure ℝ)
      = ∫⁻ x : ℝ, ‖u x‖ₑ ^ (2:ℕ) := by
    rw [hswap, lintegral_congr hinner, lintegral_const, curveIocMeasure_univ, mul_one]
  have hfin : ∫⁻ x : ℝ, ‖u x‖ₑ ^ (2:ℕ) ≠ ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := (volume : Measure ℝ))
      (f := u) (p := (2:ENNReal)) (by norm_num) (by norm_num) hu.eLpNorm_lt_top
    simpa [ENNReal.rpow_natCast] using h.ne
  have hGne : ∫⁻ x : ℝ, (∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure) ∂(volume : Measure ℝ) ≠ ⊤ := by
    rw [htotal]; exact hfin
  have hGlt : ∀ᵐ x ∂(volume : Measure ℝ),
      ∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure < ⊤ :=
    ae_lt_top' hGmeas hGne
  obtain ⟨g, hg, hfg⟩ := hS_aesm
  have hslice : ∀ᵐ x ∂(volume : Measure ℝ),
      AEStronglyMeasurable (fun t : ℝ => u (x - Q t)) curveIocMeasure := by
    filter_upwards [ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := curveIocMeasure) hfg]
      with x hx
    exact ⟨fun t : ℝ => g (x, t),
      hg.comp_measurable (Measurable.prodMk measurable_const measurable_id), hx⟩
  filter_upwards [hslice, hGlt] with x hx_meas hx_fin
  refine ⟨hx_meas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ t, ‖(fun t : ℝ => u (x - Q t)) t‖ₑ ∂curveIocMeasure
      = ∫⁻ t, ‖u (x - Q t)‖ₑ ∂curveIocMeasure := rfl
    _ ≤ ∫⁻ t, (1 + ‖u (x - Q t)‖ₑ ^ (2:ℕ)) ∂curveIocMeasure :=
        lintegral_mono fun t => ennreal_le_one_add_sq _
    _ = ∫⁻ t, (1:ℝ≥0∞) ∂curveIocMeasure + ∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure :=
        lintegral_add_left' aemeasurable_const _
    _ = 1 + ∫⁻ t, ‖u (x - Q t)‖ₑ ^ (2:ℕ) ∂curveIocMeasure := by
        rw [lintegral_const, curveIocMeasure_univ, mul_one]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨by norm_num, hx_fin⟩

/-- The curve average of an `L²` function is a.e. strongly measurable. -/
lemma aestronglyMeasurable_curveSigma (P : Polynomial ℤ) (N : ℕ) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (curveSigma P N u) (volume : Measure ℝ) := by
  have hcont : Continuous (fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  have hqmpS := quasiMeasurePreserving_curve P N
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => u (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2)))
      ((volume : Measure ℝ).prod curveIocMeasure) :=
    (hu.aestronglyMeasurable.mono_ac hqmpS.absolutelyContinuous).comp_measurable hqmpS.measurable
  have h1 : AEStronglyMeasurable
      (fun x : ℝ => ∫ t, u (x - (toRealPoly P).eval ((N:ℝ) * t)) ∂curveIocMeasure)
      (volume : Measure ℝ) := hjoint.integral_prod_right'
  obtain ⟨g, hgm, hge⟩ := h1
  have h2 : (fun x : ℝ => ∫ t, u (x - (toRealPoly P).eval ((N:ℝ) * t)) ∂curveIocMeasure)
      =ᵐ[volume] curveSigma P N u := by
    filter_upwards [ae_integrable_sub_comp (Q := fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t))
      hcont hu] with x hx
    rw [curveSigma_apply, curveIocMeasure,
      intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)]
  exact ⟨g, hgm, h2.symm.trans hge⟩


/-- **The curve average is an `L²` contraction**: `‖σ_N g‖₂ ≤ ‖g‖₂`. -/
theorem curveSigma_eLpNorm_le (P : Polynomial ℤ) (N : ℕ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    eLpNorm (curveSigma P N g) 2 (volume : Measure ℝ)
      ≤ eLpNorm g 2 (volume : Measure ℝ) := by
  have hqmpS := quasiMeasurePreserving_curve P N
  have hS_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2)))
      ((volume : Measure ℝ).prod curveIocMeasure) :=
    (hg.aestronglyMeasurable.mono_ac hqmpS.absolutelyContinuous).comp_measurable hqmpS.measurable
  have hF : AEMeasurable (Function.uncurry
      (fun x t : ℝ => ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ))
      ((volume : Measure ℝ).prod curveIocMeasure) := by
    change AEMeasurable (fun p : ℝ × ℝ => ‖g (p.1 - (toRealPoly P).eval ((N:ℝ) * p.2))‖ₑ)
      ((volume : Measure ℝ).prod curveIocMeasure)
    exact hS_aesm.enorm
  have hpt : ∀ x : ℝ, ‖curveSigma P N g x‖ₑ
      ≤ ∫⁻ t, ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ ∂curveIocMeasure := by
    intro x
    rw [curveSigma_apply, curveIocMeasure,
      intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)]
    exact MeasureTheory.enorm_integral_le_lintegral_enorm _
  have hmink : eLpNorm (fun x : ℝ => ∫⁻ t, ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ
        ∂curveIocMeasure) 2 (volume : Measure ℝ)
      ≤ ∫⁻ t, eLpNorm (fun x : ℝ => ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ)
          2 (volume : Measure ℝ) ∂curveIocMeasure :=
    Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite
      (μ := (volume : Measure ℝ)) (ν := curveIocMeasure) (p := 2) (F := fun x t : ℝ =>
        ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ) (by norm_num) (by norm_num) hF
  have hinner : ∀ t : ℝ, eLpNorm (fun x : ℝ => ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ)
        2 (volume : Measure ℝ) = eLpNorm g 2 (volume : Measure ℝ) := by
    intro t
    rw [MeasureTheory.eLpNorm_enorm (fun x : ℝ => g (x - (toRealPoly P).eval ((N:ℝ) * t)))
      (hg.aestronglyMeasurable.comp_measurePreserving
        (MeasureTheory.measurePreserving_sub_right (volume : Measure ℝ) _)),
      eLpNorm_comp_sub_right g _ 2 hg.aestronglyMeasurable]
  have hmain : eLpNorm (fun x : ℝ => ∫⁻ t, ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ
        ∂curveIocMeasure) 2 (volume : Measure ℝ) ≤ eLpNorm g 2 (volume : Measure ℝ) := by
    calc eLpNorm (fun x : ℝ => ∫⁻ t, ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ
          ∂curveIocMeasure) 2 (volume : Measure ℝ)
        ≤ ∫⁻ t, eLpNorm (fun x : ℝ => ‖g (x - (toRealPoly P).eval ((N:ℝ) * t))‖ₑ)
            2 (volume : Measure ℝ) ∂curveIocMeasure := hmink
      _ = ∫⁻ _t, eLpNorm g 2 (volume : Measure ℝ) ∂curveIocMeasure := by simp_rw [hinner]
      _ = eLpNorm g 2 (volume : Measure ℝ) := by
          rw [lintegral_const, curveIocMeasure_univ, mul_one]
  refine (MeasureTheory.eLpNorm_mono_enorm_ae (aestronglyMeasurable_curveSigma P N hg) ?_).trans hmain
  filter_upwards with x
  rw [enorm_eq_self]
  exact hpt x


/-- Pointwise linearity of the curve average where the fibres are integrable. -/
private lemma curveSigma_sub_of_integrable (P : Polynomial ℤ) (N : ℕ) {u v : ℝ → ℂ} {x : ℝ}
    (hu : Integrable (fun t : ℝ => u (x - (toRealPoly P).eval ((N:ℝ) * t))) curveIocMeasure)
    (hv : Integrable (fun t : ℝ => v (x - (toRealPoly P).eval ((N:ℝ) * t))) curveIocMeasure) :
    curveSigma P N (fun y : ℝ => u y - v y) x = curveSigma P N u x - curveSigma P N v x := by
  have hI : ∀ f : ℝ → ℂ, (∫ t in (0:ℝ)..1, f t) = ∫ t, f t ∂curveIocMeasure := by
    intro f
    rw [intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)]
    rfl
  rw [curveSigma_apply, curveSigma_apply, curveSigma_apply, hI, hI, hI]
  exact integral_sub hu hv

/-- Pointwise (a.e.) linearity of the curve average in `L²`. -/
lemma curveSigma_sub_ae (P : Polynomial ℤ) (N : ℕ) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ)) (hv : MemLp v 2 (volume : Measure ℝ)) :
    curveSigma P N (fun x : ℝ => u x - v x)
      =ᵐ[volume] (fun x : ℝ => curveSigma P N u x - curveSigma P N v x) := by
  have hcont : Continuous (fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  have hU := ae_integrable_sub_comp (Q := fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)) hcont hu
  have hV := ae_integrable_sub_comp (Q := fun t : ℝ => (toRealPoly P).eval ((N:ℝ) * t)) hcont hv
  filter_upwards [hU, hV] with x hx1 hx2
  exact curveSigma_sub_of_integrable P N hx1 hx2

/-- Subtraction rule for the multiplier calculus. -/
lemma multiplier_sub_arg (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (X Y : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (X - Y)
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm X
        - Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm Y := by
  have hFsub : 𝓕 (X - Y) = 𝓕 X - 𝓕 Y := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (X - Y)
      = (Lp.fourierTransformₗᵢ ℝ ℂ) X - (Lp.fourierTransformₗᵢ ℝ ℂ) Y
    exact map_sub _ _ _
  have hmul : Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X - 𝓕 Y)
      = Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X)
        - Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 Y) := by
    apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [Lp.coeFn_sub (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X))
        (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 Y)),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (𝓕 X),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (𝓕 Y),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (𝓕 X - 𝓕 Y),
      Lp.coeFn_sub (𝓕 X) (𝓕 Y)] with ξ e0 e1 e2 e3 e4
    simp only [Pi.sub_apply, Pi.mul_apply] at e0 e1 e2 e3 e4 ⊢
    rw [e3, e0, e1, e2, e4]
    ring
  rw [show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (X - Y)
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 (X - Y))) from rfl,
    show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm X
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X)) from rfl,
    show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm Y
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 Y)) from rfl,
    hFsub, hmul]
  change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X)
      - Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 Y))
    = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X))
      - (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 Y))
  exact map_sub _ _ _

lemma enorm_sub_comm_lp {x y : Lp ℂ 2 (volume : Measure ℝ)} : ‖x - y‖ₑ = ‖y - x‖ₑ := by
  have h : (x - y : Lp ℂ 2 (volume : Measure ℝ)) = -(y - x) := by abel
  rw [h, enorm_neg]

lemma enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; norm_cast

/-- Schwartz functions are dense in `L²`. -/
lemma exists_schwartz_tendsto' (H : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ ψ : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n : ℕ => (ψ n).toLp (2 : ℝ≥0∞) (volume : Measure ℝ)) atTop (𝓝 H) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (2 : ℝ≥0∞) (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  choose ψ hψ using fun n : ℕ =>
    (Metric.denseRange_iff.mp hdense H (1 / ((n : ℝ) + 1)) (by positivity))
  refine ⟨ψ, ?_⟩
  have hψ' : ∀ n : ℕ, dist H ((ψ n).toLp (2 : ℝ≥0∞) (volume : Measure ℝ)) < 1 / ((n : ℝ) + 1) := by
    intro n; simpa using hψ n
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [dist_comm]
  exact le_of_lt (hψ' n)

/-- The symbol `conj ∘ polyProfile P N` is essentially bounded. -/
lemma memLp_star_polyProfile (P : Polynomial ℤ) (N : ℕ) :
    MemLp (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound'
    (Complex.continuous_conj.comp (contDiff_polyProfile P N).continuous).aestronglyMeasurable 1
    (fun ξ => by rw [Complex.norm_conj]; exact norm_polyProfile_le_one P N ξ)

lemma norm_star_polyProfile_le_one (P : Polynomial ℤ) (N : ℕ) (ξ : ℝ) :
    ‖starRingEnd ℂ (polyProfile P N ξ)‖ ≤ 1 := by
  rw [Complex.norm_conj]; exact norm_polyProfile_le_one P N ξ

/-- **The curve average on the inverse Fourier transform of an `L¹ ∩ L²` function is the
multiplier with symbol `conj Φ_N`.** -/
theorem curveSigma_fourierInv_multiplier_ae (P : Polynomial ℤ) (N : ℕ) {W : ℝ → ℂ}
    (hW1 : MemLp W 1 (volume : Measure ℝ)) (hW2 : MemLp W 2 (volume : Measure ℝ))
    (hWi : Integrable (𝓕⁻ W) (volume : Measure ℝ))
    (hm : MemLp (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) ⊤ (volume : Measure ℝ)) :
    curveSigma P N (fun y : ℝ => 𝓕⁻ W y)
      =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm
        (𝓕⁻ (MemLp.toLp W hW2)) : ℝ → ℂ) := by
  have hpt : ∀ x : ℝ, 𝓕⁻ (fun β : ℝ => W β * starRingEnd ℂ (polyProfile P N β)) x
      = curveSigma P N (fun y : ℝ => 𝓕⁻ W y) x := by
    intro x
    have h := polyProfile_fourier_dilation P N (memLp_one_iff_integrable.mp hW1) hWi x
    rw [h]
    rfl
  have hpt2 : ∀ x : ℝ,
      𝓕⁻ (fun β : ℝ => starRingEnd ℂ (polyProfile P N β) * W β) x
        = curveSigma P N (fun y : ℝ => 𝓕⁻ W y) x := by
    intro x
    rw [show (fun β : ℝ => starRingEnd ℂ (polyProfile P N β) * W β)
        = (fun β : ℝ => W β * starRingEnd ℂ (polyProfile P N β)) from by
          funext β; ring]
    exact hpt x
  exact ((multiplier_fourierInv_toLp_ae
      (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm W hW1 hW2).trans
    (Filter.Eventually.of_forall hpt2)).symm

/-- **The curve average is the `L²` multiplier with symbol `conj (polyProfile P N)`.** -/
theorem curveSigma_eq_multiplier (P : Polynomial ℤ) (N : ℕ) (h : ℝ → ℂ)
    (hh : MemLp h 2 (volume : Measure ℝ)) :
    (∃ (hm : MemLp (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) ⊤ (volume : Measure ℝ)),
      curveSigma P N h =ᵐ[volume]
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm (hh.toLp) : ℝ → ℂ))
    ∧ MemLp (curveSigma P N h) 2 (volume : Measure ℝ) := by
  have hm : MemLp (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) ⊤ (volume : Measure ℝ) :=
    memLp_star_polyProfile P N
  classical
  set H : Lp ℂ 2 (volume : Measure ℝ) := hh.toLp with hHdef
  set G : Lp ℂ 2 (volume : Measure ℝ) :=
    Commons.Analysis.Fourier.BoundaryLayer.multiplier
      (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm H with hGdef
  have hcoeH : (H : ℝ → ℂ) =ᵐ[volume] h := hh.coeFn_toLp
  obtain ⟨ψ, hψtend⟩ := exists_schwartz_tendsto' (𝓕 H)
  let A : ℕ → Lp ℂ 2 (volume : Measure ℝ) :=
    fun n => (ψ n).toLp (2 : ℝ≥0∞) (volume : Measure ℝ)
  let W : ℕ → ℝ → ℂ := fun n => (ψ n : ℝ → ℂ)
  let V : ℕ → ℝ → ℂ := fun n y => 𝓕⁻ (W n) y
  let M : ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun n =>
    Commons.Analysis.Fourier.BoundaryLayer.multiplier
      (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm (𝓕⁻ (A n))
  have hAtend : Tendsto (fun n : ℕ => A n) atTop (𝓝 (𝓕 H)) := by simpa [A] using hψtend
  have hAeq : ∀ n : ℕ, MemLp.toLp ((ψ n : ℝ → ℂ)) ((ψ n).memLp 2 (volume : Measure ℝ)) = A n := by
    intro n
    apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [MemLp.coeFn_toLp ((ψ n).memLp 2 (volume : Measure ℝ)),
      SchwartzMap.coeFn_toLp (ψ n) 2 (volume : Measure ℝ)] with x h1 h2
    rw [h1, h2]
  have hAcoe : ∀ n : ℕ, ((𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] V n :=
    fun n => Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv ((ψ n).memLp 1 _)
      ((ψ n).memLp 2 _)
  have hVmem : ∀ n : ℕ, MemLp (V n) 2 (volume : Measure ℝ) :=
    fun n => MemLp.ae_eq (hAcoe n) (Lp.memLp (𝓕⁻ (A n)))
  have hWi : ∀ n : ℕ, Integrable (fun y : ℝ => 𝓕⁻ (W n) y) (volume : Measure ℝ) := by
    intro n
    have hcoe : ((𝓕⁻ (ψ n) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = fun y : ℝ => 𝓕⁻ (W n) y := by
      funext y
      rw [SchwartzMap.fourierInv_coe]
    rw [← hcoe]
    exact (𝓕⁻ (ψ n)).integrable
  have hgood : ∀ n : ℕ, curveSigma P N (V n)
      =ᵐ[volume] ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    intro n
    have h := curveSigma_fourierInv_multiplier_ae P N ((ψ n).memLp 1 _) ((ψ n).memLp 2 _)
      (hWi n) hm
    rw [hAeq n] at h
    simpa [V, W, A, M] using h
  -- the three pieces of the `n`-th approximation
  have hpiece1 : ∀ n : ℕ, eLpNorm (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
      2 (volume : Measure ℝ) ≤ eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := by
    intro n
    rw [← eLpNorm_congr_ae (curveSigma_sub_ae P N hh (hVmem n))]
    exact curveSigma_eLpNorm_le P N (hh.sub (hVmem n))
  have hpiece2 : ∀ n : ℕ, eLpNorm (fun x : ℝ => curveSigma P N (V n) x
      - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) 2 (volume : Measure ℝ) = 0 := by
    intro n
    have hz : (fun x : ℝ => curveSigma P N (V n) x
        - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) =ᵐ[volume] 0 := by
      filter_upwards [hgood n] with x hx
      rw [hx]; simp
    rw [eLpNorm_congr_ae hz]
    simp
  have hpiece3 : ∀ n : ℕ, eLpNorm (fun x : ℝ =>
        ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - (G : ℝ → ℂ) x)
      2 (volume : Measure ℝ) ≤ eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := by
    intro n
    let MnG : Lp ℂ 2 (volume : Measure ℝ) := (M n : Lp ℂ 2 (volume : Measure ℝ)) - G
    have hsub : MnG = Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm (𝓕⁻ (A n) - H) := by
      have h := (multiplier_sub_arg (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm
        (𝓕⁻ (A n)) H).symm
      simpa [MnG, M, hGdef] using h
    have hcoe : (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
        - (G : ℝ → ℂ) x) =ᵐ[volume] (MnG : ℝ → ℂ) := by
      filter_upwards [Lp.coeFn_sub (M n) G] with x hx
      simpa only [Pi.sub_apply, MnG] using hx.symm
    rw [eLpNorm_congr_ae hcoe, hsub]
    refine (eLpNorm_multiplier_le _ hm 1 (norm_star_polyProfile_le_one P N) _).trans ?_
    rw [ENNReal.ofReal_one, one_mul, ← Lp.enorm_def]
    have hkey : ((𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) - H : Lp ℂ 2 (volume : Measure ℝ))
        = 𝓕⁻ (A n - 𝓕 H) := by
      have hH : H = 𝓕⁻ (𝓕 H) := (FourierPair.fourierInv_fourier_eq H).symm
      have step1 : ((𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) - H : Lp ℂ 2 (volume : Measure ℝ))
          = 𝓕⁻ (A n) - 𝓕⁻ (𝓕 H) :=
        congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) =>
          (𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) - Z) hH
      have step2 : (𝓕⁻ (A n) - 𝓕⁻ (𝓕 H) : Lp ℂ 2 (volume : Measure ℝ)) = 𝓕⁻ (A n - 𝓕 H) := by
        change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (A n) - (Lp.fourierTransformₗᵢ ℝ ℂ).symm (𝓕 H)
          = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (A n - 𝓕 H)
        exact (map_sub _ _ _).symm
      exact step1.trans step2
    have hnorm : ‖(𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) - H‖ₑ = ‖A n - 𝓕 H‖ₑ := by
      rw [hkey, Commons.Analysis.Fourier.BoundaryLayer.enorm_fourierInv]
    have hclass : eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ)
        = ‖A n - 𝓕 H‖ₑ := by
      have haeeq : (fun x : ℝ => h x - V n x)
          =ᵐ[volume] ((H - 𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
        filter_upwards [hcoeH, hAcoe n, Lp.coeFn_sub H (𝓕⁻ (A n))] with x hx1 hx2 hx3
        simp only [Pi.sub_apply] at hx2 hx3 ⊢
        rw [hx3, hx1, hx2]
      rw [eLpNorm_congr_ae haeeq, ← Lp.enorm_def, enorm_sub_comm_lp, hnorm]
    rw [hnorm, hclass]
  have hbd : ∀ n : ℕ, eLpNorm (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x)
        2 (volume : Measure ℝ) ≤ 2 * eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := by
    intro n
    have hsplit : (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x)
        =ᵐ[volume] ((fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
          + (fun x : ℝ => curveSigma P N (V n) x
              - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
          + (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - (G : ℝ → ℂ) x)) := by
      filter_upwards with x
      simp only [Pi.add_apply]
      ring
    have hm1 : AEStronglyMeasurable (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
        (volume : Measure ℝ) :=
      (aestronglyMeasurable_curveSigma P N hh).sub (aestronglyMeasurable_curveSigma P N (hVmem n))
    have hm2 : AEStronglyMeasurable (fun x : ℝ => curveSigma P N (V n) x
        - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) (volume : Measure ℝ) :=
      (aestronglyMeasurable_curveSigma P N (hVmem n)).sub (Lp.aestronglyMeasurable (M n))
    have hm3 : AEStronglyMeasurable (fun x : ℝ =>
        ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x - (G : ℝ → ℂ) x)
        (volume : Measure ℝ) :=
      (Lp.aestronglyMeasurable (M n)).sub (Lp.aestronglyMeasurable G)
    calc eLpNorm (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ)
        = eLpNorm ((fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
            + (fun x : ℝ => curveSigma P N (V n) x
                - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
            + (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
                - (G : ℝ → ℂ) x)) 2 (volume : Measure ℝ) := eLpNorm_congr_ae hsplit
      _ ≤ eLpNorm ((fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
            + (fun x : ℝ => curveSigma P N (V n) x
                - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)) 2 (volume : Measure ℝ)
          + eLpNorm (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
              - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ) :=
          eLpNorm_add_le (by norm_num)
      _ ≤ (eLpNorm (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x) 2 (volume : Measure ℝ)
            + eLpNorm (fun x : ℝ => curveSigma P N (V n) x
                - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) 2 (volume : Measure ℝ))
          + eLpNorm (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
              - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ) :=
          add_le_add (eLpNorm_add_le (by norm_num)) le_rfl
      _ ≤ 2 * eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := by
          have h1 := hpiece1 n
          have h2 := hpiece2 n
          have h3 := hpiece3 n
          calc (eLpNorm (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
                  2 (volume : Measure ℝ)
                + eLpNorm (fun x : ℝ => curveSigma P N (V n) x
                    - ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) 2 (volume : Measure ℝ))
              + eLpNorm (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
                  - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ)
              = (eLpNorm (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
                    2 (volume : Measure ℝ) + 0)
                + eLpNorm (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
                    - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ) := by rw [h2]
            _ = eLpNorm (fun x : ℝ => curveSigma P N h x - curveSigma P N (V n) x)
                  2 (volume : Measure ℝ)
                + eLpNorm (fun x : ℝ => ((M n : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
                    - (G : ℝ → ℂ) x) 2 (volume : Measure ℝ) := by rw [add_zero]
            _ ≤ eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ)
                + eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := add_le_add h1 h3
            _ = 2 * eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ) := by rw [two_mul]
  -- the bound tends to `0`
  have hterm : ∀ n : ℕ, eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ)
      = ‖A n - 𝓕 H‖ₑ := by
    intro n
    have haeeq : (fun x : ℝ => h x - V n x)
        =ᵐ[volume] ((H - 𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
      filter_upwards [hcoeH, hAcoe n, Lp.coeFn_sub H (𝓕⁻ (A n))] with x hx1 hx2 hx3
      simp only [Pi.sub_apply] at hx2 hx3 ⊢
      rw [hx3, hx1, hx2]
    rw [eLpNorm_congr_ae haeeq, ← Lp.enorm_def]
    have hkey : (H - 𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) = 𝓕⁻ (𝓕 H - A n) := by
      have hH : H = 𝓕⁻ (𝓕 H) := (FourierPair.fourierInv_fourier_eq H).symm
      have step1 : (H - 𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) = 𝓕⁻ (𝓕 H) - 𝓕⁻ (A n) :=
        congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) =>
          Z - (𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ))) hH
      have step2 : (𝓕⁻ (𝓕 H) - 𝓕⁻ (A n) : Lp ℂ 2 (volume : Measure ℝ)) = 𝓕⁻ (𝓕 H - A n) := by
        change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (𝓕 H) - (Lp.fourierTransformₗᵢ ℝ ℂ).symm (A n)
          = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (𝓕 H - A n)
        exact (map_sub _ _ _).symm
      exact step1.trans step2
    rw [hkey, Commons.Analysis.Fourier.BoundaryLayer.enorm_fourierInv, enorm_sub_comm_lp]
  have hlim : Tendsto (fun n : ℕ => 2 * eLpNorm (fun x : ℝ => h x - V n x) 2 (volume : Measure ℝ))
      atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n : ℕ => ‖A n - 𝓕 H‖ₑ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ‖A n - 𝓕 H‖) atTop (𝓝 0) := by
        have h := (hAtend.sub_const (𝓕 H)).norm
        simpa using h
      have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal ‖A n - 𝓕 H‖) atTop (𝓝 (ENNReal.ofReal 0)) :=
        ENNReal.continuous_ofReal.tendsto 0 |> fun hh' => hh'.comp h1
      simpa [enorm_eq_ofReal_norm'] using h2
    have h3 : Tendsto (fun n : ℕ => (2:ENNReal) * ‖A n - 𝓕 H‖ₑ) atTop (𝓝 ((2:ENNReal) * 0)) :=
      ENNReal.Tendsto.const_mul hnorm (Or.inr (by norm_num : (2:ENNReal) ≠ ⊤))
    simpa [hterm] using h3
  have hzero : eLpNorm (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x)
      2 (volume : Measure ℝ) ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbd)
  have hzero' : eLpNorm (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x)
      2 (volume : Measure ℝ) = 0 := le_antisymm hzero (zero_le)
  have hae : curveSigma P N h =ᵐ[volume] (G : ℝ → ℂ) := by
    have hdiff : (fun x : ℝ => curveSigma P N h x - (G : ℝ → ℂ) x) =ᵐ[volume] 0 :=
      (MeasureTheory.eLpNorm_eq_zero_iff
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero'
    filter_upwards [hdiff] with x hx
    simpa using sub_eq_zero.mp hx
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · have hGH : (G : ℝ → ℂ) = (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => starRingEnd ℂ (polyProfile P N ξ)) hm (hh.toLp) : ℝ → ℂ) := by
      rw [hGdef]
    rw [← hGH]
    exact hae
  · exact lt_of_le_of_lt (curveSigma_eLpNorm_le P N hh) hh.eLpNorm_lt_top

/-! ## The multiplier calculus: product and scalar rules -/

lemma multiplier_sub_sym (m₁ m₂ : ℝ → ℂ) (h₁ : MemLp m₁ ⊤ (volume : Measure ℝ))
    (h₂ : MemLp m₂ ⊤ (volume : Measure ℝ))
    (h₁₂ : MemLp (fun ξ : ℝ => m₁ ξ - m₂ ξ) ⊤ (volume : Measure ℝ))
    (H : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => m₁ ξ - m₂ ξ) h₁₂ H
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁ H
        - Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ H := by
  have e₁ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁ H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)) := rfl
  have e₂ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H)) := rfl
  have e₃ : Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => m₁ ξ - m₂ ξ) h₁₂ H
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp (fun ξ : ℝ => m₁ ξ - m₂ ξ) h₁₂ (𝓕 H)) := rfl
  rw [e₁, e₂, e₃]
  have hmul : Commons.Analysis.Fourier.BoundaryLayer.mulLp (fun ξ : ℝ => m₁ ξ - m₂ ξ) h₁₂ (𝓕 H)
      = Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)
        - Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H) := by
    apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe (fun ξ : ℝ => m₁ ξ - m₂ ξ) h₁₂ (𝓕 H),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₁ h₁ (𝓕 H),
      Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₂ h₂ (𝓕 H),
      Lp.coeFn_sub (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H))
        (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H))]
      with ξ e3 e1 e2 e0
    rw [e3, e0, Pi.sub_apply, e1, e2]
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hmul]
  change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H)
      - Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H))
    = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁ (𝓕 H))
      - (Lp.fourierTransformₗᵢ ℝ ℂ).symm (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 H))
  exact map_sub _ _ _

lemma multiplier_const_smul (c : ℂ) (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmc : MemLp (fun ξ : ℝ => c * m ξ) ⊤ (volume : Measure ℝ))
    (X : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => c * m ξ) hmc X
      = c • Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm X := by
  have e₁ : Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => c * m ξ) hmc X
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp (fun ξ : ℝ => c * m ξ) hmc (𝓕 X)) := rfl
  have e₂ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm X
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X)) := rfl
  rw [e₁, e₂,
    show c • 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X))
      = 𝓕⁻ (c • Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X)) from
      (map_smul (Lp.fourierTransformₗᵢ ℝ ℂ).symm c
        (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X))).symm]
  congr 1
  apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe (fun ξ : ℝ => c * m ξ) hmc (𝓕 X),
    Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (𝓕 X), Lp.coeFn_smul c (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 X))]
    with ξ e1 e2 e3
  simp only [Pi.mul_apply, Pi.smul_apply] at e1 e2 e3 ⊢
  rw [e1, e3, e2]
  ring

lemma multiplier_mul (m₁ m₂ : ℝ → ℂ) (h₁ : MemLp m₁ ⊤ (volume : Measure ℝ))
    (h₂ : MemLp m₂ ⊤ (volume : Measure ℝ))
    (h₁₂ : MemLp (fun ξ : ℝ => m₁ ξ * m₂ ξ) ⊤ (volume : Measure ℝ))
    (X : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ X)
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => m₁ ξ * m₂ ξ) h₁₂ X := by
  have e₂ : Commons.Analysis.Fourier.BoundaryLayer.multiplier m₂ h₂ X
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 X)) := rfl
  rw [e₂, show Commons.Analysis.Fourier.BoundaryLayer.multiplier m₁ h₁
      (𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 X)))
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₁ h₁
          (𝓕 (𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 X))))) from rfl,
    FourierInvPair.fourier_fourierInv_eq]
  congr 1
  apply Lp.ext (α := ℝ) (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
  filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₁ h₁
      (Commons.Analysis.Fourier.BoundaryLayer.mulLp m₂ h₂ (𝓕 X)),
    Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m₂ h₂ (𝓕 X),
    Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe (fun ξ : ℝ => m₁ ξ * m₂ ξ) h₁₂ (𝓕 X)]
    with ξ e1 e2 e3
  simp only [Pi.mul_apply] at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  ring

lemma dyadTilde_abs_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, |dyadTilde η| ≤ B := by
  have hc : Continuous dyadTheta := dyadTheta_spec.1.continuous
  have hs : HasCompactSupport dyadTheta := dyadTheta_spec.2.1
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_continuous_hasCompactSupport hc hs
  refine ⟨B, hB0, fun η => ?_⟩
  rw [dyadTilde]
  exact hB (η / 2)


/-! ## Small generic helpers for the assembly of `Ts_l2_decay` -/

/-- Compact support is preserved by precomposition with a nonzero scaling. -/
lemma hasCompactSupport_comp_mul_left' {β : Type*} [TopologicalSpace β] [Zero β]
    {f : ℝ → β} (hf : HasCompactSupport f) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (fun ξ : ℝ => f (c * ξ)) := by
  have hcomp : IsCompact ((fun y : ℝ => y / c) '' (tsupport f)) :=
    (show IsCompact (tsupport f) from hf).image (by fun_prop)
  refine HasCompactSupport.of_support_subset_isCompact hcomp ?_
  intro ξ hξ
  change f (c * ξ) ≠ 0 at hξ
  exact ⟨c * ξ, subset_tsupport f hξ, by field_simp⟩

/-- The multiplier applied to `0` is `0`. -/
lemma multiplier_Lpzero (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (0 : Lp ℂ 2 (volume : Measure ℝ)) = 0 := by
  rw [show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (0 : Lp ℂ 2 (volume : Measure ℝ))
      = 𝓕⁻ (Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (𝓕 (0 : Lp ℂ 2 (volume : Measure ℝ)))) from rfl,
    show 𝓕 (0 : Lp ℂ 2 (volume : Measure ℝ)) = 0 from map_zero _]
  have h : Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (0 : Lp ℂ 2 (volume : Measure ℝ)) = 0 := by
    apply Lp.ext (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (0 : Lp ℂ 2 (volume : Measure ℝ)),
      Lp.coeFn_zero ℂ (p := 2) (μ := (volume : Measure ℝ))] with ξ e1 e2
    rw [e1, e2]
    simp
  rw [h]
  exact map_zero _

/-- A finite sum of a.e. equal functions is a.e. equal. -/
lemma ae_eq_finset_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, f i =ᵐ[volume] g i) :
    (∑ i ∈ s, f i) =ᵐ[volume] (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end

end Work.BourgainPlan.Maximal
