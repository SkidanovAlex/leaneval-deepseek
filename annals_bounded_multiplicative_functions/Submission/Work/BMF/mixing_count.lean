import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.triangle_fourier_pair
import Submission.Work.BMF.N7.mixing_wire
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/BMF/DESIGN.md (the lead's design for MRTTZ; your node's section has exact formulas). Shared definitions: Submission/Work/BMF/Defs.lean (do NOT edit). Owned library assets are being installed now (see Submission/Work/BMF/ASSETS.md once it exists, and DESIGN.md §8); import them instead of re-proving. Sibling nodes you import are proved in parallel; build against their statements.

# N7 `mixing_count`: the MRT mixing count

**Source.** MRT (1812.01224) Lemma 5.1 (`papers/mrt_fourier/short-uniformity.tex`, §5).

**Imports.** `Submission.Work.BMF.Defs`, and (via `Submission.Work.BMF.mixing_tbound`) the
fleet's Vinogradov–Korobov node **V6** `Submission.Work.BMF.zeta_prime_sum_twist`, which is the
`q = 1`, `χ = 1` case of N10 and is what step 3 below actually uses; the N10 wrappers that other
nodes (`N4`, `N9`, `N11`) need (non-principal `χ`, the principal-character reduction) are *not*
required here.  **Status of this node**: everything below is proved; the axiom footprint is that
of V6, i.e. currently `Work.BMF.ztw_param` and `Work.BMF.logDeriv_LFunction_VK`.

**Owned assets.**
- LVE `Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`, with
  frequencies `μ_n = log x_n`. Their separation is `≥ L/(20X)`, which gives MRT Lemma 2.3:
  `∫_{|t| ≤ T} |Σ_n e^{it log x_n}|² ≤ (2T + C·20X/L)·R`.

## Route

**1. Majorant.** Take the Fejér kernel `ψ(u) = (sin πu/(πu))²`, with `ψ̂(ξ) = (1−|ξ|)₊` and
`ψ ≥ 4/π²` on `|u| ≤ 1/2`. Since `x₁ ≥ X/10`, the condition `|x₁ − (p₂/p₁)x₂| ≤ 100L` forces
`|log(x₁p₁/(x₂p₂))| ≤ 2000 L/X`.

Use `ψ((X/(4000L)) · log(x₁p₁/(x₂p₂)))`, weighted by `π²/4`.

**2. Fourier inversion.** The sum becomes
`(4000L/X) ∫_{|ξ|≤X/(4000L)} ψ̂(4000Lξ/X) S₁(ξ) S̄₂(ξ) |T(ξ)|² dξ`,
where `S_i(ξ) = Σ_{x∈A_i} e(ξ log x)` and `T(ξ) = Σ_{p∈[P,2P]} p^{2πiξ}`.

**3. Bound on `T` (N10 plus partial summation).** For `|ξ| ≤ X`:
`|T(ξ)| ≤ C π₀(P)(1/(1+|ξ|) + (log P)^{-1})`.

This is valid because `2π|ξ| ≤ 2πX ≤ exp((log P)^{21/20})` when `P ≥ X^{c₀}` and `X` is large.

**4. Split and conclude.**
- The `1/(1+|ξ|)²` part: `|S_i| ≤ #A_i` gives the main term.
- The `(log P)^{-2}` part: Cauchy–Schwarz and step 0's large sieve give
  `√(#A₁#A₂) · d/(log P)²`.

## Size and risk

Size 2–4k. Risk low-medium. Mathlib has the Fejér kernel Fourier pair in pieces. Alternatively,
build `ψ̂` as a triangle and compute `ψ` directly.
-/

namespace Work.BMF

set_option maxHeartbeats 8000000

open Polynomial MeasureTheory Filter


/-! ## Local definitions for the mixing count -/

/-- The Fejér kernel `ψ(u) = (sinc (π u))²`, the squared sinc. It is the inverse Fourier transform
of the triangle function `x ↦ max (1 - |x|) 0` and satisfies `4/π² ≤ ψ(u)` for `|u| ≤ 1/2`. -/
noncomputable def fejer (u : ℝ) : ℝ := (Real.sinc (Real.pi * u)) ^ 2

/-- The exponential sum `S(η) = ∑_{x ∈ A} e(η log x)` over a finite set of points of the positive
half-line. -/
noncomputable def Smix (A : Finset ℝ) (η : ℝ) : ℂ := ∑ x ∈ A, eC (η * Real.log x)

/-- The prime exponential sum `T(η) = ∑_{P ≤ p ≤ 2P} e(η log p) = ∑_{P ≤ p ≤ 2P} p^{2πiη}`. -/
noncomputable def Tmix (P η : ℝ) : ℂ := ∑ p ∈ primesIn P (2 * P), eC (η * Real.log p)


/-- The Fejér kernel is nonnegative. -/
lemma fejer_nonneg (u : ℝ) : 0 ≤ fejer u := by
  rw [fejer]; positivity

/-- Continuity of the exponential sum `Smix`. -/
@[fun_prop] lemma continuous_Smix (A : Finset ℝ) : Continuous fun η : ℝ => Smix A η := by
  unfold Smix
  refine continuous_finsetSum _ (fun x _ => ?_)
  unfold eC
  fun_prop

/-- Continuity of the prime exponential sum `Tmix`. -/
@[fun_prop] lemma continuous_Tmix (Pη : ℝ) : Continuous fun η : ℝ => Tmix Pη η := by
  unfold Tmix
  refine continuous_finsetSum _ (fun x _ => ?_)
  unfold eC
  fun_prop

/-- Continuity of the weight `1 - |η|/c`. -/
lemma continuous_weight (c : ℝ) : Continuous fun η : ℝ => (((1 - |η| / c : ℝ)) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_const.sub (continuous_abs.div_const c))

/-- Continuity of the product `Smix A₁ · conj (Smix A₂) · Tmix P₀ · conj (Tmix P₀)`. -/
lemma continuous_G (A₁ A₂ : Finset ℝ) (P₀ : ℝ) : Continuous fun η : ℝ =>
    Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P₀ η * (starRingEnd ℂ) (Tmix P₀ η)) :=
  ((continuous_Smix A₁).mul (continuous_Smix A₂).star).mul
    ((continuous_Tmix P₀).mul (continuous_Tmix P₀).star)

/-- Continuity of `η ↦ (1 + |η|)^{-2}`. -/
lemma continuous_inv_one_add_abs_sq : Continuous fun η : ℝ => (1 / (1 + |η|)) ^ 2 := by
  have h1 : Continuous fun η : ℝ => (1 + |η|)⁻¹ := by
    apply Continuous.inv₀ (by fun_prop)
    intro η; positivity
  have h2 : (fun η : ℝ => (1 / (1 + |η|)) ^ 2) = (fun η : ℝ => ((1 + |η|)⁻¹) ^ 2) := by
    funext η; rw [one_div]
  rw [h2]; exact h1.pow 2

/-- The exponential character has unit modulus. -/
lemma n7_norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The norm of a real complex number. -/
lemma norm_ofReal_C (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have h1 : 0 ≤ ‖(r : ℂ)‖ := norm_nonneg _
  nlinarith [sq_abs r, abs_nonneg r]

/-- Interval integrability of continuous functions with respect to Lebesgue measure. -/
lemma ii_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable f volume a b := hf.intervalIntegrable a b

@[fun_prop] lemma continuous_Smix2 (A : Finset ℝ) : Continuous fun η : ℝ => Smix A η := continuous_Smix A

/-- **Geometric input of the majorant step.** For a quadruple `(x₁,x₂,p₁,p₂)` with
`x₁, x₂ ∈ [X/10, 10X]`, `p₁, p₂ ∈ [P, 2P]` and `|x₁ - (p₂/p₁) x₂| ≤ 100 L`, the logarithm
`log (x₁p₁/(x₂p₂))` is at most `1/2` in modulus after scaling by `X/(8000 L)`. -/
lemma abs_scaled_log_le {X L P x₁ x₂ : ℝ} {p₁ p₂ : ℕ}
    (hX : 0 < X) (hL : 0 < L) (hP : 0 < P) (hp1 : (0:ℝ) < p₁) (hp2 : (0:ℝ) < p₂)
    (hx1 : X / 10 ≤ x₁) (hx1' : x₁ ≤ 10 * X) (hx2 : X / 10 ≤ x₂) (hx2' : x₂ ≤ 10 * X)
    (hp1P : P ≤ (p₁ : ℝ)) (hp1P' : (p₁ : ℝ) ≤ 2 * P) (hp2P : P ≤ (p₂ : ℝ)) (hp2P' : (p₂ : ℝ) ≤ 2 * P)
    (hcon : |x₁ - ((p₂ : ℝ) / p₁) * x₂| ≤ 100 * L) :
    |(X / (8000 * L)) * (Real.log x₁ + Real.log (p₁ : ℝ) - Real.log x₂ - Real.log (p₂ : ℝ))|
      ≤ 1 / 2 := by
  have hx1pos : 0 < x₁ := by linarith
  have hx2pos : 0 < x₂ := by linarith
  have hq : 0 < ((p₂ : ℝ) / p₁) * x₂ := by positivity
  have hqge : X / 20 ≤ ((p₂ : ℝ) / p₁) * x₂ := by
    have h1 : (1:ℝ) / 2 ≤ (p₂ : ℝ) / p₁ := by rw [le_div_iff₀ hp1]; linarith
    nlinarith
  have hlogeq : Real.log x₁ + Real.log (p₁ : ℝ) - Real.log x₂ - Real.log (p₂ : ℝ)
      = Real.log (x₁ / (((p₂ : ℝ) / p₁) * x₂)) := by
    rw [Real.log_div (ne_of_gt hx1pos) (ne_of_gt hq),
      Real.log_mul (by positivity : ((p₂:ℝ)/p₁) ≠ 0) (ne_of_gt hx2pos),
      Real.log_div (ne_of_gt hp2) (ne_of_gt hp1)]
    ring
  set q : ℝ := ((p₂ : ℝ) / p₁) * x₂ with hqdef
  have hqpos : 0 < q := hq
  have hqge' : X / 20 ≤ q := hqge
  have hcon' : |x₁ - q| ≤ 100 * L := hcon
  have key : |Real.log (x₁ / q)| ≤ 2000 * L / X := by
    have hle1 : x₁ - q ≤ 100 * L := (abs_le.mp hcon').2
    have hle2 : q - x₁ ≤ 100 * L := by linarith [(abs_le.mp hcon').1]
    rcases le_total q x₁ with hcase | hcase
    · -- q ≤ x₁ : ratio ≥ 1
      have hdiv : x₁ / q - 1 = (x₁ - q) / q := by field_simp <;> ring
      have hb : x₁ / q - 1 ≤ 2000 * L / X := by
        rw [hdiv, div_le_div_iff₀ hqpos hX]
        nlinarith [hle1, hqge']
      have hge1 : 1 ≤ x₁ / q := (one_le_div hqpos).mpr hcase
      have hlognn : 0 ≤ Real.log (x₁ / q) := Real.log_nonneg hge1
      rw [abs_of_nonneg hlognn]
      exact le_trans (Real.log_le_sub_one_of_pos (by positivity)) hb
    · -- x₁ ≤ q : ratio ≤ 1
      have hrle1 : x₁ / q ≤ 1 := (div_le_one hqpos).mpr hcase
      have hlognp : Real.log (x₁ / q) ≤ 0 := Real.log_nonpos (by positivity) hrle1
      have hqeq : q = x₁ + (q - x₁) := by ring
      have h1 : Real.log (q / x₁) = Real.log (1 + (q - x₁) / x₁) := by
        rw [hqeq]
        congr 1
        field_simp <;> ring
      have h2 : Real.log (1 + (q - x₁) / x₁) ≤ (q - x₁) / x₁ := by
        have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (q - x₁) / x₁ by positivity)
        linarith
      have h3 : (q - x₁) / x₁ ≤ 1000 * L / X := by
        rw [div_le_div_iff₀ hx1pos hX]
        nlinarith [hle2, hx1]
      have hneg : -Real.log (x₁ / q) = Real.log (q / x₁) := by
        rw [Real.log_div (ne_of_gt hx1pos) (ne_of_gt hqpos),
          Real.log_div (ne_of_gt hqpos) (ne_of_gt hx1pos)]
        ring
      have hmain : -Real.log (x₁ / q) ≤ 1000 * L / X := by rw [hneg, h1]; linarith
      rw [abs_of_nonpos hlognp]
      have htwo : (2000:ℝ) * L / X = 2 * (1000 * L / X) := by ring
      linarith
  have hkey2 : Real.log x₁ + Real.log (p₁ : ℝ) - Real.log x₂ - Real.log (p₂ : ℝ)
      = Real.log (x₁ / q) := by rw [hlogeq]
  rw [hkey2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < X / (8000 * L))]
  have hXpos : (0:ℝ) < X / (8000 * L) := by positivity
  calc X / (8000 * L) * |Real.log (x₁ / q)| ≤ X / (8000 * L) * (2000 * L / X) :=
        mul_le_mul_of_nonneg_left key hXpos.le
    _ = 1 / 4 := by field_simp <;> ring
    _ ≤ 1 / 2 := by norm_num

/-- `d / C ≤ log y - log x` when `0 < d ≤ y - x` and `max x y ≤ C`. -/
lemma log_sub_log_ge {x y C d : ℝ} (hx : 0 < x) (hxC : x ≤ C) (hy : 0 < y) (hyC : y ≤ C)
    (hC : 0 < C) (hd : 0 ≤ d) (hxy : d ≤ y - x) : d / C ≤ Real.log y - Real.log x := by
  have h1 : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'
  rw [← h1]
  have h2 : 1 - x / y ≤ Real.log (y / x) := by
    have h3 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hx.ne' hy.ne'] at h3
    linarith
  have hbase : 0 ≤ y - x := by linarith
  have h4 : d / C ≤ 1 - x / y := by
    have h5 : (y - x) / C ≤ (y - x) / y := by
      rw [div_le_div_iff₀ hC hy]
      nlinarith
    have h6 : d / C ≤ (y - x) / C := by
      rw [div_le_div_iff_of_pos_right hC]; exact hxy
    have h9 : (y - x) / y = 1 - x / y := by field_simp <;> ring
    linarith
  linarith

/-- Cauchy–Schwarz for interval integrals of nonnegative real functions. -/
lemma interval_integral_mul_le_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t) volume a b)
    (hnf : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hng : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    ∫ t in a..b, f t * g t ≤ Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  set A : ℝ := ∫ t in a..b, f t ^ 2 with hA
  set B : ℝ := ∫ t in a..b, f t * g t with hB
  set C : ℝ := ∫ t in a..b, g t ^ 2 with hC
  have hA0 : 0 ≤ A := by rw [hA]; exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact intervalIntegral.integral_nonneg hab (fun t ht => mul_nonneg (hnf t ht) (hng t ht))
  have hquad : ∀ s : ℝ, 0 ≤ A * s ^ 2 - 2 * B * s + C := by
    intro s
    have h1 : (0:ℝ) ≤ ∫ t in a..b, (s * f t - g t) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have h2 : (∫ t in a..b, (s * f t - g t) ^ 2) = A * s ^ 2 - 2 * B * s + C := by
      have hpt : (fun t => (s * f t - g t) ^ 2)
          = (fun t => s ^ 2 * (f t ^ 2) - (2 * s) * (f t * g t) + (g t ^ 2)) := by
        funext t; ring
      rw [hpt, intervalIntegral.integral_add ((hf.const_mul _).sub (hfg.const_mul _)) hg,
        intervalIntegral.integral_sub (hf.const_mul _) (hfg.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [← hA, ← hB, ← hC]
      ring
    linarith
  have hB2 : B ^ 2 ≤ A * C := by
    rcases lt_or_ge 0 A with hpos | hle
    · have h := hquad (B / A)
      have hmin : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by
        field_simp <;> ring
      rw [hmin] at h
      have h2 : B ^ 2 / A ≤ C := by linarith
      rw [div_le_iff₀ hpos] at h2
      linarith
    · have hAz : A = 0 := le_antisymm hle hA0
      have hBz : B = 0 := by
        by_contra hBne
        set s : ℝ := (C + 1) / (2 * B) with hsdef
        have hs : 2 * B * s = C + 1 := by
          rw [hsdef]; field_simp <;> ring
        have h := hquad s
        rw [hAz] at h
        have hzero : (0:ℝ) * s ^ 2 = 0 := by simp
        rw [hzero, hs] at h
        linarith
      rw [hBz, hAz]; simp
  have hfinal : B ≤ Real.sqrt A * Real.sqrt C := by
    calc B ≤ Real.sqrt (A * C) := by
          rw [← Real.sqrt_sq hB0]
          exact Real.sqrt_le_sqrt hB2
      _ = Real.sqrt A * Real.sqrt C := Real.sqrt_mul hA0 C
  rw [hA, hB, hC]
  exact hfinal

/-- Separation of the logarithmic frequencies of an `L`-separated point set inside `[X/10,10X]`. -/
lemma log_freq_sep {X L x y : ℝ} (hX : 0 < X) (hL : 0 < L)
    (hx : X / 10 ≤ x) (hx' : x ≤ 10 * X) (hy : X / 10 ≤ y) (hy' : y ≤ 10 * X)
    (hxy : L ≤ |x - y|) : L / (20 * X) ≤ |Real.log x - Real.log y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rcases le_total x y with hle | hle
  · have hd : L ≤ y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hxy; linarith
    have h1 : L / y ≤ Real.log y - Real.log x := by
      have h5 : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy0.ne' hx0.ne'
      rw [← h5]
      have h6 : 1 - x / y ≤ Real.log (y / x) := by
        have h7 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div hx0.ne' hy0.ne'] at h7
        have h71 : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy0.ne' hx0.ne'
        rw [h71]
        linarith
      have h8 : (y - x) / y = 1 - x / y := by field_simp <;> ring
      have h9 : L / y ≤ (y - x) / y := (div_le_div_iff_of_pos_right hy0).mpr hd
      linarith
    have h2 : L / (20 * X) ≤ L / y := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 20 * X) hy0]
      nlinarith
    have h3 : |Real.log x - Real.log y| = Real.log y - Real.log x := by
      have hpos : 0 < L / y := by positivity
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h3]; linarith
  · have hd : L ≤ x - y := by
      rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hxy; linarith
    have h1 : L / x ≤ Real.log x - Real.log y := by
      have h5 : Real.log (x / y) = Real.log x - Real.log y := Real.log_div hx0.ne' hy0.ne'
      rw [← h5]
      have h6 : 1 - y / x ≤ Real.log (x / y) := by
        have h7 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div hy0.ne' hx0.ne'] at h7
        have h71 : Real.log (x / y) = Real.log x - Real.log y := Real.log_div hx0.ne' hy0.ne'
        rw [h71]
        linarith
      have h8 : (x - y) / x = 1 - y / x := by field_simp <;> ring
      have h9 : L / x ≤ (x - y) / x := (div_le_div_iff_of_pos_right hx0).mpr hd
      linarith
    have h2 : L / (20 * X) ≤ L / x := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 20 * X) hx0]
      nlinarith
    have h3 : |Real.log x - Real.log y| = Real.log x - Real.log y := by
      have hpos : 0 < L / x := by positivity
      exact abs_of_nonneg (by linarith)
    rw [h3]; linarith

/-- Membership in `primesIn a b` gives primality and the size bounds. -/
lemma mem_primesIn {a b : ℝ} {p : ℕ} (hb : 0 ≤ b) (h : p ∈ primesIn a b) :
    p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b := by
  rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at h
  obtain ⟨⟨h1, h2⟩, hp⟩ := h
  refine ⟨hp, ?_, ?_⟩
  · have h3 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h4 : (⌈a⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
    linarith
  · have h3 : (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast h2
    have h4 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
    linarith

/-- Expansion of a fourfold product of finite sums into a fourfold nested sum. -/
private lemma sum4_prod {ι κ μ ν : Type*} (s : Finset ι) (t : Finset κ) (u : Finset μ) (v : Finset ν)
    (F : ι → ℂ) (G : κ → ℂ) (H : μ → ℂ) (K : ν → ℂ) :
    (∑ i ∈ s, F i) * (∑ j ∈ t, G j) * ((∑ k ∈ u, H k) * (∑ l ∈ v, K l))
      = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, ∑ l ∈ v, F i * G j * H k * K l := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _
  ring


/-- **Finset form of the owned mean value bound for separated frequencies.**
This is `Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies` transported to
`Finset`-indexed sums (the owned lemma is stated for families indexed by `Fin X`). -/
lemma mv_finset_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset ℝ) (μ : ℝ → ℝ) (c δ : ℝ), 0 < c → 0 < δ →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |μ x - μ y|) →
      ∫ η in (-c)..c, ‖∑ x ∈ A, eC (η * μ x)‖ ^ 2 ≤ K * (A.card : ℝ) * (c + 1 / δ) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨max 2 (C / (2 * Real.pi)) + 1, by positivity, ?_⟩
  intro A μ c δ hc hδ hsep
  have h2π : 0 < 2 * Real.pi := by positivity
  have hδ' : 0 < 2 * Real.pi * δ := mul_pos h2π hδ
  set n : ℕ := A.card with hn
  set μ' : Fin n → ℝ := fun i => 2 * Real.pi * μ ((A.equivFin.symm i).val) with hμ'
  have hsep' : ∀ i j : Fin n, i ≠ j → 2 * Real.pi * δ ≤ |μ' i - μ' j| := by
    intro i j hij
    have hne : ((A.equivFin.symm i).val : ℝ) ≠ (A.equivFin.symm j).val := by
      intro h
      exact hij (A.equivFin.symm.injective (Subtype.ext h))
    have h1 : δ ≤ |μ ((A.equivFin.symm i).val) - μ ((A.equivFin.symm j).val)| :=
      hsep _ (A.equivFin.symm i).2 _ (A.equivFin.symm j).2 hne
    have h2 : μ' i - μ' j
        = 2 * Real.pi * (μ ((A.equivFin.symm i).val) - μ ((A.equivFin.symm j).val)) := by
      simp only [hμ']
      ring
    rw [h2, abs_mul, abs_of_pos h2π]
    nlinarith [Real.pi_pos, h1]
  have hmain := hC (2 * Real.pi * δ) hδ' n μ' (fun _ => 1) hsep' (-c) c (by linarith)
  have hsum : ∀ η : ℝ, (∑ i : Fin n, (1 : ℂ) * Complex.exp (Complex.I * ((μ' i : ℂ) * (η : ℂ))))
      = ∑ x ∈ A, eC (η * μ x) := by
    intro η
    rw [← Finset.sum_attach A (fun x => eC (η * μ x))]
    refine Fintype.sum_equiv (Finset.equivFin A).symm
      (fun i : Fin n => (1 : ℂ) * Complex.exp (Complex.I * ((μ' i : ℂ) * (η : ℂ))))
      (fun x : ↥A => eC (η * μ x.val)) ?_
    intro i
    simp only [hμ', Equiv.symm_apply_apply, one_mul, eC]
    congr 1
    push_cast
    ring
  have hcard : (∑ _i : Fin n, ‖(1 : ℂ)‖ ^ 2) = (A.card : ℝ) := by
    simp [n]
  have hnorm : ∀ η : ℝ, ‖∑ i : Fin n, (1 : ℂ) * Complex.exp (Complex.I * ((μ' i : ℂ) * (η : ℂ)))‖ ^ 2
      = ‖∑ x ∈ A, eC (η * μ x)‖ ^ 2 := by
    intro η; rw [hsum η]
  calc ∫ η in (-c)..c, ‖∑ x ∈ A, eC (η * μ x)‖ ^ 2
      = ∫ η in (-c)..c, ‖∑ i : Fin n, (1 : ℂ) * Complex.exp (Complex.I * ((μ' i : ℂ) * (η : ℂ)))‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro η _
        simp only []
        rw [hnorm η]
    _ ≤ (c - -c + C / (2 * Real.pi * δ)) * (A.card : ℝ) := by
        rw [← hcard]
        exact hmain
    _ ≤ (max 2 (C / (2 * Real.pi)) + 1) * (A.card : ℝ) * (c + 1 / δ) := by
        have hcard0 : (0:ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
        have h1 : c - -c = 2 * c := by ring
        rw [h1]
        have h2 : C / (2 * Real.pi * δ) = (C / (2 * Real.pi)) / δ := by
          rw [div_div]
        rw [h2]
        have h3 : 2 * c + (C / (2 * Real.pi)) / δ
            ≤ (max 2 (C / (2 * Real.pi)) + 1) * (c + 1 / δ) := by
          have h4 : 2 ≤ max 2 (C / (2 * Real.pi)) + 1 :=
            le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
          have h5 : C / (2 * Real.pi) ≤ max 2 (C / (2 * Real.pi)) + 1 :=
            le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
          have h7 : (0:ℝ) ≤ 1 / δ := by positivity
          have h8 : (0:ℝ) ≤ c := hc.le
          have h9 : 2 * c ≤ (max 2 (C / (2 * Real.pi)) + 1) * c :=
            mul_le_mul_of_nonneg_right h4 h8
          have h10 : (C / (2 * Real.pi)) / δ ≤ (max 2 (C / (2 * Real.pi)) + 1) * (1 / δ) := by
            calc (C / (2 * Real.pi)) / δ = (C / (2 * Real.pi)) * (1 / δ) := by ring
              _ ≤ (max 2 (C / (2 * Real.pi)) + 1) * (1 / δ) :=
                  mul_le_mul_of_nonneg_right h5 h7
          have hexp : (max 2 (C / (2 * Real.pi)) + 1) * (c + 1 / δ)
              = (max 2 (C / (2 * Real.pi)) + 1) * c
                + (max 2 (C / (2 * Real.pi)) + 1) * (1 / δ) := by ring
          rw [hexp]
          linarith
        calc (2 * c + (C / (2 * Real.pi)) / δ) * (A.card : ℝ)
            ≤ (max 2 (C / (2 * Real.pi)) + 1) * (c + 1 / δ) * (A.card : ℝ) :=
              mul_le_mul_of_nonneg_right h3 hcard0
          _ = (max 2 (C / (2 * Real.pi)) + 1) * (A.card : ℝ) * (c + 1 / δ) := by ring

/-- **Auxiliary form of `mixing_count`, with the analytic inputs as hypotheses.**

`hpair`/`hfejer` are the triangle/Fejér Fourier pair (so that `ψ` is a majorant with the explicit
inverse Fourier transform `(1-|ξ|)_+`), `hsieve` is the separated-frequency mean value bound for the
point sets, and `hT` is the prime exponential sum bound. The proof is the MRT §5 argument: the
Fourier majorant, the separation mean value, Cauchy–Schwarz and the prime sum bound. -/
theorem mixing_count_aux
    (hpair : ∀ u : ℝ, ∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) * eC (x * u)) =
      ((Real.sinc (Real.pi * u)) ^ 2 : ℂ))
    (hfejer : ∀ u : ℝ, |u| ≤ 1 / 2 → 4 / Real.pi ^ 2 ≤ (Real.sinc (Real.pi * u)) ^ 2)
    (hsieve : ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset ℝ) (μ : ℝ → ℝ) (c δ : ℝ), 0 < c → 0 < δ →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |μ x - μ y|) →
      ∫ η in (-c)..c, ‖∑ x ∈ A, eC (η * μ x)‖ ^ 2 ≤ K * (A.card : ℝ) * (c + 1 / δ))
    (hT : ∃ K P₀ : ℝ, 0 < K ∧ ∀ (P η : ℝ), P₀ ≤ P → 1 ≤ Real.log P →
      |η| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi) →
      ‖Tmix P η‖ ≤ K * pi0 P * (1 / (1 + |η|) + 1 / Real.log P))
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (X L P : ℝ) (A₁ A₂ : Finset ℝ), X₀ ≤ X → X ^ c₀ ≤ P →
      P ≤ X ^ (1 / 4 : ℝ) → X ^ c₀ ≤ L → L ≤ X →
      (∀ x ∈ A₁ ∪ A₂, X / 10 ≤ x ∧ x ≤ 10 * X) →
      (∀ x ∈ A₁, ∀ y ∈ A₁, x ≠ y → L ≤ |x - y|) → (∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ y → L ≤ |x - y|) →
      ((((A₁ ×ˢ A₂) ×ˢ (primesIn P (2 * P) ×ˢ primesIn P (2 * P))).filter
          (fun v ↦ |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ)
        ≤ C * ((A₁.card : ℝ) * A₂.card * (L / X) * pi0 P ^ 2 +
            Real.sqrt ((A₁.card : ℝ) * A₂.card) * pi0 P ^ 2 / Real.log P) := by
  obtain ⟨KT, PT, hKTpos, hTbound⟩ := hT
  obtain ⟨KS, hKSpos, hSbound⟩ := hsieve
  -- Thresholds
  have hth1 : ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X → max PT 0 + 1 ≤ X ^ c₀ := by
    have htend : Tendsto (fun X : ℝ => X ^ c₀) atTop atTop := tendsto_rpow_atTop hc₀
    obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp
      (htend.eventually (Filter.eventually_ge_atTop (max PT 0 + 1)))
    exact ⟨Y, fun X hX => hY X hX⟩
  have hth2 : ∃ Y : ℝ, ∀ X : ℝ, Y ≤ X →
      2 * Real.pi * X ^ (1 - c₀) / 8000 ≤ Real.exp ((c₀ * Real.log X) ^ (21 / 20 : ℝ)) := by
    refine ⟨Real.exp (((max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ)) + 1) + 2, ?_⟩
    intro X hX
    have hYpos : (0:ℝ) < Real.exp (((max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ)) + 1) :=
      Real.exp_pos _
    have hXpos : 0 < X := by linarith
    have hlogX : ((max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ)) + 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      linarith
    have hB0 : 0 ≤ max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ) :=
      div_nonneg (le_max_right _ _) (Real.rpow_nonneg hc₀.le _)
    have hB4 : 0 ≤ (max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ) := pow_nonneg hB0 _
    set u : ℝ := Real.log X with hudef
    have hu1 : 1 ≤ u := by linarith
    have hu0 : 0 ≤ u := by linarith
    have hquarter : max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ) ≤ u ^ (1 / 20 : ℝ) := by
      have h1 : (max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ) ≤ u := by linarith
      have h2 := Real.rpow_le_rpow hB4 h1 (by norm_num : (0:ℝ) ≤ 1/20)
      have h3 : ((max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) ^ (20 : ℕ)) ^ (1 / 20 : ℝ)
          = max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ) := by
        rw [← Real.rpow_natCast (max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) 20, ← Real.rpow_mul hB0]
        norm_num
      linarith [h2, h3.le, h3.ge]
    have hkey : (1 - c₀) * u ≤ (c₀ * u) ^ (21 / 20 : ℝ) := by
      have h1 : c₀ ^ (21 / 20 : ℝ) * u ^ (1 / 20 : ℝ)
          ≥ c₀ ^ (21 / 20 : ℝ) * (max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) := by
        have h5 : 0 ≤ c₀ ^ (21 / 20 : ℝ) := Real.rpow_nonneg hc₀.le _
        exact mul_le_mul_of_nonneg_left hquarter h5
      have h6 : c₀ ^ (21 / 20 : ℝ) * (max (1 - c₀) 0 / c₀ ^ (21 / 20 : ℝ)) = max (1 - c₀) 0 := by
        have h5 : (0:ℝ) < c₀ ^ (21 / 20 : ℝ) := Real.rpow_pos_of_pos hc₀ _
        field_simp
      have h7 : u ^ (21 / 20 : ℝ) = u ^ (1 / 20 : ℝ) * u := by
        rw [show (21/20 : ℝ) = 1/20 + 1 by norm_num, Real.rpow_add (by linarith : (0:ℝ) < u),
          Real.rpow_one]
      have h8 : (c₀ * u) ^ (21 / 20 : ℝ) = c₀ ^ (21 / 20 : ℝ) * u ^ (21 / 20 : ℝ) :=
        Real.mul_rpow hc₀.le hu0
      rw [h8, h7]
      have h9 : (1 - c₀) ≤ max (1 - c₀) 0 := le_max_left _ _
      nlinarith [h1, h6.le, h6.ge, h9, hu0, hB0]
    have hfin : X ^ (1 - c₀) = Real.exp ((1 - c₀) * u) := by
      rw [Real.rpow_def_of_pos hXpos]
      congr 1
      rw [hudef]
      ring
    have hfin2 : Real.exp ((1 - c₀) * u) ≤ Real.exp ((c₀ * u) ^ (21 / 20 : ℝ)) :=
      Real.exp_le_exp.mpr hkey
    have hsmall : 2 * Real.pi * X ^ (1 - c₀) / 8000 ≤ X ^ (1 - c₀) := by
      have h1 : 2 * Real.pi / 8000 ≤ 1 := by
        rw [div_le_one (by norm_num : (0:ℝ) < 8000)]
        linarith [Real.pi_lt_four]
      have h2 : 2 * Real.pi * X ^ (1 - c₀) / 8000 = (2 * Real.pi / 8000) * X ^ (1 - c₀) := by ring
      rw [h2]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hXpos.le _) h1
    rw [hudef] at hfin hfin2
    linarith [hsmall, hfin.le, hfin2, Real.rpow_nonneg hXpos.le (1 - c₀)]
  obtain ⟨Y₁, hY₁⟩ := hth1
  obtain ⟨Y₂, hY₂⟩ := hth2
  refine ⟨Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1,
    max (Real.exp (1 / c₀) + 3) (max Y₁ Y₂), by positivity, ?_⟩
  intro X L P A₁ A₂ hXle hPge hPle hLge hLle hgeom hsep1 hsep2
  have hX3 : 3 ≤ X := by
    have h := le_trans (le_max_left (Real.exp (1 / c₀) + 3) (max Y₁ Y₂)) hXle
    have he := Real.exp_pos (1 / c₀)
    linarith
  have hXexp : Real.exp (1 / c₀) ≤ X := by
    have h := le_trans (le_max_left (Real.exp (1 / c₀) + 3) (max Y₁ Y₂)) hXle
    linarith
  have hXY1 : Y₁ ≤ X :=
    le_trans (le_max_left Y₁ Y₂) (le_trans (le_max_right (Real.exp (1 / c₀) + 3) (max Y₁ Y₂)) hXle)
  have hXY2 : Y₂ ≤ X :=
    le_trans (le_max_right Y₁ Y₂) (le_trans (le_max_right (Real.exp (1 / c₀) + 3) (max Y₁ Y₂)) hXle)
  have hX1 : 1 < X := by linarith
  have hXpos : 0 < X := by linarith
  have hXnn : 0 ≤ X := hXpos.le
  have hlogX : 1 / c₀ ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXexp
  have hXc₀pos : 0 < X ^ c₀ := Real.rpow_pos_of_pos hXpos c₀
  have hLpos : 0 < L := lt_of_lt_of_le hXc₀pos hLge
  have hPpos : 0 < P := lt_of_lt_of_le hXc₀pos hPge
  have hP1 : 1 < P := by
    have h1 : 1 < X ^ c₀ := Real.one_lt_rpow hX1 hc₀
    linarith
  have hlogPpos : 0 < Real.log P := Real.log_pos hP1
  have hlogPge : c₀ * Real.log X ≤ Real.log P := by
    have h1 : Real.log (X ^ c₀) ≤ Real.log P := Real.log_le_log hXc₀pos hPge
    rwa [Real.log_rpow hXpos c₀] at h1
  have hlogP1 : 1 ≤ Real.log P := by
    have h1 : c₀ * (1 / c₀) ≤ c₀ * Real.log X := mul_le_mul_of_nonneg_left hlogX hc₀.le
    have h2 : c₀ * (1 / c₀) = 1 := by field_simp
    linarith
  have hPTle : PT ≤ P := by
    have h1 := hY₁ X hXY1
    have h2 : PT ≤ max PT 0 + 1 := le_trans (le_max_left PT 0) (by linarith)
    linarith
  -- parameters
  set c : ℝ := X / (8000 * L) with hcdef
  set δ : ℝ := L / (20 * X) with hδdef
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hcδ : c * δ = 1 / 160000 := by
    rw [hcdef, hδdef]; field_simp; ring
  have hcc : X / (8000 * L) = c := hcdef.symm
  -- the quadruple set and the weight
  let Q : Finset ((ℝ × ℝ) × (ℕ × ℕ)) := (A₁ ×ˢ A₂) ×ˢ (primesIn P (2 * P) ×ˢ primesIn P (2 * P))
  let wt : ((ℝ × ℝ) × (ℕ × ℕ)) → ℝ := fun v =>
    fejer (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))
  change (((Q.filter (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ)) ≤
    (Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1) *
      ((A₁.card : ℝ) * A₂.card * (L / X) * pi0 P ^ 2 +
        Real.sqrt ((A₁.card : ℝ) * A₂.card) * pi0 P ^ 2 / Real.log P)
  -- frequency separation
  have hsep1' : ∀ x ∈ A₁, ∀ y ∈ A₁, x ≠ y → δ ≤ |Real.log x - Real.log y| := by
    intro x hx y hy hxy
    rw [hδdef]
    have h1 := hgeom x (Finset.mem_union_left _ hx)
    have h2 := hgeom y (Finset.mem_union_left _ hy)
    exact log_freq_sep hXpos hLpos h1.1 h1.2 h2.1 h2.2 (hsep1 x hx y hy hxy)
  have hsep2' : ∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ y → δ ≤ |Real.log x - Real.log y| := by
    intro x hx y hy hxy
    rw [hδdef]
    have h1 := hgeom x (Finset.mem_union_right _ hx)
    have h2 := hgeom y (Finset.mem_union_right _ hy)
    exact log_freq_sep hXpos hLpos h1.1 h1.2 h2.1 h2.2 (hsep2 x hx y hy hxy)
  -- mean value bounds
  have hsieve1 : ∫ η in (-c)..c, ‖Smix A₁ η‖ ^ 2 ≤ KS * (A₁.card : ℝ) * (c + 1 / δ) := by
    have h := hSbound A₁ Real.log c δ hcpos hδpos hsep1'
    simpa [Smix] using h
  have hsieve2 : ∫ η in (-c)..c, ‖Smix A₂ η‖ ^ 2 ≤ KS * (A₂.card : ℝ) * (c + 1 / δ) := by
    have h := hSbound A₂ Real.log c δ hcpos hδpos hsep2'
    simpa [Smix] using h
  -- prime sum bound
  have hTbd : ∀ η : ℝ, |η| ≤ c →
      ‖Tmix P η‖ ≤ KT * pi0 P * (1 / (1 + |η|) + 1 / Real.log P) := by
    intro η hη
    refine hTbound P η hPTle hlogP1 (le_trans hη ?_)
    have hXL : X ^ (1 - c₀) * X ^ c₀ = X := by
      rw [← Real.rpow_add hXpos]
      simp
    have hstep1 : c ≤ X ^ (1 - c₀) / 8000 := by
      rw [hcdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hXL, Real.rpow_pos_of_pos hXpos (1 - c₀), hLge, hXpos.le]
    have hstep2 : X ^ (1 - c₀) / 8000 ≤
        Real.exp ((c₀ * Real.log X) ^ (21 / 20 : ℝ)) / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have h := hY₂ X hXY2
      linarith
    have hlogXnn : 0 ≤ Real.log X := by
      have hc₀inv : 0 < 1 / c₀ := one_div_pos.mpr hc₀
      linarith
    have hstep3 : Real.exp ((c₀ * Real.log X) ^ (21 / 20 : ℝ)) / (2 * Real.pi) ≤
        Real.exp ((Real.log P) ^ (21 / 20 : ℝ)) / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt (by linarith [Real.pi_pos] : (0:ℝ) < 2 * Real.pi))
      apply Real.exp_le_exp.mpr
      exact Real.rpow_le_rpow (mul_nonneg hc₀.le hlogXnn) hlogPge (by norm_num)
    linarith
  -- counting step
  have hcount : ((Q.filter (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ)
      ≤ (Real.pi ^ 2 / 4) * ∑ v ∈ Q, wt v := by
    have h1 : ((Q.filter (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ)
        = ∑ v ∈ Q, (if |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L then (1:ℝ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [h1]
    calc ∑ v ∈ Q, (if |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L then (1:ℝ) else 0)
        ≤ ∑ v ∈ Q, (Real.pi ^ 2 / 4) * wt v := by
          apply Finset.sum_le_sum
          intro v hv
          simp only [Q, Finset.mem_product] at hv
          obtain ⟨⟨hv1, hv2⟩, hvp1, hvp2⟩ := hv
          rcases lt_or_ge 0 (v.2.1 : ℝ) with hp1 | hp1
          · by_cases hcase : |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L
            · rw [if_pos hcase]
              have hw : 4 / Real.pi ^ 2 ≤ wt v := by
                simp only [wt]
                have hg := mem_primesIn (by positivity : (0:ℝ) ≤ 2 * P) hvp1
                have hg2 := mem_primesIn (by positivity : (0:ℝ) ≤ 2 * P) hvp2
                have h1 := hgeom v.1.1 (Finset.mem_union_left _ hv1)
                have h2 := hgeom v.1.2 (Finset.mem_union_right _ hv2)
                have hp2pos : (0:ℝ) < v.2.2 := by
                  have := hg2.1.two_le
                  exact_mod_cast (by omega : 0 < v.2.2)
                exact hfejer _ (abs_scaled_log_le hXpos hLpos hPpos hp1 hp2pos h1.1 h1.2 h2.1 h2.2
                  hg.2.1 hg.2.2 hg2.2.1 hg2.2.2 hcase)
              have hpi : (0:ℝ) < Real.pi ^ 2 / 4 := by positivity
              have hpid : (Real.pi ^ 2 / 4) * (4 / Real.pi ^ 2) = 1 := by
                field_simp <;> ring
              nlinarith [mul_le_mul_of_nonneg_left hw hpi.le, hpid]
            · rw [if_neg hcase]
              have := fejer_nonneg (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))
              positivity
          · have hp1z : (v.2.1 : ℝ) = 0 := le_antisymm hp1 (Nat.cast_nonneg _)
            have hp1p : v.2.1 = 0 := by exact_mod_cast hp1z
            have := (mem_primesIn (by positivity : (0:ℝ) ≤ 2 * P) hvp1).1
            rw [hp1p] at this
            exact absurd this (by norm_num)
      _ = (Real.pi ^ 2 / 4) * ∑ v ∈ Q, wt v := by rw [Finset.mul_sum]
  -- Fejér kernel as an integral
  have hfejer_c : ∀ u : ℝ, ((fejer u : ℝ) : ℂ)
      = ∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) * eC (x * u)) := by
    intro u
    have h1 : ((Real.sinc (Real.pi * u) ^ 2 : ℝ) : ℂ) = ((Real.sinc (Real.pi * u) : ℂ)) ^ 2 :=
      Complex.ofReal_pow _ 2
    rw [fejer, h1]
    exact (hpair u).symm
  -- the additive character identities
  have heC_add : ∀ a b : ℝ, eC (a + b) = eC a * eC b := by
    intro a b
    unfold eC
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heC_neg : ∀ a : ℝ, eC (-a) = (starRingEnd ℂ) (eC a) := by
    intro a
    unfold eC
    have h1 : (2 * (Real.pi : ℂ) * Complex.I * ((-a : ℝ) : ℂ))
        = (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * ((a : ℝ) : ℂ)) := by
      have h2 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * ((a : ℝ) : ℂ))
          = -(2 * (Real.pi : ℂ) * Complex.I * ((a : ℝ) : ℂ)) := by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
        ring
      rw [h2, Complex.ofReal_neg]
      ring
    rw [h1]
    exact Complex.exp_conj _
  -- expansion of the sum into the Fourier integral
  have hstep1 : ((∑ v ∈ Q, wt v : ℝ) : ℂ)
      = ∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) *
          ∑ v ∈ Q, eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2)))) := by
    rw [Complex.ofReal_sum]
    have h1 : (∑ v ∈ Q, ((wt v : ℝ) : ℂ))
        = ∑ v ∈ Q, (∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) *
            eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))))) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [wt]
      exact hfejer_c _
    rw [h1, ← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [Finset.mul_sum]
    · intro v _
      have hc1 : Continuous fun x : ℝ => (((1 - |x|) : ℝ) : ℂ) := by fun_prop
      have hc2 : Continuous fun x : ℝ =>
          eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))) := by
        unfold eC; fun_prop
      exact ii_of_continuous (by fun_prop : Continuous fun x : ℝ =>
        (((1 - |x|) : ℝ) : ℂ) * eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2)))) (-1) 1
  -- the summand factorizes
  have hA : ∀ x : ℝ, (∑ v ∈ Q, eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))))
      = ∑ x₁ ∈ A₁, ∑ x₂ ∈ A₂, ∑ p₁ ∈ primesIn P (2 * P), ∑ p₂ ∈ primesIn P (2 * P),
          eC ((c * x) * Real.log x₁) * (starRingEnd ℂ) (eC ((c * x) * Real.log x₂)) *
            eC ((c * x) * Real.log p₁) * (starRingEnd ℂ) (eC ((c * x) * Real.log p₂)) := by
    intro x
    simp only [Q, Finset.sum_product]
    apply Finset.sum_congr rfl; intro x₁ hx₁
    apply Finset.sum_congr rfl; intro x₂ hx₂
    apply Finset.sum_congr rfl; intro p₁ hp₁
    apply Finset.sum_congr rfl; intro p₂ hp₂
    rw [show x * (c * (Real.log x₁ + Real.log (p₁ : ℝ) - Real.log x₂ - Real.log (p₂ : ℝ)))
          = ((c * x) * Real.log x₁ + (-((c * x) * Real.log x₂))) +
            (((c * x) * Real.log (p₁ : ℝ)) + (-((c * x) * Real.log (p₂ : ℝ)))) by ring]
    rw [heC_add, heC_add, heC_add, heC_neg, heC_neg]
    ring
  have hB : ∀ x : ℝ, Smix A₁ (c * x) * (starRingEnd ℂ) (Smix A₂ (c * x)) *
        (Tmix P (c * x) * (starRingEnd ℂ) (Tmix P (c * x)))
      = ∑ x₁ ∈ A₁, ∑ x₂ ∈ A₂, ∑ p₁ ∈ primesIn P (2 * P), ∑ p₂ ∈ primesIn P (2 * P),
          eC ((c * x) * Real.log x₁) * (starRingEnd ℂ) (eC ((c * x) * Real.log x₂)) *
            eC ((c * x) * Real.log p₁) * (starRingEnd ℂ) (eC ((c * x) * Real.log p₂)) := by
    intro x
    rw [show Smix A₁ (c * x) = ∑ x₁ ∈ A₁, eC ((c * x) * Real.log x₁) from rfl]
    rw [show (starRingEnd ℂ) (Smix A₂ (c * x))
          = ∑ x₂ ∈ A₂, (starRingEnd ℂ) (eC ((c * x) * Real.log x₂)) by rw [Smix, map_sum]]
    rw [show (starRingEnd ℂ) (Tmix P (c * x))
          = ∑ p₂ ∈ primesIn P (2 * P), (starRingEnd ℂ) (eC ((c * x) * Real.log p₂)) by rw [Tmix, map_sum]]
    rw [show Tmix P (c * x) = ∑ p₁ ∈ primesIn P (2 * P), eC ((c * x) * Real.log p₁) from rfl]
    exact sum4_prod A₁ A₂ (primesIn P (2 * P)) (primesIn P (2 * P))
      (fun x₁ => eC ((c * x) * Real.log x₁))
      (fun x₂ => (starRingEnd ℂ) (eC ((c * x) * Real.log x₂)))
      (fun p₁ => eC ((c * x) * Real.log p₁))
      (fun p₂ => (starRingEnd ℂ) (eC ((c * x) * Real.log p₂)))
  have hfactor : ∀ x : ℝ, (∑ v ∈ Q, eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2))))
      = Smix A₁ (c * x) * (starRingEnd ℂ) (Smix A₂ (c * x)) *
        (Tmix P (c * x) * (starRingEnd ℂ) (Tmix P (c * x))) := by
    intro x
    rw [hA x, ← hB x]
  -- change of variables x ↦ η = c x
  have hstep2 : (∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) *
        ∑ v ∈ Q, eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2)))))
      = (c⁻¹ : ℂ) * ∫ η in (-c)..c, (((1 - |η| / c : ℝ) : ℂ) *
          (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η)))) := by
    have hweight : ∀ x : ℝ, (1 - |x| : ℝ) = 1 - |c * x| / c := by
      intro x
      rw [abs_mul, abs_of_pos hcpos]
      field_simp
    have h1 : (∫ x in (-1)..1, (((1 - |x| : ℝ) : ℂ) *
          ∑ v ∈ Q, eC (x * (c * (Real.log v.1.1 + Real.log v.2.1 - Real.log v.1.2 - Real.log v.2.2)))))
        = ∫ x in (-1)..1, (((1 - |c * x| / c : ℝ) : ℂ) *
            (Smix A₁ (c * x) * (starRingEnd ℂ) (Smix A₂ (c * x)) *
              (Tmix P (c * x) * (starRingEnd ℂ) (Tmix P (c * x))))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only []
      rw [hweight x, hfactor x]
    rw [h1]
    rw [intervalIntegral.integral_comp_mul_left
      (f := fun η : ℝ => (((1 - |η| / c : ℝ) : ℂ) * (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) *
        (Tmix P η * (starRingEnd ℂ) (Tmix P η))))) hcpos.ne']
    rw [show c * (-1) = -c by ring, show c * 1 = c by ring, Algebra.smul_def]
    rw [show (algebraMap ℝ ℂ) c⁻¹ = (((c⁻¹ : ℝ)) : ℂ) from rfl, Complex.ofReal_inv]
  -- the sum is bounded by the integral
  have hmain : ∑ v ∈ Q, wt v ≤ c⁻¹ * ∫ η in (-c)..c, (1 - |η| / c) *
      ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖ := by
    have h1 : ((∑ v ∈ Q, wt v : ℝ) : ℂ)
        = (c⁻¹ : ℂ) * ∫ η in (-c)..c, (((1 - |η| / c : ℝ) : ℂ) *
            (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η)))) := by
      rw [hstep1, hstep2]
    have hsum_nn : 0 ≤ ∑ v ∈ Q, wt v := Finset.sum_nonneg (fun v _ => fejer_nonneg _)
    have h2 : ‖∫ η in (-c)..c, (((1 - |η| / c : ℝ) : ℂ) *
          (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))))‖
        ≤ ∫ η in (-c)..c, (1 - |η| / c) *
          ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : -c ≤ c)).trans ?_
      apply intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
      · exact ii_of_continuous (by fun_prop : Continuous fun η : ℝ =>
          ‖(((1 - |η| / c : ℝ)) : ℂ) * (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) *
            (Tmix P η * (starRingEnd ℂ) (Tmix P η)))‖) (-c) c
      · exact ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (1 - |η| / c) *
          ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖) (-c) c
      · intro η hη
        have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
        have hw0 : 0 ≤ 1 - |η| / c := by
          have h1 : |η| / c ≤ 1 := (div_le_one hcpos).mpr hmem
          linarith
        rw [norm_mul, norm_ofReal_C, abs_of_nonneg hw0]
    calc ∑ v ∈ Q, wt v = ‖((∑ v ∈ Q, wt v : ℝ) : ℂ)‖ := by
          rw [norm_ofReal_C, abs_of_nonneg hsum_nn]
      _ = ‖(c⁻¹ : ℂ) * ∫ η in (-c)..c, (((1 - |η| / c : ℝ) : ℂ) *
            (Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))))‖ := by
          rw [h1]
      _ ≤ c⁻¹ * ∫ η in (-c)..c, (1 - |η| / c) *
            ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖ := by
          rw [norm_mul, ← Complex.ofReal_inv, norm_ofReal_C, abs_of_pos (inv_pos.mpr hcpos)]
          exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hcpos.le)
  -- the pointwise bound for T on the interval
  have hTpt : ∀ η ∈ Set.Icc (-c) c, ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) *
        (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖ ≤
      2 * (KT * pi0 P) ^ 2 * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2) +
        2 * (KT * pi0 P) ^ 2 * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2) := by
    intro η hη
    have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
    have hT := hTbd η hmem
    have hT2 : ‖Tmix P η‖ ^ 2 ≤ 2 * (KT * pi0 P) ^ 2 * ((1 / (1 + |η|)) ^ 2 + (1 / Real.log P) ^ 2) := by
      have hK : 0 < KT * pi0 P := mul_pos hKTpos (div_pos hPpos hlogPpos)
      have h1 : ‖Tmix P η‖ ≤ KT * pi0 P * ((1 / (1 + |η|)) + (1 / Real.log P)) := hT
      have hnn1 : 0 ≤ 1 / (1 + |η|) := by positivity
      have hnn2 : 0 ≤ 1 / Real.log P := by positivity
      nlinarith [sq_nonneg (1 / (1 + |η|) - 1 / Real.log P), hK, norm_nonneg (Tmix P η)]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have hsq : ‖Tmix P η‖ * ‖Tmix P η‖ = ‖Tmix P η‖ ^ 2 := by ring
    rw [hsq]
    have hnn : 0 ≤ ‖Smix A₁ η‖ * ‖Smix A₂ η‖ := by positivity
    nlinarith [hT2, hnn]
  -- the integral bound
  have hw_cont : Continuous fun η : ℝ => (1 - |η| / c : ℝ) :=
    continuous_const.sub (continuous_abs.div_const c)
  have hInt1 : Continuous fun η : ℝ => (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2) :=
    hw_cont.mul (((continuous_Smix A₁).norm.mul (continuous_Smix A₂).norm).mul continuous_inv_one_add_abs_sq)
  have hInt2 : Continuous fun η : ℝ => (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2) :=
    hw_cont.mul (((continuous_Smix A₁).norm.mul (continuous_Smix A₂).norm).mul continuous_const)
  have hInt : ∫ η in (-c)..c, (1 - |η| / c) *
        ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖
      ≤ 2 * (KT * pi0 P) ^ 2 * (Real.pi * ((A₁.card : ℝ) * A₂.card) +
          (1 / (Real.log P) ^ 2) * (KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ))) := by
    have hsplit : ∫ η in (-c)..c, (1 - |η| / c) *
          ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖
        ≤ ∫ η in (-c)..c, (2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2))
          + 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2))) := by
      apply intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
      · exact ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (1 - |η| / c) *
          ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖) (-c) c
      · exact ii_of_continuous (by fun_prop : Continuous fun η : ℝ =>
          2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2))
          + 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2))) (-c) c
      · intro η hη
        have h0 : 0 ≤ 1 - |η| / c := by
          have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
          have h1 : |η| / c ≤ 1 := (div_le_one hcpos).mpr hmem
          linarith
        calc (1 - |η| / c) *
              ‖Smix A₁ η * (starRingEnd ℂ) (Smix A₂ η) * (Tmix P η * (starRingEnd ℂ) (Tmix P η))‖
            ≤ (1 - |η| / c) * (2 * (KT * pi0 P) ^ 2 * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2)
                + 2 * (KT * pi0 P) ^ 2 * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2)) :=
                mul_le_mul_of_nonneg_left (hTpt η hη) h0
          _ = 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2))
                + 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2)) := by
                ring
    have hint_a : IntervalIntegrable (fun η : ℝ =>
        2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2))) volume (-c) c := by
      apply ii_of_continuous
      fun_prop
    have hint_b : IntervalIntegrable (fun η : ℝ =>
        2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2))) volume (-c) c := by
      apply ii_of_continuous
      fun_prop
    rw [intervalIntegral.integral_add hint_a hint_b] at hsplit
    refine hsplit.trans ?_
    have hA : ∫ η in (-c)..c, 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2))
        ≤ 2 * (KT * pi0 P) ^ 2 * (Real.pi * ((A₁.card : ℝ) * A₂.card)) := by
      have h2 : ∫ η in (-c)..c, (1 / (1 + |η|)) ^ 2 ≤ Real.pi := by
        have h3 : ∫ η in (-c)..c, (1 / (1 + |η|)) ^ 2 ≤ ∫ η in (-c)..c, (1 + η ^ 2)⁻¹ := by
          apply intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
          · exact ii_of_continuous continuous_inv_one_add_abs_sq (-c) c
          · exact ii_of_continuous (Continuous.inv₀ (by fun_prop : Continuous fun η : ℝ => 1 + η ^ 2)
              (fun η => by nlinarith [sq_nonneg η])) (-c) c
          · intro η hη
            have h1 : 1 + η ^ 2 ≤ (1 + |η|) ^ 2 := by nlinarith [abs_nonneg η, sq_abs η]
            have h2 : (0:ℝ) < (1 + |η|) ^ 2 := by positivity
            have h4 : (0:ℝ) < 1 + η ^ 2 := by positivity
            have h5 : ((1 + |η|) ^ 2)⁻¹ ≤ (1 + η ^ 2)⁻¹ := (inv_le_inv₀ h2 h4).mpr h1
            rw [div_pow, one_pow]
            simpa only [one_div] using h5
        refine h3.trans ?_
        rw [integral_inv_one_add_sq]
        linarith [Real.arctan_lt_pi_div_two c, Real.neg_pi_div_two_lt_arctan (-c)]
      have h1 : ∫ η in (-c)..c, (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2)
          ≤ ∫ η in (-c)..c, ((A₁.card : ℝ) * A₂.card) * (1 / (1 + |η|)) ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
        · exact ii_of_continuous hInt1 (-c) c
        · exact ii_of_continuous (continuous_inv_one_add_abs_sq.const_mul _) (-c) c
        · intro η hη
          have hw' : 1 - |η| / c ≤ 1 := by
            have : 0 ≤ |η| / c := div_nonneg (abs_nonneg η) hcpos.le
            linarith
          have hr : (0:ℝ) ≤ (1 / (1 + |η|)) ^ 2 := sq_nonneg _
          have hs1 : ‖Smix A₁ η‖ ≤ (A₁.card : ℝ) := by
            rw [Smix]; refine (norm_sum_le _ _).trans ?_; simp [n7_norm_eC]
          have hs2 : ‖Smix A₂ η‖ ≤ (A₂.card : ℝ) := by
            rw [Smix]; refine (norm_sum_le _ _).trans ?_; simp [n7_norm_eC]
          have h1 : ‖Smix A₁ η‖ * ‖Smix A₂ η‖ ≤ (A₁.card : ℝ) * A₂.card :=
            mul_le_mul hs1 hs2 (norm_nonneg _) (Nat.cast_nonneg _)
          calc (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / (1 + |η|)) ^ 2)
              ≤ 1 * (((A₁.card : ℝ) * A₂.card) * (1 / (1 + |η|)) ^ 2) :=
                mul_le_mul hw' (mul_le_mul_of_nonneg_right h1 hr) (by positivity) (by norm_num)
            _ = ((A₁.card : ℝ) * A₂.card) * (1 / (1 + |η|)) ^ 2 := by ring
      rw [intervalIntegral.integral_const_mul]
      rw [show Real.pi * ((A₁.card : ℝ) * A₂.card) = ((A₁.card : ℝ) * A₂.card) * Real.pi by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact h1.trans (by
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left h2 (by positivity))
    have hB : ∫ η in (-c)..c, 2 * (KT * pi0 P) ^ 2 * ((1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2))
        ≤ 2 * (KT * pi0 P) ^ 2 * ((1 / (Real.log P) ^ 2) * (KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ))) := by
      have hCSbound : ∫ η in (-c)..c, (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖)
          ≤ KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ) := by
        have hCS := interval_integral_mul_le_sqrt (by linarith : -c ≤ c)
          (f := fun η : ℝ => Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖)
          (g := fun η : ℝ => Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖)
          (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) ^ 2) (-c) c)
          (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖) ^ 2) (-c) c)
          (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) * (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖)) (-c) c)
          (fun η hη => by positivity) (fun η hη => by positivity)
        have heq : ∫ η in (-c)..c, (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) * (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖)
            = ∫ η in (-c)..c, (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖) := by
          apply intervalIntegral.integral_congr
          intro η hη
          simp only []
          rw [Set.uIcc_of_le (by linarith : -c ≤ c)] at hη
          have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
          have hw0 : 0 ≤ 1 - |η| / c := by
            have : |η| / c ≤ 1 := (div_le_one hcpos).mpr hmem
            linarith
          rw [show Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖ * (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖)
              = (Real.sqrt (1 - |η| / c) * Real.sqrt (1 - |η| / c)) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖) by ring,
            show Real.sqrt (1 - |η| / c) * Real.sqrt (1 - |η| / c) = 1 - |η| / c by
              rw [← sq, Real.sq_sqrt hw0]]
          try ring
        rw [heq] at hCS
        have hf2 : ∫ η in (-c)..c, (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) ^ 2
            ≤ KS * (A₁.card : ℝ) * (c + 1 / δ) := by
          refine (intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
            (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) ^ 2) (-c) c)
            (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => ‖Smix A₁ η‖ ^ 2) (-c) c) ?_).trans hsieve1
          intro η hη
          have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
          have hw0 : 0 ≤ 1 - |η| / c := by
            have : |η| / c ≤ 1 := (div_le_one hcpos).mpr hmem
            linarith
          have hw1 : 1 - |η| / c ≤ 1 := by
            have : 0 ≤ |η| / c := div_nonneg (abs_nonneg η) hcpos.le
            linarith
          have hsq : (Real.sqrt (1 - |η| / c)) ^ 2 = 1 - |η| / c := Real.sq_sqrt hw0
          rw [mul_pow, hsq]
          nlinarith [sq_nonneg ‖Smix A₁ η‖, hw0, hw1]
        have hg2 : ∫ η in (-c)..c, (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖) ^ 2
            ≤ KS * (A₂.card : ℝ) * (c + 1 / δ) := by
          refine (intervalIntegral.integral_mono_on (by linarith : -c ≤ c)
            (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖) ^ 2) (-c) c)
            (ii_of_continuous (by fun_prop : Continuous fun η : ℝ => ‖Smix A₂ η‖ ^ 2) (-c) c) ?_).trans hsieve2
          intro η hη
          have hmem : |η| ≤ c := abs_le.mpr ⟨by linarith [hη.1], hη.2⟩
          have hw0 : 0 ≤ 1 - |η| / c := by
            have : |η| / c ≤ 1 := (div_le_one hcpos).mpr hmem
            linarith
          have hw1 : 1 - |η| / c ≤ 1 := by
            have : 0 ≤ |η| / c := div_nonneg (abs_nonneg η) hcpos.le
            linarith
          have hsq : (Real.sqrt (1 - |η| / c)) ^ 2 = 1 - |η| / c := Real.sq_sqrt hw0
          rw [mul_pow, hsq]
          nlinarith [sq_nonneg ‖Smix A₂ η‖, hw0, hw1]
        refine hCS.trans ?_
        calc Real.sqrt (∫ η in (-c)..c, (Real.sqrt (1 - |η| / c) * ‖Smix A₁ η‖) ^ 2)
              * Real.sqrt (∫ η in (-c)..c, (Real.sqrt (1 - |η| / c) * ‖Smix A₂ η‖) ^ 2)
            ≤ Real.sqrt (KS * (A₁.card : ℝ) * (c + 1 / δ)) * Real.sqrt (KS * (A₂.card : ℝ) * (c + 1 / δ)) := by
              apply mul_le_mul
              · exact Real.sqrt_le_sqrt hf2
              · exact Real.sqrt_le_sqrt hg2
              · exact Real.sqrt_nonneg _
              · exact Real.sqrt_nonneg _
          _ = KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ) := by
              have hK : 0 ≤ KS * (c + 1 / δ) := by positivity
              rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ KS * (A₁.card : ℝ) * (c + 1 / δ))]
              rw [show KS * (A₁.card : ℝ) * (c + 1 / δ) * (KS * (A₂.card : ℝ) * (c + 1 / δ))
                  = (KS * (c + 1 / δ)) ^ 2 * ((A₁.card : ℝ) * A₂.card) by ring]
              rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (KS * (c + 1 / δ)) ^ 2),
                Real.sqrt_sq hK]
              rw [Real.sqrt_mul (Nat.cast_nonneg (A₁.card))]
              ring
      have h1 : ∫ η in (-c)..c, (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖ * (1 / Real.log P) ^ 2)
          = (1 / (Real.log P) ^ 2) * ∫ η in (-c)..c, (1 - |η| / c) * (‖Smix A₁ η‖ * ‖Smix A₂ η‖) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro η _
        ring
      rw [intervalIntegral.integral_const_mul, h1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hCSbound (by positivity)
    calc _ ≤ 2 * (KT * pi0 P) ^ 2 * (Real.pi * ((A₁.card : ℝ) * A₂.card)) +
          2 * (KT * pi0 P) ^ 2 * ((1 / (Real.log P) ^ 2) * (KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ))) := add_le_add hA hB
      _ = 2 * (KT * pi0 P) ^ 2 * (Real.pi * ((A₁.card : ℝ) * A₂.card) +
          (1 / (Real.log P) ^ 2) * (KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ))) := by ring
  -- final assembly
  have hcount' : (((Q.filter (fun v => |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ))
      ≤ (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 * (Real.pi * ((A₁.card : ℝ) * A₂.card) +
          (1 / (Real.log P) ^ 2) * (KS * Real.sqrt ((A₁.card : ℝ) * A₂.card) * (c + 1 / δ))))) := by
    refine hcount.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hmain.trans (mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr hcpos.le))
  -- arithmetic
  have hc_inv : c⁻¹ = 8000 * L / X := by
    rw [hcdef, inv_div]
  have hcδ1 : c + 1 / δ = 160001 * c := by
    have h1 : (c * δ)⁻¹ = 160000 := by rw [hcδ]; norm_num
    have h2 : 1 / δ = c * (c * δ)⁻¹ := by
      rw [div_eq_iff (ne_of_gt hδpos), mul_assoc, mul_comm (c * δ)⁻¹ δ, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (mul_pos hcpos hδpos))]
    rw [h2, h1]
    ring
  set R₁ : ℝ := (A₁.card : ℝ) with hR1def
  set R₂ : ℝ := (A₂.card : ℝ) with hR2def
  have hR1 : 0 ≤ R₁ := Nat.cast_nonneg _
  have hR2 : 0 ≤ R₂ := Nat.cast_nonneg _
  have hlp : 1 ≤ Real.log P := hlogP1
  have hlp0 : 0 < Real.log P := hlogPpos
  have hpi0 : 0 ≤ pi0 P := div_nonneg hPpos.le hlogPpos.le
  have hratio : 0 ≤ L / X := div_nonneg hLpos.le hXpos.le
  have hpoly : (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 * (Real.pi * (R₁ * R₂) +
        (1 / (Real.log P) ^ 2) * (KS * Real.sqrt (R₁ * R₂) * (c + 1 / δ)))))
      = Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi) * (R₁ * R₂ * (L / X) * pi0 P ^ 2)
        + (Real.pi ^ 2 / 2) * 160001 * KT ^ 2 * KS *
            (Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / (Real.log P) ^ 2) := by
    rw [show (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 * (Real.pi * (R₁ * R₂) +
          (1 / (Real.log P) ^ 2) * (KS * Real.sqrt (R₁ * R₂) * (c + 1 / δ)))))
        = (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 * Real.pi * (R₁ * R₂)))
          + (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 *
              ((1 / (Real.log P) ^ 2) * (KS * Real.sqrt (R₁ * R₂) * (c + 1 / δ))))) by ring]
    congr 1
    · rw [hc_inv]; ring
    · rw [hc_inv, hcδ1]
      rw [hcdef]
      field_simp
      ring
  have hmain2 : (Real.pi ^ 2 / 4) * (c⁻¹ * (2 * (KT * pi0 P) ^ 2 * (Real.pi * (R₁ * R₂) +
        (1 / (Real.log P) ^ 2) * (KS * Real.sqrt (R₁ * R₂) * (c + 1 / δ)))))
      ≤ (Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1) *
        (R₁ * R₂ * (L / X) * pi0 P ^ 2 + Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P) := by
    rw [hpoly]
    have h1 : 0 ≤ R₁ * R₂ * (L / X) * pi0 P ^ 2 := by positivity
    have h2 : 0 ≤ Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / (Real.log P) ^ 2 := by positivity
    have h3 : 0 ≤ Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P := by positivity
    have hC : 0 ≤ Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1 := by positivity
    have hlp2 : 1 / (Real.log P) ^ 2 ≤ 1 / Real.log P := by
      rw [div_le_div_iff₀ (by positivity) hlp0]
      nlinarith
    have hnum : (Real.pi ^ 2 / 2) * 160001 * KT ^ 2 * KS
        ≤ Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1 := by
      nlinarith [Real.pi_pos, hKTpos, hKSpos, sq_nonneg KT]
    have hnum2 : Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi)
        ≤ Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1 := by
      nlinarith [Real.pi_pos, hKTpos, hKSpos, sq_nonneg KT]
    have hl : Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / (Real.log P) ^ 2
        ≤ Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P := by
      have h4 : 0 ≤ Real.sqrt (R₁ * R₂) * pi0 P ^ 2 := by positivity
      calc Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / (Real.log P) ^ 2
          = (Real.sqrt (R₁ * R₂) * pi0 P ^ 2) * (1 / (Real.log P) ^ 2) := by ring
        _ ≤ (Real.sqrt (R₁ * R₂) * pi0 P ^ 2) * (1 / Real.log P) :=
              mul_le_mul_of_nonneg_left hlp2 h4
        _ = Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P := by ring
    calc Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi) * (R₁ * R₂ * (L / X) * pi0 P ^ 2)
          + (Real.pi ^ 2 / 2) * 160001 * KT ^ 2 * KS *
              (Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / (Real.log P) ^ 2)
        ≤ (Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1) * (R₁ * R₂ * (L / X) * pi0 P ^ 2)
          + (Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1) *
              (Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hnum2 h1
          · exact mul_le_mul hnum hl h2 hC
      _ = (Real.pi ^ 2 * KT ^ 2 * (4000 * Real.pi + 80001 * KS) + 1) *
            (R₁ * R₂ * (L / X) * pi0 P ^ 2 + Real.sqrt (R₁ * R₂) * pi0 P ^ 2 / Real.log P) := by
          ring
  exact hcount'.trans hmain2


/-- **N7. Mixing count** (MRT §5 (5.1)). For `L`-separated point sets `A₁, A₂ ⊆ [X/10, 10X]`,
the number of `(x₁, x₂, p₁, p₂)` with primes `p_i ∈ [P, 2P]` and `|x₁ - (p₂/p₁) x₂| ≤ 100 L` is
`≪ |A₁||A₂| (L/X) π₀(P)² + (|A₁||A₂|)^{1/2} π₀(P)² / log P`. Proof: Fourier majorant in
`(X/L) log(x₁p₁/(x₂p₂))`, the log-point large sieve, and the prime sum bound of N10. -/
theorem mixing_count (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (X L P : ℝ) (A₁ A₂ : Finset ℝ), X₀ ≤ X → X ^ c₀ ≤ P →
      P ≤ X ^ (1 / 4 : ℝ) → X ^ c₀ ≤ L → L ≤ X →
      (∀ x ∈ A₁ ∪ A₂, X / 10 ≤ x ∧ x ≤ 10 * X) →
      (∀ x ∈ A₁, ∀ y ∈ A₁, x ≠ y → L ≤ |x - y|) → (∀ x ∈ A₂, ∀ y ∈ A₂, x ≠ y → L ≤ |x - y|) →
      ((((A₁ ×ˢ A₂) ×ˢ (primesIn P (2 * P) ×ˢ primesIn P (2 * P))).filter
          (fun v ↦ |v.1.1 - ((v.2.2 : ℝ) / v.2.1) * v.1.2| ≤ 100 * L)).card : ℝ)
        ≤ C * ((A₁.card : ℝ) * A₂.card * (L / X) * pi0 P ^ 2 +
            Real.sqrt ((A₁.card : ℝ) * A₂.card) * pi0 P ^ 2 / Real.log P) := by
  obtain ⟨hpair, hfejer⟩ := triangle_fourier_pair
  obtain ⟨K, hKpos, hK⟩ := mv_finset_bound
  -- the T-bound, in the `21/20` range used by the main argument, from the fleet's
  -- Vinogradov–Korobov chain (V6 `zeta_prime_sum_twist`), via `mixing_tbound`
  have hT21 : ∃ K' P₀ : ℝ, 0 < K' ∧ ∀ (P η : ℝ), P₀ ≤ P → 1 ≤ Real.log P →
      |η| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) / (2 * Real.pi) →
      ‖Tmix P η‖ ≤ K' * pi0 P * (1 / (1 + |η|) + 1 / Real.log P) := by
    -- Live wiring: N7's own re-proof of the V-chain — V1 `vk_exp_sum` + the fleet's V2
    -- `v7chi_VKGrowth` + the fleet's V3 `LFunction_zeroFree_VK` + `N7.logDeriv_LFunction_VK_of_growth_zf`
    -- (V4) + `N7.ztw_paramN7`, assembled in `Submission/Work/BMF/N7/mixing_v6.lean`.
    -- Alternative wiring (the fleet's V6 via `mixing_tbound`): `prime_exp_sum_bound_21_of
    -- twistedLambdaVK12_of_zeta_prime_sum_twist`.
    obtain ⟨K', P₀, hK'pos, hT⟩ := Work.BMF.N7.prime_exp_sum_bound_21_N7
    exact ⟨K', P₀, hK'pos, fun P η hP _ hη => by simpa only [Tmix] using hT P η hP hη⟩
  exact mixing_count_aux hpair hfejer ⟨K, hKpos, hK⟩ hT21 c₀ hc₀

end Work.BMF
