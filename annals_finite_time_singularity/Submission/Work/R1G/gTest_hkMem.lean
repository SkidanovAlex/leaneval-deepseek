/-
# `Work.R1G.gTest_hkMem` — the visible test perturbation lies in `ℋ²`

`gTest ε z θ = ε · z²e^{-z} · sin(2θ)` (`Submission/Work/R1G/GTest.lean`) is the visible
witness of the G-route's profile data, and it must belong to the weighted space `ℋ²`,
`Work.Spaces.HkMem p 2 (gTest ε)` (`Work/Spaces/Defs.lean`), whose two conjuncts say that

* for every `z ∈ I_z = [0,∞)` the angular slice `θ ↦ HkIntegrand p 2 (gTest ε) z θ` is
  integrable on `I_θ = [0,π/2]`, and
* `z ↦ ∫_θ HkIntegrand p 2 (gTest ε) z θ` is integrable on `I_z`.

`HkIntegrand` is a sum of squares of weighted derivatives: the *pure* family
`(D_z^i f · w/√sin(2θ)^η)²` (`0 ≤ i ≤ 2`) and the *mixed* family `(D_z^j D_θ^i f · W)²`
with `1 ≤ i`, `i + j ≤ 2`, where `w = (1+z)²/z²`, `W = Wt p = w·sin(2θ)^{-γ/2}`,
`η = 99/100` and `γ = 1 + p/10`.  For `f = gTest ε` every one of these weighted
derivatives is explicit (`Submission/Work/R1G/GTest.lean`):

* `D_z^i g = ε·gPhiDi(z)·sin(2θ)` for `i = 0,1,2`, where `gPhiDj = z^j·∂_z^j gPhi` are the
  `z`-weighted radial factors (so that the `z²` of `gPhi` cancels the `z²` of the weight `w`);
* `D_z^j D_θ^i g = ε·gPhiDj(z)·gPsiDi(θ)` for `(i,j) ∈ {(1,0),(1,1),(2,0)}`, with
  `gPsiD1 = sin(4θ)`, `gPsiD2 = 4 sin(2θ)cos(4θ)`.

The proof is a pointwise domination on the quadrant, in two steps:

1. **Scalar estimates** (`weighted_term_bounds`).  On `z ≥ 0`, `θ ∈ I_θ`,
   `|gPhiDj(z)·w(z)| ≤ 10^{2j+2}·e^{-z/2}` (the polynomial growth of the radial factor is
   beaten by the exponential decay: `z^n e^{-z} ≤ 2^n n! e^{-z/2}`, `pow_mul_exp_neg_le`),
   while the angular factors are uniformly bounded:
   `|sin(2θ)|/sin(2θ)^{η/2} = sin(2θ)^{1-η/2} ≤ 1`, `|sin(4θ)|·sin(2θ)^{-γ/2} ≤ 2` and
   `|gPsiD2(θ)|·sin(2θ)^{-γ/2} ≤ 4` (here `γ ≤ 2` is used, i.e. `p ≤ 1`).
2. **Domination of the integrand** (`HkIntegrand_gTest_le`).  Expanding the integrand into
   its six summands (`Work.R1G.HkIntegrand_gTest_expand`) and squaring the scalar estimates
   gives `HkIntegrand p 2 (gTest ε) z θ ≤ 6·10^8·ε²·e^{-z/2}` on the quadrant.

The domination is turned into `HkMem` by the general transfer lemma
`Work.R1G.HkMem_of_expBound`: an exponential decay bound on the `H^k`-integrand is exactly
what the two integrability conditions of `HkMem` need (`SmoothNbhd (gTest ε)` supplies the
a.e. strong measurability of the integrand).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.GTest
import Submission.Work.R1G.HkMem_of_expBound
import Submission.Work.R1G.HkIntegrand_gTest_expand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.R1G

/-! ## The exponential decay beats every polynomial factor -/

/-- `z^n·e^{-z} ≤ 2^n·n!·e^{-z/2}` for `z ≥ 0`: the elementary comparison behind every
radial estimate below. -/
private lemma pow_mul_exp_neg_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    z ^ n * Real.exp (-z) ≤ (2 ^ n * n.factorial : ℝ) * Real.exp (-(z / 2)) := by
  have h := Real.pow_div_factorial_le_exp (z / 2) (show 0 ≤ z / 2 by linarith) n
  have hnpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 : (z / 2) ^ n ≤ (n.factorial : ℝ) * Real.exp (z / 2) := by
    have h' := (div_le_iff₀ hnpos).mp h
    linarith [h']
  have h2 : z ^ n ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (z / 2) := by
    have hmul : (2 : ℝ) ^ n * (z / 2) ^ n = z ^ n := by
      rw [← mul_pow]; ring_nf
    calc z ^ n = (2 : ℝ) ^ n * (z / 2) ^ n := hmul.symm
      _ ≤ (2 : ℝ) ^ n * ((n.factorial : ℝ) * Real.exp (z / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (z / 2) := by ring
  have hexp : Real.exp (z / 2) * Real.exp (-z) = Real.exp (-(z / 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc z ^ n * Real.exp (-z)
      ≤ ((2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (z / 2)) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = ((2 : ℝ) ^ n * (n.factorial : ℝ)) * (Real.exp (z / 2) * Real.exp (-z)) := by ring
    _ = (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-(z / 2)) := by rw [hexp]

/-! ## The three radial estimates -/

/-- `|gPhi z · w z| ≤ 100·e^{-z/2}` on `z ≥ 0`: for `z > 0` the product is
`(1+z)²e^{-z} = e^{-z} + 2z e^{-z} + z²e^{-z} ≤ (1 + 4 + 8)e^{-z/2}`, and at `z = 0` it
vanishes because `w 0 = 0`. -/
private lemma gPhi_mul_w_le {z : ℝ} (hz : 0 ≤ z) :
    |gPhi z * Work.Spaces.w z| ≤ 100 * Real.exp (-(z / 2)) := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [h.symm]
    norm_num [gPhi, Work.Spaces.w]
  · have hEq : gPhi z * Work.Spaces.w z = (1 + z) ^ 2 * Real.exp (-z) := by
      unfold gPhi Work.Spaces.w
      field_simp
    rw [hEq, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
    have h0 : Real.exp (-z) ≤ Real.exp (-(z / 2)) := Real.exp_le_exp.mpr (by linarith)
    have h1 : z * Real.exp (-z) ≤ 2 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 1 hz
      norm_num at h'
      exact h'
    have h2 : z ^ 2 * Real.exp (-z) ≤ 8 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 2 hz
      norm_num at h'
      exact h'
    have hsplit : (1 + z) ^ 2 * Real.exp (-z)
        = Real.exp (-z) + 2 * (z * Real.exp (-z)) + z ^ 2 * Real.exp (-z) := by ring
    rw [hsplit]
    nlinarith [h0, h1, h2, Real.exp_nonneg (-(z / 2))]

/-- `|gPhiD1 z · w z| ≤ 1000·e^{-z/2}` on `z ≥ 0`: for `z > 0` the product is
`(2-z)(1+z)²e^{-z}`, whose absolute value is at most
`(2 + 5z + 4z² + z³)e^{-z} ≤ (2 + 10 + 32 + 48)e^{-z/2}`. -/
private lemma gPhiD1_mul_w_le {z : ℝ} (hz : 0 ≤ z) :
    |gPhiD1 z * Work.Spaces.w z| ≤ 1000 * Real.exp (-(z / 2)) := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [h.symm]
    norm_num [gPhiD1, Work.Spaces.w]
  · have hEq : gPhiD1 z * Work.Spaces.w z = (2 - z) * (1 + z) ^ 2 * Real.exp (-z) := by
      unfold gPhiD1 Work.Spaces.w
      field_simp
    have habs : |2 - z| ≤ 2 + z := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hC : (0 : ℝ) ≤ (1 + z) ^ 2 * Real.exp (-z) :=
      mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
    have h1 : |(2 - z) * (1 + z) ^ 2 * Real.exp (-z)|
        ≤ (2 + z) * (1 + z) ^ 2 * Real.exp (-z) := by
      calc |(2 - z) * (1 + z) ^ 2 * Real.exp (-z)|
          = |2 - z| * ((1 + z) ^ 2 * Real.exp (-z)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (1 + z)),
              abs_of_nonneg (Real.exp_nonneg _)]
            ring
        _ ≤ (2 + z) * ((1 + z) ^ 2 * Real.exp (-z)) := mul_le_mul_of_nonneg_right habs hC
        _ = (2 + z) * (1 + z) ^ 2 * Real.exp (-z) := by ring
    rw [hEq]
    refine le_trans h1 ?_
    have h0 : Real.exp (-z) ≤ Real.exp (-(z / 2)) := Real.exp_le_exp.mpr (by linarith)
    have h1' : z * Real.exp (-z) ≤ 2 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 1 hz
      norm_num at h'
      exact h'
    have h2' : z ^ 2 * Real.exp (-z) ≤ 8 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 2 hz
      norm_num at h'
      exact h'
    have h3 : z ^ 3 * Real.exp (-z) ≤ 48 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 3 hz
      norm_num at h'
      exact h'
    have hsplit : (2 + z) * (1 + z) ^ 2 * Real.exp (-z)
        = 2 * Real.exp (-z) + 5 * (z * Real.exp (-z)) + 4 * (z ^ 2 * Real.exp (-z))
          + 1 * (z ^ 3 * Real.exp (-z)) := by ring
    rw [hsplit]
    nlinarith [h0, h1', h2', h3, Real.exp_nonneg (-(z / 2))]

/-- `|gPhiD2 z · w z| ≤ 10000·e^{-z/2}` on `z ≥ 0`: for `z > 0` the product is
`(4-5z+z²)(1+z)²e^{-z}`, whose absolute value is at most
`(4 + 13z + 15z² + 7z³ + z⁴)e^{-z} ≤ (4 + 26 + 120 + 336 + 384)e^{-z/2}`. -/
private lemma gPhiD2_mul_w_le {z : ℝ} (hz : 0 ≤ z) :
    |gPhiD2 z * Work.Spaces.w z| ≤ 10000 * Real.exp (-(z / 2)) := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [h.symm]
    norm_num [gPhiD2, Work.Spaces.w]
  · have hEq : gPhiD2 z * Work.Spaces.w z
        = (4 - 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z) := by
      unfold gPhiD2 Work.Spaces.w
      field_simp
    have habs : |4 - 5 * z + z ^ 2| ≤ 4 + 5 * z + z ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg z]
    have hC : (0 : ℝ) ≤ (1 + z) ^ 2 * Real.exp (-z) :=
      mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
    have h1 : |(4 - 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z)|
        ≤ (4 + 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z) := by
      calc |(4 - 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z)|
          = |4 - 5 * z + z ^ 2| * ((1 + z) ^ 2 * Real.exp (-z)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (1 + z)),
              abs_of_nonneg (Real.exp_nonneg _)]
            ring
        _ ≤ (4 + 5 * z + z ^ 2) * ((1 + z) ^ 2 * Real.exp (-z)) :=
            mul_le_mul_of_nonneg_right habs hC
        _ = (4 + 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z) := by ring
    rw [hEq]
    refine le_trans h1 ?_
    have h0 : Real.exp (-z) ≤ Real.exp (-(z / 2)) := Real.exp_le_exp.mpr (by linarith)
    have h1' : z * Real.exp (-z) ≤ 2 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 1 hz
      norm_num at h'
      exact h'
    have h2' : z ^ 2 * Real.exp (-z) ≤ 8 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 2 hz
      norm_num at h'
      exact h'
    have h3 : z ^ 3 * Real.exp (-z) ≤ 48 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 3 hz
      norm_num at h'
      exact h'
    have h4 : z ^ 4 * Real.exp (-z) ≤ 384 * Real.exp (-(z / 2)) := by
      have h' := pow_mul_exp_neg_le 4 hz
      norm_num at h'
      exact h'
    have hsplit : (4 + 5 * z + z ^ 2) * (1 + z) ^ 2 * Real.exp (-z)
        = 4 * Real.exp (-z) + 13 * (z * Real.exp (-z)) + 15 * (z ^ 2 * Real.exp (-z))
          + 7 * (z ^ 3 * Real.exp (-z)) + 1 * (z ^ 4 * Real.exp (-z)) := by ring
    rw [hsplit]
    nlinarith [h0, h1', h2', h3, h4, Real.exp_nonneg (-(z / 2))]

/-! ## The bounded angular factors -/

private lemma sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h1 h2, Real.sin_le_one _⟩

private lemma gam_le_two {p : ℝ} (hp1 : p ≤ 1) : Work.Spaces.gam p ≤ 2 := by
  rw [Work.Spaces.gam]; linarith

/-- `|sin(2θ)/sin(2θ)^{η/2}| ≤ 1` on `I_θ`: the quotient is `sin(2θ)^{1-η/2}` with
`1 - η/2 ≥ 0` and `0 ≤ sin(2θ) ≤ 1`. -/
private lemma gPsi_div_sin_le {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hs0 _),
    show |gPsi θ| = Real.sin (2 * θ) by rw [gPsi, abs_of_nonneg hs0]]
  rcases eq_or_lt_of_le hs0 with h | h
  · have hs : Real.sin (2 * θ) = 0 := h.symm
    have hpow : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
    rw [hpow, hs]
    norm_num
  · have hkey : Real.sin (2 * θ) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta / 2) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hs0 (Work.Spaces.eta / 2)]
      have hthis := (Real.rpow_add h 1 (-(Work.Spaces.eta / 2))).symm
      rw [Real.rpow_one] at hthis
      simpa [sub_eq_add_neg] using hthis
    rw [hkey]
    exact Real.rpow_le_one hs0 hs1 (by norm_num [Work.Spaces.eta])

/-- `|sin(4θ)|·sin(2θ)^{-γ/2} ≤ 2` on `I_θ`: `|sin(4θ)| ≤ 2 sin(2θ)` and
`sin(2θ)·sin(2θ)^{-γ/2} = sin(2θ)^{1-γ/2} ≤ 1` because `γ ≤ 2` (`p ≤ 1`). -/
private lemma gPsiD1_mul_rpow_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |gPsiD1 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))| ≤ 2 := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hg : 0 ≤ 1 - Work.Spaces.gam p / 2 := by have := gam_le_two hp1; linarith
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hrn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) :=
    Real.rpow_nonneg hs0 _
  rw [abs_mul, abs_of_nonneg hrn]
  have hsin4 : |gPsiD1 θ| ≤ 2 * Real.sin (2 * θ) := by
    rw [gPsiD1_eq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hs0]
    nlinarith [hcos, hs0, abs_nonneg (Real.cos (2 * θ))]
  rcases eq_or_lt_of_le hs0 with h | h
  · have hs : Real.sin (2 * θ) = 0 := h.symm
    have hzero : gPsiD1 θ = 0 := by rw [gPsiD1_eq, hs, mul_zero, zero_mul]
    have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) = 0 := by
      rw [hs, Real.zero_rpow]
      have : Work.Spaces.gam p ≠ 0 := by rw [Work.Spaces.gam]; linarith
      simpa using this
    rw [hzero, hpow, abs_zero, zero_mul]
    norm_num
  · have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))
        = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam p / 2) := by
      have hthis := (Real.rpow_add h 1 (-(Work.Spaces.gam p / 2))).symm
      rw [Real.rpow_one] at hthis
      simpa [sub_eq_add_neg] using hthis
    calc |gPsiD1 θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))
        ≤ (2 * Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) :=
          mul_le_mul_of_nonneg_right hsin4 hrn
      _ = 2 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))) := by ring
      _ = 2 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam p / 2) := by rw [hkey]
      _ ≤ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Real.rpow_le_one hs0 hs1 hg
      _ = 2 := by norm_num

/-- `|gPsiD2 θ|·sin(2θ)^{-γ/2} ≤ 4` on `I_θ`: `|4 sin(2θ)cos(4θ)| ≤ 4 sin(2θ)` and
`sin(2θ)·sin(2θ)^{-γ/2} = sin(2θ)^{1-γ/2} ≤ 1` because `γ ≤ 2` (`p ≤ 1`). -/
private lemma gPsiD2_mul_rpow_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |gPsiD2 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))| ≤ 4 := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hg : 0 ≤ 1 - Work.Spaces.gam p / 2 := by have := gam_le_two hp1; linarith
  have hcos : |Real.cos (4 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hrn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) :=
    Real.rpow_nonneg hs0 _
  rw [abs_mul, abs_of_nonneg hrn]
  have hsin2 : |gPsiD2 θ| ≤ 4 * Real.sin (2 * θ) := by
    rw [gPsiD2, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hs0]
    nlinarith [hcos, hs0, abs_nonneg (Real.cos (4 * θ))]
  rcases eq_or_lt_of_le hs0 with h | h
  · have hs : Real.sin (2 * θ) = 0 := h.symm
    have hzero : gPsiD2 θ = 0 := by rw [gPsiD2, hs, mul_zero, zero_mul]
    have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) = 0 := by
      rw [hs, Real.zero_rpow]
      have : Work.Spaces.gam p ≠ 0 := by rw [Work.Spaces.gam]; linarith
      simpa using this
    rw [hzero, hpow, abs_zero, zero_mul]
    norm_num
  · have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))
        = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam p / 2) := by
      have hthis := (Real.rpow_add h 1 (-(Work.Spaces.gam p / 2))).symm
      rw [Real.rpow_one] at hthis
      simpa [sub_eq_add_neg] using hthis
    calc |gPsiD2 θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))
        ≤ (4 * Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2)) :=
          mul_le_mul_of_nonneg_right hsin2 hrn
      _ = 4 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))) := by ring
      _ = 4 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam p / 2) := by rw [hkey]
      _ ≤ 4 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Real.rpow_le_one hs0 hs1 hg
      _ = 4 := by norm_num

/-! ## The six weighted summands -/

/-- **The scalar content of the pointwise bound.**  Each of the six weighted derivatives
appearing in `HkIntegrand p 2 (gTest ε)` is dominated on the quadrant by a constant times
`e^{-z/2}`; the constants are `10^{2j+2}` times the angular bound `1, 2, 4`. -/
private lemma weighted_term_bounds {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (z θ : ℝ)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |gPhi z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ 100 * Real.exp (-(z / 2)) ∧
    |gPhiD1 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ 1000 * Real.exp (-(z / 2)) ∧
    |gPhiD2 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ 10000 * Real.exp (-(z / 2)) ∧
    |gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ| ≤ 200 * Real.exp (-(z / 2)) ∧
    |gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ| ≤ 2000 * Real.exp (-(z / 2)) ∧
    |gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ| ≤ 400 * Real.exp (-(z / 2)) := by
  have hE : (0 : ℝ) ≤ Real.exp (-(z / 2)) := Real.exp_nonneg _
  have hang0 := gPsi_div_sin_le hθ
  have hang1 := gPsiD1_mul_rpow_le hp hp1 hθ
  have hang2 := gPsiD2_mul_rpow_le hp hp1 hθ
  have hrad0 := gPhi_mul_w_le hz
  have hrad1 := gPhiD1_mul_w_le hz
  have hrad2 := gPhiD2_mul_w_le hz
  -- multiplying two absolute-value estimates
  have hmul : ∀ a b c d : ℝ, |a| ≤ b → |c| ≤ d → |a| * |c| ≤ b * d := by
    intro a b c d ha hc
    exact mul_le_mul ha hc (abs_nonneg c) (le_trans (abs_nonneg a) ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hid : gPhi z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (gPhi z * Work.Spaces.w z) * (gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      ring
    rw [hid, abs_mul]
    calc |gPhi z * Work.Spaces.w z| * |gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)|
        ≤ (100 * Real.exp (-(z / 2))) * 1 := hmul _ _ _ _ hrad0 hang0
      _ = 100 * Real.exp (-(z / 2)) := by ring
  · have hid : gPhiD1 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (gPhiD1 z * Work.Spaces.w z) * (gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      ring
    rw [hid, abs_mul]
    calc |gPhiD1 z * Work.Spaces.w z| * |gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)|
        ≤ (1000 * Real.exp (-(z / 2))) * 1 := hmul _ _ _ _ hrad1 hang0
      _ = 1000 * Real.exp (-(z / 2)) := by ring
  · have hid : gPhiD2 z * gPsi θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (gPhiD2 z * Work.Spaces.w z) * (gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      ring
    rw [hid, abs_mul]
    calc |gPhiD2 z * Work.Spaces.w z| * |gPsi θ / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)|
        ≤ (10000 * Real.exp (-(z / 2))) * 1 := hmul _ _ _ _ hrad2 hang0
      _ = 10000 * Real.exp (-(z / 2)) := by ring
  · have hid : gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ
        = (gPhi z * Work.Spaces.w z)
          * (gPsiD1 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))) := by
      unfold Work.Spaces.Wt Work.Spaces.wTheta
      ring
    rw [hid, abs_mul]
    calc |gPhi z * Work.Spaces.w z|
          * |gPsiD1 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))|
        ≤ (100 * Real.exp (-(z / 2))) * 2 := hmul _ _ _ _ hrad0 hang1
      _ = 200 * Real.exp (-(z / 2)) := by ring
  · have hid : gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ
        = (gPhiD1 z * Work.Spaces.w z)
          * (gPsiD1 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))) := by
      unfold Work.Spaces.Wt Work.Spaces.wTheta
      ring
    rw [hid, abs_mul]
    calc |gPhiD1 z * Work.Spaces.w z|
          * |gPsiD1 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))|
        ≤ (1000 * Real.exp (-(z / 2))) * 2 := hmul _ _ _ _ hrad1 hang1
      _ = 2000 * Real.exp (-(z / 2)) := by ring
  · have hid : gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ
        = (gPhi z * Work.Spaces.w z)
          * (gPsiD2 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))) := by
      unfold Work.Spaces.Wt Work.Spaces.wTheta
      ring
    rw [hid, abs_mul]
    calc |gPhi z * Work.Spaces.w z|
          * |gPsiD2 θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam p / 2))|
        ≤ (100 * Real.exp (-(z / 2))) * 4 := hmul _ _ _ _ hrad0 hang2
      _ = 400 * Real.exp (-(z / 2)) := by ring

/-! ## The pointwise bound on the `H²`-integrand, and the theorem -/

/-- If `|A| ≤ C` then `A² ≤ C²`. -/
private lemma sq_le_sq_of_abs_le {A C : ℝ} (h : |A| ≤ C) : A ^ 2 ≤ C ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg (le_trans (abs_nonneg A) h)]
  exact h

/-- If `|x| ≤ K·E` with `0 ≤ E ≤ 1` then `x² ≤ K²·E`: the shape of every one of the six
summands of the `H²`-integrand, whose square is bounded by `ε²·K²·E`. -/
private lemma sq_le_of_abs_le_mul {x K E : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (_hK : 0 ≤ K)
    (h : |x| ≤ K * E) : x ^ 2 ≤ K ^ 2 * E := by
  have hx : x ^ 2 ≤ (K * E) ^ 2 := sq_le_sq_of_abs_le h
  have hE : E ^ 2 ≤ E := by
    nlinarith [hE0, mul_nonneg hE0 (show (0 : ℝ) ≤ 1 - E by linarith)]
  calc x ^ 2 ≤ (K * E) ^ 2 := hx
    _ = K ^ 2 * E ^ 2 := by ring
    _ ≤ K ^ 2 * E := mul_le_mul_of_nonneg_left hE (sq_nonneg K)

/-- **The pointwise domination.**  On the quadrant the `H²`-integrand of `gTest ε` is
dominated by `10^9·ε²·e^{-z/2}`: it is the sum of six squares
(`HkIntegrand_gTest_expand`), each of which is at most `10^8·ε²·e^{-z/2}` by
`weighted_term_bounds`, and `6·10^8 ≤ 10^9`. -/
private lemma HkIntegrand_gTest_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ε z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand p 2 (gTest ε) z θ ≤ 10 ^ 9 * ε ^ 2 * Real.exp (-(z / 2)) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  obtain ⟨hZ1, hZ2, hZ3, hM1, hM2, hM3⟩ := weighted_term_bounds hp hp1 z θ hz0 hθ
  have hE0 : (0 : ℝ) ≤ Real.exp (-(z / 2)) := Real.exp_nonneg _
  have hE1 : Real.exp (-(z / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have ht1 : (ε * gPhi z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 100 by norm_num) hZ1
    have hr : (ε * gPhi z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ε ^ 2 * (gPhi z * gPsi θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  have ht2 : (ε * gPhiD1 z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 1000 by norm_num) hZ2
    have hr : (ε * gPhiD1 z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ε ^ 2 * (gPhiD1 z * gPsi θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  have ht3 : (ε * gPhiD2 z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 10000 by norm_num) hZ3
    have hr : (ε * gPhiD2 z * gPsi θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ε ^ 2 * (gPhiD2 z * gPsi θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  have ht4 : (ε * gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 200 by norm_num) hM1
    have hr : (ε * gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
        = ε ^ 2 * (gPhi z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  have ht5 : (ε * gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 2000 by norm_num) hM2
    have hr : (ε * gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2
        = ε ^ 2 * (gPhiD1 z * gPsiD1 θ * Work.Spaces.Wt p z θ) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  have ht6 : (ε * gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ) ^ 2
      ≤ 10 ^ 8 * ε ^ 2 * Real.exp (-(z / 2)) := by
    have h := sq_le_of_abs_le_mul hE0 hE1 (show (0 : ℝ) ≤ 400 by norm_num) hM3
    have hr : (ε * gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ) ^ 2
        = ε ^ 2 * (gPhi z * gPsiD2 θ * Work.Spaces.Wt p z θ) ^ 2 := by ring
    rw [hr]
    nlinarith [h, sq_nonneg ε, hE0]
  rw [HkIntegrand_gTest_expand p ε z θ, gTest_apply ε z θ]
  linarith [ht1, ht2, ht3, ht4, ht5, ht6, mul_nonneg (sq_nonneg ε) hE0]

/-- **`gTest ε` belongs to `ℋ²`.**  `SmoothNbhd (gTest ε)` (analyticity on a neighbourhood
of the quadrant) supplies the a.e. strong measurability of the integrand, and the pointwise
domination `HkIntegrand_gTest_le` by the integrable function `10^9·ε²·e^{-z/2}` supplies
both integrability conditions of `HkMem` (via `HkMem_of_expBound`). -/
theorem gTest_hkMem {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ε : ℝ) :
    Work.Spaces.HkMem p 2 (gTest ε) := by
  refine HkMem_of_expBound (f := gTest ε) (C := 10 ^ 9 * ε ^ 2) (gTest_smoothNbhd ε)
    (by positivity) ?_
  intro z hz θ hθ
  exact HkIntegrand_gTest_le hp hp1 ε z θ hz hθ

end Work.R1G
