/-
# ZeroFreeTables — HB95Arith

The **numerical core** of HB Lemma 9.5 (Heath-Brown, *Zero-free regions for
Dirichlet L-functions…*, PLMS 64 (1992) 265–338, p. 59) for the cases of character
order `h = 2, 3, 4`.

HB's §9 derives, for a pair `(χ₁, ρ₁)` with `χ₁` of order `h ∈ {2,3,4}` (`χ₁` or
`ρ₁` complex) and `λ₁ = λ(ρ₁)`, the inequality

  `0 ≤ 14379·P₃((a+λ₁)/a) − 24480·P₃(1) + N_h·(a+λ₁)·(φ/2 + ε)`,   (★)

with `P₃(X) = X + X² + (2/3)X³` (HB (4.12), `P3R` of `Engine.lean`), the Chebyshev
coefficients `14379, 24480, 14900, 6000, 1250` of `(3+10cos θ)²(9+10cos θ)²`
(HB (9.16)), `φ = 1/4` (so `φ/2 = 1/8`), the constants

  `h = 2`: `a = 3.4`,  `N₂ = 30480`,
  `h = 3`: `a = 2.6`,  `N₃ = 40630`,
  `h = 4`: `a = 2.3`,  `N₄ = 45380`,

and the side condition (HB (9.17)) `30480/(a+λ₁)³ ≥ 14900/a³`, i.e.
`λ₁ ≤ (30480/14900)^{1/3}·a − a` (`0.9157`, `0.7003`, `0.6195` for the three `a`).
HB takes `ε → 0+` (so `q₀` depends on `ε`) and concludes

  `λ₁ ≥ 0.518 (h=2)`,  `λ₁ ≥ 0.389 (h=3)`,  `λ₁ ≥ 0.348 (h=4)`.

This file proves the *numerical* step: (★) (with `ε ≤ 10⁻⁵`) already forces
`λ₁ ≥ 348/1000`.  The roots of (★) at `ε = 0` are

  `0.518683… (h=2)`,  `0.389034… (h=3)`,  `0.348384… (h=4)`

(numerically computed, matching HB's `0.518, 0.389, 0.348`), so all three cases do
give the constant `0.348` needed by `HBTheorem1_complex`; the `h = 4` case is the
binding one (margin `3.8·10⁻⁴` at `ε = 0`, `1.5·10⁻²` at `ε = 10⁻⁵`).

Provenance of the shape: HB writes the conclusion of the §9 derivation for
`h ∈ {2,3,4}` as (p. 59, after dropping `Re T_h(hγ₁)` with (9.17))

  `14379 P₃((a+λ₁)/a) − 24480 P₃(1) + N_h (a+λ₁)(1/8 + ε) ≥ 0`.

The reading is confirmed by the thresholds: with these `a, N_h` the root of (★) is
`0.5187, 0.3890, 0.3484`, i.e. exactly HB's stated `0.518, 0.389, 0.348`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.Defs

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- `P₃(X) = X + X² + (2/3)X³` is increasing on `ℝ` (the algebraic factorization
`P₃ y − P₃ x = (y−x)(1 + x + y + (2/3)(x²+xy+y²))` has a strictly positive second
factor, since `1 + s + (2/3)(x²+xy+y²) ≥ 1 + s + s²/3 = ((s+3/2)² + 3/4)/3` with
`s = x + y`). -/
theorem P3R_mono : Monotone P3R := by
  intro x y hxy
  have hfac : 0 ≤ 1 + (x + y) + (2 / 3) * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y + 3 / 2)]
  have hid : P3R y - P3R x = (y - x) * (1 + (x + y) + (2 / 3) * (x ^ 2 + x * y + y ^ 2)) := by
    simp only [P3R]; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hfac]

/-- **The numerical step of HB Lemma 9.5.**  If the §9 inequality (★) holds with
parameter `a > 0`, coefficient `N > 0` and `0 ≤ ε ≤ 10⁻⁵`, then `λ₁ ≥ 348/1000`,
*provided* the same expression is negative at `λ₁ = 348/1000` and `ε = 10⁻⁵` (the
per-case certificate, verified in the three instances below). -/
theorem lam_ge_348_of_engine {a N lam₁ ε : ℝ} (ha : 0 < a) (hN : 0 < N)
    (hcert : 14379 * P3R ((a + 348 / 1000) / a) - 24480 * P3R 1
      + N * (a + 348 / 1000) * (1 / 8 + 1 / 100000) < 0)
    (hlam : lam₁ ≤ 348 / 1000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P3R ((a + lam₁) / a) - 24480 * P3R 1
      + N * (a + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  by_contra hcon
  push_neg at hcon
  have h1 : 14379 * P3R ((a + lam₁) / a) ≤ 14379 * P3R ((a + 348 / 1000) / a) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine P3R_mono ?_
    exact div_le_div_of_nonneg_right (by linarith) ha.le
  have h2 : N * (a + lam₁) * (1 / 8 + ε) ≤ N * (a + 348 / 1000) * (1 / 8 + 1 / 100000) := by
    rcases le_or_gt 0 (a + lam₁) with hp | hn
    · have hle : a + lam₁ ≤ a + 348 / 1000 := by linarith
      have he : (1 / 8 : ℝ) + ε ≤ 1 / 8 + 1 / 100000 := by linarith
      have h8 : 0 ≤ (1 / 8 : ℝ) + ε := by linarith
      calc N * (a + lam₁) * (1 / 8 + ε)
          ≤ N * (a + 348 / 1000) * (1 / 8 + ε) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hN.le) h8
        _ ≤ N * (a + 348 / 1000) * (1 / 8 + 1 / 100000) :=
            mul_le_mul_of_nonneg_left he (by positivity)
    · have hneg : N * (a + lam₁) * (1 / 8 + ε) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hN hn) (by linarith)
      have hpos : 0 < N * (a + 348 / 1000) * (1 / 8 + 1 / 100000) := by positivity
      linarith
  linarith

/-- HB Lemma 9.5, `h = 2` (`a = 3.4`, `N₂ = 30480`): (★) forces `λ₁ ≥ 348/1000`. -/
theorem h2_arith {lam₁ ε : ℝ} (hlam : lam₁ ≤ 348 / 1000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P3R ((34 / 10 + lam₁) / (34 / 10)) - 24480 * P3R 1
      + 30480 * (34 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  refine lam_ge_348_of_engine (a := 34 / 10) (N := 30480) (by norm_num) (by norm_num) ?_
    hlam hε0 hε h
  norm_num [P3R]

/-- HB Lemma 9.5, `h = 3` (`a = 2.6`, `N₃ = 40630`): (★) forces `λ₁ ≥ 348/1000`. -/
theorem h3_arith {lam₁ ε : ℝ} (hlam : lam₁ ≤ 348 / 1000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P3R ((26 / 10 + lam₁) / (26 / 10)) - 24480 * P3R 1
      + 40630 * (26 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  refine lam_ge_348_of_engine (a := 26 / 10) (N := 40630) (by norm_num) (by norm_num) ?_
    hlam hε0 hε h
  norm_num [P3R]

/-- HB Lemma 9.5, `h = 4` (`a = 2.3`, `N₄ = 45380`) — the binding case, whose root
is `0.348384…`: (★) forces `λ₁ ≥ 348/1000`. -/
theorem h4_arith {lam₁ ε : ℝ} (hlam : lam₁ ≤ 348 / 1000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P3R ((23 / 10 + lam₁) / (23 / 10)) - 24480 * P3R 1
      + 45380 * (23 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  refine lam_ge_348_of_engine (a := 23 / 10) (N := 45380) (by norm_num) (by norm_num) ?_
    hlam hε0 hε h
  norm_num [P3R]

/-! ## The `P₃` comparison identity and HB's `T_h` terms

HB's §9 derivation of Lemma 9.5 for `h ∈ {2,3,4}` produces, besides the two main
`P₃` terms, the correction term `Re T_h(hγ₁)` (HB pp. 58–59, after (9.16)):

  `T₂(t) = −24480 P₃((a+λ₁)/(a+λ₁+it)) + 14900 P₃((a+λ₁)/(a+it))
             − 6000 P₃((a+λ₁)/(a+λ₁+it)) − 6000 P₃((a+λ₁)/(a+λ₁+2it)) + 1250 P₃((a+λ₁)/(a+2it))`,
  `T₃(t) = −14900 P₃((a+λ₁)/(a+λ₁+it)) + 6000 P₃((a+λ₁)/(a+it)) − 1250 P₃((a+λ₁)/(a+λ₁+it))`,
  `T₄(t) = −6000 P₃((a+λ₁)/(a+λ₁+it)) + 1250 P₃((a+λ₁)/(a+it))`,

and HB drops it: `Re T_h(t) ≤ 0` follows from `Re P₃(α/(α+it)) ≥ 0` together with the
side condition (9.17), `30480/(a+λ₁)³ ≥ 14900/a³`.

Both ingredients are proved here in public form.  The comparison `Φ(α,β,t) ≤ (α/β)³Φ(α,α,t)`
for `0 < β ≤ α` (`PhiG_le_self`) is `private` in `P9/rescale_variants.lean` (hence not
importable), so it is reproved here from its factorization
`Re P₃(a/(b+ic)) − (a/b)³ Re P₃(a/(a+ic)) = (b−a)·E/(b³(b²+c²)³(a²+c²)³)`, `E ≥ 0`.
-/

/-- The numerator of `Re P₃(a/(b+ic))·(b²+c²)³`. -/
private def Qp (a b c : ℝ) : ℝ :=
  (b - a) * c ^ 4 + 2 * b * (b ^ 2 - a ^ 2) * c ^ 2 + b ^ 3 * (b ^ 2 + a * b + (2 / 3) * a ^ 2)

/-- The non-negative factor of the comparison identity for `Re P₃`. -/
private def Ep (a b c : ℝ) : ℝ :=
  a*b^3*(c^2)^5 + 2*a*b^5*(c^2)^4 + a*b^7*(c^2)^3
  + 2*a^2*b^4*(c^2)^4 + 2*a^2*b^6*(c^2)^3
  + 3*a^3*b^3*(c^2)^4 + (26/3)*a^3*b^5*(c^2)^3 + 3*a^3*b^7*(c^2)^2
  + (26/3)*a^4*b^4*(c^2)^3 + 6*a^4*b^6*(c^2)^2
  + (17/3)*a^5*b^3*(c^2)^3 + 14*a^5*b^5*(c^2)^2 + 3*a^5*b^7*(c^2)
  + (8/3)*a^6*b^2*(c^2)^3 + 14*a^6*b^4*(c^2)^2 + 6*a^6*b^6*(c^2)
  + (8/3)*a^7*b*(c^2)^3 + 9*a^7*b^3*(c^2)^2 + 10*a^7*b^5*(c^2) + a^7*b^7
  + (8/3)*a^8*(c^2)^3 + 8*a^8*b^2*(c^2)^2 + 10*a^8*b^4*(c^2) + 2*a^8*b^6

private lemma Ep_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Ep a b c := by
  unfold Ep; positivity

/-- `Re P₃` at `w = x + iy`. -/
private lemma P3_re_p (w : ℂ) :
    (P3 w).re = w.re + (w.re ^ 2 - w.im ^ 2) + (2 / 3) * (w.re ^ 3 - 3 * w.re * w.im ^ 2) := by
  rcases w with ⟨a, b⟩
  simp only [P3, Complex.add_re, Complex.mul_re, Complex.mul_im, pow_succ]
  norm_num
  ring

private lemma re_div_p (a b c : ℝ) :
    (((a : ℂ) / ((b : ℂ) + (c : ℂ) * Complex.I)).re) = a * b / (b ^ 2 + c ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

private lemma im_div_p (a b c : ℝ) :
    (((a : ℂ) / ((b : ℂ) + (c : ℂ) * Complex.I)).im) = -(a * c) / (b ^ 2 + c ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

private lemma phiG_formula (a b c : ℝ) (hb : 0 < b) :
    P9.PhiG a b c = a * Qp a b c / (b ^ 2 + c ^ 2) ^ 3 := by
  have hD : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  simp only [P9.PhiG]
  rw [P3_re_p, re_div_p a b c, im_div_p a b c]
  unfold Qp
  field_simp
  ring

private lemma phiG_cmp (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P9.PhiG a b c - (a / b) ^ 3 * P9.PhiG a a c
      = (b - a) * Ep a b c / (b ^ 3 * (b ^ 2 + c ^ 2) ^ 3 * (a ^ 2 + c ^ 2) ^ 3) := by
  have hQaa : Qp a a c = (8 / 3) * a ^ 5 := by unfold Qp; ring
  rw [phiG_formula a b c hb, phiG_formula a a c ha, hQaa]
  field_simp
  unfold Qp Ep
  ring

/-- **The `P₃` comparison** (public form of HB's Lemma 8.3 tool):
`Φ(α,β,t) = Re P₃(α/(β+it)) ≤ (α/β)³ Φ(α,α,t)` for `0 < β ≤ α`. -/
theorem PhiG_le_self {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) :
    P9.PhiG a b c ≤ (a / b) ^ 3 * P9.PhiG a a c := by
  have hkey := phiG_cmp a b c ha hb
  have hE : 0 ≤ Ep a b c := Ep_nonneg a b c ha.le hb.le
  have hnum : (b - a) * Ep a b c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hE
  have hden : 0 ≤ b ^ 3 * (b ^ 2 + c ^ 2) ^ 3 * (a ^ 2 + c ^ 2) ^ 3 := by positivity
  have hle : P9.PhiG a b c - (a / b) ^ 3 * P9.PhiG a a c ≤ 0 := by
    rw [hkey]; exact div_nonpos_of_nonpos_of_nonneg hnum hden
  linarith

/-- HB's (9.17): `30480/(a+λ₁)³ ≥ 14900/a³`, in polynomial form. -/
def cond917 (a lam₁ : ℝ) : Prop := 14900 * (a + lam₁) ^ 3 ≤ 30480 * a ^ 3

/-- Rescaling the side condition: if `c (a+λ₁)³ ≤ d a³` and `0 < c ≤ c'`, `d' ≥ 0`
with `c' d ≤ c d'`, then `c' (a+λ₁)³ ≤ d' a³`. -/
private lemma scal_cond {a lam₁ c d c' d' : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d)
    (hc' : 0 < c') (hdd : 0 ≤ d') (hr : c' * d ≤ c * d')
    (h : c * (a + lam₁) ^ 3 ≤ d * a ^ 3) : c' * (a + lam₁) ^ 3 ≤ d' * a ^ 3 := by
  have h1 : (c' / c) * (c * (a + lam₁) ^ 3) ≤ (c' / c) * (d * a ^ 3) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e1 : (c' / c) * (c * (a + lam₁) ^ 3) = c' * (a + lam₁) ^ 3 := by field_simp
  have e2 : (c' / c) * (d * a ^ 3) = (c' * d / c) * a ^ 3 := by ring
  have e3 : c' * d / c ≤ d' := by
    rw [div_le_iff₀ hc]; linarith
  have ha3 : 0 ≤ a ^ 3 := by positivity
  calc c' * (a + lam₁) ^ 3 = (c' / c) * (c * (a + lam₁) ^ 3) := e1.symm
    _ ≤ (c' / c) * (d * a ^ 3) := h1
    _ = (c' * d / c) * a ^ 3 := e2
    _ ≤ d' * a ^ 3 := mul_le_mul_of_nonneg_right e3 ha3

/-- The side condition in the shape consumed by the `T_h` bounds: for coefficients
`cn, cp` with `0 ≤ cn, 0 ≤ cp` and `cp (a+λ₁)³ ≤ cn a³` the "shifted-zero" term
dominates the "far" term, `cp Φ(a+λ₁,a,t) ≤ cn Φ(a+λ₁,a+λ₁,t)`. -/
theorem PhiG_pair_le {a lam₁ cn cp t : ℝ} (ha : 0 < a) (hl : 0 ≤ lam₁)
    (hcn : 0 ≤ cn) (hcp : 0 ≤ cp) (h17 : cp * (a + lam₁) ^ 3 ≤ cn * a ^ 3) :
    cp * P9.PhiG (a + lam₁) a t ≤ cn * P9.PhiG (a + lam₁) (a + lam₁) t := by
  have hlt : 0 < a + lam₁ := by linarith
  have hcmp : P9.PhiG (a + lam₁) a t
      ≤ ((a + lam₁) / a) ^ 3 * P9.PhiG (a + lam₁) (a + lam₁) t :=
    PhiG_le_self hlt ha (by linarith)
  have h1 : cp * P9.PhiG (a + lam₁) a t
      ≤ cp * (((a + lam₁) / a) ^ 3 * P9.PhiG (a + lam₁) (a + lam₁) t) :=
    mul_le_mul_of_nonneg_left hcmp hcp
  have h2 : cp * (((a + lam₁) / a) ^ 3 * P9.PhiG (a + lam₁) (a + lam₁) t)
      ≤ cn * P9.PhiG (a + lam₁) (a + lam₁) t := by
    have hnn : 0 ≤ P9.PhiG (a + lam₁) (a + lam₁) t := P9.PhiG_nonneg hlt le_rfl
    have hratio : cp * ((a + lam₁) / a) ^ 3 ≤ cn := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < a ^ 3)]
      linarith
    calc cp * (((a + lam₁) / a) ^ 3 * P9.PhiG (a + lam₁) (a + lam₁) t)
        = (cp * ((a + lam₁) / a) ^ 3) * P9.PhiG (a + lam₁) (a + lam₁) t := by ring
      _ ≤ cn * P9.PhiG (a + lam₁) (a + lam₁) t := mul_le_mul_of_nonneg_right hratio hnn
  linarith

/-- `Φ(a,b,0) = P₃(a/b)` on the real axis. -/
theorem PhiG_zero_right {a b : ℝ} (hb : 0 < b) : P9.PhiG a b 0 = P3R (a / b) := by
  rw [phiG_formula a b 0 hb]
  unfold Qp P3R
  field_simp
  ring

theorem PhiG_one_one : P9.PhiG 1 1 0 = P3R 1 := by
  rw [PhiG_zero_right (by norm_num : (0:ℝ) < 1)]; norm_num

/-- `T₂` of HB p. 59 (with the shifts `t` and `2t`), as a real number. -/
def T2re (a lam₁ t : ℝ) : ℝ :=
  -24480 * P9.PhiG (a + lam₁) (a + lam₁) t + 14900 * P9.PhiG (a + lam₁) a t
  - 6000 * P9.PhiG (a + lam₁) (a + lam₁) t
  - 6000 * P9.PhiG (a + lam₁) (a + lam₁) (2 * t) + 1250 * P9.PhiG (a + lam₁) a (2 * t)

/-- `T₃` of HB p. 59. -/
def T3re (a lam₁ t : ℝ) : ℝ :=
  -14900 * P9.PhiG (a + lam₁) (a + lam₁) t + 6000 * P9.PhiG (a + lam₁) a t
  - 1250 * P9.PhiG (a + lam₁) (a + lam₁) t

/-- `T₄` of HB p. 59. -/
def T4re (a lam₁ t : ℝ) : ℝ :=
  -6000 * P9.PhiG (a + lam₁) (a + lam₁) t + 1250 * P9.PhiG (a + lam₁) a t

/-- **HB p. 59, `h = 2`: `Re T₂ ≤ 0` under (9.17).** -/
theorem T2re_nonpos {a lam₁ t : ℝ} (ha : 0 < a) (hl : 0 ≤ lam₁) (h17 : cond917 a lam₁) :
    T2re a lam₁ t ≤ 0 := by
  have hA : 14900 * P9.PhiG (a + lam₁) a t
      ≤ 30480 * P9.PhiG (a + lam₁) (a + lam₁) t :=
    PhiG_pair_le ha hl (by norm_num) (by norm_num)
      (by have h := h17; unfold cond917 at h; linarith [h])
  have hB : 1250 * (a + lam₁) ^ 3 ≤ 6000 * a ^ 3 :=
    scal_cond (a := a) (lam₁ := lam₁) (c := 14900) (d := 30480) (c' := 1250) (d' := 6000)
      ha.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h17
  have hB' : 1250 * P9.PhiG (a + lam₁) a (2 * t)
      ≤ 6000 * P9.PhiG (a + lam₁) (a + lam₁) (2 * t) :=
    PhiG_pair_le ha hl (by norm_num) (by norm_num) hB
  have h0 : 0 ≤ P9.PhiG (a + lam₁) (a + lam₁) (2 * t) :=
    P9.PhiG_nonneg (by linarith : (0:ℝ) < a + lam₁) le_rfl
  unfold T2re
  linarith

/-- **HB p. 59, `h = 3`: `Re T₃ ≤ 0` under (9.17).** -/
theorem T3re_nonpos {a lam₁ t : ℝ} (ha : 0 < a) (hl : 0 ≤ lam₁) (h17 : cond917 a lam₁) :
    T3re a lam₁ t ≤ 0 := by
  have h6000 : 6000 * (a + lam₁) ^ 3 ≤ 16150 * a ^ 3 :=
    scal_cond (a := a) (lam₁ := lam₁) (c := 14900) (d := 30480) (c' := 6000) (d' := 16150)
      ha.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h17
  have hA : 6000 * P9.PhiG (a + lam₁) a t
      ≤ 16150 * P9.PhiG (a + lam₁) (a + lam₁) t :=
    PhiG_pair_le ha hl (by norm_num) (by norm_num) h6000
  unfold T3re
  linarith

/-- **HB p. 59, `h = 4`: `Re T₄ ≤ 0` under (9.17).** -/
theorem T4re_nonpos {a lam₁ t : ℝ} (ha : 0 < a) (hl : 0 ≤ lam₁) (h17 : cond917 a lam₁) :
    T4re a lam₁ t ≤ 0 := by
  have h1250 : 1250 * (a + lam₁) ^ 3 ≤ 6000 * a ^ 3 :=
    scal_cond (a := a) (lam₁ := lam₁) (c := 14900) (d := 30480) (c' := 1250) (d' := 6000)
      ha.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h17
  have hA : 1250 * P9.PhiG (a + lam₁) a t
      ≤ 6000 * P9.PhiG (a + lam₁) (a + lam₁) t :=
    PhiG_pair_le ha hl (by norm_num) (by norm_num) h1250
  unfold T4re
  linarith

/-! ## End-to-end reductions: (9.16) including `T_h` already gives `λ₁ ≥ 348/1000` -/

/-- **`h = 2` reduction**: the §9 inequality with its `T₂` term (and (9.17)) forces
`λ₁ ≥ 348/1000`. -/
theorem h2_reduce {lam₁ ε t : ℝ} (hl : 0 ≤ lam₁) (h17 : cond917 (34 / 10) lam₁)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P9.PhiG (34 / 10 + lam₁) (34 / 10) 0 - 24480 * P9.PhiG 1 1 0
      + T2re (34 / 10) lam₁ t + 30480 * (34 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  have hT := T2re_nonpos (a := 34 / 10) (t := t) (by norm_num) hl h17
  rw [PhiG_zero_right (a := 34 / 10 + lam₁) (b := 34 / 10) (by norm_num), PhiG_one_one] at h
  by_contra hc
  push_neg at hc
  have := h2_arith (lam₁ := lam₁) (ε := ε) hc.le hε0 hε (by linarith)
  linarith

/-- **`h = 3` reduction.** -/
theorem h3_reduce {lam₁ ε t : ℝ} (hl : 0 ≤ lam₁) (h17 : cond917 (26 / 10) lam₁)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P9.PhiG (26 / 10 + lam₁) (26 / 10) 0 - 24480 * P9.PhiG 1 1 0
      + T3re (26 / 10) lam₁ t + 40630 * (26 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  have hT := T3re_nonpos (a := 26 / 10) (t := t) (by norm_num) hl h17
  rw [PhiG_zero_right (a := 26 / 10 + lam₁) (b := 26 / 10) (by norm_num), PhiG_one_one] at h
  by_contra hc
  push_neg at hc
  have := h3_arith (lam₁ := lam₁) (ε := ε) hc.le hε0 hε (by linarith)
  linarith

/-- **`h = 4` reduction** (the binding case, root `0.348384…`). -/
theorem h4_reduce {lam₁ ε t : ℝ} (hl : 0 ≤ lam₁) (h17 : cond917 (23 / 10) lam₁)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (h : 0 ≤ 14379 * P9.PhiG (23 / 10 + lam₁) (23 / 10) 0 - 24480 * P9.PhiG 1 1 0
      + T4re (23 / 10) lam₁ t + 45380 * (23 / 10 + lam₁) * (1 / 8 + ε)) :
    348 / 1000 ≤ lam₁ := by
  have hT := T4re_nonpos (a := 23 / 10) (t := t) (by norm_num) hl h17
  rw [PhiG_zero_right (a := 23 / 10 + lam₁) (b := 23 / 10) (by norm_num), PhiG_one_one] at h
  by_contra hc
  push_neg at hc
  have := h4_arith (lam₁ := lam₁) (ε := ε) hc.le hε0 hε (by linarith)
  linarith

end Work.ZeroFreeTables
