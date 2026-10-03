/-
# Area 4 (round 6): the crude (triangle-inequality) bound for the §15 closing estimate

This module proves `Work.FIArea4.A6CrudeProp` — the *concentrated-support* branch of the closing
estimate of *FI* §15 in the round-6 vocabulary:

if `0 ≤ ψ ≤ 1`, `supp β ⊆ S`, `‖β‖ ≤ Bmax` and every pair `(z₁,z₂) ∈ S × S` has at most `Dmax`
admissible moduli `d` (the moduli with `4d ∣ |Δ(z₁,z₂)|`, `1 ≤ d ≤ |Δ|/4 + 1` and `X < d`), then

  `‖Tcut (radN Pa) (ψ-cut) β‖ ≤ C·Bmax²·#S²·Dmax·(log(4N)+1)`.

No polar-box hypothesis is needed: the whole `(z₁,z₂)`-sum of `Tcut` lives in the box
`gBox (radN Pa)` of radius `⌈√(4N)⌉`, and for `z` in that box `|z|² ≤ 18N`
(`a6_mem_boxN_gnorm_le`), so `logFac6 z₁ z₂ = log(8|z₁z₂|/|Δ|)` is bounded by `40(log(4N)+1)`
(`a6_logFac6_abs_le`): it is `≥ log 8 > 0` because `|Δ| ≤ |z₁z₂|`, and `≤ log(144N)` because
`|Δ| ≥ 1` off the vanishing case.

The proof is then the triangle inequality: the cut is supported on the `X < d` part of `Sset`,
`φ(d)/d ≤ 1`, `|ψ| ≤ 1` and `|(z₂/z₁|d)| ≤ 1`, so each pair contributes at most
`Dmax·40(log(4N)+1)` and the ordered-pair sum at most `2·Bmax²·#S²·Dmax·40(log(4N)+1)`.
-/
import Mathlib
import Submission.Work.FIArea4.A6Defs

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary Gaussian, box and logarithm bounds -/

lemma a6_gnorm_cast (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
  have h2 : z.norm = z.re * z.re + z.im * z.im := by
    rw [Zsqrtd.norm_def]; ring
  have h3z : (0 : ℤ) ≤ z.re * z.re + z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hcast : ((|z.re * z.re + z.im * z.im| : ℤ) : ℝ)
      = (z.re : ℝ) * z.re + (z.im : ℝ) * z.im := by
    rw [abs_of_nonneg h3z]; push_cast; ring
  show ((z.norm.natAbs : ℕ) : ℝ) = _
  rw [h2, Nat.cast_natAbs, hcast]
  ring

lemma a6_gnorm_eq_normSq (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = Complex.normSq (z : ℂ) := by
  rw [Work.FIPlan.gnorm, Nat.cast_natAbs,
    abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg z), GaussianInt.intCast_real_norm]

lemma a6_norm_toComplex_eq_sqrt (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [a6_gnorm_eq_normSq z, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma a6_gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma a6_delta_toComplex_im (z1 z2 : GaussianInt) :
    ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) = (star (z1 : ℂ) * (z2 : ℂ)).im := by
  have h : ((star z1 * z2 : GaussianInt) : ℂ) = star (z1 : ℂ) * (z2 : ℂ) := by
    rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star]; simp
  rw [Work.FIPlan.Delta, GaussianInt.intCast_im, h]

lemma a6_absDelta_le_sqrt_gnorm (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
  have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := h1
    _ = |(star (z1 : ℂ) * (z2 : ℂ)).im| := by rw [a6_delta_toComplex_im]
    _ ≤ ‖star (z1 : ℂ) * (z2 : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [a6_norm_toComplex_eq_sqrt, a6_norm_toComplex_eq_sqrt]
    _ = Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
        rw [a6_gnorm_mul, Nat.cast_mul]

lemma a6_sqrt_gnorm_mul_le (N : ℝ) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 18 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 18 * N) :
    Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 18 * N := by
  have h2N : 0 ≤ 18 * N := le_trans (Nat.cast_nonneg _) hg1
  have h1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (18 * N) :=
    Real.sqrt_le_sqrt hg1
  have h2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (18 * N) :=
    Real.sqrt_le_sqrt hg2
  calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [a6_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ Real.sqrt (18 * N) * Real.sqrt (18 * N) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 18 * N := by
        rw [← Real.sqrt_mul h2N, show 18 * N * (18 * N) = (18 * N) ^ 2 by ring, Real.sqrt_sq h2N]

/-- A member of the inner box `boxN Pa = gBox ⌈√(4N)⌉` has `|z|² ≤ 18N`. -/
lemma a6_mem_boxN_gnorm_le (Pa : Work.FITop.Params) {z : GaussianInt}
    (hz : z ∈ Work.FITop.boxN Pa) : (Work.FIPlan.gnorm z : ℝ) ≤ 18 * Pa.N := by
  obtain ⟨hre, him⟩ := mem_gBox_coords (R := Work.FITop.radN Pa) hz
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have h4N : (0 : ℝ) ≤ 4 * Pa.N := by linarith
  have hceil : ((Work.FITop.radN Pa : ℤ) : ℝ) ≤ Real.sqrt (4 * Pa.N) + 1 := by
    have h := Nat.ceil_lt_add_one (a := Real.sqrt (4 * Pa.N)) (by positivity)
    have hcast : ((Work.FITop.radN Pa : ℤ) : ℝ)
        = ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := by
      unfold Work.FITop.radN; push_cast; ring
    rw [hcast]; linarith
  have hre1 : (z.re : ℝ) ≤ Real.sqrt (4 * Pa.N) + 1 := by
    have h1 : ((z.re : ℤ) : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      exact_mod_cast (le_trans (le_abs_self z.re) hre)
    linarith
  have hre2 : -(Real.sqrt (4 * Pa.N) + 1) ≤ (z.re : ℝ) := by
    have h1 : ((-z.re : ℤ) : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      exact_mod_cast (le_trans (neg_le_abs z.re) hre)
    push_cast at h1; linarith
  have him1 : (z.im : ℝ) ≤ Real.sqrt (4 * Pa.N) + 1 := by
    have h1 : ((z.im : ℤ) : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      exact_mod_cast (le_trans (le_abs_self z.im) him)
    linarith
  have him2 : -(Real.sqrt (4 * Pa.N) + 1) ≤ (z.im : ℝ) := by
    have h1 : ((-z.im : ℤ) : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by
      exact_mod_cast (le_trans (neg_le_abs z.im) him)
    push_cast at h1; linarith
  have hre3 : (z.re : ℝ) ^ 2 ≤ (Real.sqrt (4 * Pa.N) + 1) ^ 2 := sq_le_sq' hre2 hre1
  have him3 : (z.im : ℝ) ^ 2 ≤ (Real.sqrt (4 * Pa.N) + 1) ^ 2 := sq_le_sq' him2 him1
  have hsN : Real.sqrt Pa.N ≤ Pa.N := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]
  have hsq : (Real.sqrt (4 * Pa.N)) ^ 2 = 4 * Pa.N := Real.sq_sqrt h4N
  rw [a6_gnorm_cast z]
  nlinarith [hre3, him3, hsN, hs, hsq, hN1]

/-- The two-sided bound for the round-6 logarithm `logFac6 z₁ z₂ = log(8|z₁z₂|/|Δ|)`: for
`|z_i|² ≤ 18N` with `N ≥ 1` it is at most `40(log(4N)+1)` in absolute value. -/
lemma a6_log_expr_abs_le (N : ℝ) (hN : 1 ≤ N) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 18 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 18 * N) :
    |Real.log (8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))| ≤ 40 * (Real.log (4 * N) + 1) := by
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · have hz : Real.log (8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) = 0 := by
      rw [h0]; simp
    rw [hz, abs_zero]
    have : (0 : ℝ) ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    linarith
  · have hΔ1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hΔpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hsq := a6_sqrt_gnorm_mul_le N z1 z2 hg1 hg2
    have hge : 1 ≤ 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hΔpos]
      linarith [a6_absDelta_le_sqrt_gnorm z1 z2]
    have hargpos : 0 < 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hle : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 144 * N := by
      rw [div_le_iff₀ hΔpos]
      nlinarith [hsq, hΔ1]
    rw [abs_of_nonneg (Real.log_nonneg hge)]
    have hmono := Real.log_le_log hargpos hle
    have h144 : Real.log (144 * N) = Real.log 36 + Real.log (4 * N) := by
      rw [show (144 : ℝ) * N = 36 * (4 * N) by ring,
        Real.log_mul (by norm_num) (by linarith)]
    have hlog36 : Real.log 36 ≤ 35 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 36 by norm_num)
      linarith
    have hlog4N : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
    rw [h144] at hmono
    linarith

/-- `logFac6` is bounded by `40(log(4N)+1)` for a pair in the inner box. -/
lemma a6_logFac6_abs_le (N : ℝ) (hN : 1 ≤ N) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 18 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 18 * N) :
    |Work.FITop4.logFac6 z1 z2| ≤ 40 * (Real.log (4 * N) + 1) := by
  simpa only [Work.FITop4.logFac6] using a6_log_expr_abs_le N hN z1 z2 hg1 hg2

/-- The ratio symbol `(z₂/z₁|d)` is a Jacobi symbol, hence `≤ 1` in absolute value. -/
lemma a6_ratioSym_abs_le (z1 z2 : GaussianInt) (d : ℕ) :
    |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
  unfold Work.FITop4.ratioSym Work.FIArea7.ratioSym
  rcases jacobiSym.trichotomy _ d with h | h | h <;> rw [h] <;> norm_num

/-! ## The inner `d`-sum and the `(z₁,z₂)`-summand of `Tcut` -/

/-- The inner `d`-sum of the `(z₁,z₂)`-term of `Tcut (ψ-cut)`, as a real number:
`Σ_{d ∈ Sset z₁z₂} (φ(d)/d)·ψ-cut(d)·(z₂/z₁|d)·logFac6`. -/
def a6Dsum (ψ : ℝ → ℝ) (X j : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ d ∈ Work.FITop4.Sset z1 z2,
    ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2

/-- The `(z₁,z₂)`-summand of `Tcut (ψ-cut)`: the coprimality cut times `β z₁ β̄ z₂` times the
inner `d`-sum. -/
def a6Inner (ψ : ℝ → ℝ) (X j : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime z1 z2 then
    (β z1 * star (β z2)) * ((a6Dsum ψ X j z1 z2 : ℝ) : ℂ) else 0

/-- The same summand with the coprimality cut dropped (it is `≤` the cut one in norm). -/
def a6U (ψ : ℝ → ℝ) (X j : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℂ :=
  (β z1 * star (β z2)) * ((a6Dsum ψ X j z1 z2 : ℝ) : ℂ)

lemma a6_tcut_eq (Rz : ℤ) (ψ : ℝ → ℝ) (X j : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz (A6cut ψ X j) β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          a6Inner ψ X j β z1 z2 := by
  rw [Tcut_eq_sum_ofReal]
  congr 1

/-- **The trivial estimate for the inner `d`-sum of a single pair.**  The cut is supported on the
`X < d` part of `Sset`, `φ(d)/d ≤ 1`, `|ψ| ≤ 1`, `|(z₂/z₁|d)| ≤ 1`, and `|logFac6| ≤ 40(log(4N)+1)`
for `z₁, z₂` in the inner box, so at most `Dmax` admissible moduli give
`|a6Dsum| ≤ Dmax·40(log(4N)+1)`. -/
lemma a6Dsum_abs_le (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ)
    (hψ0 : ∀ y : ℝ, 0 ≤ ψ y) (hψ1 : ∀ y : ℝ, ψ y ≤ 1)
    {z1 z2 : GaussianInt} (hz1 : z1 ∈ Work.FITop.boxN Pa) (hz2 : z2 ∈ Work.FITop.boxN Pa)
    {Dmax : ℝ}
    (hcard : (((Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ X < d)).card : ℝ) ≤ Dmax) :
    |a6Dsum ψ X j z1 z2| ≤ Dmax * (40 * (Real.log (4 * Pa.N) + 1)) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hlog : |Work.FITop4.logFac6 z1 z2| ≤ 40 * (Real.log (4 * Pa.N) + 1) :=
    a6_logFac6_abs_le Pa.N hN1 z1 z2 (a6_mem_boxN_gnorm_le Pa hz1)
      (a6_mem_boxN_gnorm_le Pa hz2)
  have hLnn : 0 ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
    have : 0 ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith)
    linarith
  set A : Finset ℕ := (Work.FITop4.Sset z1 z2).filter (fun d => X < d) with hAdef
  have hAcard : (A.card : ℝ) ≤ Dmax := by
    rw [hAdef, Work.FITop4.Sset, Finset.filter_filter]
    exact hcard
  have hDmax : 0 ≤ Dmax := le_trans (Nat.cast_nonneg _) hAcard
  have hterm : ∀ d ∈ A, |((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
        * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
      ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
    intro d hd
    have hdS : d ∈ Work.FITop4.Sset z1 z2 := (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdS).1).1
    have hcard1 : |(Nat.totient d : ℝ) / (d : ℝ)| ≤ 1 := by
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
        div_le_one hdpos]
      exact_mod_cast Nat.totient_le d
    have hcut : |A6cut ψ X j z1 z2 d| ≤ 1 := by
      unfold A6cut
      split_ifs with h
      · rw [abs_of_nonneg (hψ0 _)]; exact hψ1 _
      · norm_num
    have hrs : |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := a6_ratioSym_abs_le z1 z2 d
    rw [abs_mul, abs_mul, abs_mul]
    have h1 : |(Nat.totient d : ℝ) / (d : ℝ)| * |A6cut ψ X j z1 z2 d| ≤ 1 * 1 :=
      mul_le_mul hcard1 hcut (abs_nonneg _) (by norm_num)
    have h2 : |(Nat.totient d : ℝ) / (d : ℝ)| * |A6cut ψ X j z1 z2 d|
        * |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 * 1 * 1 :=
      mul_le_mul h1 hrs (abs_nonneg _) (by norm_num)
    have h3 : |(Nat.totient d : ℝ) / (d : ℝ)| * |A6cut ψ X j z1 z2 d|
        * |(Work.FITop4.ratioSym z1 z2 d : ℝ)| * |Work.FITop4.logFac6 z1 z2|
        ≤ 1 * |Work.FITop4.logFac6 z1 z2| := by
      have := mul_le_mul h2 (le_refl (|Work.FITop4.logFac6 z1 z2|)) (abs_nonneg _)
        (by norm_num)
      simpa using this
    linarith [h3, hlog]
  have hsum_eq : (∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2)
      = ∑ d ∈ A, ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro d hdS hdA
    have hX' : ¬ X < d := fun h => hdA (Finset.mem_filter.mpr ⟨hdS, h⟩)
    unfold A6cut
    rw [if_neg hX']
    ring
  unfold a6Dsum
  rw [hsum_eq]
  calc |∑ d ∈ A, ((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
        * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
      ≤ ∑ d ∈ A, |((Nat.totient d : ℝ) / (d : ℝ)) * A6cut ψ X j z1 z2 d
        * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ A, (40 * (Real.log (4 * Pa.N) + 1)) := Finset.sum_le_sum hterm
    _ = (A.card : ℝ) * (40 * (Real.log (4 * Pa.N) + 1)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Dmax * (40 * (Real.log (4 * Pa.N) + 1)) :=
        mul_le_mul_of_nonneg_right hAcard hLnn

/-! ## The crude bound -/

theorem A6Crude : Work.FIArea4.A6CrudeProp := by
  refine ⟨80, by norm_num, ?_⟩
  intro ψ hψ0 hψ1 Pa X j Bmax Dmax S β hX hsupp hB hD
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  by_cases hS : S = ∅
  · have hβ0 : ∀ z : GaussianInt, β z = 0 := by
      intro z
      by_contra hz
      have hmem := hsupp z hz
      rw [hS] at hmem
      simp at hmem
    have hTc : Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β = 0 := by
      rw [a6_tcut_eq]
      have hzero : ∀ z1 z2 : GaussianInt, a6Inner ψ X j β z1 z2 = 0 := by
        intro z1 z2
        rw [a6Inner, hβ0 z1]
        by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc]
      rw [Finset.sum_eq_zero (fun z1 _ => Finset.sum_eq_zero (fun z2 _ => hzero z1 z2)),
        mul_zero]
    rw [hTc, norm_zero, hS]
    simp
  · obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hDmax : 0 ≤ Dmax := le_trans (Nat.cast_nonneg _) (hD z0 hz0 z0 hz0)
    have hBmax : 0 ≤ Bmax := le_trans (norm_nonneg (β 0)) (hB 0)
    have hLnn : 0 ≤ 40 * (Real.log (4 * Pa.N) + 1) := by
      have : 0 ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith)
      linarith
    set T : Finset GaussianInt := (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
      (fun z => β z ≠ 0) with hT
    have hsubT : T ⊆ Work.FIPlan.gBox (Work.FITop.radN Pa) := fun z hz =>
      (Finset.mem_filter.mp hz).1
    have hTS : T ⊆ S := fun z hz => hsupp z (Finset.mem_filter.mp hz).2
    have hcardT : (T.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hTS
    have hzeroU : ∀ z1 z2 : GaussianInt, β z1 = 0 → ‖a6U ψ X j β z1 z2‖ = 0 := by
      intro z1 z2 h
      simp [a6U, h]
    have hzeroU2 : ∀ z1 z2 : GaussianInt, β z2 = 0 → ‖a6U ψ X j β z1 z2‖ = 0 := by
      intro z1 z2 h
      simp [a6U, h]
    have hpairU : ∀ z1 ∈ T, ∀ z2 ∈ T, ‖a6U ψ X j β z1 z2‖
        ≤ Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) := by
      intro z1 hz1 z2 hz2
      have hz1' := Finset.mem_filter.mp hz1
      have hz2' := Finset.mem_filter.mp hz2
      have hsum := a6Dsum_abs_le Pa X j ψ hψ0 hψ1 hz1'.1 hz2'.1
        (hD z1 (hTS hz1) z2 (hTS hz2))
      simp only [a6U, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      have hb : ‖β z1‖ * ‖β z2‖ ≤ Bmax * Bmax :=
        mul_le_mul (hB z1) (hB z2) (norm_nonneg _) hBmax
      calc ‖β z1‖ * ‖β z2‖ * |a6Dsum ψ X j z1 z2|
          ≤ (Bmax * Bmax) * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) :=
            mul_le_mul hb hsum (abs_nonneg _) (mul_nonneg hBmax hBmax)
        _ = Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) := by ring
    have hstep2 : ∀ z1 z2 : GaussianInt,
        ‖a6Inner ψ X j β z1 z2‖ ≤ ‖a6U ψ X j β z1 z2‖ := by
      intro z1 z2
      rw [a6Inner]
      by_cases hc : Work.FIPlan.GaussCoprime z1 z2
      · rw [if_pos hc, a6U]
      · rw [if_neg hc, norm_zero]; exact norm_nonneg _
    have hstep3 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6U ψ X j β z1 z2‖)
        = ∑ z1 ∈ T, ∑ z2 ∈ T, ‖a6U ψ X j β z1 z2‖ := by
      have hinner : ∀ z1 : GaussianInt,
          (∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6U ψ X j β z1 z2‖)
            = ∑ z2 ∈ T, ‖a6U ψ X j β z1 z2‖ := by
        intro z1
        refine (Finset.sum_subset hsubT ?_).symm
        intro z2 hz2 hz2T
        have hb : β z2 = 0 := by
          by_contra h
          exact hz2T (by rw [hT, Finset.mem_filter]; exact ⟨hz2, h⟩)
        exact hzeroU2 z1 z2 hb
      calc (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6U ψ X j β z1 z2‖)
          = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ∑ z2 ∈ T,
              ‖a6U ψ X j β z1 z2‖ :=
            Finset.sum_congr rfl (fun z1 _ => hinner z1)
        _ = ∑ z1 ∈ T, ∑ z2 ∈ T, ‖a6U ψ X j β z1 z2‖ := by
            refine (Finset.sum_subset hsubT ?_).symm
            intro z1 hz1 hz1T
            have hb : β z1 = 0 := by
              by_contra h
              exact hz1T (by rw [hT, Finset.mem_filter]; exact ⟨hz1, h⟩)
            exact Finset.sum_eq_zero (fun z2 _ => hzeroU z1 z2 hb)
    have hmain : ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), a6Inner ψ X j β z1 z2‖
        ≤ Bmax ^ 2 * (S.card : ℝ) ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) := by
      have h1 : ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), a6Inner ψ X j β z1 z2‖
          ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6Inner ψ X j β z1 z2‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _))
      have h2 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6Inner ψ X j β z1 z2‖)
          ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6U ψ X j β z1 z2‖ :=
        Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => hstep2 z1 z2))
      have h3 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖a6U ψ X j β z1 z2‖)
          ≤ Bmax ^ 2 * (S.card : ℝ) ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) := by
        rw [hstep3]
        refine (Finset.sum_le_sum
          (fun z1 hz1 => Finset.sum_le_sum (fun z2 hz2 => hpairU z1 hz1 z2 hz2))).trans ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hXnn : 0 ≤ Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) :=
          mul_nonneg (sq_nonneg _) (mul_nonneg hDmax hLnn)
        have hsq : (T.card : ℝ) * (T.card : ℝ) ≤ (S.card : ℝ) * (S.card : ℝ) :=
          mul_le_mul hcardT hcardT (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        calc (T.card : ℝ) * ((T.card : ℝ)
              * (Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1)))))
            = ((T.card : ℝ) * (T.card : ℝ))
                * (Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1)))) := by ring
          _ ≤ ((S.card : ℝ) * (S.card : ℝ))
                * (Bmax ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1)))) :=
              mul_le_mul_of_nonneg_right hsq hXnn
          _ = Bmax ^ 2 * (S.card : ℝ) ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1))) := by ring
      exact h1.trans (h2.trans h3)
    calc ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut ψ X j) β‖
        = 2 * ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), a6Inner ψ X j β z1 z2‖ := by
          rw [a6_tcut_eq, norm_mul, Complex.norm_ofNat]
      _ ≤ 2 * (Bmax ^ 2 * (S.card : ℝ) ^ 2 * (Dmax * (40 * (Real.log (4 * Pa.N) + 1)))) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = 80 * Bmax ^ 2 * (S.card : ℝ) ^ 2 * Dmax * (Real.log (4 * Pa.N) + 1) := by ring

end

end Work.FIArea4
