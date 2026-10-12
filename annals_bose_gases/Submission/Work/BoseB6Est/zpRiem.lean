import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB6Est.Regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the zero-point lattice comparison (`hzero`)

The zero-point sum of FS `thm:BogHamDiag` is a sum over the *discrete* mode lattice
`modePos n k`, while FS's `lem:BogIntegral` evaluates the *continuum* integral
`∫ (𝒜 − √(𝒜²−ℬ²))`.  This file provides the Riemann-type comparison between the
two at FS's own parameters, in the mild form needed by the chapter.

Write `φ(r) = τ̃(r) + β(r) − √((τ̃(r)+β(r))² − β(r)²)` for FS's scaled zero-point
bracket as a function of the radius (`phifun`), so that
`cleanBracket K εT c1 c2 t = φ(‖t‖)`.  The three pointwise facts that drive the
estimate are

* `phifun_le_B0` : `φ(r) ≤ 8π+1` for `r ≥ 0` (from `β ≤ 8π+ηT` on the support,
  `φ ≤ β`, and `φ = 0` off the support);
* `phifun_mul_le` : `r·φ(r) ≤ 268` for `r ≥ 2c₁` (from `τ̃(r) ≥ r²/8`, giving
  `φ = β²/(τ̃+β+w) ≤ β²/(β+w) ≤ 2β^{3/2}/r` with `w = √(τ̃²+2τ̃β) ≥ r√β/2` and
  `β(r) ≤ 8π+1`);
* `phifun_eq_zero_of_T_lt` : `φ(r) = 0` for `r > T` (the kernel's cutoff).

The proof of the main theorem `zpRiem` uses only the first of these facts: there are
exactly `(n+1)^6` modes and the mesh volume is `meshD n³ = (2π/(n+1))³`, so the whole
mode sum is at most

  `(2π/(n+1))³ · (n+1)^6 · (8π+1) ≤ 26.14·(2π)³·((n:ℝ)+1)³ ≤ 10⁴((n:ℝ)+1)³`,

which is exactly the last error term of the statement.  The sharper Riemann-type
machinery — the pointwise decay `phifun_mul_le` below, and the layer-cake/counting
bounds `Submission.Work.BoseB6Est.{zpCount, layerCake, zpIntegral, zpArith}` proved
in this workspace — is therefore not needed for the statement as given; it is kept
here because it sharpens the comparison to `∫ cleanBracket + O(1)`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

set_option maxHeartbeats 4000000

local notation "ℝ³" => Fin 3 → ℝ

/-! ## 1. The zero-point bracket as a function of the radius -/

/-- FS's scaled zero-point bracket `𝒜 − √(𝒜²−ℬ²)` with `𝒜 = τ̃(r)+β(r)`,
`ℬ = β(r)` (i.e. `cleanBracket` read as a function of `r = ‖t‖`). -/
def phifun (K : FsKernel) (εT c1 c2 r : ℝ) : ℝ :=
  (Work.BoseB6.fsTau εT c1 c2 r + K.β r)
    - Real.sqrt ((Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2)

/-- `cleanBracket` is `phifun` composed with the Euclidean norm. -/
lemma cleanBracket_eq_phifun (K : FsKernel) (εT c1 c2 : ℝ) (t : ℝ³) :
    cleanBracket K εT c1 c2 t = phifun K εT c1 c2 (nrm t) := rfl

/-! ## 2. Elementary pointwise facts about `phifun` -/

/-- `φ ≥ 0` (as soon as `τ̃, β ≥ 0`). -/
lemma phifun_nonneg (K : FsKernel) {εT c1 c2 r : ℝ} (hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r) :
    0 ≤ phifun K εT c1 c2 r := by
  have hb : 0 ≤ K.β r := K.nonneg r
  have h1 : (Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2
      ≤ (Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 := by nlinarith [sq_nonneg (K.β r)]
  have h2 := (Real.sqrt_le_left (by linarith :
      (0 : ℝ) ≤ Work.BoseB6.fsTau εT c1 c2 r + K.β r)).mpr h1
  rw [phifun]
  linarith

/-- `φ ≤ β` (uses `(τ̃+β)² − β² ≤ (τ̃+β)²`). -/
lemma phifun_le_beta (K : FsKernel) {εT c1 c2 r : ℝ}
    (hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r) :
    phifun K εT c1 c2 r ≤ K.β r := by
  have hb : 0 ≤ K.β r := K.nonneg r
  have h1 : (Work.BoseB6.fsTau εT c1 c2 r) ^ 2
      ≤ (Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2 := by nlinarith
  have h2 : Work.BoseB6.fsTau εT c1 c2 r
      ≤ Real.sqrt ((Work.BoseB6.fsTau εT c1 c2 r + K.β r) ^ 2 - (K.β r) ^ 2) :=
    (Real.le_sqrt hτ (by nlinarith [sq_nonneg (K.β r), hτ, hb])).mpr h1
  rw [phifun]
  linarith

/-- `φ` vanishes when `β` does. -/
lemma phifun_of_beta_eq_zero (K : FsKernel) {εT c1 c2 r : ℝ}
    (hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r) (hb : K.β r = 0) :
    phifun K εT c1 c2 r = 0 := by
  rw [phifun, hb]
  norm_num only [add_zero, zero_pow, sub_zero, Ne, reduceCtorEq, not_false_eq_true]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hτ, sub_self]

/-! ## 3. The pointwise facts in FS's regime -/

/-- **The support of `φ`**: `φ(r) = 0` beyond the kernel's momentum cutoff `T`. -/
lemma phifun_eq_zero_of_T_lt (K : FsKernel) {εT c1 c2 : ℝ} (hε0 : 0 ≤ εT)
    (hε1 : εT ≤ 1) {r : ℝ} (hr : K.T < r) : phifun K εT c1 c2 r = 0 :=
  phifun_of_beta_eq_zero K
    (fsTau_nonneg hε0 hε1 (le_of_lt (lt_of_le_of_lt K.Tnn hr)))
    (K.support r hr)

/-- **`β(r) ≤ 8π+1` for `r ≥ 0`** (on the support `β ≤ 8π + ηr ≤ 8π + ηT ≤ 8π+1`,
off the support `β = 0`). -/
lemma beta_le_B0 {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr0 : 0 ≤ r) :
    K.β r ≤ 8 * Real.pi + 1 := by
  rcases le_or_gt r K.T with hrT | hrT
  · have hclose := (abs_le.mp (K.close r hr0 hrT)).2
    have hη : K.η * r ≤ K.η * K.T := mul_le_mul_of_nonneg_left hrT K.ηnn
    linarith [h.hηT]
  · rw [K.support r hrT]; have := Real.pi_pos; linarith

/-- **`φ(r) ≤ 8π+1` for `r ≥ 0`**. -/
lemma phifun_le_B0 {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr0 : 0 ≤ r) :
    phifun K εT c1 c2 r ≤ 8 * Real.pi + 1 :=
  le_trans (phifun_le_beta K (fsTau_nonneg h.hε0 (by linarith [h.hε1]) hr0))
    (beta_le_B0 h hr0)

/-- **`τ̃(r) ≥ r²/8` for `r ≥ 2c₁`** (from `ε_T ≤ 1/2`, `0 ≤ c₁ ≤ c₂`). -/
lemma fsTau_ge {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1 / 2) (hc1 : 0 ≤ c1)
    (_hc12 : c1 ≤ c2) (h2c1 : 2 * c1 ≤ r) : r ^ 2 / 8 ≤ Work.BoseB6.fsTau εT c1 c2 r := by
  have hr : 0 ≤ r := by linarith
  have h1 : r / 2 ≤ max (|r| - c1) 0 := by
    rw [abs_of_nonneg hr]; exact le_max_of_le_left (by linarith)
  have h2 : (r / 2) ^ 2 ≤ (max (|r| - c1) 0) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : (1 - εT) * (r / 2) ^ 2 ≤ (1 - εT) * (max (|r| - c1) 0) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 : 0 ≤ εT * (max (|r| - c2) 0) ^ 2 := mul_nonneg hε0 (sq_nonneg _)
  have h5 : r ^ 2 / 8 ≤ (1 - εT) * (r / 2) ^ 2 := by nlinarith
  simp only [Work.BoseB6.fsTau]; linarith

/-- **The key pointwise bound**: for `r ≥ 2c₁`, `r·φ(r) ≤ 268`.

Indeed `τ̃(r) ≥ r²/8` gives `w = √(τ̃²+2τ̃β) ≥ r√β/2`, and
`φ = β²/(τ̃+β+w) ≤ β²/(β+w) ≤ 2β^{3/2}/r ≤ 2(8π+1)^{3/2}/r ≤ 268/r`. -/
lemma phifun_mul_le {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr : 2 * c1 ≤ r) :
    r * phifun K εT c1 c2 r ≤ 268 := by
  have hr0 : 0 ≤ r := by linarith [hr, h.hc1]
  rcases eq_or_lt_of_le hr0 with hrz | hrpos
  · rw [← hrz, zero_mul]; norm_num
  · have hB0 : K.β r ≤ 8 * Real.pi + 1 := beta_le_B0 h hr0
    have hτ0 : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r :=
      fsTau_nonneg h.hε0 (by linarith [h.hε1]) hr0
    have hτge : r ^ 2 / 8 ≤ Work.BoseB6.fsTau εT c1 c2 r := fsTau_ge h.hε0 h.hε1 h.hc1 h.hc12 hr
    set τ := Work.BoseB6.fsTau εT c1 c2 r with hτdef
    set v := K.β r with hvdef
    have hv0 : 0 ≤ v := by rw [hvdef]; exact K.nonneg r
    have hτ0' : 0 ≤ τ := by rw [hτdef]; exact hτ0
    have hτge' : r ^ 2 / 8 ≤ τ := by rw [hτdef]; exact hτge
    have hB : v ≤ 8 * Real.pi + 1 := by rw [hvdef]; exact hB0
    set w := Real.sqrt ((τ + v) ^ 2 - v ^ 2) with hwdef
    have hwsq : w ^ 2 = (τ + v) ^ 2 - v ^ 2 := Real.sq_sqrt (by nlinarith [hτ0', hv0])
    have hwnn : 0 ≤ w := Real.sqrt_nonneg _
    have hφ : phifun K εT c1 c2 r = (τ + v) - w := by rw [phifun, hτdef, hvdef, hwdef]
    have hident : ((τ + v) - w) * (τ + v + w) = v ^ 2 := by nlinarith [hwsq]
    rcases eq_or_lt_of_le hv0 with hvz | hvpos
    · have hvz' : v = 0 := hvz.symm
      have hwsq' : w ^ 2 = τ ^ 2 := by rw [hwsq, hvz']; ring
      have hwτ : w = τ := by nlinarith [hwsq', hwnn, hτ0']
      rw [hφ, hwτ, hvz', add_zero, sub_self, mul_zero]
      norm_num
    · have hwge : r * Real.sqrt v / 2 ≤ w := by
        rw [hwdef]
        refine (Real.le_sqrt (by positivity) (by nlinarith [hτ0', hv0])).mpr ?_
        have hsq : (r * Real.sqrt v / 2) ^ 2 = r ^ 2 * v / 4 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hv0]; ring
        rw [hsq]; nlinarith [hτge', hv0]
      have hdenp : 0 < v + r * Real.sqrt v / 2 := by
        have h1 : 0 ≤ r * Real.sqrt v / 2 := by positivity
        linarith
      have hstep1 : (τ + v) - w ≤ v ^ 2 / (v + r * Real.sqrt v / 2) := by
        rw [le_div_iff₀ hdenp]
        have h2 : 0 ≤ (τ + v) - w := by
          have h3 : 0 ≤ phifun K εT c1 c2 r := phifun_nonneg K hτ0
          rwa [hφ] at h3
        calc ((τ + v) - w) * (v + r * Real.sqrt v / 2)
            ≤ ((τ + v) - w) * (τ + v + w) := mul_le_mul_of_nonneg_left (by linarith) h2
          _ = v ^ 2 := hident
      have hstep2 : v ^ 2 / (v + r * Real.sqrt v / 2) ≤ 2 * v * Real.sqrt v / r := by
        rw [div_le_div_iff₀ hdenp hrpos]
        have hs : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0
        have hexp : 2 * v * Real.sqrt v * (v + r * Real.sqrt v / 2)
            = 2 * v ^ 2 * Real.sqrt v + r * v ^ 2 := by
          calc 2 * v * Real.sqrt v * (v + r * Real.sqrt v / 2)
              = 2 * v * Real.sqrt v * v + r * v * (Real.sqrt v * Real.sqrt v) := by ring
            _ = 2 * v * Real.sqrt v * v + r * v * v := by rw [hs]
            _ = 2 * v ^ 2 * Real.sqrt v + r * v ^ 2 := by ring
        have hprod : 0 ≤ 2 * v ^ 2 * Real.sqrt v := by positivity
        linarith [hexp, hprod]
      have hnum : 2 * v * Real.sqrt v ≤ 268 := by
        have hsv : Real.sqrt v ≤ Real.sqrt (8 * Real.pi + 1) := Real.sqrt_le_sqrt hB
        have hsB : Real.sqrt (8 * Real.pi + 1) ≤ 5.113 := by
          rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 5.113)]
          nlinarith [Real.pi_lt_d20]
        have hB2 : 8 * Real.pi + 1 ≤ 26.14 := by nlinarith [Real.pi_lt_d20]
        have hv2 : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0
        nlinarith [hB, hsv, hsB, hB2, hv0, Real.sqrt_nonneg v, Real.sqrt_nonneg (8*Real.pi+1)]
      calc r * phifun K εT c1 c2 r = r * ((τ + v) - w) := by rw [hφ]
        _ ≤ r * (2 * v * Real.sqrt v / r) := by
            apply mul_le_mul_of_nonneg_left _ hrpos.le
            linarith [hstep1, hstep2]
        _ = 2 * v * Real.sqrt v := by rw [mul_div_cancel₀ _ (ne_of_gt hrpos)]
        _ ≤ 268 := hnum

/-! ## 4. Elementary numeric bounds used in the assembly -/

lemma sqrt_three_le : Real.sqrt 3 ≤ 1.7321 := by
  rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 1.7321)]; norm_num

lemma eight_pi_add_one_le : 8 * Real.pi + 1 ≤ 26.14 := by
  nlinarith [Real.pi_lt_d20]

lemma sqrt_three_pi_cube_le : (Real.sqrt 3 * Real.pi) ^ 3 ≤ 161.2 := by
  have h1 : Real.sqrt 3 * Real.pi ≤ 5.4416 := by
    nlinarith [sqrt_three_le, Real.pi_lt_d20, Real.sqrt_nonneg 3, Real.pi_pos]
  have h2 : (0:ℝ) ≤ Real.sqrt 3 * Real.pi := by positivity
  calc (Real.sqrt 3 * Real.pi) ^ 3 ≤ 5.4416 ^ 3 := pow_le_pow_left₀ h2 h1 3
    _ ≤ 161.2 := by norm_num

/-! ## 5. The main Riemann-type comparison -/

/-- The mesh-`n` mode lattice has `(n+1)^6` points. -/
lemma card_modeIdx (n : ℕ) : (Fintype.card (modeIdx n) : ℝ) = ((n : ℝ) + 1) ^ 6 := by
  have h1 : Fintype.card (modeIdx n) = (Work.BoseB6.gridD n) ^ 3 := by
    simp [modeIdx, Fintype.card_fin]
  rw [h1, Work.BoseB6.gridD]
  push_cast
  ring

/-- **The zero-point lattice comparison.**

Every summand of the zero-point sum is at most `8π+1 ≤ 26.14` (`phifun_le_B0`),
there are `(n+1)^6` modes and the mesh volume is `meshD n³ = (2π/(n+1))³`, so the
whole sum is at most `26.14·(2π)³·((n:ℝ)+1)³ ≤ 10⁴((n:ℝ)+1)³`, which is dominated
by the last error term of the statement. -/
theorem zpRiem {n : ℕ} {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) (hn : 1 ≤ n)
    (hT : K.T ≤ Real.sqrt 3 * Real.pi * ((n : ℝ) + 1)) :
    (Work.BoseB6.meshD n) ^ 3 * (∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k))
      ≤ (∫ t : Fin 3 → ℝ, cleanBracket K εT c1 c2 t)
        + 10 ^ 4 * (1 + K.B) ^ 2 * (1 + |Real.log (K.T / c2)|)
        + 10 ^ 4 * ((n : ℝ) + 1) ^ 3 := by
  classical
  have hcard := card_modeIdx n
  -- each summand is at most `8π + 1 ≤ 26.14`
  have hsum_le : (∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k))
      ≤ 26.14 * ((n : ℝ) + 1) ^ 6 := by
    calc (∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k))
        ≤ ∑ _k : modeIdx n, 26.14 := by
          apply Finset.sum_le_sum
          intro k _
          rw [cleanBracket_eq_phifun]
          have h1 : phifun K εT c1 c2 (nrm (modePos n k)) ≤ 8 * Real.pi + 1 :=
            phifun_le_B0 h (Submission.BoseGases.eucNorm3_nonneg (modePos n k))
          linarith [eight_pi_add_one_le]
      _ = 26.14 * (Fintype.card (modeIdx n) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = 26.14 * ((n : ℝ) + 1) ^ 6 := by rw [hcard]
  -- the mesh volume times the number of modes
  have hcube : (Work.BoseB6.meshD n) ^ 3 * ((n : ℝ) + 1) ^ 6
      = (2 * Real.pi) ^ 3 * ((n : ℝ) + 1) ^ 3 := by
    rw [Work.BoseB6.meshD, div_pow]
    field_simp
  have hmain : (Work.BoseB6.meshD n) ^ 3
        * (∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k))
      ≤ 10 ^ 4 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (Work.BoseB6.meshD n) ^ 3 * (∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k))
        ≤ (Work.BoseB6.meshD n) ^ 3 * (26.14 * ((n : ℝ) + 1) ^ 6) :=
      mul_le_mul_of_nonneg_left hsum_le (by rw [Work.BoseB6.meshD]; positivity)
    have h2 : (Work.BoseB6.meshD n) ^ 3 * (26.14 * ((n : ℝ) + 1) ^ 6)
        = 26.14 * ((2 * Real.pi) ^ 3 * ((n : ℝ) + 1) ^ 3) := by
      rw [← hcube]; ring
    have h3 : 26.14 * ((2 * Real.pi) ^ 3 * ((n : ℝ) + 1) ^ 3) ≤ 10 ^ 4 * ((n : ℝ) + 1) ^ 3 := by
      have hp : Real.pi ≤ 3.1416 := by linarith [Real.pi_lt_d20]
      have hpos : 0 ≤ ((n : ℝ) + 1) ^ 3 := by positivity
      have h4 : 26.14 * (2 * Real.pi) ^ 3 ≤ 10 ^ 4 := by
        have h5 : 2 * Real.pi ≤ 6.2832 := by linarith
        have h6 : (2 * Real.pi) ^ 3 ≤ 6.2832 ^ 3 := pow_le_pow_left₀ (by positivity) h5 3
        nlinarith [h6]
      nlinarith [h4, hpos]
    linarith
  -- the remaining two error terms are nonnegative
  have hnonneg2 : 0 ≤ 10 ^ 4 * (1 + K.B) ^ 2 * (1 + |Real.log (K.T / c2)|) := by
    have h1 : 0 ≤ 1 + K.B := by linarith [K.Bnn]
    positivity
  have hint0 : 0 ≤ ∫ t : Fin 3 → ℝ, cleanBracket K εT c1 c2 t := by
    apply integral_nonneg
    intro t
    rw [cleanBracket_eq_phifun]
    exact phifun_nonneg K (fsTau_nonneg h.hε0 (by linarith [h.hε1])
      (Submission.BoseGases.eucNorm3_nonneg t))
  linarith [hmain, hint0, hnonneg2]

end Work.BoseB6Est
