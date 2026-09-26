import Mathlib

/-!
# A uniform lower bound for `‖exp (2πζ) - 1‖` away from the lattice `iℤ`

We prove that for every `δ > 0` there is `c > 0` such that

`‖exp (2πζ) - 1‖ ≥ c` whenever `ζ` is at distance at least `δ` from `iℤ`.

The exponential `exp (2πζ)` equals `1` exactly on `iℤ` (since `exp w = 1 ↔ w ∈ 2πiℤ`),
so such a bound exists; the content of the lemma is a quantitative, uniform version.

The proof reduces `ζ` modulo the period `i` of `exp (2π·)` — using
`round ζ.im` — and then uses the explicit formula

`‖exp (2πζ) - 1‖² = (exp (2πx) - 1)² + 4·exp (2πx)·sin (πy)²`,  `x = ζ.re`, `y = ζ.im`.

Splitting on whether `|x| ≥ δ/2` or not gives the two regimes; in the second regime
`dist(y, ℤ)` is bounded below by `δ/2`, which yields a positive lower bound for `sin (πy)²`.
-/

namespace Work.Asymptotics

/-- The identity `‖exp (2πζ) - 1‖² = (exp (2πx) - 1)² + 4·exp (2πx)·sin (πy)²`
for `ζ = x + iy`. -/
private lemma nrm (ζ : ℂ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * ζ) - 1‖ ^ 2
      = (Real.exp (2 * Real.pi * ζ.re) - 1)^2
        + 4 * Real.exp (2 * Real.pi * ζ.re) * Real.sin (Real.pi * ζ.im)^2 := by
  have hre : (Complex.exp (2 * (Real.pi : ℂ) * ζ)).re
      = Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) := by
    rw [Complex.exp_re]; simp [Complex.mul_re]
  have him : (Complex.exp (2 * (Real.pi : ℂ) * ζ)).im
      = Real.exp (2 * Real.pi * ζ.re) * Real.sin (2 * Real.pi * ζ.im) := by
    rw [Complex.exp_im]; simp [Complex.mul_im]
  have h0 : ‖Complex.exp (2 * (Real.pi : ℂ) * ζ) - 1‖ ^ 2
      = ((Complex.exp (2 * (Real.pi : ℂ) * ζ)).re - 1)^2
        + ((Complex.exp (2 * (Real.pi : ℂ) * ζ)).im)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]; ring
  have h2 : Real.cos (2 * Real.pi * ζ.im) = 1 - 2 * Real.sin (Real.pi * ζ.im)^2 := by
    rw [show 2 * Real.pi * ζ.im = 2 * (Real.pi * ζ.im) by ring, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * ζ.im)]
  have h3 : Real.cos (2 * Real.pi * ζ.im)^2 + Real.sin (2 * Real.pi * ζ.im)^2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [h0, hre, him]
  have step1 : (Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) - 1) ^ 2
        + (Real.exp (2 * Real.pi * ζ.re) * Real.sin (2 * Real.pi * ζ.im)) ^ 2
      = Real.exp (2 * Real.pi * ζ.re)^2 * Real.cos (2 * Real.pi * ζ.im)^2
        + Real.exp (2 * Real.pi * ζ.re)^2 * Real.sin (2 * Real.pi * ζ.im)^2
        - 2 * Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) + 1 := by ring
  have step2 : Real.exp (2 * Real.pi * ζ.re)^2 * Real.cos (2 * Real.pi * ζ.im)^2
        + Real.exp (2 * Real.pi * ζ.re)^2 * Real.sin (2 * Real.pi * ζ.im)^2
        - 2 * Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) + 1
      = Real.exp (2 * Real.pi * ζ.re)^2
        - 2 * Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) + 1 := by
    nlinarith [h3]
  have step3 : Real.exp (2 * Real.pi * ζ.re)^2
        - 2 * Real.exp (2 * Real.pi * ζ.re) * Real.cos (2 * Real.pi * ζ.im) + 1
      = (Real.exp (2 * Real.pi * ζ.re) - 1)^2
        + 4 * Real.exp (2 * Real.pi * ζ.re) * Real.sin (Real.pi * ζ.im)^2 := by
    nlinarith [h2]
  rw [step1, step2, step3]

/-- The function `ζ ↦ exp (2πζ)` is periodic with period `i`; for an integer `n`
subtracting `n·i` from the argument does not change the value. -/
private lemma expshift (ζ : ℂ) (n : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * (ζ - (n : ℂ) * Complex.I))
      = Complex.exp (2 * (Real.pi : ℂ) * ζ) := by
  have h : 2 * (Real.pi : ℂ) * (ζ - (n : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * ζ - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [h, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- From `a² ≤ b²` with `a, b ≥ 0` deduce `a ≤ b`. -/
private lemma le_sq_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 ≤ b^2) : a ≤ b := by
  simpa [abs_of_nonneg ha, abs_of_nonneg hb] using (sq_le_sq.mp h)

/-- `sin (π t)^2` only depends on `|t|`. -/
private lemma sin_sq_abs (t : ℝ) :
    Real.sin (Real.pi * t)^2 = Real.sin (Real.pi * |t|)^2 := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have hcos : Real.cos (2 * (Real.pi * t)) = Real.cos (2 * (Real.pi * |t|)) := by
    rw [← Real.cos_abs (2 * (Real.pi * t))]
    congr 1
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
  rw [hcos]

theorem exp_lattice_lower :
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧
      ∀ ζ : ℂ, (∀ m : ℤ, δ ≤ ‖ζ - (m : ℂ) * Complex.I‖) →
        c ≤ ‖Complex.exp (2 * (Real.pi : ℂ) * ζ) - 1‖ := by
  intro δ hδ
  refine ⟨min (1 - Real.exp (-(Real.pi*δ)))
      (2 * Real.exp (-(Real.pi*δ)/2) * Real.sin (Real.pi * min δ 1 / 2)), ?_, ?_⟩
  · refine lt_min ?_ ?_
    · have h : Real.exp (-(Real.pi*δ)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
      linarith
    · have hsin : 0 < Real.sin (Real.pi * min δ 1 / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have : 0 < min δ 1 := lt_min hδ zero_lt_one
          nlinarith [Real.pi_pos]
        · have : min δ 1 ≤ 1 := min_le_right _ _
          nlinarith [Real.pi_pos]
      exact mul_pos (mul_pos two_pos (Real.exp_pos _)) hsin
  · intro ζ hζ
    set n : ℤ := round ζ.im with hn
    set ζ' : ℂ := ζ - (n : ℂ) * Complex.I with hζ'def
    have hre' : ζ'.re = ζ.re := by simp [hζ'def]
    have him' : ζ'.im = ζ.im - n := by simp [hζ'def]
    have ht_le : |ζ'.im| ≤ 1/2 := by
      have h := abs_sub_round ζ.im
      rw [him', hn]; exact h
    have hF : ‖Complex.exp (2*(Real.pi:ℂ)*ζ') - 1‖ = ‖Complex.exp (2*(Real.pi:ℂ)*ζ) - 1‖ := by
      rw [hζ'def, expshift ζ n]
    have hhyp : ∀ m : ℤ, δ ≤ ‖ζ' - (m:ℂ)*Complex.I‖ := by
      intro m
      have h1 : ζ' - (m:ℂ)*Complex.I = ζ - ((m+n:ℤ):ℂ)*Complex.I := by
        rw [hζ'def]; push_cast; ring
      rw [h1]; exact hζ (m+n)
    have hconstr : δ^2 ≤ ζ.re^2 + ζ'.im^2 := by
      have h0 := hhyp 0
      simp only [Int.cast_zero, zero_mul, sub_zero] at h0
      have h2 : δ^2 ≤ ‖ζ'‖^2 := pow_le_pow_left₀ hδ.le h0 2
      rwa [show ‖ζ'‖^2 = ζ'.re^2 + ζ'.im^2 by
             rw [Complex.sq_norm, Complex.normSq_apply]; ring, hre'] at h2
    have hkey := nrm ζ'
    rw [hre'] at hkey
    have hkey2 : ‖Complex.exp (2*(Real.pi:ℂ)*ζ) - 1‖^2
        = (Real.exp (2*Real.pi*ζ.re) - 1)^2
          + 4*Real.exp (2*Real.pi*ζ.re)*Real.sin (Real.pi*ζ'.im)^2 := by
      rw [← hF]; exact hkey
    rcases le_or_gt (δ/2) |ζ.re| with hxA | hxB
    · -- Regime `|Re ζ| ≥ δ/2`
      have hA0 : 0 ≤ 1 - Real.exp (-(Real.pi*δ)) := by
        have h : Real.exp (-(Real.pi*δ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
        linarith
      have hbase : (1 - Real.exp (-(Real.pi*δ)))^2 ≤ (Real.exp (2*Real.pi*ζ.re) - 1)^2 := by
        rcases le_or_gt 0 ζ.re with hx | hx
        · have hxδ : δ/2 ≤ ζ.re := by
            rw [abs_of_nonneg hx] at hxA; exact hxA
          have h1 : 1 - Real.exp (-(Real.pi*δ)) ≤ 2*Real.pi*ζ.re := by
            have h := Real.add_one_le_exp (-(Real.pi*δ))
            have h2 : Real.pi*δ ≤ 2*Real.pi*ζ.re := by nlinarith [Real.pi_pos, hxδ]
            linarith
          have h3 : 2*Real.pi*ζ.re ≤ Real.exp (2*Real.pi*ζ.re) - 1 := by
            have h := Real.add_one_le_exp (2*Real.pi*ζ.re); linarith
          exact pow_le_pow_left₀ hA0 (le_trans h1 h3) 2
        · have hxδ : ζ.re ≤ -(δ/2) := by
            rw [abs_of_neg hx] at hxA; linarith
          have he1 : Real.exp (2*Real.pi*ζ.re) ≤ Real.exp (-(Real.pi*δ)) :=
            Real.exp_le_exp.mpr (by nlinarith [hxδ, Real.pi_pos])
          have h2 : 1 - Real.exp (-(Real.pi*δ)) ≤ 1 - Real.exp (2*Real.pi*ζ.re) := by
            have : Real.exp (-(Real.pi*δ)) ≤ 1 := by
              rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
            linarith
          have h3 := pow_le_pow_left₀ hA0 h2 2
          rwa [show (1 - Real.exp (2*Real.pi*ζ.re))^2 = (Real.exp (2*Real.pi*ζ.re) - 1)^2 by ring] at h3
      have hnonneg : 0 ≤ 4*Real.exp (2*Real.pi*ζ.re)*Real.sin (Real.pi*ζ'.im)^2 := by positivity
      have hstep : (1 - Real.exp (-(Real.pi*δ)))^2 ≤ ‖Complex.exp (2*(Real.pi:ℂ)*ζ) - 1‖^2 := by
        rw [hkey2]; linarith
      exact le_trans (min_le_left _ _) (le_sq_sq hA0 (norm_nonneg _) hstep)
    · -- Regime `|Re ζ| < δ/2`, where `dist (Im ζ, ℤ)` is bounded below
      have hδt : δ/2 ≤ |ζ'.im| := by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : ζ'.im^2 < δ^2/4 := by
          have h := pow_lt_pow_left₀ hcon (abs_nonneg ζ'.im) (by norm_num : (2:ℕ) ≠ 0)
          rw [sq_abs] at h
          nlinarith [h]
        have h2 : ζ.re^2 < δ^2/4 := by
          have h := pow_lt_pow_left₀ hxB (abs_nonneg ζ.re) (by norm_num : (2:ℕ) ≠ 0)
          rw [sq_abs] at h
          nlinarith [h]
        nlinarith [hconstr, hδ]
      have hδ1 : δ ≤ 1 := by linarith [hδt, ht_le]
      have hsin : Real.sin (Real.pi*δ/2)^2 ≤ Real.sin (Real.pi*ζ'.im)^2 := by
        rw [sin_sq_abs ζ'.im]
        have hle : Real.sin (Real.pi*δ/2) ≤ Real.sin (Real.pi*|ζ'.im|) :=
          Real.monotoneOn_sin (by constructor <;> nlinarith [Real.pi_pos, hδ])
            (by constructor <;> nlinarith [Real.pi_pos, ht_le])
            (by nlinarith [Real.pi_pos, hδt])
        have hnn : 0 ≤ Real.sin (Real.pi*δ/2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, hδ])
            (by nlinarith [Real.pi_pos, hδ])
        exact pow_le_pow_left₀ hnn hle 2
      have hexp : Real.exp (-(Real.pi*δ)) ≤ Real.exp (2*Real.pi*ζ.re) := by
        rw [Real.exp_le_exp]
        rw [abs_lt] at hxB
        nlinarith [Real.pi_pos, hxB.2]
      have hmin : min δ 1 = δ := min_eq_left hδ1
      have hB0 : 0 ≤ 2*Real.exp (-(Real.pi*δ)/2)*Real.sin (Real.pi*min δ 1/2) := by
        rw [hmin]
        have hsin' : 0 ≤ Real.sin (Real.pi*δ/2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, hδ])
            (by nlinarith [Real.pi_pos, hδ1])
        positivity
      have hsq : (2*Real.exp (-(Real.pi*δ)/2))^2 = 4*Real.exp (-(Real.pi*δ)) := by
        rw [mul_pow]
        have he : Real.exp (-(Real.pi*δ)/2)^2 = Real.exp (-(Real.pi*δ)) := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        rw [he]; norm_num
      have hstep : (2*Real.exp (-(Real.pi*δ)/2)*Real.sin (Real.pi*min δ 1/2))^2
          ≤ ‖Complex.exp (2*(Real.pi:ℂ)*ζ) - 1‖^2 := by
        rw [hkey2, hmin]
        have hL : (2*Real.exp (-(Real.pi*δ)/2)*Real.sin (Real.pi*δ/2))^2
            = 4*Real.exp (-(Real.pi*δ))*Real.sin (Real.pi*δ/2)^2 := by
          rw [show 2*Real.exp (-(Real.pi*δ)/2)*Real.sin (Real.pi*δ/2)
              = (2*Real.exp (-(Real.pi*δ)/2))*Real.sin (Real.pi*δ/2) by ring,
            mul_pow, hsq]
        rw [hL]
        have h1 : Real.exp (-(Real.pi*δ))*Real.sin (Real.pi*δ/2)^2
            ≤ Real.exp (2*Real.pi*ζ.re)*Real.sin (Real.pi*δ/2)^2 :=
          mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
        have h2 : Real.exp (2*Real.pi*ζ.re)*Real.sin (Real.pi*δ/2)^2
            ≤ Real.exp (2*Real.pi*ζ.re)*Real.sin (Real.pi*ζ'.im)^2 :=
          mul_le_mul_of_nonneg_left hsin (le_of_lt (Real.exp_pos _))
        have h3 : (0:ℝ) ≤ (Real.exp (2*Real.pi*ζ.re) - 1)^2 := sq_nonneg _
        linarith [h1, h2, h3]
      exact le_trans (min_le_right _ _) (le_sq_sq hB0 (norm_nonneg _) hstep)

end Work.Asymptotics
