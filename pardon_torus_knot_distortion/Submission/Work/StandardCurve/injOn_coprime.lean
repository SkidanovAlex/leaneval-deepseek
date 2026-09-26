import Mathlib
import Submission.Work.Core.Torus

/-!
# Injectivity of the standard `(p,q)`-torus curve on a fundamental interval

The main result of this file, `Work.StandardCurve.injOn_coprime`, is that the
explicitly parametrized standard `(p,q)`-torus curve on the torus of revolution
(with major radius `2` and minor radius `1`) is injective on the half-open
fundamental interval `[0, 2π)` as soon as `p` and `q` are coprime.

The geometry behind the proof is the following.  Writing the curve as
`t ↦ (θ(t), φ(t)) = (p t, q t)` in the two angle coordinates of the torus, the
map `(θ, φ) ↦ ((2 + cos φ) cos θ, (2 + cos φ) sin θ, sin φ)` determines
`φ mod 2π` and then `θ mod 2π`, since the factor `2 + cos φ` is always positive
(indeed at least `1`).  Hence an equality of the two points of `ℝ³` forces
`p(s - t) ∈ 2πℤ` and `q(s - t) ∈ 2πℤ`, and by Bézout (coprimality) this forces
`s - t ∈ 2πℤ`.  Since `s, t` lie in `[0, 2π)` we get `|s - t| < 2π`, hence
`s = t`.
-/

set_option linter.unusedVariables false

open LeanEval.KnotTheory.PardonDistortion

namespace Work.StandardCurve

/-- The third coordinate of the standard `(p,q)`-torus curve. -/
lemma curve_apply_two (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t 2 = Real.sin ((q : ℝ) * t) := rfl

/-- The second coordinate of the standard `(p,q)`-torus curve. -/
lemma curve_apply_one (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t 1 = (2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t) := rfl

/-- The first coordinate of the standard `(p,q)`-torus curve. -/
lemma curve_apply_zero (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t 0 = (2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t) := rfl

/-- If `cos a = cos b` and `sin a = sin b`, then `a ≡ b` modulo `2π`. -/
lemma exists_int_mul_two_pi_of_cos_sin_eq {a b : ℝ} (hcos : Real.cos a = Real.cos b)
    (hsin : Real.sin a = Real.sin b) : ∃ k : ℤ, a = b + k * (2 * Real.pi) := by
  have h1 : Real.cos (a - b) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq b]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (a - b)).mp h1
  exact ⟨k, by linarith [hk]⟩

/-- The standard `(p,q)`-torus curve is injective on `[0, 2π)` when `p` and `q`
are coprime. -/
theorem injOn_coprime (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    Set.InjOn (LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q) (Set.Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  rw [Set.mem_Ico] at hs ht
  -- Extract the three coordinate equalities.
  have h2 : Real.sin ((q : ℝ) * s) = Real.sin ((q : ℝ) * t) := by
    have := congrArg (fun v : R3 => v 2) hst
    simpa [curve_apply_two] using this
  have h0 : (2 + Real.cos ((q : ℝ) * s)) * Real.cos ((p : ℝ) * s) =
      (2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t) := by
    have := congrArg (fun v : R3 => v 0) hst
    simpa [curve_apply_zero] using this
  have h1 : (2 + Real.cos ((q : ℝ) * s)) * Real.sin ((p : ℝ) * s) =
      (2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t) := by
    have := congrArg (fun v : R3 => v 1) hst
    simpa [curve_apply_one] using this
  -- Squaring and adding the first two coordinates shows `2 + cos (q s) = 2 + cos (q t)`.
  have hsquares : (2 + Real.cos ((q : ℝ) * s)) ^ 2 = (2 + Real.cos ((q : ℝ) * t)) ^ 2 := by
    have hsum := congrArg (fun x : ℝ => x ^ 2) h0
    have hsum1 := congrArg (fun x : ℝ => x ^ 2) h1
    nlinarith [hsum, hsum1, Real.cos_sq_add_sin_sq ((p : ℝ) * s),
      Real.cos_sq_add_sin_sq ((p : ℝ) * t)]
  have hcosq : Real.cos ((q : ℝ) * s) = Real.cos ((q : ℝ) * t) := by
    have hs1 : (1 : ℝ) ≤ 2 + Real.cos ((q : ℝ) * s) := by
      linarith [Real.neg_one_le_cos ((q : ℝ) * s)]
    have ht1 : (1 : ℝ) ≤ 2 + Real.cos ((q : ℝ) * t) := by
      linarith [Real.neg_one_le_cos ((q : ℝ) * t)]
    nlinarith [hsquares, hs1, ht1]
  -- The prefactor `2 + cos (q t)` is nonzero, so the first two coordinates also
  -- determine `cos (p t)` and `sin (p t)`.
  have hcpos : (2 + Real.cos ((q : ℝ) * t)) ≠ 0 := by
    have : (1 : ℝ) ≤ 2 + Real.cos ((q : ℝ) * t) := by
      linarith [Real.neg_one_le_cos ((q : ℝ) * t)]
    linarith
  have hcosp : Real.cos ((p : ℝ) * s) = Real.cos ((p : ℝ) * t) := by
    have h := h0
    rw [hcosq] at h
    exact mul_left_cancel₀ hcpos h
  have hsinp : Real.sin ((p : ℝ) * s) = Real.sin ((p : ℝ) * t) := by
    have h := h1
    rw [hcosq] at h
    exact mul_left_cancel₀ hcpos h
  -- Congruences modulo `2π` for the two angles.
  obtain ⟨kq, hkq⟩ := exists_int_mul_two_pi_of_cos_sin_eq hcosq h2
  obtain ⟨kp, hkp⟩ := exists_int_mul_two_pi_of_cos_sin_eq hcosp hsinp
  set u : ℝ := s - t with hu
  have huq : (q : ℝ) * u = (kq : ℝ) * (2 * Real.pi) := by
    have h : (q : ℝ) * u = (q : ℝ) * s - (q : ℝ) * t := by rw [hu]; ring
    rw [h]; linarith [hkq]
  have hup : (p : ℝ) * u = (kp : ℝ) * (2 * Real.pi) := by
    have h : (p : ℝ) * u = (p : ℝ) * s - (p : ℝ) * t := by rw [hu]; ring
    rw [h]; linarith [hkp]
  -- Bézout: `a p + b q = 1`, so `u = (a p + b q) u` is an integral multiple of `2π`.
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hc : IsCoprime ((p : ℤ)) ((q : ℤ)))
  have habR : ((a * (p : ℤ) + b * (q : ℤ) : ℤ) : ℝ) = 1 := by exact_mod_cast hab
  have huJ : u = ((a * kp + b * kq : ℤ) : ℝ) * (2 * Real.pi) := by
    calc u = ((a * (p : ℤ) + b * (q : ℤ) : ℤ) : ℝ) * u := by rw [habR, one_mul]
      _ = (a : ℝ) * ((p : ℝ) * u) + (b : ℝ) * ((q : ℝ) * u) := by push_cast; ring
      _ = (a : ℝ) * ((kp : ℝ) * (2 * Real.pi)) + (b : ℝ) * ((kq : ℝ) * (2 * Real.pi)) := by
            rw [hup, huq]
      _ = ((a * kp + b * kq : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, u = (J : ℝ) * (2 * Real.pi) := ⟨_, huJ⟩
  -- Since `s, t ∈ [0, 2π)`, we have `-2π < u < 2π`, which forces `J = 0`.
  have hulo : -(2 * Real.pi) < u := by rw [hu]; linarith [hs.1, ht.2]
  have huhi : u < 2 * Real.pi := by rw [hu]; linarith [hs.2, ht.1]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hJlt1 : (J : ℝ) < 1 := by nlinarith [huhi, hJ, hpi]
  have hJgt : (-1 : ℝ) < (J : ℝ) := by nlinarith [hulo, hJ, hpi]
  have hJeq : J = 0 := by
    have h1' : J < 1 := by exact_mod_cast hJlt1
    have h2' : (-1 : ℤ) < J := by exact_mod_cast hJgt
    omega
  have hu0 : u = 0 := by rw [hJ, hJeq]; simp
  linarith [hu, hu0]

end Work.StandardCurve
