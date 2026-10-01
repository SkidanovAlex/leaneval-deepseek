import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime

open scoped BigOperators ComplexConjugate

namespace Commons.NumberTheory.GaussSum

/-- Conjugating the standard additive character at `a` gives the character at `-a`. -/
private lemma stdAddChar_star (p : ℕ) [NeZero p] (a : ZMod p) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  calc star (ZMod.stdAddChar a)
      = star (((ZMod.toCircle (N := p)) a : Circle) : ℂ) := rfl
    _ = ((((ZMod.toCircle (N := p)) a : Circle))⁻¹ : ℂ) :=
        (Circle.coe_inv_eq_conj _).symm
    _ = ((((ZMod.toCircle (N := p)) a : Circle))⁻¹ : Circle) :=
        (Circle.coe_inv _).symm
    _ = (((ZMod.toCircle (N := p)) (-a) : Circle) : ℂ) := by
          congr 1
          exact (AddChar.map_neg_eq_inv (ZMod.toCircle (N := p)) a).symm
    _ = ZMod.stdAddChar (-a) := rfl

/-- A complete non-trivial linear character sum over `ZMod p` vanishes. -/
private lemma sum_stdAddChar_mul (p : ℕ) [Fact p.Prime] [NeZero p] {u : ZMod p}
    (hu : u ≠ 0) : ∑ y : ZMod p, ZMod.stdAddChar (u * y) = 0 := by
  have h := AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar p)
  rw [if_neg hu] at h
  simpa [mul_comm] using h

/-- A complete non-trivial affine character sum over `ZMod p` vanishes. -/
private lemma sum_stdAddChar_mul_add (p : ℕ) [Fact p.Prime] [NeZero p] {u v : ZMod p}
    (hu : u ≠ 0) : ∑ y : ZMod p, ZMod.stdAddChar (u * y + v) = 0 := by
  have h1 : ∀ y : ZMod p, ZMod.stdAddChar (u * y + v)
      = ZMod.stdAddChar (u * y) * ZMod.stdAddChar v := fun y => by
    rw [AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.sum_mul, sum_stdAddChar_mul p hu, zero_mul]

/-- `2` is nonzero in `ZMod p` for an odd prime `p`. -/
private lemma zmod_two_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  rcases (Nat.dvd_prime (show Nat.Prime 2 by norm_num)).mp hdvd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h2

/-- The squared modulus of a non-degenerate quadratic Gauss sum over `ZMod p` is `p`. -/
private lemma norm_sq_quadratic_sum (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    (a b : ZMod p) (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * x ^ 2 + b * x)‖ ^ 2 = (p : ℝ) := by
  have hstar : ∀ t : ZMod p, star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) :=
    stdAddChar_star p
  have h2z : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp2
  set T : ℂ := ∑ x : ZMod p, ZMod.stdAddChar (a * x ^ 2 + b * x) with hTdef
  have hT : T * star T = (p : ℂ) := by
    have h1 : T * star T
        = ∑ x : ZMod p, ∑ y : ZMod p,
            ZMod.stdAddChar ((x - y) * (a * (x + y) + b)) := by
      rw [hTdef, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hstar, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    have h2 : (∑ x : ZMod p, ∑ y : ZMod p,
          ZMod.stdAddChar ((x - y) * (a * (x + y) + b)))
        = ∑ y : ZMod p, ∑ u : ZMod p,
            ZMod.stdAddChar (u * (a * (u + 2 * y) + b)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Equiv.sum_comp (Equiv.addRight y)
        (fun x : ZMod p => ZMod.stdAddChar ((x - y) * (a * (x + y) + b)))]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Equiv.coe_addRight]
      congr 1
      ring
    have h3 : (∑ y : ZMod p, ∑ u : ZMod p,
          ZMod.stdAddChar (u * (a * (u + 2 * y) + b)))
        = ∑ u : ZMod p, ∑ y : ZMod p,
            ZMod.stdAddChar ((2 * a * u) * y + u * (a * u + b)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun y _ => ?_
      congr 1
      ring
    have h4 : (∑ u : ZMod p, ∑ y : ZMod p,
          ZMod.stdAddChar ((2 * a * u) * y + u * (a * u + b))) = (p : ℂ) := by
      have hinner : ∀ u : ZMod p,
          (∑ y : ZMod p, ZMod.stdAddChar ((2 * a * u) * y + u * (a * u + b)))
            = if u = 0 then (p : ℂ) else 0 := by
        intro u
        by_cases hu : u = 0
        · subst u
          simp [AddChar.map_zero_eq_one, Finset.sum_const, ZMod.card]
        · rw [if_neg hu]
          have hcoef : (2 * a * u : ZMod p) ≠ 0 :=
            mul_ne_zero (mul_ne_zero h2z ha) hu
          simpa only [mul_assoc] using
            sum_stdAddChar_mul_add p (u := 2 * a * u) (v := u * (a * u + b)) hcoef
      rw [Finset.sum_congr rfl fun u _ => hinner u]
      rw [Finset.sum_ite_eq' Finset.univ 0 (fun _ => (p : ℂ))]
      simp
    rw [h1, h2, h3, h4]
  have hnorm : Complex.normSq T = (p : ℝ) := by
    have hcast : ((Complex.normSq T : ℝ) : ℂ) = (p : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      exact hT
    exact Complex.ofReal_inj.mp hcast
  have hsq : ‖T‖ ^ 2 = (p : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hnorm
  exact hsq

/-- From `‖S‖² = p` conclude `‖S‖ ≤ 2√p`. -/
private lemma norm_le_two_sqrt_of_sq_eq (p : ℕ) (S : ℂ) (h : ‖S‖ ^ 2 = (p : ℝ)) :
    ‖S‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hpnn : (0 : ℝ) ≤ p := by positivity
  have hsqrt : ‖S‖ = Real.sqrt (p : ℝ) := by
    have h1 : Real.sqrt (‖S‖ ^ 2) = Real.sqrt (p : ℝ) := by rw [h]
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg S)] at h1
  rw [hsqrt]
  nlinarith [Real.sqrt_nonneg (p : ℝ)]

theorem prime_field_quadratic_bound (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    (β δ : ℤ) (hδ : ¬ (p : ℤ) ∣ δ) :
    ‖∑ x : ZMod p, ZMod.stdAddChar ((β : ZMod p) * x - (δ : ZMod p) * x ^ 2)‖
      ≤ 2 * Real.sqrt p := by
  have hδz : (δ : ZMod p) ≠ 0 := by
    intro h
    exact hδ ((ZMod.intCast_zmod_eq_zero_iff_dvd δ p).mp h)
  have ha : (-(δ : ZMod p)) ≠ 0 := neg_ne_zero.mpr hδz
  have hsum : (∑ x : ZMod p, ZMod.stdAddChar ((β : ZMod p) * x - (δ : ZMod p) * x ^ 2))
      = ∑ x : ZMod p,
          ZMod.stdAddChar ((-(δ : ZMod p)) * x ^ 2 + (β : ZMod p) * x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  rw [hsum]
  exact norm_le_two_sqrt_of_sq_eq p _ (norm_sq_quadratic_sum p hp2 (-(δ : ZMod p)) (β : ZMod p) ha)

end Commons.NumberTheory.GaussSum