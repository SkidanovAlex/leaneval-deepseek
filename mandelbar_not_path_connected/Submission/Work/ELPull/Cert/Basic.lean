/-
# ELPull — the rational arithmetic layer of the angle certificate (P5)

This module contains the workhorses which turn every check of the exact-rational angle
certificate (`Submission/Work/lead_mb/mb_EL_cert.py`) into a `norm_num`/`decide` computation
over `ℚ`, together with the cast lemmas which transfer the whole certificate to `ℝ`.

The normal form of an angle is `qq p N = p / N` with `p : ℤ`, `N : ℕ`; the angle-doubling map
`Tq q = Int.fract (-2 * q)` acts on it by `p ↦ p * (-2) % N`.

## Main results

* `Work.ELPull.Cert.qq`, `qq_cast` : the normal form and its cast to `ℝ`;
* `Tq_qq`, `Tq_iterate_qq` : `Tq^[n] (p/N) = (p * (-2)^n % N)/N`;
* `Tq_cast`, `Tq_iterate_cast` : the same on `ℝ`;
* `InArcQ_iff_of` : `InArcQ x a b ↔ a < x ∧ x < b` for unwrapped arcs;
* `fract_eq_of_mem` : evaluation of `Int.fract` on an explicit rational;
* `preArcQ`, `IsPB1StepQ` : the `ℚ`-versions of the pull-back notions of `Defs.lean`, with
  `preArcQ_cast_fst`/`snd` and `IsPB1StepQ.to_real`.
-/
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

/-! ## 1. The normal form `qq p N` of a rational angle -/

/-- `p / N` as a rational: the normal form of every angle of the certificate. -/
abbrev qq (p : ℤ) (N : ℕ) : ℚ := (p : ℚ) / (N : ℚ)

theorem qq_cast (p : ℤ) (N : ℕ) : ((qq p N : ℚ) : ℝ) = (p : ℝ) / (N : ℝ) := by
  rw [qq]; push_cast; ring

/-! ## 2. The doubling map on the normal form -/

/-- `Tq` on `p / N`: the numerator is multiplied by `-2` modulo `N`. -/
theorem Tq_qq (p : ℤ) (N : ℕ) : Tq (qq p N) = qq ((-2 * p) % (N : ℤ)) N := by
  rw [Tq, qq, qq,
    show -2 * ((p : ℚ) / ((N : ℕ) : ℚ)) = (((-2 * p : ℤ)) : ℚ) / ((N : ℕ) : ℚ) by
      push_cast; ring,
    Int.fract_div_intCast_eq_div_intCast_mod]

/-- `(a * (b % N)) % N = (a * b) % N`. -/
theorem mul_emod_left (a b N : ℤ) : (a * (b % N)) % N = (a * b) % N := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

/-- The iterates of `Tq` on the normal form: `Tq^[n] (p/N) = (p * (-2)^n mod N)/N`, the
numerator of the input being assumed reduced modulo `N`. -/
theorem Tq_iterate_qq (n : ℕ) (p : ℤ) (N : ℕ) (hp : p % (N : ℤ) = p) :
    Tq^[n] (qq p N) = qq (p * (-2) ^ n % (N : ℤ)) N := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, mul_one, hp]
  | succ n ih =>
    have h : (-2 * (p * (-2) ^ n % (N : ℤ))) % (N : ℤ) = (p * (-2) ^ (n + 1)) % (N : ℤ) := by
      rw [mul_emod_left (-2) (p * (-2) ^ n) (N : ℤ), pow_succ]
      congr 1
      ring
    rw [Function.iterate_succ_apply', ih, Tq_qq, h]

/-- The value of `Tq^[n]` at a concrete normal-form angle, with the numerator supplied. -/
theorem Tq_iterate_qq_of (n : ℕ) (p r : ℤ) (N : ℕ) (hp : p % (N : ℤ) = p)
    (hr : p * (-2) ^ n % (N : ℤ) = r) : Tq^[n] (qq p N) = qq r N := by
  rw [Tq_iterate_qq n p N hp, hr]

/-! ## 3. Casting to `ℝ` -/

/-- The cast of the doubling map: `T` on `ℝ` is `Tq` on `ℚ`. -/
theorem Tq_cast (q : ℚ) : T (q : ℝ) = ((Tq q : ℚ) : ℝ) := by
  rw [T, Tq, Rat.cast_fract]
  push_cast
  rfl

/-- The cast of the iterates of the doubling map. -/
theorem Tq_iterate_cast (n : ℕ) (q : ℚ) : T^[n] (q : ℝ) = ((Tq^[n] q : ℚ) : ℝ) := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Tq_cast]

/-! ## 4. Arcs on `ℚ` -/

theorem arcLenQ_nonneg (a b : ℚ) : 0 ≤ arcLenQ a b := Int.fract_nonneg _

theorem arcLenQ_lt_one (a b : ℚ) : arcLenQ a b < 1 := Int.fract_lt_one _

/-- `InArcQ` for an *unwrapped* arc `(a, b)` (`0 ≤ b - a < 1`) and an unwrapped point
`x ∈ [a, a+1)`: it is just the strict inequality `a < x < b`. -/
theorem InArcQ_iff_of {x a b : ℚ} (h0 : 0 ≤ b - a) (h1 : b - a < 1) (h2 : 0 ≤ x - a)
    (h3 : x - a < 1) : InArcQ x a b ↔ a < x ∧ x < b := by
  rw [InArcQ, arcLenQ, Int.fract_eq_self.mpr ⟨h2, h3⟩, Int.fract_eq_self.mpr ⟨h0, h1⟩,
    sub_pos, sub_lt_sub_iff_right]

/-- Evaluation of `Int.fract` at an explicit rational: `Int.fract x = r` as soon as
`0 ≤ r < 1` and `x - r` is an integer. -/
theorem fract_eq_of_mem {x r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1)
    (h : ∃ z : ℤ, x - r = (z : ℚ)) : Int.fract x = r :=
  Int.fract_eq_iff.mpr ⟨h0, h1, h⟩

/-- The same, with the difference hypothesis in the form `x - r ∈ ℤ`. -/
theorem fract_eq_of_mem' {x r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1)
    (h : x - r ∈ Set.range (Int.cast : ℤ → ℚ)) : Int.fract x = r := by
  obtain ⟨z, hz⟩ := Set.mem_range.mp h
  exact fract_eq_of_mem h0 h1 ⟨z, hz.symm⟩

/-- The `k`-th counterclockwise `T`-preimage arc of the rational arc `I = (p, q)` (with `q` the
unwrapped upper endpoint), as a pair of rationals. -/
def preArcQ (k : Fin 2) (I : ℚ × ℚ) : ℚ × ℚ :=
  (Int.fract (-(I.2) / 2 + (k : ℚ) / 2), Int.fract (-(I.1) / 2 + (k : ℚ) / 2))

theorem preArcQ_cast_fst (k : Fin 2) (I : ℚ × ℚ) :
    (((preArcQ k I).1 : ℚ) : ℝ) = (preArc k ((I.1 : ℝ), (I.2 : ℝ))).1 := by
  rw [preArcQ, preArc]; push_cast; rfl

theorem preArcQ_cast_snd (k : Fin 2) (I : ℚ × ℚ) :
    (((preArcQ k I).2 : ℚ) : ℝ) = (preArc k ((I.1 : ℝ), (I.2 : ℝ))).2 := by
  rw [preArcQ, preArc]; push_cast; rfl

/-- The `ℚ`-version of `IsPreimageArcPair`. -/
def IsPreimageArcPairQ (k : Fin 2) (I Q : ℚ × ℚ) : Prop :=
  (Q.1 = (preArcQ k I).1 ∧ Q.2 = (preArcQ k I).2) ∨
    (Q.2 = (preArcQ k I).1 ∧ Q.1 = (preArcQ k I).2)

/-- The `ℚ`-version of the one-step pull-back relation `IsPB1Step`. -/
def IsPB1StepQ (I Q : ℚ × ℚ) : Prop := IsPreimageArcPairQ 0 I Q ∨ IsPreimageArcPairQ 1 I Q

theorem IsPreimageArcPairQ.to_real {k : Fin 2} {I Q : ℚ × ℚ} (h : IsPreimageArcPairQ k I Q) :
    IsPreimageArcPair k ((I.1 : ℝ), (I.2 : ℝ)) ((Q.1 : ℝ), (Q.2 : ℝ)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1, preArcQ_cast_fst], by rw [h2, preArcQ_cast_snd]⟩
  · exact Or.inr ⟨by rw [h1, preArcQ_cast_fst], by rw [h2, preArcQ_cast_snd]⟩

theorem IsPB1StepQ.to_real {I Q : ℚ × ℚ} (h : IsPB1StepQ I Q) :
    IsPB1Step ((I.1 : ℝ), (I.2 : ℝ)) ((Q.1 : ℝ), (Q.2 : ℝ)) :=
  h.elim (fun h0 => Or.inl h0.to_real) (fun h1 => Or.inr h1.to_real)

/-- `x` is one of the two angles of the pair `Q`. -/
def MemPairQ (x : ℚ) (Q : ℚ × ℚ) : Prop := x = Q.1 ∨ x = Q.2

/-- Two pairs are **unlinked**: each of them has both its angles on the same side of each arc
of the other. -/
def UnlinkedQ (P Q : ℚ × ℚ) : Prop :=
  (InArcQ Q.1 P.1 P.2 ↔ InArcQ Q.2 P.1 P.2) ∧ (InArcQ P.1 Q.1 Q.2 ↔ InArcQ P.2 Q.1 Q.2)

/-- `InArcQ` for an unwrapped arc `(a, b)` and a point `x` *below* `a` (the wrapped part of the
arc): the condition is `x + 1 < b`. -/
theorem InArcQ_iff_of_lt {x a b : ℚ} (ha : a < b) (hb : b - a < 1) (hx : x < a)
    (hx1 : a < x + 1) : InArcQ x a b ↔ x + 1 < b := by
  have hfr : Int.fract (x - a) = x - a + 1 := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by ring⟩⟩
  rw [InArcQ, arcLenQ, hfr, Int.fract_eq_self.mpr ⟨by linarith, hb⟩]
  constructor
  · intro h; linarith [h.2]
  · intro h; exact ⟨by linarith, by linarith⟩

/-- Both angles of the pair `Q` lie on the same side of the arc `I`. -/
def SameSide (Q I : ℚ × ℚ) : Prop := InArcQ Q.1 I.1 I.2 ↔ InArcQ Q.2 I.1 I.2

/-- `Tq` is invariant under integral translations of the angle. -/
theorem Tq_add_int (q : ℚ) (m : ℤ) : Tq (q + m) = Tq q := by
  rw [Tq, Tq, show -2 * (q + (m : ℚ)) = -2 * q - ((2 * m : ℤ) : ℚ) by push_cast; ring]
  exact Int.fract_sub_intCast (-2 * q) (2 * m)

/-- `Tq^[n+1]` is invariant under integral translations of the angle. -/
theorem Tq_iterate_add_int (n : ℕ) (q : ℚ) (m : ℤ) : Tq^[n + 1] (q + m) = Tq^[n + 1] q := by
  induction n with
  | zero => rw [Function.iterate_one]; exact Tq_add_int q m
  | succ n ih =>
    rw [Function.iterate_succ_apply' Tq (n + 1) (q + m), ih]
    exact (Function.iterate_succ_apply' Tq (n + 1) q).symm

theorem arcLenQ_cast (a b : ℚ) : arcLen (a : ℝ) (b : ℝ) = ((arcLenQ a b : ℚ) : ℝ) := by
  rw [arcLen, arcLenQ, Rat.cast_fract]
  push_cast
  rfl

/-- The certificate transfers to real angles: `InArcQ` implies `InArc`. -/
theorem InArcQ.to_real {x a b : ℚ} (h : InArcQ x a b) : InArc (x : ℝ) (a : ℝ) (b : ℝ) := by
  rw [InArcQ] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · exact_mod_cast h1
  · rw [arcLenQ_cast]
    exact_mod_cast h2

/-- The integral translation lemma behind `Tq_iterate_add_int`, on a single angle. -/
theorem Tq_intCast (q : ℚ) (m : ℤ) : Tq (q + m) = Tq q := Tq_add_int q m

/-- An integer multiple of `Int.fract x` has the same fractional part as the integer multiple of
`x`. -/
theorem fract_mul_intCast {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (m : ℤ) (x : R) : Int.fract (m * x) = Int.fract (m * Int.fract x) := by
  rw [Int.fract_eq_fract]
  refine ⟨m * ⌊x⌋, ?_⟩
  rw [← mul_sub, Int.self_sub_fract]
  push_cast
  ring

/-- The general iterate formula for the angle-doubling map on `ℚ`. -/
theorem Tq_iterate_eq (n : ℕ) (q : ℚ) :
    Tq^[n + 1] q = Int.fract (((-2 : ℤ) ^ (n + 1) : ℚ) * q) := by
  induction n with
  | zero => rw [Function.iterate_one, Tq]; norm_num
  | succ n ih =>
    have h : Int.fract (-2 * Int.fract (((-2 : ℤ) ^ (n + 1) : ℚ) * q))
        = Int.fract (-2 * (((-2 : ℤ) ^ (n + 1) : ℚ) * q)) :=
      (fract_mul_intCast (-2) (((-2 : ℤ) ^ (n + 1) : ℚ) * q)).symm
    rw [Function.iterate_succ_apply' Tq (n + 1) q, ih, Tq, h]
    congr 1
    rw [pow_succ]
    push_cast
    ring

end Work.ELPull
