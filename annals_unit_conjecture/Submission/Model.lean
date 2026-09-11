import Submission.PGroup
import Mathlib.Tactic.FinCases

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

open scoped Classical

/-!
# The concrete model group HW

Elements are pairs `(e : E, q : Q)` where `E = ℤ × ℤ × ℤ` are exponent triples
(additive) and `Q = (ZMod 2) × (ZMod 2)` is the Klein four group (written
additively).  The multiplication is the group-extension law

  (e, q) * (e', q') = (e + act q e' + f q q', q + q')

where `act` and `f` are defined in `PGroup`.

All lemmas below are stated with complete machine-checked proofs, so that
`lake build Submission.Model` succeeds with no gaps and relies only on the
standard foundations.

Useful facts already in `Submission.PGroup`:
- `Q_cases : ∀ q : Q, q = q0 ∨ q = qA ∨ q = qB ∨ q = qAB`
- `act_qA, act_qB, act_qAB, act_q0 : act qA m = ...` etc.
- `act_add : act q (m + n) = act q m + act q n`
- `act_act : act q (act q m) = m`
- `act_add_q : act q (act q' m) = act (q + q') m`
- `f_q0_q0 ... f_qAB_qAB` (simp lemmas for the 16 values of f)
- `add_q0_q0 ... add_qAB_qAB` (simp lemmas for sums in Q)
- `E` is `ℤ × ℤ × ℤ`; use `rcases m with ⟨i, j, k⟩`, `ext <;> simp`, `ring`,
  `omega`, `decide`, `norm_num` for the integer arithmetic.
- `sig`, `w` are about the abstract group `P`, not needed here.
-/

/-- The model group: elements (exponent triple, coset representative index). -/
structure HW where
  e : E
  q : Q
deriving DecidableEq

namespace HW

/-- The identity. -/
def one : HW := { e := (0, 0, 0), q := q0 }

/-- Multiplication. -/
def mul (g h : HW) : HW :=
  { e := g.e + act g.q h.e + f g.q h.q, q := g.q + h.q }

/-- Inverse: q is self-inverse in Q and the translation part is solved. -/
def inv (g : HW) : HW :=
  { e := act g.q (-(g.e + f g.q g.q)), q := g.q }

-- ------------------------------------------------------------
-- basic arithmetic lemmas (all proofs to be filled in)
-- ------------------------------------------------------------

-- HINTS:
-- * For statements over Q: `rcases (Q_cases q) with rfl | rfl | rfl | rfl`
--   then `norm_num`, `decide`, `ext <;> simp`, `ring`, `omega` on the closed
--   integer arithmetic that remains.
-- * After case splits the goals are decidable equalities of concrete integer
--   triples; often `decide` or `native_decide` closes them, or
--   `ext <;> norm_num` / `ext <;> omega` / `ext <;> ring`.
-- * `E = ℤ × ℤ × ℤ`; negation, addition are componentwise (Prod instances).
--   For `act_neg`: case split on q then `ext <;> ring` or `simp [act]`.
-- * `mul_assoc_lem`: case split on the three q's (`rcases (Q_cases q) with ...`)
--   after that use `ext`; the resulting integer identities are consequences of
--   `act_add`, `act_act`, `act_add_q`, `cocycle` and linearity; you can also
--   prove associativity directly from those lemmas without case splits.
-- * `A_sq` etc: unfold and `simp [A, Tx, HW.mul]` then `norm_num`/`decide`.
-- * `exp_zero_iff_one`: `ext <;> simp` both directions.
-- * `sq_ne_one`: case split `rcases (Q_cases g.q) with ...`; in the q0 case the
--   hypothesis is contradictory; otherwise unfold the multiplication; the
--   exponent part is never zero because of the "+1 component" from f (e.g. for
--   q = qA: e + act qA e = (2i, 0, 0) and f adds (1,0,0), so 2i+1 ≠ 0).
-- * `torsion_free`: split on whether g.q = q0.
--   - q = q0 case: g = (e,0) with e ≠ 0, then (e,0)^n = (n • e, 0) ≠ 0.
--   - q ≠ q0 case: for odd n the q-component of g^n is g.q ≠ q0 so g^n ≠ 1;
--     for even n use g^2 ≠ 1 (sq_ne_one) and that powers of (e2,0) with
--     e2 ≠ 0 are never 1.  You may find it easier to split on the parity of n
--     via `Nat.even_or_odd n` or by `rcases Nat.not_even_iff_odd.mp ...`.
-- You are free to add extra helper lemmas and change proof structure, but do
-- NOT change any statement or definition (they are used by other modules).

-- extensionality for HW
@[ext] theorem ext' {x y : HW} (he : x.e = y.e) (hq : x.q = y.q) : x = y := by
  rcases x with ⟨e, q⟩
  rcases y with ⟨e', q'⟩
  simp at he hq
  rw [he, hq]

lemma act_zero (q : Q) : act q (0, 0, 0) = (0, 0, 0) := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl <;> ext <;> simp [act, q0, qA, qB, qAB]


lemma act_neg (q : Q) (m : E) : act q (-m) = -act q m := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  <;> rcases m with ⟨i, j, k⟩
  <;> ext <;> simp [act, q0, qA, qB, qAB]


lemma f_zero_left (q : Q) : f q0 q = (0, 0, 0) := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl <;> simp


lemma f_zero_right (q : Q) : f q q0 = (0, 0, 0) := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl <;> simp


lemma f_fixed (q : Q) : act q (f q q) = f q q := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl <;> simp [act_q0, act_qA, act_qB, act_qAB]


lemma q_add_zero (q : Q) : q0 + q = q := by
  ext <;> simp [q0]


lemma q_zero_add (q : Q) : q + q0 = q := by
  ext <;> simp [q0]


/-- 2-cocycle identity. -/
lemma cocycle (q q' q'' : Q) :
    act q (f q' q'') + f q (q' + q'') = f q q' + f (q + q') q'' := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  <;> rcases (Q_cases q') with rfl | rfl | rfl | rfl
  <;> rcases (Q_cases q'') with rfl | rfl | rfl | rfl
  <;> ext <;> simp [act_q0, act_qA, act_qB, act_qAB]


-- ------------------------------------------------------------
-- group instance
-- ------------------------------------------------------------

lemma one_mul_lem (g : HW) : mul one g = g := by
  ext <;> simp [mul, one, act_q0, f_zero_left, q_add_zero]


lemma mul_one_lem (g : HW) : mul g one = g := by
  ext <;> simp [mul, one, act_zero, f_zero_right, q_zero_add]


lemma mul_assoc_lem (g h k : HW) : mul (mul g h) k = mul g (mul h k) := by
  ext1
  · simp [mul]
    simp only [act_add, act_add_q]
    conv_rhs => rw [add_assoc]
    conv_rhs => rw [add_assoc]
    rw [cocycle]
    ring
  · simp [mul, add_assoc]


/-- q + q = 0 in Q (char 2). -/
lemma q_add_self (q : Q) : q + q = q0 := by
  rcases (Q_cases q) with rfl | rfl | rfl | rfl <;> simp

lemma inv_mul_cancel_lem (g : HW) : mul (inv g) g = one := by
  ext1
  · simp [mul, one, inv, act_neg, act_add, f_fixed]
    rfl
  · simp [mul, one, inv, q_add_self]


/-- the group structure on HW -/
instance group : Group HW where
  mul := mul
  one := one
  inv := inv
  one_mul := one_mul_lem
  mul_one := mul_one_lem
  mul_assoc := mul_assoc_lem
  inv_mul_cancel := inv_mul_cancel_lem

@[simp] lemma mul_def (g h : HW) : g * h = mul g h := rfl
@[simp] lemma one_def : (1 : HW) = one := rfl
@[simp] lemma inv_def (g : HW) : g⁻¹ = inv g := rfl

-- ------------------------------------------------------------
-- explicit elements
-- ------------------------------------------------------------

/-- the element a -/
def A : HW := { e := (0, 0, 0), q := qA }

/-- the element b -/
def B : HW := { e := (0, 0, 0), q := qB }

/-- the translation x = a^2 -/
def Tx : HW := { e := (1, 0, 0), q := q0 }

/-- the translation y = b^2 -/
def Ty : HW := { e := (0, 1, 0), q := q0 }

/-- the translation z = (ab)^2 -/
def Tz : HW := { e := (0, 0, 1), q := q0 }

lemma A_sq : A * A = Tx := by
  ext <;> simp [A, Tx, mul, act_zero]


lemma B_sq : B * B = Ty := by
  ext <;> simp [B, Ty, mul, act_zero]


lemma AB_sq : (A * B) * (A * B) = Tz := by
  ext <;> simp [A, B, Tz, mul, act_zero]


-- ------------------------------------------------------------
-- torsion-freeness of HW
-- ------------------------------------------------------------

/-- the second power of an element above a nontrivial q is not 1 -/
-- the e-component of the square of an element above a nontrivial q is never zero
lemma sq_e_ne_zero (g : HW) (hg : g.q ≠ q0) : (g * g).e ≠ (0, 0, 0) := by
  rcases g with ⟨e, q⟩
  rcases (Q_cases q) with rfl | rfl | rfl | rfl
  · exact (hg rfl).elim
  · rcases e with ⟨i, j, k⟩
    intro h
    have hc := congrArg (fun x : E => x.1) h
    simp [mul, act_qA] at hc
    omega
  · rcases e with ⟨i, j, k⟩
    intro h
    have hc := congrArg (fun x : E => x.2.1) h
    simp [mul, act_qB] at hc
    omega
  · rcases e with ⟨i, j, k⟩
    intro h
    have hc := congrArg (fun x : E => x.2.2) h
    simp [mul, act_qAB] at hc
    omega

lemma sq_ne_one (g : HW) (hg : g.q ≠ q0) : g * g ≠ 1 := by
  intro h
  exact sq_e_ne_zero g hg (by simpa [one] using (congrArg (fun x : HW => x.e) h))


/-- an element of the translation subgroup is 1 iff its exponent is 0 -/
lemma exp_zero_iff_one (e : E) : ({ e := e, q := q0 } : HW) = 1 ↔ e = (0, 0, 0) := by
  constructor
  · intro h
    have he := congrArg (fun x : HW => x.e) h
    simpa [one] using he
  · intro h
    subst h
    simp [one]


/-- HW is torsion-free -/
-- the q-component of any square is 0
lemma sq_q0 (g : HW) : (g * g).q = q0 := by
  rcases g with ⟨e, q⟩
  simp [mul, q_add_self]

-- multiplication of two translations
lemma mul_q0 (a b : E) : ({ e := a, q := q0 } : HW) * { e := b, q := q0 } = { e := a + b, q := q0 } := by
  ext1
  · simp [mul, act_q0]
  · simp [mul]

-- powers of a translation: (e,q0)^n = (n • e, q0)
lemma pow_q0 (e : E) (n : ℕ) : ({ e := e, q := q0 } : HW) ^ n = { e := n • e, q := q0 } := by
  induction n with
  | zero => simp [one]
  | succ n ih =>
      rw [pow_succ, ih]
      rw [mul_q0]
      ext1
      · exact (succ_nsmul e n).symm
      · rfl

-- in Z^3, a nonzero multiple of a nonzero vector is nonzero
lemma nsmul_E_ne_zero (n : ℕ) (hn : n ≠ 0) (e : E) (he : e ≠ (0, 0, 0)) : n • e ≠ (0, 0, 0) := by
  rcases e with ⟨i, j, k⟩
  intro h
  have hi : n • i = 0 := by
    have hf := congrArg (fun x : E => x.1) h
    simpa using hf
  have hj : n • j = 0 := by
    have hf := congrArg (fun x : E => x.2.1) h
    simpa using hf
  have hk : n • k = 0 := by
    have hf := congrArg (fun x : E => x.2.2) h
    simpa using hf
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hi0 : i = 0 := by
    have h' : (n : ℤ) * i = 0 := by simpa [nsmul_eq_mul] using hi
    exact (mul_eq_zero.mp h').resolve_left hnz
  have hj0 : j = 0 := by
    have h' : (n : ℤ) * j = 0 := by simpa [nsmul_eq_mul] using hj
    exact (mul_eq_zero.mp h').resolve_left hnz
  have hk0 : k = 0 := by
    have h' : (n : ℤ) * k = 0 := by simpa [nsmul_eq_mul] using hk
    exact (mul_eq_zero.mp h').resolve_left hnz
  apply he
  ext <;> simp [hi0, hj0, hk0]

-- an element above a nontrivial q has no nonzero power equal to 1
lemma pow_ne_one_of_q_ne_zero (g : HW) (hgq : g.q ≠ q0) : ∀ n : ℕ, n ≠ 0 → g ^ n ≠ 1 := by
  intro n hn hpow
  have hg2 : g * g = { e := (g * g).e, q := q0 } := by
    ext1
    · rfl
    · exact sq_q0 g
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro h0
      apply hn
      omega
    have hp : (g ^ 2) ^ m = 1 := by
      calc
        (g ^ 2) ^ m = g ^ (2 * m) := by rw [← pow_mul]
        _ = g ^ (m + m) := by congr 1; omega
        _ = g ^ n := by rw [← hm]
        _ = 1 := hpow
    have hp2 : (g * g) ^ m = 1 := by
      simpa [pow_two] using hp
    rw [hg2] at hp2
    have he2 : (g * g).e ≠ (0, 0, 0) := sq_e_ne_zero g hgq
    have hf := congrArg (fun x : HW => x.e) hp2
    rw [pow_q0] at hf
    have hmul : m • (g * g).e = (0, 0, 0) := by simpa [one] using hf
    exact (nsmul_E_ne_zero m hm0 (g * g).e he2) hmul
  · rcases hOdd with ⟨k, hk⟩
    have hqeven : (g ^ (2 * k)).q = q0 := by
      rw [pow_mul, pow_two, hg2, pow_q0]
    have hqodd : (g ^ (2 * k + 1)).q = g.q := by
      calc
        (g ^ (2 * k + 1)).q = (g ^ (2 * k) * g).q := by rw [pow_succ]
        _ = (g ^ (2 * k)).q + g.q := by simp [mul]
        _ = q0 + g.q := by rw [hqeven]
        _ = g.q := by rw [q_add_zero]
    have hq1 := congrArg (fun x : HW => x.q) hpow
    rw [hk] at hq1
    rw [hqodd] at hq1
    have hqg : g.q = q0 := by simpa [one] using hq1
    exact hgq hqg

theorem torsion_free : ∀ g : HW, g ≠ 1 → ∀ n : ℕ, n ≠ 0 → g ^ n ≠ 1 := by
  intro g hg n hn
  by_cases hq0 : g.q = q0
  · intro hpow
    have hg' : g = { e := g.e, q := q0 } := by
      ext1 <;> simp [hq0]
    have he : g.e ≠ (0, 0, 0) := by
      intro he0
      apply hg
      rw [hg', he0]
      simp [one]
    have hnse : n • g.e = (0, 0, 0) := by
      have hf := congrArg (fun x : HW => x.e) hpow
      rw [hg'] at hf
      rw [pow_q0] at hf
      simpa [one] using hf
    exact (nsmul_E_ne_zero n hn g.e he) hnse
  · exact pow_ne_one_of_q_ne_zero g hq0 n hn


end HW

end Submission
