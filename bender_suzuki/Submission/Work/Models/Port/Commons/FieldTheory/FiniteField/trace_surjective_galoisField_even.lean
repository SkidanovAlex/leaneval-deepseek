import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Surjectivity of the relative trace `x + x ^ (2 ^ n)` on `GaloisField 2 (2 * n)`

Let `q = 2 ^ n` and `F = GaloisField 2 (2 * n)`, so `Nat.card F = q ^ 2`.  The map

`T : F → F,  x ↦ x + x ^ q`

is the relative trace of the quadratic extension `F / GF(q)`.  Its image is exactly the
fixed field `K = {y : F // y ^ q = y}` of the order-two automorphism `x ↦ x ^ q`.  We
prove that `T` is surjective onto `K`: for every `y` with `y ^ q = y` there is `x` with
`x + x ^ q = y`.

The proof is elementary and explicit.  Since `X ^ q - X` is a nonzero polynomial of
degree `q = 2 ^ n`, the set `K` of its roots has at most `q` elements, while
`Nat.card F = q ^ 2 > q`.  Hence there is `θ : F` with `θ ^ q ≠ θ`.  For such `θ` put
`c = θ + θ ^ q`; then `c ≠ 0` and `c ^ q = c`, and the element `x = (y / c) * θ`
satisfies `x + x ^ q = (y / c) * (θ + θ ^ q) = y`.
-/

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.FiniteField

theorem trace_surjective_galoisField_even (n : ℕ) (hn : 1 ≤ n) (y : GaloisField 2 (2 * n))
    (hy : y ^ (2 ^ n) = y) : ∃ x : GaloisField 2 (2 * n), x + x ^ (2 ^ n) = y := by
  classical
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  set q : ℕ := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : Nat.card (GaloisField 2 (2 * n)) = q ^ 2 := by
    rw [GaloisField.card (p := 2) (n := 2 * n) (by omega), hq, ← pow_mul]
    congr 1
    omega
  -- The fixed points of `x ↦ x ^ q` are the roots of `X ^ q - X`, whence at most `q`.
  have hSle : (Finset.univ.filter (fun x : GaloisField 2 (2 * n) => x ^ q = x)).card ≤ q := by
    set S : Finset (GaloisField 2 (2 * n)) := Finset.univ.filter (fun x => x ^ q = x) with hS
    set p : Polynomial (GaloisField 2 (2 * n)) := Polynomial.X ^ q - Polynomial.X with hp
    have hp_ne : p ≠ 0 := by
      intro h
      have h1 : (Polynomial.X ^ q : Polynomial (GaloisField 2 (2 * n))) = Polynomial.X := by
        have h' := h; rw [hp] at h'; exact sub_eq_zero.mp h'
      have hdeg := congrArg Polynomial.natDegree h1
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hdeg
      omega
    have hpdeg : p.natDegree = q := by
      rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow q
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; exact hq2
    calc S.card ≤ p.roots.toFinset.card := by
            apply Finset.card_le_card
            intro x hx
            rw [hS] at hx
            obtain ⟨_, hxq⟩ := Finset.mem_filter.mp hx
            rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def, hp]
            rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
            simp [hxq]
      _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = q := hpdeg
  -- Hence `x ↦ x ^ q` is not the identity, and we may pick `θ` with `θ ^ q ≠ θ`.
  obtain ⟨θ, hθ⟩ : ∃ θ : GaloisField 2 (2 * n), θ ^ q ≠ θ := by
    by_contra hcon
    push Not at hcon
    have hSuniv : (Finset.univ.filter (fun x : GaloisField 2 (2 * n) => x ^ q = x)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hcon x⟩
    have hSq : (Finset.univ.filter (fun x : GaloisField 2 (2 * n) => x ^ q = x)).card = q ^ 2 := by
      rw [hSuniv, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    have hlt : q < q ^ 2 := by nlinarith [hq2]
    omega
  set c : GaloisField 2 (2 * n) := θ + θ ^ q with hc
  have hθθ : θ + θ = 0 := CharTwo.add_self_eq_zero θ
  have hc_ne : c ≠ 0 := by
    intro h0
    apply hθ
    have h1 : θ + θ ^ q = θ + θ := by rw [hc] at h0; rw [h0, hθθ]
    exact add_left_cancel h1
  have hsum : (θ + θ ^ q) ^ q = θ ^ q + (θ ^ q) ^ q := by
    rw [hq]
    rw [add_pow_char_pow θ (θ ^ q) 2 n]
  have hpow : (θ ^ q) ^ q = θ := by
    rw [← pow_mul]
    rw [show q * q = Fintype.card (GaloisField 2 (2 * n)) by
      rw [← Nat.card_eq_fintype_card, hcard]; ring]
    exact FiniteField.pow_card θ
  have hcq : c ^ q = c := by
    rw [hc, hsum, hpow, add_comm]
  refine ⟨(y * c⁻¹) * θ, ?_⟩
  have h1 : ((y * c⁻¹) * θ) ^ q = (y * c⁻¹) * θ ^ q := by
    rw [mul_pow]
    congr 1
    rw [mul_pow, hy, inv_pow, hcq]
  rw [h1, ← mul_add, ← hc, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]

end Commons.FieldTheory.FiniteField