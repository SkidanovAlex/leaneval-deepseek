import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.a0dpow_comp_a0pow` — the Wick (normal-ordering) identity for `a₀†, a₀`

On the algebraic core `FockCore E = ℕ →₀ E` of the Fock space `Fock E = ⨁ₙ E`
(`Defs.lean`) the condensate creation and annihilation operators satisfy the
canonical commutation relation `a₀ a₀† = a₀† a₀ + 1` (`Defs.ccr`).  This file
proves the complete normal-ordering expansion of the anti-normal monomial
`(a₀†)^q a₀^p`:

    (a₀†)^q a₀^p = ∑_{k=0}^{p} (-1)^k k! C(p,k) C(q,k) · a₀^{p-k} (a₀†)^{q-k},

i.e. the operator identity of `theorem a0dpow_comp_a0pow` below.  It is the
finite-`p,q` form of the Wick theorem for a single mode, and the identity that
converts FS's anti-normal monomials `monoOp p q B = a₀^p (a₀†)^q ⊗ B`
(`Defs.monoOp`) into normally ordered ones.

## How it is proved

Fix a `ℂ`-algebra `R` (below: the endomorphism algebra
`FockCore E →ₗ[ℂ] FockCore E`, whose multiplication is composition, see
`mul_eq_comp_aux`), and let `x y : R` satisfy `x * y = y * x + 1`
(here `x = a₀`, `y = a₀†`).  The whole content is ring-theoretic and is proved
in the abstract form `wick`:

    y^q * x^p = ∑ k ∈ range(p+1), wickCoeff p q k • (x^(p-k) * y^(q-k)).

The proof is an induction on `p`.  Writing `S(p,q)` for the right-hand side and
using `y^q x^{p+1} = (y^q x^p) x`, the induction hypothesis gives

    y^q x^{p+1} = ∑_{k=0}^{p} wickCoeff p q k · x^{p-k} y^{q-k} x,

and the commutation relation `pow_mul_left` (`y^m x = x y^m - m y^{m-1}`, the
mirror of `a0d_comp_a0pow`) pushes the trailing `x` to the left:

    x^{p-k} y^{q-k} x = x^{p+1-k} y^{q-k} - (q-k) · x^{p-k} y^{q-k-1}.

Shifting the index of the second sum by one (`Finset.sum_range_succ'`) turns
the statement into the binomial identity

    wickCoeff (p+1) q (k+1) = wickCoeff p q (k+1) - wickCoeff p q k * (q-k),

i.e. `(p+1 choose k+1) = (p choose k+1) + (p choose k)` combined with
`(q choose k+1)(k+1) = (q choose k)(q-k)` (`Nat.choose_succ_right_eq`); this is
`wc_succ_p`, closed by `linear_combination`.
-/

noncomputable section

namespace Work.BoseB4

set_option autoImplicit false

/-! ## The Wick coefficient and the abstract normal-ordering identity -/

/-- The coefficient `(-1)^k k! C(p,k) C(q,k)` of the `k`-th term in the
normal-ordering expansion of `(a₀†)^q a₀^p`. -/
private def wickCoeff (p q k : ℕ) : ℂ :=
  ((-1 : ℂ)) ^ k * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
    * ((q.choose k : ℕ) : ℂ)

/-- Transfer of the binomial/factorial identity `C(q,k)(q-k) = C(q,k+1)(k+1)`
to `ℂ`. -/
private lemma cast_choose_succ_right (q k : ℕ) :
    ((q.choose k : ℕ) : ℂ) * ((q - k : ℕ) : ℂ)
      = ((q.choose (k + 1) : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) := by
  rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_succ_right_eq]

/-- Transfer of Pascal's rule `C(p+1,k+1) = C(p,k) + C(p,k+1)` to `ℂ`. -/
private lemma cast_choose_succ_succ (p k : ℕ) :
    (((p + 1).choose (k + 1) : ℕ) : ℂ)
      = ((p.choose k : ℕ) : ℂ) + ((p.choose (k + 1) : ℕ) : ℂ) := by
  rw [Nat.choose_succ_succ']; push_cast; ring

/-- Transfer of the factorial recursion `(k+1)! = (k+1) k!` to `ℂ`. -/
private lemma cast_factorial_succ (k : ℕ) :
    (((k + 1).factorial : ℕ) : ℂ) = ((k + 1 : ℕ) : ℂ) * ((k.factorial : ℕ) : ℂ) := by
  rw [Nat.factorial_succ]; push_cast; ring

/-- **The coefficient recurrence in `p`** behind the induction:

    wickCoeff (p+1) q (k+1) = wickCoeff p q (k+1) - wickCoeff p q k * (q-k). -/
private lemma wc_succ_p (p q k : ℕ) :
    wickCoeff (p + 1) q (k + 1) = wickCoeff p q (k + 1) - wickCoeff p q k * ((q - k : ℕ) : ℂ) := by
  have hq := cast_choose_succ_right q k
  simp only [wickCoeff, cast_choose_succ_succ, cast_factorial_succ, pow_succ]
  linear_combination ((-1 : ℂ) ^ k * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)) * hq

/-- **`x y^{k+1} = y^{k+1} x + (k+1) y^k`** in any ring, given `x y = y x + 1`. -/
private lemma ring_pow_mul_left {R : Type*} [Ring R] {x y : R} (h : x * y = y * x + 1) (k : ℕ) :
    x * y ^ (k + 1) = y ^ (k + 1) * x + (k + 1 : R) * y ^ k := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h1 : x * y ^ (k + 1 + 1) = (x * y ^ (k + 1)) * y := by rw [pow_succ, ← mul_assoc]
    have hkey : (k + 1 : R) * y ^ k * y = (k + 1 : R) * y ^ (k + 1) := by
      rw [mul_assoc, pow_succ]
    rw [h1, ih, add_mul, hkey]
    have hR : y ^ (k + 1) * x * y = y ^ (k + 1 + 1) * x + y ^ (k + 1) := by
      rw [mul_assoc, h, mul_add, mul_one, ← mul_assoc, ← pow_succ]
    rw [hR]
    push_cast
    noncomm_ring

/-- **`y^n x = x y^n - n · y^{n-1}`**, the `ℂ`-scalar form of `ring_pow_mul_left`
(the convention `y^{n-1} = 1` at `n = 0`, where the scalar vanishes). -/
private lemma pow_mul_left {R : Type*} [Ring R] [Algebra ℂ R] {x y : R}
    (h : x * y = y * x + 1) (n : ℕ) :
    y ^ n * x = x * y ^ n - ((n : ℕ) : ℂ) • y ^ (n - 1) := by
  rcases n with _ | m
  · simp
  · rw [Nat.add_sub_cancel, eq_sub_iff_add_eq, ring_pow_mul_left h m]
    congr 1
    rw [Algebra.smul_def, map_natCast]
    push_cast
    noncomm_ring

/-- **The Wick / normal-ordering identity in an abstract `ℂ`-algebra.**  If
`x * y = y * x + 1`, then `y^q x^p = ∑ k ∈ range(p+1), wickCoeff p q k • (x^{p-k} y^{q-k})`. -/
private lemma wick {R : Type*} [Ring R] [Algebra ℂ R] (x y : R) (h : x * y = y * x + 1) :
    ∀ p q : ℕ, y ^ q * x ^ p
      = ∑ k ∈ Finset.range (p + 1), wickCoeff p q k • (x ^ (p - k) * y ^ (q - k)) := by
  intro p
  induction p with
  | zero =>
    intro q
    rw [pow_zero, mul_one, Nat.zero_add, Finset.sum_range_one]
    simp [wickCoeff]
  | succ p ih =>
    intro q
    rw [pow_succ, ← mul_assoc, ih q, Finset.sum_mul]
    have hterm : ∀ k ∈ Finset.range (p + 1),
        (wickCoeff p q k • (x ^ (p - k) * y ^ (q - k))) * x
          = wickCoeff p q k • (x ^ (p + 1 - k) * y ^ (q - k))
            - (wickCoeff p q k * ((q - k : ℕ) : ℂ)) • (x ^ (p - k) * y ^ (q - k - 1)) := by
      intro k hk
      have hk' : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Algebra.smul_mul_assoc]
      have hinner : (x ^ (p - k) * y ^ (q - k)) * x
          = x ^ (p + 1 - k) * y ^ (q - k)
            - ((q - k : ℕ) : ℂ) • (x ^ (p - k) * y ^ (q - k - 1)) := by
        have hexp : p - k + 1 = p + 1 - k := by omega
        rw [mul_assoc, pow_mul_left h (q - k), mul_sub, ← mul_assoc, ← pow_succ, hexp,
          Algebra.mul_smul_comm]
      rw [hinner, smul_sub, smul_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have hc1 : wickCoeff p q (p + 1) = 0 := by simp [wickCoeff]
    have hA : (∑ k ∈ Finset.range (p + 1), wickCoeff p q k • (x ^ (p + 1 - k) * y ^ (q - k)))
        = ∑ j ∈ Finset.range (p + 1 + 1), wickCoeff p q j • (x ^ (p + 1 - j) * y ^ (q - j)) := by
      conv_rhs => rw [Finset.sum_range_succ]
      rw [hc1, zero_smul, add_zero]
    have hsplit : ∀ r : ℕ,
        (∑ j ∈ Finset.range (p + 1 + 1), wickCoeff r q j • (x ^ (p + 1 - j) * y ^ (q - j)))
          = wickCoeff r q 0 • (x ^ (p + 1) * y ^ q)
            + ∑ k ∈ Finset.range (p + 1), wickCoeff r q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)) := by
      intro r
      rw [Finset.sum_range_succ', add_comm,
        show wickCoeff r q 0 • (x ^ (p + 1 - 0) * y ^ (q - 0))
              = wickCoeff r q 0 • (x ^ (p + 1) * y ^ q) by
          rw [Nat.sub_zero, Nat.sub_zero]]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      have e1 : p + 1 - (k + 1) = p - k := by omega
      have e2 : q - (k + 1) = q - k - 1 := by omega
      rw [e1, e2]
    have hc0 : wickCoeff p q 0 = wickCoeff (p + 1) q 0 := by simp [wickCoeff]
    have hAsplit : (∑ k ∈ Finset.range (p + 1), wickCoeff p q k • (x ^ (p + 1 - k) * y ^ (q - k)))
        = wickCoeff (p + 1) q 0 • (x ^ (p + 1) * y ^ q)
          + ∑ k ∈ Finset.range (p + 1), wickCoeff p q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)) := by
      rw [hA, hsplit p, hc0]
    have key : (∑ k ∈ Finset.range (p + 1), wickCoeff p q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)))
          - (∑ k ∈ Finset.range (p + 1),
              (wickCoeff p q k * ((q - k : ℕ) : ℂ)) • (x ^ (p - k) * y ^ (q - k - 1)))
        = ∑ k ∈ Finset.range (p + 1),
            wickCoeff (p + 1) q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← sub_smul, wc_succ_p]
    calc (∑ k ∈ Finset.range (p + 1), wickCoeff p q k • (x ^ (p + 1 - k) * y ^ (q - k)))
            - (∑ k ∈ Finset.range (p + 1),
                (wickCoeff p q k * ((q - k : ℕ) : ℂ)) • (x ^ (p - k) * y ^ (q - k - 1)))
        = (wickCoeff (p + 1) q 0 • (x ^ (p + 1) * y ^ q)
            + ∑ k ∈ Finset.range (p + 1),
                wickCoeff p q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)))
            - (∑ k ∈ Finset.range (p + 1),
                (wickCoeff p q k * ((q - k : ℕ) : ℂ)) • (x ^ (p - k) * y ^ (q - k - 1))) := by
          rw [hAsplit]
      _ = wickCoeff (p + 1) q 0 • (x ^ (p + 1) * y ^ q)
            + ((∑ k ∈ Finset.range (p + 1),
                  wickCoeff p q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)))
              - (∑ k ∈ Finset.range (p + 1),
                  (wickCoeff p q k * ((q - k : ℕ) : ℂ)) • (x ^ (p - k) * y ^ (q - k - 1)))) := by
          abel
      _ = wickCoeff (p + 1) q 0 • (x ^ (p + 1) * y ^ q)
            + ∑ k ∈ Finset.range (p + 1),
                wickCoeff (p + 1) q (k + 1) • (x ^ (p - k) * y ^ (q - k - 1)) := by
          rw [key]
      _ = ∑ j ∈ Finset.range (p + 1 + 1),
            wickCoeff (p + 1) q j • (x ^ (p + 1 - j) * y ^ (q - j)) :=
          (hsplit (p + 1)).symm

/-! ## The endomorphism algebra of the core -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- In the endomorphism ring `FockCore E →ₗ[ℂ] FockCore E` the multiplication is
composition. -/
private lemma mul_eq_comp_aux (f g : FockCore E →ₗ[ℂ] FockCore E) : f * g = f.comp g := by
  ext x
  simp [Module.End.mul_apply]

/-- `a0pow k` is the `k`-th ring power of `a0`. -/
private lemma a0pow_eq_ringpow (k : ℕ) :
    a0pow (E := E) k = (a0 (E := E) : FockCore E →ₗ[ℂ] FockCore E) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [a0pow_succ, ih, ← mul_eq_comp_aux, pow_succ]

/-- `a0dpow k` is the `k`-th ring power of `a0d`. -/
private lemma a0dpow_eq_ringpow (k : ℕ) :
    a0dpow (E := E) k = (a0d (E := E) : FockCore E →ₗ[ℂ] FockCore E) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [a0dpow_succ, ih, ← mul_eq_comp_aux, pow_succ]

/-! ## The target theorem -/

/-- **Wick's identity for the condensate mode.**  The anti-normal monomial
`(a₀†)^q a₀^p` expanded in normally ordered form,

    (a₀†)^q a₀^p = ∑_{k=0}^{p} (-1)^k k! C(p,k) C(q,k) · a₀^{p-k} (a₀†)^{q-k}. -/
theorem a0dpow_comp_a0pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (p q : ℕ) :
    ((Work.BoseB4.a0dpow q : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E)).comp
        (Work.BoseB4.a0pow p)
      = ∑ k ∈ Finset.range (p + 1),
          (((-1 : ℂ) ^ k) * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
              * ((q.choose k : ℕ) : ℂ))
            • ((Work.BoseB4.a0pow (p - k)).comp (Work.BoseB4.a0dpow (q - k))) := by
  have h : (a0 : FockCore E →ₗ[ℂ] FockCore E) * a0d = a0d * a0 + 1 := by
    rw [mul_eq_comp_aux, mul_eq_comp_aux]
    exact ccr
  rw [← mul_eq_comp_aux (a0dpow q) (a0pow p), a0dpow_eq_ringpow q, a0pow_eq_ringpow p,
    wick (a0 : FockCore E →ₗ[ℂ] FockCore E) a0d h p q]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_eq_comp_aux, a0pow_eq_ringpow (p - k), a0dpow_eq_ringpow (q - k)]
  simp only [wickCoeff]

end Work.BoseB4
