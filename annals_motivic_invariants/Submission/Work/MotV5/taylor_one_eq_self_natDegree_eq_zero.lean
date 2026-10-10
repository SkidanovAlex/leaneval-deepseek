import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Polynomials of degree `≤ 4` over a field of characteristic `5` fixed by `X ↦ X + 1`

`Polynomial.taylor 1 r` is the polynomial `r (X + 1)`, so `taylor 1 r = r` says that `r` is
invariant under the translation `X ↦ X + 1`.  In characteristic `5` the invariants of this
translation on `K[X]` are `K[X ^ 5 - X]`, so an invariant polynomial of degree `≤ 4` is
constant; that is the lemma below.

The proof only needs the degree-`(d - 1)` coefficient of the identity `taylor 1 r = r`, where
`d = r.natDegree`: by `Polynomial.taylor_coeff` it is `(hasseDeriv (d - 1) r).eval 1`, and
`hasseDeriv (d - 1) r` is a linear polynomial whose `X`-coefficient is `d * leadingCoeff r`.
Equality with `r.coeff (d - 1)` therefore forces `d * leadingCoeff r = 0`, which is impossible
since `0 < d ≤ 4 < 5 = char K` and `r ≠ 0`.
-/

namespace Work.MotV5

theorem taylor_one_eq_self_natDegree_eq_zero {K : Type*} [Field K] [CharP K 5]
    (r : Polynomial K) (h4 : r.natDegree ≤ 4) (h : Polynomial.taylor 1 r = r) :
    r.natDegree = 0 := by
  by_contra hne
  -- `r` has degree `d ≥ 1`, hence is nonzero.
  have hdpos : 1 ≤ r.natDegree := Nat.one_le_iff_ne_zero.mpr hne
  have hrne : r ≠ 0 := fun h0 => hne (by rw [h0, Polynomial.natDegree_zero])
  -- The coefficient of `X ^ (d - 1)` in `taylor 1 r = r` is `(hasseDeriv (d - 1) r).eval 1`.
  have hcoeff : (Polynomial.hasseDeriv (r.natDegree - 1) r).eval 1
      = r.coeff (r.natDegree - 1) := by
    have hh := congrArg (fun p : Polynomial K => p.coeff (r.natDegree - 1)) h
    rwa [Polynomial.taylor_coeff] at hh
  -- `hasseDeriv (d - 1) r` is linear.
  have hnd : (Polynomial.hasseDeriv (r.natDegree - 1) r).natDegree ≤ 1 := by
    have h1 := Polynomial.natDegree_hasseDeriv_le r (r.natDegree - 1)
    rwa [Nat.sub_sub_self hdpos] at h1
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hnd
  have hd1 : 1 + (r.natDegree - 1) = r.natDegree := by omega
  have hchoose : r.natDegree.choose (r.natDegree - 1) = r.natDegree := by
    have hh := Nat.choose_succ_self_right (r.natDegree - 1)
    rwa [Nat.sub_add_cancel hdpos] at hh
  -- Its coefficients are `r.coeff (d - 1)` (degree `0`) and `d * leadingCoeff r` (degree `1`).
  have hc1 : (Polynomial.hasseDeriv (r.natDegree - 1) r).coeff 1
      = ((r.natDegree : ℕ) : K) * r.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff (r.natDegree - 1) r 1, hd1, hchoose,
      Polynomial.coeff_natDegree]
  have hc0 : (Polynomial.hasseDeriv (r.natDegree - 1) r).coeff 0
      = r.coeff (r.natDegree - 1) := by
    rw [Polynomial.hasseDeriv_coeff (r.natDegree - 1) r 0]
    simp
  have heval : (Polynomial.hasseDeriv (r.natDegree - 1) r).eval 1
      = ((r.natDegree : ℕ) : K) * r.leadingCoeff + r.coeff (r.natDegree - 1) := by
    conv_lhs => rw [hlin]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hc1, hc0, mul_one]
  -- Hence `d * leadingCoeff r = 0`.
  have hmain : ((r.natDegree : ℕ) : K) * r.leadingCoeff = 0 := by
    have h2 : ((r.natDegree : ℕ) : K) * r.leadingCoeff + r.coeff (r.natDegree - 1)
        - r.coeff (r.natDegree - 1) = 0 := sub_eq_zero.mpr (by rw [← heval]; exact hcoeff)
    simpa using h2
  -- Both factors are nonzero: `d < 5 = char K` and `r ≠ 0`.
  have hdcast : ((r.natDegree : ℕ) : K) ≠ 0 := by
    intro hc
    have h5 : 5 ∣ r.natDegree := (CharP.cast_eq_zero_iff K 5 r.natDegree).mp hc
    omega
  have hlc : r.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hrne
  exact (mul_ne_zero hdcast hlc) hmain

end Work.MotV5
