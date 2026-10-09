import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- `ExpChar K p` is a typeclass whose proofs are used by `frobenius`, `minpoly` and friends, so the
-- local `haveI` declarations below are genuine instances; the `haveILetI` style linter wrongly
-- suggests replacing them by `have`.
set_option linter.style.haveILetI false

/-!
# Perfection descends along an extension with bounded element degrees

If `L / K` is a field extension such that every element of `L` is a root of a monic polynomial
over `K` of degree at most `N`, and `L` is perfect, then `K` is perfect.

The mathematical content (in characteristic `p`) is the following: if `a ∈ K` is not a `p`-th
power in `K` and `x n` denotes a compatible system of `p ^ n`-th roots of `a` inside the perfect
field `L`, then the minimal polynomial of `x (n + 1)` over `K` has degree exactly `p ^ (n + 1)`
(see `natDegree_minpoly_eq_pow_of_pow_mem_not_mem`), contradicting the uniform bound `N` as soon
as `p ^ (N + 1) > N`.
-/

namespace NK.RamificationAudit

open Polynomial

/-- If `z` is an element of an extension `E` of `K` (of exponential characteristic `p`) such that
`z ^ p ^ (m + 1)` lies in `K` but `z ^ p ^ m` does not, then `z` has degree `p ^ (m + 1)` over `K`.

Indeed, the minimal polynomial of such a `z` is purely inseparable over `K` (it has separable degree
one), hence is of the form `X ^ p ^ e - C y` with `z ^ p ^ e = y ∈ K`; divisibility of
`X ^ p ^ (m + 1) - C c` (`z ^ p ^ (m + 1) = c ∈ K`) gives `e ≤ m + 1`, while minimality of `m`
forces `m + 1 ≤ e`. -/
lemma natDegree_minpoly_eq_pow_of_pow_mem_not_mem {K E : Type*} [Field K] [Field E] [Algebra K E]
    (p m : ℕ) [ExpChar K p] (hpp : p.Prime) {z : E}
    (hmem : z ^ p ^ (m + 1) ∈ (algebraMap K E).range)
    (hmin : z ^ p ^ m ∉ (algebraMap K E).range) :
    (minpoly K z).natDegree = p ^ (m + 1) := by
  -- `z` is purely inseparable over `K`, so its minimal polynomial has separable degree one.
  have hsep : (minpoly K z).natSepDegree = 1 :=
    (minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p).mpr ⟨m + 1, hmem⟩
  obtain ⟨e, y, he⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p).mp hsep
  -- The degree of the minimal polynomial is `p ^ e` ...
  have hdeg_e : (minpoly K z).natDegree = p ^ e := by
    rw [he, Polynomial.natDegree_X_pow_sub_C]
  -- ... and `z ^ p ^ e = y ∈ K`.
  have hzy : z ^ p ^ e = algebraMap K E y := by
    have h := minpoly.aeval K z
    rw [he, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h
    exact h
  -- The minimal polynomial divides `X ^ p ^ (m + 1) - C c` for `z ^ p ^ (m + 1) = c ∈ K`, so
  -- `p ^ e ≤ p ^ (m + 1)`, i.e. `e ≤ m + 1`.
  have hem : e ≤ m + 1 := by
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp hmem
    have hdvd : minpoly K z ∣ Polynomial.X ^ p ^ (m + 1) - Polynomial.C c := by
      refine minpoly.dvd K z ?_
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]
    have h1 := Polynomial.natDegree_le_of_dvd hdvd
      (Polynomial.X_pow_sub_C_ne_zero (expChar_pow_pos K p (m + 1)) c)
    rw [Polynomial.natDegree_X_pow_sub_C, hdeg_e] at h1
    exact (Nat.pow_le_pow_iff_right hpp.one_lt).mp h1
  -- Conversely `z ^ p ^ e ∈ K` forces `m + 1 ≤ e`, by minimality of `m`.
  have hme : m + 1 ≤ e := by
    by_contra hlt
    rw [not_le] at hlt
    have hem' : e ≤ m := Nat.lt_succ_iff.mp hlt
    refine hmin ?_
    have hsplit : p ^ m = p ^ e * p ^ (m - e) := by
      rw [← pow_add, Nat.add_sub_cancel' hem']
    rw [hsplit, pow_mul, hzy]
    exact ⟨y ^ p ^ (m - e), by rw [map_pow]⟩
  rw [hdeg_e, le_antisymm hem hme]

/-- **Perfection descends along an extension with bounded degrees.**  Let `L / K` be an extension of
fields and suppose there is `N` such that every `x : L` is a root of a monic polynomial over `K` of
degree at most `N`.  If `L` is perfect then so is `K`.

Proof sketch (characteristic `p`): given `b : K`, take `x : L` with `x ^ p = b` (as `L` is perfect).
Let `x₀ = x` and `x_{i+1} : L` with `x_{i+1} ^ p = x_i`.  For each `i`, `x_i` is purely inseparable
over `K` (witnessed by `x_i ^ p ^ (i+1) = b`), so by `IsPurelyInseparable.minpoly_eq'` (applied to
the subextension `K⟮x_i⟯` and transported with `IntermediateField.minpoly_eq`) its minimal polynomial
has the form `X ^ p ^ e_i - C c_i`; the degree bound gives `p ^ e_i ≤ N`, hence `e_i ≤ N`.  From
`x_i = x_{i+1} ^ p` one gets `e_{i+1} = e_i + 1` whenever `e_i ≥ 1`.  If `e_0 ≥ 1` then
`e_N = e_0 + N ≥ N + 1 > N`, contradiction; hence `e_0 = 0`, i.e. `x` lies in `K`, so `b = x ^ p` is
a `p`-th power in `K`.  This gives surjectivity of the Frobenius of `K`, and
`PerfectRing.ofSurjective`/`PerfectRing.toPerfectField` finish. -/
theorem perfectField_of_forall_monic_aeval_eq_zero_natDegree_le {K L : Type*} [Field K] [Field L]
    [Algebra K L] [PerfectField L] (N : ℕ)
    (h : ∀ x : L, ∃ f : Polynomial K, f.Monic ∧ f.natDegree ≤ N ∧ Polynomial.aeval x f = 0) :
    PerfectField K := by
  -- Every element of `L` has degree at most `N` over `K`.
  have hdeg : ∀ x : L, (minpoly K x).natDegree ≤ N := by
    intro x
    obtain ⟨f, hfm, hfd, hfx⟩ := h x
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hfx) hfm.ne_zero).trans hfd
  obtain ⟨p, hpexp⟩ := ExpChar.exists K
  rcases hpexp with _ | ⟨hpp⟩
  · -- characteristic zero: every field is perfect
    exact PerfectField.ofCharZero
  · -- characteristic `p` prime
    haveI hEK : ExpChar K p := ExpChar.prime hpp
    haveI hEL : ExpChar L p := ExpChar.of_injective_algebraMap' K p
    have hsurj : Function.Surjective (frobenius K p) := by
      intro a
      by_cases ha : ∃ b : K, b ^ p = a
      · obtain ⟨b, hb⟩ := ha
        exact ⟨b, by rw [frobenius_def, hb]⟩
      · -- `a` is not a `p`-th power in `K`: this contradicts the degree bound.
        exfalso
        -- a compatible system of `p ^ n`-th roots of `a` inside the perfect field `L`
        let x : ℕ → L := fun n => (frobeniusEquiv L p).symm^[n] (algebraMap K L a)
        have hxpow : ∀ n, x n ^ p ^ n = algebraMap K L a := fun n =>
          iterate_frobeniusEquiv_symm_pow_p_pow L p (algebraMap K L a) n
        have hxstep : ∀ n, x (n + 1) ^ p = x n := by
          intro n
          have hxn : x (n + 1) = (frobeniusEquiv L p).symm (x n) := by
            simp only [x, Function.iterate_succ_apply']
          rw [hxn]
          exact frobeniusEquiv_symm_pow_p L p (x n)
        -- `x 1` is a `p`-th root of `a`, hence not in `K`
        have hx1 : x 1 ∉ (algebraMap K L).range := by
          rintro ⟨c, hc⟩
          refine ha ⟨c, (algebraMap K L).injective ?_⟩
          have h1 : x 1 ^ p = algebraMap K L a := by simpa using hxpow 1
          rw [map_pow, hc, h1]
        -- hence `x (j + 1) ^ p ^ j = x 1` is never in `K`
        have hxk : ∀ j : ℕ, x (j + 1) ^ p ^ j = x 1 := by
          intro j
          induction j with
          | zero => rw [pow_zero, pow_one]
          | succ i ih =>
            rw [pow_succ', pow_mul, hxstep (i + 1)]
            exact ih
        have hmem : x (N + 1) ^ p ^ (N + 1) ∈ (algebraMap K L).range :=
          ⟨a, (hxpow (N + 1)).symm⟩
        have hmin : x (N + 1) ^ p ^ N ∉ (algebraMap K L).range := by
          rw [hxk N]
          exact hx1
        have hkey := natDegree_minpoly_eq_pow_of_pow_mem_not_mem p N hpp hmem hmin
        have hle := hdeg (x (N + 1))
        rw [hkey] at hle
        have h1 : 2 ^ (N + 1) ≤ N :=
          (Nat.pow_le_pow_left hpp.two_le (N + 1)).trans hle
        have h2 : N < 2 ^ (N + 1) := lt_trans (Nat.lt_succ_self N) Nat.lt_two_pow_self
        exact absurd h1 (not_le.mpr h2)
    exact @PerfectRing.toPerfectField K p _ _ (PerfectRing.ofSurjective K p hsurj)

end NK.RamificationAudit
