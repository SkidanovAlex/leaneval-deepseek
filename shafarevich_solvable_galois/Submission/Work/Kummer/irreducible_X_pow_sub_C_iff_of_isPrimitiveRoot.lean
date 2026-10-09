/-
# Irreducibility of `X ^ n - C a` over a field containing a primitive `n`-th root of unity

If `K` contains a primitive `n`-th root of unity `ζ`, then `X ^ n - C a` is irreducible over `K`
if and only if no `a ^ m` (`0 < m < n`) is an `n`-th power in `K`.

This is the Kummer-theoretic refinement of Capelli's theorem.  The condition on the right says
that the class of `a` in `Kˣ / (Kˣ)ⁿ` has order exactly `n`, which is equivalent to
`[K (a ^ (1/n)) : K] = n`, i.e. to the irreducibility of the Kummer polynomial.

The proof is elementary and does not use Kummer theory proper:

* (⟸) If `g` is an irreducible factor of `X ^ n - C a` and `α` is a root of `g`, then
  `N(α) ^ n = a ^ deg g` (norm identity), so if `deg g < n` the hypothesis is violated at `m = deg g`.
  Hence every irreducible factor has degree `n`, and `X ^ n - C a` is irreducible.
* (⟹) If `c ^ n = a ^ m` with `0 < m < n`, then `(α ^ m / c) ^ n = 1` in `K (α)`, so (as `ζ` is
  a root of unity of order `n` in `K`) `α ^ m ∈ K`; then `α` satisfies a polynomial of degree `m`
  over `K`, contradicting `[K (α) : K] = n`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open Polynomial AdjoinRoot

namespace Work.Kummer

theorem irreducible_X_pow_sub_C_iff_of_isPrimitiveRoot {K : Type*} [Field K] {n : ℕ} [NeZero n]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {a : K} :
    Irreducible (Polynomial.X ^ n - Polynomial.C a) ↔
      ∀ m, 0 < m → m < n → ∀ c : K, c ^ n ≠ a ^ m := by
  constructor
  · -- (⟹) Suppose `X ^ n - C a` is irreducible and `c ^ n = a ^ m` with `0 < m < n`.
    intro H m hm0 hmn c hc
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    haveI : Fact (Irreducible (X ^ n - C a : K[X])) := ⟨H⟩
    have hn1 : n ≠ 1 := by omega
    -- `c ≠ 0`, else `a = 0` and `X ^ n` would be irreducible with `n ≠ 1`.
    have hc_ne : c ≠ 0 := by
      intro hc0
      have ha0 : a = 0 := by
        have hz : a ^ m = 0 := by rw [← hc, hc0]; exact zero_pow hn.ne'
        exact (pow_eq_zero_iff hm0.ne').mp hz
      rw [ha0, map_zero, sub_zero] at H
      exact not_irreducible_pow hn1 H
    have ha_ne : a ≠ 0 := by
      intro ha0
      apply hc_ne
      have hz : c ^ n = 0 := by rw [hc, ha0]; exact zero_pow hm0.ne'
      exact (pow_eq_zero_iff hn.ne').mp hz
    -- Work in the field `K (α) = AdjoinRoot (X ^ n - C a)`.
    let f : K[X] := X ^ n - C a
    have hα_pow : (AdjoinRoot.root f) ^ n = algebraMap K (AdjoinRoot f) a := by
      rw [AdjoinRoot.algebraMap_eq]; exact root_X_pow_sub_C_pow n a
    have hL_inj : Function.Injective (algebraMap K (AdjoinRoot f)) := by
      rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.coe_injective'
    have hal : algebraMap K (AdjoinRoot f) a ≠ 0 :=
      fun h => ha_ne (hL_inj (by rw [map_zero]; exact h))
    have hac : algebraMap K (AdjoinRoot f) c ≠ 0 :=
      fun h => hc_ne (hL_inj (by rw [map_zero]; exact h))
    have hζL : IsPrimitiveRoot (algebraMap K (AdjoinRoot f) ζ) n :=
      hζ.map_of_injective hL_inj
    -- `β = α ^ m / c` is an `n`-th root of unity.
    set β : AdjoinRoot f := AdjoinRoot.root f ^ m * (algebraMap K (AdjoinRoot f) c)⁻¹ with hβdef
    have hβ : β ^ n = 1 := by
      rw [hβdef, mul_pow]
      have h1 : (AdjoinRoot.root f ^ m) ^ n = (algebraMap K (AdjoinRoot f) a) ^ m := by
        rw [← pow_mul, mul_comm, pow_mul, hα_pow]
      have h2 : ((algebraMap K (AdjoinRoot f) c)⁻¹) ^ n =
          ((algebraMap K (AdjoinRoot f) a) ^ m)⁻¹ := by
        rw [inv_pow, ← map_pow (algebraMap K (AdjoinRoot f)) c n, hc,
          ← map_pow (algebraMap K (AdjoinRoot f)) a m]
      rw [h1, h2, mul_inv_cancel₀ (pow_ne_zero m hal)]
    -- Hence `β` is a power of `ζ`, i.e. `α ^ m ∈ K`.
    obtain ⟨i, _hi, hβi⟩ := hζL.eq_pow_of_pow_eq_one hβ
    have hαm : AdjoinRoot.root f ^ m = algebraMap K (AdjoinRoot f) (c * ζ ^ i) := by
      have hle : β * algebraMap K (AdjoinRoot f) c = AdjoinRoot.root f ^ m := by
        rw [hβdef, mul_assoc, inv_mul_cancel₀ hac, mul_one]
      rw [← hle, ← hβi, map_mul, map_pow, mul_comm]
    -- But then `α` has degree `≤ m < n` over `K`, contradicting `minpoly = X ^ n - C a`.
    have hmp : minpoly K (AdjoinRoot.root f) = X ^ n - C a := by
      have h1 := minpoly.eq_of_irreducible_of_monic (x := AdjoinRoot.root f) (p := X ^ n - C a) H
          ?_ (monic_X_pow_sub_C a hn.ne')
      · exact h1.symm
      · have : (aeval (AdjoinRoot.root f)) (X ^ n - C a) =
            (AdjoinRoot.root f)^n - algebraMap K (AdjoinRoot f) a := by simp
        rw [this, hα_pow, sub_self]
    have hdvd : minpoly K (AdjoinRoot.root f) ∣ X ^ m - C (c * ζ ^ i) :=
      minpoly.dvd K (AdjoinRoot.root f) (by
        have : (aeval (AdjoinRoot.root f)) (X ^ m - C (c * ζ ^ i)) =
            (AdjoinRoot.root f)^m - algebraMap K (AdjoinRoot f) (c * ζ ^ i) := by simp
        rw [this, hαm, sub_self])
    have hnonzero : (X ^ m - C (c * ζ ^ i) : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hm0 _
    have hle2 : (minpoly K (AdjoinRoot.root f)).natDegree ≤ m := by
      have := natDegree_le_of_dvd hdvd hnonzero
      rwa [natDegree_X_pow_sub_C] at this
    have hdeg : (minpoly K (AdjoinRoot.root f)).natDegree = n := by
      rw [hmp, natDegree_X_pow_sub_C]
    omega
  · -- (⟸) Assume the condition and let `g` be an irreducible factor of `X ^ n - C a`.
    intro h
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hf_ne : (X ^ n - C a : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hn a
    have hf_not_unit : ¬ IsUnit (X ^ n - C a : K[X]) := by
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hn, Nat.cast_eq_zero]
      exact hn.ne'
    obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hf_not_unit hf_ne
    have hg_ne : g ≠ 0 := hg_irr.ne_zero
    suffices natDegree g = n from
      (associated_of_dvd_of_natDegree_le hg_dvd hf_ne
        (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg_irr
    -- The norm identity `N(α) ^ n = a ^ deg g`, where `α` is a root of `g`.
    have hα_pow : (AdjoinRoot.root g) ^ n = algebraMap K (AdjoinRoot g) a := by
      have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (AdjoinRoot.of g) (AdjoinRoot.root g) hg_dvd
        (AdjoinRoot.eval₂_root g)
      rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
      rw [this, AdjoinRoot.algebraMap_eq]
    have hnorm : (Algebra.norm K (AdjoinRoot.root g)) ^ n = a ^ g.natDegree := by
      rw [← map_pow (Algebra.norm K) (AdjoinRoot.root g) n, hα_pow, Algebra.norm_algebraMap,
        (AdjoinRoot.powerBasis hg_ne).finrank, powerBasis_dim hg_ne]
    have hle : g.natDegree ≤ n := by
      have := natDegree_le_of_dvd hg_dvd hf_ne
      rwa [natDegree_X_pow_sub_C] at this
    -- If `deg g < n`, the hypothesis is violated at `m = deg g`.
    by_contra hne
    have hlt : g.natDegree < n := lt_of_le_of_ne hle hne
    exact h _ hg_irr.natDegree_pos hlt _ hnorm

end Work.Kummer
