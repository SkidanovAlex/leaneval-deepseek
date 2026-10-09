import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.valuation_le_iff_comap_eq
import Submission.NK.NeukirchUchida.exists_valuation_le_pow_of_rankOne
import Submission.NK.NeukirchUchida.mulArchimedean_valueGroupWithZero_of_elementwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The extension of a finite place of a number field to the separable closure has rank one

Let `K` be a number field, `p` a finite place of `K` (i.e. a height one prime of `𝓞 K`) and
`K'` a separable closure of `K`.  Let `A` be a valuation subring of `K'` whose contraction to
`K` is the valuation ring `𝒪_𝔭` of `p`.  We prove

`Nonempty (Valuation.RankOne A.valuation)`,

i.e. the `p`-adic valuation of `K` extends to `K'` as a valuation of **rank one**: its value
group embeds strictly monotonically into `ℝ≥0`.

## Mathematical content

Two inputs are combined.

* **Algebraicity of `K'` over `K` forces the value group extension to be torsion.**
  For `x : K'` algebraic over `K`, the classical "two maximal terms have equal value" argument
  applied to the minimal polynomial of `x` produces `n > 0` and `c : K` with
  `A.valuation x ^ n = A.valuation (algebraMap c)`
  (`Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic`).

* **The value group of `K` at `p` is archimedean** because it is `ℤ`: the element level form of
  this is `NK.NeukirchUchida.exists_valuation_le_pow_of_rankOne`.

Given `u, z : K'` with `1 < A.valuation z`, torsion for `u` and for `z` writes `A.valuation u ^ n`
and `A.valuation z ^ m` as values of elements `a, b` of `K`; the archimedean property of the base
furnishes `N₀` with `A.valuation (algebraMap a) ≤ A.valuation (algebraMap b) ^ N₀`; taking the
`n`-th power and comparing gives `A.valuation u < A.valuation z ^ (m * N₀ + 1)`.

Since every element of the value group is a value, this element level statement is exactly
`MulArchimedean` of the value group of `A.valuation`, which together with nontriviality of
`A.valuation` is `Valuation.RankOne` (`Valuation.nonempty_rankOne_iff_mulArchimedean`).

The order comparison between the values of `A` on `K` and the values of the base valuation `w`
is `Commons.RingTheory.Valuation.valuation_le_iff_comap_eq` together with the identification of
the valuation subring of `w` with the contraction of `A`.
-/

noncomputable section

open scoped NumberField

namespace NK.NeukirchUchida

/-- **Order transfer.**  If the contraction of the valuation subring `A` of `L` along
`K → L` is the valuation subring of the valuation `w` on `K`, then for nonzero `c : K` the
comparison of the `A`-values of `algebraMap x` and `algebraMap c` is the comparison of the
`w`-values of `x` and `c`. -/
lemma le_iff_le_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (A : ValuationSubring L)
    (hA : A.comap (algebraMap K L) = w.valuationSubring) {x c : K} (hc : c ≠ 0) :
    A.valuation (algebraMap K L x) ≤ A.valuation (algebraMap K L c) ↔ w x ≤ w c := by
  have h1 : w.IsEquiv w.valuationSubring.valuation :=
    (Valuation.isEquiv_iff_valuationSubring w _).mpr
      (by rw [ValuationSubring.valuationSubring_valuation])
  exact (Commons.RingTheory.Valuation.valuation_le_iff_comap_eq w.valuationSubring A hA hc).trans
    h1.le_iff_le.symm

/-- **Element level archimedean property of the extension.**  If `K ⊆ L` is algebraic, `w` is a
rank one valuation on `K` and `A` is a valuation subring of `L` contracting to the valuation
subring of `w`, then every `A`-value is dominated by a power of any `A`-value `> 1`.

The proof combines the torsion statement for algebraic extensions
(`exists_pow_eq_algebraMap_of_isAlgebraic`) with the archimedean property of the base
(`exists_valuation_le_pow_of_rankOne`). -/
lemma exists_valuation_lt_pow_of_one_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) [w.RankOne]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L)
    (hA : A.comap (algebraMap K L) = w.valuationSubring) {u z : L} (hz : z ≠ 0)
    (hz1 : 1 < A.valuation z) :
    ∃ N : ℕ, A.valuation u < A.valuation z ^ N := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, by rw [map_zero, pow_zero]; exact zero_lt_one⟩
  -- Torsion of the value group extension for `u` and for `z`.
  obtain ⟨n, hn, a, _ha0, ha⟩ :=
    Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic (k := K) (K := L)
      A.valuation (halg.isAlgebraic u) hu
  obtain ⟨m, hm, b, hb0, hb⟩ :=
    Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic (k := K) (K := L)
      A.valuation (halg.isAlgebraic z) hz
  -- `1 < A.valuation (algebraMap b)`, transported to the base valuation `w`.
  have hb1 : 1 < A.valuation (algebraMap K L b) := by
    rw [← hb]
    exact one_lt_pow₀ hz1 (ne_of_gt hm)
  have hwb1 : 1 < w b := by
    have h := le_iff_le_of_comap_eq w A hA (x := b) (c := 1) one_ne_zero
    rw [map_one (algebraMap K L), map_one w] at h
    rw [lt_iff_not_ge] at hb1 ⊢
    exact fun hle => hb1 (h.mpr hle)
  -- The archimedean property of the base valuation.
  obtain ⟨N₀, hN₀⟩ := exists_valuation_le_pow_of_rankOne w (a := a) (b := b) hwb1
  have htrans : A.valuation (algebraMap K L a) ≤ A.valuation (algebraMap K L (b ^ N₀)) := by
    refine (le_iff_le_of_comap_eq w A hA (x := a) (c := b ^ N₀) (pow_ne_zero _ hb0)).mpr ?_
    rw [map_pow w]
    exact hN₀
  have hstep : (A.valuation u) ^ n ≤ ((A.valuation z) ^ m) ^ N₀ := by
    calc (A.valuation u) ^ n = A.valuation (algebraMap K L a) := ha
      _ ≤ A.valuation (algebraMap K L (b ^ N₀)) := htrans
      _ = (A.valuation (algebraMap K L b)) ^ N₀ := by
        rw [map_pow (algebraMap K L), Valuation.map_pow]
      _ = ((A.valuation z) ^ m) ^ N₀ := by rw [hb]
  -- Raise to the `n`-th power and compare with a large power of `A.valuation z`.
  refine ⟨m * N₀ + 1, ?_⟩
  have hlt : (A.valuation u) ^ n < ((A.valuation z) ^ (m * N₀ + 1)) ^ n := by
    rw [← pow_mul]
    refine lt_of_le_of_lt (hstep.trans (le_of_eq (pow_mul _ _ _).symm)) (pow_lt_pow_right₀ hz1 ?_)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hn)
  exact lt_of_pow_lt_pow_left₀ n zero_le hlt

/-- **Rank one passes to algebraic extensions.**  Let `K ⊆ L` be an algebraic extension of
fields, `w` a rank one valuation on `K` and `A` a valuation subring of `L` whose contraction to
`K` is the valuation subring of `w`.  Then `A.valuation` has rank one. -/
theorem nonempty_rankOne_of_comap_eq_valuationSubring {K L : Type*} [Field K] [Field L]
    [Algebra K L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) [w.RankOne]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L)
    (hA : A.comap (algebraMap K L) = w.valuationSubring) :
    Nonempty A.valuation.RankOne := by
  -- Nontriviality of `A.valuation`, from nontriviality of `w`.
  have hnt : A.valuation.IsNontrivial := by
    rw [Valuation.IsNontrivial_iff_exists_one_lt]
    obtain ⟨x₀, hx₀⟩ := Valuation.IsNontrivial.exists_one_lt (v := w)
    refine ⟨algebraMap K L x₀, ?_⟩
    have h := le_iff_le_of_comap_eq w A hA (x := x₀) (c := 1) one_ne_zero
    rw [map_one (algebraMap K L), map_one w] at h
    rw [lt_iff_not_ge] at hx₀ ⊢
    exact fun hle => hx₀ (h.mp hle)
  -- The element level archimedean property upgrades to `MulArchimedean` of the value group,
  -- which is equivalent to rank one once nontriviality is known.
  have hma : MulArchimedean (MonoidWithZeroHom.ofClass A.valuation).ValueGroup₀ :=
    mulArchimedean_valueGroupWithZero_of_elementwise A fun u z hz hz1 =>
      exists_valuation_lt_pow_of_one_lt w halg A hA hz hz1
  exact (Valuation.nonempty_rankOne_iff_mulArchimedean (v := A.valuation)).mpr hma

/-- **The `p`-adic valuation of a number field extends to its separable closure with rank one.**
Let `K` be a number field, `p` a finite place of `K`, `K'` a separable closure of `K` and `A` a
valuation subring of `K'` whose contraction to `K` is the valuation ring at `p`.  Then the
valuation of `A` has rank one. -/
theorem rankOne_valuationSubringAtPrime_sepClosure {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    Nonempty (Valuation.RankOne A.valuation) := by
  refine nonempty_rankOne_of_comap_eq_valuationSubring
    (IsDedekindDomain.HeightOneSpectrum.valuation K p) (inferInstanceAs (Algebra.IsAlgebraic K K'))
    A ?_
  rw [hA, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]

end NK.NeukirchUchida
