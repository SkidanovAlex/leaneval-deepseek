import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_finite
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of an admissible modulus

Let `L / K` be a finite Galois extension of number fields.  This file constructs a modulus
`m > 0` which is

* **admissible** (`NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m`, Lang, Chapter VII §4):
  at every prime `𝔭` of `𝓞 K` dividing `(m)`, every unit of `K_𝔭` which is `≡ 1 mod (m)` is a
  local norm from `L_𝔮` for every prime `𝔮 | 𝔭`, and
* **supported on the ramified primes**: every prime of `𝓞 K` which is not unramified in `L`
  divides `(m)`.

This is the input `∃ m, 0 < m ∧ IsAdmissible K L m ∧ (ramified primes divide m)` used in the
ideal-theoretic form of the conductor theorem of Lang, Chapter X §2
(`NK.CFTLib.ArtinReciprocityIdeal.langCyclicKernelLe` and its consumers), where the modulus of
the ray class group has to be large enough to see all ramification and fine enough for the local
norm groups.

## The construction

The file `Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage` proves, at a *chosen*
prime `q | Q`, a congruence level `levelOf Q` such that every `z ≡ 1 mod Q^(levelOf Q)` is a local
norm from `L_q` (`exists_level_localNormFinite`, `mem_range_localNormFinite_of_val_le_levelOf`).
For `IsAdmissible` one needs the same statement at *every* prime of `L` above `Q`, so here we take
`levelQ Q` to be the maximum of the levels over the (finitely many) primes of `L` above `Q`
(`levelOver` and the `Finset.sup` defining `levelQ`), and then build the modulus exactly as in
`exists_modulus`:

`m = ∏_{Q ∈ ramPrimes} (N Q) ^ (sup_{Q ∈ ramPrimes} levelQ Q)`.

Then `m` is divisible by `levelQ`-th powers of every ramified `Q` (`exists_modulus_level`), which
gives both `IsAdmissible K L m` (the ramified case from the local level, the unramified case from
surjectivity of the local norm on units) and the divisibility of `(m)` by every prime which is not
unramified in `L` (`ramPrimes` is by definition the set of primes below a ramified prime of `L`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## A uniform local congruence level at a prime of `𝓞 K` -/

/-- The congruence level of the local norm at a prime `q` of `𝓞 L` above `Q`: every unit of `K_Q`
of valuation at most `exp (-(levelOver Q q hq))` is a norm from `L_qˣ`. -/
noncomputable def levelOver (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) : ℕ :=
  Classical.choose
    (NK.CFTLib.ExistsCongruence.exists_level_localNormFinite (K := K) (L := L) Q q hq)

theorem levelOver_pos (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) : 0 < levelOver (K := K) (L := L) Q q hq :=
  (Classical.choose_spec
    (NK.CFTLib.ExistsCongruence.exists_level_localNormFinite (K := K) (L := L) Q q hq)).1

/-- The defining property of `levelOver`. -/
theorem mem_range_of_val_le_levelOver (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (z : (Q.adicCompletion K)ˣ)
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      (WithZero.exp (-((levelOver (K := K) (L := L) Q q hq : ℕ) : ℤ)) :
        WithZero (Multiplicative ℤ))) :
    z ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range :=
  (Classical.choose_spec
    (NK.CFTLib.ExistsCongruence.exists_level_localNormFinite (K := K) (L := L) Q q hq)).2 z hz

/-- `levelOver` extended by `1` to primes of `𝓞 L` not lying over `Q`; this is the function whose
supremum over the primes above `Q` is the uniform level `levelQ`. -/
noncomputable def levelAny (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) : ℕ := by
  classical
  exact if hq : q.asIdeal.LiesOver Q.asIdeal then levelOver (K := K) (L := L) Q q hq else 1

theorem levelAny_of_liesOver (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    levelAny (K := K) (L := L) Q q = levelOver (K := K) (L := L) Q q hq := by
  unfold levelAny
  exact dif_pos hq

theorem levelAny_pos (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) :
    0 < levelAny (K := K) (L := L) Q q := by
  classical
  by_cases hq : q.asIdeal.LiesOver Q.asIdeal
  · rw [levelAny_of_liesOver (K := K) (L := L) Q q hq]
    exact levelOver_pos (K := K) (L := L) Q q hq
  · have h1 : levelAny (K := K) (L := L) Q q = 1 := by
      unfold levelAny
      exact dif_neg hq
    rw [h1]
    norm_num

/-- **The uniform level at a prime `Q` of `𝓞 K`**: the maximum of the local levels at the primes
of `L` above `Q`.  Every unit of `K_Q` which is `≡ 1` modulo this level is a norm from `L_q` for
every `q | Q`. -/
noncomputable def levelQ (Q : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).sup
    (levelAny (K := K) (L := L) Q)

theorem levelQ_pos (Q : HeightOneSpectrum (𝓞 K)) : 0 < levelQ (K := K) (L := L) Q := by
  obtain ⟨q₀, hq₀⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
  have hmem : q₀ ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)).mpr hq₀
  have hle : levelAny (K := K) (L := L) Q q₀ ≤ levelQ (K := K) (L := L) Q :=
    Finset.le_sup (s := NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q)
      (f := levelAny (K := K) (L := L) Q) hmem
  exact lt_of_lt_of_le (levelAny_pos (K := K) (L := L) Q q₀) hle

/-- The defining property of `levelQ`: at every prime `q` of `𝓞 L` above `Q`, every unit of `K_Q`
which is `≡ 1` modulo `levelQ Q` (i.e. of valuation at most `exp (-(levelQ Q))`) is a norm from
`L_qˣ`. -/
theorem mem_range_of_val_le_levelQ (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (z : (Q.adicCompletion K)ˣ)
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      (WithZero.exp (-((levelQ (K := K) (L := L) Q : ℕ) : ℤ)) : WithZero (Multiplicative ℤ))) :
    z ∈ (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
  classical
  have hmem : q ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)).mpr hq
  have hle : levelAny (K := K) (L := L) Q q ≤ levelQ (K := K) (L := L) Q :=
    Finset.le_sup (s := NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q)
      (f := levelAny (K := K) (L := L) Q) hmem
  rw [levelAny_of_liesOver (K := K) (L := L) Q q hq] at hle
  have hexp : (WithZero.exp (-((levelQ (K := K) (L := L) Q : ℕ) : ℤ)) :
        WithZero (Multiplicative ℤ)) ≤
      (WithZero.exp (-((levelOver (K := K) (L := L) Q q hq : ℕ) : ℤ)) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.exp_le_exp]
    exact neg_le_neg (by exact_mod_cast hle)
  exact mem_range_of_val_le_levelOver (K := K) (L := L) Q q hq z (le_trans hz hexp)

/-! ## The modulus -/

/-- **The modulus**, with the uniform level `levelQ`: there is `m > 0` which is divisible, at every
ramified prime `Q`, by the `levelQ Q`-th power of `Q`. -/
theorem exists_modulus_level :
    ∃ m : ℕ, 0 < m ∧ ∀ Q : HeightOneSpectrum (𝓞 K),
      Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L) →
      (m : 𝓞 K) ∈ Q.asIdeal ^ levelQ (K := K) (L := L) Q := by
  classical
  refine ⟨∏ Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L),
      (Ideal.absNorm Q.asIdeal) ^
        (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
          (levelQ (K := K) (L := L)), ?_, ?_⟩
  · refine Finset.prod_pos fun Q _ => pow_pos ?_ _
    exact Nat.pos_of_ne_zero fun h => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  · intro Q hQ
    have hAN : (((Ideal.absNorm Q.asIdeal) ^
        (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
          (levelQ (K := K) (L := L)) : ℕ) : 𝓞 K)
        ∈ Q.asIdeal ^ (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
            (levelQ (K := K) (L := L)) := by
      rw [Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem Q.asIdeal) _
    have hle : levelQ (K := K) (L := L) Q ≤
        (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
          (levelQ (K := K) (L := L)) := Finset.le_sup hQ
    rw [← Finset.prod_erase_mul (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L))
      (fun Q => (Ideal.absNorm Q.asIdeal) ^
        (NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)).sup
          (levelQ (K := K) (L := L))) hQ]
    rw [Nat.cast_mul]
    refine Ideal.mul_mem_left (Q.asIdeal ^ levelQ (K := K) (L := L) Q) _ ?_
    exact Ideal.pow_le_pow_right hle hAN

/-! ## Admissibility of the modulus -/

/-- A modulus divisible by the `levelQ`-th powers of all ramified primes is admissible. -/
theorem isAdmissible_of_mem_pow (m : ℕ)
    (hm : ∀ Q : HeightOneSpectrum (𝓞 K),
      Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L) →
      (m : 𝓞 K) ∈ Q.asIdeal ^ levelQ (K := K) (L := L) Q) :
    IsAdmissible K L m := by
  intro Q hQmem q hq x hx
  by_cases hram : Q ∈ NK.CFTLib.ExistsCongruence.ramPrimes (K := K) (L := L)
  · refine mem_range_of_val_le_levelQ (K := K) (L := L) Q q hq x (le_trans hx ?_)
    exact NK.CFTLib.ExistsCongruence.val_natCast_le_exp_neg_of_mem_pow Q m
      (levelQ (K := K) (L := L) Q) (hm Q hram)
  · exact NK.CFTLib.ExistsCongruence.mem_range_localNormFinite_of_congr (K := K) (L := L)
      Q q hq
      (NK.CFTLib.ExistsCongruence.ramificationIdx_eq_one_of_notMem_ramPrimes
        (K := K) (L := L) hram hq)
      (m := m) hQmem (z := x) hx

/-! ## The main theorem -/

theorem exists_admissible (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ m : ℕ, 0 < m ∧ NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) := by
  classical
  obtain ⟨m, hmpos, hm⟩ := exists_modulus_level (K := K) (L := L)
  refine ⟨m, hmpos, isAdmissible_of_mem_pow (K := K) (L := L) m hm, ?_⟩
  intro p hp
  have hex : ∃ P : NK.Chebotarev.PrimeIdeal L,
      P.asIdeal.LiesOver p.asIdeal ∧ P.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := by
    by_contra h
    apply hp
    intro P hP
    by_contra hne
    exact h ⟨P, hP, hne⟩
  obtain ⟨P, hP, hne⟩ := hex
  exact Ideal.pow_le_self (n := levelQ (K := K) (L := L) p)
    (levelQ_pos (K := K) (L := L) p).ne'
    (hm p (NK.CFTLib.ExistsCongruence.mem_ramPrimes_of_ramificationIdx_ne_one
      (K := K) (L := L) (Q := p) hP hne))

end NK.CFTLib.ArtinReciprocityIdeal
