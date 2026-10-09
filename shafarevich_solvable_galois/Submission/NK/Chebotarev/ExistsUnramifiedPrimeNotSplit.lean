import Mathlib
import Submission.NK.Mine.Generation
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime which is unramified and does not split completely

For a finite Galois extension `L / K` of number fields of degree `> 1` there is a nonzero prime
`p` of `𝓞 K` which is unramified in `L` and does *not* split completely in `L`; in fact the
unramified primes of `𝓞 K` form a set of Dirichlet density `1`, while the completely split primes
have density `1 / [L : K] < 1`.

The two inputs are

* `Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`: the primes
  splitting completely have Dirichlet density `1 / [L : K]`, so their complement has density
  `1 - 1 / [L : K] ≠ 0`;
* `Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`: only finitely many primes
  of `𝓞 L` ramify over `𝓞 K`, hence the ramified primes of `𝓞 K` also form a finite set, of
  Dirichlet density `0`.

As a set of density `≠ 0` cannot be contained in a set of density `0` (nor in a finite set), the
primes which are unramified and not completely split are nonempty.  This is the "easy half of
Chebotarev" needed to see that the decomposition groups of the absolute Galois group of a number
field generate it.
-/

open Filter IsDedekindDomain Topology Set

namespace NK.Chebotarev

/-- **Some prime is unramified and does not split completely.**  If `L / K` is a finite Galois
extension of number fields of degree `> 1`, then some nonzero prime `p` of `𝓞 K` is unramified in
`L` (all primes of `𝓞 L` above `p` have ramification index `1`) and has fewer primes of `𝓞 L`
above it than the degree `[L : K]`. -/
theorem ExistsUnramifiedPrimeNotSplit {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h : 1 < Module.finrank K L) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        P.asIdeal.LiesOver p.asIdeal →
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard < Module.finrank K L := by
  classical
  -- Suppose every unramified prime splits completely.  Then the primes which do not split
  -- completely are all ramified, hence finite; but they have Dirichlet density `1 - 1 / [L : K]`.
  by_contra hcon
  -- The primes of `𝓞 K` that ramify in `L`, i.e. those having a prime of `𝓞 L` above them with
  -- ramification index `≠ 1`.
  set Bad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    {p | ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1} with hBaddef
  -- Only finitely many primes of `𝓞 L` ramify (they divide the different), so `Bad` is finite.
  have hBadFin : Bad.Finite := by
    have hL : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    refine (hL.image (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) =>
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) q)).subset ?_
    rintro p ⟨P, hP, heP⟩
    exact ⟨P, heP, IsDedekindDomain.HeightOneSpectrum.ext (by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hP.over])⟩
  -- A set of Dirichlet density zero, by finiteness of `Bad`.
  have hBadZero : NumberField.Set.HasDirichletDensity
      ({p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard =
          Module.finrank K L}ᶜ) 0 := by
    refine Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hBadFin) ?_
    intro p hp
    -- `hp` says that `p` does not split completely; if `p` were also unramified we would be done.
    by_contra hbad
    refine hcon ⟨p, ?_, ?_⟩
    · intro P hP
      by_contra heP
      exact hbad ⟨P, hP, heP⟩
    · simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hp
      have hle :=
        Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank (K := K) (L := L) p
      omega
  -- The completely split primes have density `1 / [L : K]`, so their complement has the
  -- complementary density, which is nonzero.
  have hsplit : NumberField.Set.HasDirichletDensity
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L}
      (1 / (Module.finrank K L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have hcompl := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hsplit
  have heq : 1 - 1 / (Module.finrank K L : ℝ) = 0 := tendsto_nhds_unique hcompl hBadZero
  -- Hence `[L : K] = 1`, contradicting the hypothesis.
  have hnpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L))
  have hn1 : (Module.finrank K L : ℝ) = 1 := by
    field_simp at heq
    linarith
  have : Module.finrank K L = 1 := by exact_mod_cast hn1
  omega

end NK.Chebotarev
