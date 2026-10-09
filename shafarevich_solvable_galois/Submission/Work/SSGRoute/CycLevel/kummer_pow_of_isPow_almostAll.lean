import Mathlib
import Submission.Work.SSGRoute.CycLevel.KummerBundle
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `K^×/K^{×q}` injects into the local `q`-power classes after deleting a finite set of primes

Let `K` be a number field, `q` a prime such that `K` contains a primitive `q`-th root of unity, and
`a ∈ Kˣ`.  If `a` is a `q`-th power in the completion `K_𝔭` for every finite place `𝔭` outside a
finite set `T`, then `a` is a `q`-th power in `K`.

The proof is the classical Chebotarev argument.  Suppose `a` is not a `q`-th power in `K`.  Then
the Kummer field `L = K(a^{1/q}) ⊆ K'` is a cyclic extension of `K` of degree `q`
(`NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank`).  The local Kummer dichotomy
(`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`) says that a prime `𝔭` splits completely
in `L` exactly when `a` is a `q`-th power in `K_𝔭`; so by hypothesis every `𝔭 ∉ T` splits
completely.  Hence the set of primes that do *not* split completely in `L` is contained in the
finite set `T`, so has Dirichlet density `0`, and therefore the set of primes splitting completely
has density `1`.  But Chebotarev's theorem
(`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`) gives that
density `1/[L:K] = 1/q ≠ 1`.  Contradiction.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.CycLevel

theorem kummer_pow_of_isPow_almostAll {K : Type} [Field K] [NumberField K]
    (K' : Type) [Field K'] [Algebra K K'] [IsSepClosure K K']
    (q : ℕ) (hq : q.Prime) (hmu : ∃ ζ : K, IsPrimitiveRoot ζ q)
    (a : Kˣ)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (h : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔭 ∉ T →
      ∃ b : (𝔭.adicCompletion K)ˣ,
        algebraMap K (𝔭.adicCompletion K) (a : K) = (b : 𝔭.adicCompletion K) ^ q) :
    ∃ b : Kˣ, (b : K) ^ q = (a : K) := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨ζ, hζ⟩ := hmu
  -- `a` is not a `q`-th power in `K`, phrased in the Kummer class group.
  have ha : a ∉ NK.LocalAnabelian.powSubgroup q K := by
    intro hmem
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hmem
    refine hcon b ?_
    have h' : ((b ^ q : Kˣ) : K) = (a : K) := congrArg (fun u : Kˣ => (u : K)) hb
    rwa [Units.val_pow_eq_pow_val] at h'
  -- The Kummer field, a cyclic extension of `K` of degree `q`.
  let L : IntermediateField K K' := NK.LocalAnabelian.kummerField (K' := K') q a
  obtain ⟨hgal, hfr⟩ :=
    NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := K) (K' := K') q hq hζ a ha
  have hfrL : Module.finrank K ↥L = q := hfr
  haveI hgalI : IsGalois K ↥L := hgal
  haveI hfin : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hfrL]; exact hq.pos)
  haveI hNF : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  -- The set of primes of `K` splitting completely in `L`.
  let S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    {𝔭 | (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard = Module.finrank K ↥L}
  -- Chebotarev: `S` has density `1/[L:K] = 1/q`.
  have hdens : NumberField.Set.HasDirichletDensity S (1 / (q : ℝ)) := by
    have hd :=
      Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
        (K := K) (L := ↥L)
    simpa [S, hfrL] using hd
  -- By hypothesis every prime outside `T` splits completely, so `Sᶜ ⊆ T`.
  have hsub : Sᶜ ⊆ (↑T : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) := by
    intro 𝔭 h𝔭
    by_contra h𝔭T
    have h𝔭T' : 𝔭 ∉ T := by simpa using h𝔭T
    -- the local Kummer dichotomy
    have h1 : ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔭.asIdeal →
        NK.UchidaKummer.localDeg P 𝔭 = 1 :=
      (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := K) (K' := K')
        q hq hζ a L rfl 𝔭).mpr (h 𝔭 h𝔭T')
    have h2 : NK.UchidaKummer.SplitsCompletely (K := K) (L := ↥L) 𝔭 :=
      (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
        (K := K) (L := ↥L) 𝔭).mpr h1
    exact h𝔭 (by simpa [S, NK.UchidaKummer.SplitsCompletely] using h2)
  -- Hence `Sᶜ` has density `0`, and `S` has density `1`.
  have hSc : NumberField.Set.HasDirichletDensity Sᶜ 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
        (S := (↑T : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K)))) T.finite_toSet) hsub
  have hS1 : NumberField.Set.HasDirichletDensity S 1 := by
    have hcomp := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl hSc
    simpa using hcomp
  -- Uniqueness of the limit gives `1/q = 1`, absurd since `q` is prime.
  have heq : (1 : ℝ) / (q : ℝ) = 1 := tendsto_nhds_unique hdens hS1
  have hq1 : q = 1 := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h2 : (q : ℝ) = 1 := ((div_eq_one_iff_eq hqR).mp heq).symm
    exact_mod_cast h2
  have hq2 : 2 ≤ q := hq.two_le
  omega

end Work.SSGRoute.CycLevel
