import Mathlib
import Submission.Work.DSM8m.Presentation.exists_smul_mem_of_le
import Submission.Work.DSM8m.Presentation.isFractionRing_adjoin_singleton
import Submission.Work.DSM8m2.Algebra.exists_clearing_of_generators

/-!
# Clearing denominators on a finitely generated algebra

Let `A` be a domain with fraction field `K = Frac A`, let `L` be a field with `A ⊆ K ⊆ L` a tower
of algebras, let `η ∈ L` be integral over `A` and primitive over `K` (`K[η] = L`), and let
`φ : B →ₐ[A] L` be an `A`-algebra map from a finitely generated `A`-algebra `B`.

Then a *single* nonzero `c ∈ A` clears denominators in the following graded sense: for every
`b : B` there is `n : ℕ` and a polynomial `Q ∈ A[X]` with

  `φ b * c ^ n = Q(η)`.

This is the "A[η][1/c] contains the image of B" statement (`Submission/Work/DSM8m/DESIGN.md` §3)
needed for the M8m node.

## Proof

Write `S = A[η] ⊆ L`.  Since `η` is integral over `A`, `S` is a finite `A`-module, and since
`K[η] = L` the field `L` is the fraction field of `S`.  Hence every `x ∈ L` is a fraction
`s₁ / s₂` with `s₁, s₂ ∈ S`, and `s₂ ≠ 0` admits an `A`-multiple lying in `A`: there are `c ≠ 0`
in `A` and `y ∈ S` with `y · s₂ = c`.  Therefore

  `x · c = y · s₁ ∈ S`,

i.e. *every* element of `L` acquires an `A`-denominator lying in `S`.

For a finitely generated `B` it remains to package this.  Pick a finite generating set `gens` of
`B` over `A` (from `Algebra.FiniteType`), a denominator `c_g ∈ A` for each `φ g` (`g ∈ gens`) and
put `c = ∏_{g ∈ gens} c_g`.  The set

  `T = { x : L | ∃ k, x · c ^ k ∈ S }`

is an `A`-subalgebra of `L`, and each `φ g` lies in it, because `c = c_g · ∏_{h ≠ g} c_h`
factorizes off the witness for `g`.  Pulling `T` back along `φ` gives an `A`-subalgebra of `B`
containing `gens`, hence equal to `⊤` since `gens` generates `B`.  This packaging step is the
general lemma `Work.DSM8m2.Algebra.exists_clearing_of_generators` (no fraction-field hypotheses on
`A` are needed for it).  Finally `S = A[η] = range (aeval η)`, so membership in `S` is exactly
being a polynomial in `η` over `A`.
-/

set_option linter.style.haveILetI false

namespace Work.DSM8m2.Algebra

theorem exists_clearing_denominator {A K L B : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [CommRing B] [Algebra A B] (φ : B →ₐ[A] L)
    (hB : Algebra.FiniteType A B) {η : L} (hint : IsIntegral A η)
    (hη : Algebra.adjoin K ({η} : Set L) = ⊤) :
    ∃ c : A, c ≠ 0 ∧ ∀ b : B, ∃ (n : ℕ) (Q : Polynomial A),
      φ b * (algebraMap A L c) ^ n = Polynomial.aeval η Q := by
  classical
  -- The `A`-subalgebra `S = A[η]` of `L`.
  let S : Subalgebra A L := Algebra.adjoin A ({η} : Set L)
  -- `S` is a finite `A`-module, because `η` is integral over `A`.
  haveI hSfin : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (A := L) (s := ({η} : Set L))
      (Set.finite_singleton η) (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hint)
  -- `L` is the fraction field of `S`, because `K[η] = L` and `K = Frac A`.
  have hSfrac : IsFractionRing S L :=
    Work.DSM8m.Presentation.isFractionRing_adjoin_singleton (A := A) (K := K) (L := L) η hη
  -- Step 1: every element of `L` has a nonzero `A`-denominator lying in `S`.
  have key : ∀ x : L, ∃ c : A, c ≠ 0 ∧ x * algebraMap A L c ∈ S := by
    intro x
    haveI : IsLocalization (nonZeroDivisors S) L := hSfrac
    haveI : IsDomain ↥S := Subalgebra.isDomain S
    -- write `x = w.1 / w.2` with `w.1, w.2 ∈ S`
    obtain ⟨w, hw⟩ := IsLocalization.surj (nonZeroDivisors S) x
    have hbne : (w.2 : S) ≠ 0 := by
      intro h
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (R := S) (K := L)
        (x := (w.2 : S)) w.2.2) (by rw [h, map_zero])
    -- turn the `S`-denominator `w.2` into an `A`-denominator
    obtain ⟨c, y, hc, hyw⟩ :=
      Work.DSM8m.Presentation.exists_mul_eq_algebraMap_of_finite A L S hbne
    refine ⟨c, hc, ?_⟩
    have hw' : x * ((w.2 : S) : L) = ((w.1 : S) : L) := hw
    have hyw' : (y : L) * ((w.2 : S) : L) = algebraMap A L c := by
      have h := congrArg (algebraMap S L) hyw
      rw [map_mul] at h
      rw [IsScalarTower.algebraMap_apply A S L c]
      simpa using h
    have hfinal : x * algebraMap A L c = (y : L) * ((w.1 : S) : L) := by
      calc x * algebraMap A L c = x * ((y : L) * ((w.2 : S) : L)) := by rw [hyw']
        _ = (y : L) * (x * ((w.2 : S) : L)) := by ring
        _ = (y : L) * ((w.1 : S) : L) := by rw [hw']
    rw [hfinal]
    exact mul_mem y.2 w.1.2
  -- Step 2: a finite generating set of `B` over `A`.
  obtain ⟨gens, hgens⟩ := hB.out
  -- Step 3: a common denominator of the images of the generators.
  have hgen : ∀ g ∈ gens, ∃ c : A, c ≠ 0 ∧ φ g * algebraMap A L c ∈ S :=
    fun g _ => key (φ g)
  -- Step 4: package the clearing of the generators into clearing of all of `B`.
  obtain ⟨c, hcne, hclearing⟩ := exists_clearing_of_generators φ gens hgens S hgen
  -- Step 5: conclude, using `S = A[η] = range (aeval η)`.
  refine ⟨c, hcne, fun b => ?_⟩
  obtain ⟨k, hk⟩ := hclearing b
  have hk' : φ b * (algebraMap A L c) ^ k ∈ Algebra.adjoin A ({η} : Set L) := hk
  rw [Algebra.adjoin_singleton_eq_range_aeval A η] at hk'
  obtain ⟨Q, hQ⟩ := (AlgHom.mem_range (Polynomial.aeval (R := A) (A := L) η)).mp hk'
  exact ⟨k, Q, hQ.symm⟩

end Work.DSM8m2.Algebra
