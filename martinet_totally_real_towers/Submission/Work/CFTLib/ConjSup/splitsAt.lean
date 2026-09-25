import Mathlib
import Submission.Work.CFTLib.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_sup
import Submission.Work.Tower.Shafarevich.Frobenius.splitsCompletelyIn_iff_ncard_primesOver
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_iSup_eq_top

/-!
# Splitting in the compositum of the conjugates of `L'`

Let `F` be a number field, `K'/F` a finite Galois extension, `L'/K'` a finite Galois extension
and `M = conjSup p K' L'` the compositum of the `F`-conjugates of `L'` (the smallest Galois
extension of `F` containing `L'`).  If a prime `v` of `F` splits completely in `K'` and every
prime of `K'` above `v` splits completely in `L'`, then `v` splits completely in `M`.

This is the "bookkeeping" step in the proof of Shafarevich's relation-rank bound: it says that
the set `T` of primes which is assumed to split in `K'` (and whose primes in `K'` split in `L'`)
also splits in the Galois closure `M` of `L'` over `F`, to which the bound is then applied.

## Proof

Everything is done at the level of the predicate `Work.Tower.SplitsCompletelyIn` ("every prime
above `𝔭` is unramified with residue field `𝓞 F ⧸ 𝔭`"), which for a prime `𝔭 ≠ ⊥` is equivalent
to "every prime above `𝔭` has `e = f = 1`" — and that, in turn, is exactly what `SplitsAt` needs.

1. `ef_of_splitsAt` and `ef_of_tower`: `v ∈ T` has `e = f = 1` over all its primes in `K'` (from
   the unramifiedness of `K'/F` and the splitting hypothesis) and hence in `L'` as well, by
   multiplicativity of `e` and `f` in the tower `𝓞 F ⊆ 𝓞 K' ⊆ 𝓞 L'` (here `T''` — the primes of
   `K'` above `T` — is what makes the hypothesis on `L'/K'` available).
2. `conjSup_iSup_comap_eq_top`: the conjugates `σ(L')` of `L'` generate `M` over `F`; this is
   the definition of `conjSup` transported into the lattice of intermediate fields of `↥M`.
3. `splitsCompletelyIn_of_algEquiv` and `splitsCompletelyIn_comap`: complete splitting is
   invariant under `F`-algebra isomorphisms, so it transfers from `L'` to each conjugate image
   `σ(L')` and to its copy inside `↥M`.
4. `Work.Tower.Unramified.splitsCompletelyIn_of_iSup_eq_top`: complete splitting ascends from a
   finite family of intermediate fields to its supremum (iterating the compositum theorem
   `Work.Tower.Unramified.compositum_splits_completely_alt`), here applied to the family of
   conjugate images, whose supremum is everything.
5. The conclusion `SplitsAt` is recovered from complete splitting via
   `Work.Tower.Unramified.ef_eq_one_of_splitsCompletelyIn` and `Ideal.inertiaDegIn_eq_inertiaDeg`.

## Main result

* `Work.CFTLib.ConjSup.splitsAt`
-/

open NumberField Work.CFTLib
open scoped Classical nonZeroDivisors

namespace Work.CFTLib.ConjSup

/-! ### The conjugates generate the compositum -/

/-- The conjugates of `L'` (inside `M = conjSup p K' L'`) generate `M`. -/
theorem conjSup_iSup_comap_eq_top (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L'] [NumberField ↥(conjSup p K' L')] :
    (⨆ σ : ↥K' ≃ₐ[F] ↥K',
      (((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom).comap
        (IntermediateField.val (conjSup p K' L')))) = ⊤ := by
  set M := conjSup p K' L' with hM
  set E : (↥K' ≃ₐ[F] ↥K') → IntermediateField F (AlgebraicClosure F) :=
    fun σ => (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom with hE
  have hEsup : M = ⨆ σ, E σ := rfl
  have hfr : (IntermediateField.val M).fieldRange = M := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hmain : (⨆ σ, (E σ).comap (IntermediateField.val M)).map (IntermediateField.val M) = M := by
    rw [IntermediateField.map_iSup]
    conv_rhs => rw [hEsup]
    refine iSup_congr fun σ => ?_
    rw [IntermediateField.map_comap_eq_self (by rw [hfr]; exact le_iSup E σ)]
  have hcomap : M.comap (IntermediateField.val M) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact x.2
  have htop : (⊤ : IntermediateField F ↥M).map (IntermediateField.val M) = M := by
    rw [← hcomap, IntermediateField.map_comap_eq_self (le_of_eq hfr.symm)]
  exact IntermediateField.map_injective (IntermediateField.val M) (by rw [hmain, htop])

/-! ### Transport of complete splitting -/

/-- Complete splitting is invariant under `F`-algebra isomorphisms of number fields. -/
theorem splitsCompletelyIn_of_algEquiv {F L L' : Type} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    [FiniteDimensional F L] [FiniteDimensional F L']
    (e : L ≃ₐ[F] L') (𝔭 : Ideal (𝓞 F)) :
    Work.Tower.SplitsCompletelyIn F L 𝔭 ↔ Work.Tower.SplitsCompletelyIn F L' 𝔭 :=
  ⟨fun h => Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭 e.symm.toAlgHom h,
   fun h => Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭 e.toAlgHom h⟩

/-- Complete splitting descends to the copy `E.comap M.val` of an intermediate field `E` inside a
larger number field `M`. -/
theorem splitsCompletelyIn_comap {F A : Type} [Field F] [NumberField F] [Field A]
    [Algebra F A] {E M : IntermediateField F A} [NumberField ↥E] [NumberField ↥M]
    [FiniteDimensional F ↥E] [FiniteDimensional F ↥M]
    (𝔭 : Ideal (𝓞 F)) (h : Work.Tower.SplitsCompletelyIn F ↥E 𝔭) :
    Work.Tower.SplitsCompletelyIn F ↥(E.comap (IntermediateField.val M)) 𝔭 := by
  haveI : FiniteDimensional F ↥(E.comap (IntermediateField.val M)) :=
    IntermediateField.finiteDimensional_left (E.comap (IntermediateField.val M))
  haveI : NumberField ↥(E.comap (IntermediateField.val M)) :=
    NumberField.of_module_finite F ↥(E.comap (IntermediateField.val M))
  refine Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭 ?_ h
  exact ((IntermediateField.val M).comp (IntermediateField.val
    (E.comap (IntermediateField.val M)))).codRestrict E.toSubalgebra (fun x => x.2)

/-! ### Unramifiedness and splitting in the tower -/

/-- A prime which splits completely in `K'/F` (unramified) has trivial ramification index and
inertia degree over every prime above it. -/
lemma ef_of_splitsAt (F : Type) [Field F] [NumberField F]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    [NumberField ↥K']
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hKunr : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K')
    (hKsplit : CFTLib.SplitsAt F ↥K' T)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∈ T) :
    ∀ P : v.asIdeal.primesOver (𝓞 ↥K'),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
  intro P
  haveI : P.1.IsPrime := P.2.1
  haveI : P.1.LiesOver v.asIdeal := P.2.2
  refine ⟨hKunr P.1 P.2.1, ?_⟩
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 (↥K' ≃ₐ[F] ↥K')]
  exact hKsplit v hv

/-- If `v` splits completely in `K'/F` and every prime of `K'` above `v` splits completely in
`L'/K'` (both extensions unramified), then `v` splits completely in `L'/F`. -/
lemma ef_of_tower (F : Type) [Field F] [NumberField F]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L']
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hKunr : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K')
    (hKsplit : CFTLib.SplitsAt F ↥K' T)
    (hLgal : IsGalois ↥K' ↥L')
    (hLunr : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L')
    (T'' : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K')))
    (hT'' : (∀ v ∈ T'', ∃ u ∈ T, v.asIdeal.LiesOver u.asIdeal) ∧
      (∀ u ∈ T, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K'),
        v.asIdeal.LiesOver u.asIdeal → v ∈ T''))
    (hLsplit : ∀ v ∈ T'', Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L') = 1)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∈ T) :
    ∀ R : v.asIdeal.primesOver (𝓞 ↥L'),
      R.1.ramificationIdx (𝓞 F) = 1 ∧ R.1.inertiaDeg (𝓞 F) = 1 := by
  haveI := hLgal
  intro R
  haveI : R.1.IsPrime := R.2.1
  haveI : R.1.LiesOver v.asIdeal := R.2.2
  set P : Ideal (𝓞 ↥K') := R.1.under (𝓞 ↥K')
  haveI hPpr : P.IsPrime := R.2.1.under (𝓞 ↥K')
  haveI hPlie : P.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot R.1 P v.asIdeal
  haveI hRLP : R.1.LiesOver P := Ideal.over_under R.1
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hPmem : (⟨P, hPpr, hPne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K')) ∈ T'' :=
    hT''.2 v hv ⟨P, hPpr, hPne⟩ hPlie
  have hsplitP : Ideal.inertiaDegIn P (𝓞 ↥L') = 1 := hLsplit ⟨P, hPpr, hPne⟩ hPmem
  have hfRP : R.1.inertiaDeg (𝓞 ↥K') = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg P R.1 (↥L' ≃ₐ[↥K'] ↥L')]
    exact hsplitP
  have heRP : R.1.ramificationIdx (𝓞 ↥K') = 1 := hLunr R.1 R.2.1
  have hfPv : P.inertiaDeg (𝓞 F) = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P (↥K' ≃ₐ[F] ↥K')]
    exact hKsplit v hv
  have hePv : P.ramificationIdx (𝓞 F) = 1 := hKunr P hPpr
  refine ⟨?_, ?_⟩
  · rw [Ideal.ramificationIdx_tower (R := 𝓞 F) P R.1, hePv, heRP, mul_one]
  · rw [Ideal.inertiaDeg_tower (R := 𝓞 F) P R.1, hfPv, hfRP, mul_one]

/-! ### The main theorem -/

theorem splitsAt (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    [NumberField ↥K'] [NumberField ↥L'] [NumberField ↥(conjSup p K' L')]
    (hKunr : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K')
    (hKsplit : CFTLib.SplitsAt F ↥K' T)
    (hLgal : IsGalois ↥K' L')
    (hLunr : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L')
    (T'' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K')))
    (hT'' : (∀ v ∈ T'', ∃ u ∈ T, v.asIdeal.LiesOver u.asIdeal) ∧
      (∀ u ∈ T, ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K'),
        v.asIdeal.LiesOver u.asIdeal → v ∈ T''))
    (hLsplit : ∀ v ∈ T'', Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers ↥L') = 1)
    (hMgal : IsGalois F ↥(conjSup p K' L')) :
    CFTLib.SplitsAt F ↥(conjSup p K' L') T := by
  haveI := hLgal
  haveI := hMgal
  haveI : Nonempty (↥K' ≃ₐ[F] ↥K') := ⟨1⟩
  intro v hv
  -- `v` splits completely in `L'/F`
  have hL' : ∀ R : v.asIdeal.primesOver (𝓞 ↥L'),
      R.1.ramificationIdx (𝓞 F) = 1 ∧ R.1.inertiaDeg (𝓞 F) = 1 :=
    ef_of_tower F K' L' T hKunr hKsplit hLgal hLunr T'' hT'' hLsplit hv
  have hsplitL' : Work.Tower.SplitsCompletelyIn F ↥L' v.asIdeal :=
    Work.Tower.Unramified.splitsCompletelyIn_of_NF v.isPrime v.ne_bot
      (Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia v.isPrime hL')
  -- each conjugate image inside `M` splits completely at `v`
  have hfam : ∀ σ : ↥K' ≃ₐ[F] ↥K',
      Work.Tower.SplitsCompletelyIn F
        ↥(((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom).comap
          (IntermediateField.val (conjSup p K' L'))) v.asIdeal := by
    intro σ
    set N : IntermediateField F (AlgebraicClosure F) :=
      (L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom with hN
    have e₁ : ↥L' ≃ₐ[F] ↥N :=
      IntermediateField.intermediateFieldMap (σ.liftNormal (AlgebraicClosure F))
        (L'.restrictScalars F)
    haveI hfinN : FiniteDimensional F ↥N := LinearEquiv.finiteDimensional e₁.toLinearEquiv
    haveI hnfN : NumberField ↥N := NumberField.of_module_finite F ↥N
    have hNsplit : Work.Tower.SplitsCompletelyIn F ↥N v.asIdeal :=
      (splitsCompletelyIn_of_algEquiv e₁ v.asIdeal).mp hsplitL'
    exact splitsCompletelyIn_comap (E := N) (M := conjSup p K' L') v.asIdeal hNsplit
  have hsup := conjSup_iSup_comap_eq_top F p K' L'
  have hM : Work.Tower.SplitsCompletelyIn F ↥(conjSup p K' L') v.asIdeal :=
    Work.Tower.Unramified.splitsCompletelyIn_of_iSup_eq_top
      (E := fun σ : ↥K' ≃ₐ[F] ↥K' =>
        ((L'.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom).comap
          (IntermediateField.val (conjSup p K' L')))
      v.isPrime v.ne_bot hsup hfam
  -- convert back to the inertia degree condition
  have hef := Work.Tower.Unramified.ef_eq_one_of_splitsCompletelyIn v.ne_bot hM
  obtain ⟨Q⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 ↥(conjSup p K' L'))))
  haveI : Q.1.IsPrime := Q.2.1
  haveI : Q.1.LiesOver v.asIdeal := Q.2.2
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q.1
    (↥(conjSup p K' L') ≃ₐ[F] ↥(conjSup p K' L'))]
  exact (hef Q).2

end Work.CFTLib.ConjSup
