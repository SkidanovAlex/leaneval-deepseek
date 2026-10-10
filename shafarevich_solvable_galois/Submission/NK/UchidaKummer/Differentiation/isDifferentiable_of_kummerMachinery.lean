import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.NK.UchidaKummer.Differentiation.kummerStep_multiPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Differentiation

open IsDedekindDomain

/-! ## The primes of `𝓞 L` above a prime of `𝓞 K` as a `Finset` -/

/-- The (finite) set of primes of `𝓞 L` lying over a nonzero prime `p` of `𝓞 K`, as a `Finset`. -/
noncomputable def primesOverFinset {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (p : NK.Chebotarev.PrimeIdeal K) :
    Finset (NK.Chebotarev.PrimeIdeal L) := by
  classical
  have hfin : (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver p.asIdeal p.isPrime p.ne_bot
  letI : Fintype ↥(p.asIdeal.primesOver (NumberField.RingOfIntegers L)) := hfin.fintype
  exact Finset.univ.image (fun q : ↥(p.asIdeal.primesOver (NumberField.RingOfIntegers L)) =>
    ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q.2⟩)

theorem mem_primesOverFinset {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {p : NK.Chebotarev.PrimeIdeal K}
    {q : NK.Chebotarev.PrimeIdeal L} :
    q ∈ primesOverFinset p ↔ q.asIdeal.LiesOver p.asIdeal := by
  classical
  have hfin : (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver p.asIdeal p.isPrime p.ne_bot
  letI : Fintype ↥(p.asIdeal.primesOver (NumberField.RingOfIntegers L)) := hfin.fintype
  rw [primesOverFinset]
  constructor
  · intro h
    obtain ⟨I, -, hI⟩ := Finset.mem_image.mp h
    have h1 : I.1 = q.asIdeal := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hI
    rw [← h1]
    exact I.2.2
  · intro h
    exact Finset.mem_image.mpr ⟨⟨q.asIdeal, q.isPrime, h⟩, Finset.mem_univ _,
      IsDedekindDomain.HeightOneSpectrum.ext rfl⟩

/-! ## The trivial extension

The field `K` itself, viewed inside `K'` as the bottom intermediate field, has local degree `1`
at every prime: `⊥ = K(1^{1/ℓ})` is a Kummer field whose radical `1` is a local `ℓ`-th power. -/

theorem localDeg_eq_one_of_bot {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (Q : NK.Chebotarev.PrimeIdeal ↥(⊥ : IntermediateField K K'))
    (hQ : Q.asIdeal.LiesOver 𝔭.asIdeal) : NK.UchidaKummer.localDeg Q 𝔭 = 1 := by
  have hL : (⊥ : IntermediateField K K') =
      NK.LocalAnabelian.kummerField (K' := K') ℓ (1 : Kˣ) :=
    (NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := K') ℓ hℓ hζ
      (one_mem _)).symm
  haveI : FiniteDimensional K (⊥ : IntermediateField K K') := inferInstance
  haveI : NumberField ↥(⊥ : IntermediateField K K') :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  refine (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := K) (K' := K') ℓ hℓ hζ
    (1 : Kˣ) ⊥ hL 𝔭).mpr ?_ Q hQ
  exact ⟨1, by simp⟩

/-! ## A prime of the intermediate field below a prime of the overfield -/

/-- Given a prime `Q` of a number field `G` lying over a prime `𝔭` of a subfield `K`, and an
intermediate field `F` (`K ⊆ F ⊆ G`), there is a prime `P` of `F` with `Q` over `P` and `P`
over `𝔭`: the *contraction* `Q.asIdeal.under (𝓞 F)` of `Q`. -/
theorem exists_liesUnder_of_liesOver {K F G : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Field G] [NumberField G] [Algebra K F] [Algebra F G] [Algebra K G]
    [IsScalarTower K F G] (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (Q : NK.Chebotarev.PrimeIdeal G) (hQ : Q.asIdeal.LiesOver 𝔭.asIdeal) :
    ∃ P : NK.Chebotarev.PrimeIdeal F, Q.asIdeal.LiesOver P.asIdeal ∧
      P.asIdeal.LiesOver 𝔭.asIdeal := by
  haveI : Q.asIdeal.LiesOver (𝔭.asIdeal) := hQ
  haveI hover : Q.asIdeal.LiesOver (Q.asIdeal.under (NumberField.RingOfIntegers F)) :=
    Ideal.over_under Q.asIdeal
  have hUnder : (Q.asIdeal.under (NumberField.RingOfIntegers F)).LiesOver 𝔭.asIdeal :=
    Ideal.LiesOver.tower_bot Q.asIdeal (Q.asIdeal.under (NumberField.RingOfIntegers F)) 𝔭.asIdeal
  haveI := hUnder
  have hprime : (Q.asIdeal.under (NumberField.RingOfIntegers F)).IsPrime :=
    Ideal.isPrime_of_liesOver Q.asIdeal (Q.asIdeal.under (NumberField.RingOfIntegers F))
  have hne : (Q.asIdeal.under (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot
      (Q.asIdeal.under (NumberField.RingOfIntegers F))
  exact ⟨⟨_, hprime, hne⟩, Ideal.over_under Q.asIdeal, hUnder⟩

/-! ## A primitive `ℓ`-th root of unity in `K` -/

/-- The Kummer machinery, applied to the bottom intermediate field `K ⊆ K'`, exhibits a
primitive `ℓ`-th root of unity in `K` itself (transporting along `↥⊥ ≅ K`). -/
theorem exists_isPrimitiveRoot_of_machinery {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hmach : NK.UchidaKummer.HasKummerMachinery K K' ℓ) :
    ∃ ζ : K, IsPrimitiveRoot ζ ℓ := by
  haveI hfin0 : FiniteDimensional K (⊥ : IntermediateField K K') := inferInstance
  have hNF0 : NumberField ↥(⊥ : IntermediateField K K') :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  have hsep0 : IsSepClosure ↥(⊥ : IntermediateField K K') K' :=
    ⟨IsSepClosure.sep_closed K, inferInstance⟩
  obtain ⟨ζ', hζ'⟩ := (hmach ⊥ hfin0 hNF0 hsep0).1
  obtain ⟨y, hy⟩ := Set.mem_range.mp
    (IntermediateField.mem_bot.mp (show (ζ'.1 : K') ∈ (⊥ : IntermediateField K K') from ζ'.2))
  refine ⟨y, ?_⟩
  have h1 : IsPrimitiveRoot ((ζ' : K')) ℓ :=
    hζ'.map_of_injective (f := algebraMap ↥(⊥ : IntermediateField K K') K')
      (algebraMap ↥(⊥ : IntermediateField K K') K').injective
  have h2 : IsPrimitiveRoot (algebraMap K K' y) ℓ := by
    rw [hy]
    exact h1
  exact h2.of_map_of_injective (f := algebraMap K K') (algebraMap K K').injective

/-! ## The differentiation lemma of §5

We produce, for every finite list `𝔭 : Fin n → PrimeIdeal K` of primes and every prescription
`a : Fin n → ℕ`, a finite extension `L / K` inside `K'` whose local degree at `𝔭 i` is `ℓ ^ a i`.

The proof is the *tower* induction of §5, run with the Kummer machinery over **every** finite
intermediate field.  Writing `b` for the exponent already achieved at the current field `M` and
`N` for a bound on the remaining deficit `a i - b i`, one Kummer step multiplies the local degree
at *every* prime over every index `i` with `b i < a i` by `ℓ`, and keeps the local degree `1` at
every prime over every index `i` with `b i = a i`; the maximal deficit therefore drops by one, so
the induction terminates.  The local degrees of the tower `K ⊆ M ⊆ M(β^{1/ℓ})` are computed with
`localDeg_tower`, in the *nested* presentation `↥M ⊆ ↥E` of the two fields, where all the
tower instances are canonical. -/
theorem mainAux {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hmach : NK.UchidaKummer.HasKummerMachinery K K' ℓ) :
    ∀ N : ℕ, ∀ (n : ℕ) (𝔭 : Fin n → NK.Chebotarev.PrimeIdeal K) (a b : Fin n → ℕ),
      Function.Injective 𝔭 → (∀ i, b i ≤ a i) → (∀ i, a i ≤ b i + N) →
      ∀ (M : IntermediateField K K') (hMfin : FiniteDimensional K M) (hMNF : NumberField ↥M),
        (∀ i, ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver (𝔭 i).asIdeal →
          NK.UchidaKummer.localDeg Q (𝔭 i) = ℓ ^ b i) →
        ∃ (M' : IntermediateField K K') (_ : FiniteDimensional K M') (_ : NumberField ↥M'),
          ∀ i, ∀ Q' : NK.Chebotarev.PrimeIdeal ↥M', Q'.asIdeal.LiesOver (𝔭 i).asIdeal →
            NK.UchidaKummer.localDeg Q' (𝔭 i) = ℓ ^ a i := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n 𝔭 a b h𝔭 hba hab M hMfin hMNF hMinv
    classical
    haveI := hMfin
    haveI := hMNF
    rcases Nat.eq_zero_or_pos N with hN | hN
    · -- no deficit left: `b = a` and the current field works
      subst hN
      have hEq : b = a := funext fun i => le_antisymm (hba i) (by have := hab i; omega)
      subst hEq
      exact ⟨M, hMfin, hMNF, hMinv⟩
    · obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      -- the indices whose exponent has not been reached
      set R : Finset (Fin n) := Finset.univ.filter (fun i => b i < a i) with hRdef
      by_cases hR : R = ∅
      · -- nothing to do
        have hEq : b = a := funext fun i => by
          have h1 := hba i
          have h2 : ¬ (b i < a i) := by
            intro hlt
            have hmem : i ∈ R := by
              rw [hRdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩
            rw [hR] at hmem
            simpa using hmem
          omega
        subst hEq
        exact ⟨M, hMfin, hMNF, hMinv⟩
      · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hR
        haveI hMsep : IsSepClosure ↥M K' :=
          ⟨IsSepClosure.sep_closed K, inferInstance⟩
        obtain ⟨ζ, hζ⟩ := (hmach M hMfin hMNF hMsep).1
        have hsurjM := (hmach M hMfin hMNF hMsep).2.1
        have hnonpowM := (hmach M hMfin hMNF hMsep).2.2.1
        have hdichM := (hmach M hMfin hMNF hMsep).2.2.2
        -- the primes to be raised, and those to be kept split
        set RM : Finset (NK.Chebotarev.PrimeIdeal ↥M) :=
          R.biUnion (fun i => primesOverFinset (𝔭 i)) with hRMdef
        set SM : Finset (NK.Chebotarev.PrimeIdeal ↥M) :=
          (Finset.univ.filter (fun i => ¬ b i < a i)).biUnion
            (fun i => primesOverFinset (𝔭 i)) with hSMdef
        have hRMmem : ∀ i ∈ R, ∀ P : NK.Chebotarev.PrimeIdeal ↥M,
            P.asIdeal.LiesOver (𝔭 i).asIdeal → P ∈ RM := by
          intro i hi P hP
          rw [hRMdef, Finset.mem_biUnion]
          exact ⟨i, hi, by rw [mem_primesOverFinset]; exact hP⟩
        have hSMmem : ∀ i, ¬ (b i < a i) → ∀ P : NK.Chebotarev.PrimeIdeal ↥M,
            P.asIdeal.LiesOver (𝔭 i).asIdeal → P ∈ SM := by
          intro i hi P hP
          rw [hSMdef, Finset.mem_biUnion]
          exact ⟨i, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩,
            by rw [mem_primesOverFinset]; exact hP⟩
        have hdisj : Disjoint RM SM := by
          rw [Finset.disjoint_left]
          intro P hP1 hP2
          rw [hRMdef, Finset.mem_biUnion] at hP1
          obtain ⟨i, hi, hPi⟩ := hP1
          rw [hSMdef, Finset.mem_biUnion] at hP2
          obtain ⟨j, hj, hPj⟩ := hP2
          rw [hRdef, Finset.mem_filter] at hi
          rw [Finset.mem_filter] at hj
          rw [mem_primesOverFinset] at hPi hPj
          have hseq : 𝔭 i = 𝔭 j :=
            IsDedekindDomain.HeightOneSpectrum.ext (hPi.over.trans hPj.over.symm)
          have hij : i = j := h𝔭 hseq
          subst hij
          exact absurd hi.2 hj.2
        have hRneM : RM.Nonempty := by
          obtain ⟨i, hi⟩ := hRne
          have hlt : b i < a i := by
            have h' := hi
            rw [hRdef, Finset.mem_filter] at h'
            exact h'.2
          obtain ⟨P, hP⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
            (K := K) (L := ↥M) (𝔭 i)
          exact ⟨P, hRMmem i hi P hP⟩
        -- one Kummer step over the current field
        obtain ⟨E, hEfin, hENF, hstepR, hstepS⟩ :=
          kummerStep_multiPrime (B := ↥M) (K' := K') ℓ hℓ hζ RM SM (RM ∪ SM) hRneM
            (fun 𝔮 _ => Finset.mem_union.mpr (Or.inl ‹𝔮 ∈ RM›))
            (fun 𝔮 _ => Finset.mem_union.mpr (Or.inr ‹𝔮 ∈ SM›))
            (fun 𝔮 h1 h2 => Finset.disjoint_left.mp hdisj h1 h2)
            (hsurjM (RM ∪ SM)) (fun 𝔮 _ => hnonpowM 𝔮) hdichM
        -- the new current field, viewed over `K`
        haveI hENF' : NumberField ↥(E.restrictScalars K) := inferInstanceAs (NumberField ↥E)
        haveI hEfin' : FiniteDimensional K ↥(E.restrictScalars K) := by
          haveI := hMfin
          haveI := hEfin
          exact FiniteDimensional.trans K ↥M ↥E
        -- the new exponents
        have hb'le : ∀ i, (if b i < a i then b i + 1 else b i) ≤ a i := by
          intro i
          by_cases h : b i < a i
          · rw [if_pos h]; have := hba i; omega
          · rw [if_neg h]; exact hba i
        have hb'a : ∀ i, a i ≤ (if b i < a i then b i + 1 else b i) + N' := by
          intro i
          by_cases h : b i < a i
          · rw [if_pos h]; have := hab i; omega
          · rw [if_neg h]; have h1 := hab i; have h2 := hba i; omega
        -- the invariant at the new field, in the nested presentation `↥M ⊆ ↥E`
        have hInner : ∀ i, ∀ Q' : NK.Chebotarev.PrimeIdeal ↥E,
            Q'.asIdeal.LiesOver (𝔭 i).asIdeal →
            NK.UchidaKummer.localDeg Q' (𝔭 i) =
              ℓ ^ (if b i < a i then b i + 1 else b i) := by
          intro i Q' hQ'
          obtain ⟨P, hQP, hP⟩ :=
            exists_liesUnder_of_liesOver (K := K) (F := ↥M) (G := ↥E) (𝔭 i) Q' hQ'
          rw [NK.UchidaKummer.API.localDeg_tower (𝔭 i) P Q' hP hQP]
          by_cases h : b i < a i
          · have hiR : i ∈ R := by
              rw [hRdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
            rw [hstepR P (hRMmem i hiR P hP) Q' hQP, hMinv i P hP, if_pos h, pow_succ']
          · rw [hstepS P (hSMmem i h P hP) Q' hQP, hMinv i P hP, if_neg h, one_mul]
        -- recurse with the new field and the new exponents
        obtain ⟨M', hM'fin, hM'NF, hM'⟩ :=
          ih N' (by omega) n 𝔭 a (fun i => if b i < a i then b i + 1 else b i) h𝔭 hb'le hb'a
            (E.restrictScalars K) hEfin' hENF' hInner
        exact ⟨M', hM'fin, hM'NF, hM'⟩

theorem isDifferentiable_of_kummerMachinery (K : Type*) [Field K] [NumberField K]
    (K' : Type*) [Field K'] [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hmach : NK.UchidaKummer.HasKummerMachinery K K' ℓ) :
    NK.UchidaKummer.IsDifferentiable K K' ℓ := by
  intro n 𝔭 h𝔭 a
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_machinery (K := K) (K' := K') ℓ hℓ hmach
  haveI hfin0 : FiniteDimensional K (⊥ : IntermediateField K K') := inferInstance
  have hNF0 : NumberField ↥(⊥ : IntermediateField K K') :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  have hinv : ∀ i, ∀ Q : NK.Chebotarev.PrimeIdeal ↥(⊥ : IntermediateField K K'),
      Q.asIdeal.LiesOver (𝔭 i).asIdeal →
        NK.UchidaKummer.localDeg Q (𝔭 i) = ℓ ^ (fun _ : Fin n => 0) i := by
    intro i Q hQ
    simpa using localDeg_eq_one_of_bot (K := K) (K' := K') ℓ hℓ hζ (𝔭 i) Q hQ
  obtain ⟨M', hM'fin, hM'NF, hM'⟩ :=
    mainAux (K := K) (K' := K') ℓ hℓ hmach (Finset.univ.sum a) n 𝔭 a (fun _ => 0) h𝔭
      (fun i => Nat.zero_le _)
      (fun i => by
        have h := Finset.single_le_sum (f := a) (fun j _ => Nat.zero_le (a j))
          (Finset.mem_univ i)
        simpa using h)
      ⊥ hfin0 hNF0 hinv
  exact ⟨M', hM'fin, hM'NF, hM'⟩

end NK.UchidaKummer.Differentiation
