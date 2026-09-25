import Mathlib
import Submission.NK.IndecomposedDeep.Corrected
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
import Submission.NK.LocalInputs.ResidueChar.primeBelow_eq_of_liesOver
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open IsDedekindDomain.HeightOneSpectrum

/-! ## Auxiliary lemmas -/

/-- `CharP` is transported along a ring isomorphism. -/
private theorem charP_of_ringEquiv {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [Nontrivial R] [Nontrivial S] (e : R ≃+* S) {p : ℕ} (hp : p.Prime) (h : CharP R p) :
    CharP S p := by
  rw [CharP.charP_iff_prime_eq_zero hp] at h ⊢
  rw [← map_natCast (e : R →+* S) p, h, map_zero]

/-- The indicator of `ζ_p ∈ κ` is a field-theoretic invariant. -/
private theorem zetaIndicator_eq_of_ringEquiv {F G : Type*} [Field F] [Field G] {p : ℕ}
    (e : F ≃+* G) :
    NK.LocalInputs.zetaIndicator p F = NK.LocalInputs.zetaIndicator p G := by
  unfold NK.LocalInputs.zetaIndicator
  by_cases hF : ∃ ζ : F, IsPrimitiveRoot ζ p
  · have hG : ∃ ζ : G, IsPrimitiveRoot ζ p := by
      obtain ⟨ζ, hζ⟩ := hF
      exact ⟨e ζ, hζ.map_of_injective e.injective⟩
    rw [if_pos hF, if_pos hG]
  · have hG : ¬ ∃ ζ : G, IsPrimitiveRoot ζ p := by
      rintro ⟨η, hη⟩
      exact hF ⟨e.symm η, hη.map_of_injective e.symm.injective⟩
    rw [if_neg hF, if_neg hG]

/-- The Kummer class group `κˣ/(κˣ)^p` has the same cardinality for isomorphic fields. -/
private theorem kummerGroup_card_eq_of_ringEquiv {F G : Type*} [Field F] [Field G] (p : ℕ)
    (e : F ≃+* G) :
    Nat.card (NK.LocalAnabelian.KummerGroup p F) =
      Nat.card (NK.LocalAnabelian.KummerGroup p G) :=
  NK.LocalInputs.PowerQuotient.natCard_quot_powMonoidHom_eq_of_mulEquiv p
    (Units.mapEquiv e.toMulEquiv)

/-- **The residue characteristic of the completion at a prime of a number field.** -/
private theorem charP_residueField_of_liesOver {K : Type*} [Field K] [NumberField K]
    [Algebra ℚ K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : q.asIdeal.LiesOver P.asIdeal) :
    CharP (IsLocalRing.ResidueField (q.adicCompletionIntegers K))
      (Rat.HeightOneSpectrum.primesEquiv P).1 := by
  have hp : (Rat.HeightOneSpectrum.primesEquiv P).1.Prime :=
    (Rat.HeightOneSpectrum.primesEquiv P).2
  have hquot : CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal)
      (Rat.HeightOneSpectrum.primesEquiv P).1 := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hmem : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈
        P.asIdeal :=
      Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq P _ hp (Subtype.ext rfl)
    have hmem' : ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers K) ∈
        q.asIdeal := by
      rw [← map_natCast (algebraMap (NumberField.RingOfIntegers ℚ)
        (NumberField.RingOfIntegers K)) _]
      show algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)
        ((Rat.HeightOneSpectrum.primesEquiv P).1 : NumberField.RingOfIntegers ℚ) ∈ q.asIdeal
      rw [← Ideal.mem_under, ← h.over]
      exact hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem'
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists q
  exact charP_of_ringEquiv e.symm hp hquot

/-- **The degree-rigidity of `p`-adic fields** (the statement of
`NK.IndecomposedDeep.LocalDegreeRigidity`, unpacked).

Let `M` be a finite extension of the `p`-adic field `α = 𝔮.adicCompletion L`, realised inside a
separable closure of `α`.  If `M` is isomorphic to `α` *as a ring* — no compatibility with the
embeddings is assumed — then `M` is trivial, i.e. `M = ⊥` (equivalently `[M : α] = 1`).

This is the classical statement that the absolute degree `[F : ℚ_p]` of a `p`-adic field `F` is
intrinsic to the field structure.  It is needed to convert Neukirch's local theorem
(`NK.LocalStructure.LocalNUExistence`), which returns an *abstract* ring isomorphism `M ≅ α`, into
the degree statement `M = ⊥`, i.e. into the maximality of decomposition groups
(`Submission/Work/IndecomposedDeep/Corrected.lean`). -/
theorem localDegreeRigidity (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : IntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)))
    [FiniteDimensional (𝔮.adicCompletion L) ↥M]
    (h : Nonempty (↥M ≃+* 𝔮.adicCompletion L)) : M = ⊥ := by
  classical
  -- ## The rational prime `P` below `𝔮`, and the residue characteristic `p`
  let P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    NK.LocalInputs.primeBelow L 𝔮
  have hlies : 𝔮.asIdeal.LiesOver P.asIdeal := NK.LocalInputs.primeBelow_liesOver L 𝔮
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv P).1
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv P).2
  -- ## The `ℚ_p`-algebra structures on `α = L_𝔮` and on `M`
  letI : Algebra (P.adicCompletion ℚ) (𝔮.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap P 𝔮 hlies)
  letI : Algebra (P.adicCompletion ℚ) ↥M :=
    RingHom.toAlgebra ((algebraMap (𝔮.adicCompletion L) ↥M).comp
      (Commons.RingTheory.Henselian.adicCompletionMap P 𝔮 hlies))
  letI : Module (P.adicCompletion ℚ) ↥M := Algebra.toModule
  haveI : IsScalarTower (P.adicCompletion ℚ) (𝔮.adicCompletion L) ↥M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (P.adicCompletion ℚ) (𝔮.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion P 𝔮 hlies
  haveI : Module.Finite (P.adicCompletion ℚ) ↥M :=
    Module.Finite.trans (𝔮.adicCompletion L) ↥M
  -- ## The power-class count of `αˣ`
  have hcharα : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L)) p :=
    charP_residueField_of_liesOver 𝔮 P hlies
  have hαcard : Nat.card (NK.LocalAnabelian.KummerGroup p (𝔮.adicCompletion L)) =
      p ^ (NK.LocalInputs.localDegree L 𝔮 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔮.adicCompletion L)) :=
    NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow 𝔮
      (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hp hcharα)
  -- ## Krasner: `M` is the completion of a number field over `ℚ_p`
  obtain ⟨L', hL'f, hL'nf, hL'a, 𝔮', h𝔮', ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{0, u, u}
      (B := ↥M) P
  -- the `ℚ`-algebra structure on a field is unique: its canonical form is `DivisionRing.toRatAlgebra`
  have hLaeq : hL'a = (DivisionRing.toRatAlgebra : Algebra ℚ L') := Subsingleton.elim _ _
  letI : Algebra (P.adicCompletion ℚ) (𝔮'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap P 𝔮' h𝔮')
  -- ## The power-class count of `L'_{𝔮'}ˣ`
  have hchar' : CharP (IsLocalRing.ResidueField (𝔮'.adicCompletionIntegers L')) p :=
    @charP_residueField_of_liesOver L' hL'f hL'nf hL'a 𝔮' P h𝔮'
  have h'card : Nat.card (NK.LocalAnabelian.KummerGroup p (𝔮'.adicCompletion L')) =
      p ^ (NK.LocalInputs.localDegree L' 𝔮' + 1 +
        NK.LocalInputs.zetaIndicator p (𝔮'.adicCompletion L')) :=
    NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow 𝔮'
      (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮' hp hchar')
  -- ## Transport along the two isomorphisms `M ≅ α` and `M ≅ L'_{𝔮'}`
  have hMα : Nat.card (NK.LocalAnabelian.KummerGroup p ↥M) =
      Nat.card (NK.LocalAnabelian.KummerGroup p (𝔮.adicCompletion L)) :=
    kummerGroup_card_eq_of_ringEquiv p h.some
  have hM' : Nat.card (NK.LocalAnabelian.KummerGroup p ↥M) =
      Nat.card (NK.LocalAnabelian.KummerGroup p (𝔮'.adicCompletion L')) :=
    kummerGroup_card_eq_of_ringEquiv p e.toRingEquiv
  have hδ : NK.LocalInputs.zetaIndicator p (𝔮'.adicCompletion L') =
      NK.LocalInputs.zetaIndicator p (𝔮.adicCompletion L) := by
    rw [← zetaIndicator_eq_of_ringEquiv (p := p) e.toRingEquiv,
      zetaIndicator_eq_of_ringEquiv (p := p) h.some]
  have hpow : p ^ (NK.LocalInputs.localDegree L' 𝔮' + 1 +
        NK.LocalInputs.zetaIndicator p (𝔮'.adicCompletion L')) =
      p ^ (NK.LocalInputs.localDegree L 𝔮 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔮.adicCompletion L)) := by
    rw [← h'card, ← hM', hMα, hαcard]
  have hexp := Nat.pow_right_injective hp.one_lt hpow
  have hdeg : NK.LocalInputs.localDegree L' 𝔮' = NK.LocalInputs.localDegree L 𝔮 := by
    omega
  -- ## `localDegree L' 𝔮'` computed as `[L'_{𝔮'} : ℚ_p]`
  have hld : NK.LocalInputs.localDegree L' 𝔮' =
      𝔮'.asIdeal.ramificationIdx ℤ * 𝔮'.asIdeal.inertiaDeg ℤ :=
    NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔮'
  have hfinEF : Module.finrank (P.adicCompletion ℚ) (𝔮'.adicCompletion L') =
      𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
        𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    (@Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      ℚ L' _ _ _ _ hL'a P 𝔮' h𝔮').symm
  have hram : 𝔮'.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) =
      𝔮'.asIdeal.ramificationIdx ℤ := by
    rw [hLaeq]
    exact NK.LocalInputs.Degree.ramificationIdx_rat_eq 𝔮'.asIdeal
      (IsDedekindDomain.HeightOneSpectrum.ne_bot 𝔮')
  have hinter : 𝔮'.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) =
      𝔮'.asIdeal.inertiaDeg ℤ := by
    rw [hLaeq]
    exact NK.LocalInputs.Degree.inertiaDeg_rat_eq 𝔮'.asIdeal
      (IsDedekindDomain.HeightOneSpectrum.ne_bot 𝔮')
  have hfin' : NK.LocalInputs.localDegree L' 𝔮' =
      Module.finrank (P.adicCompletion ℚ) (𝔮'.adicCompletion L') := by
    rw [hld, hfinEF, hram, hinter]
  -- ## The degrees: `[M : ℚ_p] = [α : ℚ_p]`
  have hfinM : Module.finrank (P.adicCompletion ℚ) ↥M =
      Module.finrank (P.adicCompletion ℚ) (𝔮'.adicCompletion L') :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  have htower : Module.finrank (P.adicCompletion ℚ) ↥M =
      Module.finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) *
        Module.finrank (𝔮.adicCompletion L) ↥M :=
    (Module.finrank_mul_finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) ↥M).symm
  have hldα : NK.LocalInputs.localDegree L 𝔮 =
      Module.finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) := rfl
  have hdpos : 0 < Module.finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) :=
    Module.finrank_pos
  have hkey : Module.finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) *
      Module.finrank (𝔮.adicCompletion L) ↥M =
      Module.finrank (P.adicCompletion ℚ) (𝔮.adicCompletion L) := by
    rw [← htower, hfinM, ← hfin', hdeg, hldα]
  have hn : Module.finrank (𝔮.adicCompletion L) ↥M = 1 :=
    Nat.eq_of_mul_eq_mul_left hdpos (hkey.trans (mul_one _).symm)
  exact (IntermediateField.finrank_eq_one_iff (F := 𝔮.adicCompletion L) (K := M)).mp hn

end NK.IndecomposedDeep
