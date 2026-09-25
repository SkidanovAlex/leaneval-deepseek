import Mathlib
import Submission.Commons.NumberTheory.RamificationInertia.ramificationIdx_one_sup

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.RamificationInertia

open NumberField

/-- **Transport of the unramifiedness statement across an equality of intermediate fields.**

If `L = M` as intermediate fields of `AlgebraicClosure F` and every prime of `𝓞 ↥L` over a prime
`𝔭 ≠ ⊥` of `𝓞 F` has ramification index `1`, then the same holds for `𝓞 ↥M`.

Proof: the algebra equivalence `↥L ≃ₐ[F] ↥M` induces an `𝓞 F`-algebra equivalence
`𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥M` (`RingOfIntegers.mapAlgEquiv`), along which the ramification index is
invariant (`ramificationIdx_comap_algEquiv`). -/
theorem ramificationIdx_one_intermediateField_eq {F : Type*} [Field F] [NumberField F]
    {L M : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F L]
    [FiniteDimensional F M] (hLM : L = M)
    (hL : ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥L)),
      𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥L) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1) :
    ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥M)),
      𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥M) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  intro 𝔭 𝔓 h𝔭 h𝔭ne h𝔓
  obtain ⟨h𝔓prime, h𝔓lies⟩ := h𝔓
  haveI : 𝔓.IsPrime := h𝔓prime
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  haveI : NumberField ↥M := NumberField.of_module_finite F ↥M
  let e : ↥L ≃ₐ[F] ↥M := IntermediateField.equivOfEq hLM
  let φ : 𝓞 ↥L ≃ₐ[𝓞 F] 𝓞 ↥M := RingOfIntegers.mapAlgEquiv e
  have htrans : (𝔓.comap φ).ramificationIdx (𝓞 F) = 𝔓.ramificationIdx (𝓞 F) :=
    ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ 𝔓
  haveI : (𝔓.comap φ).IsPrime := inferInstance
  haveI : (𝔓.comap φ).LiesOver 𝔭 := Ideal.comap_liesOver 𝔓 𝔭 φ
  rw [← htrans]
  exact hL 𝔭 (𝔓.comap φ) h𝔭 h𝔭ne ⟨inferInstance, inferInstance⟩

/-- The base case `L = ⊥`: the trivial extension `F/F` has ramification index `1` at every
nonzero prime.  After transporting along `𝓞 ↥⊥ ≃ₐ[𝓞 F] 𝓞 F` this is the statement that a prime
`Q` of `𝓞 F` lying over `𝔭` is `𝔭` itself, whose ramification index over `𝓞 F` is `1`. -/
theorem ramificationIdx_one_bot {F : Type*} [Field F] [NumberField F] :
    ∀ (𝔭 : Ideal (RingOfIntegers F))
      (𝔓 : Ideal (RingOfIntegers ↥(⊥ : IntermediateField F (AlgebraicClosure F)))),
      𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(⊥ : IntermediateField F (AlgebraicClosure F))) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  intro 𝔭 𝔓 h𝔭 h𝔭ne h𝔓
  obtain ⟨h𝔓prime, h𝔓lies⟩ := h𝔓
  haveI : 𝔓.IsPrime := h𝔓prime
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lies
  haveI : NumberField ↥(⊥ : IntermediateField F (AlgebraicClosure F)) :=
    NumberField.of_module_finite F _
  let φ : 𝓞 ↥(⊥ : IntermediateField F (AlgebraicClosure F)) ≃ₐ[𝓞 F] 𝓞 F :=
    RingOfIntegers.mapAlgEquiv (IntermediateField.botEquiv F (AlgebraicClosure F))
  have htrans : (𝔓.comap φ.symm).ramificationIdx (𝓞 F) = 𝔓.ramificationIdx (𝓞 F) :=
    ramificationIdx_comap_algEquiv 𝔭 h𝔭ne φ.symm 𝔓
  haveI : (𝔓.comap φ.symm).IsPrime := inferInstance
  haveI : (𝔓.comap φ.symm).LiesOver 𝔭 := Ideal.comap_liesOver 𝔓 𝔭 φ.symm
  rw [← htrans]
  have hEq : 𝔓.comap φ.symm = 𝔭 := by
    have hover : 𝔭 = (𝔓.comap φ.symm).under (𝓞 F) := Ideal.LiesOver.over
    rw [Ideal.under_def] at hover
    simpa using hover.symm
  rw [hEq]
  exact Ideal.ramificationIdx_eq_one 𝔭 (𝓞 F)

open NumberField in
/-- **Unramifiedness at finite primes is preserved by finite composita.**

Let `f : ι → IntermediateField F (AlgebraicClosure F)` be finite-dimensional Galois intermediate
fields over a number field `F` and let `s` be a finite set of indices.  If every prime of each
`𝓞 ↥(f i)` over a prime `𝔭` of `𝓞 F` has ramification index `1`, then so does every prime of
`𝓞 ↥(⨆ i ∈ s, f i)` over `𝔭`.

Proof: induction on the Finset using
`Commons.NumberTheory.RamificationInertia.ramificationIdx_one_sup` (in the empty case use that
`↥(⨆ i ∈ ∅, f i) = ↥⊥ ≃ₐ[F] F`); note `⨆ i ∈ insert a s, f i = f a ⊔ ⨆ i ∈ s, f i`. -/
theorem ramificationIdx_one_iSup_finset {F : Type*} [Field F] [NumberField F] {ι : Type*}
    (s : Finset ι) (f : ι → IntermediateField F (AlgebraicClosure F))
    [∀ i, FiniteDimensional F ↥(f i)] [∀ i, IsGalois F ↥(f i)]
    (h : ∀ i, ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥(f i))),
      𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(f i)) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1) :
    ∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥(⨆ i ∈ s, f i))),
      𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(⨆ i ∈ s, f i)) →
      𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  classical
  let P : Finset ι → Prop := fun s =>
    IsGalois F ↥(⨆ i ∈ s, f i) ∧
      (∀ (𝔭 : Ideal (RingOfIntegers F)) (𝔓 : Ideal (RingOfIntegers ↥(⨆ i ∈ s, f i))),
        𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔓 ∈ 𝔭.primesOver (RingOfIntegers ↥(⨆ i ∈ s, f i)) →
        𝔓.ramificationIdx (RingOfIntegers F) = 1)
  have hP : ∀ s, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        constructor
        · have hbot : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ := by simp
          rw [hbot]
          infer_instance
        · have hbot : (⨆ i ∈ (∅ : Finset ι), f i) = (⊥ : IntermediateField F (AlgebraicClosure F)) :=
            by simp
          exact ramificationIdx_one_intermediateField_eq hbot.symm ramificationIdx_one_bot
    | insert a t ha ih =>
        obtain ⟨ihGal, ihRam⟩ := ih
        have hsup : (⨆ i ∈ insert a t, f i) = f a ⊔ ⨆ i ∈ t, f i := by
          rw [← Finset.sup_eq_iSup, Finset.sup_insert, Finset.sup_eq_iSup]
        constructor
        · rw [hsup]
          haveI : IsGalois F ↥(⨆ i ∈ t, f i) := ihGal
          infer_instance
        · have hsup' : f a ⊔ ⨆ i ∈ t, f i = ⨆ i ∈ insert a t, f i := hsup.symm
          haveI : IsGalois F ↥(⨆ i ∈ t, f i) := ihGal
          exact ramificationIdx_one_intermediateField_eq hsup'
            (ramificationIdx_one_sup (f a) (⨆ i ∈ t, f i) (h a) ihRam)
  exact (hP s).2

end Commons.NumberTheory.RamificationInertia
