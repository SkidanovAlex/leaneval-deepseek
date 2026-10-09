import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` §4 recursion: the invariant, the step and its existence

`PreTwo` is the prefix form of the invariant of the `p = 2` recursion of Schmidt--Wingberg §4 (see
`ZDataTwo/NOTE_two_recursion_DESIGN.md` §2): the escape primes `Q_m = (f m).1` are finite, split in
`Λ` and pairwise `k`- and `K`-fresh; the classes `z_m = χ_{b_m}` realise the prescribed datum of
`TwoRec.prescDatum` on the local groups of the blocks of `T_m = TwoRec.TBlock S f m`, kill the
involutions, are unramified outside the `K`-classes of `T_m` and of `Q_m`, and are normalised at
`Q_m` (odd valuation).

`PreTwo_step` is the one-stage step (the oracle `P2Core.escapeStepNormalised` applied at
`T = TBlock S f n` with the datum `prescDatum`), and `preTwoExists` is the existence of a history
satisfying the invariant at every prefix.

The one-stage step and the existence of a history satisfying the invariant at every prefix are
delegated to
`Submission/Work/SSGRoute/ZDataTwo/TwoRec/PreTwo_step.lean` and
`Submission/Work/SSGRoute/ZDataTwo/TwoRec/preTwoExists.lean`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The escape oracle of the `p = 2` §4 recursion** (`= Work.SSGRoute.P2Core.escapeStepNormalised`,
proved): from a datum `(g,h)` on a pairwise non-`K`-conjugate place set `T` covering the ramified and
`2`-adic places, produce an escape prime `Q` outside the `K`- and `k`-classes of `T`, split in `Λ`,
and a class `b ∈ Kˣ` whose Kummer cochain realises `g + h` on the local groups of `T`, kills the
involutions, is confined to `T` and its own `Q`, and is normalised at `Q` (odd valuation). -/
def Oracle (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) : Prop :=
  ∀ (T : Finset (ValuationSubring Ω)), (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
    (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B) →
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) →
    ∀ (g : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y) →
      SSGRoute.IsLocConstOn K.fixingSubgroup g →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0) →
      ∀ (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2),
        (∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
          ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y) →
        (∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
          ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) →
        (∀ A ∈ T,
          (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
            SSGRoute.IsSplitIn k Λ A) →
        (∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) →
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0) →
        (∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) →
        ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
          SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
          (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
          (∀ A ∈ T, ¬ SSGRoute.IsConjPlace k A Q) ∧
          (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
            Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
          (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
            Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
            (¬ Work.SSGRoute.gesKConj K Q B) →
            ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
          (∃ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
            Q.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
            Odd (FractionalIdeal.count ↥K 𝔮
              (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
                (b : ↥K))))

/-- **A history of the `p = 2` §4 recursion**: the sequence of escape primes with elements. -/
structure St where
  /-- the sequence of escape primes with elements -/
  f : ℕ → (ValuationSubring Ω × (↥K)ˣ)

/-- **The prefix invariant of the `p = 2` §4 recursion.** -/
noncomputable def PreTwo (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2) (n : ℕ)
    (s : St (K := K)) : Prop :=
  (∀ m < n, SSGRoute.IsFinPlace k ((s.f m).1)) ∧
  (∀ m < n, SSGRoute.IsSplitIn k Λ ((s.f m).1)) ∧
  (∀ m l : ℕ, m < l → l < n → ¬ Work.SSGRoute.gesKConj K ((s.f m).1) ((s.f l).1)) ∧
  (∀ m l : ℕ, m < l → l < n → ¬ SSGRoute.IsConjPlace k ((s.f m).1) ((s.f l).1)) ∧
  (∀ m < n, ∀ A ∈ TBlock S s.f m, ¬ Work.SSGRoute.gesKConj K A ((s.f m).1)) ∧
  (∀ m < n, ∀ A ∈ TBlock S s.f m, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ
        = y σ + prescDatum (K := K) ζ hζ hζK S y s.f m A σ) ∧
  (∀ m < n, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 c = 0) ∧
  (∀ m < n, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ TBlock S s.f m, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K ((s.f m).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = 0) ∧
  (∀ m < n, ∃ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      ((s.f m).1).comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      Odd (FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((s.f m).2 : ↥K))))


/-- **The prefix invariant depends only on the first `n` entries of the history.** -/
theorem PreTwo_congr {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2} {n : ℕ}
    {s s' : St (k := k) (Ω := Ω) (K := K)} (h : ∀ i < n, s'.f i = s.f i)
    (hs : PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    PreTwo (K := K) Λ ζ hζ hζK S y n s' := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  have hT : ∀ m < n, TBlock S s'.f m = TBlock S s.f m := fun m hm =>
    TBlock_congr (K := K) (fun i hi => h i (lt_trans hi hm))
  have hP : ∀ m < n, prescDatum (K := K) ζ hζ hζK S y s'.f m
      = prescDatum (K := K) ζ hζ hζK S y s.f m := fun m hm =>
    prescDatum_congr (K := K) (fun i hi => h i (lt_trans hi hm))
  refine ⟨fun m hm => ?_, fun m hm => ?_, fun m l hml hl => ?_, fun m l hml hl => ?_,
    fun m hm => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩
  · rw [h m hm]; exact h0 m hm
  · rw [h m hm]; exact h1 m hm
  · rw [h m (lt_trans hml hl), h l hl]; exact h2 m l hml hl
  · rw [h m (lt_trans hml hl), h l hl]; exact h3 m l hml hl
  · rw [hT m hm, h m hm]; exact h4 m hm
  · rw [hT m hm, h m hm, hP m hm]; exact h5 m hm
  · rw [h m hm]; exact h6 m hm
  · rw [h m hm]
    intro B hB hBT hQB σ hσK hσI
    refine h7 m hm B hB ?_ ?_ σ hσK hσI
    · intro A hA hc
      refine hBT A ?_ hc
      rw [← hT m hm] at hA
      exact hA
    · exact hQB
  · rw [h m hm]; exact h8 m hm


/-- **The paper's Claim for one escape class.**  For every `σ ∉ G_K` whose restriction to `K` is an
involution of `Gal(K|k)`, the Kummer cochain of `b` vanishes on the local group of the sibling
`σ • Q` (Schmidt--Wingberg, p. 16). -/
def ClaimClause (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (Q : ValuationSubring Ω) (b : (↥K)ˣ) : Prop :=
  ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
    ∀ u ∈ SSGRoute.decomp k (σ • Q) ⊓ K.fixingSubgroup,
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b u = 0

end Work.SSGRoute.ZDataTwo.TwoRec
