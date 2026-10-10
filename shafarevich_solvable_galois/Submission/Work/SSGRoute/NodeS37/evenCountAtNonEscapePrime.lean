import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined
import Submission.Work.SSGRoute.NodeS37.evenCountOfKillsInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The divisor of a recursion class has odd part exactly its escape prime

`Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime` is the "(DIV)" fact of the p. 16 computation
(`ACTION_claimOfPreTwo_p16_carve_session39.md` §1): for a history satisfying the `p = 2` recursion
invariant `PreTwo` at all prefixes, every `K`-prime other than the escape prime `𝔮_m := Q_m ∩ K` of
the `m`-th stage divides `b_m` to an **even** order.  Together with `PreTwo`'s clause (9) (`v_{𝔮_m}`
is odd) this says

  `div(b_m) = 𝔮_m · A²`   for a fractional ideal `A`,

which is condition (1) of Schmidt--Wingberg p. 16 in its divisor form, and the input of the whole
`Σ`-computation.

The proof is the strong confinement of the recursion's classes: `χ_{b_m}` kills the inertia of every
finite place that is not `K`-conjugate to `Q_m` (`NodeS37.claimOfPreTwoConfined`), and a Kummer class
killing the inertia of a place has even order there (`NodeS37.evenCountOfKillsInertia`).  The only
point needing a little care is that a place `B` over a `K`-prime `𝔭 ≠ 𝔮_m` is indeed *not*
`K`-conjugate to `Q_m` — because `K`-conjugacy preserves the prime of `K` below a place.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `K`-conjugate places of `Ω` have the same prime of `↥K` below them. -/
theorem comap_eq_of_gesKConj {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) :
    B.comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
  obtain ⟨τ, hτ, hτA⟩ := h
  have hτinv : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτ
  have hpoint : ∀ x : ↥K, τ⁻¹ (algebraMap ↥K Ω x) = algebraMap ↥K Ω x := by
    intro x
    exact (IntermediateField.mem_fixingSubgroup_iff (K := K) τ⁻¹).mp hτinv
      (algebraMap ↥K Ω x) x.2
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hτA,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hs : τ⁻¹ • (algebraMap ↥K Ω x) = (algebraMap ↥K Ω x) := by
    simpa using hpoint x
  rw [hs]

/-- **The divisor of a recursion class has odd part exactly its escape prime.**  For a history
satisfying `PreTwo` at every prefix, every `K`-prime different from the escape prime of the `m`-th
stage occurs in `div(b_m)` with even multiplicity. -/
theorem evenCountAtNonEscapePrime {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (m : ℕ) (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : 𝔭 ≠ Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1)
      ((hs (m + 1)).1 m (Nat.lt_succ_self m))) :
    Even (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((s.f m).2 : ↥K))) := by
  classical
  -- the strong confinement of the stage-`m` class
  have hconf := Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ)
    hKΛ ζ hζ hζK S y hy hyT s hs
  -- a place of `Ω` over `𝔭`
  obtain ⟨B, hBcomap⟩ := NK.ReconstructField.exists_finitePlace_of_prime_level
    (K₁ := k) (K₁' := Ω) K 𝔭
  have hBfin : SSGRoute.IsFinPlace k B.1 := B.2
  -- it is not `K`-conjugate to the escape prime
  have hnotconj : ¬ Work.SSGRoute.gesKConj K ((s.f m).1) B.1 := by
    intro hconj
    have h1 : B.1.comap (algebraMap ↥K Ω) = ((s.f m).1).comap (algebraMap ↥K Ω) :=
      comap_eq_of_gesKConj hconj
    rw [hBcomap, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K)
      ((hs (m + 1)).1 m (Nat.lt_succ_self m))] at h1
    exact h𝔭 (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K) h1)
  -- hence the class kills the inertia there, and has even order at `𝔭`
  refine Work.SSGRoute.NodeS37.evenCountOfKillsInertia (K := K) ζ hζ hζK (s.f m).2 B.1 hBfin
    𝔭 hBcomap ?_
  intro u huK huI
  exact hconf m B.1 hBfin hnotconj u huK huI

/-- **The escape prime occurs to odd order** (`PreTwo`'s clause (9), Schmidt--Wingberg condition
(1)). -/
theorem oddCountAtEscapePrime {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) (m : ℕ) :
    Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1)
        ((hs (m + 1)).1 m (Nat.lt_succ_self m)))
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((s.f m).2 : ↥K))) := by
  obtain ⟨hfin, hsplit, hdisjK, hdisjk, hexcl, hreal, hinv, hconf, hnorm⟩ := hs (m + 1)
  obtain ⟨𝔮, h𝔮comap, h𝔮odd⟩ := hnorm m (Nat.lt_succ_self m)
  have h𝔮eq : 𝔮 = Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1)
      (hfin m (Nat.lt_succ_self m)) := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
    rw [← h𝔮comap, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K)
      (hfin m (Nat.lt_succ_self m))]
  simpa only [h𝔮eq] using h𝔮odd

/-- **Condition (1) of Schmidt--Wingberg p. 16 in divisor form**: for a history satisfying `PreTwo`
at every prefix, `div(b_m) = 𝔮_m · A²` — the escape prime of the stage occurs to odd order and
every other prime to even order. -/
theorem divisor_oddPart_eq_escapePrime {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) (m : ℕ) :
    Odd (FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1)
          ((hs (m + 1)).1 m (Nat.lt_succ_self m)))
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((s.f m).2 : ↥K))) ∧
      ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        P ≠ Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1)
          ((hs (m + 1)).1 m (Nat.lt_succ_self m)) →
        Even (FractionalIdeal.count ↥K P
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            ((s.f m).2 : ↥K))) :=
  ⟨oddCountAtEscapePrime (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs m,
    fun P hP => evenCountAtNonEscapePrime (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT s hs m P hP⟩

end Work.SSGRoute.NodeS37
