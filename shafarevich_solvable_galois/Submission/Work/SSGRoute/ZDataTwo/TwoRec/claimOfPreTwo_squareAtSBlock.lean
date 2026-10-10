import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeSquare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The stage classes of the `p = 2` §4 recursion are squares at the `S`-blocks

`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock`: for a history `s` satisfying the
prefix invariant `PreTwo` at every stage, the class `z_m = χ_{b_m}` of the `m`-th stage kills the
**whole local group** `decomp k B ⊓ G_K` of every finite place `B` that is `k`-conjugate to a place
of `S`, provided `B` is either non-split in `K` or `2`-adic.

The proof is the "trivial" half of Schmidt--Wingberg's p. 16 input:
* `B` being `k`-conjugate to `S`, the place set `TBlock S s.f m` contains a block `A` that is
  `K`-conjugate to `B` (`TBlock_covers_S`), and at such a block the prescribed datum vanishes
  (`prescDatum_eq_zero_of_isConjPlace`), so the realisation clause of `PreTwo` gives `χ_{b_m} = y`
  on the whole local group of `A`;
* the conjugation invariance of `χ_{b_m}` (`nodeKummerCocharZMod_conj`) transports this to `B`;
* `y` vanishes on that local group by the hypothesis `hy0`, the condition
  `¬ IsSplitIn k K · ∨ (·).valuation 2 < 1` being invariant under the `G_k`-translation (this is
  `not_isSplitIn_or_val_two_conj` below, using `isSplitIn_conj` and the fact that `G_k`-conjugation
  does not move the prime of `k` below a place).
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The "not split in `K`, or `2`-adic" condition is invariant under the translation of a place
by an element of `G_k`.**  If `B = g • A`, then `A` and `B` lie over the same prime of `k`, so
`A.valuation (2 : Ω) < 1 ↔ B.valuation (2 : Ω) < 1`, and complete splitting in the normal
extension `K|k` is conjugation-invariant (`Work.SSGRoute.isSplitIn_conj`). -/
theorem not_isSplitIn_or_val_two_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {A B : ValuationSubring Ω} {g : Ω ≃ₐ[k] Ω} (h : g • A = B) :
    (¬ SSGRoute.IsSplitIn k K A ∨ A.valuation (2 : Ω) < 1) ↔
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) := by
  have hKn : (K.fixingSubgroup).Normal := inferInstance
  have hBA : g⁻¹ • B = A := by rw [← h, inv_smul_smul]
  have hsplit : SSGRoute.IsSplitIn k K A ↔ SSGRoute.IsSplitIn k K B := by
    rw [← hBA]
    exact Work.SSGRoute.isSplitIn_conj K hKn B g⁻¹
  have hcomap : B.comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
    rw [← h, Work.SSGRoute.comap_algebraMap_smul]
  have hvalA : A.valuation (2 : Ω) < 1 ↔ (A.comap (algebraMap k Ω)).valuation (2 : k) < 1 := by
    rw [show (2 : Ω) = algebraMap k Ω (2 : k) from (map_ofNat (algebraMap k Ω) 2).symm]
    exact (Work.SSGRoute.comap_valuation_lt_one_iff A (2 : k)).symm
  have hvalB : B.valuation (2 : Ω) < 1 ↔ (B.comap (algebraMap k Ω)).valuation (2 : k) < 1 := by
    rw [show (2 : Ω) = algebraMap k Ω (2 : k) from (map_ofNat (algebraMap k Ω) 2).symm]
    exact (Work.SSGRoute.comap_valuation_lt_one_iff B (2 : k)).symm
  rw [hsplit, hvalA, hvalB, hcomap]

theorem claimOfPreTwo_squareAtSBlock {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (k := k) (Ω := Ω) (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m B hBfin hBS hP u hu
  classical
  -- the two `p = 2` encodings of the Kummer cochain agree
  rw [← Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar k Ω K ζ hζK hζ (s.f m).2]
  -- a block `A` of the stage-`m` place set that is `K`-conjugate to `B`
  obtain ⟨A₀, hA₀, hA₀B⟩ := hBS
  obtain ⟨A, hA, hAK⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (S := S) (f := s.f) (m := m) hA₀ hA₀B
  obtain ⟨v, hvK, hvA⟩ := hAK
  -- the conjugate of `u` lying in the local group of `A`
  set σ' : Ω ≃ₐ[k] Ω := v⁻¹ * u * v with hσ'def
  have hvu : v * σ' * v⁻¹ = u := by rw [hσ'def]; group
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u • B = B := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hu).1
  have hσ'K : σ' ∈ K.fixingSubgroup := by
    rw [hσ'def]
    exact K.fixingSubgroup.mul_mem
      (K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hvK) huK) hvK
  have hσ'D : σ' ∈ SSGRoute.decomp k A := MulAction.mem_stabilizer_iff.mpr (by
    show (v⁻¹ * u * v) • A = A
    rw [mul_smul, mul_smul, hvA, huD, ← hvA, inv_smul_smul])
  -- the realisation clause of the invariant at the block `A`, where the prescribed datum vanishes
  obtain ⟨-, -, -, -, -, hreal, -, -, -⟩ := hs (m + 1)
  have hAP : ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A :=
    ⟨A₀, hA₀, Work.SSGRoute.isConjPlace_trans hA₀B
      (Work.SSGRoute.isConjPlace_symm ⟨v, hvA⟩)⟩
  have hχσ' : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ' = y σ' := by
    rw [hreal m (Nat.lt_succ_self m) A hA σ' (Subgroup.mem_inf.mpr ⟨hσ'D, hσ'K⟩),
      congrFun (Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_zero_of_isConjPlace (K := K)
        (S := S) (y := y) (f := s.f) (m := m) (A := A) hAP) σ', add_zero]
  -- conjugation invariance of the class
  have hχconj : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ' := by
    have h1 := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2 hvK σ'
    rwa [hvu] at h1
  -- `A` is a finite place, and `hy0` kills `y` on its local group
  have hAfin : SSGRoute.IsFinPlace k A := by
    have hAeq : A = v⁻¹ • B := by rw [← hvA, inv_smul_smul]
    rw [hAeq]
    exact (Work.SSGRoute.isFinPlace_smul_iff B v⁻¹).mpr hBfin
  have hP'A : (¬ SSGRoute.IsSplitIn k K A ∨ A.valuation (2 : Ω) < 1) :=
    (not_isSplitIn_or_val_two_conj (K := K) hvA).mpr hP
  have hy0' : y σ' = 0 := hy0 A hAfin hAP hP'A σ' hσ'K hσ'D
  rw [hχconj, hχσ', hy0']

end Work.SSGRoute.ZDataTwo.TwoRec
