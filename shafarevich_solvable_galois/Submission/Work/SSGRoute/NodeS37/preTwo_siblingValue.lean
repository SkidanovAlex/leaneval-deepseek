import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.tblockBasics
import Submission.Work.SSGRoute.ZDataTwo.Mu2EscapeSquare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open scoped Pointwise

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The stage-`m` class at a sibling of an older escape prime is the branch scalar times the
older class.**  For `l < m` and `ρ ≠ 1`, the class `χ_{b_m}` of the `m`-th stage of the `p = 2`
recursion agrees on the whole local group of the `ρ`-sibling of the `l`-th escape prime with
`eGam l m ρ · χ_{b_l}`: the block of `TBlock S s.f m` covering that sibling has the unique
attachment `(l, ρ)` (`TBlock_covers_Q`, `attach_unique`), and `PreTwo`'s realisation clause
together with the collapse `prescDatum_attach` of the prescribed datum gives
`χ_{b_m} = y + (-y + eScalar l m ρ · χ_{b_l})` at that block, transported back to the sibling by the
conjugation invariance of the cochain and of `y`. -/
theorem preTwo_siblingValue {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ]
    (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    {l m : ℕ} (hlm : l < m) {ρ : K ≃ₐ[k] K} (hρ : ρ ≠ 1) :
    ∀ σ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1)
        ⊓ K.fixingSubgroup,
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 σ
        = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f l m ⟨ρ, hρ⟩
          • Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f l).2 σ := by
  intro σ hσ
  -- the prefix invariant at stage `m + 1`
  obtain ⟨hfin, hsplit, hdisjK, hdisjk, hexcl, hreal, hinv, hconf, hnorm⟩ := hs (m + 1)
  -- the block of `TBlock S s.f m` covering the sibling of the `l`-th escape prime
  obtain ⟨A', hA'mem, hA'B⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_Q (K := K) (S := S) (f := s.f) (m := m)
      (j := l) hlm
      (Work.SSGRoute.isConjPlace_symm (siblingPlace_isConjPlace (K := K) ρ (s.f l).1))
  have hAtt : Work.SSGRoute.gesKConj K
      (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1) A' :=
    Work.SSGRoute.H9.swGesKConj_symm hA'B
  -- the split and non-conjugacy hypotheses at stage `m`
  have hsplit' : ∀ j < m, SSGRoute.IsSplitIn k K (s.f j).1 :=
    fun j hj =>
      Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (hsplit j (by omega))
  have hdisj' : ∀ j l' : ℕ, j < m → l' < m → j ≠ l' →
      ¬ SSGRoute.IsConjPlace k (s.f j).1 (s.f l').1 := by
    intro j l' hj hl' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdisjk j l' h (by omega)
    · intro hc
      exact hdisjk l' j h (by omega) (Work.SSGRoute.isConjPlace_symm hc)
  -- the attachment of `A'` is unique
  have huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1) A' →
      l' = l ∧ ρ' = ρ := by
    intro l' hl' ρ' h'
    have h1 := attach_unique (K := K) (f := s.f) (m := m) (A := A') (q := (l, ρ)) (q' := (l', ρ'))
      hsplit' hdisj' hlm hl' hAtt h'
    exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩
  -- `A'` is not `k`-conjugate to a place of `S`
  have hS : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A' := by
    rintro ⟨A₀, hA₀, hconj⟩
    have hconjQ : SSGRoute.IsConjPlace k A₀ (s.f l).1 :=
      Work.SSGRoute.isConjPlace_trans hconj
        (Work.SSGRoute.isConjPlace_trans (gesKConj_isConjPlace hA'B)
          (siblingPlace_isConjPlace (K := K) ρ (s.f l).1))
    obtain ⟨A'', hA'', hA''Q⟩ :=
      Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (S := S) (f := s.f) (m := l)
        hA₀ hconjQ
    exact hexcl l (by omega) A'' hA'' hA''Q
  -- the prescribed datum collapses at `A'`
  have hpd : Work.SSGRoute.ZDataTwo.TwoRec.prescDatum (K := K) ζ hζ hζK S y s.f m A'
      = fun σ => - y σ + Work.SSGRoute.ZDataTwo.TwoRec.eScalar (K := K) ζ hζ hζK s.f l m ρ
          • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ :=
    prescDatum_attach (K := K) (f := s.f) (m := m) (A := A') hS hlm hAtt huniq
  -- the transport element and the conjugated argument
  obtain ⟨τ, hτmem, hτA'⟩ := hA'B
  set σ' : Ω ≃ₐ[k] Ω := τ⁻¹ * σ * τ with hσ'def
  have hτστ : τ * σ' * τ⁻¹ = σ := by rw [hσ'def]; group
  have hσd : σ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1) :=
    (Subgroup.mem_inf.mp hσ).1
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hσdB : σ • (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1)
      = Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1 :=
    MulAction.mem_stabilizer_iff.mp hσd
  have hσ'A' : σ' • A' = A' := by
    rw [hσ'def, mul_smul, mul_smul, hτA', hσdB, ← hτA', inv_smul_smul]
  have hNormal : (K.fixingSubgroup).Normal := Work.SSGRoute.P2Core.fixingSubgroup_normal K
  have hσ'K : σ' ∈ K.fixingSubgroup := by
    rw [hσ'def]
    simpa using hNormal.conj_mem σ hσK τ⁻¹
  have hσ'd : σ' ∈ SSGRoute.decomp k A' := MulAction.mem_stabilizer_iff.mpr hσ'A'
  have hσ' : σ' ∈ SSGRoute.decomp k A' ⊓ K.fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨hσ'd, hσ'K⟩
  -- the realisation clause of `PreTwo` at the block `A'`
  have hstep : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ'
      = Work.SSGRoute.ZDataTwo.TwoRec.eScalar (K := K) ζ hζ hζK s.f l m ρ
        • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ' := by
    rw [hreal m (Nat.lt_succ_self m) A' hA'mem σ' hσ', congrFun hpd σ']
    ring
  -- conjugation invariance of the two cochains
  have hconjm : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ' := by
    have h1 := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj (K := K) ζ hζ hζK (s.f m).2
      hτmem σ'
    rwa [hτστ] at h1
  have hconjl : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ' := by
    have h1 := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj (K := K) ζ hζ hζK (s.f l).2
      hτmem σ'
    rwa [hτστ] at h1
  have hmain : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ
      = Work.SSGRoute.ZDataTwo.TwoRec.eScalar (K := K) ζ hζ hζK s.f l m ρ
        • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ := by
    rw [hconjm, hstep, hconjl]
  -- pass from `eScalar` to `eGam` and from the `ZMod`-cochain to the `kummerSqrt`-cochain
  have he : Work.SSGRoute.ZDataTwo.TwoRec.eScalar (K := K) ζ hζ hζK s.f l m ρ
      = Work.SSGRoute.ZDataTwo.TwoRec.eGam (K := K) ζ hζ hζK s.f l m ⟨ρ, hρ⟩ := by
    rw [Work.SSGRoute.ZDataTwo.TwoRec.eScalar, dif_neg hρ]
  rw [← he,
    ← Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar k Ω K ζ hζK hζ (s.f m).2,
    ← Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar k Ω K ζ hζK hζ (s.f l).2]
  exact hmain

end Work.SSGRoute.NodeS37
