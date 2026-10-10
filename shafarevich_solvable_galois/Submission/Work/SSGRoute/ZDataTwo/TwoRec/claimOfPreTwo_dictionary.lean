import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local dictionary of the `p = 2` §4 recursion, read off from `PreTwo`

`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary` is the "dictionary" step of
Schmidt--Wingberg's local computation at `p = 2` (the local pairing at a sibling place of the escape
prime equals the value of the class at a pinned Frobenius there):

    pinValue (χ_b) at the ρ-sibling of Q  =  oPairAt_{ρQ} (χ_b, χ_{ρ b}) .

The arithmetic input is the local dictionary of the crossed two-place chain,
`Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count`; the two hypotheses it needs are supplied by the
prefix invariant `PreTwo`:

* the **confinement** of the class to its own escape prime, `claimOfPreTwoConfined`: the sibling
  `galLift K ρ • Q` is not `K`-conjugate to `Q` (`ZDataMup.siblingPlace_not_gesKConj`), so `χ_b` kills
  its inertia, whence the Kummer level `↥K(b^{1/2})` is unramified there;
* the **normalisation**: the escape prime's odd `𝔮`-count (clause (9) of `PreTwo`) is transported to
  the sibling by `H9.swCount_conjUnit`.
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

theorem claimOfPreTwo_dictionary {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (k := k) (Ω := Ω) (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m : ℕ, ∀ ρ : K ≃ₐ[k] K, ρ ≠ 1 → ρ ^ 2 = 1 →
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) 0 ρ
        = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
            (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
            (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f m).1)
            ((SSGRoute.isFinPlace_smul_iff (s.f m).1 (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr
              ((hs (m + 1)).1 m (Nat.lt_succ_self m)))
            (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2)
            (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
              (Work.SSGRoute.H9.conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K ρ)
                (s.f m).2)) := by
  intro m ρ hρ hρ2
  classical
  -- ## the Kummer-level instances of the stage-`m` class
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI hfd : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (s.f m).2
  haveI hgal : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (s.f m).2
  haveI hnf : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (s.f m).2
  haveI hnm : Normal ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    hgal.to_normal
  -- ## the bookkeeping clauses of the prefix invariant
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs (m + 1)
  have hQfin : SSGRoute.IsFinPlace k ((s.f m).1) := h1 m (Nat.lt_succ_self m)
  have hAfin : SSGRoute.IsFinPlace k
      (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f m).1) :=
    (Work.SSGRoute.isFinPlace_smul_iff (s.f m).1 (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hQfin
  have hQsplit : SSGRoute.IsSplitIn k K ((s.f m).1) :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (h2 m (Nat.lt_succ_self m))
  have hsep : ¬ Work.SSGRoute.gesKConj K ((s.f m).1)
      (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K hρ hQsplit
  -- ## the confinement of the class at the sibling (strong form of clause (7))
  have hkill : ∀ u ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 :=
    fun u huK huI =>
      Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ) hKΛ
        ζ hζ hζK S y hy hyT s hs m (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1)
        hAfin hsep u huK huI
  have hunr := Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := 2) ζ hζ hζK
    (s.f m).2 (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) hAfin hkill
  -- ## the transported read-off normalisation
  obtain ⟨𝔮, h𝔮comap, h𝔮odd⟩ := h9 m (Nat.lt_succ_self m)
  have h𝔮eq : 𝔮 = Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1) hQfin := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
    rw [← h𝔮comap, Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hQfin]
  have hcountQ : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) ((s.f m).1) hQfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((s.f m).2 : ↥K))) := by
    simpa only [h𝔮eq] using h𝔮odd
  have hcount : Odd (FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) hAfin)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((Work.SSGRoute.H9.conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K ρ)
          (s.f m).2 : (↥K)ˣ) : ↥K))) := by
    rw [Work.SSGRoute.H9.swCount_conjUnit (K := K) (s.f m).2 ρ ((s.f m).1) hQfin hAfin]
    exact hcountQ
  -- ## a pinned Frobenius at the sibling place
  obtain ⟨⟨ψ, hψmem⟩, hψpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f m).2)) 0
    (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) hAfin hkill
  -- ## the local dictionary, and the identification of `χ_b ψ` with `pinValue`
  have hdict : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ'
      (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) hAfin
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (Work.SSGRoute.H9.conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K ρ) (s.f m).2))
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ :=
    Work.SSGRoute.H9.CV2.oPairAt_eq_value_of_odd_count (K := K) (k := k) (Ω := Ω) ζ hζ hζK
      (s.f m).2
      (Work.SSGRoute.H9.conjUnit (K := K) (Work.SSGRoute.ZDataMup.galLift K ρ) (s.f m).2)
      (Work.SSGRoute.ZDataMup.galLift K ρ • (s.f m).1) hAfin ψ
      (Subgroup.mem_inf.mp hψmem).2 hunr hψpin hcount
  have hpin : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) 0 ρ :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) 0 ρ hρ ψ hψmem hψpin
  exact hpin.symm.trans hdict.symm

end Work.SSGRoute.ZDataTwo.TwoRec
