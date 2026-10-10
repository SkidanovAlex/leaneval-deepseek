import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.P2Close.claimOfPinnedZero
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.pinnedValue_diagonal_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

/-- **The p. 16 diagonal pinned value in the form in which the recursion consumes it.**

The sibling value `pinValue … 0 ρ` of the `m`-th Kummer class vanishes at every involution
`ρ ≠ 1` of `Gal(K|k)`.  This is Schmidt--Wingberg's p. 16 computation (the irreducible arithmetic
core of the corrected `p = 2` §4 recursion), i.e. `TwoRec.pinnedValue_diagonal_proved`, restated
with the `IsFinPlace` witness family read off the bookkeeping half of the prefix invariant
`hs (m + 1)` rather than from the auxiliary `TwoRec.preTwo_finPlace_diag`.  The two families are
equal because `SSGRoute.IsFinPlace k (s.f m).1` is a proposition, so the passage between them is
proof irrelevance. -/
theorem mu2PinnedValueDiagonal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (m : ℕ) (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1) :
    Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) 0 ρ = 0 := by
  classical
  have h := Work.SSGRoute.ZDataTwo.TwoRec.pinnedValue_diagonal_proved (K := K) (Λ := Λ) hKΛ
    ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf s hs m ρ hρ1 hρ2
  -- the two `IsFinPlace` witness families are equal (both live in a proposition)
  have hfin_eq :
      (fun _ : ℕ => Work.SSGRoute.ZDataTwo.TwoRec.preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m)
        = (fun _ : ℕ => (hs (m + 1)).1 m (Nat.lt_succ_self m)) :=
    funext fun n => Subsingleton.elim _ _
  rwa [hfin_eq] at h

end Work.SSGRoute.ZDataTwo
