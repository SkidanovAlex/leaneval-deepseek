import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.P16Diagonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The three-case dispatch of the paper's Claim, a twin

`Work.SSGRoute.NodeS37.claimOfPreTwo` is the three-case dispatch of Schmidt--Wingberg's Claim:

* `m > l`: `NodeS37.claimOfPreTwo_gt` (proved, no arithmetic);
* `m = l`: the p. 16 diagonal case, dispatched to `ZDataTwo.TwoRec.claimOfPreTwo_diagonal`;
* `m < l`: `NodeS37.claimOfPreTwo_lt` (proved, the two-place chain of SW p. 17).

This file is the statement-identical twin of the dispatch in this lane, with the diagonal call
replaced by `Work.SSGRoute.ZConstruction.claimOfPreTwoDiagonalTwin`
(`ZConstruction/P16Diagonal.lean`), so that this lane can close the node without editing the
`ZDataTwo`/`NodeS37` lanes' files.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The paper's Claim for a history satisfying `PreTwo`** (statement-identical twin of
`Work.SSGRoute.NodeS37.claimOfPreTwo`): for every involution `σ ∉ G_K` of `G(k)` and every index
pair `m l`, the class `χ_{b_m}` of the recursion vanishes on the decomposition group of the
`σ`-sibling of the escape prime `Q_l`. -/
theorem claimOfPreTwoTwin {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
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
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m l : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m l σ hσK hσ2 u hu
  rcases lt_trichotomy m l with hlt | heq | hgt
  · -- `m < l`: the crossed two-place chain (Schmidt--Wingberg p. 17)
    exact Work.SSGRoute.NodeS37.claimOfPreTwo_lt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT s hs
      m l hlt σ hσK hσ2 u hu
  · -- `m = l`: the paper's Claim (Schmidt--Wingberg p. 16)
    subst heq
    exact claimOfPreTwoDiagonalTwin (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf s hs m σ hσK hσ2 u hu
  · -- `l < m`: the prescription of the rule at the earlier escape prime
    exact Work.SSGRoute.NodeS37.claimOfPreTwo_gt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs m l hgt
      σ hσK hσ2 u hu

end Work.SSGRoute.ZConstruction
