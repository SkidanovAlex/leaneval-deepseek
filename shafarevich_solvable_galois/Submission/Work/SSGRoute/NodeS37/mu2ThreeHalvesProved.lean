import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwo
import Submission.Work.SSGRoute.NodeS37.goodClassOfHistory
import Submission.Work.SSGRoute.NodeS37.reduce
import Submission.Work.SSGRoute.NodeS37.twoRecExists
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `NodeS37.mu2ThreeHalvesProved`: the `p = 2` Kummer core of Schmidt--Wingberg §4, reassembled

This is the statement of `Work.SSGRoute.ZDataTwo.mu2ThreeHalves` (character-identical), proved here
from the three pieces of this lane:

* `NodeS37.twoRecExists`  — the §4 recursion (the escape primes `Q_m` with classes `b_m` satisfying
  `ZDataTwo.TwoRec.PreTwo` at every prefix),
* `NodeS37.claimOfPreTwo` — the paper's Claim (SW pp. 16--17) for such a history, using the node's
  `hy0` (the prime-`2` correction: the prescribed class is trivial at the primes over `2` and at the
  primes ramified in `K|k`),
* `NodeS37.goodClassOfHistory` — the verification: the minimal shoe-box triple of
  `ZDataTwo.pigeonhole_three_minimal` on the `Ψ`-vector, `ZDataTwo.blocks_of_prVal`, the crossed
  two-place identity `ZDataTwo.crossedValueTwoProof` and `ZDataTwo.threeTerm_kills_localGroup`
  produce the one good class `B = b_i b_j b_N`,
* `NodeS37.threeHalvesConcl_of_goodClass` (this lane, `NodeS37/reduce.lean`) and Kummer duality
  `ZSplit.exists_kummerCocharZMod_of_additive_locConst` close the three halves.

The `oracle` hypothesis of the target is inherited from `shafarevichZDataTwoKummerCoreH` and is not
needed by this route (the concrete `P2Core.escapeStepNormalised` is used inside `twoRecExists`); it
is kept in the statement because the statement is the frozen one.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem mu2ThreeHalvesProved (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
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
    (oracle : ∀ (T : Finset (ValuationSubring Ω)),
      (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (B.valuation (2 : Ω) < 1 ∨
          ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
        ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) →
      ∀ (g : (Ω ≃ₐ[k] Ω) → ZMod 2),
        (∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup, g (x * z) = g x + g z) →
        SSGRoute.IsLocConstOn K.fixingSubgroup g →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0) →
        ∀ (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2),
          (∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
            ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * z) = h A x + h A z) →
          (∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
            ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) →
          (∀ A ∈ T, (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
            SSGRoute.IsSplitIn k Λ A) →
          (∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
            g σ + h A σ = 0) →
          (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0) →
          (∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) →
          ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
            SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
            (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
            (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
            (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
            (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
              (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
              (¬ Work.SSGRoute.gesKConj K Q B) →
              ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
                Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0)) :
    ∃ (Pset : Finset (ValuationSubring Ω)) (b : Fin 3 → (↥K)ˣ),
      (∀ P ∈ Pset, SSGRoute.IsFinPlace k P) ∧
      (∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P) ∧
      (∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P) ∧
      (∀ i : Fin 3, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) σ = y σ) ∧
      (∀ i : Fin 3, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) σ = 0) ∧
      (∀ P ∈ Pset, ∀ B : ValuationSubring Ω, SSGRoute.IsConjPlace k P B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B) →
        ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) u = 0) := by


  have hsepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  haveI : IsSepClosure ↥K Ω := hsepK
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  obtain ⟨s, hs⟩ :=
    twoRecExists (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSram y hy hyc hyS hyT hyinf
  have hclaim :=
    claimOfPreTwo (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyT hy0
      hyinf s hs
  obtain ⟨Pset, B, hPfin, hPsplit, hPnotS, h1, h2, h3, h4⟩ :=
    goodClassOfHistory (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyT hy0
      hyinf s hs hclaim
  obtain ⟨b, hb⟩ :=
    ZSplit.exists_kummerCocharZMod_of_additive_locConst 2 k Ω K ζ hζK hζ y hy hyc
  refine threeHalvesConcl_of_goodClass K Λ ζ hζK hζ S Pset hPfin hPsplit hPnotS y hyinf b B ?_
    h1 h2 h3 h4
  intro σ hσ
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two
    (K := K) ζ hζ hζK b σ]
  exact (hb σ hσ).symm

end Work.SSGRoute.NodeS37
