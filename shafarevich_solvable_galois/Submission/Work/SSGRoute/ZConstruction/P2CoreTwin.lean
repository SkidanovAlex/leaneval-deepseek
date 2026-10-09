import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.ThreeHalves
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh
import Submission.Work.SSGRoute.NodeS37.mu2ThreeHalvesProved
import Submission.Work.SSGRoute.ZConstruction.Mu2ThreeHalvesTwin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` Kummer core, from the `NodeS37` twin of the three-halves recursion

`Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH` (`ZDataTwo/shafarevichZDataTwoKummerCoreH.lean`)
is the `p = 2` Kummer core that the node `Work.SSGRoute.shafarevich_z_construction` consumes through
`Work.SSGRoute.isMupZData_of_kummerCoreTwo` (`ZConstruction/MupCoreTwo.lean`).  Its proof calls the
`p = 2` three-halves recursion `Work.SSGRoute.ZDataTwo.mu2ThreeHalves`, whose own file still carries
the `sorry` of the `ZDataTwo` lane.

The `NodeS37` lane has meanwhile *proved* a statement-identical twin of that recursion,
`Work.SSGRoute.NodeS37.mu2ThreeHalvesProved` (`Submission/Work/SSGRoute/NodeS37/mu2ThreeHalvesProved.lean`,
`#print axioms` walk: its proof-term closure now reaches exactly one `sorry`-bearing declaration,
`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_diagonal`, which is filed and live).  This file
therefore re-proves the `p = 2` Kummer core from *that* twin, so that the node
`Work.SSGRoute.shafarevich_z_construction` depends on the **live** frontier node rather than on the
stale `sorry` of `mu2ThreeHalves.lean`; the node becomes `sorry`-free automatically as soon as
`claimOfPreTwo_diagonal` lands, with no edit to any other lane's file.
-/

namespace Work.SSGRoute.ZConstruction

/-- **The `p = 2` Kummer core** (statement of
`Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH`), from the `NodeS37` twin of the three-halves
recursion and the proved escape realisation `mu2EscapeRealisationHKfresh`. -/
theorem shafarevichZDataTwoKummerCoreH_twin (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, _root_.SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, _root_.SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (_root_.SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → ¬ _root_.SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
      (¬ _root_.SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ _root_.SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ _root_.SSGRoute.decomp k B →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → ¬ _root_.SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → _root_.SSGRoute.IsSplitIn k Λ B →
        (∃ σ, _root_.SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, _root_.SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ _root_.SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b τ = 0) := by
  obtain ⟨Pset, b, hPfin, hPsplit, hPnotS, hagree, hinv, hconf, hconj⟩ :=
    Work.SSGRoute.ZConstruction.mu2ThreeHalvesTwin k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
      (fun T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf => by
        obtain ⟨b, Q, h1, h2, h3, _h4, h5, h6, h7⟩ :=
          Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj
            hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf
        exact ⟨b, Q, h1, h2, h3, h5, h6, h7⟩)
  exact Work.SSGRoute.ZDataTwo.kummerCore_of_three_halves K Λ hKΛ ζ hζ hζK S Pset hPfin
    hPsplit hPnotS y b hagree hinv hconf hconj

end Work.SSGRoute.ZConstruction
