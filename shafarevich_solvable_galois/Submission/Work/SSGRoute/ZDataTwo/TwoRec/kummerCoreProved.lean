import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.ThreeHalves
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH
import Submission.Work.SSGRoute.NodeS37.mu2ThreeHalvesProved
import Submission.Work.SSGRoute.ZDataTwo.mu2ThreeHalves
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` Kummer core, proved from the `NodeS37` lane

`Work.SSGRoute.ZDataTwo.TwoRec.kummerCoreProved`: the statement of the node's arithmetic core
`Work.SSGRoute.shafarevich_z_data_two_kummerCore`, obtained by running
`ZDataTwo.shafarevichZDataTwoKummerCoreH`'s assembly with a **proved** three-halves construction in
place of the `sorry`-carrying `ZDataTwo.mu2ThreeHalves`.

**Re-pointed 2026-10-05 (node lane of `Work.SSGRoute.scholz_succ_of_properStage`).**
`Work.SSGRoute.ZDataTwo.mu2ThreeHalves` itself is now proved and axiom-clean
(`ZDataTwo/mu2ThreeHalves.lean` routes the §4 core through `NodeS37.twoRecExists`,
`NodeS37.goodClassOfHistory`, `TwoRec.claimOfPreTwo_gt`, `ZDataTwo.mu2PinnedValueDiagonal` and
`P2Close.claimOfPinnedZero`), so the older workaround through `NodeS37.mu2ThreeHalvesProved` — whose
cone still passes through the `sorry`-carrying `TwoRec.claimOfPreTwo_diagonal` — is stale and was
the last `sorryAx` of the Step-4 cone.  See
`Submission/Work/SSGRoute/PING_p2core_closed_repoint_the_N5_workaround.md`.
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

open scoped Pointwise

theorem kummerCoreProved (k Ω : Type) [Field k] [NumberField k]
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
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b τ = 0) := by
  classical
  obtain ⟨Pset, b, hPfin, hPsplit, hPnotS, hagree, hinv, hconf, hconj⟩ :=
    Work.SSGRoute.ZDataTwo.mu2ThreeHalves k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
      (fun T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhhinf =>
        mu2EscapeRealisationH k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj hTcov g hg hgc hgram
          h hh hhc horth hinertia hginf hhhinf)
  exact kummerCore_of_three_halves K Λ hKΛ ζ hζ hζK S Pset hPfin hPsplit hPnotS y b
    hagree hinv hconf hconj

end Work.SSGRoute.ZDataTwo.TwoRec
