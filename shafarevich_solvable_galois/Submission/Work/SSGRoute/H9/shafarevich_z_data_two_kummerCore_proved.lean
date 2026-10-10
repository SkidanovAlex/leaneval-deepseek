import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.NodeS37.mu2ThreeHalvesProved
import Submission.Work.SSGRoute.ZDataTwo.mu2ThreeHalves
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

/-- **The `p = 2` Kummer core of Schmidt–Wingberg §4** (the `p = 2` half of the single arithmetic input of the node `Work.SSGRoute.shafarevich_z_construction`, hence of `Work.SSGRoute.shafarevich_existence` and of the Z-side of `Work.SSGRoute.scholz_succ_of_properStage`): every additive locally constant datum `y` with values in `ZMod 2` on `G_K = K.fixingSubgroup` (unramified outside the classes of `S` except where it is not split in `Λ`, vanishing on the inertia of the places of `S` and on the involutions) is the Kummer cochain `χ_b` of an element `b ∈ Kˣ` up to a finite set of new primes, with SW's sharpened condition (b), together with the prime-2 correction "`b` is totally positive", i.e. `χ_b` kills the involutions (`conjunct 2`).  The statement is already on disk, character for character and with a `sorry`, as `Work.SSGRoute.shafarevich_z_data_two_kummerCore` (`Submission/Work/SSGRoute/shafarevich_z_data_two.lean:2739`), with the unramified case already proved there (`shafarevich_z_data_two_kummerCore_of_unramified`, line 2669) and the reduction `shafarevich_z_data_two_of_kummerCore` (to an arbitrary one-dimensional coefficient module) also on disk.  Route warning (both reviewers): the Grünwald-with-escape route used for the odd-`p` core needs `hKimag` (`p = 2 → ∀ c, c^2 = 1 → c ∈ K.fixingSubgroup → c = 1`), which is *not* derivable in this lane (`AUDIT_p2_two_torsion_atom.lean.md`, `H9_STATUS.md` §26, `PING_zkummer_hKimag_finding.md`), so at `p = 2` the escape route is blocked; the intended route is the involution/archimedean one (conjunct 2 is the prime-2 "b totally positive" correction, and at odd `p` the involution clause is free).  The available `p = 2` machinery is `Submission/Work/SSGRoute/ZDataTwo/` (`KummerCocharBase`, `ArchKummer`, `archPair_two_kummer_eq_zero_iff`, `FiniteReciprocity`, `RealPlaceInvolution`, `LocalCongruence`, `AdicBridge`), `grunwald_surjective_two`, `kummerChar_eq_zero_of_isInertia_of_unit`, `exists_kummerChar_of_additive_locConst`, and the 211 kB of proved scaffolding of `shafarevich_z_data_two.lean` itself. -/
theorem shafarevich_z_data_two_kummerCore_proved (k Ω : Type) [Field k] [NumberField k]
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
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
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
  classical
  -- The `p = 2` three-halves construction of Schmidt–Wingberg §4, with the escape oracle
  -- `mu2EscapeRealisationHKfresh` fed in as the recursion's one-stage step.
  obtain ⟨Pset, b, hPfin, hPsplit, hPnotS, hagree, hinv, hconf, hconj⟩ :=
    Work.SSGRoute.NodeS37.mu2ThreeHalvesProved k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
      (fun T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf => by
        obtain ⟨b, Q, h1, h2, h3, _h4, h5, h6, h7⟩ :=
          Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj
            hTcov g hg hgc hgram h hh hhc horth hinertia hginf hhinf
        exact ⟨b, Q, h1, h2, h3, h5, h6, h7⟩)
  exact Work.SSGRoute.ZDataTwo.kummerCore_of_three_halves K Λ hKΛ ζ hζ hζK S Pset hPfin hPsplit
    hPnotS y b hagree hinv hconf hconj

end Work.SSGRoute.H9
