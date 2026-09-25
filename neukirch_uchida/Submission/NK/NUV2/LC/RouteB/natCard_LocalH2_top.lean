import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.ABHN.local_brauer_trivial
import Submission.NK.NUV2.LCLeaves
import Submission.NK.LocalDecomposition.All
import Submission.NK.NUV2.LC.cardH2P_adicCompletion
import Submission.NK.NUV2.LC.decompContinuousIso
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

/-- **The local group at a finite place has `p` elements** (`Br(F_v)[p] ≅ Z/p`), for a number
field `F` containing a primitive `p`-th root of unity `ζ`.

This is the local Brauer computation of local class field theory in the trivial-coefficient form:
`p` odd and `ζ ∈ F ⊆ F_v` make the cyclotomic module `μ_p` trivial, so
`H²(G_{F_v}, Z/p) = Br(F_v)[p] ≅ Z/p`. -/
theorem natCard_LocalH2_top (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    {F : Type} [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (A : NK.BrauerHasse.OverFinitePrime F F') :
    Nat.card (NK.BrauerHasse.LocalH2 (K := F) (K' := F') p ⊤ A.1) = p := by
  -- the finite prime `𝔭` of `F` below the place `A`
  obtain ⟨𝔭, h𝔭⟩ :=
    NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := F) (K' := F') A.1 A.2
  -- the decomposition group of `A` is the absolute Galois group of the completion `F_𝔭`
  obtain ⟨e⟩ := NK.NUV2.LC.decompContinuousIso F F' 𝔭 A.1 h𝔭
  -- `F ⊆ F_𝔭` carries the primitive `p`-th root of unity
  have hζ' : ∃ ζ' : 𝔭.adicCompletion F, IsPrimitiveRoot ζ' p :=
    ⟨algebraMap F (𝔭.adicCompletion F) ζ,
      hζ.map_of_injective (algebraMap F (𝔭.adicCompletion F)).injective⟩
  -- the decomposition group is closed in the Krull topology
  have hDcl : IsClosed
      ((NK.BrauerHasse.stabSubgroup A.1 : Subgroup Gal(F'/F)) : Set Gal(F'/F)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A.1
  -- the local Brauer computation at the decomposition group
  have hcard := NK.NUV2.LC.card_h2P_of_homeomorph (K := F) (K' := F') 𝔭 hp hζ'
    (NK.BrauerHasse.stabSubgroup A.1) hDcl e
  -- `LocalH2 p ⊤ D_A = H²(D_A, Z/p)` and `⊤ ⊓ D_A = D_A`
  rw [NK.LocalDecomposition.LocalH2.eq_profinite, inf_eq_right.mpr le_top]
  exact hcard

end NK.NUV2.LC.RouteB
