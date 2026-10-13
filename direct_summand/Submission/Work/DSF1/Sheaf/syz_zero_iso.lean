import Mathlib
import Submission.Work.DSF1.Sheaf.AcyclicToolkit

universe u v

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

/-- If `i : M[0] ⟶ K` is a quasi-isomorphism from the complex concentrated in degree `0`,
then `M` is canonically the zeroth syzygy of `K`, i.e. the kernel of `K.d 0 1`.

Indeed, `H₀` of a cochain complex indexed by `ℕ` has no incoming differential, so
`K.homology 0 ≅ K.cycles 0 = syz K 0`, while `H₀ (M[0]) ≅ M`, and `i` induces an
isomorphism on `H₀`. -/
theorem syz_zero_iso {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    (M : C) (K : CochainComplex C ℕ) [∀ i : ℕ, HomologicalComplex.HasHomology K i]
    (i : (CochainComplex.single₀ C).obj M ⟶ K) [QuasiIso i] :
    Nonempty (M ≅ Work.DSF1.Sheaf.syz K 0) := by
  -- in degree `0` (which has no predecessor) the cycles are the whole homology
  have hnext : (ComplexShape.up ℕ).next 0 = 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk 0 1 rfl)
  -- `K.cycles 0` is the kernel of `K.d 0 1`, i.e. `syz K 0`
  have eK : K.cycles 0 ≅ syz K 0 :=
    IsLimit.conePointUniqueUpToIso
      (t := KernelFork.ofι (Limits.kernel.ι (K.d 0 1))
        (Limits.kernel.condition (K.d 0 1)))
      (K.cyclesIsKernel 0 1 hnext) (Limits.kernelIsKernel (K.d 0 1))
  refine ⟨(HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 M).symm
      ≪≫ isoOfQuasiIsoAt i 0
      ≪≫ (CochainComplex.isoHomologyπ₀ K).symm
      ≪≫ eK⟩

end Work.DSF1.Sheaf
