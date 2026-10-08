import Mathlib
import Submission.OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement

namespace Work.RED

/-- If `C` is normal in `G` and `K` is a normal subgroup of `↥C` which is a complement of a
Sylow 2-subgroup of `↥C`, then `K`, viewed as a subgroup of `G` via `C.subtype`, is normal in `G`.
Hint for the proof: import `Submission.OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement` and use
`OddOrder.Isaacs.Ch05.map_mulAut_of_normal_pcomplement`, which says that such a `K` is
fixed by every `MulAut` of `↥C`; combine it with `MulAut.conjNormal`. -/
theorem normal_map_of_complement_sylow
    {G : Type*} [Group G] [Finite G] {C : Subgroup G} (hC : C.Normal)
    {K : Subgroup ↥C} (hKn : K.Normal) {Q : Sylow 2 ↥C}
    (hK : Subgroup.IsComplement' K (Q : Subgroup ↥C)) :
    (K.map C.subtype).Normal := by
  classical
  haveI := hC
  haveI := hKn
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  rw [Subgroup.map_map]
  have hcomp : (↑(MulAut.conj g) : G →* G).comp C.subtype
      = C.subtype.comp (↑(MulAut.conjNormal (H := C) g) : ↥C →* ↥C) := by
    ext k
    exact MulAut.conjNormal_apply (H := C) g k
  rw [hcomp, ← Subgroup.map_map]
  have hfix : K.map (↑(MulAut.conjNormal (H := C) g) : ↥C →* ↥C) = K :=
    OddOrder.Isaacs.Ch05.map_mulAut_of_normal_pcomplement (p := 2) hK
      (MulAut.conjNormal (H := C) g)
  rw [hfix]

end Work.RED
