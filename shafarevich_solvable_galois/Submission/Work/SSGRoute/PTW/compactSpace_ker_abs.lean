import Mathlib
import Submission.Work.SSGRoute.PTW.logSectionDefs
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of the content `C_K →* ℝˣ` is compact

The content (idèle norm) `abs : C_K →* ℝˣ` fits into the exact sequence
`1 → C¹_K → C_K → ℝˣ`, where `C¹_K = 𝕀¹K ⧸ Kˣ` is the norm-one idèle class group: the
canonical map `𝕀¹K → 𝕀 K → C_K` is a continuous homomorphism which kills `Kˣ`, hence descends to
a continuous homomorphism `ι : C¹_K →* C_K` whose range consists exactly of the classes of
content one, i.e. of `ker abs`.

Since `C¹_K` is compact (`NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup`,
which rests on finiteness of the class group and Dirichlet's unit theorem), its continuous image
`ι.range = ker abs` is compact; equivalently the subtype `↥(ker abs)` is a compact topological
space.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open NK.GlobalCFT

namespace Work.SSGRoute.PTW

theorem compactSpace_ker_abs (K : Type) [Field K] [NumberField K] :
    CompactSpace ↥((NK.GlobalCFT.IdeleClassGroup.abs K).ker) := by
  classical
  -- the norm-one idèle class group is compact
  haveI : CompactSpace (IdeleClassGroup.normOneClassGroup K) :=
    IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup (K := K)
  -- the principal idèles inside `𝕀¹K`
  let N : Subgroup (Idele.normOne K) :=
    (Idele.principalSubgroup K).subgroupOf (Idele.normOne K)
  have hmap : N ≤ Subgroup.comap (Idele.normOne K).subtype (Idele.principalSubgroup K) :=
    fun _ hx => hx
  -- the induced homomorphism `C¹_K →* C_K`
  let ι : IdeleClassGroup.normOneClassGroup K →* IdeleClassGroup K :=
    QuotientGroup.map N (Idele.principalSubgroup K) (Idele.normOne K).subtype hmap
  -- it is continuous, being a quotient of the continuous inclusion `𝕀¹K → 𝕀 K`
  have hcont : Continuous ι := by
    refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr ?_
    show Continuous (fun x : Idele.normOne K => ι (QuotientGroup.mk x))
    have h1 : (fun x : Idele.normOne K => ι (QuotientGroup.mk x))
        = ⇑((QuotientGroup.mk' (Idele.principalSubgroup K)).comp (Idele.normOne K).subtype) := by
      funext x
      rw [MonoidHom.comp_apply, QuotientGroup.map_mk, QuotientGroup.mk'_apply]
    rw [h1]
    exact (QuotientGroup.continuous_mk (N := Idele.principalSubgroup K)).comp continuous_subtype_val
  -- and its range is exactly `ker abs`
  have hrange : ι.range = (IdeleClassGroup.abs K).ker := by
    ext z
    constructor
    · intro hz
      rw [MonoidHom.mem_ker]
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hz
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N w
      rw [QuotientGroup.map_mk']
      show (IdeleClassGroup.abs K) (IdeleClassGroup.mk K (x : Idele K)) = 1
      rw [IdeleClassGroup.abs_mk]
      exact Idele.mem_normOne.mp x.2
    · intro hz
      rw [MonoidHom.mem_ker] at hz
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Idele.principalSubgroup K) z
      have hy : y ∈ Idele.normOne K := by
        rw [Idele.mem_normOne]
        have hz' : (IdeleClassGroup.abs K) (IdeleClassGroup.mk K y) = 1 := hz
        rw [IdeleClassGroup.abs_mk] at hz'
        exact hz'
      refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' N ⟨y, hy⟩, ?_⟩
      rw [QuotientGroup.map_mk']
      rfl
  -- the range is compact as a continuous image of a compact space
  have hIc : IsCompact (Set.range ⇑ι) := isCompact_range hcont
  have hIc' : IsCompact ((IdeleClassGroup.abs K).ker : Set (IdeleClassGroup K)) := by
    rw [← MonoidHom.coe_range, hrange] at hIc
    exact hIc
  exact isCompact_iff_compactSpace.mp hIc'

end Work.SSGRoute.PTW
