import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.OrthTwoAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Archimedean local norms from the involution condition (`p = 2`)

`Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition`: if a Kummer character at `p = 2`
vanishes at every involution of `K.fixingSubgroup` (the hypothesis `hginf` of the target), then —
for **any** finite Galois level `F/↥K` — the archimedean components of the element are local norms.

The dictionary is the same as in `OrthTwoAux.hapos_arch_localNorm_aux`, with `hapos` replaced by the
involution condition on `bg` and `OrthTwoAux.not_isNegAt_of_involution_condition` supplying the
total positivity.
-/

namespace Work.SSGRoute.ZDataTwo

open NumberField

/-- **The archimedean components are local norms, from the involution condition.** -/
theorem arch_localNorm_of_involution_condition
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    (h : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ b
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    ∀ w : NumberField.InfinitePlace ↥K,
      NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
          (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hACK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- `b` is not negative at any real place
  have hnotneg : ∀ w : NumberField.InfinitePlace ↥K, ¬ IsNegAt w b :=
    not_isNegAt_of_involution_condition k Ω K ζ hζ b h
  -- total positivity
  have hpos : ∀ (w : NumberField.InfinitePlace ↥K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap ↥K w.Completion ((b : ↥K))) := by
    intro w hw
    have h1 : ¬ (NumberField.InfinitePlace.embedding_of_isReal hw ((b : ↥K)) < 0) :=
      fun hlt => hnotneg w ⟨hw, hlt⟩
    have h2 : NumberField.InfinitePlace.embedding_of_isReal hw ((b : ↥K)) ≠ 0 := by
      simpa using (map_ne_zero (NumberField.InfinitePlace.embedding_of_isReal hw)) b.ne_zero
    have h3 : 0 < NumberField.InfinitePlace.embedding_of_isReal hw ((b : ↥K)) :=
      lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    simpa [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using h3
  intro w
  exact Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
    (K := ↥K) (L := ↥F) b w hpos

end Work.SSGRoute.ZDataTwo
