import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

/-- The normalisation of a locally constant `2`-coboundary on `D` is again a locally constant
`2`-coboundary on `D`: if `c = d¹ E` on `D × D` then `normC c = d¹ (E - const (c 1 1))`
(note `E 1 = c 1 1`). -/
theorem normC_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.coboundaries2 p k Ω K M D) :
    normC p k Ω K M c ∈ Work.SSGRoute.coboundaries2 p k Ω K M D := by
  obtain ⟨E, hE, hEc⟩ := hc
  refine ⟨fun g => E g - c 1 1, ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hE
    exact ⟨U, hUo, fun g hg u hu huH => by
      show E (g * u) - c 1 1 = E g - c 1 1
      rw [hU g hg u hu huH]⟩
  · intro g hg h hh
    show normC p k Ω K M c g h
      = SSGRoute.res k K g • (E h - c 1 1) - (E (g * h) - c 1 1) + (E g - c 1 1)
    rw [normC_apply, hEc g hg h hh]
    simp only [smul_sub]
    abel

end Work.SSGRoute.HSRow
