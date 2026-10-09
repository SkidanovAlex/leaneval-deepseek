import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
import Submission.Work.SSGRoute.HRec.mem_normSet_of_not_isNegAt
import Submission.Work.SSGRoute.HRec.not_isNegAt_of_mem_normSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reverse Artin–Schreier characterisation, assembled

For the involution `c` attached to a real place `w` (with `Ψ` the lift of steps 1–2 and `hΨ`, `hc`
its defining properties), the Kummer character of `a : kˣ` at `c` vanishes exactly when `a` is not
negative at `w`.

Pure composition of cells proved earlier in this stretch: `ArchDefs.kummerChar_eq_zero_iff_mem_normSet`
sends the left side to `a ∈ normSet c.toRingEquiv`, and the two branches
`HRec.mem_normSet_of_not_isNegAt` (`⟸`) and `HRec.not_isNegAt_of_mem_normSet` (`⟹`) close it.
The character lemma takes `hc : c ^ 2 = 1` (not `c * c = 1`).
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

theorem kummerChar_eq_zero_iff_not_isNegAt {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (w : NumberField.InfinitePlace k) (hw : w.IsReal)
    {Ψ : Ω →+* ℂ} {c : Ω ≃ₐ[k] Ω} (hc2 : c ^ 2 = 1)
    (hΨ : ∀ a : k, Ψ (algebraMap k Ω a) =
      (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ))
    (hc : ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x))
    (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
  rw [Work.SSGRoute.ZDataTwo.kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc2 a]
  exact ⟨fun hm => not_isNegAt_of_mem_normSet (Ω := Ω) w hw hΨ hc a hm,
    fun ha => mem_normSet_of_not_isNegAt (Ω := Ω) w hw hΨ hc a ha⟩

end Work.SSGRoute.HRec
