import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.KleinTwRuleMem
import Submission.Work.MotK.TwRuling.sdW_kleinTwR_ne_zero
import Submission.Work.MotK.TwRuling.SdThetaFracTopAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

theorem SdThetaFracTop_charNeTwo (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Subfield.closure
      (Set.range (algebraMap (Work.MotK.TGen.sdR K D h) (Work.MotK.TGen.sdA K D h))) = ⊤ := by
  set A := Work.MotK.TGen.sdA K D h with hA
  set T : Subfield A := Subfield.closure (Set.range (algebraMap (Work.MotK.TGen.sdR K D h) A))
    with hT
  have hKm : ∀ k : K, algebraMap K A k ∈ T := by
    intro k; rw [hT]; exact algebraMap_K_mem K D h k
  have hYmem : ∀ i : Fin 5, Work.MotK.TGen.sdY K D h i ∈ T := by
    intro i; rw [hT]; exact sdY_mem K h2 D hD h hh i
  have ht : (RatFunc.X : A) ∈ T := by
    rw [hT]; exact ratFunc_X_mem K h2 D hD h hh
  have hSle : Subfield.closure (Set.range (algebraMap K A)
      ∪ Set.range (Work.MotK.TGen.sdY K D h)) ≤ T := by
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, rfl⟩ := hx; exact hKm k
    · obtain ⟨i, rfl⟩ := hx; exact hYmem i
  have hFmem : ∀ a : ↥(Work.MotK.twistFieldTG K D h),
      algebraMap ↥(Work.MotK.twistFieldTG K D h) A a ∈ T := by
    intro a
    exact hSle (range_algebraMap_subset K D h ⟨a, rfl⟩)
  have hle : IntermediateField.adjoin ↥(Work.MotK.twistFieldTG K D h) ({(RatFunc.X : A)} : Set A)
      ≤ T.toIntermediateField hFmem := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ht
  have htop : T.toIntermediateField hFmem = ⊤ :=
    le_antisymm le_top (by
      rw [← RatFunc.adjoin_X (K := ↥(Work.MotK.twistFieldTG K D h))]
      exact hle)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (T.toIntermediateField hFmem) := by
    rw [htop]
    simp
  exact hx

end Work.MotK.TwRuling
