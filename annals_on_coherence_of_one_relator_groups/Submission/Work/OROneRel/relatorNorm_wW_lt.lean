import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

universe u

namespace Work.OROneRel

theorem relatorNorm_wW_lt {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (ht : t ∈ Work.OROneRel.relatorLetters u) :
    Work.OROneRel.relatorNorm (Work.OROneRel.wW c t u) < Work.OROneRel.relatorNorm u := by
  classical
  have hb' : ∃ b, (t, b) ∈ wordOf u := by
    rw [relatorLetters] at ht
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, by simpa [wordOf] using hb⟩
  have hnorm : relatorNorm (wW c t u) ≤ (wWL c t u).length := by
    rw [wW, relatorNorm]
    exact @FreeGroup.norm_mk_le (wBeta c t u) (wWL c t u) (Classical.decEq _)
  have hlen : (wWL c t u).length = (wvListAux c t 0 (wordOf u)).length := by
    rw [wWL, List.length_map]
  have hlt : (wvListAux c t 0 (wordOf u)).length < (wordOf u).length :=
    wvListAux_length_lt c t 0 (wordOf u) hb'
  have hword : (wordOf u).length = relatorNorm u := by rw [relatorNorm, wordOf]; rfl
  rw [hlen] at hnorm
  exact lt_of_le_of_lt hnorm (hword ▸ hlt)

end Work.OROneRel
