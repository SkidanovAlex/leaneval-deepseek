import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Characters

theorem cfInner_vchar_eq_coeff {G : Type*} [Group G] [Fintype G]
    (c : ↥(Work.CharCore.Irr G) → ℤ) (j : ↥(Work.CharCore.Irr G)) :
    Work.CharCore.cfInner (∑ χ : ↥(Work.CharCore.Irr G), (c χ : ℂ) • (χ : G → ℂ))
      (j : G → ℂ) = (c j : ℂ) := by
  rw [Work.CharCore.cfInner_sum_smul_left]
  rw [Finset.sum_eq_single j]
  · rw [Work.CharCore.irr_orthonormal (j : G → ℂ) (j : G → ℂ) j.2 j.2]
    simp
  · intro χ _ hχ
    have hne : (χ : G → ℂ) ≠ (j : G → ℂ) := fun h => hχ (Subtype.ext h)
    rw [Work.CharCore.irr_orthonormal (χ : G → ℂ) (j : G → ℂ) χ.2 j.2]
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Work.BrauerSuzuki.Characters
