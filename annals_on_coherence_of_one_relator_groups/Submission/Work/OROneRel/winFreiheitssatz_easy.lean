import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winRho_winRoot

/-!
# The easy half of the Freiheitssatz for the window basis

For the window basis `β = E(D) ∖ T` of `Submission.Work.OROneRel.winBasisDefs` and the deleted walk
word `v = winRoot`, the class map `winRho` sends the normal closure of `v ^ l` into the normal closure
of `u ^ l`: this is immediate from the telescoping identity `winRho v = u`
(`Work.OROneRel.winRho_winRoot`) and the functoriality of the normal closure.

The converse inclusion -- `winRho x ∈ ⟪u ^ l⟫ → x ∈ ⟪v ^ l⟫`, the Freiheitssatz of the domain -- is
`Work.OROneRel.winFreiheitssatz`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The easy half of the Freiheitssatz**: anything in the normal closure of `v ^ l` maps into the
normal closure of `u ^ l`. -/
theorem winRoot_preimage_easy (Wt : ℤ → FreeGroup α) (hW0 : Wt 0 = 1) {c : α → ℤ} {u : FreeGroup α}
    (hu : Work.OROneRel.cohom c u = 1) (lo hi : ℤ) (l : ℕ)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi))
    (hx : x ∈ Subgroup.normalClosure
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) :
    Work.OROneRel.winRho Wt c lo hi x ∈
      Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) := by
  have hv : Work.OROneRel.winRho Wt c lo hi (Work.OROneRel.winRoot Wt c lo hi u) = u :=
    Work.OROneRel.winRho_winRoot Wt hW0 hu lo hi hwin
  have hle : (Subgroup.normalClosure
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))).map
        (Work.OROneRel.winRho Wt c lo hi) ≤
      Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) := by
    refine le_trans (Subgroup.map_normalClosure_le _ _) ?_
    refine Subgroup.normalClosure_mono ?_
    rintro y ⟨z, hz, rfl⟩
    rw [Set.mem_singleton_iff] at hz ⊢
    rw [hz, map_pow, hv]
  exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

end Work.OROneRel
