import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.FreiheitssatzCases

namespace Work.OROneRel

universe u

theorem mk_ne_one_of_misses_letter {α : Type u} {r v : FreeGroup α} {a₀ : α}
    (hr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ha₀ : a₀ ∈ Work.OROneRel.relatorLetters r) (hv : a₀ ∉ Work.OROneRel.relatorLetters v)
    (hv1 : v ≠ 1) :
    PresentedGroup.mk ({r} : Set (FreeGroup α)) v ≠ 1 := by
  classical
  -- `v` uses only the generators `T = α \ {a₀}`.
  set T : Set α := {a | a ≠ a₀} with hT
  -- `r` is not supported on `T`, because it uses the letter `a₀ ∉ T`.
  have hTnot : r ∉ Subgroup.closure (FreeGroup.of '' T) := by
    intro hmem
    have hsub : SupportedOn r T := (letters_closure_iff r T).mp hmem
    exact (hsub ha₀) rfl
  have hinj : Function.Injective (presentedGroupMap r T) := freiheitssatz_at r hr T hTnot
  -- `v` is supported on `T`, so it is the image of some word `v'` in `FreeGroup T`.
  have hvT : SupportedOn v T := fun a ha h => hv (h ▸ ha)
  obtain ⟨v', hv'⟩ := exists_lift_of_supportedOn hvT
  -- If `mk v = 1` then `presentedGroupMap r T v' = 1 = presentedGroupMap r T 1`.
  intro h1
  have hzero : presentedGroupMap r T v' = presentedGroupMap r T 1 := by
    rw [map_one]
    show PresentedGroup.mk ({r} : Set (FreeGroup α))
        (FreeGroup.lift (fun a : T => FreeGroup.of (a : α)) v') = 1
    rw [hv', h1]
  have hv'1 : v' = 1 := hinj hzero
  exact hv1 (by rw [← hv', hv'1, map_one])

end Work.OROneRel
