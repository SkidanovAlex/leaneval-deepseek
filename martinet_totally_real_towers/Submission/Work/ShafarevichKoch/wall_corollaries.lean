import Mathlib
import Submission.Work.ShafarevichKoch.wall_of_kcClosedRelationCount_and_gaschutzDictionary
import Submission.Work.ShafarevichKoch.Kc

/-!
# The caller-facing walls from the closed relation count and Gaschütz's dictionary

**Module** `Submission.Work.ShafarevichKoch.wall_corollaries`.  Immediate consequences of
`Work.ShafarevichKoch.wall_of_kcClosedRelationCount_and_gaschutzDictionary` in the shapes the
requester consumes: the unramified pro-`2` tower wall and the bounded-root-discriminant tower wall
(`Submission.NumberField.*`), plus the statement that every degree bound is attained by an
unramified level of `Kc` with unchanged root discriminant.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- The unramified pro-`2` tower wall of `Kc`, from the classical (closed) relation count and
Hopf--Gaschütz. -/
theorem unramifiedPro2TowerWall_of_kcClosedRelationCount_and_gaschutzDictionary
    (h : KcClosedRelationCount) (hdict : Work.HopfGaschutz.GaschutzDictionary 2) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  Work.ClassFieldTower.unramifiedPro2TowerWall_of_infiniteProTwoExtension
    (wall_of_kcClosedRelationCount_and_gaschutzDictionary h hdict)

/-- The bounded-root-discriminant tower wall, from the same two inputs. -/
theorem boundedRdTowerWall_of_kcClosedRelationCount_and_gaschutzDictionary
    (h : KcClosedRelationCount) (hdict : Work.HopfGaschutz.GaschutzDictionary 2) :
    Submission.NumberField.BoundedRdTowerWall :=
  Submission.NumberField.boundedRdTowerWall_of_unramifiedPro2TowerWall
    (unramifiedPro2TowerWall_of_kcClosedRelationCount_and_gaschutzDictionary h hdict)

/-- **Asymptotically good unramified levels of `Kc`**: for every `N` there is a finite Galois
`L/Kc` with `[L : Kc] ≥ N`, `𝒟_{L/Kc} = 1` and `rootDiscr L = rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_of_kcClosedRelationCount_and_gaschutzDictionary
    (h : KcClosedRelationCount) (hdict : Work.HopfGaschutz.GaschutzDictionary 2) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  obtain ⟨M, hM⟩ := wall_of_kcClosedRelationCount_and_gaschutzDictionary h hdict
  exact Work.ClassFieldTower.exists_unramifiedLevel_of_infinite (F := Kc) (p := 2) M hM N

end Work.ShafarevichKoch
