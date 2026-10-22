import Mathlib
import Submission.Work.TOOLKIT.Levelwise.Maps
import Submission.Work.TOOLKIT.Levelwise.SolidEquivBasic

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.TOOLKIT.Levelwise

/-- If `K` is concentrated in degrees `≤ 0`, then `trunc 0 K` is the single complex with
`K.X 0` in degree `0`: the projection `truncProj K 0` (the identity in degree `0`) is an
isomorphism.  Indeed its component in degree `0` is an isomorphism and all its other
components are maps between zero objects. -/
lemma isIso_truncProj_zero (K : Cpx) (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) :
    IsIso (truncProj K 0) := by
  haveI hcomp : ∀ n : ℤ, IsIso ((truncProj K 0).f n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [truncProj_f_self K 0]
      infer_instance
    · rw [truncProj_f_of_ne K 0 hn]
      refine IsZero.isIso ?_ ?_ 0
      · rcases lt_trichotomy n 0 with h | h | h
        · exact trunc_isZero_X (j := 0) (n := n) (by omega) K
        · exact absurd h hn
        · rw [trunc_X_of_le (j := 0) (n := n) (by omega) K]
          exact hK n h
      · exact isZero_sng_obj_X (q := 0) (n := n) hn (K.X 0)
  exact HomologicalComplex.Hom.isIso_of_components (truncProj K 0)

theorem solidEquiv_truncMap_zero_of {K L : Work.TOOLKIT.Cpx} (f : K ⟶ L) (hK : ∀ q : ℤ, 0 < q → CategoryTheory.Limits.IsZero (K.X q)) (hL : ∀ q : ℤ, 0 < q → CategoryTheory.Limits.IsZero (L.X q)) (hf : Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map (f.f 0))) : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map (Work.TOOLKIT.Levelwise.truncMap f 0)) := by
  haveI hKi : IsIso (truncProj K 0) := isIso_truncProj_zero K hK
  haveI hLi : IsIso (truncProj L 0) := isIso_truncProj_zero L hL
  -- Naturality of `truncProj` in the complex
  have hnat : DerivedCategory.Q.map (truncMap f 0) ≫ DerivedCategory.Q.map (truncProj L 0) =
      DerivedCategory.Q.map (truncProj K 0) ≫
        DerivedCategory.Q.map ((sng 0).map (f.f 0)) := by
    rw [← Functor.map_comp, truncProj_naturality f 0, Functor.map_comp]
  -- Isolate `Q.map (truncMap f 0)` using that the two projections are isomorphisms
  have hkey : DerivedCategory.Q.map (truncMap f 0) =
      DerivedCategory.Q.map (truncProj K 0) ≫
        (DerivedCategory.Q.map ((sng 0).map (f.f 0)) ≫
          inv (DerivedCategory.Q.map (truncProj L 0))) := by
    calc DerivedCategory.Q.map (truncMap f 0)
        = DerivedCategory.Q.map (truncMap f 0) ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = DerivedCategory.Q.map (truncMap f 0) ≫
            (DerivedCategory.Q.map (truncProj L 0) ≫
              inv (DerivedCategory.Q.map (truncProj L 0))) := by rw [IsIso.hom_inv_id]
      _ = (DerivedCategory.Q.map (truncMap f 0) ≫ DerivedCategory.Q.map (truncProj L 0)) ≫
            inv (DerivedCategory.Q.map (truncProj L 0)) := by rw [Category.assoc]
      _ = (DerivedCategory.Q.map (truncProj K 0) ≫
              DerivedCategory.Q.map ((sng 0).map (f.f 0))) ≫
            inv (DerivedCategory.Q.map (truncProj L 0)) := by rw [hnat]
      _ = DerivedCategory.Q.map (truncProj K 0) ≫
            (DerivedCategory.Q.map ((sng 0).map (f.f 0)) ≫
              inv (DerivedCategory.Q.map (truncProj L 0))) := by rw [Category.assoc]
  rw [hkey]
  refine (solidEquiv_iso_conj (DerivedCategory.Q.map (truncProj K 0))
    (DerivedCategory.Q.map ((sng 0).map (f.f 0)))
    (inv (DerivedCategory.Q.map (truncProj L 0))) inferInstance inferInstance).mpr ?_
  simpa only [DerivedCategory.Q_map_single_map] using hf

end Work.TOOLKIT.Levelwise
