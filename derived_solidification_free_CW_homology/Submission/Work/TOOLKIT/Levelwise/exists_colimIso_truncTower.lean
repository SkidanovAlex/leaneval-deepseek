import Mathlib
import Submission.Work.TOOLKIT.Levelwise.Tower
import Submission.Work.TOOLKIT.Levelwise.Maps
import Submission.Work.TOOLKIT.Levelwise.Basic

namespace Work.TOOLKIT.Levelwise

open CategoryTheory Limits

/-- In degree `n` above the target index `b`, the inclusion of truncations
`truncIncl h : trunc b K ⟶ trunc a K` is the comparison of two copies of `K.X n`, i.e. an
`eqToHom`, hence invertible. -/
lemma isIso_truncIncl_f_of_le {a b n : ℤ} (h : a ≤ b) (hb : b ≤ n) (K : Cpx) :
    IsIso ((truncIncl h K).f n) := by
  rw [truncIncl_f_of_le h hb K, ← inv_eqToHom (trunc_X_of_le (le_trans h hb) K)]
  infer_instance

/-- In degree `n` above `b`, the component of the inclusion `truncIntoK b K : trunc b K ⟶ K`
is an `eqToHom`, hence invertible. -/
lemma isIso_truncIntoK_f_of_le {b n : ℤ} (hb : b ≤ n) (K : Cpx) :
    IsIso ((truncIntoK b K).f n) := by
  rw [truncIntoK_f_of_le hb K]
  infer_instance

/-- The cocone exhibited by the inclusions of the stages `T_m K = trunc (-m) K` into `K` is a
colimit cocone.  Indeed, in each degree `q` the tower is eventually constant — once `-m ≤ q`,
the term `(T_m K).X q` is `K.X q` and all transition maps are `eqToHom`s — and the leg at a
stage with `-m ≤ q` is already an isomorphism. -/
noncomputable def truncTowerCocone_isColimit (K : Cpx) : IsColimit (truncTowerCocone K) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun q => ?_)
  set i₀ : ℕ := Int.toNat (-q) with hi₀
  have hb : -(i₀ : ℤ) ≤ q := by
    have h := Int.self_le_toNat (-q)
    rw [← hi₀] at h
    omega
  haveI : IsIso (((HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) q).mapCocone
      (truncTowerCocone K)).ι.app i₀) := by
    change IsIso ((truncIntoK (-(i₀ : ℤ)) K).f q)
    exact isIso_truncIntoK_f_of_le hb K
  apply Functor.IsEventuallyConstantFrom.isColimitOfIsIso (i₀ := i₀)
  intro j f
  have hle : i₀ ≤ j := leOfHom f
  change IsIso ((truncIncl (a := -(j : ℤ)) (b := -(i₀ : ℤ)) (by omega) K).f q)
  exact isIso_truncIncl_f_of_le _ hb K

theorem exists_colimIso_truncTower (K : Work.TOOLKIT.Cpx) : Exists (fun e : CategoryTheory.Iso (CategoryTheory.Limits.colimit (Work.TOOLKIT.Levelwise.truncTower K)) K => forall m : Nat, CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (Work.TOOLKIT.Levelwise.truncTower K) m) e.hom = Work.TOOLKIT.Levelwise.truncIntoK (Int.negOfNat m) K) := by
  refine ⟨(IsColimit.coconePointUniqueUpToIso (colimit.isColimit (truncTower K))
    (truncTowerCocone_isColimit K) : colimit (truncTower K) ≅ K), ?_⟩
  intro m
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (truncTower K))
    (truncTowerCocone_isColimit K) m
  exact h.trans rfl

end Work.TOOLKIT.Levelwise
