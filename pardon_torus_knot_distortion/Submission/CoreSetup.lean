import ChallengeDeps
import Submission.Basic
import Submission.Extract
import Submission.Work.TorusCover.Main
import Submission.Work.Geometry.periodic_bounded
import Submission.Work.Geometry.diameter_systole
import Submission.Work.Geometry.fderiv_bound_on_bounded

/-!
# Setting up the geometric data of the challenge in the `TorusCover` vocabulary

For a knot `K` satisfying the class hypothesis of the challenge, its curve lies on the
embedded torus `F` parametrised by

  `Ψ : ℝ × ℝ → ℝ³,  Ψ x y = Φ.Hinv 1 (torusMap x y)`,

and its winding vector in that torus is `(p, q)`.  In particular the curve is
*essential* (not null-homotopic in `F`), which is what starts the shrinking
argument of the core: a large ball whose intersection with `F` contains an
essential loop.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- The embedding into `ℝ³` of the standard torus determined by the inverse of the
time-one map of the ambient isotopy. -/
noncomputable def psiOf (Φ : AmbientIsotopy) : ℝ → ℝ → R3 :=
  fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)

/-- Under the class hypothesis, the curve of `K` has winding vector `(p, q)` in the
parametrised torus `psiOf Φ`. -/
theorem curve_hasWinding {p q : ℕ} (Φ : AmbientIsotopy) (σ : CircleReparam) (K : Knot)
    (h : ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    Work.TorusCover.HasWinding (psiOf Φ) K.curve ((p : ℤ), (q : ℤ)) := by
  have h1 := Work.TorusCover.hasWinding_comp_standardTorusCurve p q (Φ.Hinv 1) σ
  have hfun : (fun t => Φ.Hinv 1 (standardTorusCurve p q (σ.f t))) = K.curve :=
    funext fun t => (curve_eq_inv_comp Φ σ K h t).symm
  rw [hfun] at h1
  exact h1

/-- Under the class hypothesis with `p, q > 0`, the curve of `K` is essential on the
parametrised torus `psiOf Φ`: it is not null-homotopic there. -/
theorem curve_isEssential {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (Φ : AmbientIsotopy)
    (σ : CircleReparam) (K : Knot)
    (h : ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    Work.TorusCover.IsEssential (psiOf Φ) K.curve := by
  refine ⟨((p : ℤ), (q : ℤ)), ?_, curve_hasWinding Φ σ K h⟩
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  intro hcon
  exact hpz (congrArg Prod.fst hcon)

/-- The parametrised torus `psiOf Φ` satisfies all the hypotheses of the
`TorusCover` chapter (periodicity, injectivity mod `2π`, continuity, and a uniform
positive lower bound for the derivative), with *some* positive constant `c`. -/
theorem exists_torusParam_psiOf (Φ : AmbientIsotopy) :
    ∃ P : Work.TorusCover.TorusParam, P.psi = psiOf Φ := by
  obtain ⟨P0, hP0, -⟩ := Work.TorusCover.exists_torusParam_torusMap
  have hΨ : ContDiff ℝ (1 : ℕ∞) (fun x : R3 => Φ.H 1 x) :=
    (Φ.smooth.comp (f := fun x : R3 => ((1 : ℝ), x)) (by fun_prop)).of_le (by simp)
  have hΨinv : ContDiff ℝ (1 : ℕ∞) (fun x : R3 => Φ.Hinv 1 x) :=
    (Φ.smooth_inv.comp (f := fun x : R3 => ((1 : ℝ), x)) (by fun_prop)).of_le (by simp)
  have hbdd : Bornology.IsBounded (Set.range fun p : ℝ × ℝ => Φ.Hinv 1 (P0.psi p.1 p.2)) := by
    refine Work.Geometry.periodic_bounded (fun x y => Φ.Hinv 1 (P0.psi x y)) ?_ ?_ ?_
    · exact hΨinv.continuous.comp P0.contDiff.continuous
    · intro x y
      exact congrArg (Φ.Hinv 1) (P0.periodic_fst x y)
    · intro x y
      exact congrArg (Φ.Hinv 1) (P0.periodic_snd x y)
  obtain ⟨C, -, hbound⟩ :=
    Work.Geometry.fderiv_bound_on_bounded (Φ.H 1) hΨ
      (Set.range fun p : ℝ × ℝ => Φ.Hinv 1 (P0.psi p.1 p.2)) hbdd
  obtain ⟨P', hP'psi, -⟩ := Work.TorusCover.exists_torusParam_comp P0 (Φ.H 1) (Φ.Hinv 1)
    hΨ hΨinv (fun x => Φ.inv_left 1 x) (fun x => Φ.inv_right 1 x) (max C 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (fun z hz => le_trans (hbound z hz) (le_max_left _ _))
  exact ⟨P', by rw [hP'psi, hP0]; rfl⟩

end Submission
