import Submission.Work.Stems.Hur2.SquareFill

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The four faces of the filling square

`square_filling`: the map produced by `exists_square_of_loop` has, on the four faces of the square,
the three prescribed paths and the constant path at the base point.

The two ingredients are

* `exists_square_of_loop`, which gives `K : C(IC 2, X)` with `K (bd t) = loopPath p₀ pe p₁ t` on the
  whole boundary;
* the four *point identities* `(faceCM i b) t = bd (pt (t 0))` (proved below by `rw [bd_…]`,
  `funext`, `fin_cases` and `simp [faceCM_apply, faceFun_apply, Fin.succAboveCases]`), which
  identify the faces of the square with the four edges in the `bd`-parametrisation.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- **The 2-cube filling a square of paths.**  Given `γ₀ : x₀ → a`, `e : a → b`, `γ₁ : x₀ → b`
there is a square `K : I² → X` whose four faces are `x₀`, `γ₀`, `e` and `γ₁`. -/
theorem square_filling {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    {x₀ a b : X} (γ₀ : Path x₀ a) (e : Path a b) (γ₁ : Path x₀ b) :
    ∃ K : C(IC 2, X),
      (∀ t : IC 1, K (faceCM (0 : Fin 2) (0 : unitInterval) t) = x₀) ∧
      (∀ t : IC 1, K (faceCM (1 : Fin 2) (0 : unitInterval) t) = γ₀ (t 0)) ∧
      (∀ t : IC 1, K (faceCM (0 : Fin 2) (1 : unitInterval) t) = e (t 0)) ∧
      (∀ t : IC 1, K (faceCM (1 : Fin 2) (1 : unitInterval) t) = γ₁ (t 0)) := by
  obtain ⟨K, hK⟩ := exists_square_of_loop x₀ γ₀ e γ₁ γ₀.source'
    (e.source'.trans γ₀.target'.symm) (e.target'.trans γ₁.target'.symm) γ₁.source'
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [show (faceCM (0 : Fin 2) (0 : unitInterval)) t = bd (leftPt (t 0)) from by
      rw [bd_left]
      funext j
      fin_cases j <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases], hK]
    exact loopPath_leftPt _ _ _ _
  · intro t
    rw [show (faceCM (1 : Fin 2) (0 : unitInterval)) t = bd (quarter (t 0)) from by
      rw [bd_quarter_bot]
      funext j
      fin_cases j <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, Fin.zero_eta], hK]
    exact loopPath_quarter _ _ _ _
  · intro t
    rw [show (faceCM (0 : Fin 2) (1 : unitInterval)) t = bd (rightPt (t 0)) from by
      rw [bd_right]
      funext j
      fin_cases j <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, Fin.zero_eta], hK]
    exact loopPath_rightPt _ _ _ _
  · intro t
    rw [show (faceCM (1 : Fin 2) (1 : unitInterval)) t = bd (topPt (t 0)) from by
      rw [bd_top]
      funext j
      fin_cases j <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, Fin.zero_eta], hK]
    exact loopPath_topPt _ _ _ _

end

end Work.Stems.Hur2
