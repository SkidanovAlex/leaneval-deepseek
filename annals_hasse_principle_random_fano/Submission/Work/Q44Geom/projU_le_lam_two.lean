import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.Q44Geom.projU_toE_add_smul
import Submission.Work.Q44Geom.not_mem_zspan_of_linIndep_two

/-!
# `‖projU (toE x) (toE w)‖ ≤ lam N 2` for a rank-`2` lattice `N = span{x,w}`

Let `N ⊆ ℤ^5` be a rank-`2` lattice spanned by `x ≠ 0` and `w`.  The point of the lemma is
that the length of the component of `w` orthogonal to `x`,

  `p = projU (toE x) (toE w)`,

is at most the *second successive minimum* `lam N 2`, even though the particular basis `(x,w)`
may be far from reduced.

The mechanism is that coordinates in the basis `(x,w)` give a surjection
`ψ : N → ℤ`, `ψ (a • x + b • w) = b`, whose kernel is `ℤ x`; hence every lattice vector
outside `ℤ x` has norm at least `‖p‖` (its orthogonal component is `ψ` times `p` by
`Work.Q44Geom.projU_toE_add_smul`, and `|ψ| ≥ 1`).  Since two independent lattice vectors
cannot both lie in the rank-`1` module `ℤ x` (this is
`Work.Q44Geom.not_mem_zspan_of_linIndep_two`), one of the two vectors supplied by the second
successive minimum has norm at least `‖p‖`, whence `‖p‖ ≤ lam N 2`.

Nothing here needs `x, w` to be linearly independent, only that `N` has rank `2` (so that two
independent lattice vectors exist).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

/-- Every vector of `N = span{x,w}` which is not an integral multiple of `x` has norm at least
the length of the orthogonal component of `w` with respect to `x`.

Indeed, writing `v = a • x + b • w` we must have `b ≠ 0`, and `projU (toE x)` sends `toE v` to
`b • projU (toE x) (toE w)`, so `‖toE v‖ ≥ ‖projU (toE x) (toE v)‖ = |b| ‖p‖ ≥ ‖p‖`. -/
lemma projU_le_eNorm_of_not_smul (N : Submodule ℤ (Fin 5 → ℤ)) (x w v : Fin 5 → ℤ)
    (hx0 : x ≠ 0) (hspan : N = Submodule.span ℤ ({x, w} : Set (Fin 5 → ℤ)))
    (hvN : v ∈ N) (hnotz : ∀ c : ℤ, v ≠ c • x) :
    ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖ ≤ Work.HP.eNorm v := by
  classical
  have hmem : v ∈ Submodule.span ℤ ({x, w} : Set (Fin 5 → ℤ)) := by
    rw [← hspan]; exact hvN
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  -- the `w`-coordinate of `v` is nonzero
  have hbne : b ≠ 0 := by
    intro hb
    exact hnotz a (by rw [← hab, hb, zero_smul, add_zero])
  -- projecting kills the `x`-component, leaving `b` times `p`
  have hproj : Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE v)
      = (b : ℝ) • Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w) := by
    have h := projU_toE_add_smul x w hx0 a b
    rwa [hab] at h
  have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
    have h := Int.one_le_abs hbne
    exact_mod_cast h
  have hnorm : ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖
      ≤ ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE v)‖ := by
    rw [hproj, norm_smul, Real.norm_eq_abs]
    calc ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖
        = 1 * ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖ :=
          (one_mul _).symm
      _ ≤ |(b : ℝ)| * ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖ :=
          mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
  calc ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖
      ≤ ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE v)‖ := hnorm
    _ ≤ ‖Work.HP.Q44Child.toE v‖ := Work.HP.norm_projU_le _ _
    _ = Work.HP.eNorm v := Work.HP.Q44Child.norm_toE v

theorem projU_le_lam_two (N : Submodule ℤ (Fin 5 → ℤ)) (hN : Work.HP.rk N = 2)
    (x w : Fin 5 → ℤ) (hxN : x ∈ N) (hwN : w ∈ N) (hx0 : x ≠ 0)
    (hspan : N = Submodule.span ℤ ({x, w} : Set (Fin 5 → ℤ))) :
    ‖Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w)‖ ≤ Work.HP.lam N 2 := by
  classical
  -- two linearly independent lattice vectors, of norm at most `lam N 2`
  obtain ⟨f, hfN, hfI, hfb⟩ :=
    Work.HP.Q44Child.lamAttained_aux (i := 2) N (le_of_eq hN.symm)
  -- at least one of them is not an integral multiple of `x`
  have hsome : (∀ c : ℤ, f 0 ≠ c • x) ∨ (∀ c : ℤ, f 1 ≠ c • x) :=
    not_mem_zspan_of_linIndep_two x hfI
  rcases hsome with h | h
  · exact (projU_le_eNorm_of_not_smul N x w (f 0) hx0 hspan (hfN 0) h).trans (hfb 0)
  · exact (projU_le_eNorm_of_not_smul N x w (f 1) hx0 hspan (hfN 1) h).trans (hfb 1)

end Work.Q44Geom
