import Mathlib
import Submission.Work.WilC1.Defs

namespace Work.WilC1

/-- Pulling back an `REx` set along the reindexing map `f` on the coordinates.  If `X` is cut
out of `κ → ℝ` by an exp-polynomial `P` (in the coordinates `κ ⊕ γ` and their `rexp`s, with a
block of witnesses indexed by the finite type `γ`), then the set of `w : μ → ℝ` whose pullback
`w ∘ f` lies in `X` is cut out by the same polynomial with the variable map
`(κ ⊕ γ) → (μ ⊕ γ)` acting on the coordinate block `κ → μ` by `f` and fixing the witness
block. -/
theorem REx_preimage {κ μ : Type*} (f : κ → μ) {X : Set (κ → ℝ)} (hX : REx κ X) :
    REx μ {w : μ → ℝ | w ∘ f ∈ X} := by
  obtain ⟨γ, hγ, P, hP⟩ := hX
  refine ⟨γ, hγ, MvPolynomial.rename (polyMap (Sum.map f (id : γ → γ))) P, ?_⟩
  -- the variable substitution commutes with the evaluation: pulling back the coordinate block
  -- by `f` and keeping the witnesses `y` fixed
  have hcomp : ∀ (w : μ → ℝ) (y : γ → ℝ),
      (Sum.elim w y) ∘ (Sum.map f (id : γ → γ)) = Sum.elim (w ∘ f) y := by
    intro w y
    funext q
    rcases q with i | j <;> rfl
  ext w
  rw [hP]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [rexpEval_rename, hcomp w y]; exact hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [rexpEval_rename, hcomp w y] at hy; exact hy⟩

end Work.WilC1
