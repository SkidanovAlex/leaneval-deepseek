import Mathlib
import Submission.Work.Properness.BridgeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `HasSurjectiveLift` in terms of the projection `M.pi`

For a closure model `M` of an embedding problem `E` over `ℚ`, the predicate
`M.HasSurjectiveLift` asks for a surjective homomorphism `ψ : G_ℚ →* E.G` with open kernel such
that `M.autCongr (E.π (ψ σ)) = restrictHom M.L σ` for every `σ`.

Since `M.pi : E.G →* Gal(M.L/ℚ)` is by definition the composite `M.autCongr ∘ E.π`
(`Submission.EmbeddingProblem.ClosureModel.pi`), this is exactly the statement that
`M.pi.comp ψ = restrictHom M.L` as homomorphisms of groups.  The present file records that
unfolding: the existence of a surjective lift with open kernel and composite `M.pi` equal to the
restriction map is equivalent to `M.HasSurjectiveLift`.
-/

namespace Work.Properness

/-- **`HasSurjectiveLift`, phrased with the projection `M.pi`.**  The composite condition
`M.pi.comp ψ = restrictHom M.L`, which is the composite of group homomorphisms and therefore
definitionally the pointwise condition of `ClosureModel.HasSurjectiveLift` up to the unfolding
`M.pi g = M.autCongr (E.π g)`, is equivalent to the defining condition of `M.HasSurjectiveLift`. -/
theorem hasSurjectiveLift_iff_exists_properLift {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel) : M.HasSurjectiveLift ↔ ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G, IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ Function.Surjective ψ ∧ M.pi.comp ψ = Work.AbsoluteGalois.restrictHom M.L := by
  constructor
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact ⟨ψ, hopen, hsurj, MonoidHom.ext fun σ => by
      rw [MonoidHom.comp_apply, Submission.EmbeddingProblem.ClosureModel.pi_apply]
      exact hcomp σ⟩
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact ⟨ψ, hopen, hsurj, fun σ => by
      have h := congrFun (congrArg DFunLike.coe hcomp) σ
      rw [MonoidHom.comp_apply, Submission.EmbeddingProblem.ClosureModel.pi_apply] at h
      exact h⟩

end Work.Properness
