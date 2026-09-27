import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.Rank

/-- Every idempotent complex matrix is Murray--von Neumann equivalent (`Work.KT.Mat.MvN`, the
relation of `Submission/Work/KT/Defs.lean`) to the identity matrix of size equal to its rank.

Route: `P` is the projection onto `V = range P.mulVecLin` along `W = ker P.mulVecLin`, and
`V` and `W` are complementary (`LinearMap.IsIdempotentElem.isCompl`).  A linear equivalence
`e : (Fin P.rank → ℂ) ≃ₗ V` exists by `LinearEquiv.ofFinrankEq` (as `Matrix.rank` is by definition
the `finrank` of the range).  Then the matrix `b` of `V.subtype ∘ₗ e` and the matrix `a` of
`e.symm ∘ₗ V.projectionOnto W h` satisfy `b * a = P` and `a * b = 1`. -/
theorem mvN_one_rank_v2 (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P) :
    Work.KT.Mat.MvN (⟨n, P⟩ : Work.KT.Mat ℂ) (Work.KT.Mat.one ℂ P.rank) := by
  -- `P.mulVecLin` is idempotent, being the linear map underlying the idempotent matrix `P`.
  have hf : IsIdempotentElem P.mulVecLin := by
    show P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, hP]
  -- `V = range P`, `W = ker P`, a direct sum decomposition of `Fin n → ℂ`.
  let V : Submodule ℂ (Fin n → ℂ) := P.mulVecLin.range
  let W : Submodule ℂ (Fin n → ℂ) := P.mulVecLin.ker
  have hcompl : IsCompl V W := LinearMap.IsIdempotentElem.isCompl hf
  -- `P.mulVecLin` is the projection onto `V` along `W`.
  have heq : P.mulVecLin = V.projection W hcompl := LinearMap.IsIdempotentElem.eq_projection hf
  -- `V` has dimension `P.rank`, by definition of `Matrix.rank`.
  have hVrank : Module.finrank ℂ V = P.rank := by rw [Matrix.rank]
  have hrank : Module.finrank ℂ (Fin P.rank → ℂ) = Module.finrank ℂ V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hVrank.symm
  -- A linear equivalence `(Fin P.rank → ℂ) ≃ₗ V`.
  let e : (Fin P.rank → ℂ) ≃ₗ[ℂ] V := LinearEquiv.ofFinrankEq (Fin P.rank → ℂ) V hrank
  -- `B` is `V ⊆ Fin n → ℂ` in coordinates, `A` is the projection `V` followed by `e.symm`.
  let B : (Fin P.rank → ℂ) →ₗ[ℂ] (Fin n → ℂ) := V.subtype ∘ₗ e.toLinearMap
  let A : (Fin n → ℂ) →ₗ[ℂ] (Fin P.rank → ℂ) :=
    e.symm.toLinearMap ∘ₗ V.projectionOnto W hcompl
  have hproj : V.projectionOnto W hcompl ∘ₗ V.subtype = LinearMap.id :=
    Submodule.projectionOnto_comp_subtype hcompl
  have htoLin : ∀ M : Matrix (Fin n) (Fin n) ℂ, Matrix.toLin' M = M.mulVecLin := fun _ => rfl
  -- `B ∘ A = P`: the projection onto `V` along `W`, which is `P`.
  have hBA : B.comp A = P.mulVecLin := by
    apply LinearMap.ext
    intro x
    show V.subtype (e (e.symm (V.projectionOnto W hcompl x))) = P.mulVecLin x
    rw [e.apply_symm_apply, heq]
    rfl
  -- `A ∘ B = id`: the projection fixes `V`, and `e.symm ∘ e = id`.
  have hAB : A.comp B = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show e.symm (V.projectionOnto W hcompl (V.subtype (e x))) = x
    rw [← LinearMap.comp_apply, hproj, LinearMap.id_apply, e.symm_apply_apply]
  -- Unfold `Mat.one` so that the sizes are `n` and `P.rank`.
  change Work.KT.Mat.MvN (⟨n, P⟩ : Work.KT.Mat ℂ) (⟨P.rank, 1⟩ : Work.KT.Mat ℂ)
  refine ⟨LinearMap.toMatrix' A, LinearMap.toMatrix' B, ?_, ?_⟩
  · show LinearMap.toMatrix' B * LinearMap.toMatrix' A = P
    have key : Matrix.toLin' (LinearMap.toMatrix' B * LinearMap.toMatrix' A) = P.mulVecLin := by
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
      exact hBA
    rw [← LinearMap.toMatrix'_toLin' (LinearMap.toMatrix' B * LinearMap.toMatrix' A), key,
      ← htoLin P]
    exact LinearMap.toMatrix'_toLin' P
  · show LinearMap.toMatrix' A * LinearMap.toMatrix' B = 1
    have key : Matrix.toLin' (LinearMap.toMatrix' A * LinearMap.toMatrix' B) = LinearMap.id := by
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
      exact hAB
    rw [← LinearMap.toMatrix'_toLin' (LinearMap.toMatrix' A * LinearMap.toMatrix' B), key]
    simp

end Work.KT.Rank
