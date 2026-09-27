import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.ball_K
import Submission.Work.KT.ballK_transfer
import Submission.Work.KT.SG.kpair_R_vanishing
import Submission.Work.KT.ballK_dim2
import Submission.Work.KT.ballK_step

/-!
# `Work.KT.sphKT_ball_K` — the statement of `ball_K`, assembled from its four ingredients

The file `Submission/Work/KT/ball_K.lean` proves `Work.KT.ball_K_of`, which concludes
`∀ V y0 j, BallKStmt V y0 j` from the four ingredient statements

* `ballK_transfer` (change of norm and dimension),
* `SG.kpair_R_vanishing` = `ballK_dim1` (`K̃(D¹/S⁰) = 0`, i.e. injectivity of the augmentation
  on `K₀(Kpair ℝ)`; the module `ball_K` uses the *copy* of that statement in `Work.KT.SG`, since
  `ballK_dim1.lean` currently misses an import and does not compile),
* `ballK_dim2` (the Bott class on `S²`),
* `ballK_step` (the suspension step `d → d + 2`),

but the final theorem `Work.KT.ball_K` in that file is still a `sorry`.  This module performs the
fifteen-line assembly itself, under the name `sphKT_ball_K`, so that the node `Work.KT.sphere_K`
depends only on the four ingredients (all of which are `sorry`-free as soon as
`ballK_dim2`/`fund_product` are) and not on the unfinished final line of `ball_K.lean`.

Nothing here is new mathematics: it is the assembly recorded in
`Submission/Work/KT/NOTES_ext_generator.md` §5(b).
-/

namespace Work.KT

open Matrix

noncomputable section

/-- `K̃(D_V / S_V) = K̃(S^d)`, `d = dim V`: infinite cyclic with `ψ^k = k^j` if `d = 2j`, zero if
`d` is odd — assembled from the four ingredient nodes. -/
theorem sphKT_ball_K (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (y0 : Ball V) (hy0 : y0 ∈ bdry V) (j : ℕ) :
    BallKStmt V y0 hy0 j :=
  ball_K_of
    (fun V W _ _ _ _ _ _ φ y0 hy0 y0' hy0' j h => ballK_transfer V W φ y0 hy0 y0' hy0' j h)
    (fun y0 hy0 z hz => SG.kpair_R_vanishing y0 hy0 z hz)
    (fun y0W hy0W => by
      obtain ⟨H, h0, h1, h2, hψ2, hψ3⟩ := ballK_dim2 y0W hy0W
      refine ⟨fun _ => ⟨⟨H, h0, h1, h2⟩, ?_, ?_⟩, fun hh => ?_⟩
      · intro ψ hψ z hz
        obtain ⟨k, rfl⟩ := h2 z hz
        rw [map_zsmul, hψ2 ψ hψ, ← natCast_zsmul H 2, pow_one, smul_smul, smul_smul]
        congr 1
        ring
      · intro ψ hψ z hz
        obtain ⟨k, rfl⟩ := h2 z hz
        rw [map_zsmul, hψ3 ψ hψ, ← natCast_zsmul H 3, pow_one, smul_smul, smul_smul]
        congr 1
        ring
      · rw [finrank_euclideanSpace_fin] at hh
        omega)
    (fun V W _ _ _ _ _ _ y0V hV y0W hW y0 hy0 hVd hWd j h =>
      ballK_step V W y0V hV y0W hW y0 hy0 hVd hWd j h)
    V y0 hy0 j

end

end Work.KT
