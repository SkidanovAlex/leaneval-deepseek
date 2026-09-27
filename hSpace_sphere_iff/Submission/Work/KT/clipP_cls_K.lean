import Mathlib
import Submission.Work.KT.clipP_cls
import Submission.Work.KT.sphere_K_even

/-!
# The `K₀`-class of the clutching projection (`Work.KT.cls_clipP`)

The vanishing of the reduced `K`-theory of the odd sphere `S^{2j+1}` (`Work.KT.sphere_K_even`,
transported from the odd clause of `Work.KT.ball_K`) supplies the hypothesis of
`Work.KT.cls_clipP_of_vanishing`.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `K₀`-class of the clutching projection of a unit is the class of the trivial bundle of
rank `n`. -/
theorem cls_clipP (j : ℕ) (hV : Module.finrank ℝ V = 2 * j + 1) (n : ℕ)
    (gamma : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n gamma) :
    cls (⟨n + n, clipP V n gamma G hG⟩ : Mat (TwoDisk V)) = cls (Mat.one (TwoDisk V) n) :=
  cls_clipP_of_vanishing V j hV n gamma G hG fun t0 z hz =>
    sphere_K_even (WithLp 2 (V × ℝ)) j
      (by rw [(WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq, Module.finrank_prod, hV,
        Module.finrank_self]) t0 z hz

end

end Work.KT
