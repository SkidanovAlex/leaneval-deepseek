import Mathlib
import Submission.Work.KT.clipP_range_defs

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

/-- Multiplication by the inverse of a unit matrix is injective on vectors. -/
lemma mulVec_unit_injective {S : Type} [Ring S] {N : ℕ} (G : (Matrix (Fin N) (Fin N) S)ˣ) :
    Function.Injective (fun v : Fin N → S => (↑(G⁻¹) : Matrix (Fin N) (Fin N) S) *ᵥ v) := by
  intro f f' hf
  have h := congrArg (fun v => (↑G : Matrix (Fin N) (Fin N) S) *ᵥ v) hf
  simpa only [Matrix.mulVec_mulVec, Units.val_mul, Units.mul_inv, Matrix.one_mulVec] using h

/-- The patched module of `γ` embeds into the range of the clutching projection: the
vector `z ↦ (G⁻¹ *ᵥ padVec f 0, padVec g 0)` loses no information. -/
theorem clipRangeFun_injective (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ)
    (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    Function.Injective (clipRangeFun V n γ G hG) := by
  intro z z' h
  have h1 : (↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ)) =
      (↑(G⁻¹) : BallMat V n) *ᵥ padVec z'.1.1 (0 : Fin n → C(Ball V, ℂ)) := by
    funext j
    exact congrArg (fun w : TwoDisk V => w.1.1) (congrFun h j)
  have h2 : padVec z.1.2 (0 : Fin n → C(Ball V, ℂ)) =
      padVec z'.1.2 (0 : Fin n → C(Ball V, ℂ)) := by
    funext j
    exact congrArg (fun w : TwoDisk V => w.1.2) (congrFun h j)
  have he1 : z.1.1 = z'.1.1 := (padVec_inj (mulVec_unit_injective G h1)).1
  have he2 : z.1.2 = z'.1.2 := (padVec_inj h2).1
  exact Subtype.ext (Prod.ext he1 he2)

end

end Work.KT
