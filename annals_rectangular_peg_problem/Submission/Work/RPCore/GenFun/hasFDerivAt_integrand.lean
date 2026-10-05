import Mathlib

namespace Work.RPCore.GenFun

/-- The Fréchet derivative of the integrand `z ↦ B (b (t • z)) z`.

`B` is a continuous bilinear form, `b` is `C³`, and the closedness/symmetry
hypothesis `hclosed` records that the bilinear pairing of `fderiv b y ·` with
a vector is symmetric in the two vectors.  Writing the map as the composition
of `z ↦ (b (t • z), z)` with the bounded bilinear map `(a, c) ↦ B a c`, the
derivative is `B (t • fderiv b (t • y) y + b (t • y))` (a linear functional),
where `hclosed` is used to move `y` from the second slot of `B` to the outside. -/
theorem hasFDerivAt_integrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b : E → E) (hb : ContDiff ℝ 3 b)
    (hclosed : ∀ y u v, B (fderiv ℝ b y u) v = B (fderiv ℝ b y v) u)
    (t : ℝ) (y : E) :
    HasFDerivAt (fun z : E => B (b (t • z)) z)
      (B (t • fderiv ℝ b (t • y) y + b (t • y))) y := by
  -- `b` is differentiable and its derivative at `t • y` is `fderiv ℝ b (t • y)`
  have hb_diff : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hb_deriv : HasFDerivAt b (fderiv ℝ b (t • y)) (t • y) :=
    hb_diff.differentiableAt.hasFDerivAt
  -- the map `z ↦ t • z` is linear with derivative `t • 1`
  have hsmul : HasFDerivAt (fun z : E => t • z) (t • (1 : E →L[ℝ] E)) y := by
    have hcoe : (fun z : E => t • z) = ⇑(t • (1 : E →L[ℝ] E)) := by
      funext z; simp
    rw [hcoe]
    exact (t • (1 : E →L[ℝ] E) : E →L[ℝ] E).hasFDerivAt
  -- hence `z ↦ b (t • z)` has derivative `t • fderiv ℝ b (t • y)`
  have hf : HasFDerivAt (fun z : E => b (t • z)) (t • fderiv ℝ b (t • y)) y := by
    have h := hb_deriv.comp y hsmul
    have h' : (fderiv ℝ b (t • y)).comp (t • (1 : E →L[ℝ] E)) =
        t • fderiv ℝ b (t • y) := by
      have : (t • (1 : E →L[ℝ] E)) = t • ContinuousLinearMap.id ℝ E := rfl
      rw [this, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
    exact h.congr_fderiv h'
  -- the identity map has derivative `1`
  have hg : HasFDerivAt (fun z : E => z) (1 : E →L[ℝ] E) y := hasFDerivAt_id y
  -- the bilinear chain rule for `(a, c) ↦ B a c`
  have h := B.hasFDerivAt_of_bilinear (G' := E) hf hg
  -- identify the resulting derivative with the claimed one
  apply h.congr_fderiv
  ext v
  -- `hclosed` lets us move `y` out of the second slot of `B`
  have key : B (t • fderiv ℝ b (t • y) v) y = B (t • fderiv ℝ b (t • y) y) v := by
    rw [map_smul, map_smul, smul_apply, smul_apply, hclosed (t • y) v y]
  rw [show (B.precompR E (b (t • y)) (1 : E →L[ℝ] E) +
        B.precompL E (t • fderiv ℝ b (t • y)) y) v
      = B (b (t • y)) v + B (t • fderiv ℝ b (t • y) v) y from rfl, key, map_add, add_apply]
  ring

end Work.RPCore.GenFun
