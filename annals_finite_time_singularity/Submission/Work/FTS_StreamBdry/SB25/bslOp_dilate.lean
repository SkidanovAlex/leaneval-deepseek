import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.bslOp_dilate` — `bslOp` commutes with dilations of `z`

`bslOp α` is an *Euler-type* operator: its coefficients involve the weight `z` (and `z ^ 2`) next
to one (resp. two) radial derivatives, together with the purely angular operator `Lzero`.  Hence
the dilation `z ↦ lam * z` of the self-similar variable maps the operator into itself, with no
smoothness hypothesis whatsoever.

The proof is unconditional: Mathlib's `deriv` is totalised (junk value `0` where the function is
not differentiable), and the chain rule `deriv_comp_mul_left` holds for *every* `lam`, so the
identities `pz (P(lam·)) = lam · pz P (lam·)`, `pzIter 2 (P(lam·)) = lam^2 · pzIter 2 P (lam·)`
hold pointwise, while `Lzero` and the angular derivatives do not see the dilation at all
(definitionally).
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## The radial derivatives and the dilation -/

/-- The plain radial derivative of a dilated datum.  Unconditional in `lam` (including `lam = 0`,
where both sides are the junk value `0`), because `deriv_comp_mul_left` is unconditional. -/
lemma pz_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.pz (fun z θ => P (lam * z) θ)
      = fun z θ => lam * Work.Spaces.pz P (lam * z) θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => P ζ θ) z

/-- `∂_z` of a constant multiple of a dilated datum. -/
lemma pz_const_mul_dilate_z (P : ℝ → ℝ → ℝ) (c lam : ℝ) :
    Work.Spaces.pz (fun z θ => c * P (lam * z) θ)
      = fun z θ => c * (lam * Work.Spaces.pz P (lam * z) θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (x := z) (v := fun z' => P (lam * z') θ) c]
  congr 1
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => P ζ θ) z

/-- The iterated radial derivative of a dilated datum picks up `lam ^ n`. -/
lemma pzIter_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => P (lam * z) θ)
      = fun z θ => lam ^ n * Work.Spaces.pzIter n P (lam * z) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_const_mul_dilate_z]
      funext z θ
      rw [Work.Spaces.pzIter_succ, pow_succ]
      ring

/-- `Lzero` is a purely angular operator, so it does not see the dilation (definitional). -/
lemma Lzero_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Elliptic.Lzero (fun z θ => P (lam * z) θ)
      = fun z θ => Work.Elliptic.Lzero P (lam * z) θ := by
  funext z θ
  rfl

/-! ## The statement -/

/-- **E2a `bslOp_dilate`**: `bslOp` commutes with dilations in `z` (unconditional). -/
theorem bslOp_dilate (α lam : ℝ) (P : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpDilate α lam P := by
  intro z θ
  simp only [Work.Elliptic.bslOp]
  rw [show Work.Spaces.pzIter 2 (fun z θ => P (lam * z) θ) z θ
        = lam ^ 2 * Work.Spaces.pzIter 2 P (lam * z) θ from
      congrFun (congrFun (pzIter_dilate_z P lam 2) z) θ,
      show Work.Spaces.pz (fun z θ => P (lam * z) θ) z θ
        = lam * Work.Spaces.pz P (lam * z) θ from
      congrFun (congrFun (pz_dilate_z P lam) z) θ,
      show Work.Elliptic.Lzero (fun z θ => P (lam * z) θ) z θ
        = Work.Elliptic.Lzero P (lam * z) θ from
      congrFun (congrFun (Lzero_dilate_z P lam) z) θ]
  ring

end Work.FTS_StreamBdry.SB25
