import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs
import Submission.Work.Diff.Alg.Pinch.qform_bmat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positive semidefiniteness of `bmat v S` for tensors with nonnegative isotropic curvature

For a four-index array `S` (a curvature tensor in an orthonormal frame) and a vector `v`, the
`(0,2)`-tensor `bmat v S p q = ∑ᵢⱼ vᵢ vⱼ S i p j q` is `S(v, e_p, v, e_q)` in frame notation.  Its
quadratic form in a vector `w` is

`qform (bmat v S) w = R4 S v w v w`   (`Work.Diff.Alg.Pinch.qform_bmat`),

i.e. the (unnormalised) sectional curvature of the plane spanned by `v` and `w`.

Since `InPIC2 S` is `0 ≤ R4 S x z x z + R4 S x w x w + R4 S y z y z + R4 S y w y w − 2 R4 S x y z w`
for *all* vectors `x y z w`, specialising to `y = w = 0` (and `x = v`, `z = w`) collapses the four
auxiliary terms and yields `0 ≤ R4 S v w v w`.  Hence `bmat v S` is positive semidefinite for every
`v` — the fact used to symmetrise pairings `∑_{p q} M p q · bmat v S p q` in the strict Ricci-form
estimates.
-/

namespace Work.Diff.Alg.Pinch

/-- `R4 R 0 a b c = 0`: the multilinear evaluation vanishes when its first argument is `0`. -/
private lemma r4_zero₁ {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (a b c : Fin n → ℝ) :
    Submission.Diff.Alg.R4 R 0 a b c = 0 := by
  simp [Submission.Diff.Alg.R4]

/-- `R4 R a 0 c d = 0`: the multilinear evaluation vanishes when its second argument is `0`. -/
private lemma r4_zero₂ {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (a c d : Fin n → ℝ) :
    Submission.Diff.Alg.R4 R a 0 c d = 0 := by
  simp [Submission.Diff.Alg.R4]

theorem bmat_psd (n : ℕ) {S : Submission.Diff.Alg.Curv4 n} (hP : Submission.Diff.Alg.InPIC2 S)
    (v : Fin n → ℝ) : ∀ w : Fin n → ℝ, 0 ≤ Work.Diff.Alg.Pinch.qform (Work.Diff.Alg.Pinch.bmat v S) w := by
  intro w
  rw [qform_bmat n v w S]
  -- `InPIC2 S` at `(x, y, z, w') = (v, 0, w, 0)` reads `0 ≤ R4 S v w v w + 0 + 0 + 0 - 2 * 0`.
  have h := hP v 0 w 0
  have h₂ : Submission.Diff.Alg.R4 S v 0 v 0 = 0 := r4_zero₂ S v v 0
  have h₃ : Submission.Diff.Alg.R4 S 0 w 0 w = 0 := r4_zero₁ S w 0 w
  have h₄ : Submission.Diff.Alg.R4 S 0 0 0 0 = 0 := r4_zero₁ S 0 0 0
  have h₅ : Submission.Diff.Alg.R4 S v 0 w 0 = 0 := r4_zero₂ S v w 0
  linarith

end Work.Diff.Alg.Pinch
