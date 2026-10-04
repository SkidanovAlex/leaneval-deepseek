import Mathlib
import Submission.Work.Diff.Alg.Pinch.Phi_wedge_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

/-- `cR4 R ζ η ζ̄ η̄` is the real number `EFun R (Re ζ) (Im ζ) (Re η) (Im η)`.

The bilinear form `cR4 R ζ η ζ̄ η̄` is self-conjugate (conjugation exchanges the two pairs, and
`cR4` is symmetric in the pair by the algebraic symmetry of the curvature), hence real; its real
part is the isotropic curvature `EFunC`, which is `EFun` by definition. -/
theorem cR4_wedge_real (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (ζ η : Fin n → ℂ) :
    Work.Diff.Alg.cR4 R ζ η (star ζ) (star η)
      = ((Work.Diff.Alg.Q2P.EFun R (Work.Diff.Alg.Q2P.cRe ζ) (Work.Diff.Alg.Q2P.cIm ζ)
          (Work.Diff.Alg.Q2P.cRe η) (Work.Diff.Alg.Q2P.cIm η) : ℝ) : ℂ) := by
  -- `star` interchanges `cR4` with the componentwise conjugation, and (by pair symmetry) leaves the
  -- expression `cR4 R ζ η ζ̄ η̄` fixed: it is self-conjugate.
  have hreal : star (Work.Diff.Alg.cR4 R ζ η (star ζ) (star η))
      = Work.Diff.Alg.cR4 R ζ η (star ζ) (star η) := by
    rw [cR4_star]
    simp only [star_star]
    exact (cR4_pair R hR ζ η (star ζ) (star η)).symm
  -- The real part is the real isotropic curvature `EFunC = EFun`.
  have hre : (Work.Diff.Alg.cR4 R ζ η (star ζ) (star η)).re
      = Work.Diff.Alg.Q2P.EFun R (Work.Diff.Alg.Q2P.cRe ζ) (Work.Diff.Alg.Q2P.cIm ζ)
          (Work.Diff.Alg.Q2P.cRe η) (Work.Diff.Alg.Q2P.cIm η) :=
    Work.Diff.Alg.cR4_re R hR ζ η
  -- Self-conjugacy forces the imaginary part to vanish.
  have him : (Work.Diff.Alg.cR4 R ζ η (star ζ) (star η)).im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

end Work.Diff.Alg.Pinch
