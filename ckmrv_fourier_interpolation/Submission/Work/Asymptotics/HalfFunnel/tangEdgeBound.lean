/-
# The kernel is bounded on the three non-contour edges of the tangency rectangle

The kernel `z ↦ K^{(d)}(τ,z)` is meromorphic with simple poles exactly on the `SL(2,ℤ)`-orbit of
`τ` (the coincidence set `j z = j τ`).  On the closed tangency region `ctanCl` the
orbit classification `tangOrbitRectCl` says that the closed rectangle
`[0,1/4] × [1/2,3/2]` contains exactly one point of that orbit, the pole `poleOne τ`; and by
`tangPoleGeomCl` that pole misses the three non-contour edges of the rectangle
(`Re z = 1/4`, `Im z = 1/2`, `Im z = 3/2`), meeting only the contour edge `Re z = 0`, at the
two tangency points `τ = ±1/2 + i/2`.

Consequently `j` separates `ctanCl` (compact) from the three edges (`edgeH`, compact), so on
the compact set `ctanCl × edgeH` the kernel is bounded
(`exists_bound_Kfun_off_coincidence`), and a supremum over that compact set is the required
constant.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRectCl
import Submission.Work.Asymptotics.HalfFunnel.tangEdgeDefs
import Submission.Work.Asymptotics.HalfFunnel.isCompact_edgeH
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeomCl
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane

noncomputable section

/-- **The coincidence divisor misses the three non-contour edges.**  For `τ` in the closed
tangency region and `ζ` on one of the three edges `Re ζ = 1/4`, `Im ζ = 1/2`, `Im ζ = 3/2` of
the rectangle `[0,1/4] × [1/2,3/2]`, the `j`-invariants differ: the unique orbit point in the
rectangle is `poleOne τ`, which by `tangPoleGeomCl` lies strictly off those three edges. -/
lemma edgeH_separated {τ : ℍ} (hτ : τ ∈ ctanCl) {ζ : ℍ} (hζ : ζ ∈ edgeH) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
  intro h
  have hzC : (ζ : ℂ) ∈ edgeC := (mem_edgeH_iff ζ).mp hζ
  have hrect := edgeC_rect hzC
  have hζeq : ζ = poleOne τ := tangOrbitRectCl τ ζ hτ
    (by simpa [UpperHalfPlane.coe_re] using hrect.1)
    (by simpa [UpperHalfPlane.coe_re] using hrect.2.1)
    (by simpa [UpperHalfPlane.coe_im] using hrect.2.2.1)
    (by simpa [UpperHalfPlane.coe_im] using hrect.2.2.2)
    h.symm
  have hp := tangPoleGeomCl τ hτ
  rw [hζeq] at hzC
  rcases hzC with ⟨hre, _, _⟩ | ⟨him, _, _⟩ | ⟨him, _, _⟩
  · rw [UpperHalfPlane.coe_re] at hre
    linarith [hre, hp.1]
  · rw [UpperHalfPlane.coe_im] at him
    linarith [him, hp.2.1]
  · rw [UpperHalfPlane.coe_im] at him
    linarith [him, hp.2.2]

/-- **The kernel is bounded on the three non-contour edges of the rectangle
`[0,1/4] × [1/2,3/2]`.** -/
theorem tangEdgeBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (z : ℂ), τ ∈ Work.Asymptotics.HalfFunnel.ctanCl →
      ((z.re = 1 / 4 ∧ (1 : ℝ) / 2 ≤ z.im ∧ z.im ≤ 3 / 2) ∨
       (z.im = 1 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4) ∨
       (z.im = 3 / 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 4)) →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_Kfun_off_coincidence ℓ d hd
    (S := ctanCl) (T := edgeH) isCompact_ctanCl isCompact_edgeH
    (fun τ hτ ζ hζ => edgeH_separated hτ hζ)
  exact ⟨C, hCpos, fun τ z hτ hz =>
    hC τ hτ (UpperHalfPlane.ofComplex z) ⟨z, hz, rfl⟩⟩

end

end Work.Asymptotics.HalfFunnel
