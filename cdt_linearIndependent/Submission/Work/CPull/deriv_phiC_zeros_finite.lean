import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.phiC_ext_defs
import Submission.Work.CPull.psiC_psiF
import Submission.Work.CPull.hauptH_deriv_zeros_finite

/-!
# CPull — finiteness of the critical set of `phiC` on the unit disc

`phiC = hauptH ∘ psiC` is the Theorem C contour map of the paper.  Its critical points in the
unit disc are finite: since `psiC` is a conformal map onto a lune (whence `deriv psiC` is
nowhere zero, obtained from the explicit rational inverse `psiF` of `psiC`), a critical point
`z` is exactly a point with `hauptH' (psiC z) = 0`.  As `‖psiC ‖ ≤ 3/4` on the closed unit
disc, the critical points of `phiC` in the disc sit inside the image under `psiC` of the
(finite) zero set of `deriv hauptH` in the compact set `closedBall 0 (3/4)`, and `psiC` is
injective.  This is the "finite zero set of `deriv phiC` on the disc" used by the meromorphic
pullback of the three derivative functions.
-/

namespace Work.CPull

open Submission.CDTPlan

theorem deriv_phiC_zeros_finite (hM : Submission.CDTPlan.HauptFacts) (hP : Submission.CDTPlan.PsiCFacts) :
    ∃ S : Finset ℂ, ∀ z ∈ Metric.ball (0:ℂ) 1, deriv Submission.CDTPlan.phiC z = 0 → z ∈ S := by
  classical
  have hZfin : {w : ℂ | w ∈ Metric.closedBall (0:ℂ) (3/4) ∧ deriv hauptH w = 0}.Finite :=
    hauptH_deriv_zeros_finite hM
  obtain ⟨hψF, hψFd⟩ := psiC_psiF
  obtain ⟨hMd, hM0, hMz, hMsq⟩ := hM
  obtain ⟨hPc, hPd, hP0, hPder, hPb, hPinj⟩ := hP
  have hchain : ∀ z ∈ Metric.ball (0:ℂ) 1,
      deriv phiC z = deriv hauptH (psiC z) * deriv psiC z := by
    intro z hz
    show deriv (fun x => hauptH (psiC x)) z = deriv hauptH (psiC z) * deriv psiC z
    have hdz : DifferentiableAt ℂ psiC z :=
      hPd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hmem : psiC z ∈ Metric.ball (0:ℂ) 1 := by
      have h1 : ‖psiC z‖ ≤ 3/4 := hPb z (Metric.ball_subset_closedBall hz)
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hdh : DifferentiableAt ℂ hauptH (psiC z) :=
      hMd.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hthis := deriv_comp (x := z) hdh hdz
    simpa [Function.comp_def] using hthis
  have hne : ∀ z ∈ Metric.ball (0:ℂ) 1, deriv psiC z ≠ 0 := by
    intro z hz
    have hdz : DifferentiableAt ℂ psiC z :=
      hPd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hdF : DifferentiableAt ℂ psiF (psiC z) := hψFd z
    have hcomp : deriv (psiF ∘ psiC) z = deriv psiF (psiC z) * deriv psiC z :=
      deriv_comp (x := z) hdF hdz
    have hid : (psiF ∘ psiC) = id := funext hψF
    have h1 : deriv (psiF ∘ psiC) z = 1 := by rw [hid, deriv_id]
    rw [hcomp] at h1
    intro h0; rw [h0, mul_zero] at h1; exact one_ne_zero h1.symm
  have hinj : Function.Injective psiC := by
    intro z1 z2 h
    calc z1 = psiF (psiC z1) := (hψF z1).symm
      _ = psiF (psiC z2) := by rw [h]
      _ = z2 := hψF z2
  refine ⟨hZfin.toFinset.image (fun w => if hh : (∃ z, z ∈ Metric.ball (0:ℂ) 1 ∧ psiC z = w)
      then hh.choose else 0), ?_⟩
  intro z hz hderiv
  have h1 := hchain z hz
  rw [hderiv] at h1
  have hdψ : deriv psiC z ≠ 0 := hne z hz
  have h2 : deriv hauptH (psiC z) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact h3
    · exact absurd h3 hdψ
  have hwZ : psiC z ∈ {w : ℂ | w ∈ Metric.closedBall (0:ℂ) (3/4) ∧ deriv hauptH w = 0} := by
    refine ⟨?_, h2⟩
    have h3 : ‖psiC z‖ ≤ 3/4 := hPb z (Metric.ball_subset_closedBall hz)
    rw [Metric.mem_closedBall, dist_zero_right]; linarith
  rw [Finset.mem_image]
  refine ⟨psiC z, (Set.Finite.mem_toFinset hZfin).mpr hwZ, ?_⟩
  have hex : ∃ z', z' ∈ Metric.ball (0:ℂ) 1 ∧ psiC z' = psiC z := ⟨z, hz, rfl⟩
  rw [dif_pos hex]
  exact hinj hex.choose_spec.2

end Work.CPull
