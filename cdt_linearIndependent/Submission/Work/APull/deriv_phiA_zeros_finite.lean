import Mathlib
import Submission.Work.APsi.psiA_facts
import Submission.Work.CPull.hauptH_deriv_zeros_finite

/-!
# APull — finiteness of the critical set of `phiA` on the unit disc

`phiA = hauptH ∘ psiA` is the Theorem A contour map of the paper.  Its critical points in the
unit disc are finite: since `psiA` is injective on the disc (a hypothesis here, proved in
`Submission.Work.APull.psiA_injective_ball`) and `deriv psiA` is nowhere zero there (also a
hypothesis, proved in `Submission.Work.APull.deriv_psiA_ne_zero`), a critical point `z` is
exactly a point with `deriv hauptH (psiA z) = 0`.

The key point is that `psiA` maps the closed unit disc into the disc of radius `4/5`:
`psiA = -(4/5) · lune (36/5) ∘ (⋯ composite of slits ⋯)` and `lune c` maps the closed unit disc
into itself.  Hence the critical points of `phiA` in the unit disc are the injective image under
`psiA` of the (finite) zero set of `deriv hauptH` in the compact set `closedBall 0 (4/5)`,
finiteness coming from `Work.CPull.finite_zeros_deriv_of_differentiableOn`.
-/

namespace Work.APull

open Submission.CDTPlan Complex Metric

noncomputable section

/-- `psiA` maps the closed unit disc into the disc of radius `4/5`. -/
lemma psiA_norm_le_four_fifths (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖psiA z‖ ≤ 4 / 5 := by
  have h5 : ‖Work.APsi.psiA_st5 z‖ ≤ 1 := by
    have h := Work.APsi.psiA_st5_maps hz
    rwa [Work.APsi.psiA_mem_closedBall_one] at h
  have hl := (Work.APsi.lune_facts (36 / 5) (by norm_num)).2.2.2.1
  have h2 : ‖lune (36 / 5) (-(Work.APsi.psiA_st5 z))‖ ≤ 1 := hl _ (by simpa using h5)
  have heq : psiA z = -((4 : ℂ) / 5) * lune (36 / 5) (-(Work.APsi.psiA_st5 z)) := by
    simp only [Submission.CDTPlan.psiA, Work.APsi.psiA_slitsA_eq]
  have hc : ‖((4 : ℂ) / 5)‖ = (4 / 5 : ℝ) := by
    rw [show ((4 : ℂ) / 5) = ((4 / 5 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  have h1 : ‖psiA z‖ = (4 / 5) * ‖lune (36 / 5) (-(Work.APsi.psiA_st5 z))‖ := by
    rw [heq, norm_mul, norm_neg, hc]
  rw [h1]
  nlinarith

theorem deriv_phiA_zeros_finite (hM : Submission.CDTPlan.HauptFacts)
    (hP : Submission.CDTPlan.PsiAFacts)
    (hinj : ∀ z w : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → w ∈ Metric.ball (0 : ℂ) 1 →
      Submission.CDTPlan.psiA z = Submission.CDTPlan.psiA w → z = w)
    (hderiv : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) 1 → deriv Submission.CDTPlan.psiA z ≠ 0) :
    ∃ S : Finset ℂ, ∀ z ∈ Metric.ball (0 : ℂ) 1, deriv Submission.CDTPlan.phiA z = 0 → z ∈ S := by
  classical
  -- zeros of `deriv hauptH` on the closed disc of radius `4/5` are finite
  have hZfin : {w : ℂ | w ∈ Metric.closedBall (0 : ℂ) (4 / 5) ∧ deriv hauptH w = 0}.Finite :=
    Work.CPull.finite_zeros_deriv_of_differentiableOn (r := 4 / 5) (R := 1)
      (by norm_num) (by norm_num) hM.1 (by rw [hM.2.1]; norm_num)
  have hPd : DifferentiableOn ℂ psiA (Metric.ball (0 : ℂ) 1) := hP.2.1
  -- chain rule: `phiA' = (hauptH' ∘ psiA) · psiA'` on the unit disc
  have hchain : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      deriv phiA z = deriv hauptH (psiA z) * deriv psiA z := by
    intro z hz
    show deriv (fun x => hauptH (psiA x)) z = deriv hauptH (psiA z) * deriv psiA z
    have hdz : DifferentiableAt ℂ psiA z :=
      hPd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hmem : psiA z ∈ Metric.ball (0 : ℂ) 1 := by
      have h1 : ‖psiA z‖ ≤ 4 / 5 := psiA_norm_le_four_fifths z (Metric.ball_subset_closedBall hz)
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hdh : DifferentiableAt ℂ hauptH (psiA z) :=
      hM.1.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    exact deriv_comp (x := z) hdh hdz
  -- for each zero `w` of `deriv hauptH` pick a preimage under `psiA` in the disc, if any
  refine ⟨hZfin.toFinset.image (fun w => if hh : (∃ z, z ∈ Metric.ball (0 : ℂ) 1 ∧ psiA z = w)
      then hh.choose else 0), ?_⟩
  intro z hz hderiv0
  have h1 := hchain z hz
  rw [hderiv0] at h1
  have hdψ : deriv psiA z ≠ 0 := hderiv z hz
  have h2 : deriv hauptH (psiA z) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact h3
    · exact absurd h3 hdψ
  have hwZ : psiA z ∈ {w : ℂ | w ∈ Metric.closedBall (0 : ℂ) (4 / 5) ∧ deriv hauptH w = 0} := by
    refine ⟨?_, h2⟩
    have h3 : ‖psiA z‖ ≤ 4 / 5 := psiA_norm_le_four_fifths z (Metric.ball_subset_closedBall hz)
    rw [Metric.mem_closedBall, dist_zero_right]; exact h3
  rw [Finset.mem_image]
  refine ⟨psiA z, (Set.Finite.mem_toFinset hZfin).mpr hwZ, ?_⟩
  have hex : ∃ z', z' ∈ Metric.ball (0 : ℂ) 1 ∧ psiA z' = psiA z := ⟨z, hz, rfl⟩
  rw [dif_pos hex]
  exact hinj _ _ hex.choose_spec.1 hz hex.choose_spec.2

end

end Work.APull
