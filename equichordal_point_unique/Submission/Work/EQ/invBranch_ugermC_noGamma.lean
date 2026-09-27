import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.fwdC_germC

/-!
# The backward branch `invBranch a true` scales the unstable germ parameter

`invBranch a true (ugermC a h w) = ugermC a h (λ w)` near `0`, for every stable germ `h`
(no heteroclinic connection needed).

The unstable germ is the mirror image of the stable one, `ugermC a h = eqMirror ∘ germC a h`, and
the bisector reflection `eqMirror` conjugates the principal forward branch to the principal backward
branch (`fwdC_mirror`).  Hence the statement below is the mirror conjugate of
`fwdC a (germC a h u) = germC a h (λ u)`; that identity is proved in
`Submission/Work/EQ/fwdC_germC.lean` (`fwdC_germC`), where the hypothesis `IsHeteroclinic` is
never used in the proof body.  We therefore re-prove it here without that hypothesis
(`fwdC_germC_noGamma`) and conjugate.
-/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- `invBranch a true` is the mirror conjugate of `fwdC`: the bisector reflection carries the
forward branch at `eqMirror Q` to the principal backward branch at `Q`. -/
theorem invBranch_true_eqMirror_fwdC {a : ℝ} (Q : ℂ × ℂ) :
    invBranch a true Q = eqMirror (fwdC a (eqMirror Q)) := by
  rw [fwdC_mirror, eqMirror_eqMirror]

/-- **The principal forward branch acts on the stable germ by scaling the parameter** — this is
`fwdC_germC` with its (unused) heteroclinic-connection hypothesis removed, so that it applies to an
arbitrary stable germ. -/
theorem fwdC_germC_noGamma {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      fwdC a (germC a h u) = germC a h ((eqLam a : ℂ) * u) := by
  obtain ⟨ρg, hρg, hAnC, hC0, hRP, hInjY, hderivY⟩ := germC_facts ha0 ha1 hh
  obtain ⟨ρs, hρs, hslitS⟩ := exists_ball_bsq_slitPlane ha0 ha1 hh
  have hρpos : 0 < min ρg ρs := lt_min hρg hρs
  have hρle_g : min ρg ρs ≤ ρg := min_le_left _ _
  have hρle_s : min ρg ρs ≤ ρs := min_le_right _ _
  have hslit : ∀ u ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      bsq (subO2 a (germC a h u)) ∈ Complex.slitPlane :=
    fun u hu => hslitS u (Metric.ball_subset_ball hρle_s hu)
  have hgc : ContinuousOn (fun u => germC a h u) (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    hAnC.continuousOn.mono (Metric.ball_subset_ball hρle_g)
  refine ⟨min ρg ρs, hρpos, ?_⟩
  intro u hu
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hgcl : ContinuousOn (fun w => germC a h ((eqLam a : ℂ) * w))
      (Metric.ball (0 : ℂ) (min ρg ρs)) := by
    have hlin : ContinuousOn (fun w : ℂ => (eqLam a : ℂ) * w) (Metric.ball (0 : ℂ) (min ρg ρs)) :=
      (by fun_prop : Continuous fun w : ℂ => (eqLam a : ℂ) * w).continuousOn
    refine ContinuousOn.comp hAnC.continuousOn hlin ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    exact lt_of_lt_of_le (norm_mul_lt_of_lt hl0 hl1 hρpos hx) hρle_g
  have hphi : ContinuousOn
      (fun w => ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖)
      (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    (hgcl.sub (continuousOn_fwdC_germC hgc hslit)).norm
  have hkey : ∀ w ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ = 0 ∨
      1 ≤ ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ := by
    intro w hw
    have hwg : w ∈ Metric.ball (0 : ℂ) ρg := Metric.ball_subset_ball hρle_g hw
    obtain ⟨⟨hEq, hPnd, hQnd⟩, -⟩ := hRP w hwg
    rcases fwd_pair_dichotomy hEq hPnd with hcase | hcase
    · left; rw [hcase]; simp
    · right
      rw [hcase]
      have h2 : ‖fwdAlt a (germC a h w) - fwdC a (germC a h w)‖
          = ‖fwdC a (germC a h w) - fwdAlt a (germC a h w)‖ := by
        rw [show fwdAlt a (germC a h w) - fwdC a (germC a h w)
            = -(fwdC a (germC a h w) - fwdAlt a (germC a h w)) by rw [neg_sub]]
        exact norm_neg _
      rw [h2]
      exact fwd_branch_separation a (germC a h w) hPnd
  have hphi_ne : ∀ w ∈ Metric.ball (0 : ℂ) (min ρg ρs),
      ‖germC a h ((eqLam a : ℂ) * w) - fwdC a (germC a h w)‖ ≠ 1 / 2 := by
    intro w hw hc
    rcases hkey w hw with h | h <;> linarith
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (min ρg ρs) := by
    simpa using hρpos
  have hphi0 : ‖germC a h ((eqLam a : ℂ) * 0) - fwdC a (germC a h 0)‖ < 1 / 2 := by
    rw [mul_zero, hC0, fwdC_neg_half ha0]
    simp
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) (min ρg ρs)) :=
    (convex_ball (0 : ℂ) (min ρg ρs)).isPreconnected
  have hlt := hpre.gt_of_ne hphi hphi_ne ⟨0, h0mem, hphi0⟩ (x := u) hu
  have hzero : ‖germC a h ((eqLam a : ℂ) * u) - fwdC a (germC a h u)‖ = 0 := by
    rcases hkey u hu with h | h
    · exact h
    · linarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

theorem invBranch_ugermC_noGamma {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w ∈ Metric.ball (0 : ℂ) ρ,
      invBranch a true (ugermC a h w) = ugermC a h ((eqLam a : ℂ) * w) := by
  obtain ⟨ρf, hρf, hf⟩ := fwdC_germC_noGamma ha0 ha1 hh
  refine ⟨ρf, hρf, fun w hw => ?_⟩
  have h1 : ugermC a h w = eqMirror (germC a h w) := rfl
  rw [invBranch_true_eqMirror_fwdC, h1, eqMirror_eqMirror, hf w hw]
  rfl

end

end Work.EQ
