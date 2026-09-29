import Mathlib
import Submission.Work.TMContract.Gluing.idsAnalytic_of
import Submission.Work.TMComp.RedC7T.dioph_consumers
import Submission.Work.TMComp.prove_RotBasics

open MeasureTheory Filter Topology Set

open scoped Topology

namespace Work.LocCantor

-- File: Submission/Work/LocCantor/idsAnalytic_of_dioph.lean
-- Module: Submission.Work.LocCantor.idsAnalytic_of_dioph
-- Namespace: Work.LocCantor
-- Aim: the Diophantine-restricted version of Work.TMContract.Gluing.idsAnalytic_of
-- (Submission/Work/TMContract/Gluing/idsAnalytic_of.lean), with `P_mAnalytic` replaced by
-- `Work.TMComp.RedProj.P_mAnalytic_dioph` (Submission/Work/TMComp/RedC7T/dioph_consumers.lean).
-- Do NOT import Submission.Work.TMComp.prove_LocCantor or Submission.Work.TMComp.prove_Reducibility
-- (they pull in the `sorry`-stubbed C7 `prove_BJ`); the imported modules listed below are
-- enough to copy the proof of `idsAnalytic_of` verbatim, with the two extra hypotheses
-- `(b₀)`, `0 < b₀`, `DiophBelow α b₀` carried into the `h9` call.
theorem idsAnalytic_of_dioph
    (h5 : Work.TMContract.P_RotBasics)
    (h9 : Work.TMComp.RedProj.P_mAnalytic_dioph) :
    ∀ (α lam a b b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ →
      0 < lam → lam ≤ 1 → a < b → Set.Ioo a b ⊆ Work.TMContract.amoSpec α lam →
      AnalyticOnNhd ℝ (Work.TMContract.ids α lam) (Set.Ioo a b) := by
  intro α lam a b b₀ hα hb₀ hD h0 h1 hab hsub
  obtain ⟨C, φ, _hC, hφ, hCper, hφper, hCdet, hCdeg, hconj⟩ :=
    h9 α lam a b b₀ hα hb₀ hD h0 h1 hab hsub
  have hFanal : AnalyticOnNhd ℝ (fun E : ℝ => ∫ x in (0:ℝ)..1, φ E x) (Ioo a b) :=
    Work.TMContract.Gluing.analyticOnNhd_integral hφ
  intro E₀ hE₀
  -- C5 part 4 with `k = 0`, at the single point `E₀`
  obtain ⟨j₀, hj₀⟩ := h5.2.2.2 α lam E₀ (C E₀) (φ E₀) 0 (hCdeg E₀ hE₀) (hCper E₀)
     (hCdet E₀ hE₀) (Work.TMContract.Gluing.continuous_slice_of_jointAnalytic hφ hE₀)
     (hφper E₀) (hconj E₀ hE₀)
  have hj₀' : Work.TMContract.rotLift α lam E₀
      = 2 * (∫ x in (0:ℝ)..1, φ E₀ x) + 2 * (j₀:ℝ) := by
    rw [hj₀]; push_cast; ring
  -- continuity of the relevant functions at `E₀`
  have hids_cont : ContinuousAt (fun E : ℝ => Work.TMContract.ids α lam E) E₀ := by
    have hc : Continuous (fun p : ℝ × ℝ => Work.TMContract.ids p.1 lam p.2) := h5.2.2.1 lam
    fun_prop
  have hrot_cont : ContinuousAt (fun E : ℝ => Work.TMContract.rotLift α lam E) E₀ := by
    have heq : (fun E : ℝ => Work.TMContract.rotLift α lam E)
        = fun E => 1 - Work.TMContract.ids α lam E := by
      funext E; simp only [Work.TMContract.ids]; ring
    rw [heq]
    exact continuousAt_const.sub hids_cont
  have hg_cont : ContinuousAt (fun E : ℝ =>
      Work.TMContract.rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x)) E₀ :=
    hrot_cont.sub ((hFanal E₀ hE₀).continuousAt.const_mul 2)
  -- the `2ℤ`-valuedness of `rotLift - 2∫φ` near `E₀`
  have hjf : ∀ᶠ E in 𝓝 E₀, ∃ j : ℤ,
      Work.TMContract.rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x) = 2 * (j:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hE₀] with E hE
    obtain ⟨j, hj⟩ := h5.2.2.2 α lam E (C E) (φ E) 0 (hCdeg E hE) (hCper E)
       (hCdet E hE) (Work.TMContract.Gluing.continuous_slice_of_jointAnalytic hφ hE)
       (hφper E) (hconj E hE)
    refine ⟨j, ?_⟩
    rw [hj]; push_cast; ring
  have hg₀ : Work.TMContract.rotLift α lam E₀ - 2 * (∫ x in (0:ℝ)..1, φ E₀ x) = 2 * (j₀:ℝ) := by
    rw [hj₀']; ring
  have hconst : ∀ᶠ E in 𝓝 E₀,
      Work.TMContract.rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x)
        = Work.TMContract.rotLift α lam E₀ - 2 * (∫ x in (0:ℝ)..1, φ E₀ x) :=
    Work.TMContract.Gluing.eventually_eq_of_two_mul_int_continuousAt hg_cont hg₀ hjf
  -- hence `ids` agrees near `E₀` with an explicit real-analytic function
  have han : AnalyticAt ℝ (fun E : ℝ =>
      1 - (2 * (∫ x in (0:ℝ)..1, φ E x) + 2 * (j₀:ℝ))) E₀ := by
    have h1 : AnalyticAt ℝ (fun E : ℝ => (∫ x in (0:ℝ)..1, φ E x)) E₀ := hFanal E₀ hE₀
    fun_prop
  refine han.congr ?_
  filter_upwards [hconst] with E hE
  have hE' : Work.TMContract.rotLift α lam E
      = 2 * (∫ x in (0:ℝ)..1, φ E x) + 2 * (j₀:ℝ) := by linarith
  simp only [Work.TMContract.ids]
  rw [hE']

end Work.LocCantor
