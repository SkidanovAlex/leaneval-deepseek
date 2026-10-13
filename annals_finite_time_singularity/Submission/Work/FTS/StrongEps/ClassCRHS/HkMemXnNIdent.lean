/-
# `HkMemXnNIdent` — the twenty piece identifications `PB = NBlk` on the open quadrant

Each §8 piece `PB α w Φs Φg k` (the paper's `N_i^{ab}`) agrees, on the open quadrant, with its
product form `NBlk α w Φs Φg k`: the only content is the algebraic cancellation of the
`(z+1)/z`-weight against the `z/(1+z)`-scaling, the replacement of `∂_θ` by `D_θ/ sin 2θ` and the
explicit value `FK (F_*) = 2α·hKer`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.FstarPkgAll

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem PB_eq_NBlk {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (w Φs Φg : Fn) :
    ∀ k ∈ Finset.range 20, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg k z θ = NBlk α w Φs Φg k z θ := by
  have h2ne : (1 : ℕ) + 1 ≠ 0 := by norm_num
  have hid0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 0 z θ = NBlk α w Φs Φg 0 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N1gg]
    ring
  have hid1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 1 z θ = NBlk α w Φs Φg 1 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N1gs]
    ring
  have hid2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 2 z θ = NBlk α w Φs Φg 2 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N1sg]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid3 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 3 z θ = NBlk α w Φs Φg 3 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N1ss]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 4 z θ = NBlk α w Φs Φg 4 z θ := by
    intro z θ _ hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2gg, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid5 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 5 z θ = NBlk α w Φs Φg 5 z θ := by
    intro z θ _ hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2gs, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 6 z θ = NBlk α w Φs Φg 6 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 7 z θ = NBlk α w Φs Φg 7 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2ss, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 8 z θ = NBlk α w Φs Φg 8 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N3gg]
    ring
  have hid9 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 9 z θ = NBlk α w Φs Φg 9 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N3gs]
    ring
  have hid10 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 10 z θ = NBlk α w Φs Φg 10 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N3sg]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid11 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 11 z θ = NBlk α w Φs Φg 11 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N3ss]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid12 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 12 z θ = NBlk α w Φs Φg 12 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4gg]
    ring
  have hid13 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 13 z θ = NBlk α w Φs Φg 13 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4gs, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hid14 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 14 z θ = NBlk α w Φs Φg 14 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4sg, Work.Spaces.Dth,
      Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hid15 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 15 z θ = NBlk α w Φs Φg 15 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4ss, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hid16 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 16 z θ = NBlk α w Φs Φg 16 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5gg]
    ring
  have hid17 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 17 z θ = NBlk α w Φs Φg 17 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5gs]
    ring
  have hid18 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 18 z θ = NBlk α w Φs Φg 18 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5sg]
    ring
  have hid19 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 19 z θ = NBlk α w Φs Φg 19 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5ss]
    ring
  intro k hk z θ hz hθ0 hθ1
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k <;>
    first
      | exact hid0 z θ hz hθ0 hθ1
      | exact hid1 z θ hz hθ0 hθ1
      | exact hid2 z θ hz hθ0 hθ1
      | exact hid3 z θ hz hθ0 hθ1
      | exact hid4 z θ hz hθ0 hθ1
      | exact hid5 z θ hz hθ0 hθ1
      | exact hid6 z θ hz hθ0 hθ1
      | exact hid7 z θ hz hθ0 hθ1
      | exact hid8 z θ hz hθ0 hθ1
      | exact hid9 z θ hz hθ0 hθ1
      | exact hid10 z θ hz hθ0 hθ1
      | exact hid11 z θ hz hθ0 hθ1
      | exact hid12 z θ hz hθ0 hθ1
      | exact hid13 z θ hz hθ0 hθ1
      | exact hid14 z θ hz hθ0 hθ1
      | exact hid15 z θ hz hθ0 hθ1
      | exact hid16 z θ hz hθ0 hθ1
      | exact hid17 z θ hz hθ0 hθ1
      | exact hid18 z θ hz hθ0 hθ1
      | exact hid19 z θ hz hθ0 hθ1

end Work.FTS.StrongEps.ClassCRHS
