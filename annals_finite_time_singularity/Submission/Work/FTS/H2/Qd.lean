/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open quadrant `(0,∞) × (0,π/2)` and continuity of the weights on it

This module is the **single owner** of the small geometric/continuity cluster that the rest of
`Submission/Work/FTS/H2` uses:

* `Work.FTS.H2.Qd` — the open quadrant `(0,∞) × (0,π/2) ⊆ ℝ²` (`= Work.Construction.Qd`), on
  which the weights `w(z) = (1+z)²/z²` and `sin(2θ)^{-c}` are honest continuous functions;
* `isOpen_Qd`, `Qd_subset_nbhU`, `Qd_subset_quadU`, `quadU_subset_nbhU` — the elementary
  topological facts;
* `sin_two_pos_Qd` — `sin(2θ) > 0` for `θ ∈ (0,π/2)`;
* `continuousOn_w_Qd`, `continuousOn_sin_rpow_Qd` (alias `continuousOn_sinpow_Qd`),
  `continuousOn_Whz_Qd`, `continuousOn_Wm_Qd`, `continuousOn_Wt_Qd` — continuity of the weights
  on the open quadrant;
* `Whz_nonneg`, `Wm_nonneg` — nonnegativity of `Whz`, `Wm` on the closed angular interval.

The complement of `Qd` inside `Iz ×ˢ Iθ` is the union of the three segments `{0} × Iθ`,
`Iz × {0}`, `Iz × {π/2}`, which is null; that is why continuity on `Qd` upgrades to a.e. strong
measurability for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`, `Work.Spaces.aesm_slice_of_continuousOn_Qd`).

Every declaration here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

theorem Qd_subset_nbhU : Qd ⊆ Work.Spaces.nbhU := by
  intro p hp
  simp only [Qd, Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

theorem Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

theorem quadU_subset_nbhU : Work.Spaces.quadU ⊆ Work.Spaces.nbhU := by
  intro p hp
  simp only [Work.Spaces.quadU, Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

theorem sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

theorem continuousOn_sin_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))

/-- `continuousOn_sin_rpow_Qd` under the name used by the `T2`-family of this directory. -/
theorem continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  continuousOn_sin_rpow_Qd c

theorem continuousOn_Whz_Qd : ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Qd := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    continuousOn_sin_rpow_Qd (Work.Spaces.eta / 2)
  refine continuousOn_w_Qd.div hsin (fun p hp => ?_)
  exact ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _)

theorem continuousOn_Wm_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Qd := by
  simp only [Wm, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd (-(Work.Spaces.gam α / 2)))

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Qd :=
    continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd (-(Work.Spaces.gam α / 2)))
  simpa only [Work.Spaces.Wt, Work.Spaces.wTheta] using h1

/-- `sin(2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  linarith [hθ.2, Real.pi_pos]

theorem Whz_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Whz z θ := by
  simp only [Whz, Work.Spaces.w]
  exact div_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

theorem Wm_nonneg (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wm α z θ := by
  simp only [Wm, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

end

end Work.FTS.H2
