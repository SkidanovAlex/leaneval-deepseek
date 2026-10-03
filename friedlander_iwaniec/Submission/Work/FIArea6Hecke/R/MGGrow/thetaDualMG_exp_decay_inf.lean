/-
# `Submission.Work.FIArea6Hecke.R.MGGrow.thetaDualMG_exp_decay_inf`

**Exponential decay at `∞` of the normalised dual kernel `thetaDualMG`.**

The kernel `thetaDualMG d χ m x = c·thetaDualM d χ m (x/(16d²))` is the Poisson dual of the
holomorphic theta series `thetaHol χ m` (see `R/LamRightHalf.thetaHol_one_div_dual`).  Its Mellin
transform is the completed Hecke `L`-function of `χ` of weight `m`; the growth of that completed
`L`-function is read off from the decay proved here.

Two ingredients, both already available:

* `thetaDualM_decay` gives `‖thetaDualM d χ m w‖ ≤ C·e^{-πw}` for `w ≥ 1` (the `ξ = 0` Fourier
  coefficient vanishes, either because `m ≥ 1` kills it or by the hypothesis `ĝ(0) = 0` when
  `m = 0`); rescaling `w = x/(16d²)` produces the decay `e^{-(π/(16d²))x}` of `thetaDualMG` for
  `x ≥ 16d²`;
* `thetaDualM_continuous` makes `thetaDualMG` continuous on `(0,∞)`, hence **bounded** on the
  compact initial interval `[1, 16d²]`; on that interval the exponential factor `e^{-(π/16d²)x}`
  is bounded below by `e^{-π}`, so the same constant serves.

The two pieces are glued by taking the maximum of the two constants.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_continuous

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R.MGGrow

open scoped BigOperators

noncomputable section

/-- **Continuity of the normalised dual kernel on `(0,∞)`** (the rescaling `x ↦ x/(16d²)` of
`thetaDualM_continuous`). -/
theorem continuousOn_thetaDualMG_Ioi (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (m : ℕ) :
    ContinuousOn (Work.FIArea6Hecke.R.thetaDualMG d chi m) (Set.Ioi 0) := by
  have hden : (0 : ℝ) < 16 * (d : ℝ) ^ 2 := by
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    positivity
  refine (((Work.FIArea6Hecke.R.thetaDualM_continuous d hchi m).comp
    (continuous_id.div_const _).continuousOn ?_).const_mul _)
  intro x hx
  simp only [Set.mem_Ioi] at hx ⊢
  exact div_pos hx hden

/-- **Exponential decay of the normalised dual kernel at `∞`.**  There is `C > 0` with
`‖thetaDualMG d χ m x‖ ≤ C·e^{-(π/(16d²))x}` for every `x ≥ 1`. -/
theorem thetaDualMG_exp_decay_inf (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (k : ℕ)
    (h0 : k = 0 → Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ ≤
        C * Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * x) := by
  have hden : (0 : ℝ) < 16 * (d : ℝ) ^ 2 := by positivity
  -- the decay rate `c = π/(16d²)` packaged as a local definition
  set c : ℝ := Real.pi / (16 * (d : ℝ) ^ 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcp : c * (16 * (d : ℝ) ^ 2) = Real.pi := by
    rw [hcdef, div_mul_cancel₀ _ (by positivity)]
  have harg : ∀ x : ℝ, -Real.pi * (x / (16 * (d : ℝ) ^ 2)) = (-c) * x := by
    intro x; rw [hcdef]; ring
  -- input 1: exponential decay of the dual theta series at level `w ≥ 1`
  obtain ⟨Cg, hdecg⟩ := Work.FIArea6Hecke.R.thetaDualM_decay d hd hchi k h0
  -- input 2: boundedness on the compact initial interval `[1, 16d²]`
  have hg_cont := continuousOn_thetaDualMG_Ioi d hd hchi k
  have hsub : Set.Icc (1 : ℝ) (16 * (d : ℝ) ^ 2) ⊆ Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn
    (s := Set.Icc (1 : ℝ) (16 * (d : ℝ) ^ 2)) isCompact_Icc (hg_cont.mono hsub)
  set K' : ℝ := max K 0 with hK'def
  have hK'nn : 0 ≤ K' := le_max_right _ _
  -- the two constants glued by a maximum
  refine ⟨max (K' * Real.exp Real.pi) (max (‖Work.FIArea6Hecke.R.dualConst d chi k‖ * Cg) 1),
    ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max (K' * Real.exp Real.pi)
        (max (‖Work.FIArea6Hecke.R.dualConst d chi k‖ * Cg) 1) :=
      le_trans (le_max_right _ 1) (le_max_right _ _)
    linarith
  · intro x hx1
    -- rewrite the exponential in terms of the rate `c` (definitional, since `c` is `set`)
    have hE : Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * x) = Real.exp ((-c) * x) := rfl
    rw [hE]
    by_cases hxle : x ≤ 16 * (d : ℝ) ^ 2
    · -- initial interval: the compact bound, with `e^{-cx} ≥ e^{-π}` there
      have hxmem : x ∈ Set.Icc (1 : ℝ) (16 * (d : ℝ) ^ 2) := ⟨hx1, hxle⟩
      have h1 : ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ ≤ K' :=
        le_trans (hK x hxmem) (le_max_left _ _)
      have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi - c * x) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hcx : c * x ≤ c * (16 * (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hxle hcpos.le
        linarith [hcp]
      calc ‖Work.FIArea6Hecke.R.thetaDualMG d chi k x‖ ≤ K' := h1
        _ ≤ K' * Real.exp (Real.pi - c * x) := by
              simpa using mul_le_mul_of_nonneg_left hexp1 hK'nn
        _ = (K' * Real.exp Real.pi) * Real.exp ((-c) * x) := by
              rw [show Real.pi - c * x = Real.pi + (-c) * x by ring, Real.exp_add]
              ring
        _ ≤ max (K' * Real.exp Real.pi)
              (max (‖Work.FIArea6Hecke.R.dualConst d chi k‖ * Cg) 1) *
              Real.exp ((-c) * x) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    · -- tail: rescale the decay of `thetaDualM` at level `x/(16d²) ≥ 1`
      have hxle' : 16 * (d : ℝ) ^ 2 < x := not_le.mp hxle
      have harg1 : (1 : ℝ) ≤ x / (16 * (d : ℝ) ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith [hxle']
      have hb := hdecg _ harg1
      rw [Work.FIArea6Hecke.R.thetaDualMG, norm_mul]
      calc ‖Work.FIArea6Hecke.R.dualConst d chi k‖ *
              ‖Work.FIArea6Hecke.R.thetaDualM d chi k (x / (16 * (d : ℝ) ^ 2))‖
          ≤ ‖Work.FIArea6Hecke.R.dualConst d chi k‖ *
              (Cg * Real.exp (-Real.pi * (x / (16 * (d : ℝ) ^ 2)))) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = (‖Work.FIArea6Hecke.R.dualConst d chi k‖ * Cg) * Real.exp ((-c) * x) := by
              rw [harg x]; ring
        _ ≤ max (K' * Real.exp Real.pi)
              (max (‖Work.FIArea6Hecke.R.dualConst d chi k‖ * Cg) 1) *
              Real.exp ((-c) * x) :=
              mul_le_mul_of_nonneg_right
                (le_trans (le_max_left _ _) (le_max_right _ _)) (Real.exp_nonneg _)

end

end Work.FIArea6Hecke.R.MGGrow
