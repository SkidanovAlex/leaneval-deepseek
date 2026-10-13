import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-
# The `D_θ F_*`-package at order six

`Work.FTS.Nonlinear.FstarPkg.DthFstar_W` proves the level-`4` statement
`𝒲^{4,∞}(D_θ F_*) ≤ C α²`.  Here we extend it to level `6`, which needs the angular weighted
estimate `|D_θ^m Γ| ·  sin(2θ)^{-α/5}/(α + sin 2θ) ≤ K α` for `2 ≤ m ≤ 7` instead of `m ≤ 5`.
Everything else in the level-`4` proof was already level-generic (the factorisation
`pzIter k (DthIter j (Dth F_*)) = (2α/c) · hKer^{(k)} · D_θ^{j+1}Γ` holds for all `j,k`, the
radial bound `pzIter_hKer_bound` for all `k`).

The point of this file is therefore the *two extra induction steps* of the weighted angular
estimate.  They are obtained without any explicit polynomial computation: instead of the sharp
pointwise bound `|D_θ^m q| ≤ 1000 sin²(2θ)` (which was computed by hand for `m ≤ 4`), we use

* the *numerical* `qBound m` (a compactness bound for `|D_θ^m q|` on `[0,π/2]`, whose value is
  irrelevant), and
* the elementary weight inequality `sin 2θ · Γ · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1`
  (`sin_Gam_Wt_le_one`), which is exactly what makes the *top* summand `a = m` of the Leibniz
  expansion `D_θ^{m+1}Γ = α ∑_a C(m,a) (D_θ^a q)(D_θ^{m-a}Γ)` harmless: the factor
  `D_θ^m q = sin 2θ · (D_θ^{m-1}q)'` supplies the single factor of `sin 2θ` needed.

Both the `α Γ Wt ≤ 1` and the `sin 2θ Γ Wt ≤ 1` inequalities are used in the two non-top cases.
-/

namespace W6Aux

open Work.FTS.Nonlinear.FstarPkg.DthAux

/-! ## Numerical bounds for the iterates of `qfun` -/

/-- A uniform bound for `|D_θ^a q|` on `[0,π/2]`, always at least `1`. -/
noncomputable def Qb (a : ℕ) : ℝ := max (Work.Spaces.qBound a) 1

lemma Qb_pos (a : ℕ) : 0 < Qb a := lt_of_lt_of_le one_pos (le_max_right _ _)

lemma Qb_nonneg (a : ℕ) : 0 ≤ Qb a := le_of_lt (Qb_pos a)

lemma abs_iter_qfun_le_Qb (a : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| ≤ Qb a :=
  le_trans (Work.Spaces.dthU_qfun_le_qBound a hθ) (le_max_left _ _)

/-- The sum of the first `m+1` constants `Qb`. -/
noncomputable def Qs (m : ℕ) : ℝ := ∑ a ∈ Finset.range (m + 1), Qb a

lemma Qs_nonneg (m : ℕ) : 0 ≤ Qs m :=
  Finset.sum_nonneg fun a _ => Qb_nonneg a

lemma Qb_le_Qs {a m : ℕ} (ha : a ≤ m) : Qb a ≤ Qs m :=
  Finset.single_le_sum (fun i _ => Qb_nonneg i) (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

/-- `|(D_θ^m q)'|` is bounded on `[0,π/2]`. -/
lemma deriv_iter_qfun_bounded (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun) θ| ≤ B := by
  have hcd : ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.Spaces.dthU^[m] Work.Spaces.qfun) :=
    Work.Spaces.dthU_iter_smooth Work.Spaces.qfun_smooth m
  have hcont : ContinuousOn (deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun))
      (Set.Icc 0 (π / 2)) :=
    (hcd.continuous_deriv (by simp)).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

noncomputable def dqB (m : ℕ) : ℝ := Classical.choose (deriv_iter_qfun_bounded m)

lemma dqB_nonneg (m : ℕ) : 0 ≤ dqB m :=
  (Classical.choose_spec (deriv_iter_qfun_bounded m)).1

lemma deriv_iter_qfun_le_dqB (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun) θ| ≤ dqB m :=
  (Classical.choose_spec (deriv_iter_qfun_bounded m)).2 θ hθ

/-- `D_θ^j q = sin 2θ · (D_θ^{j-1}q)'` for `j ≥ 1`. -/
lemma dthU_iter_pointwise {j : ℕ} (hj : 1 ≤ j) (θ : ℝ) :
    Work.Spaces.dthU^[j] Work.Spaces.qfun θ
      = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j - 1] Work.Spaces.qfun) θ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]

/-! ## The one-factor weight inequality -/

/-- `sin 2θ · Γ · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1`: a single factor of `sin 2θ` suffices to
absorb the weight `Wt`, because `Γ · sin(2θ)^{-α/5} ≤ 1`. -/
lemma sin_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩
  have hA : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 :=
    Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne hα hα1 hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  rw [Wt,
    show Real.sin (2 * θ) * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (Real.sin (2 * θ) * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))))
        / (α + Real.sin (2 * θ)) from by ring,
    div_le_one hden]
  nlinarith [hs0, hA]

/-! ## The two extra Leibniz steps -/

/-- The per-summand budget of the `m ↦ m+1` step. -/
noncomputable def Bsum (m : ℕ) (K : ℝ) : ℝ :=
  Qb 0 * K + Qs m * TM m + dqB (m - 1)

lemma Bsum_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bsum m K := by
  rw [Bsum]
  have h2 : 0 ≤ Qs m * TM m := mul_nonneg (Qs_nonneg m) (le_of_lt (TM_pos m))
  have h3 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
  have h1 : 0 ≤ Qb 0 * K := mul_nonneg (Qb_nonneg 0) hK
  linarith

/-- The budget for a fixed binomial coefficient `C(m,a) ≤ 2^m`. -/
noncomputable def CQ (m : ℕ) (K : ℝ) : ℝ := (2 : ℝ) ^ m * Bsum m K

lemma CQ_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ CQ m K := by
  rw [CQ]
  exact mul_nonneg (by positivity) (Bsum_nonneg hK)

/-- The `m ↦ m+1` budget. -/
noncomputable def Bstep2 (m : ℕ) (K : ℝ) : ℝ := ((m : ℝ) + 1) * CQ m K

lemma Bstep2_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bstep2 m K := by
  rw [Bstep2]
  have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  exact mul_nonneg this (CQ_nonneg hK)

/-- The bound for a single summand of the Leibniz expansion at order `m ≥ 2`. -/
lemma summand_le2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {a : ℕ} (ha : a ≤ m) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
        Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
      ≤ Bsum m K := by
  have hW : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- `a = 0`: the induction hypothesis, times `|q| ≤ Qb 0`
    subst ha0
    simp only [Function.iterate_zero_apply, Nat.sub_zero]
    have hIH := hKm α hα hα1 θ hθ
    have hq := abs_iter_qfun_le_Qb 0 hθ
    have hstep : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ) ≤ Qb 0 * (K * α) :=
      mul_le_mul hq hIH (mul_nonneg (abs_nonneg _) hW) (Qb_nonneg 0)
    have hfin : Qb 0 * (K * α) ≤ Qb 0 * K := by
      apply mul_le_mul_of_nonneg_left _ (Qb_nonneg 0)
      nlinarith [hK0, hα, hα1]
    have h1 : Qb 0 * K ≤ Bsum m K := by
      rw [Bsum]
      have hTM := TM_pos m
      have hd := dqB_nonneg (m - 1)
      have hQ := Qs_nonneg m
      nlinarith [mul_nonneg hQ (le_of_lt hTM)]
    calc |Work.Spaces.qfun θ * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
        = |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ) := by rw [abs_mul]; ring
      _ ≤ Qb 0 * (K * α) := hstep
      _ ≤ Qb 0 * K := hfin
      _ ≤ Bsum m K := h1
  · rcases eq_or_lt_of_le ha with ham | ham
    · -- `a = m`: `D_θ^m q = sin 2θ · (D_θ^{m-1}q)'` supplies the factor of `sin 2θ`
      rw [ham]
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2, Real.pi_pos]⟩
      have hpt := dthU_iter_pointwise (j := m) (by omega) θ
      have hk : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * Wt α θ
          ≤ dqB (m - 1) := by
        rw [hpt, abs_mul, abs_of_nonneg hs0]
        have hsin := sin_Gam_Wt_le_one hα hα1 hθ
        have hle : |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
            ≤ dqB (m - 1) := deriv_iter_qfun_le_dqB (m - 1) hθ
        have hd0 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
        calc Real.sin (2 * θ) * |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
              * Work.Spaces.Gam α θ * Wt α θ
            = |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
              * (Real.sin (2 * θ) * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ dqB (m - 1) * 1 :=
              mul_le_mul hle hsin (mul_nonneg (mul_nonneg hs0 hG0) hW) hd0
          _ = dqB (m - 1) := by ring
      have h1 : dqB (m - 1) ≤ Bsum m K := by
        rw [Bsum]
        have hTM := TM_pos m
        have hQ := Qs_nonneg m
        have h1 : 0 ≤ Qb 0 * K := mul_nonneg (Qb_nonneg 0) hK0
        have h2 : 0 ≤ Qs m * TM m := mul_nonneg hQ (le_of_lt hTM)
        have h3 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
        linarith
      calc |Work.Spaces.dthU^[m] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          = |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * Wt α θ := by
            simp only [Nat.sub_self, Function.iterate_zero_apply, abs_mul,
              abs_of_nonneg hG0]
        _ ≤ dqB (m - 1) := hk
        _ ≤ Bsum m K := h1
    · -- `1 ≤ a ≤ m-1`: the crude bound for `D_θ^{m-a}Γ`
      have ha1 : 1 ≤ a := hapos
      have hm1 : 1 ≤ m - a := by omega
      have hQ := abs_iter_qfun_le_Qb a hθ
      have hQ' : Qb a ≤ Qs m := Qb_le_Qs ha
      have hCrude := Work.Spaces.dthU_Gam_le (m - a) hm1 α hα hα1 θ hθ
      have htB : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := tBound_le_TM (by omega)
      have hk : |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ Qs m * TM m := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|
            ≤ α * TM m * Work.Spaces.Gam α θ :=
          le_trans hCrude (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htB hα.le) hG0)
        have h1 : α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
          have h := alpha_Gam_Wt_le_one hα hθ
          linarith [h]
        calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| *
              |Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
            ≤ Qs m * (α * TM m * Work.Spaces.Gam α θ) * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul (le_trans hQ hQ') h2 (abs_nonneg _) (Qs_nonneg m)
          _ = Qs m * TM m * (α * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ Qs m * TM m * 1 := by
              apply mul_le_mul_of_nonneg_left h1
              exact mul_nonneg (Qs_nonneg m) (le_of_lt (TM_pos m))
          _ = Qs m * TM m := by ring
      have h1 : Qs m * TM m ≤ Bsum m K := by
        rw [Bsum]
        have hd := dqB_nonneg (m - 1)
        have h0 := mul_nonneg (Qb_nonneg 0) hK0
        linarith
      calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ Qs m * TM m := hk
        _ ≤ Bsum m K := h1

/-- **The Leibniz step at order `m ≥ 2`**: the weighted bound at order `m+1` from the bound at
order `m`, valid for every `m ≥ 2` (no upper bound on `m` is needed). -/
lemma step2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m + 1] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ Bstep2 m K * α := by
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  by_cases hI : θ ∈ Set.Ioo 0 (π / 2)
  · have hGam_diff : ContDiffOn ℝ ⊤ (fun t => Work.Spaces.Gam α t) (Set.Ioo 0 (π / 2)) :=
      contDiffOn_Gam_Ioo' α
    have hq_diff : ContDiffOn ℝ ⊤ Work.Spaces.qfun (Set.Ioo 0 (π / 2)) := by
      show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - 1 / 3) (Set.Ioo 0 (π / 2))
      fun_prop
    have hEqOn : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) := by
      intro t ht
      rw [Work.Spaces.dthU_Gam α t hα ht]
      ring
    have hmain : Work.Spaces.dthU^[m + 1] (fun t => Work.Spaces.Gam α t) θ
        = α * (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)) := by
      rw [Function.iterate_succ_apply]
      rw [dthU_iter_congr_open isOpen_Ioo m (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) hEqOn hI]
      simp only [Work.Spaces.dthU_iter_const_mul]
      rw [show (fun θ : ℝ => Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
          = (Work.Spaces.qfun * fun θ : ℝ => Work.Spaces.Gam α θ) from rfl]
      rw [dthU_iter_mul_Ioo m Work.Spaces.qfun (fun θ : ℝ => Work.Spaces.Gam α θ) hI
        hq_diff hGam_diff]
    have hsum : |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        ≤ ((m : ℝ) + 1) * CQ m K := by
      have habs : |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| := by
        calc |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ ∑ a ∈ Finset.range (m + 1), |(m.choose a : ℝ) *
                (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose a))]
      have h2 : (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
          ≤ ((m : ℝ) + 1) * CQ m K := by
        rw [Finset.sum_mul]
        calc ∑ a ∈ Finset.range (m + 1), ((m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
            ≤ ∑ _a ∈ Finset.range (m + 1), CQ m K := by
              apply Finset.sum_le_sum
              intro a ha
              have ham : a ≤ m := by
                have := Finset.mem_range.mp ha
                omega
              have hX := summand_le2 m hm hK0 hKm hα hα1 hθ ham
              have hb : (m.choose a : ℝ) ≤ (2 : ℝ) ^ m := by
                exact_mod_cast Nat.choose_le_two_pow m a
              have hX0 : 0 ≤ |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                    Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ :=
                mul_nonneg (abs_nonneg _) hW0
              calc ((m.choose a : ℝ) *
                    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                      Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
                  = (m.choose a : ℝ) *
                      (|Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                        Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ) := by
                    ring
                _ ≤ (2 : ℝ) ^ m * Bsum m K :=
                    mul_le_mul hb hX hX0 (by positivity)
                _ = CQ m K := by rw [CQ]
          _ = ((m : ℝ) + 1) * CQ m K := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      exact le_trans (mul_le_mul_of_nonneg_right habs hW0) h2
    rw [hmain, abs_mul, abs_of_pos hα]
    calc α * |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        = α * (|∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ) := by ring
      _ ≤ α * (((m : ℝ) + 1) * CQ m K) := mul_le_mul_of_nonneg_left hsum hα.le
      _ = Bstep2 m K * α := by rw [Bstep2]; ring
  · -- angular endpoints: the weight vanishes
    have hs : Real.sin (2 * θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π / 2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2 * (π / 2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    exact mul_nonneg (Bstep2_nonneg hK0) hα.le

/-- One step of the induction, valid for any `m ≥ 2`. -/
lemma Good_step2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K) (hK : Good m K) :
    Good (m + 1) (max K (Bstep2 m K)) := by
  intro m' hm2 hm' α hα hα1 θ hθ
  by_cases hle : m' ≤ m
  · have h1 := hK m' hm2 hle α hα hα1 θ hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  · have hm'eq : m' = m + 1 := by omega
    rw [hm'eq]
    have h2 := step2 m hm hK0 (hK m hm (le_refl m)) α hα hα1 θ hθ
    exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le)

/-- The weighted angular estimate at orders `2 ≤ m ≤ 6`. -/
lemma Good_six : Good 6 (max K5 (Bstep2 5 K5)) :=
  Good_step2 5 (by norm_num) (le_of_lt K5_pos) Good_five

/-- The weighted angular estimate at orders `2 ≤ m ≤ 7`. -/
lemma Good_seven : Good 7 (max (max K5 (Bstep2 5 K5))
    (Bstep2 6 (max K5 (Bstep2 5 K5)))) :=
  Good_step2 6 (by norm_num)
    (le_trans (le_of_lt K5_pos) (le_max_left _ _)) Good_six

/-- **The weighted angular estimate at orders `2 ≤ m ≤ 7`.** -/
theorem dthGamWeightLe7 : ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → m ≤ 7 →
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α := by
  refine ⟨max (max K5 (Bstep2 5 K5)) (Bstep2 6 (max K5 (Bstep2 5 K5))),
    lt_of_lt_of_le K5_pos (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro m hm hm7
  exact Good_seven m hm hm7

/-! ## The level-`l` assembly

The remainder of the level-`4` proof (`DthFstar_mixed_bound`, `KD`, `WlInfMem_DthFstar`,
`WlInf_DthFstar_le`) is level-independent except for the explicit numerals `4`, `5`: the
factorization `FstarDthFactor` holds for all `j,k`, the radial bound `pzIter_hKer_bound` for all
`k`, and the angular input is used only through the hypothesis `hK` on the orders `2 ≤ m ≤ l+1`.
We therefore prove the level-`l` statements once and specialise to `l = 6`. -/

/-- The universal constant of the level-`l` estimate for `D_θF_*`. -/
noncomputable def KBl (l : ℕ) (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), 20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)))
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then 20 * K * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KBl_nonneg (l : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ KBl l K := by
  rw [KBl]
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  · exact mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)) (by positivity)
  · split_ifs with h
    · exact mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)
    · norm_num

/-- The mixed slots of `𝒲^{l,∞}(D_θF_*)`. -/
lemma DthFstar_mixed_bound_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j) (hjl : j ≤ l)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  rw [show (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))
      = (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ * Wt α θ from by
    rw [Wt]; ring]
  rw [FstarDthFactor α j k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hdth := hK (j+1) (by omega) (by omega) α hα hα1 θ hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ) * Wt α θ
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ) := by ring
  have hmain : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ)|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
    rw [abs_mul]
    have hAB : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
        ≤ 20 * α * ((k.factorial : ℝ) * (k + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
    have hdW : |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ| ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hW0]
      exact hdth
    calc |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
          * |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ|
        ≤ (20 * α * ((k.factorial : ℝ) * (k + 1))) * (K * α) :=
          mul_le_mul hAB hdW (abs_nonneg _) (by positivity)
      _ = (20 * K * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring
  rw [hloc]
  exact hmain

/-- Membership of `D_θF_*` in `𝒲^{l,∞}`. -/
lemma WlInfMem_DthFstar_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α l (Work.Spaces.Dth (Work.Construction.Fstar α)) := by
  constructor
  · intro k hk
    refine ⟨20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2,
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_mixed_bound_l hK α hα hα1 j k hj1 hj z θ hz hθ

/-- The `𝒲^{l,∞}`-norm bound for `D_θF_*`. -/
lemma WlInf_DthFstar_le_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α l (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ KBl l K * α^2 := by
  have h2 : KBl l K * α^2 =
      (∑ k ∈ Finset.range (l + 1),
          20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2)
        + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then
              20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2 else 0) := by
    rw [KBl, add_mul]
    congr 1
    · rw [Finset.sum_mul]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h <;> ring
  rw [Work.Spaces.WlInf, h2]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => DthFstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        DthFstar_mixed_bound_l hK α hα hα1 j k hcond.1 (by omega) z θ hz hθ
    · simp

end W6Aux

theorem DthFstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := W6Aux.dthGamWeightLe7
  have hK6 : ∀ m : ℕ, 2 ≤ m → m ≤ 6 + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ K * α :=
    fun m hm hm7 => hK m hm hm7
  refine ⟨W6Aux.KBl 6 K + 1, by linarith [W6Aux.KBl_nonneg 6 (le_of_lt hKpos)],
    fun α hα hα1 => ⟨?_, ?_⟩⟩
  · exact W6Aux.WlInfMem_DthFstar_l hK6 α hα hα1
  · refine le_trans (W6Aux.WlInf_DthFstar_le_l hK6 α hα hα1) ?_
    have h0 : 0 ≤ α ^ 2 := sq_nonneg α
    nlinarith [W6Aux.KBl_nonneg 6 (le_of_lt hKpos), h0]

end Work.FTS.StrongPersist
