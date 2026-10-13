import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_θ`-bounds for the angular source `Γ̄ = Γ/c − (5/4) sin 2θ`

The angular part of the `Φ_*`-profile is `Γ̄(θ) = Γ(θ)/c − (5/4) sin 2θ`, where
`Γ(θ) = (sin θ cos²θ)^{α/3}` (`Work.Spaces.Gam`) and `c = c(α) ∈ [1/10, 10]`
(`Work.Spaces.c_bounds`) is the normalisation constant.

This file proves that `Γ̄` is bounded uniformly for `0 < α ≤ 1/4`, and that its
iterated `D_θ`-derivatives (`D_θ φ = sin 2θ · φ'`, `Work.Spaces.dthU`) satisfy

  `|D_θ^j Γ̄(θ)| ≤ cc j · α · Γ(θ) + dd j · sin 2θ`   (`1 ≤ j ≤ 5`)

on the open quadrant `(0, π/2)`, with constants independent of `α`.

**Route.**  `D_θ^j` is applied to the two summands separately.  For `Γ` the exact
formula `D_θ^j Γ = α · Tfun (j-1) α · Γ` (`Work.Spaces.dthU_iter_Gam`) together with
the uniform bound `|Tfun| ≤ tBound` (`Work.Spaces.dthU_iter_Tfun_le`) gives the first
summand; for `sin 2θ` one uses the elementary estimate `|D_θ^j sin 2·| ≤ D j · sin 2θ`
(`sin_two_dthU_le` below), which follows from the compactness of `[0, π/2]`: the ordinary
derivatives of `D_θ^i (sin 2·)` are continuous hence bounded there.

Because `D_θ^j (f + g)` is only available on an *open* set (the summands are not
globally smooth — `Γ` is not differentiable at `θ = 0, π/2`), the splitting is
formalised as an `Set.EqOn` on `(0, π/2)`: writing
`dGam α j = Γ` (`j = 0`) resp. `dGam α j = α · Tfun (j-1) α · Γ` (`j ≥ 1`) and
`Giter j = D_θ^j (sin 2·)`, one proves by induction on `j` that
`D_θ^j Γ̄ = (1/c) · dGam α j − (5/4) · Giter j` on `(0, π/2)`
(`GamBar_iter_EqOn`), using `dthU_EqOn_of_eqOn` (a function identity on an open set
is preserved by `D_θ`) and the one-step identity `dGam_step`, which is the recurrence
`α Tfun j α Γ ↦ α Tfun (j+1) α Γ` (`dthU_Tfun_mul_Gam_aux`) plus its `j = 0` case
(`dthU_Gam`).
-/

namespace Work.FTS.PhiStar.Psi0Aux

open scoped Real Topology
open Set Filter

noncomputable section

local notation "C∞" => (⊤ : ℕ∞)

/-! ## Congruence of `D_θ` on an open set -/

/-- `D_θ` only depends on the germ of the function: two functions agreeing on an open
set have `D_θ`-derivatives agreeing there. -/
lemma dthU_EqOn_of_eqOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn f g s) :
    Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) s := by
  intro θ hθ
  simp only [Work.Spaces.dthU_apply]
  rw [Filter.EventuallyEq.deriv_eq (h.eventuallyEq_of_mem (hs.mem_nhds hθ))]

/-! ## The two summands of `Γ̄` -/

/-- `sin 2θ`, as a function of `θ`. -/
noncomputable def S2 : ℝ → ℝ := fun θ => Real.sin (2 * θ)

/-- `Giter j = D_θ^j (sin 2·)`. -/
noncomputable def Giter (j : ℕ) : ℝ → ℝ := Work.Spaces.dthU^[j] S2

/-- The `j`-th `D_θ`-iterate of `Γ` on `(0, π/2)`: `dGam α 0 = Γ` and
`dGam α (j+1) = α · Tfun j α · Γ` (`= D_θ^{j+1} Γ` there). -/
noncomputable def dGam (α : ℝ) : ℕ → ℝ → ℝ
  | 0 => Work.Spaces.Gam α
  | (j+1) => fun θ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ

/-- The right-hand side of the decomposition of `D_θ^j Γ̄` on `(0, π/2)`. -/
noncomputable def Fbar (α : ℝ) (j : ℕ) : ℝ → ℝ :=
  fun θ => (1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ

lemma Fbar_apply (α : ℝ) (j : ℕ) (θ : ℝ) : Fbar α j θ
    = (1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ := rfl

lemma Fbar_zero_apply (α : ℝ) (θ : ℝ) : Fbar α 0 θ = Work.FTS.VocabO.GamBar α θ := by
  change (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ - (5 / 4) * Real.sin (2 * θ)
    = Work.Spaces.Gam α θ / Work.Spaces.c α - (5 / 4) * Real.sin (2 * θ)
  ring

/-! ## Smoothness of the two summands -/

lemma contDiff_S2 : ContDiff ℝ C∞ S2 := by
  show ContDiff ℝ C∞ (fun θ : ℝ => Real.sin (2 * θ))
  fun_prop

lemma Giter_contDiff (j : ℕ) : ContDiff ℝ C∞ (Giter j) := by
  simpa only [Giter] using Work.Spaces.dthU_iter_smooth contDiff_S2 j

lemma Giter_differentiableAt (j : ℕ) (θ : ℝ) : DifferentiableAt ℝ (Giter j) θ :=
  ((Giter_contDiff j).differentiable (by simp)).differentiableAt

lemma dGam_diff (α : ℝ) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : DifferentiableAt ℝ (dGam α j) θ := by
  cases j with
  | zero =>
      simp only [dGam]
      exact Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
  | succ j =>
      simp only [dGam]
      exact (Work.Spaces.Tfun_smooth j α).differentiable (by simp) |>.differentiableAt.const_mul α
        |>.mul (Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2)

/-! ## The two auxiliary estimates -/

/-- **The iterated `D_θ`-derivatives of `sin 2θ` are `O(sin 2θ)`.**
The proof is non-computational: `D_θ (sin 2·) = sin 2θ · (2 cos 2θ)` and, more
generally, `D_θ^{i+1} (sin 2·) = sin 2θ · (D_θ^i (sin 2·))'`, so it suffices to bound
the ordinary derivatives of the iterates; those are continuous (the iterates are
`C^∞`) on the compact interval `[0, π/2]`, hence bounded by compactness, and the
bounds may be fed back as one constant. -/
lemma sin_two_dthU_le :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ m : ℕ, m ≤ 5 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.dthU^[m] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ D m * Real.sin (2 * θ) := by
  have key : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Giter i) θ| ≤ C := by
    intro i
    have hcont : ContinuousOn (deriv (Giter i)) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
      ((Giter_contDiff i).continuous_deriv (by simp)).continuousOn
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
    refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
    have := hC θ hθ
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  choose C hC0 hCbd using key
  refine ⟨fun _ => max 1 (∑ i ∈ Finset.range 7, C i), ?_, ?_⟩
  · intro m
    exact le_trans zero_le_one (le_max_left _ _)
  · intro m hm θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rcases m with _ | i
    · change |S2 θ| ≤ max 1 (∑ i ∈ Finset.range 7, C i) * Real.sin (2 * θ)
      rw [S2, abs_of_nonneg hsin0]
      calc Real.sin (2 * θ) = 1 * Real.sin (2 * θ) := by ring
        _ ≤ max 1 (∑ i ∈ Finset.range 7, C i) * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hsin0
    · change |Work.Spaces.dthU^[i + 1] S2 θ| ≤ max 1 (∑ i ∈ Finset.range 7, C i)
        * Real.sin (2 * θ)
      have hstep : Work.Spaces.dthU^[i + 1] S2 θ
          = Real.sin (2 * θ) * deriv (Giter i) θ := by
        rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
        rfl
      rw [hstep, abs_mul, abs_of_nonneg hsin0]
      have hi7 : i < 7 := by omega
      have hCi : C i ≤ ∑ j ∈ Finset.range 7, C j :=
        Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr hi7)
      have hCD : C i ≤ max 1 (∑ j ∈ Finset.range 7, C j) :=
        le_trans hCi (le_max_right _ _)
      calc Real.sin (2 * θ) * |deriv (Giter i) θ|
          ≤ Real.sin (2 * θ) * C i := mul_le_mul_of_nonneg_left (hCbd i θ hθI) hsin0
        _ ≤ Real.sin (2 * θ) * max 1 (∑ j ∈ Finset.range 7, C j) :=
            mul_le_mul_of_nonneg_left hCD hsin0
        _ = max 1 (∑ j ∈ Finset.range 7, C j) * Real.sin (2 * θ) := by ring

/-- **The recurrence `D_θ (α · Tfun j α · Γ) = α · Tfun (j+1) α · Γ`** on `(0, π/2)`,
by the product rule and `Work.Spaces.Tfun_succ`, using `D_θ Γ = α q Γ`
(`Work.Spaces.dthU_Gam`). -/
lemma dthU_Tfun_mul_Gam_aux (j : ℕ) (α : ℝ) (hα : 0 < α) : Set.EqOn
    (Work.Spaces.dthU (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ))
    (fun θ : ℝ => α * Work.Spaces.Tfun (j + 1) α θ * Work.Spaces.Gam α θ)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
    Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
  have hT : DifferentiableAt ℝ (Work.Spaces.Tfun j α) θ :=
    ((Work.Spaces.Tfun_smooth j α).differentiable (by simp)).differentiableAt
  have hmul : Work.Spaces.dthU (fun θ : ℝ => Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ
      = Work.Spaces.dthU (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
        + Work.Spaces.Tfun j α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ :=
    Work.Spaces.dthU_mul_apply (Work.Spaces.Tfun j α)
      (fun t : ℝ => Work.Spaces.Gam α t) θ hT hG
  have hfun : (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)
      = (fun θ : ℝ => α * (Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)) := by
    funext t; ring
  calc Work.Spaces.dthU (fun θ : ℝ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ
      = α * Work.Spaces.dthU (fun θ : ℝ => Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ := by
        rw [hfun, Work.Spaces.dthU_const_mul]
    _ = α * (Work.Spaces.dthU (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
          + Work.Spaces.Tfun j α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ) := by
        rw [hmul]
    _ = α * (Real.sin (2 * θ) * deriv (Work.Spaces.Tfun j α) θ * Work.Spaces.Gam α θ
          + Work.Spaces.Tfun j α θ * (α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)) := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_Gam α θ hα hθ]
    _ = α * Work.Spaces.Tfun (j + 1) α θ * Work.Spaces.Gam α θ := by
        rw [Work.Spaces.Tfun_succ]; ring

/-! ## The one-step recurrence for `dGam` -/

lemma dthU_dGam_zero (α : ℝ) (hα : 0 < α) :
    Set.EqOn (Work.Spaces.dthU (dGam α 0)) (dGam α 1) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  simpa only [dGam, Work.Spaces.Tfun_zero] using h

lemma dGam_step (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU (dGam α j)) (dGam α (j + 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  cases j with
  | zero => exact dthU_dGam_zero α hα
  | succ i => simpa only [dGam] using dthU_Tfun_mul_Gam_aux i α hα

/-! ## The decomposition of `D_θ^j Γ̄` -/

lemma Fbar_step (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU (Fbar α j)) (Fbar α (j + 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  have hA : DifferentiableAt ℝ (fun θ : ℝ => (1 / Work.Spaces.c α) * dGam α j θ) θ :=
    (dGam_diff α j hθ).const_mul _
  have hB : DifferentiableAt ℝ (fun θ : ℝ => (5 / 4) * Giter j θ) θ :=
    (Giter_differentiableAt j θ).const_mul _
  have hderiv : deriv (Fbar α j) θ
      = (1 / Work.Spaces.c α) * deriv (dGam α j) θ - (5 / 4) * deriv (Giter j) θ := by
    change deriv ((fun θ : ℝ => (1 / Work.Spaces.c α) * dGam α j θ)
      - (fun θ : ℝ => (5 / 4) * Giter j θ)) θ = _
    rw [deriv_sub hA hB, Work.Spaces.deriv_const_mul', Work.Spaces.deriv_const_mul']
  have h1 : Real.sin (2 * θ) * deriv (dGam α j) θ = dGam α (j + 1) θ := by
    have h := dGam_step α hα j hθ
    simpa only [Work.Spaces.dthU_apply] using h
  have h2 : Real.sin (2 * θ) * deriv (Giter j) θ = Giter (j + 1) θ := by
    simp only [Giter, Function.iterate_succ_apply', Work.Spaces.dthU_apply]
  calc Work.Spaces.dthU (Fbar α j) θ
      = Real.sin (2 * θ) * deriv (Fbar α j) θ := by rw [Work.Spaces.dthU_apply]
    _ = Real.sin (2 * θ) * ((1 / Work.Spaces.c α) * deriv (dGam α j) θ
          - (5 / 4) * deriv (Giter j) θ) := by rw [hderiv]
    _ = (1 / Work.Spaces.c α) * (Real.sin (2 * θ) * deriv (dGam α j) θ)
          - (5 / 4) * (Real.sin (2 * θ) * deriv (Giter j) θ) := by ring
    _ = (1 / Work.Spaces.c α) * dGam α (j + 1) θ - (5 / 4) * Giter (j + 1) θ := by rw [h1, h2]
    _ = Fbar α (j + 1) θ := by
        change _ = (1 / Work.Spaces.c α) * dGam α (j + 1) θ - (5 / 4) * Giter (j + 1) θ
        rfl

/-- **The decomposition of the iterated `D_θ`-derivatives of `Γ̄`.**  On the open
quadrant, `D_θ^j Γ̄ = (1/c)·dGam α j − (5/4)·Giter j`. -/
lemma GamBar_iter_EqOn (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α)) (Fbar α j)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  induction j with
  | zero =>
      intro θ _
      simp only [Function.iterate_zero_apply]
      exact (Fbar_zero_apply α θ).symm
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      rw [dthU_EqOn_of_eqOn isOpen_Ioo ih hθ]
      exact Fbar_step α hα j hθ

/-! ## The pointwise bound on `dGam` -/

lemma dGam_le (α : ℝ) (j : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) (hj : 1 ≤ j) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |dGam α j θ| ≤ α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG := Work.Spaces.Gam_bounds α θ hα hθI
  have hT : |Work.Spaces.Tfun i α θ| ≤ Work.Spaces.tBound i 0 := by
    simpa only [Function.iterate_zero_apply] using
      Work.Spaces.dthU_iter_Tfun_le i α hα hα1 θ hθI 0
  simp only [dGam]
  rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG.1]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (le_of_lt hα)) hG.1

/-! ## The target -/

theorem GamBar_dthU_le :
    (∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.VocabO.GamBar α θ| ≤ K) ∧
    (∃ cc dd : ℕ → ℝ, (∀ j, 0 ≤ cc j) ∧ (∀ j, 0 ≤ dd j) ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
          ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)) := by
  obtain ⟨D, hD0, hD⟩ := sin_two_dthU_le
  constructor
  · refine ⟨12, by norm_num, ?_⟩
    intro α hα hα1 θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hG := Work.Spaces.Gam_bounds α θ hα hθI
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
      rw [abs_div, abs_of_pos hcpos, abs_of_nonneg hG.1]
      calc Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 1 / Work.Spaces.c α :=
            div_le_div_of_nonneg_right hG.2 (le_of_lt hcpos)
        _ ≤ 10 := by
            have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hc
            have h2 : (1 : ℝ) / (1 / 10) = 10 := by norm_num
            linarith
    have h2 : |(5 / 4) * Real.sin (2 * θ)| ≤ 5 / 4 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      have := Real.abs_sin_le_one (2 * θ)
      linarith
    have h3 : |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
        ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := by
      calc |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
          = |Work.Spaces.Gam α θ / Work.Spaces.c α + -(5 / 4 * Real.sin (2 * θ))| := by
            ring_nf
        _ ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |-(5 / 4 * Real.sin (2 * θ))| :=
            abs_add_le _ _
        _ = |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := by
            rw [abs_neg]
    change |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)| ≤ 12
    linarith
  · refine ⟨fun j => 10 * Work.Spaces.tBound (j - 1) 0, fun j => (5 / 4) * D j, ?_, ?_, ?_⟩
    · intro j
      have := Work.Spaces.tBound_nonneg (j - 1) 0
      linarith
    · intro j
      have := hD0 j
      linarith
    · intro α hα hα1 j hj1 hj5 θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have heq := GamBar_iter_EqOn α hα j hθ
      have h4 : |(1 / Work.Spaces.c α) * dGam α j θ|
          ≤ 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Work.Spaces.c α)]
        have h1' := dGam_le α j hα (by linarith) hj1 hθ
        have hle : (1 / Work.Spaces.c α) ≤ 10 := by
          have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hc
          have h2 : (1 : ℝ) / (1 / 10) = 10 := by norm_num
          linarith
        have hnn : 0 ≤ α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hG.1
        calc (1 / Work.Spaces.c α) * |dGam α j θ|
            ≤ (1 / Work.Spaces.c α) * (α * Work.Spaces.tBound (j - 1) 0
                * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1' (by positivity)
          _ ≤ 10 * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ := by ring
      have h2 : |(5 / 4) * Giter j θ| ≤ ((5 / 4) * D j) * Real.sin (2 * θ) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        have h := hD j hj5 θ hθ
        have hG2 : |Giter j θ| ≤ D j * Real.sin (2 * θ) := by
          change |Work.Spaces.dthU^[j] S2 θ| ≤ D j * Real.sin (2 * θ)
          exact h
        linarith [hG2]
      have h3 : |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
          ≤ |(1 / Work.Spaces.c α) * dGam α j θ| + |(5 / 4) * Giter j θ| := by
        calc |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
            = |(1 / Work.Spaces.c α) * dGam α j θ + -((5 / 4) * Giter j θ)| := by ring_nf
          _ ≤ |(1 / Work.Spaces.c α) * dGam α j θ| + |-((5 / 4) * Giter j θ)| :=
              abs_add_le _ _
          _ = |(1 / Work.Spaces.c α) * dGam α j θ| + |(5 / 4) * Giter j θ| := by rw [abs_neg]
      rw [heq, Fbar_apply]
      show |(1 / Work.Spaces.c α) * dGam α j θ - (5 / 4) * Giter j θ|
        ≤ 10 * Work.Spaces.tBound (j - 1) 0 * α * Work.Spaces.Gam α θ
          + 5 / 4 * D j * Real.sin (2 * θ)
      linarith [h3, h4, h2]

end

end Work.FTS.PhiStar.Psi0Aux
