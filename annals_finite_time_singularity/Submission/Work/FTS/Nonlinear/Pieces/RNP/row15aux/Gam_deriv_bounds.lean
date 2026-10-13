import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.GamSeqDefs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gseq_iter_bounded
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_low_left
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_low_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bounds for the `dthU`-iterates of `deriv Γ`, and the pointwise lower bound on `|deriv Γ|`

The main content is the identity (on `(0,π/2)`)

  `D_θ^d (deriv Γ) = α · Gseq α d · Γ / sin 2θ`,

where `D_θ = sin 2θ ∂_θ` and `Gseq` is the sequence of `GamSeqDefs.lean`.  Since all the
`D_θ`-iterates of `Gseq α d` are bounded by constants (`Gseq_iter_bounded`), this gives the
first half of `Gam_deriv_bounds`; the second half is the two-sided lower bound obtained from
the explicit formula `deriv Γ = (α/3)(sin θ cos²θ)^{α/3-1} cos θ (cos²θ - 2 sin²θ)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## Elementary differentiability facts -/

theorem deriv_sin_two (θ : ℝ) : deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]
  ring

theorem differentiableAt_sin_two (θ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t)) θ := by
  fun_prop

theorem differentiableOn_Gam (α : ℝ) :
    DifferentiableOn ℝ (Work.Spaces.Gam α) (Set.Ioo 0 (π / 2)) :=
  fun θ hθ => DifferentiableAt.differentiableWithinAt
    (Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2)

theorem differentiableOn_Gseq (α : ℝ) (d : ℕ) :
    DifferentiableOn ℝ (Gseq α d) (Set.Ioo 0 (π / 2)) :=
  Differentiable.differentiableOn ((Gseq_smooth α d).differentiable (by simp))

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
  linarith [hθ.2, Real.pi_pos]

/-! ## The identity `D_θ^d (Γ') = α · Gseq α d · Γ / sin 2θ` -/

/-- If `D_θ^d (Γ') · sin 2θ = 2 α (Gseq α d) Γ` on `(0,π/2)` then `D_θ^d (Γ')` is
differentiable there (it equals an explicit smooth quotient). -/
theorem diffOn_of_eqOn (α : ℝ) (_hα : 0 < α) (d : ℕ)
    (h : Set.EqOn
      (fun θ => Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ
        * Real.sin (2 * θ))
      (fun θ => 2 * α * Gseq α d θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2))) :
    DifferentiableOn ℝ
      (Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t)) (Set.Ioo 0 (π / 2)) := by
  have hR : DifferentiableOn ℝ
      (fun θ => 2 * α * Gseq α d θ * Work.Spaces.Gam α θ / Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) := by
    refine DifferentiableOn.div ?_ ?_ ?_
    · exact DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const (2 * α))
        (differentiableOn_Gseq α d)) (differentiableOn_Gam α)
    · exact fun θ _ => DifferentiableAt.differentiableWithinAt (differentiableAt_sin_two θ)
    · intro θ hθ
      exact ne_of_gt (sin_two_pos_of_mem hθ)
  refine hR.congr ?_
  intro θ hθ
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_of_mem hθ)
  have hh := h hθ
  field_simp
  linarith [hh]

/-- **The key identity.**  On `(0,π/2)`, `D_θ^d (deriv Γ) · sin 2θ = 2 α (Gseq α d) Γ`;
together with the differentiability used inductively. -/
theorem Gam_deriv_iter_eqOn (α : ℝ) (hα : 0 < α) (d : ℕ) :
    Set.EqOn
      (fun θ => Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ
        * Real.sin (2 * θ))
      (fun θ => 2 * α * Gseq α d θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) ∧
    DifferentiableOn ℝ
      (Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t)) (Set.Ioo 0 (π / 2)) := by
  induction d with
  | zero =>
      have hEq : Set.EqOn
          (fun θ => Work.Spaces.dthU^[0] (fun t => deriv (Work.Spaces.Gam α) t) θ
            * Real.sin (2 * θ))
          (fun θ => 2 * α * Gseq α 0 θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
        intro θ hθ
        have h := Work.Spaces.dthU_Gam α θ hα hθ
        simp only [Work.Spaces.dthU_apply] at h
        simp only [Function.iterate_zero_apply, Gseq_zero]
        linear_combination h
      exact ⟨hEq, diffOn_of_eqOn α hα 0 hEq⟩
  | succ d ih =>
      obtain ⟨ihEq, ihDiff⟩ := ih
      have hgoal : Set.EqOn
          (fun θ => Work.Spaces.dthU^[d + 1] (fun t => deriv (Work.Spaces.Gam α) t) θ
            * Real.sin (2 * θ))
          (fun θ => 2 * α * Gseq α (d + 1) θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
        intro θ hθ
        show Work.Spaces.dthU^[d + 1] (fun t => deriv (Work.Spaces.Gam α) t) θ
            * Real.sin (2 * θ) = 2 * α * Gseq α (d + 1) θ * Work.Spaces.Gam α θ
        set Fd : ℝ → ℝ := Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) with hFd
        have hθmem : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
        have hev := ihEq.eventuallyEq_of_mem hθmem
        have hderiv := hev.deriv_eq
        have hdiffAt : DifferentiableAt ℝ Fd θ := ihDiff.differentiableAt hθmem
        have hd1 : DifferentiableAt ℝ (fun t : ℝ => 2 * α * Gseq α d t) θ :=
          DifferentiableAt.const_mul (DifferentiableOn.differentiableAt (differentiableOn_Gseq α d)
            hθmem) (2 * α)
        have hd2 : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
          DifferentiableOn.differentiableAt (differentiableOn_Gam α) hθmem
        have hL : deriv (fun t => Fd t * Real.sin (2 * t)) θ
            = deriv Fd θ * Real.sin (2 * θ) + Fd θ * (2 * Real.cos (2 * θ)) := by
          rw [show (fun t : ℝ => Fd t * Real.sin (2 * t))
                = Fd * (fun t : ℝ => Real.sin (2 * t)) from funext (fun t => rfl),
            deriv_mul hdiffAt (differentiableAt_sin_two θ), deriv_sin_two]
        have hR : deriv (fun t => 2 * α * Gseq α d t * Work.Spaces.Gam α t) θ
            = 2 * α * (deriv (Gseq α d) θ * Work.Spaces.Gam α θ
                + Gseq α d θ * deriv (Work.Spaces.Gam α) θ) := by
          rw [show (fun t : ℝ => 2 * α * Gseq α d t * Work.Spaces.Gam α t)
              = (fun t : ℝ => 2 * α * Gseq α d t) * (fun t => Work.Spaces.Gam α t)
                from funext (fun t => rfl),
            deriv_mul hd1 hd2, Work.Spaces.deriv_const_mul']
          ring
        have hkey : deriv Fd θ * Real.sin (2 * θ)
            = 2 * α * (deriv (Gseq α d) θ * Work.Spaces.Gam α θ
                + Gseq α d θ * deriv (Work.Spaces.Gam α) θ)
              - 2 * Real.cos (2 * θ) * Fd θ := by
          rw [hL, hR] at hderiv
          linear_combination hderiv
        have hIH' : Real.sin (2 * θ) * Fd θ
            = 2 * α * Gseq α d θ * Work.Spaces.Gam α θ := by
          rw [mul_comm]; exact ihEq hθ
        have hGam : Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
            = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
          have h := Work.Spaces.dthU_Gam α θ hα hθ
          rwa [Work.Spaces.dthU_apply] at h
        have hstep : Work.Spaces.dthU^[d + 1] (fun t => deriv (Work.Spaces.Gam α) t)
            = Work.Spaces.dthU Fd :=
          (Work.Spaces.dthU_iter_succ_apply d (fun t => deriv (Work.Spaces.Gam α) t)).symm
        rw [hstep, Work.Spaces.dthU_apply, Gseq_succ_apply, gfun_eq,
          Work.Spaces.dthU_apply]
        rw [show Real.sin (2 * θ) * deriv Fd θ * Real.sin (2 * θ)
              = Real.sin (2 * θ) * (deriv Fd θ * Real.sin (2 * θ)) from by ring, hkey]
        rw [show Real.sin (2 * θ) * (2 * α * (deriv (Gseq α d) θ * Work.Spaces.Gam α θ
                + Gseq α d θ * deriv (Work.Spaces.Gam α) θ)
              - 2 * Real.cos (2 * θ) * Fd θ)
            = 2 * α * (Real.sin (2 * θ) * (deriv (Gseq α d) θ * Work.Spaces.Gam α θ)
                + Gseq α d θ * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ))
              - 2 * Real.cos (2 * θ) * (Real.sin (2 * θ) * Fd θ) from by ring, hGam, hIH',
          Work.Spaces.qfun_apply]
        ring
      exact ⟨hgoal, diffOn_of_eqOn α hα (d + 1) hgoal⟩

/-! ## The assembly -/

/-- The first conjunct of `Gam_deriv_bounds`, from the constant bounds on the
`dthU`-iterates of the sequence `Gseq`. -/
theorem Gam_deriv_upper (hG : ∀ d : ℕ, ∃ M : ℕ → ℝ, (∀ m, 0 ≤ M m) ∧
      ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ m : ℕ,
        |Work.Spaces.dthU^[m] (Gseq α d) θ| ≤ M m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∀ d : ℕ, d ≤ 4 →
        |Work.Spaces.dthU^[d] (fun t : ℝ => deriv (Work.Spaces.Gam α) t) θ|
          ≤ C * α * Work.Spaces.Gam α θ
              * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1) := by
  classical
  choose M hM using hG
  have hM0 : ∀ d m, 0 ≤ M d m := fun d => (hM d).1
  have hMle : ∀ d α, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ, ∀ m : ℕ,
      |Work.Spaces.dthU^[m] (Gseq α d) θ| ≤ M d m := fun d => (hM d).2
  refine ⟨(∑ k ∈ Finset.range 5, M k 0) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range 5, M k 0 := Finset.sum_nonneg (fun k _ => hM0 k 0)
    linarith
  · intro α θ hα hα1 hθ d hd
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hsc : 0 < Real.sin θ * Real.cos θ := mul_pos hsin hcos
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
    have hcs : Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ
        = 1 / (Real.sin θ * Real.cos θ) := by
      rw [div_add_div _ _ (ne_of_gt hsin) (ne_of_gt hcos),
        show Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 from by
          nlinarith [Real.sin_sq_add_cos_sq θ]]
    have hGd : |Gseq α d θ| ≤ M d 0 := hMle d α hα hα1 θ hθI 0
    have hEq := (Gam_deriv_iter_eqOn α hα d).1 hθ
    have habs : |Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ|
          * Real.sin (2 * θ) = 2 * α * |Gseq α d θ| * Work.Spaces.Gam α θ := by
      have h := congrArg (fun x => |x|) hEq
      rw [abs_mul, abs_of_pos hs, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α),
        abs_of_nonneg hGam0] at h
      linarith [h]
    have hF : |Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ|
        = 2 * α * |Gseq α d θ| * Work.Spaces.Gam α θ / Real.sin (2 * θ) :=
      (eq_div_iff (ne_of_gt hs)).2 habs
    have hMC : M d 0 ≤ (∑ k ∈ Finset.range 5, M k 0) + 1 := by
      have hd5 : d ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
      have := Finset.single_le_sum (f := fun k => M k 0) (fun k _ => hM0 k 0) hd5
      linarith
    have hbr : (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1) * Real.sin (2 * θ)
        = 2 * (1 + Real.sin θ * Real.cos θ) := by
      rw [hcs, Real.sin_two_mul]
      field_simp
    have hsc0 : 0 ≤ Real.sin θ * Real.cos θ := le_of_lt hsc
    have hprod : |Gseq α d θ| * (α * Work.Spaces.Gam α θ)
        ≤ (M d 0) * (α * Work.Spaces.Gam α θ) :=
      mul_le_mul_of_nonneg_right hGd (mul_nonneg (le_of_lt hα) hGam0)
    have hCprod : (M d 0) * (α * Work.Spaces.Gam α θ)
        ≤ ((∑ k ∈ Finset.range 5, M k 0) + 1) * (α * Work.Spaces.Gam α θ) :=
      mul_le_mul_of_nonneg_right hMC (mul_nonneg (le_of_lt hα) hGam0)
    have h1 : 2 * α * |Gseq α d θ| * Work.Spaces.Gam α θ
        ≤ 2 * α * (M d 0) * Work.Spaces.Gam α θ := by
      have h := mul_le_mul_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [h]
    have h2 : 2 * α * (M d 0) * Work.Spaces.Gam α θ
        ≤ 2 * α * ((∑ k ∈ Finset.range 5, M k 0) + 1) * Work.Spaces.Gam α θ := by
      have h := mul_le_mul_of_nonneg_right hCprod (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [h]
    have hC0 : 0 ≤ (∑ k ∈ Finset.range 5, M k 0) + 1 := by
      have hsum0 : 0 ≤ ∑ k ∈ Finset.range 5, M k 0 := Finset.sum_nonneg (fun k _ => hM0 k 0)
      linarith
    have h3 : 2 * α * ((∑ k ∈ Finset.range 5, M k 0) + 1) * Work.Spaces.Gam α θ
        ≤ ((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
            * (2 * (1 + Real.sin θ * Real.cos θ)) := by
      have hnn : 0 ≤ ((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ :=
        mul_nonneg (mul_nonneg hC0 (le_of_lt hα)) hGam0
      have h2le : (2 : ℝ) ≤ 2 * (1 + Real.sin θ * Real.cos θ) := by linarith
      calc 2 * α * ((∑ k ∈ Finset.range 5, M k 0) + 1) * Work.Spaces.Gam α θ
          = 2 * (((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ) := by ring
        _ ≤ 2 * (1 + Real.sin θ * Real.cos θ)
              * (((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right h2le hnn
        _ = ((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
              * (2 * (1 + Real.sin θ * Real.cos θ)) := by ring
    have hmain : |Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ| * Real.sin (2 * θ)
        ≤ (((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
            * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1)) * Real.sin (2 * θ) := by
      calc |Work.Spaces.dthU^[d] (fun t => deriv (Work.Spaces.Gam α) t) θ| * Real.sin (2 * θ)
          = 2 * α * |Gseq α d θ| * Work.Spaces.Gam α θ := habs
        _ ≤ 2 * α * (M d 0) * Work.Spaces.Gam α θ := h1
        _ ≤ 2 * α * ((∑ k ∈ Finset.range 5, M k 0) + 1) * Work.Spaces.Gam α θ := h2
        _ ≤ ((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
              * (2 * (1 + Real.sin θ * Real.cos θ)) := h3
        _ = (((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
              * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1))
              * Real.sin (2 * θ) := by
            rw [show (((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
                  * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1)) * Real.sin (2 * θ)
                = ((∑ k ∈ Finset.range 5, M k 0) + 1) * α * Work.Spaces.Gam α θ
                  * ((Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1)
                    * Real.sin (2 * θ)) from by ring, hbr]
    exact le_of_mul_le_mul_right hmain hs

/-- The second conjunct of `Gam_deriv_bounds`, from the two one-sided bounds. -/
theorem Gam_deriv_lower
    (hL : ∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 6) →
        c * α * (Real.sin θ) ^ (α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|)
    (hR : ∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ico (Real.pi / 3) (Real.pi / 2) →
        c * α * (Real.cos θ) ^ (2 * α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      (θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 6) →
          c * α * (Real.sin θ) ^ (α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|) ∧
      (θ ∈ Set.Ico (Real.pi / 3) (Real.pi / 2) →
          c * α * (Real.cos θ) ^ (2 * α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|) := by
  obtain ⟨c₁, hc₁, h₁⟩ := hL
  obtain ⟨c₂, hc₂, h₂⟩ := hR
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun α θ hα hα1 => ⟨?_, ?_⟩⟩
  · intro hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hr : 0 ≤ (Real.sin θ) ^ (α / 3 - 1) := Real.rpow_nonneg hsin _
    refine le_trans ?_ (h₁ α θ hα hα1 hθ)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hα)) hr
  · intro hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], le_of_lt hθ.2⟩
    have hr : 0 ≤ (Real.cos θ) ^ (2 * α / 3 - 1) := Real.rpow_nonneg hcos _
    refine le_trans ?_ (h₂ α θ hα hα1 hθ)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hα)) hr

theorem Gam_deriv_bounds :
    (∃ C : ℝ, 0 < C ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∀ d : ℕ, d ≤ 4 →
        |Work.Spaces.dthU^[d] (fun t : ℝ => deriv (Work.Spaces.Gam α) t) θ|
          ≤ C * α * Work.Spaces.Gam α θ
              * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
      (θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 6) →
          c * α * (Real.sin θ) ^ (α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|) ∧
      (θ ∈ Set.Ico (Real.pi / 3) (Real.pi / 2) →
          c * α * (Real.cos θ) ^ (2 * α / 3 - 1) ≤ |deriv (Work.Spaces.Gam α) θ|)) :=
  ⟨Gam_deriv_upper Gseq_iter_bounded,
   Gam_deriv_lower Gam_deriv_low_left Gam_deriv_low_right⟩

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
