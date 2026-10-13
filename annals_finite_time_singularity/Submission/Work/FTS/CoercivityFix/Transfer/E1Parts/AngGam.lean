/-
# `E1Parts/AngGam.lean` — the angular data of the transfer defect `E1`

`E1 α f = (sin 2θ · Γ'(θ)) · radA α f (z)` with `Γ = Gam α = (sinθ cos²θ)^{α/3}`.  Writing
`D_θ = sin(2θ) ∂_θ = Spaces.Lop`, the angular factor is `D_θ Γ`, and
`DthIter i (fun _ θ' => D_θΓ θ') 0 θ = Lop^[i+1] (Gam α) θ`.  This file proves

* `Lop_iter_Gam_succ`: `Lop^[j+1] (Gam α) θ = Gam α θ · (2α/3)·Aang j (cos²θ) α` on the open
  interval, by the `glop_step`/`glop_Aang_succ` recursion (the `Construction.Aang` family);
* `Gam_Lop_iter_bound`: `|Lop^[k] (Gam α) θ| ≤ 10^8 · Gam α θ` for `1 ≤ k ≤ 4`, `θ ∈ Iθ`;
* `Gam_sq_smE_integrable`, `Gam_sq_smG_integrable`: the two weighted squares of `Γ` are
  integrable on `Iθ` (from `Gam θ² ≤ sin(2θ)^{2α/3}` and `Spaces.sin_two_rpow`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The iterates of `Γ` -/

/-- **`D_θ^{j+1} Γ = Γ · (2α/3)·Aᵢ(cos²θ)`** on the open quadrant, for `j ≤ 4`. -/
theorem Lop_iter_Gam_succ (α : ℝ) (hα : 0 < α) :
    ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
        = Work.Spaces.Gam α θ
          * (2 * α / 3 * Work.Construction.Aang j (Real.cos θ ^ 2) α) := by
  intro j
  induction j with
  | zero =>
      intro _ θ hθ
      show Work.Spaces.Lop (Work.Spaces.Gam α) θ = _
      rw [Work.Construction.glop_Gam_deriv α θ hα hθ, Work.Construction.Aang_zero]
      ring
  | succ j ih =>
      intro hj θ hθ
      have hj4 : j ≤ 4 := by omega
      have hj3 : j ≤ 3 := by omega
      have hev : (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj4 y hy
      have hidx : (Work.Spaces.Lop^[Nat.succ j + 1] (Work.Spaces.Gam α))
          = Work.Spaces.Lop (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) :=
        Function.iterate_succ_apply' Work.Spaces.Lop (j + 1) (Work.Spaces.Gam α)
      rw [hidx]
      have hLop : Work.Spaces.Lop (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
          = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j + 1] (Work.Spaces.Gam α)) θ
          = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y
              * (2 * α / 3 * Work.Construction.Aang j (Real.cos y ^ 2) α)) θ
        rw [hev.deriv_eq]
      rw [hLop]
      rw [Work.Construction.glop_step α hα
        (fun x : ℝ => 2 * α / 3 * Work.Construction.Aang j x α)
        ((Work.Construction.differentiable_Aang j hj4 α).const_mul (2 * α / 3)) θ hθ]
      rw [deriv_const_mul (2 * α / 3)
        ((Work.Construction.differentiable_Aang j hj4 α).differentiableAt)]
      rw [← Work.Construction.glop_Aang_succ j hj3 (Real.cos θ ^ 2) α]
      ring

/-- The coefficient `(2α/3)·Aang j x α` is bounded by `10^8` on `[0,1]` for `j ≤ 4`,
`0 < α ≤ 1`. -/
theorem coeff_abs_le (j : ℕ) (hj : j ≤ 4) (x α : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / 3 * Work.Construction.Aang j x α| ≤ 10 ^ 8 := by
  have hα3 : 0 ≤ 2 * α / 3 := by linarith
  have hx41 : 4 * x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [Work.Construction.Aang_zero, abs_mul, abs_of_nonneg hα3]
    have h3x2 : |3 * x - 2| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]
    nlinarith
  · have hb : |Work.Construction.Aang j x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
      interval_cases j
      · exact Work.Construction.glop_Aang_bound_one x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_two x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_three x α hx hα hα1
      · exact Work.Construction.glop_Aang_bound_four x α hx hα hα1
    rw [abs_mul, abs_of_nonneg hα3]
    have h2 : 10 ^ 7 * (α + 4 * x * (1 - x)) ≤ 2 * 10 ^ 7 := by nlinarith
    nlinarith

/-- **The angular iterate bound**: `|D_θ^k Γ θ| ≤ 10^8 Γ θ` for `1 ≤ k ≤ 4` and `θ ∈ Iθ`. -/
theorem Gam_Lop_iter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[k] (Work.Spaces.Gam α)) θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
  have hGam : Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := rfl
  intro k hk hk4 θ hθ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- the `sin 2θ = 0` endpoints
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hzero : (Work.Spaces.Lop^[m + 1] (Work.Spaces.Gam α)) 0 = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]
    rw [hzero, hGam]
    have hb : Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) := by norm_num
    show |(0 : ℝ)| ≤ 10 ^ 8 * ((Real.sin 0 * Real.cos 0 ^ 2) ^ (α / 3))
    rw [hb, Real.zero_rpow (by positivity : α / 3 ≠ 0)]
    norm_num
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    have hzero : (Work.Spaces.Lop^[m + 1] (Work.Spaces.Gam α)) (π / 2) = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      have hs : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
      rw [hs, zero_mul]
    rw [hzero, hGam]
    have hb : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = (0 : ℝ) := by norm_num
    show |(0 : ℝ)| ≤ 10 ^ 8 * ((Real.sin (π / 2) * Real.cos (π / 2) ^ 2) ^ (α / 3))
    rw [hb, Real.zero_rpow (by positivity : α / 3 ≠ 0)]
    norm_num
  · have hm4 : m ≤ 4 := by omega
    rw [Lop_iter_Gam_succ α hα m hm4 θ ⟨h0, h1⟩, abs_mul]
    have hΓnn : 0 ≤ Work.Spaces.Gam α θ := by
      rw [hGam]
      exact Real.rpow_nonneg (mul_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi h0
        (by linarith [h1, Real.pi_pos]))) (sq_nonneg _)) _
    rw [abs_of_nonneg hΓnn]
    have hx : Real.cos θ ^ 2 ∈ Set.Icc 0 1 :=
      ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩
    have := coeff_abs_le m hm4 (Real.cos θ ^ 2) α hx hα hα1
    nlinarith [hΓnn]

/-! ## The weighted squares of `Γ` are integrable -/

/-- On the open interval, `Γ θ² = (sinθ cos²θ)^{2α/3}`. -/
theorem Gam_sq_eq (α θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
  have hpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl,
    pow_two, ← Real.rpow_add hpos (α / 3) (α / 3)]
  congr 1
  ring

/-- On the open interval, `sinθ cos²θ ≤ sin(2θ)`. -/
theorem sin_cos_sq_le_sin_two (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos]))
  have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have h3 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [h2, Real.cos_le_one θ]
  have h4 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left h3 h1
  have h5 : Real.sin θ * Real.cos θ ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; nlinarith
  exact le_trans h4 h5

/-- `Γ²` is continuous on the open interval. -/
private theorem continuousOn_Gam_sq (α : ℝ) :
    ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hpow : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const (fun θ hθ => Or.inl (by
      have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity))
  have hmul : ContinuousOn (fun θ : ℝ => ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))) (Set.Ioo (0 : ℝ) (π / 2)) := hpow.mul hpow
  refine hmul.congr (fun θ _ => ?_)
  show (Work.Spaces.Gam α θ) ^ 2
      = ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
  rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl, pow_two]

/-- `Γ θ² · sin(2θ)^{-η}` is integrable on `Iθ`. -/
theorem Gam_sq_smE_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ := by
  have hsmE : Work.FTS.Nonlinear.RadialProd.smE
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [hIθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.eta := by
    have h1 := Work.Spaces.eta_lt_one
    have h2 := Work.Spaces.eta_pos
    linarith
  have hp2 : 2 * α / 3 - Work.Spaces.eta ≤ 0 := by
    have h1 : 2 * α / 3 ≤ 2 / 3 := by linarith
    have h2 : (2 : ℝ) / 3 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
    linarith
  have hmaj := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.eta) hp1 hp2).1
  have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine ContinuousOn.mul (continuousOn_Gam_sq α) ?_
    rw [hsmE]
    refine ContinuousOn.rpow_const
      (f := fun θ : ℝ => Real.sin (2 * θ)) ?_ (fun θ hθ => Or.inl (ne_of_gt ?_))
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smE θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smE θ) (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo] at h1
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  rw [(MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo).symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])
  have hΓ := Gam_sq_eq α θ hθ
  have hle := sin_cos_sq_le_sin_two θ hθ
  have hnonneg : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos]))
    have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    positivity
  have hnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [hsmE]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hsmE, hΓ]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnonneg hle (by linarith))
          (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta) := by
        rw [← Real.rpow_add hsin]
        ring_nf

/-- `Γ θ² · sin(2θ)^{-γ}` is integrable on `Iθ`. -/
theorem Gam_sq_smG_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
  have hsmG : Work.FTS.Nonlinear.RadialProd.smG α
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [hIθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hγpos : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by
    rw [Work.Spaces.gam]; linarith
  have hmaj := (Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hp1 hp2).1
  have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine ContinuousOn.mul (continuousOn_Gam_sq α) ?_
    rw [hsmG]
    refine ContinuousOn.rpow_const
      (f := fun θ : ℝ => Real.sin (2 * θ)) ?_ (fun θ hθ => Or.inl (ne_of_gt ?_))
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo] at h1
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  rw [(MeasureTheory.Measure.restrict_congr_set (μ := volume) hIoo).symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])
  have hΓ := Gam_sq_eq α θ hθ
  have hle := sin_cos_sq_le_sin_two θ hθ
  have hnonneg : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos]))
    have h2 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    positivity
  have hnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [hsmG]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hsmG, hΓ]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnonneg hle (by linarith))
          (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
        rw [← Real.rpow_add hsin]
        ring_nf

/-- **The angular data of `E1`.** -/
theorem AngGam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[k] (Work.Spaces.Gam α)) θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ) ∧
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ :=
  ⟨Gam_Lop_iter_bound α hα hα1, Gam_sq_smE_integrable α hα hα1,
    Gam_sq_smG_integrable α hα hα1⟩

end Work.FTS.CoercivityFix.Transfer.E1Parts
