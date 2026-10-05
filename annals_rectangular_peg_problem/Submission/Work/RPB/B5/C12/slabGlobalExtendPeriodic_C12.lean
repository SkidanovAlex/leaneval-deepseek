import Mathlib
import Submission.Work.RPB.B5.slabGlobalExtendPeriodic

/-!
# Order-`12` version of the global periodic slab extension

This is the order-`12` upgrade of `Work.RPB.B5.slabGlobalExtendPeriodic`.  We are given a
function `S : ℝ → ℝ → ℝ → ℝ` which is `C^12` on the open slab `(-1,2) × ℝ × (-ρ₀,ρ₀)`,
periodic in `t` with period `2π`, and vanishing on `ρ = 0` for `τ ∈ [0,1]`.  We produce a
globally `C^12` function `S'` which is again `2π`-periodic in `t`, vanishes on `ρ = 0`
everywhere, and agrees with `S` on the strip `[0,1] × ℝ × (-ρ₀/2, ρ₀/2)`.

The construction is identical to the order-`8` case: `S' = Θ - Θ(·,·,0)` where
`Θ = θ(τ)·ψ(ρ)·S`, with `θ`, `ψ` the smooth cut-offs of `Work.RPB.B5` (equal to `1` near the
region of interest and to `0` near the boundary of the slab; they are smooth to all orders,
so the numerical value `8` is irrelevant).  Since the support of `θψ` is a compact subset of
the open slab, `Θ` is globally `C^12`; subtracting its trace at `ρ = 0` gives the required
vanishing without changing the agreement with `S` on the strip (where `S(·,·,0) = 0`).
-/

namespace Work.RPB.B5.C12

open scoped ContDiff

noncomputable section

/-- The order-`12` upgrade of `Work.RPB.B5.theta_contDiff`. -/
theorem theta_contDiff_12 : ContDiff ℝ 12 Work.RPB.B5.theta := by
  unfold Work.RPB.B5.theta; fun_prop

/-- The order-`12` upgrade of `Work.RPB.B5.psi_contDiff`. -/
theorem psi_contDiff_12 (ρ₀ : ℝ) : ContDiff ℝ 12 (Work.RPB.B5.psi ρ₀) := by
  unfold Work.RPB.B5.psi; fun_prop

/-- `Θ` is globally `C^12`: it is a product of smooth cut-offs with `S`, and the cut-offs are
supported in a compact subset of the open slab where `S` is `C^12`; where the cut-offs vanish,
`Θ` is locally zero.  This is the order-`12` version of `Work.RPB.B5.Theta_contDiff`. -/
theorem Theta_contDiff_12 (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀)) :
    ContDiff ℝ 12 (Work.RPB.B5.Theta S ρ₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h1 : z.1 < -3 / 4
  · have hmem : {w : ℝ × (ℝ × ℝ) | w.1 < -3 / 4} ∈ nhds z :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds h1
    have hev : Work.RPB.B5.Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with w hw
      simp only [Work.RPB.B5.Theta]
      rw [Work.RPB.B5.theta_eq_zero_of_le hw.le, zero_mul, zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · by_cases h2 : 7 / 4 < z.1
    · have hmem : {w : ℝ × (ℝ × ℝ) | 7 / 4 < w.1} ∈ nhds z :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds h2
      have hev : Work.RPB.B5.Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with w hw
        simp only [Work.RPB.B5.Theta]
        rw [Work.RPB.B5.theta_eq_zero_of_ge hw.le, zero_mul, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    · by_cases h3 : z.2.2 < -7 * ρ₀ / 8
      · have hmem : {w : ℝ × (ℝ × ℝ) | w.2.2 < -7 * ρ₀ / 8} ∈ nhds z :=
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds h3
        have hev : Work.RPB.B5.Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
          filter_upwards [hmem] with w hw
          simp only [Work.RPB.B5.Theta]
          rw [Work.RPB.B5.psi_eq_zero_of_le hρ₀ hw.le, mul_zero, zero_mul]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
      · by_cases h4 : 7 * ρ₀ / 8 < z.2.2
        · have hmem : {w : ℝ × (ℝ × ℝ) | 7 * ρ₀ / 8 < w.2.2} ∈ nhds z :=
            (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds h4
          have hev : Work.RPB.B5.Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
            filter_upwards [hmem] with w hw
            simp only [Work.RPB.B5.Theta]
            rw [Work.RPB.B5.psi_eq_zero_of_ge hρ₀ hw.le, mul_zero, zero_mul]
          exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
        · have h1' : -3 / 4 ≤ z.1 := not_lt.mp h1
          have h2' : z.1 ≤ 7 / 4 := not_lt.mp h2
          have h3' : -7 * ρ₀ / 8 ≤ z.2.2 := not_lt.mp h3
          have h4' : z.2.2 ≤ 7 * ρ₀ / 8 := not_lt.mp h4
          have hzmem : z ∈ (Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ)
              ×ˢ Set.Ioo (-ρ₀) ρ₀ := by
            simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_univ, true_and]
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hρ₀]
          have hS' : ContDiffAt ℝ 12 (fun w : ℝ × (ℝ × ℝ) => S w.1 w.2.1 w.2.2) z :=
            hS.contDiffAt ((Work.RPB.B5.isOpen_slab ρ₀).mem_nhds hzmem)
          have hθ : ContDiffAt ℝ 12 (fun w : ℝ × (ℝ × ℝ) => Work.RPB.B5.theta w.1) z :=
            (theta_contDiff_12.comp contDiff_fst).contDiffAt
          have hψ : ContDiffAt ℝ 12 (fun w : ℝ × (ℝ × ℝ) => Work.RPB.B5.psi ρ₀ w.2.2) z :=
            ((psi_contDiff_12 ρ₀).comp contDiff_snd.snd).contDiffAt
          show ContDiffAt ℝ 12 (fun x : ℝ × (ℝ × ℝ) =>
            Work.RPB.B5.theta x.1 * Work.RPB.B5.psi ρ₀ x.2.2 * S x.1 x.2.1 x.2.2) z
          exact (hθ.mul hψ).mul hS'

theorem slabGlobalExtendPeriodic_C12 (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, S τ t 0 = 0) :
    ∃ S' : ℝ → ℝ → ℝ → ℝ,
      ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => S' z.1 z.2.1 z.2.2) ∧
      (∀ τ t ρ, S' τ (t + 2 * Real.pi) ρ = S' τ t ρ) ∧
      (∀ τ t, S' τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t ρ, |ρ| < ρ₀ / 2 → S' τ t ρ = S τ t ρ) := by
  refine ⟨fun τ t ρ => Work.RPB.B5.Theta S ρ₀ (τ, (t, ρ))
      - Work.RPB.B5.Theta S ρ₀ (τ, (t, 0)), ?_, ?_, ?_, ?_⟩
  · exact (Theta_contDiff_12 S ρ₀ hρ₀ hS).sub
      ((Theta_contDiff_12 S ρ₀ hρ₀ hS).comp (by fun_prop))
  · intro τ t ρ
    have hper' : ∀ τ t ρ,
        Work.RPB.B5.Theta S ρ₀ (τ, (t + 2 * Real.pi, ρ)) = Work.RPB.B5.Theta S ρ₀ (τ, (t, ρ)) := by
      intro τ t ρ
      simp only [Work.RPB.B5.Theta]
      rw [hper τ t ρ]
    show Work.RPB.B5.Theta S ρ₀ (τ, (t + 2 * Real.pi, ρ))
          - Work.RPB.B5.Theta S ρ₀ (τ, (t + 2 * Real.pi, 0))
        = Work.RPB.B5.Theta S ρ₀ (τ, (t, ρ)) - Work.RPB.B5.Theta S ρ₀ (τ, (t, 0))
    rw [hper' τ t ρ, hper' τ t 0]
  · intro τ t
    show Work.RPB.B5.Theta S ρ₀ (τ, (t, 0)) - Work.RPB.B5.Theta S ρ₀ (τ, (t, 0)) = 0
    rw [sub_self]
  · intro τ hτ t ρ hρ
    have hψ : Work.RPB.B5.psi ρ₀ ρ = 1 := by
      apply Work.RPB.B5.psi_eq_one hρ₀
      rw [abs_lt] at hρ
      exact ⟨by linarith [hρ₀, hρ.1], by linarith [hρ₀, hρ.2]⟩
    show Work.RPB.B5.Theta S ρ₀ (τ, (t, ρ)) - Work.RPB.B5.Theta S ρ₀ (τ, (t, 0)) = S τ t ρ
    have h1 : Work.RPB.B5.Theta S ρ₀ (τ, (t, ρ)) = S τ t ρ := by
      simp only [Work.RPB.B5.Theta, Work.RPB.B5.theta_eq_one hτ, hψ, one_mul]
    have h2 : Work.RPB.B5.Theta S ρ₀ (τ, (t, 0)) = 0 := by
      simp only [Work.RPB.B5.Theta, Work.RPB.B5.theta_eq_one hτ]
      rw [h0 τ hτ t, mul_zero]
    rw [h1, h2, sub_zero]

end

end Work.RPB.B5.C12
