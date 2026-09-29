import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.MeasureTheory.Integral

theorem sum_eq_integral_card_filter {d : ℕ} (F : Finset (Fin d → ℤ)) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a) :
    (∑ x ∈ F, g ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖)
      = ∫ t in (0 : ℝ)..(g 0),
          ((F.filter (fun x => t ≤
            g ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖)).card : ℝ) := by
  -- Write `u x` for the norm of the lattice point `x`; the identity is purely about a
  -- nonnegative function `g` of `u x` with `g (u x) ≤ g 0`.
  let u : (Fin d → ℤ) → ℝ := fun x => ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖
  change (∑ x ∈ F, g (u x)) = ∫ t in (0 : ℝ)..(g 0), ((F.filter (fun x => t ≤ g (u x))).card : ℝ)
  -- The single-point identity `g a = ∫_0^{g 0} 1_{[0,a]}` for `0 ≤ a ≤ g 0`.
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ g 0 →
      ∫ t in (0:ℝ)..(g 0), ({s : ℝ | s ≤ a}.indicator (fun _ => (1:ℝ)) t) = a := by
    intro a ha hac
    rw [intervalIntegral.integral_indicator (show a ∈ Set.Icc (0:ℝ) (g 0) from ⟨ha, hac⟩)]
    rw [intervalIntegral.integral_const]
    simp
  -- Interval-integrability of the indicator of `(-∞, a]` on `(0, g 0]`.
  have hInt : ∀ a : ℝ,
      IntervalIntegrable (fun t : ℝ => {s : ℝ | s ≤ a}.indicator (fun _ => (1:ℝ)) t)
        volume (0:ℝ) (g 0) := by
    intro a
    rw [intervalIntegrable_iff]
    refine (integrableOn_const (μ := volume) (s := Set.uIoc (0:ℝ) (g 0))
      (C := (1:ℝ)) ?_).indicator measurableSet_Iic
    have : volume (Set.uIoc (0:ℝ) (g 0)) < ⊤ := by
      change volume (Set.Ioc (min (0:ℝ) (g 0)) (max (0:ℝ) (g 0))) < ⊤
      exact measure_Ioc_lt_top
    exact this.ne
  -- The integrand is the finite sum of the individual indicators.
  have hpoint : ∀ t : ℝ,
      ∑ x ∈ F, ({s : ℝ | s ≤ g (u x)}.indicator (fun _ => (1:ℝ)) t)
        = ((F.filter (fun x => t ≤ g (u x))).card : ℝ) := by
    intro t
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : t ≤ g (u x) <;> simp [h]
  calc (∑ x ∈ F, g (u x))
      = ∑ x ∈ F, ∫ t in (0:ℝ)..(g 0),
          ({s : ℝ | s ≤ g (u x)}.indicator (fun _ => (1:ℝ)) t) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (key (g (u x)) (hpos (u x))
          (hmono 0 (u x) (le_refl 0) (norm_nonneg _))).symm
    _ = ∫ t in (0:ℝ)..(g 0), ∑ x ∈ F,
          ({s : ℝ | s ≤ g (u x)}.indicator (fun _ => (1:ℝ)) t) := by
        exact (intervalIntegral.integral_finsetSum (fun a _ => hInt (g (u a)))).symm
    _ = ∫ t in (0:ℝ)..(g 0), ((F.filter (fun x => t ≤ g (u x))).card : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hpoint t

end Commons.MeasureTheory.Integral