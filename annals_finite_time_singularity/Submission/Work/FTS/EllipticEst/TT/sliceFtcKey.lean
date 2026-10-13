import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set

/-- Fundamental theorem of calculus on the open interval `(0, π/2)`: for a function of class `C¹`
there and `0 < a ≤ b < π/2`, the set integral of `deriv f` over `(a,b)` is `f b - f a`. -/
private lemma slice_ftc_Ioo {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    (∫ t in Set.Ioo a b, deriv f t) = f b - f a := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have h1 : (∫ x in a..b, deriv f x) = f b - f a :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hf.mono hsub) hab
  rw [← h1, intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- Additivity of the set integral of `deriv f` over slices of `(0, π/2)`: for
`0 ≤ a ≤ b ≤ c ≤ π/2`, `∫_{(a,c)} deriv f = ∫_{(a,b)} deriv f + ∫_{(b,c)} deriv f`.  The
integrability of `deriv f` on each of the slices (including the degenerate ones, granted by `hI`)
is what licenses the additivity of the interval integral. -/
private lemma slice_prim_add {f : ℝ → ℝ}
    (hI : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) (hc : c ≤ Real.pi / 2)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ t in Set.Ioo a c, deriv f t)
      = (∫ t in Set.Ioo a b, deriv f t) + (∫ t in Set.Ioo b c, deriv f t) := by
  have hsub_ab : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  have hsub_bc : Set.Ioo b c ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_le_of_lt (le_trans ha hab) hx.1, lt_of_lt_of_le hx.2 hc⟩
  have Iab : IntervalIntegrable (fun t : ℝ => deriv f t) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 (hI a b hsub_ab)
  have Ibc : IntervalIntegrable (fun t : ℝ => deriv f t) MeasureTheory.volume b c :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hbc).2 (hI b c hsub_bc)
  calc (∫ t in Set.Ioo a c, deriv f t)
      = (∫ t in Set.Ioc a c, deriv f t) := MeasureTheory.integral_Ioc_eq_integral_Ioo.symm
    _ = (∫ t in a..c, deriv f t) := (intervalIntegral.integral_of_le (le_trans hab hbc)).symm
    _ = (∫ t in a..b, deriv f t) + (∫ t in b..c, deriv f t) :=
          (intervalIntegral.integral_add_adjacent_intervals Iab Ibc).symm
    _ = (∫ t in Set.Ioc a b, deriv f t) + (∫ t in Set.Ioc b c, deriv f t) := by
          rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hbc]
    _ = (∫ t in Set.Ioo a b, deriv f t) + (∫ t in Set.Ioo b c, deriv f t) := by
          rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
            MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem sliceFtcKey (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hI : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b)) :
    (∃ c : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        f θ - c = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) θ))
          (fun t : ℝ => deriv f t)) ∧
    (∃ c : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        f θ - c = -MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
          (fun t : ℝ => deriv f t)) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  constructor
  · -- the antiderivative is computed from the left end of the interval
    refine ⟨?_, ?_⟩
    · exact f (Real.pi / 4) - (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 4), deriv f t)
    · intro θ hθ
      have hθ0 : 0 < θ := hθ.1
      have hθπ : θ < Real.pi / 2 := hθ.2
      rcases le_total (Real.pi / 4) θ with hle | hlt
      · have hadd := slice_prim_add hI (a := 0) (b := Real.pi / 4) (c := θ)
          le_rfl h4lt.le hθπ.le h4pos.le hle
        have hftc := slice_ftc_Ioo hf (a := Real.pi / 4) (b := θ) h4pos hθπ hle
        rw [hadd, hftc]
        ring
      · have hadd := slice_prim_add hI (a := 0) (b := θ) (c := Real.pi / 4)
          le_rfl hθπ.le h4lt.le hθ0.le hlt
        have hftc := slice_ftc_Ioo hf (a := θ) (b := Real.pi / 4) hθ0 h4lt hlt
        rw [hadd, hftc]
        ring
  · -- the antiderivative is computed from the right end of the interval
    refine ⟨?_, ?_⟩
    · exact f (Real.pi / 4) + (∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), deriv f t)
    · intro θ hθ
      have hθ0 : 0 < θ := hθ.1
      have hθπ : θ < Real.pi / 2 := hθ.2
      rcases le_total (Real.pi / 4) θ with hle | hlt
      · have hadd := slice_prim_add hI (a := Real.pi / 4) (b := θ) (c := Real.pi / 2)
          h4pos.le hθπ.le le_rfl hle hθπ.le
        have hftc := slice_ftc_Ioo hf (a := Real.pi / 4) (b := θ) h4pos hθπ hle
        rw [hadd, hftc]
        ring
      · have hadd := slice_prim_add hI (a := θ) (b := Real.pi / 4) (c := Real.pi / 2)
          hθ0.le h4lt.le le_rfl hlt h4lt.le
        have hftc := slice_ftc_Ioo hf (a := θ) (b := Real.pi / 4) hθ0 h4lt hlt
        rw [hadd, hftc]
        ring

end Work.FTS.EllipticEst.TT
