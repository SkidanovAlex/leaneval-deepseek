import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.Angular

open MeasureTheory

/-- Mean value inequality for `g²` on `[0,π/2]`: if `g²` is integrable on `Iθ`, then at some
point `t` of the *open* interval the value `g t ^ 2` is at most the average of `g ^ 2`,
i.e. `2 * g t ^ 2 ≤ (4/π) ∫_{Iθ} g ^ 2`.

The proof is by contradiction: if `g ^ 2 > A / (π/2)` everywhere on `(0, π/2)`, where `A` is
the integral of `g ^ 2` over `[0, π/2]`, then `g ^ 2 - A / (π/2)` is a nonnegative function,
positive on the whole open interval, so its integral over `(0, π/2)` is strictly positive;
but the same integral over `[0, π/2]` equals `A - (A / (π/2)) * (π/2) = 0`. -/
theorem meanValue {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      2 * g t ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2) := by
  by_contra h
  simp only [Work.Spaces.Iθ] at h
  set A : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 with hA
  -- if the claim failed, `g ^ 2` exceeds the average `A / (π/2)` everywhere on `(0, π/2)`
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), A / (Real.pi / 2) < g t ^ 2 := by
    intro t ht
    have h1 : (4 / Real.pi) * A < 2 * g t ^ 2 := by
      by_contra hc
      exact h ⟨t, ht, not_lt.mp hc⟩
    have h2 : ((4 / Real.pi) * A) / 2 < g t ^ 2 := by linarith
    have h3 : A / (Real.pi / 2) = ((4 / Real.pi) * A) / 2 := by ring
    linarith
  have hIntG_Icc : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hint
  have hIntG_Ioo : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hIntG_Icc.mono_set Set.Ioo_subset_Icc_self
  have hIntC_Ioo : MeasureTheory.IntegrableOn (fun _ : ℝ => A / (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_const (μ := volume) (s := Set.Ioo 0 (Real.pi / 2)) (C := A / (Real.pi / 2))
      measure_Ioo_lt_top.ne (by simp)
  have hIntF_Ioo : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 - A / (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hIntG_Ioo.sub hIntC_Ioo
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (0 : ℝ) ≤ (fun θ => g θ ^ 2 - A / (Real.pi / 2)) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    have := hpos t ht
    linarith
  have hnonneg : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ => g θ ^ 2 - A / (Real.pi / 2)) := hnn
  have hsupp : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆
      Function.support (fun θ => g θ ^ 2 - A / (Real.pi / 2)) := by
    intro t ht
    rw [Function.mem_support]
    exact ne_of_gt (by have := hpos t ht; linarith)
  have hIntPos : 0 < ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hIntF_Ioo]
    have hset : Function.support (fun θ => g θ ^ 2 - A / (Real.pi / 2)) ∩
        Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) :=
      Set.inter_eq_right.mpr hsupp
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  have hIntPosIcc : 0 < ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact hIntPos
  have hvol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    have h1 : MeasureTheory.volume (Set.Icc (0 : ℝ) (Real.pi / 2)) = ENNReal.ofReal (Real.pi / 2) := by
      rw [Real.volume_Icc, sub_zero]
    rw [MeasureTheory.Measure.real, h1, ENNReal.toReal_ofReal (by positivity)]
  have hfirst : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2) = A := hA.symm
  have hIntC_Icc : MeasureTheory.IntegrableOn (fun _ : ℝ => A / (Real.pi / 2))
      (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_const (μ := volume) (s := Set.Icc 0 (Real.pi / 2)) (C := A / (Real.pi / 2))
      measure_Icc_lt_top.ne (by simp)
  have hzero : ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) = 0 := by
    rw [MeasureTheory.integral_sub hIntG_Icc hIntC_Icc, MeasureTheory.setIntegral_const, smul_eq_mul,
      hvol, hfirst, mul_div_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0), sub_self]
  linarith [hIntPosIcc, hzero]

end Work.FTS_RXTPieces.Angular
