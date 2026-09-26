import Mathlib
import Submission.Work.BoxShrink.PinchOff.SliceConnected
import Submission.Work.BoxShrink.PinchOff.TangentConfig
import Submission.Work.CountedPinch.Defs
import Submission.Work.CoreTopology.Winding

namespace Work.CountedPinch

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The oscillating curve on the standard torus

The witness for the failure of `FiniteCrossing` at the standard configuration is the loop
`γ t = torusMap 0 (π/6 + osc t)`, where `osc t = |sin (t/2)| * sin (1 / |sin (t/2)|)`.  The
function `osc` is `2π`-periodic, continuous, and vanishes at the infinitely many parameters
`t k = 2 * arcsin (1 / ((k+1) π))`, which accumulate at `0`; at those parameters `γ` hits the
point `torusMap 0 (π/6)`, whose third coordinate is `sin (π/6) = 1/2`.  The function also takes
both signs, so the loop visits both sides of the plane `{z = 1/2}`. -/

/-- `u ↦ u sin(1/u)` is continuous, with the value `0` at `u = 0`. -/
private lemma continuous_mul_sin_inv : Continuous (fun u : ℝ => u * Real.sin (1 / u)) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  rcases eq_or_ne u₀ 0 with rfl | hu₀
  · rw [ContinuousAt]
    have h0 : (0 : ℝ) * Real.sin (1 / 0) = 0 := by simp
    rw [h0]
    refine squeeze_zero_norm (f := fun u : ℝ => u * Real.sin (1 / u))
      (a := fun u => ‖u‖) (fun u => ?_) ?_
    · rw [norm_mul]
      have h1 : ‖Real.sin (1 / u)‖ ≤ 1 := by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
      nlinarith [norm_nonneg u]
    · simpa using (continuous_norm.tendsto (0 : ℝ))
  · have hsin : ContinuousAt (fun u : ℝ => Real.sin (1 / u)) u₀ := by
      have : ContinuousAt (fun u : ℝ => Real.sin (u⁻¹)) u₀ :=
        Real.continuous_sin.continuousAt.comp (continuousAt_inv₀ hu₀)
      simpa [one_div] using this
    exact continuousAt_id.mul hsin

/-- The oscillating perturbation `osc t = |sin (t/2)| * sin (1 / |sin (t/2)|)`. -/
private def osc (t : ℝ) : ℝ := |Real.sin (t / 2)| * Real.sin (1 / |Real.sin (t / 2)|)

private lemma continuous_osc : Continuous osc := by
  unfold osc
  exact continuous_mul_sin_inv.comp ((Real.continuous_sin.comp (continuous_id.div_const 2)).abs)

private lemma osc_periodic (t : ℝ) : osc (t + 2 * Real.pi) = osc t := by
  unfold osc
  have h : (t + 2 * Real.pi) / 2 = t / 2 + Real.pi := by ring
  rw [h, Real.sin_add_pi, abs_neg]

private lemma osc_two_mul_arcsin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    osc (2 * Real.arcsin x) = x * Real.sin (1 / x) := by
  unfold osc
  have h2 : (2 * Real.arcsin x) / 2 = Real.arcsin x := by ring
  rw [h2, Real.sin_arcsin (by linarith) hx1, abs_of_nonneg hx0]

private lemma one_div_pos_le_one (m : ℕ) :
    (0 : ℝ) < 1 / (((m : ℝ) + 1) * Real.pi) ∧ 1 / (((m : ℝ) + 1) * Real.pi) ≤ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < ((m : ℝ) + 1) * Real.pi := mul_pos hm hpi
  refine ⟨div_pos one_pos hpos, ?_⟩
  rw [div_le_one hpos]
  nlinarith [Real.pi_gt_three, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- `osc` vanishes at the accumulating sequence `2 * arcsin (1/((k+1) π))`. -/
private lemma osc_series (k : ℕ) :
    osc (2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi))) = 0 := by
  obtain ⟨hx0, hx1⟩ := one_div_pos_le_one k
  rw [osc_two_mul_arcsin hx0.le hx1]
  have hx : 1 / (1 / (((k : ℝ) + 1) * Real.pi)) = ((k : ℝ) + 1) * Real.pi := by
    rw [one_div, one_div, inv_inv]
  rw [hx]
  have : Real.sin (((k : ℝ) + 1) * Real.pi) = 0 := by
    have h := Real.sin_nat_mul_pi (k + 1)
    simpa using h
  rw [this, mul_zero]

private lemma osc_upper : osc (2 * Real.arcsin ((2 : ℝ) / Real.pi)) = 2 / Real.pi := by
  rw [osc_two_mul_arcsin (by positivity)
    (by rw [div_le_one Real.pi_pos]; nlinarith [Real.pi_gt_three])]
  have h : 1 / ((2 : ℝ) / Real.pi) = Real.pi / 2 := by field_simp
  rw [h, Real.sin_pi_div_two, mul_one]

private lemma osc_lower : osc (2 * Real.arcsin ((2 : ℝ) / (3 * Real.pi))) =
    -(2 / (3 * Real.pi)) := by
  rw [osc_two_mul_arcsin (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three])]
  have h : 1 / ((2 : ℝ) / (3 * Real.pi)) = 3 * Real.pi / 2 := by field_simp
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    have h' : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [h', Real.sin_add_pi, Real.sin_pi_div_two]
  rw [h, hsin]
  ring

/-! ## The standard torus lies in the box `PBox 4 0 σ` -/

private lemma torusMap_coord_zero (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) (0 : Fin 3) = (2 + Real.cos φ) * Real.cos θ := by
  simp [Work.Core.torusMap]

private lemma torusMap_coord_one (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) (1 : Fin 3) = (2 + Real.cos φ) * Real.sin θ := by
  simp [Work.Core.torusMap]

private lemma torusMap_coord_two (θ φ : ℝ) :
    (Work.Core.torusMap θ φ) (2 : Fin 3) = Real.sin φ := by
  simp [Work.Core.torusMap]

/-- Every coordinate of a point of the standard torus has absolute value at most `3`. -/
private lemma abs_torusMap_apply_le_three (θ φ : ℝ) (i : Fin 3) :
    |(Work.Core.torusMap θ φ) i| ≤ 3 := by
  fin_cases i
  · show |(Work.Core.torusMap θ φ) (0 : Fin 3)| ≤ 3
    rw [torusMap_coord_zero]
    have hc : |2 + Real.cos φ| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith [Real.neg_one_le_cos φ, Real.cos_le_one φ]
    calc |(2 + Real.cos φ) * Real.cos θ| = |2 + Real.cos φ| * |Real.cos θ| := abs_mul _ _
      _ ≤ 3 * 1 := mul_le_mul hc (by
            rw [abs_le]
            exact ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩) (abs_nonneg _) (by norm_num)
      _ = 3 := by ring
  · show |(Work.Core.torusMap θ φ) (1 : Fin 3)| ≤ 3
    rw [torusMap_coord_one]
    have hc : |2 + Real.cos φ| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith [Real.neg_one_le_cos φ, Real.cos_le_one φ]
    calc |(2 + Real.cos φ) * Real.sin θ| = |2 + Real.cos φ| * |Real.sin θ| := abs_mul _ _
      _ ≤ 3 * 1 := mul_le_mul hc (Real.abs_sin_le_one θ) (abs_nonneg _) (by norm_num)
      _ = 3 := by ring
  · show |(Work.Core.torusMap θ φ) (2 : Fin 3)| ≤ 3
    rw [torusMap_coord_two]; nlinarith [Real.abs_sin_le_one φ]

/-- The standard torus is contained in `PBox 4 0 σ` for every coordinate permutation `σ`. -/
private lemma torusMap_mem_PBox_four (θ φ : ℝ) (σ : Equiv.Perm (Fin 3)) :
    Work.Core.torusMap θ φ ∈ Submission.PBox 4 (0 : R3) σ := by
  rw [Submission.mem_PBox]
  intro i
  have h3 : |(Work.Core.torusMap θ φ) (σ i)| ≤ 3 := abs_torusMap_apply_le_three θ φ (σ i)
  have hb : (1 : ℝ) ≤ Submission.boxSide i := Submission.one_le_boxSide i
  have hz : (0 : R3) (σ i) = 0 := by simp
  rw [hz, sub_zero]
  nlinarith

/-! ## Two trigonometric inequalities -/

private lemma sin_pi_div_six_sub_lt_half :
    Real.sin (Real.pi / 6 - 2 / (3 * Real.pi)) < (1 : ℝ) / 2 := by
  rw [← Real.sin_pi_div_six]
  have hpos : (0 : ℝ) < 2 / (3 * Real.pi) := by positivity
  have hlt : (2 : ℝ) / (3 * Real.pi) < Real.pi / 6 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi)]; nlinarith [Real.pi_gt_three]
  refine Real.strictMonoOn_sin.lt_iff_lt
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ |>.mpr ?_
  linarith

private lemma half_lt_sin_pi_div_six_add :
    (1 : ℝ) / 2 < Real.sin (Real.pi / 6 + 2 / Real.pi) := by
  rw [← Real.sin_pi_div_six]
  have h2 : (0 : ℝ) < 2 / Real.pi := by positivity
  have h : (2 : ℝ) / Real.pi < Real.pi / 3 := by
    rw [div_lt_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  refine Real.strictMonoOn_sin.lt_iff_lt
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith⟩ |>.mpr ?_
  linarith

/-! ## The witnessing curve -/

/-- The witnessing loop `γ t = torusMap 0 (π/6 + osc t)`. -/
private def gammaFun (t : ℝ) : R3 := Work.Core.torusMap 0 (Real.pi / 6 + osc t)

private lemma continuous_gammaFun : Continuous gammaFun := by
  have hpair : Continuous (fun t : ℝ => ((0 : ℝ), Real.pi / 6 + osc t)) :=
    continuous_const.prodMk (continuous_const.add continuous_osc)
  have h := Work.CoreTopology.torusMap_continuous.comp hpair
  exact h

private lemma gammaFun_periodic (t : ℝ) : gammaFun (t + 2 * Real.pi) = gammaFun t := by
  simp only [gammaFun]
  rw [osc_periodic]

private lemma gammaFun_apply_two (t : ℝ) :
    (gammaFun t) (2 : Fin 3) = Real.sin (Real.pi / 6 + osc t) := by
  rw [gammaFun, torusMap_coord_two]

private lemma gammaFun_mem (t : ℝ) :
    gammaFun t ∈ (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo).carrier := by
  rw [Work.Smooth.Morse.torus_carrier]
  exact ⟨(0, Real.pi / 6 + osc t), rfl⟩

/-- The hypothesis `FiniteCrossing` of the sibling chapter `Work.BoxShrink.PinchOff` is FALSE at a
concrete configuration of the standard torus: take the standard torus (`ψ` the identity
diffeomorphism), the box `PBox 4 0 (refl (Fin 3))` (with half-lengths `4, 4 * 2^(1/3), 4 * 2^(2/3)`,
which contains the whole torus: `|x| ≤ 3 < 4`, `|y| ≤ 3`, `|z| ≤ 1`), and the cutting plane
`{z = 1/2}` (`σ = refl`, `u = 1/2`), which is transverse to the surface (`planeG = sin (second
parameter) - 1/2` has gradient `(0, cos)`, nowhere zero on the slice `{sin = 1/2}`).

The witnessing loop is `γ t = torusMap 0 (π/6 + osc t)` where `osc` is the continuous `2π`-periodic
function `osc t = |sin (t/2)| * sin (1 / |sin (t/2)|)` (with `osc 0 = 0`); its image lies in the box
region, it visits both sides of the plane, and it meets the slice at the infinitely many parameters
`t = 2 * arcsin (1 / (k * π))` with `k ≥ 1`, all in `[0, 2 * π]`.

Hence the sibling's reduction theorems whose hypothesis is the global statement
`∀ ψ s c σ u, TransverseSlice ψ s c σ u → IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u`
(`Work.BoxShrink.PinchOff.dropCase_of_finiteCrossing_of_isPathConnected_slice`,
`…keyTameClosed_of_finiteCrossing_of_isPathConnected_slice`,
`…bubbleHalf_of_finiteCrossing_of_isPathConnected_slice`) are **vacuous**, as is the engine-based
assembly of `Work.CountedPinch.Arcs`, which carries the same hypothesis. -/
theorem not_finiteCrossing_std :
    ¬ Work.BoxShrink.PinchOff.FiniteCrossing Work.BoxShrink.PinchOff.idDiffeo 4
        (0 : LeanEval.KnotTheory.PardonDistortion.R3) (Equiv.refl (Fin 3)) (1 / 2) := by
  intro hFC
  let γ : Work.CoreTopology.ClosedCurve
      (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) :=
    { γ := gammaFun
      cont := continuous_gammaFun
      periodic := gammaFun_periodic
      mem := gammaFun_mem }
  have hOmega : ∀ t : ℝ,
      γ t ∈ Work.BoxShrink.PinchOff.Omega Work.BoxShrink.PinchOff.idDiffeo 4 (0 : R3)
        (Equiv.refl (Fin 3)) := by
    intro t
    rw [Work.BoxShrink.PinchOff.Omega, Work.BoxShrink.Core.mem_boxRegion]
    exact ⟨γ.mem t,
      torusMap_mem_PBox_four 0 (Real.pi / 6 + osc t) (Equiv.refl (Fin 3))⟩
  have ht₁ : ∃ t₁ : ℝ, γ t₁ ∉ Work.BoxShrink.PinchOff.UpperSide Work.BoxShrink.PinchOff.idDiffeo 4
      (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) := by
    refine ⟨2 * Real.arcsin (2 / (3 * Real.pi)), ?_⟩
    intro hmem
    rw [Work.BoxShrink.PinchOff.UpperSide, Set.mem_inter_iff] at hmem
    have h2 : (1 : ℝ) / 2 ≤ (γ (2 * Real.arcsin (2 / (3 * Real.pi)))) (2 : Fin 3) := by
      simpa using hmem.2
    have hval : (γ (2 * Real.arcsin (2 / (3 * Real.pi)))) (2 : Fin 3) =
        Real.sin (Real.pi / 6 - 2 / (3 * Real.pi)) := by
      show (gammaFun (2 * Real.arcsin (2 / (3 * Real.pi)))) (2 : Fin 3) =
        Real.sin (Real.pi / 6 - 2 / (3 * Real.pi))
      rw [gammaFun_apply_two, osc_lower]
      ring_nf
    rw [hval] at h2
    linarith [sin_pi_div_six_sub_lt_half]
  have ht₂ : ∃ t₂ : ℝ, γ t₂ ∉ Work.BoxShrink.PinchOff.LowerSide Work.BoxShrink.PinchOff.idDiffeo 4
      (0 : R3) (Equiv.refl (Fin 3)) (1 / 2) := by
    refine ⟨2 * Real.arcsin (2 / Real.pi), ?_⟩
    intro hmem
    rw [Work.BoxShrink.PinchOff.LowerSide, Set.mem_inter_iff] at hmem
    have h2 : (γ (2 * Real.arcsin (2 / Real.pi))) (2 : Fin 3) ≤ (1 : ℝ) / 2 := by
      simpa using hmem.2
    have hval : (γ (2 * Real.arcsin (2 / Real.pi))) (2 : Fin 3) =
        Real.sin (Real.pi / 6 + 2 / Real.pi) := by
      show (gammaFun (2 * Real.arcsin (2 / Real.pi))) (2 : Fin 3) =
        Real.sin (Real.pi / 6 + 2 / Real.pi)
      rw [gammaFun_apply_two, osc_upper]
    rw [hval] at h2
    linarith [half_lt_sin_pi_div_six_add]
  have hcross := hFC γ hOmega ht₁ ht₂
  have hinf : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
      γ t ∈ Work.BoxShrink.PinchOff.Sigma Work.BoxShrink.PinchOff.idDiffeo 4 (0 : R3)
        (Equiv.refl (Fin 3)) (1 / 2)}.Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => 2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi)))
    · intro a b hab
      have harc : Real.arcsin (1 / (((a : ℝ) + 1) * Real.pi))
          = Real.arcsin (1 / (((b : ℝ) + 1) * Real.pi)) := by linarith
      have hx : 1 / (((a : ℝ) + 1) * Real.pi) = 1 / (((b : ℝ) + 1) * Real.pi) :=
        (Real.arcsin_inj (by have := (one_div_pos_le_one a).1; linarith)
          (one_div_pos_le_one a).2
          (by have := (one_div_pos_le_one b).1; linarith)
          (one_div_pos_le_one b).2).mp harc
      have hx' : ((a : ℝ) + 1) * Real.pi = ((b : ℝ) + 1) * Real.pi := by
        have := hx
        rwa [one_div, one_div, inv_inj] at this
      have hc : (a : ℝ) = (b : ℝ) := by
        have h := mul_right_cancel₀ Real.pi_ne_zero hx'
        linarith
      exact Nat.cast_injective hc
    · intro k
      obtain ⟨hx0, hx1⟩ := one_div_pos_le_one k
      have hxlt : 1 / (((k : ℝ) + 1) * Real.pi) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < ((k : ℝ) + 1) * Real.pi)]
        nlinarith [Real.pi_gt_three, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
      constructor
      · constructor
        · have := Real.arcsin_nonneg.mpr hx0.le; linarith
        · have hlt : Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi)) < Real.pi / 2 :=
            Real.arcsin_lt_pi_div_two.mpr hxlt
          linarith [Real.pi_pos]
      · have hthird : γ (2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi))) (2 : Fin 3) = 1 / 2 := by
          show (gammaFun (2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi)))) (2 : Fin 3) = 1 / 2
          rw [gammaFun_apply_two, osc_series k, add_zero, Real.sin_pi_div_six]
        show γ (2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi))) ∈
          Work.BoxShrink.Core.sliceRegion
            (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo) 4 (0 : R3)
            (Equiv.refl (Fin 3)) (1 / 2)
        rw [Work.BoxShrink.Core.mem_sliceRegion]
        refine ⟨γ.mem _, ?_, ?_⟩
        · exact torusMap_mem_PBox_four 0 (Real.pi / 6 + osc (2 * Real.arcsin (1 / (((k : ℝ) + 1) * Real.pi))))
            (Equiv.refl (Fin 3))
        · simpa using hthird
  exact hinf hcross

end

end Work.CountedPinch
