import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Defs
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Temps
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2` — the two endpoint representations

At the left end we use a point `ξ ∈ (0, θ)` so close to `0` that `|G ξ| ≤ ε` (possible because
`|G ξ| ≤ C₁ · sin ξ cos²ξ / 2 ≤ C₁ ξ / 2`); the two-point bound then gives
`|G θ| ≤ ε + ∫_ξ^θ gwt ≤ ε + ∫_0^θ gwt`.  At the right end we use `ξ ∈ (θ, π/2)` with
`π/2 - ξ` so small that `|G ξ| ≤ ε` and conclude `|G θ| ≤ ε + ∫_θ^{π/2} gwt`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Left representation**: for `θ ∈ (0, π/4]`, `|G θ| ≤ ∫_0^θ gwt A C`. -/
lemma left_rep {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |wfun θ * u1fun u z θ| ≤ ∫ t in (0 : ℝ)..θ, gwt A C t := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hC₁1 : 0 < C₁ + 1 := by linarith
  set ξ : ℝ := min (θ / 2) (ε / (C₁ + 1)) with hξdef
  have hξpos : 0 < ξ := by
    rw [hξdef]; exact lt_min (by linarith) (div_pos hε hC₁1)
  have hξlt : ξ < θ := by
    rw [hξdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hξε : ξ ≤ ε / (C₁ + 1) := by rw [hξdef]; exact min_le_right _ _
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hξpos, lt_trans hξlt hθlt⟩
  have hcr := crude_G (u := u) (H := H) (z := z) hC₁ hcrude hξmem
  have hle : wfun ξ / Real.sin (2 * ξ) ≤ ξ / 2 := Wdiv_le_theta hξmem
  have hsmall : |wfun ξ * u1fun u z ξ| ≤ ε := by
    have h1 : C₁ * (wfun ξ / Real.sin (2 * ξ)) ≤ C₁ * (ξ / 2) :=
      mul_le_mul_of_nonneg_left hle hC₁
    have h2 : C₁ * (ξ / 2) ≤ ε := by
      have h3 : ξ / 2 ≤ ε / (C₁ + 1) / 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      have h5 : C₁ * (ε / (C₁ + 1) / 2) ≤ ε := by
        have h6 : C₁ / (C₁ + 1) ≤ 1 := by rw [div_le_one hC₁1]; linarith
        have h7 : C₁ * (ε / (C₁ + 1) / 2) = (C₁ / (C₁ + 1)) * (ε / 2) := by
          field_simp
          try ring
        rw [h7]
        calc (C₁ / (C₁ + 1)) * (ε / 2) ≤ 1 * ε :=
              mul_le_mul h6 (by linarith [hε]) (by positivity) (by norm_num)
          _ = ε := one_mul ε
      linarith
    linarith
  have htp := two_point (u := u) (H := H) (z := z) (A := A) (C := C) hode hH hξpos
    (le_of_lt hξlt) hθlt
  have htri : |wfun θ * u1fun u z θ| ≤ ε + ∫ t in ξ..θ, gwt A C t := by
    have h1 : |wfun θ * u1fun u z θ| ≤
        |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| + |wfun ξ * u1fun u z ξ| := by
      have := abs_add_le (wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ)
        (wfun ξ * u1fun u z ξ)
      simpa only [sub_add_cancel] using this
    linarith
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..ξ, gwt A C t := by
    refine intervalIntegral.integral_nonneg (le_of_lt hξpos) (fun u' hu' => ?_)
    exact gwt_nonneg_Icc hA hC ⟨hu'.1, le_trans hu'.2 (le_of_lt (lt_trans hξlt hθlt))⟩
  have hadd : (∫ t in (0 : ℝ)..ξ, gwt A C t) + ∫ t in ξ..θ, gwt A C t
      = ∫ t in (0 : ℝ)..θ, gwt A C t :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_gwt A C).intervalIntegrable 0 ξ)
      ((continuous_gwt A C).intervalIntegrable ξ θ)
  linarith

/-- **Right representation**: for `θ ∈ [π/4, π/2)`, `|G θ| ≤ ∫_θ^{π/2} gwt A C`. -/
lemma right_rep {u H : ℝ → ℝ → ℝ} {z A C C₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (u1fun u z)
        (H z θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * u1fun u z θ) θ)
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |H z θ| ≤ A / Real.sin (2 * θ) + C)
    (hcrude : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.sin (2 * θ) * u1fun u z θ| ≤ C₁)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |wfun θ * u1fun u z θ| ≤ ∫ t in θ..(Real.pi / 2), gwt A C t := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hθpos : 0 < θ := by linarith [hθ.1, Real.pi_pos]
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hC₁1 : 0 < C₁ + 1 := by linarith
  have harg : 0 < 2 * ε / (C₁ + 1) := by positivity
  have hs : 0 < Real.sqrt (2 * ε / (C₁ + 1)) := Real.sqrt_pos.mpr harg
  set d : ℝ := min ((Real.pi / 2 - θ) / 2) (Real.sqrt (2 * ε / (C₁ + 1))) with hddef
  have hdpos : 0 < d := by rw [hddef]; exact lt_min (by linarith) hs
  have hdle : d ≤ (Real.pi / 2 - θ) / 2 := by rw [hddef]; exact min_le_left _ _
  have hdlt : d < Real.pi / 2 - θ := lt_of_le_of_lt hdle (by linarith)
  have hd2 : d ^ 2 ≤ 2 * ε / (C₁ + 1) := by
    have h := min_le_right ((Real.pi / 2 - θ) / 2) (Real.sqrt (2 * ε / (C₁ + 1)))
    rw [← hddef] at h
    have h' := mul_self_le_mul_self (le_of_lt hdpos) h
    rw [Real.mul_self_sqrt (le_of_lt harg)] at h'
    simpa [pow_two] using h'
  set ξ : ℝ := Real.pi / 2 - d with hξdef
  have hξgt : θ < ξ := by rw [hξdef]; linarith
  have hξlt : ξ < Real.pi / 2 := by rw [hξdef]; linarith
  have hξpos : 0 < ξ := lt_trans hθpos hξgt
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hξpos, hξlt⟩
  have hπξ : Real.pi / 2 - ξ = d := by rw [hξdef]; ring
  have hcr := crude_G (u := u) (H := H) (z := z) hC₁ hcrude hξmem
  have hle : wfun ξ / Real.sin (2 * ξ) ≤ (Real.pi / 2 - ξ) ^ 2 / 2 :=
    Wdiv_le_right ⟨le_trans hθ.1 (le_of_lt hξgt), hξlt⟩
  have hsmall : |wfun ξ * u1fun u z ξ| ≤ ε := by
    have h1 : C₁ * (wfun ξ / Real.sin (2 * ξ)) ≤ C₁ * ((Real.pi / 2 - ξ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hle hC₁
    have h2 : C₁ * ((Real.pi / 2 - ξ) ^ 2 / 2) ≤ ε := by
      rw [hπξ]
      have h3 : d ^ 2 / 2 ≤ (2 * ε / (C₁ + 1)) / 2 := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      have h5 : C₁ * ((2 * ε / (C₁ + 1)) / 2) ≤ ε := by
        have h6 : C₁ / (C₁ + 1) ≤ 1 := by rw [div_le_one hC₁1]; linarith
        have h7 : C₁ * ((2 * ε / (C₁ + 1)) / 2) = (C₁ / (C₁ + 1)) * ε := by
          field_simp
          try ring
        rw [h7]
        calc (C₁ / (C₁ + 1)) * ε ≤ 1 * ε :=
              mul_le_mul h6 (le_refl ε) (by positivity) (by norm_num)
          _ = ε := one_mul ε
      linarith
    linarith
  have htp := two_point (u := u) (H := H) (z := z) (A := A) (C := C) hode hH hθpos
    (le_of_lt hξgt) hξlt
  have htri : |wfun θ * u1fun u z θ| ≤ ε + ∫ t in θ..ξ, gwt A C t := by
    have h2 : |wfun θ * u1fun u z θ| ≤
        |wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ| + |wfun ξ * u1fun u z ξ| := by
      have := abs_add_le (wfun θ * u1fun u z θ - wfun ξ * u1fun u z ξ)
        (wfun ξ * u1fun u z ξ)
      simpa only [sub_add_cancel] using this
    rw [abs_sub_comm] at h2
    linarith
  have hnn : 0 ≤ ∫ t in ξ..(Real.pi / 2), gwt A C t := by
    refine intervalIntegral.integral_nonneg (le_of_lt hξlt) (fun u' hu' => ?_)
    exact gwt_nonneg_Icc hA hC ⟨le_trans (le_of_lt hξpos) hu'.1, hu'.2⟩
  have hadd : (∫ t in θ..ξ, gwt A C t) + ∫ t in ξ..(Real.pi / 2), gwt A C t
      = ∫ t in θ..(Real.pi / 2), gwt A C t :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_gwt A C).intervalIntegrable θ ξ)
      ((continuous_gwt A C).intervalIntegrable ξ (Real.pi / 2))
  linarith

end Work.FTS_StreamBdry.SB6.UprimeAux
