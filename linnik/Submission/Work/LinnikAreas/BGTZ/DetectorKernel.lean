import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorMellinDefs

/-!
# The BGTZ detector kernel

We evaluate the Mellin/Perron kernel
`mellK c x = (1/2π) ∫_ℝ x^{c+it} / ((c+it)(c+1+it)) dt`
for `c > 0` and real `x > 0`, obtaining `max 0 (1 - 1/x)`.

The argument is Mellin inversion applied to the tent function `u ↦ max 0 (1 - u)`,
whose Mellin transform is `1/(s(s+1))`, evaluated at `1/x`.
-/

namespace Work.LinnikAreas.BGTZ

open MeasureTheory Set Complex Asymptotics Filter
open scoped BigOperators Topology ComplexConjugate

/-- The tent function `u ↦ max 0 (1 - u)`, as a complex-valued function. -/
noncomputable def tent (u : ℝ) : ℂ := ((max 0 (1 - u) : ℝ) : ℂ)

/-- On `(0, ∞)`, the tent function agrees with the difference of the indicators of `(0,1]`. -/
lemma tent_eq_ind (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
    tent t = ((Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t)
      - ((Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)) t) := by
  have ht0 : 0 < t := ht
  simp only [tent]
  rcases le_or_gt t 1 with h | h
  · rw [Set.indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht0, h⟩),
        Set.indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht0, h⟩)]
    rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - t)]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (show t ∉ Ioc 0 1 from fun hc => absurd hc.2 (not_le.mpr h)),
        Set.indicator_of_notMem (show t ∉ Ioc 0 1 from fun hc => absurd hc.2 (not_le.mpr h))]
    rw [max_eq_left (by linarith : (1:ℝ) - t ≤ 0)]
    simp

/-- The Mellin transform of the tent function is `1/(s(s+1))` in the half-plane `Re s > 0`. -/
lemma hasMellin_tent (s : ℂ) (hs : 0 < s.re) : HasMellin tent s (1 / (s * (s + 1))) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith [hs]
  have hA : HasMellin ((Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ))) s (1/s) :=
    hasMellin_one_Ioc hs
  have hB : HasMellin ((Ioc 0 1).indicator (fun t : ℝ => (t:ℂ))) s (1/(s+1)) := by
    have h := hasMellin_cpow_Ioc (1:ℂ) (s := s) (by simp only [Complex.one_re]; linarith [hs])
    simpa [Complex.cpow_one] using h
  have hsub := hasMellin_sub hA.1 hB.1
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent]
    exact (integrableOn_congr_fun (fun t ht => by rw [tent_eq_ind t ht]) measurableSet_Ioi).mpr
      hsub.1
  · have h1 : mellin tent s = mellin (fun t =>
        (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t
          - (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)) t) s :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [tent_eq_ind t ht])
    rw [h1, hsub.2, hA.2, hB.2]
    field_simp
    ring

/-- Auxiliary kernel `1/((c+iy)(c+1+iy))`, integrable on the whole real line. -/
noncomputable def kern (c : ℝ) (y : ℝ) : ℂ :=
  1 / (((c:ℂ) + y*I) * ((c:ℂ) + 1 + y*I))

lemma kern_conj (c y : ℝ) : kern c (-y) = conj (kern c y) := by
  unfold kern
  rw [map_div₀, map_one, map_mul]
  rw [show conj ((c:ℂ) + y*I) = (c:ℂ) + (-y)*I from by apply Complex.ext <;> simp,
      show conj ((c:ℂ) + 1 + y*I) = (c:ℂ) + 1 + (-y)*I from by apply Complex.ext <;> simp]
  norm_num

lemma kern_cont (c : ℝ) (hc : 0 < c) : Continuous (kern c) := by
  unfold kern
  rw [show (fun y : ℝ => 1 / (((c:ℂ) + y*I) * ((c:ℂ) + 1 + y*I)))
      = fun y : ℝ => ((((c:ℂ) + y*I) * ((c:ℂ) + 1 + y*I)))⁻¹ from by funext y; rw [one_div]]
  apply Continuous.inv₀
  · fun_prop
  · intro y
    have hA : ((c:ℂ) + y*I) ≠ 0 := by
      intro h
      have h' : ((c:ℂ) + y*I).re = c := by simp
      rw [h] at h'
      simp at h'
      linarith
    have hB : ((c:ℂ) + 1 + y*I) ≠ 0 := by
      intro h
      have h' : ((c:ℂ) + 1 + y*I).re = c + 1 := by simp
      rw [h] at h'
      simp at h'
      linarith
    exact mul_ne_zero hA hB

lemma kern_integrable (c : ℝ) (hc : 0 < c) : Integrable (kern c) := by
  apply LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (f := kern c) (g := fun y : ℝ => (1 + y^2)⁻¹)
  · exact (kern_cont c hc).locallyIntegrable
  · filter_upwards with y
    simp only [Function.comp_apply]
    rw [kern_conj c y, norm_conj]
  · rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    have hA : (y:ℝ) ≤ ‖(c:ℂ) + y*I‖ := by
      have h := Complex.abs_im_le_norm ((c:ℂ) + y*I)
      rw [show ((c:ℂ) + y*I).im = y by simp, abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at h
      exact h
    have hB : (y:ℝ) ≤ ‖(c:ℂ) + 1 + y*I‖ := by
      have h := Complex.abs_im_le_norm ((c:ℂ) + 1 + y*I)
      rw [show ((c:ℂ) + 1 + y*I).im = y by simp, abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at h
      exact h
    rw [kern, one_div, norm_inv, norm_mul]
    rw [show ‖(1 + y^2)⁻¹‖ = (1 + y^2)⁻¹ by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]]
    have hle : y * y ≤ ‖(c:ℂ) + y*I‖ * ‖(c:ℂ) + 1 + y*I‖ :=
      mul_le_mul hA hB (by linarith) (norm_nonneg _)
    calc (‖(c:ℂ) + y*I‖ * ‖(c:ℂ) + 1 + y*I‖)⁻¹
        ≤ (y * y)⁻¹ := by
          rw [inv_le_inv₀ (mul_pos (lt_of_lt_of_le hy0 hA) (lt_of_lt_of_le hy0 hB))
                (mul_pos hy0 hy0)]
          exact hle
      _ ≤ 2 * (1 + y^2)⁻¹ := by
          rw [show (y * y)⁻¹ = 1/(y*y) by rw [one_div],
              show (2:ℝ) * (1 + y^2)⁻¹ = 2/(1+y^2) by rw [div_eq_mul_inv]]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hy]
  · exact integrable_inv_one_add_sq.integrableAtFilter atTop

lemma tent_cont : Continuous tent := by
  unfold tent
  exact continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_id))

/-- The inverse Mellin transform of `mellin tent` at `1/x` is the BGTZ kernel `mellK c x`. -/
lemma mellinInv_mellin_tent_eq_mellK (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (mellin tent) (1/x) = mellK c (x:ℂ) := by
  rw [mellinInv, mellK]
  have hintegral : (∫ y : ℝ, ((1/x : ℝ) : ℂ) ^ (-(↑c + y * I)) • (mellin tent) (↑c + y * I))
      = ∫ t : ℝ, (x:ℂ) ^ ((c:ℂ) + t * I)
          / (((c:ℂ) + t * I) * ((c:ℂ) + 1 + t * I)) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [show ((1/x : ℝ) : ℂ) = (x:ℂ)⁻¹ by rw [one_div, Complex.ofReal_inv]]
    rw [show (mellin tent) (↑c + y*I) = 1/(((c:ℂ)+y*I)*((c:ℂ)+1+y*I)) by
      rw [(hasMellin_tent (↑c + y*I) (by simpa using hc)).2]
      congr 1
      ring]
    rw [smul_eq_mul, Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv]
    ring_nf
  rw [hintegral, Complex.real_smul]
  congr 1
  push_cast
  ring

theorem DetectorKernel {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    Work.LinnikAreas.BGTZ.mellK c (x : ℂ) = (if 1 ≤ x then (1 - 1 / x : ℝ) else 0 : ℂ) := by
  have hconv : MellinConvergent tent (c:ℂ) := (hasMellin_tent (c:ℂ) (by simpa using hc)).1
  have hvert : VerticalIntegrable (mellin tent) c := by
    refine (kern_integrable c hc).congr ?_
    filter_upwards with y
    rw [kern, (hasMellin_tent (↑c + y*I) (by simpa using hc)).2]
    congr 1
    ring
  have hinv := mellinInv_mellin_eq c tent (show (0:ℝ) < 1/x by positivity) hconv hvert
    tent_cont.continuousAt
  have hkey := mellinInv_mellin_tent_eq_mellK c x hc hx
  rw [← hkey, hinv]
  unfold tent
  by_cases h : 1 ≤ x
  · rw [if_pos h, max_eq_right (by have := (div_le_one hx).mpr h; linarith)]
  · rw [if_neg h, max_eq_left (by have := (one_lt_div hx).mpr (lt_of_not_ge h); linarith)]
    norm_num

end Work.LinnikAreas.BGTZ
