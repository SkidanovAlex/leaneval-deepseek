import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.labels_arg_sum
import Submission.Work.WindCert.circleIntegral_logDeriv_quadrants

namespace Work.Cert

open Submission.CDTPlan Complex Metric
open scoped BigOperators
namespace Work.Cert

/-! ## Small supporting lemmas

* the value of `finRotate 4096 i` on `ℕ`,
* reading the list `(List.range 4096).map lab` at an index,
* the four units are exactly the fourth roots of unity,
* every `‖z‖ = 1` is `circleMap 0 1 (2πt)` with `0 ≤ t < 1`,
* the `4096` uniform arcs cover `[0,1)`. -/

lemma finRotate_4096_val (i : Fin 4096) : (((finRotate 4096 i) : Fin 4096) : ℕ) = ((i : ℕ) + 1) % 4096 := by
  rw [finRotate_apply, Fin.val_add]; simp

lemma range_map_lab_get (lab : ℕ → ℕ) (k : ℕ) (hk : k < 4096) :
    (((List.range 4096).map lab).get ⟨k, by simpa using hk⟩) = lab k := by
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_range]

lemma powI_mem_four (m : ℕ) (h : m < 4) :
    Complex.I ^ m = 1 ∨ Complex.I ^ m = Complex.I ∨ Complex.I ^ m = -1 ∨
      Complex.I ^ m = -Complex.I := by
  interval_cases m <;> simp [pow_succ, Complex.I_mul_I]

lemma exists_circleMap_unit {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ circleMap 0 1 (2 * Real.pi * t) = z := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff z).mp hz
  refine ⟨Int.fract (θ / (2 * Real.pi)), Int.fract_nonneg _, Int.fract_lt_one _, ?_⟩
  have h2 : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hfr : Int.fract (θ / (2 * Real.pi)) + (⌊θ / (2 * Real.pi)⌋ : ℝ) = θ / (2 * Real.pi) := by
    rw [Int.fract]; ring
  have hr : (2 * Real.pi) * Int.fract (θ / (2 * Real.pi))
      = θ - (⌊θ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
    have h := congrArg (fun x : ℝ => (2 * Real.pi) * x) hfr
    rw [mul_add, mul_div_cancel₀ θ h2] at h
    linarith [h]
  rw [circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  have harg : ((2 * Real.pi * Int.fract (θ / (2 * Real.pi)) : ℝ) : ℂ)
      = (θ : ℂ) - ((⌊θ / (2 * Real.pi)⌋ : ℤ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) := by
    rw [show (2 * Real.pi * Int.fract (θ / (2 * Real.pi)) : ℝ)
        = (2 * Real.pi) * Int.fract (θ / (2 * Real.pi)) by ring, hr]
    push_cast
    ring
  rw [harg, sub_mul, mul_assoc]
  have hc : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
  rw [Complex.exp_sub, hc, Complex.exp_int_mul_two_pi_mul_I, div_one]
  exact hθ

lemma covers_uniform (n : ℕ) (hn : 0 < n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ i : Fin n, t ∈ Set.Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n) := by
  set k := Nat.floor (t * n) with hk
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlt : k < n := by
    rw [Nat.floor_lt (by positivity)]
    nlinarith [ht1]
  refine ⟨⟨k, hlt⟩, ?_, ?_⟩
  · have h1 : (k : ℝ) ≤ t * n := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hn']
    linarith
  · have h2 : t * n < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hn']
    linarith

/-- If `g` is analytic on `ball 0 R` with `1 < R`, and on each uniform arc `[i/4096,(i+1)/4096]` of
the unit circle `g` takes its values in the open half plane `{w | 0 < (w · conj (I ^ lab i)).re}`
with `lab i < 4`, and the cyclic label sequence of length 4096 makes exactly one turn
(`labelsOK`), then `g` is zero free on `|z| = 1` and the logarithmic derivative of `g` has circle
integral `2πI`.  (Quadrant winding with `ρ = 1` plus `Work.Cert.labels_arg_sum`.) -/
theorem winding_of_quadrant_arcs {g : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hg : AnalyticOnNhd ℂ g (ball 0 R))
    (lab : ℕ → ℕ) (hlt : ∀ i, i < 4096 → lab i < 4)
    (hOK : labelsOK ((List.range 4096).map lab) = true)
    (harc : ∀ i : Fin 4096, ∀ t ∈ Set.Icc ((i : ℝ) / 4096) (((i : ℝ) + 1) / 4096),
      0 < (g (circleMap 0 1 (2 * Real.pi * t)) * star (Complex.I ^ lab (i : ℕ))).re) :
    (∀ z : ℂ, ‖z‖ = 1 → g z ≠ 0) ∧
      circleIntegral (fun z => logDeriv g z) 0 1 = 2 * (Real.pi : ℂ) * Complex.I := by
  -- the label list as a `List`
  have hlen : ((List.range 4096).map lab).length = 4096 := by simp
  have hlt' : ∀ l ∈ (List.range 4096).map lab, l < 4 := by
    intro l hl
    rw [List.mem_map] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    exact hlt j (List.mem_range.mp hj)
  -- the total argument turn of the label sequence is `2π`
  have hARG := labels_arg_sum (n := 4096) (by norm_num) ((List.range 4096).map lab) hlen hlt' hOK
  have hsum : (∑ i : Fin 4096, (Complex.arg (Complex.I ^ lab (((finRotate 4096 i) : Fin 4096) : ℕ)
      / Complex.I ^ lab (i : ℕ)) : ℂ)) = 2 * (Real.pi : ℂ) := by
    rw [← hARG]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [range_map_lab_get lab (i : ℕ) i.isLt,
      range_map_lab_get lab (((i : ℕ) + 1) % 4096) (Nat.mod_lt _ (by norm_num)),
      finRotate_4096_val i]
  -- the per-arc half plane hypotheses in the form of the quadrant winding lemma
  have hu : ∀ i : Fin 4096, Complex.I ^ lab (i : ℕ) = 1 ∨ Complex.I ^ lab (i : ℕ) = Complex.I ∨
      Complex.I ^ lab (i : ℕ) = -1 ∨ Complex.I ^ lab (i : ℕ) = -Complex.I :=
    fun i => powI_mem_four _ (hlt _ i.isLt)
  have hquad := Work.WindCert.circleIntegral_logDeriv_quadrants (g := g) (R := R) (ρ := 1)
    (by norm_num) hR hg 4096 (by norm_num) (fun i : Fin 4096 => Complex.I ^ lab (i : ℕ)) hu harc
  refine ⟨?_, ?_⟩
  · -- `g` is zero free on the unit circle
    intro z hz
    obtain ⟨t, ht0, ht1, htz⟩ := exists_circleMap_unit hz
    obtain ⟨i, hi⟩ := covers_uniform 4096 (by norm_num) t ht0 ht1
    have h := harc i t hi
    rw [htz] at h
    intro hz0
    rw [hz0, zero_mul, Complex.zero_re] at h
    exact lt_irrefl 0 h
  · -- the circle integral is `2πI`
    rw [hquad]
    rw [show (∑ i : Fin 4096, (Complex.arg ((fun i : Fin 4096 => Complex.I ^ lab (i : ℕ))
        (finRotate 4096 i) / (fun i : Fin 4096 => Complex.I ^ lab (i : ℕ)) i) : ℂ)) =
          2 * (Real.pi : ℂ) from hsum]
    ring

end Work.Cert
end Work.Cert

namespace Work.Cert

open Submission.CDTPlan Complex Metric
open scoped BigOperators

/-- The same statement as the declaration produced by the seeded file layout
(`Work.Cert.Work.Cert.winding_of_quadrant_arcs`), restated under the module-derived name
`Work.Cert.winding_of_quadrant_arcs`. -/
theorem winding_of_quadrant_arcs {g : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hg : AnalyticOnNhd ℂ g (ball 0 R))
    (lab : ℕ → ℕ) (hlt : ∀ i, i < 4096 → lab i < 4)
    (hOK : labelsOK ((List.range 4096).map lab) = true)
    (harc : ∀ i : Fin 4096, ∀ t ∈ Set.Icc ((i : ℝ) / 4096) (((i : ℝ) + 1) / 4096),
      0 < (g (circleMap 0 1 (2 * Real.pi * t)) * star (Complex.I ^ lab (i : ℕ))).re) :
    (∀ z : ℂ, ‖z‖ = 1 → g z ≠ 0) ∧
      circleIntegral (fun z => logDeriv g z) 0 1 = 2 * (Real.pi : ℂ) * Complex.I :=
  Work.Cert.Work.Cert.winding_of_quadrant_arcs hR hg lab hlt hOK harc

end Work.Cert
