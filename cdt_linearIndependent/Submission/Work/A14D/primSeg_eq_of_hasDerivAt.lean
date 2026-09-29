import Mathlib
import Submission.Work.A14D.LC_setup
import Submission.Work.C17g.segment_primitive

/-!
# `Work.A14D.primSeg_eq_of_hasDerivAt`

The segment integral `primSeg g c z = ∫₀¹ g (c + t(z-c)) · (z-c) dt` is the primitive of `g`
vanishing at `c`.  Hence, on an open convex set `S` on which `g` is holomorphic and `Φ` is an
antiderivative of `g`, `primSeg g c z = Φ z - Φ c` for every `z ∈ S`.

The proof identifies `primSeg g c w` with `Φ w - Φ c` for `w ∈ S` by the fundamental theorem of
calculus applied to `t ↦ Φ (c + t(w-c))`, whose `t`-derivative is `(w-c)·g(c + t(w-c))`; the
resulting (parameter) integral is exactly `primSeg g c w`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace Work.A14D

theorem primSeg_eq_of_hasDerivAt {S : Set ℂ} (hSo : IsOpen S) (hSc : Convex ℝ S) {c z : ℂ}
    (hc : c ∈ S) (hz : z ∈ S) {g Φ : ℂ → ℂ} (hgd : DifferentiableOn ℂ g S)
    (hΦ : ∀ w ∈ S, HasDerivAt Φ (g w) w) :
    Work.A14D.primSeg g c z = Φ z - Φ c := by
  have hcontOn : ContinuousOn g S := hgd.continuousOn
  -- the segment `c + t(z-c)`, `t ∈ [0,1]`, stays in `S`
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, c + (t : ℂ) * (z - c) ∈ S := by
    intro t ht
    simpa [Complex.real_smul] using hSc.add_smul_sub_mem hc hz ht
  -- the `t`-derivative of `t ↦ Φ (c + t(z-c))`
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Φ (c + (t : ℂ) * (z - c)))
        (g (c + (t : ℂ) * (z - c)) * (z - c)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
    have hm : c + (t : ℂ) * (z - c) ∈ S := hseg t ht'
    have hγ : HasDerivAt (fun t : ℝ => c + (t : ℂ) * (z - c)) (z - c) t := by
      simpa [Complex.real_smul] using ((hasDerivAt_id t).smul_const (z - c)).const_add c
    exact (hΦ _ hm).comp t hγ
  -- the integrand is continuous on `[0,1]`, hence interval integrable
  have hcont' : ContinuousOn (fun t : ℝ => g (c + (t : ℂ) * (z - c))) (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
    have hm : c + (t : ℂ) * (z - c) ∈ S := hseg t ht'
    have hinnerC : ContinuousAt (fun s : ℝ => c + (s : ℂ) * (z - c)) t := by fun_prop
    have hfC : ContinuousAt g (c + (t : ℂ) * (z - c)) :=
      hcontOn.continuousAt (hSo.mem_nhds hm)
    have h1 : ContinuousAt (fun s : ℝ => g (c + (s : ℂ) * (z - c))) t :=
      ContinuousAt.comp' hfC hinnerC
    exact h1.continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => g (c + (t : ℂ) * (z - c)) * (z - c))
      volume 0 1 :=
    (hcont'.mul_const (z - c)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [primSeg, Complex.ofReal_zero, Complex.ofReal_one] using hFTC

end Work.A14D
