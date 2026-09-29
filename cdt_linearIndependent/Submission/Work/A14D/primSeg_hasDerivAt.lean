import Mathlib
import Submission.Work.A14D.LC_setup

/-!
# `Work.A14D.primSeg_hasDerivAt`

The primitive `primSeg f c z = ∫₀¹ f (c + t(z-c)) (z-c) dt` along the segment from `c` to `z`
has complex derivative `f z` at every point `z` of a convex open set `S` on which `f` is
holomorphic.

The proof picks, by the Poincaré lemma for convex sets
(`Convex.exists_forall_hasDerivWithinAt`, Mathlib), a primitive `g` of `f` on `S`, and identifies
`primSeg f c w` with `g w - g c` for `w ∈ S` by the fundamental theorem of calculus applied to
`t ↦ g (c + t(w - c))` (whose `t`-derivative is `(w-c) f (c + t(w-c))`).  The derivative then
follows from that of `g`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace Work.A14D

theorem primSeg_hasDerivAt {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) {c : ℂ} (hc : c ∈ S)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    ∀ z ∈ S, HasDerivAt (primSeg f c) (f z) z := by
  -- A primitive of `f` on the convex set `S` (Poincaré lemma).
  obtain ⟨g, hg⟩ := hS.exists_forall_hasDerivWithinAt hf
  have hcontOn : ContinuousOn f S := hf.continuousOn
  -- `primSeg f c w = g w - g c` for `w ∈ S`.
  have hprim : ∀ w ∈ S, primSeg f c w = g w - g c := by
    intro w hw
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, c + (t : ℂ) * (w - c) ∈ S := by
      intro t ht
      simpa [AffineMap.lineMap_apply, Complex.real_smul, add_comm] using hS.lineMap_mem hc hw ht
    -- the `t`-derivative of `t ↦ g (c + t(w-c))`
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => g (c + (t : ℂ) * (w - c)))
          (f (c + (t : ℂ) * (w - c)) * (w - c)) t := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
      have hm : c + (t : ℂ) * (w - c) ∈ S := hseg t ht'
      have hγ : HasDerivAt (fun t : ℝ => c + (t : ℂ) * (w - c)) (w - c) t := by
        simpa [Complex.real_smul] using ((hasDerivAt_id t).smul_const (w - c)).const_add c
      have hgd : HasDerivAt g (f (c + (t : ℂ) * (w - c))) (c + (t : ℂ) * (w - c)) :=
        (hg _ hm).hasDerivAt (hSo.mem_nhds hm)
      exact hgd.comp t hγ
    have hcont' : ContinuousOn (fun t : ℝ => f (c + (t : ℂ) * (w - c))) (uIcc (0 : ℝ) 1) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
      have hm : c + (t : ℂ) * (w - c) ∈ S := hseg t ht'
      have hinnerC : ContinuousAt (fun s : ℝ => c + (s : ℂ) * (w - c)) t := by fun_prop
      have hfC : ContinuousAt f (c + (t : ℂ) * (w - c)) :=
        hcontOn.continuousAt (hSo.mem_nhds hm)
      have h1 : ContinuousAt (fun s : ℝ => f (c + (s : ℂ) * (w - c))) t :=
        ContinuousAt.comp' hfC hinnerC
      exact h1.continuousWithinAt
    have hint : IntervalIntegrable (fun t : ℝ => f (c + (t : ℂ) * (w - c)) * (w - c))
        volume 0 1 :=
      (hcont'.mul_const (w - c)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [primSeg, Complex.ofReal_zero, Complex.ofReal_one] using hFTC
  intro z hz
  have hgz : HasDerivAt g (f z) z := (hg z hz).hasDerivAt (hSo.mem_nhds hz)
  have hsub : HasDerivAt (fun w => g w - g c) (f z) z := hgz.sub_const (g c)
  refine hsub.congr_of_eventuallyEq ?_
  filter_upwards [hSo.mem_nhds hz] with w hw
  exact hprim w hw

end Work.A14D
