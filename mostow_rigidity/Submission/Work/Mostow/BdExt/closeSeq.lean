import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BdExt.lawCosines

/-!
# `closeSeq`: two sequences at bounded hyperbolic distance have the same boundary limit

If `u` and `v` are sequences in the chart `E n` of `ℍⁿ` whose successive points are at bounded
hyperbolic distance (`hdist (u k) (v k) ≤ D`) and both escape to infinity (`lvl (u k), lvl (v k) →
∞`), then `u` and `v` converge to the *same* boundary point (if any): the Euclidean directions
`dirv (u k)` and `dirv (v k)` have the same limit.

The proof is the quantitative law of cosines `norm_sub_dirv_sq_le`:
`‖dirv u - dirv v‖² ≤ 2 (cosh (hdist u v) - 1) / (sinh (lvl u) · sinh (lvl v))`,
and `cosh (hdist u v) ≤ cosh D` while `sinh (lvl u) · sinh (lvl v) → ∞`, so the difference of the
two directions tends to `0`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

noncomputable section

variable {n : ℕ}

/-- `Real.sinh` tends to `+∞` at `+∞` (its argument dominates `id` on `[0, ∞)`). -/
lemma tendsto_sinh_atTop' : Filter.Tendsto Real.sinh Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono' Filter.atTop
    ((Filter.eventually_ge_atTop (0 : ℝ)).mono fun _ hx => Real.self_le_sinh_iff.mpr hx)
    tendsto_id

/-- The hyperbolic level of the origin is `0`. -/
lemma lvl_zero : lvl (0 : E n) = 0 := by
  have h := norm_eq_sinh_lvl (0 : E n)
  rw [norm_zero] at h
  exact Real.sinh_eq_zero.mp h.symm

theorem closeSeq (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (u v : ℕ → Submission.Mostow.E n) (D : ℝ)
    (hD : 0 ≤ D) (hclose : ∀ k, Submission.Mostow.hdist (u k) (v k) ≤ D)
    (hu : Filter.Tendsto (fun k => Work.Mostow.BdExt.lvl (u k)) Filter.atTop Filter.atTop)
    (hv : Filter.Tendsto (fun k => Work.Mostow.BdExt.lvl (v k)) Filter.atTop Filter.atTop)
    (η : Submission.Mostow.E n) (hη : Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (u k)) Filter.atTop (nhds η)) :
    Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (v k)) Filter.atTop (nhds η) := by
  -- `sinh (lvl ·)` escapes to `+∞` for both sequences, hence so does their product
  have hsu : Filter.Tendsto (fun k => Real.sinh (lvl (u k))) Filter.atTop Filter.atTop :=
    tendsto_sinh_atTop'.comp hu
  have hsv : Filter.Tendsto (fun k => Real.sinh (lvl (v k))) Filter.atTop Filter.atTop :=
    tendsto_sinh_atTop'.comp hv
  have hprod : Filter.Tendsto
      (fun k => Real.sinh (lvl (u k)) * Real.sinh (lvl (v k))) Filter.atTop Filter.atTop :=
    hsu.atTop_mul_atTop₀ hsv
  have hdiv : Filter.Tendsto (fun k => 2 * (Real.cosh D - 1) /
      (Real.sinh (lvl (u k)) * Real.sinh (lvl (v k)))) Filter.atTop (nhds 0) :=
    hprod.const_div_atTop _
  -- both sequences are eventually nonzero, so the law of cosines applies
  have hbig_u : ∀ᶠ k in Filter.atTop, (1 : ℝ) ≤ lvl (u k) :=
    hu.eventually (Filter.eventually_ge_atTop 1)
  have hbig_v : ∀ᶠ k in Filter.atTop, (1 : ℝ) ≤ lvl (v k) :=
    hv.eventually (Filter.eventually_ge_atTop 1)
  -- the quantitative bound on the difference of the directions
  have hbound : ∀ᶠ k in Filter.atTop, ‖dirv (u k) - dirv (v k)‖ ^ 2 ≤
      2 * (Real.cosh D - 1) / (Real.sinh (lvl (u k)) * Real.sinh (lvl (v k))) := by
    filter_upwards [hbig_u, hbig_v] with k hku hkv
    have hu0 : u k ≠ 0 := by
      intro h
      rw [h, lvl_zero] at hku
      linarith
    have hv0 : v k ≠ 0 := by
      intro h
      rw [h, lvl_zero] at hkv
      linarith
    have hpu : 0 < Real.sinh (lvl (u k)) := Real.sinh_pos_iff.mpr (by linarith)
    have hpv : 0 < Real.sinh (lvl (v k)) := Real.sinh_pos_iff.mpr (by linarith)
    have hden : 0 < Real.sinh (lvl (u k)) * Real.sinh (lvl (v k)) := mul_pos hpu hpv
    have hdnn : 0 ≤ hdist (u k) (v k) := hI.1 _ _
    have hcosh : Real.cosh (hdist (u k) (v k)) ≤ Real.cosh D :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg hdnn, abs_of_nonneg hD]
        exact hclose k)
    calc ‖dirv (u k) - dirv (v k)‖ ^ 2
        ≤ 2 * (Real.cosh (hdist (u k) (v k)) - 1) /
            (Real.sinh (lvl (u k)) * Real.sinh (lvl (v k))) :=
          norm_sub_dirv_sq_le (u k) (v k) hu0 hv0
      _ ≤ 2 * (Real.cosh D - 1) / (Real.sinh (lvl (u k)) * Real.sinh (lvl (v k))) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          linarith
  -- squeeze: the squared distance of the directions tends to `0`
  have hsq : Filter.Tendsto (fun k => ‖dirv (u k) - dirv (v k)‖ ^ 2) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
      (Filter.Eventually.of_forall fun k => sq_nonneg _) hbound
  have hsqrt : Filter.Tendsto (fun k => Real.sqrt (‖dirv (u k) - dirv (v k)‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    rwa [Real.sqrt_zero] at h
  have hnorm : Filter.Tendsto (fun k => ‖dirv (u k) - dirv (v k)‖) Filter.atTop (nhds 0) :=
    hsqrt.congr' (Filter.Eventually.of_forall fun k =>
      Real.sqrt_sq (norm_nonneg (dirv (u k) - dirv (v k))))
  have hdiff : Filter.Tendsto (fun k => dirv (v k) - dirv (u k)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  have hsum : Filter.Tendsto (fun k => dirv (v k) - dirv (u k) + dirv (u k))
      Filter.atTop (nhds (0 + η)) := hdiff.add hη
  simpa only [sub_add_cancel, zero_add] using hsum

end

end Work.Mostow.BdExt
