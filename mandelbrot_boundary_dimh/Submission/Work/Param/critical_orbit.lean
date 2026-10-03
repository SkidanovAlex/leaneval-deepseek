import Mathlib
import Submission.Work.Param.Basic
import Submission.Work.Param.koenigs
import Submission.Work.Param.extend_step
import Submission.Work.Param.CriticalKit
import Submission.Work.Param.CriticalKit.basin_bounded
import Submission.Work.Param.CriticalKit.good_mem_basin
import Submission.Work.Param.CriticalKit.exists_good_iterate

namespace Work.Param

open Filter Topology
open scoped Topology

noncomputable section

/-- **The critical orbit of the quadratic family with multiplier `l` converges to `0`.**  For
`‖l‖ < 1` the critical point `-l/2` of `Q l x = l x + x²` lies in the basin of the attracting fixed
point `0`: `(Q l)^[n] (-l/2) → 0`.  (For `l = 0` the orbit is identically `0`.)

Intended proof.  Use `Work.Param.koenigs` to get `R > 0` and a holomorphic `ψ` on `Metric.ball 0 R`
with `ψ 0 = 0`, `deriv ψ 0 = 1` and `Q l (ψ w) = ψ (l * w)`.  If the critical value `-l²/4` is not
attained by `ψ` on that ball, `Work.Param.extend_step` extends `ψ` to `Metric.ball 0 (R/‖l‖)` with
the same equation and normalisation, and the agreement on the smaller ball makes the extensions
compatible.  Suppose the critical value is never attained at any stage: then `ψ` extends to an
entire function, which is bounded because `ψ w` lies in the basin of `0`
(`(Q l)^[n] (ψ w) = ψ (l^n w) → ψ 0 = 0`) and the basin is bounded (for `‖x‖` large
`‖Q l x‖ ≥ ‖x‖²/2`), while `deriv ψ 0 = 1 ≠ 0`; a bounded entire function is constant.  Hence at
some stage `ψ w = -l²/4` for some `w ∈ Metric.ball 0 R`, so the critical value lies in the basin;
the basin is backward invariant (`Q l (-l/2) = -l²/4`), so the critical point lies in the basin,
i.e. `(Q l)^[n] (-l/2) → 0`. -/
theorem critical_orbit (l : ℂ) (hl : ‖l‖ < 1) :
    Filter.Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) Filter.atTop (nhds 0) := by
  rcases eq_or_ne l 0 with rfl | hl0
  · -- for `l = 0` the critical point is `0` and the orbit is identically `0`
    have h0 : (Q 0) 0 = 0 := by simp [Q]
    have h : (fun n : ℕ => (Q 0)^[n] (-(0 / 2))) = fun _ : ℕ => (0 : ℂ) := by
      funext n
      simpa using Function.iterate_fixed h0 n
    rw [h]
    exact tendsto_const_nhds
  · by_contra hnot
    -- Koenigs' local linearisation of the attracting fixed point `0`
    obtain ⟨R, hR, ψ, hψdiff, hψ0, hψderiv, hψeq⟩ := koenigs l hl hl0
    have hψ : Good l R ψ := ⟨hR, hψdiff, hψ0, hψderiv, hψeq⟩
    -- the basin of `0` is bounded
    obtain ⟨M, hM⟩ := Work.Param.CriticalKit.basin_bounded l
    have hM0 : 0 ≤ M := by simpa using hM 0 (basin_zero l)
    have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
    -- some stage at which the disc of definition of the Koenigs solution is longer than `M`
    have h1 : 1 < (‖l‖)⁻¹ := by simpa [one_div] using (one_lt_div hlpos).mpr hl
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((M + 1) / R) h1
    have hRn : M < R / ‖l‖ ^ n := by
      have hmul : R * ((M + 1) / R) < R * (‖l‖⁻¹) ^ n := mul_lt_mul_of_pos_left hn hR
      have hleft : R * ((M + 1) / R) = M + 1 := by field_simp
      rw [hleft, inv_pow] at hmul
      rw [div_eq_mul_inv]
      linarith
    -- the solution extended to that longer disc
    obtain ⟨φ, hφ⟩ := Work.Param.CriticalKit.exists_good_iterate l hl hl0 hR hψ hnot n
    rcases hφ with ⟨hrpos, hdiff, hφ0, hderiv, heq⟩
    -- its values lie in the basin, hence in the ball of radius `M`
    have hmap : Set.MapsTo φ (Metric.ball 0 (R / ‖l‖ ^ n)) (Metric.closedBall (φ 0) M) := by
      intro w hw
      have hw' : φ w ∈ Metric.closedBall (0 : ℂ) M := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hM (φ w)
          (Work.Param.CriticalKit.good_mem_basin l hl ⟨hrpos, hdiff, hφ0, hderiv, heq⟩ w hw)
      simpa [hφ0] using hw'
    -- Schwarz' lemma: derivative at `0` at most `M / r < 1`, contradicting `deriv φ 0 = 1`
    have hsch := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmap hrpos
    rw [hderiv, norm_one] at hsch
    have hlt : M / (R / ‖l‖ ^ n) < 1 := by
      rw [div_lt_one (by positivity)]
      exact hRn
    linarith

end

end Work.Param
