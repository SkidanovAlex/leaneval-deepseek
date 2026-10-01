import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.g0_deriv_bound

open Filter
open scoped Topology

namespace Work.LinnikAreas.A5

/-!
# The derivative bound `|gc'| ≤ 1/K` on `[0,K]`

For the λ → 0 endpoint test function `gc K t = (K−t)/K` on `[0,K]` (and `0` outside), the
same bound as for `g0 K` holds: `‖deriv (gc K) t‖ ≤ 1/K` for all `t ∈ [0,K]`.

Unlike `g0 K t = if t ≤ K then (K−t)/K else 0` (which equals the affine map `t ↦ (K−t)/K`
on *all* of `(−∞, K)`), `gc K` is cut off at `t = 0` as well, so `gc K` is constant `0`
on `(−∞, 0)`.  Consequently:

* on the *open* interval `(0, K)` the function `gc K` agrees with the affine `t ↦ (K−t)/K`,
  so its derivative there is the constant `−1/K` (`gc_deriv_of_pos_lt`);
* at the left endpoint `t = 0` the function jumps (`gc K 0 = 1` while `gc K t = 0` for
  `t < 0`), so it is not even continuous there, hence not differentiable and
  `deriv (gc K) 0 = 0` (`not_differentiableAt_gc_zero`);
* at the right endpoint `t = K` the function coincides with `g0 K` near `K` (both are
  positive near `K`), and `g0 K` is not differentiable at `K`, so neither is `gc K`
  (`not_differentiableAt_gc_K`), whence `deriv (gc K) K = 0`.

The requested bound `gc_deriv_bound` is the immediate combination of these three facts.
-/

/-- On the open interval `(0, K)` the test function `gc K` agrees with the affine map
`t ↦ (K−t)/K`, so its derivative is the constant `−1/K`. -/
lemma gc_deriv_of_pos_lt {K t : ℝ} (h0 : 0 < t) (hKt : t < K) :
    deriv (gc K) t = -(1 / K) := by
  have hev : (fun s : ℝ => (K - s) / K) =ᶠ[𝓝 t] gc K := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h0, hKt⟩] with s hs
    exact (gc_of_mem hs.1.le hs.2.le).symm
  rw [← hev.deriv_eq]
  rw [deriv_div_const]
  have h1 : deriv (fun s : ℝ => K - s) t = -1 := by
    simp
  rw [h1]
  ring

/-- At the left endpoint `t = 0` the function `gc K` jumps (`gc K 0 = 1` while `gc K t = 0`
for all `t < 0`), so it is not continuous there, hence not differentiable.  This forces
`deriv (gc K) 0 = 0`. -/
lemma not_differentiableAt_gc_zero {K : ℝ} (hK : 0 < K) : ¬ DifferentiableAt ℝ (gc K) 0 := by
  intro hd
  -- `gc K` tends to `0` along `𝓝[<] 0` (it is constantly `0` there)
  have hleft : Tendsto (gc K) (𝓝[<] (0:ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (gc_of_lt ht).symm
  -- but differentiability would force it to tend to `gc K 0` there too
  have hright : Tendsto (gc K) (𝓝[<] (0:ℝ)) (𝓝 (gc K 0)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0val : gc K 0 = 1 := by
    rw [gc_of_mem le_rfl hK.le, sub_zero, div_self (ne_of_gt hK)]
  have : (0:ℝ) = gc K 0 := tendsto_nhds_unique hleft hright
  rw [h0val] at this
  norm_num at this

/-- At the right endpoint `t = K` the function `gc K` coincides with `g0 K` near `K` (both
equal `0` for `t > K` and the affine `(K−t)/K` for `t` just below `K`), and `g0 K` is not
differentiable at `K`; hence `gc K` is not differentiable at `K` either. -/
lemma not_differentiableAt_gc_K {K : ℝ} (hK : 0 < K) : ¬ DifferentiableAt ℝ (gc K) K := by
  intro hd
  apply not_differentiableAt_g0 hK
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hK] with t ht
  rw [gc]
  by_cases hle : t ≤ K
  · rw [if_pos ⟨ht.le, hle⟩, g0_of_le hle]
  · rw [if_neg (fun hc => hle hc.2), g0, if_neg hle]

/-- The derivative bound for the λ → 0 endpoint test function
`gc K t = (K−t)/K` on `[0,K]` (and `0` outside): `‖gc K'‖ ≤ 1/K` on `[0,K]`.
On `(0,K)` the function agrees near each point with the affine `(K−t)/K`, whose derivative
is the constant `−1/K` of norm `1/K`; at the corners `t = 0` and `t = K` the function is
*not* differentiable, so `deriv (gc K) · = 0` there by `deriv_zero_of_not_differentiableAt`,
and the bound holds. -/
theorem gc_deriv_bound (K : ℝ) (hK : 0 < K) :
    ∀ t ∈ Set.Icc (0:ℝ) K, ‖deriv (Work.LinnikAreas.A5.gc K) t‖ ≤ 1 / K := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0eq | h0lt
  · -- `t = 0`
    rw [← h0eq, deriv_zero_of_not_differentiableAt (not_differentiableAt_gc_zero hK), norm_zero]
    exact one_div_nonneg.mpr hK.le
  · rcases lt_or_eq_of_le ht.2 with hlt | heq
    · -- `0 < t < K`
      rw [gc_deriv_of_pos_lt h0lt hlt, norm_neg,
        Real.norm_of_nonneg (one_div_nonneg.mpr hK.le)]
    · -- `t = K`
      rw [heq, deriv_zero_of_not_differentiableAt (not_differentiableAt_gc_K hK), norm_zero]
      exact one_div_nonneg.mpr hK.le

end Work.LinnikAreas.A5
