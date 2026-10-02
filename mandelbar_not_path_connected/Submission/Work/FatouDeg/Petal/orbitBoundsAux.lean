import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

open Filter

/-- **Orbit bounds from the one-step contraction.**

If a set `S` is invariant under `Pfun m G`, on `S` the modulus never increases and the chart
`z ↦ ‖z‖^(-(m-1))` is strictly increasing with uniform increment `c > 0`, then for every `z ∈ S`
the orbit satisfies

* `(‖P^[k] z‖^(m-1))⁻¹ ≥ (‖z‖^(m-1))⁻¹ + c*k`,
* `‖P^[k] z‖^(m-1) ≤ ((‖z‖^(m-1))⁻¹ + c*k)⁻¹`,
* `P^[k] z → 0` as `k → ∞`.

In particular the orbits decay like `k^(-1/(m-1))`. -/
theorem orbitBoundsAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {S : Set ℂ} {c : ℝ} (hc : 0 < c)
    (hmap : Set.MapsTo (Pfun m G) S S)
    (hnorm : ∀ z ∈ S, ‖Pfun m G z‖ ≤ ‖z‖)
    (hcontract : ∀ z ∈ S, (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹) :
    (∀ z ∈ S, ∀ k : ℕ, (‖(Pfun m G)^[k] z‖ ^ (m - 1))⁻¹ ≥ (‖z‖ ^ (m - 1))⁻¹ + c * k) ∧
    (∀ z ∈ S, ∀ k : ℕ, ‖(Pfun m G)^[k] z‖ ^ (m - 1) ≤ ((‖z‖ ^ (m - 1))⁻¹ + c * k)⁻¹) ∧
    (∀ z ∈ S, Filter.Tendsto (fun k : ℕ => (Pfun m G)^[k] z) Filter.atTop (nhds 0)) := by
  -- `m - 1 ≥ 1`, in particular nonzero.
  have hm1ne : m - 1 ≠ 0 := by omega
  -- the parabolic fixed point is at the origin.
  have hP0 : Pfun m G 0 = 0 := by
    rw [Pfun]
    have hm0 : m ≠ 0 := by omega
    have hm1 : m + 1 ≠ 0 := by omega
    rw [zero_pow hm0, zero_pow hm1]
    ring
  -- the orbit of a point of `S` stays in `S`.
  have hmem : ∀ z ∈ S, ∀ k : ℕ, (Pfun m G)^[k] z ∈ S := by
    intro z hz k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hmap ih
  -- `0 ∉ S` (the one-step contraction is incompatible with `c > 0` at the fixed point).
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz hz0
    rw [hz0] at hz
    have h := hcontract 0 hz
    rw [hP0, norm_zero] at h
    rw [zero_pow hm1ne, inv_zero] at h
    simp only [zero_add] at h
    linarith
  -- (1) the chart value grows linearly along the orbit.
  have h1 : ∀ z ∈ S, ∀ k : ℕ,
      (‖(Pfun m G)^[k] z‖ ^ (m - 1))⁻¹ ≥ (‖z‖ ^ (m - 1))⁻¹ + c * k := by
    intro z hz k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := hcontract ((Pfun m G)^[k] z) (hmem z hz k)
        rw [Function.iterate_succ_apply']
        push_cast
        calc (‖Pfun m G ((Pfun m G)^[k] z)‖ ^ (m - 1))⁻¹
            ≥ (‖(Pfun m G)^[k] z‖ ^ (m - 1))⁻¹ + c := hstep
          _ ≥ (‖z‖ ^ (m - 1))⁻¹ + c * ↑k + c := by linarith
          _ = (‖z‖ ^ (m - 1))⁻¹ + c * (↑k + 1) := by ring
  -- (2) inverting the bound of (1).
  have h2 : ∀ z ∈ S, ∀ k : ℕ,
      ‖(Pfun m G)^[k] z‖ ^ (m - 1) ≤ ((‖z‖ ^ (m - 1))⁻¹ + c * k)⁻¹ := by
    intro z hz k
    have hz0 := hne z hz
    have hBpos : 0 < (‖z‖ ^ (m - 1))⁻¹ + c * k := by
      have hpos : 0 < (‖z‖ ^ (m - 1))⁻¹ := by
        apply inv_pos.mpr
        exact pow_pos (norm_pos_iff.mpr hz0) _
      have hc0 : 0 ≤ c * (k : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg k)
      linarith
    simpa using inv_anti₀ hBpos (h1 z hz k)
  refine ⟨h1, h2, ?_⟩
  -- (3) the orbits converge to `0`.
  intro z hz
  let x : ℕ → ℝ := fun k => ‖(Pfun m G)^[k] z‖
  have hxnn : ∀ k, 0 ≤ x k := fun k => norm_nonneg _
  -- the comparison sequence `k ↦ ((‖z‖^(m-1))⁻¹ + c*k)⁻¹` tends to `0`.
  have hBtop : Tendsto (fun k : ℕ => (‖z‖ ^ (m - 1))⁻¹ + c * (k:ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop ((‖z‖ ^ (m - 1))⁻¹)
      (Filter.Tendsto.const_mul_atTop hc (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hBinv : Tendsto (fun k : ℕ => ((‖z‖ ^ (m - 1))⁻¹ + c * (k:ℝ))⁻¹) atTop (nhds 0) :=
    hBtop.inv_tendsto_atTop
  -- squeeze for the `(m-1)`-th powers.
  have hy : Tendsto (fun k : ℕ => x k ^ (m - 1)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBinv ?_ ?_
    · intro k; exact pow_nonneg (hxnn k) _
    · intro k; exact h2 z hz k
  -- `(m-1)`-th powers tending to `0` forces the sequence itself to tend to `0`.
  have hxtend : Tendsto x atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at hy
    obtain ⟨N, hN⟩ := hy (ε ^ (m - 1)) (pow_pos hε _)
    refine ⟨N, fun n hn => ?_⟩
    have hlt : x n ^ (m - 1) < ε ^ (m - 1) := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (hxnn n) _)] at this
    have hlt' : x n < ε := (pow_lt_pow_iff_left₀ (hxnn n) hε.le hm1ne).mp hlt
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hxnn n)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hxtend

end Work.FatouDeg.Petal
