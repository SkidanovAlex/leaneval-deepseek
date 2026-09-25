import Mathlib
import Submission.Work.NN.Core.fderiv_eq_zero_of_vanishing_off_polydisc

/-!
# A function vanishing off a polydisc has vanishing iterated derivatives there

Let `χ : ℂⁿ → ℂ` be `C^m` and vanish on the closed exterior
`S = {z | ∃ i, ρ i ≤ ‖z i‖}` of the (possibly degenerate) polydisc of radii `ρ`.
Then every iterated derivative `iteratedFDeriv ℝ m χ` vanishes on `S`:

`iteratedFDeriv ℝ m χ z v = 0` for all `z ∈ S` and all `v : Fin m → (Fin n → ℂ)`.

The argument is the standard one for this situation:

* On the **open** exterior `W = {z | ∃ i, ρ i < ‖z i‖}` the function agrees with `0` in a
  neighbourhood of every one of its points (namely the open set `{ρ i < ‖· i‖}` for a suitable
  `i`), so by `Filter.EventuallyEq.iteratedFDeriv` its iterated derivatives agree with those of
  `0` there.
* `W` is **dense** in `S`: given `z ∈ S` with witness `j` (`ρ j ≤ ‖z j‖`), let `w` be the vector
  which equals `z j` in the `j`-th coordinate if `z j ≠ 0` and equals `1` there otherwise (and `0`
  elsewhere).  Then `z + t • w ∈ W` for every `t > 0` (the `j`-th coordinate is scaled up, resp.
  moved away from the origin) and `z + t • w → z` as `t → 0⁺`.
* The zero set of the continuous map `z ↦ iteratedFDeriv ℝ m χ z` is closed
  (`ContDiff.continuous_iteratedFDeriv'`), so being zero on the dense subset `W` of `S` it is zero
  on all of `S` (`IsClosed.mem_of_tendsto`).
-/

namespace Work.NN.Core

open Filter
open scoped Topology

theorem iteratedFDeriv_apply_eq_zero_of_vanishing {n : ℕ} {ρ : Fin n → ℝ}
    {f : (Fin n → ℂ) → ℂ} {m : ℕ} (hf : ContDiff ℝ m f)
    (hsub : ∀ z, (∃ i, ρ i ≤ ‖z i‖) → f z = 0) :
    ∀ z, (∃ i, ρ i ≤ ‖z i‖) → ∀ v : Fin m → Fin n → ℂ, iteratedFDeriv ℝ m f z v = 0 := by
  -- Step 1: the iterated derivative vanishes on the open exterior of the polydisc.
  have hzero_of_lt : ∀ y : Fin n → ℂ, (∃ i, ρ i < ‖y i‖) → iteratedFDeriv ℝ m f y = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := hy
    -- `f` vanishes on the open neighbourhood `{ρ i < ‖· i‖}` of `y`.
    have hopen : IsOpen {y : Fin n → ℂ | ρ i < ‖y i‖} :=
      isOpen_lt continuous_const ((continuous_apply i).norm)
    have hmem : {y : Fin n → ℂ | ρ i < ‖y i‖} ∈ 𝓝 y := hopen.mem_nhds hi
    have hev : f =ᶠ[𝓝 y] (fun _ : Fin n → ℂ => (0 : ℂ)) := by
      filter_upwards [hmem] with y' hy'
      exact hsub y' ⟨i, le_of_lt hy'⟩
    -- hence the iterated derivatives agree with those of `0` in a neighbourhood of `y`.
    have h1 : iteratedFDeriv ℝ m f y = iteratedFDeriv ℝ m (fun _ : Fin n → ℂ => (0 : ℂ)) y :=
      (hev.iteratedFDeriv ℝ m).self_of_nhds
    rw [h1, iteratedFDeriv_fun_zero]
    exact Pi.zero_apply y
  intro z hz v
  obtain ⟨j, hj⟩ := hz
  -- Step 2: an explicit sequence in the open exterior converging to `z`.
  -- `w` is an outward direction in the `j`-th coordinate.
  let w : Fin n → ℂ := Function.update 0 j (if z j = 0 then 1 else z j)
  let t : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  let zk : ℕ → (Fin n → ℂ) := fun k => z + t k • w
  have htpos : ∀ k, 0 < t k := by intro k; simp only [t]; positivity
  -- the points of the sequence lie in the open exterior, witnessed by the coordinate `j`.
  have hzk_mem : ∀ k, ∃ i, ρ i < ‖zk k i‖ := by
    intro k
    refine ⟨j, ?_⟩
    have hwj : w j = if z j = 0 then 1 else z j := by simp [w]
    have hval : zk k j = z j + t k • w j := by
      simp [zk, Pi.add_apply, Pi.smul_apply]
    rw [hval, hwj]
    by_cases hzj : z j = 0
    · -- `z j = 0`, so `ρ j ≤ 0` and the `j`-th coordinate of `zk k` is `t k > 0 = ρ j`.
      have h0 : ρ j ≤ (0 : ℝ) := by simpa [hzj] using hj
      rw [ite_eq_left hzj, hzj, zero_add, norm_smul,
        Real.norm_of_nonneg (le_of_lt (htpos k)), norm_one, mul_one]
      linarith [htpos k, h0]
    · -- `z j ≠ 0`, so the `j`-th coordinate is scaled by `1 + t k > 1`.
      have hpos : 0 < ‖z j‖ := norm_pos_iff.mpr hzj
      have hEq : z j + t k • z j = (1 + t k) • z j := by rw [add_smul, one_smul]
      rw [ite_eq_right hzj, hEq, norm_smul, Real.norm_of_nonneg (by linarith [htpos k])]
      nlinarith [hj, hpos, htpos k, norm_nonneg (z j)]
  have htend : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    simpa [t, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hzk_tend : Tendsto zk atTop (𝓝 z) := by
    have h2 : Tendsto (fun k => t k • w) atTop (𝓝 ((0 : ℝ) • w)) := htend.smul_const w
    have h3 : Tendsto (fun k => z + t k • w) atTop (𝓝 (z + (0 : ℝ) • w)) :=
      tendsto_const_nhds.add h2
    simpa [zk] using h3
  -- Step 3: the zero set of the iterated derivative is closed.
  have hclosed : IsClosed {y : Fin n → ℂ | iteratedFDeriv ℝ m f y = 0} :=
    isClosed_eq hf.continuous_iteratedFDeriv' continuous_const
  have hzmem : z ∈ {y : Fin n → ℂ | iteratedFDeriv ℝ m f y = 0} :=
    hclosed.mem_of_tendsto hzk_tend
      (Eventually.of_forall fun k => hzero_of_lt (zk k) (hzk_mem k))
  have hz0 : iteratedFDeriv ℝ m f z = 0 := hzmem
  rw [hz0]
  simp

end Work.NN.Core
