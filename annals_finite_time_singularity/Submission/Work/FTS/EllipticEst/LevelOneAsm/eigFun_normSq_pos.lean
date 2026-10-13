/-
Copyright: work module for the Elgindi finite-time singularity project.

# `LevelOneAsm/eigFun_normSq_pos`: the angular eigenfunctions have positive norm

`Work.FTS.EllipticEst.LevelOneAsm.eigFun_normSq_pos`:

  `0 < ∫_{Iθ} Θ_n(θ)² cos θ dθ`   for `n ≥ 1`,

with `Θ_n(θ) = cos θ · p_n(sin θ)` the angular eigenfunctions of `EigBasis`
(`p_n(u) = Σ_{k<n} c_k u^{2k+1}`, `c_0 = 1`, `Θ_n = eigFun n`).

## The proof

`(Θ_n θ)² cos θ = cos³θ · p_n(sin θ)²`, so the substitution `u = sin θ`
(`Work.FTS.EllipticEst.LevelOneAsm.subst_cos_cube_sin`) turns the angular integral into

  `∫_0^1 (1 - u²) p_n(u)² du`.

On `[0,1]` the integrand is nonnegative, and it is strictly positive on a small interval
`(0, δ)`: factor `p_n(u) = u · R_n(u)` with `R_n(u) = Σ_{k<n} c_k u^{2k}`.  The polynomial
`R_n` is continuous with `R_n(0) = c_0 = 1 > 0`, hence `R_n > 0` on some neighbourhood of
`0` (this is the only place where `n ≥ 1` is used: it makes the `k = 0` term present and
`R_0 ≡ 0` is excluded).  For `0 < u < δ ≤ 1` both factors `u` and `R_n(u)` are positive, and
`1 - u² > 0` as well, so the integrand is positive on `(0, δ)`.

`intervalIntegral.intervalIntegral_pos_of_pos_on` then gives `0 < ∫_0^δ`, and the split
`∫_0^1 = ∫_0^δ + ∫_δ^1` with a nonnegative second term finishes the proof.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_moment
import Submission.Work.FTS.EllipticEst.LevelOneAsm.subst_cos_cube_sin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

/-- `eigPoly n` is continuous (it is the polynomial `u ↦ Σ_{k<n} c_k u^{2k+1}`).

(Kept `private`: a public `continuous_eigPoly` already exists in
`Cores/eigPolyCos3Cross.lean`, and importing both modules would clash.) -/
private lemma continuous_eigPoly (n : ℕ) : Continuous (eigPoly n) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom n u).continuousAt

/-- `R_n(u) = Σ_{k<n} c_k u^{2k}`, the cofactor of the simple root of `p_n` at `u = 0`. -/
private def eigPolyQuot (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, eigCoef n k * u ^ (2 * k)

/-- The factorisation `p_n(u) = u · R_n(u)`. -/
private lemma eigPoly_eq_mul_quot (n : ℕ) (u : ℝ) : eigPoly n u = u * eigPolyQuot n u := by
  unfold eigPolyQuot
  rw [eigPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ']
  ring

/-- `R_n(0) = c_0 = 1` (this uses `n ≥ 1`: the sum must be nonempty). -/
private lemma eigPolyQuot_zero (n : ℕ) (hn : 1 ≤ n) : eigPolyQuot n 0 = 1 := by
  have h := Finset.sum_eq_single (s := Finset.range n) (a := 0)
    (f := fun k => eigCoef n k * (0 : ℝ) ^ (2 * k))
    (fun k _ hk => by rw [zero_pow (by omega : 2 * k ≠ 0), mul_zero])
    (fun h => absurd (Finset.mem_range.mpr (by omega : 0 < n)) h)
  simpa [eigPolyQuot] using h

/-- `R_n` is continuous. -/
private lemma continuous_eigPolyQuot (n : ℕ) : Continuous (eigPolyQuot n) := by
  unfold eigPolyQuot
  refine continuous_finsetSum (Finset.range n)
    (f := fun k u => eigCoef n k * u ^ (2 * k)) fun k _ => ?_
  exact continuous_const.mul (continuous_id.pow (2 * k))

/-- **`p_n` is positive just to the right of `0`**: `R_n` is continuous with `R_n(0) = 1`, so
`R_n > 0` near `0`, and there `p_n(u) = u · R_n(u) > 0`. -/
private lemma eigPoly_pos_near_zero_aux (n : ℕ) (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ u : ℝ, 0 < u → u < δ → 0 < eigPoly n u := by
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, |u| ≤ ε → 0 < eigPolyQuot n u := by
    have hopen : IsOpen {u : ℝ | 0 < eigPolyQuot n u} :=
      IsOpen.preimage (continuous_eigPolyQuot n) isOpen_Ioi
    have hmem : {u : ℝ | 0 < eigPolyQuot n u} ∈ 𝓝 (0 : ℝ) :=
      hopen.mem_nhds (by
        show 0 < eigPolyQuot n 0
        rw [eigPolyQuot_zero n hn]
        norm_num)
    obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨η / 2, half_pos hηpos, fun u hu => hη ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith
  refine ⟨min ε 1, lt_min hεpos one_pos, min_le_right _ _, fun u hu0 huδ => ?_⟩
  rw [eigPoly_eq_mul_quot]
  refine mul_pos hu0 (hε u ?_)
  rw [abs_of_pos hu0]
  exact le_trans huδ.le (min_le_left _ _)

/-- The `u = sin θ` form of the angular norm square is positive:
`0 < ∫_0^1 (1 - u²) p_n(u)² du` for `n ≥ 1`. -/
private lemma eigPoly_normSq_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u) ^ 2 := by
  obtain ⟨δ, hδpos, hδ1, hδpost⟩ := eigPoly_pos_near_zero_aux n hn
  have hcont : Continuous fun u : ℝ => (1 - u ^ 2) * (eigPoly n u) ^ 2 :=
    (continuous_const.sub (continuous_id.pow 2)).mul ((continuous_eigPoly n).pow 2)
  have hpos : ∀ u ∈ Ioo (0 : ℝ) δ, 0 < (1 - u ^ 2) * (eigPoly n u) ^ 2 := by
    rintro u ⟨hu0, huδ⟩
    have hu1 : u < 1 := lt_of_lt_of_le huδ hδ1
    have h1 : 0 < 1 - u ^ 2 := by nlinarith
    exact mul_pos h1 (pow_pos (hδpost u hu0 huδ) 2)
  have hint : 0 < ∫ u in (0 : ℝ)..δ, (1 - u ^ 2) * (eigPoly n u) ^ 2 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable 0 δ) hpos hδpos
  have hsplit : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * (eigPoly n u) ^ 2)
      = (∫ u in (0 : ℝ)..δ, (1 - u ^ 2) * (eigPoly n u) ^ 2)
        + ∫ u in δ..1, (1 - u ^ 2) * (eigPoly n u) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 δ)
      (hcont.intervalIntegrable δ 1)).symm
  have h2 : 0 ≤ ∫ u in δ..1, (1 - u ^ 2) * (eigPoly n u) ^ 2 := by
    refine intervalIntegral.integral_nonneg hδ1 fun u hu => ?_
    have hu1 : u ≤ 1 := hu.2
    have hu0 : 0 ≤ u := (lt_of_lt_of_le hδpos hu.1).le
    exact mul_nonneg (by nlinarith) (sq_nonneg _)
  rw [hsplit]
  linarith

theorem eigFun_normSq_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.LevelOneAsm.eigFun n θ) ^ 2 * Real.cos θ := by
  have h1 : (∫ θ in Work.Spaces.Iθ, (eigFun n θ) ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Real.cos θ ^ 3 * (eigPoly n (Real.sin θ)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with θ
    simp only [eigFun]
    ring
  rw [h1, subst_cos_cube_sin (fun u : ℝ => (eigPoly n u) ^ 2) ((continuous_eigPoly n).pow 2)]
  exact eigPoly_normSq_pos n hn

end Work.FTS.EllipticEst.LevelOneAsm
