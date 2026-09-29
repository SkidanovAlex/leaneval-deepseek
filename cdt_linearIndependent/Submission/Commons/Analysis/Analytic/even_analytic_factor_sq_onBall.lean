import Mathlib
import Submission.Commons.Analysis.Analytic.even_analytic_factor_sq

/-!
# Even analytic functions factor through the square map, on a whole ball

Version of `even_analytic_factor_sq` with the *ball* statement: if `f` has the
power series `p` on the ball of (extended) radius `R` around `0` and is even
on that ball, then `f z = g (z ^ 2)` for a function `g` which has a power
series expansion on the ball of radius `R ^ 2`.

The proof is the same as for `even_analytic_factor_sq`, with two extra
analytic ingredients:

* the even subseries `q = evenPart p` has radius of convergence at least
  `R ^ 2` (shown by comparing coefficient bounds: a bound at radius `r` for
  `p` gives a bound at radius `r ^ 2` for the even terms);
* the equality `g (z ^ 2) = f z` holds for every `z` in the ball of radius
  `R`, by reindexing the (uniform) power series sum and using the vanishing
  of the odd coefficients of `p`.
-/

namespace Commons.Analysis.Analytic

open Filter Metric
open scoped Topology ENNReal NNReal

section Reindex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- If `u : ℕ → 𝕜` sums to `s` and all its odd-indexed terms vanish, then the
subsequence of even-indexed terms also sums to `s`. -/
private lemma hasSum_even_subsequence {u : ℕ → 𝕜} {s : 𝕜} (hu : HasSum u s)
    (hodd : ∀ k : ℕ, u (2 * k + 1) = 0) : HasSum (fun k : ℕ => u (2 * k)) s := by
  classical
  have hus : Summable u := hu.summable
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    exact Nat.mul_left_cancel (by norm_num) h
  have hv : Summable (fun k : ℕ => u (2 * k)) := hus.comp_injective hinj
  have hve : HasSum (fun k : ℕ => u (2 * k)) (∑' k : ℕ, u (2 * k)) := hv.hasSum
  have hoo : HasSum (fun k : ℕ => u (2 * k + 1)) 0 := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : 𝕜)) 0).congr_fun
    intro k
    simp [hodd k]
  have htotal : HasSum u ((∑' k : ℕ, u (2 * k)) + 0) := hve.even_add_odd hoo
  have ht : (∑' k : ℕ, u (2 * k)) = s := by simpa using (htotal.unique hu)
  simpa [ht] using hve

end Reindex

section OddCoefficients

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- An analytic function at `0` which is even in a neighbourhood of `0` has a
power series expansion at `0` whose odd coefficients all vanish. -/
private lemma odd_coeff_eq_zero_of_even {f : 𝕜 → 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 𝕜}
    (hfp : HasFPowerSeriesAt f p 0) (heven : ∀ᶠ z in 𝓝 (0 : 𝕜), f (-z) = f z) :
    ∀ n : ℕ, Odd n → p.coeff n = 0 := by
  have hA : ∀ᶠ z in 𝓝 (0 : 𝕜), HasSum (fun n : ℕ => z ^ n • p.coeff n) (f z) := by
    simpa using (hasFPowerSeriesAt_iff.mp hfp)
  have hAn : ∀ᶠ z in 𝓝 (0 : 𝕜),
      HasSum (fun n : ℕ => (-z) ^ n • p.coeff n) (f (-z)) := by
    have ht : Tendsto (fun z : 𝕜 => -z) (𝓝 (0 : 𝕜)) (𝓝 (0 : 𝕜)) := by
      simpa [neg_zero] using continuous_neg.tendsto (0 : 𝕜)
    exact ht.eventually hA
  let a : ℕ → 𝕜 := fun n => (1 - (-1 : 𝕜) ^ n) • p.coeff n
  have hmain : ∀ᶠ z in 𝓝 (0 : 𝕜),
      HasSum (fun n : ℕ => z ^ n • a n) (0 : 𝕜) := by
    filter_upwards [heven, hA, hAn] with z hev hzA hzAn
    have hAsub : HasSum (fun n : ℕ => z ^ n • p.coeff n - (-z) ^ n • p.coeff n)
        (f z - f (-z)) := hzA.sub hzAn
    have hz : HasSum (fun n : ℕ => z ^ n • ((1 - (-1 : 𝕜) ^ n) • p.coeff n))
        (f z - f (-z)) := by
      apply hAsub.congr_fun
      intro n
      rw [neg_pow]
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    simpa [a, hev] using hz
  let d : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
    fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a n)
  have hdcoeff : ∀ n : ℕ, d.coeff n = a n := by
    intro n
    unfold d
    unfold FormalMultilinearSeries.coeff
    change ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a n) (fun _ : Fin n => (1 : 𝕜)) = a n
    rw [ContinuousMultilinearMap.mkPiRing_apply]
    simp
  have hd : HasFPowerSeriesAt (fun _ : 𝕜 => (0 : 𝕜)) d 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hmain] with z hz
    apply hz.congr_fun
    intro n
    simp [hdcoeff]
  have hd0 : d = 0 := HasFPowerSeriesAt.eq_zero hd
  intro n hn
  have hdn : a n = 0 := by
    have h0 : d.coeff n = 0 :=
      (FormalMultilinearSeries.coeff_eq_zero (p := d)).2 (congrFun hd0 n)
    exact (hdcoeff n).symm.trans h0
  have hne : (1 - (-1 : 𝕜) ^ n) ≠ 0 := by
    have hneg : (-1 : 𝕜) ^ n = -1 := hn.neg_one_pow
    rw [hneg]
    have h2 : (2 : 𝕜) ≠ 0 := by exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)
    have : (1 - (-1 : 𝕜)) = (2 : 𝕜) := by norm_num
    rwa [this]
  exact (mul_eq_zero.mp (by simpa [a, smul_eq_mul] using hdn)).resolve_left hne

end OddCoefficients

section Radius

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `p` is bounded at radius `r`, then its even part is bounded at radius
`r ^ 2`; hence the radius of the even part is at least the square of the
radius of `p`. -/
private lemma evenPart_radius_ge_sq_of_lt (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < p.radius) :
    ((r ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ (evenPart p).radius := by
  rcases p.norm_mul_pow_le_of_lt_radius hr with ⟨C, hCpos, hC⟩
  let sr : ℝ≥0 := r ^ 2
  have hnorm : ∀ k : ℕ, ‖evenPart p k‖ = ‖p (2 * k)‖ := by
    intro k
    dsimp [evenPart]
    rw [ContinuousMultilinearMap.norm_mkPiRing]
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  have hpow : ∀ k : ℕ, (sr : ℝ) ^ k = (r : ℝ) ^ (2 * k) := by
    intro k
    dsimp [sr]
    rw [← pow_mul (r : ℝ) 2 k]
  have hb : ∀ k : ℕ, ‖evenPart p k‖ * (sr : ℝ) ^ k ≤ C := by
    intro k
    calc
      ‖evenPart p k‖ * (sr : ℝ) ^ k = ‖p (2 * k)‖ * (r : ℝ) ^ (2 * k) := by
        rw [hnorm k, hpow k]
      _ ≤ C := hC (2 * k)
  have hle : ((sr : ℝ≥0) : ℝ≥0∞) ≤ (evenPart p).radius :=
    (evenPart p).le_radius_of_bound C hb
  simpa [sr] using hle

/-- A square-root comparison in the extended nonnegative reals: from
`s < R ^ 2` (with `s : ℝ≥0`) one gets `√s < R`. -/
private lemma sqrt_lt_of_lt_sq {R : ℝ≥0∞} {s : ℝ≥0} (hs : (s : ℝ≥0∞) < R ^ 2) :
    (NNReal.sqrt s : ℝ≥0∞) < R := by
  by_cases htop : R = ∞
  · rw [htop]
    exact ENNReal.coe_lt_top
  · let c : ℝ≥0 := R.toNNReal
    have hc : (c : ℝ≥0∞) = R := ENNReal.coe_toNNReal htop
    rw [← hc] at hs ⊢
    rw [← ENNReal.coe_pow] at hs
    have hs' : s < c ^ 2 := ENNReal.coe_lt_coe.mp hs
    have hsc : NNReal.sqrt s < c := by
      have h1 : NNReal.sqrt s < NNReal.sqrt (c ^ 2) := (NNReal.sqrt_lt_sqrt).2 hs'
      simpa [NNReal.sqrt_sq] using h1
    exact ENNReal.coe_lt_coe.mpr hsc

/-- The even part of a formal power series has radius of convergence at least
the square of the radius of the original series. -/
private lemma evenPart_radius_ge_sq (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) :
    p.radius ^ 2 ≤ (evenPart p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt ?_
  intro s hs
  let t : ℝ≥0 := NNReal.sqrt s
  have htR : (t : ℝ≥0∞) < p.radius := by
    simpa [t] using (sqrt_lt_of_lt_sq (R := p.radius) hs)
  have hb : ((t ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ (evenPart p).radius :=
    evenPart_radius_ge_sq_of_lt p htR
  simpa [t, NNReal.sq_sqrt] using hb

end Radius

section Norms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The extended norm of a square is the square of the extended norm. -/
private lemma enorm_sq (z : 𝕜) : ‖z ^ 2‖ₑ = ‖z‖ₑ ^ 2 := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_pow, ← ENNReal.coe_pow]

/-- Squares of points of the ball of radius `R` lie in the ball of radius
`R ^ 2`. -/
private lemma sq_mem_eball_of_mem {R : ℝ≥0∞} {z : 𝕜} (hz : z ∈ Metric.eball (0 : 𝕜) R) :
    z ^ 2 ∈ Metric.eball (0 : 𝕜) (R ^ 2) := by
  rw [mem_eball_zero_iff]
  have hz' : ‖z‖ₑ < R := (mem_eball_zero_iff.mp hz)
  rw [enorm_sq]
  rw [pow_two, pow_two]
  exact ENNReal.mul_lt_mul hz' hz'

/-- Zero belongs to a ball of positive radius around zero. -/
private lemma zero_mem_eball {R : ℝ≥0∞} (hR : 0 < R) : (0 : 𝕜) ∈ Metric.eball (0 : 𝕜) R := by
  rw [mem_eball_zero_iff]
  simpa [enorm_eq_nnnorm] using hR

end Norms

section Main

/-- If `f` is analytic on the ball of radius `R` around `0` with power series
`p`, and even on that ball, then `f` factors through the square map: there is
`g` which is analytic (as a power series `q`) on the ball of radius `R ^ 2`,
with `g 0 = f 0` and `g (z ^ 2) = f z` for every `z` in the ball of radius
`R`. -/
theorem even_analytic_factor_sq_onBall {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R)
    (heven : ∀ z : 𝕜, z ∈ Metric.eball (0 : 𝕜) R → f (-z) = f z) :
    ∃ g : 𝕜 → 𝕜, ∃ q : FormalMultilinearSeries 𝕜 𝕜 𝕜,
      HasFPowerSeriesOnBall g q 0 (R ^ 2) ∧ g 0 = f 0 ∧
        ∀ z : 𝕜, z ∈ Metric.eball (0 : 𝕜) R → g (z ^ 2) = f z := by
  classical
  have hodd : ∀ n : ℕ, Odd n → p.coeff n = 0 := by
    apply odd_coeff_eq_zero_of_even hf.hasFPowerSeriesAt
    filter_upwards [Metric.eball_mem_nhds (0 : 𝕜) hf.r_pos] with z hz
    exact heven z hz
  let q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := evenPart p
  let g : 𝕜 → 𝕜 := q.sum
  have hqcoeff : ∀ k : ℕ, q.coeff k = p.coeff (2 * k) := by
    intro k
    unfold q evenPart
    unfold FormalMultilinearSeries.coeff
    change ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) (p.coeff (2 * k)) (fun _ : Fin k => (1 : 𝕜)) =
      p.coeff (2 * k)
    rw [ContinuousMultilinearMap.mkPiRing_apply]
    simp
  have hR2pos : 0 < R ^ 2 := by
    rw [pow_two]
    exact ENNReal.mul_pos (ne_of_gt hf.r_pos) (ne_of_gt hf.r_pos)
  have hqR : R ^ 2 ≤ q.radius := by
    have h := evenPart_radius_ge_sq (𝕜 := 𝕜) (p := p)
    -- h : p.radius ^ 2 ≤ (evenPart p).radius ; need R ^ 2 ≤ p.radius ^ 2 from hf.r_le
    have hmono : R ^ 2 ≤ p.radius ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul' hf.r_le hf.r_le
    simpa [q] using le_trans hmono h
  have hqpos : 0 < q.radius := lt_of_lt_of_le hR2pos hqR
  have hgball : HasFPowerSeriesOnBall g q 0 (R ^ 2) := by
    have hb : HasFPowerSeriesOnBall q.sum q 0 (R ^ 2) :=
      (q.hasFPowerSeriesOnBall hqpos).mono hR2pos hqR
    simpa [g] using hb
  have heq : ∀ z : 𝕜, z ∈ Metric.eball (0 : 𝕜) R → g (z ^ 2) = f z := by
    intro z hz
    have hzsq : z ^ 2 ∈ Metric.eball (0 : 𝕜) (R ^ 2) := sq_mem_eball_of_mem (𝕜 := 𝕜) hz
    have hgzs : HasSum (fun k : ℕ => q k (fun _ : Fin k => z ^ 2)) (g (z ^ 2)) := by
      simpa using hgball.hasSum hzsq
    have hfzs : HasSum (fun n : ℕ => p n (fun _ : Fin n => z)) (f z) := by
      simpa using hf.hasSum hz
    have huz : HasSum (fun m : ℕ => z ^ m • p.coeff m) (f z) := by
      simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using hfzs
    have hoddz : ∀ k : ℕ, (fun m : ℕ => z ^ m • p.coeff m) (2 * k + 1) = 0 := by
      intro k
      have hc : p.coeff (2 * k + 1) = 0 := hodd (2 * k + 1) ⟨k, rfl⟩
      simp [hc]
    have hve : HasSum (fun k : ℕ => z ^ (2 * k) • p.coeff (2 * k)) (f z) := by
      simpa using (hasSum_even_subsequence (u := fun m : ℕ => z ^ m • p.coeff m) huz hoddz)
    have hfqz : HasSum (fun k : ℕ => q k (fun _ : Fin k => z ^ 2)) (f z) := by
      apply hve.congr_fun
      intro k
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
      rw [pow_mul z 2 k]
      rw [← hqcoeff k]
    exact hgzs.unique hfqz
  have hg0 : g 0 = f 0 := by
    simpa using (heq 0 (zero_mem_eball (𝕜 := 𝕜) hf.r_pos))
  exact ⟨g, q, hgball, hg0, heq⟩

end Main

end Commons.Analysis.Analytic
