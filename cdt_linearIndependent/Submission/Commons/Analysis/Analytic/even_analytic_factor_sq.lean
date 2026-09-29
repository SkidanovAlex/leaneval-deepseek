import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Even analytic functions factor through the square map

If `f` is analytic at `0` and even in a neighbourhood of `0`
(`f (-z) = f z`), then `f` factors as `f z = g (z ^ 2)` for some function
`g` analytic at `0` (with `g 0 = f 0`).

The proof uses formal power series: an analytic function has a convergent
power series `p` around `0`, evenness forces the odd coefficients of `p` to
vanish, and the even subseries `q` (with `q.coeff n = p.coeff (2n)`) has
positive radius of convergence.  Then `g = q.sum` is analytic at `0` and
satisfies `g (z ^ 2) = f z` near `0`.
-/

namespace Commons.Analysis.Analytic

open Filter Metric
open scoped Topology ENNReal NNReal

section Definitions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The formal power series consisting of the even-degree terms of `p`
(`(evenPart p).coeff n = p.coeff (2n)`). -/
noncomputable def evenPart (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) :
    FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
  fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff (2 * n))

end Definitions

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

section Subseries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The even subseries of a series with positive radius of convergence again
has positive radius of convergence. -/
private lemma evenPart_radius_pos (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) (hp : 0 < p.radius) :
    0 < (evenPart p).radius := by
  classical
  obtain ⟨ρ, hρpos, hρlt⟩ : ∃ ρ : ℝ≥0, 0 < ρ ∧ (ρ : ℝ≥0∞) < p.radius := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp with ⟨ρ, hρ0, hρlt⟩
    exact ⟨ρ, ENNReal.coe_pos.mp hρ0, hρlt⟩
  obtain ⟨C, hCpos, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ n, ‖p n‖ * (ρ : ℝ) ^ n ≤ C := by
    rcases p.norm_mul_pow_le_of_lt_radius hρlt with ⟨C, hCpos, hC⟩
    exact ⟨C, hCpos, hC⟩
  let q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := evenPart p
  let r : ℝ≥0 := ρ ^ 2
  have hnorm : ∀ k : ℕ, ‖q k‖ = ‖p (2 * k)‖ := by
    intro k
    dsimp [q, evenPart]
    rw [ContinuousMultilinearMap.norm_mkPiRing]
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  have hpow : ∀ k : ℕ, (r : ℝ) ^ k = (ρ : ℝ) ^ (2 * k) := by
    intro k
    dsimp [r]
    rw [← pow_mul (ρ : ℝ) 2 k]
  have hb : ∀ k : ℕ, ‖q k‖ * (r : ℝ) ^ k ≤ C := by
    intro k
    calc
      ‖q k‖ * (r : ℝ) ^ k = ‖p (2 * k)‖ * (ρ : ℝ) ^ (2 * k) := by
        rw [hnorm k, hpow k]
      _ ≤ C := hC (2 * k)
  have hle : ((r : ℝ≥0) : ℝ≥0∞) ≤ q.radius := q.le_radius_of_bound C hb
  have hrpos : 0 < r := by
    dsimp [r]
    exact pow_pos hρpos 2
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hrpos) hle

end Subseries

section Main

/-- If an analytic function `f` near `0` is even, then it factors through the
square map: there is `g` analytic at `0` with `g (z ^ 2) = f z` for `z` in a
neighbourhood of `0`, and `g 0 = f 0`. -/
theorem even_analytic_factor_sq {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f 0)
    (heven : ∀ᶠ z in 𝓝 (0 : 𝕜), f (-z) = f z) :
    ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g 0 ∧ g 0 = f 0 ∧
      ∀ᶠ z in 𝓝 (0 : 𝕜), g (z ^ 2) = f z := by
  classical
  rcases hf with ⟨p, hfp0⟩
  have hodd : ∀ n : ℕ, Odd n → p.coeff n = 0 := odd_coeff_eq_zero_of_even hfp0 heven
  let q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := evenPart p
  let g : 𝕜 → 𝕜 := q.sum
  have hqpos : 0 < q.radius := by
    simpa [q] using evenPart_radius_pos p hfp0.radius_pos
  have hg_pow : HasFPowerSeriesAt g q 0 := by
    exact (q.hasFPowerSeriesOnBall hqpos).hasFPowerSeriesAt
  have hg_analytic : AnalyticAt 𝕜 g 0 := hg_pow.analyticAt
  have hqcoeff : ∀ k : ℕ, q.coeff k = p.coeff (2 * k) := by
    intro k
    unfold q evenPart
    unfold FormalMultilinearSeries.coeff
    change ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) (p.coeff (2 * k)) (fun _ : Fin k => (1 : 𝕜)) = p.coeff (2 * k)
    rw [ContinuousMultilinearMap.mkPiRing_apply]
    simp
  rcases hfp0 with ⟨r, hfr⟩
  have hg0 : g 0 = f 0 := by
    have hf0 : f 0 = p.coeff 0 := by
      have hcv := hfr.coeff_zero (fun _ : Fin 0 => (0 : 𝕜))
      have hp0v : p 0 (fun _ : Fin 0 => (0 : 𝕜)) = p.coeff 0 := by
        rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
        simp
      exact (hcv.symm.trans hp0v)
    have hgq0 : q.sum 0 = q.coeff 0 := by
      have hcv := (q.hasFPowerSeriesOnBall hqpos).coeff_zero (fun _ : Fin 0 => (0 : 𝕜))
      have hq0v : q 0 (fun _ : Fin 0 => (0 : 𝕜)) = q.coeff 0 := by
        rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
        simp
      exact (hcv.symm.trans hq0v)
    have hqc0 : q.coeff 0 = p.coeff 0 := by
      simpa using hqcoeff 0
    simp [g, hgq0, hqc0, hf0]
  have heq : ∀ᶠ z in 𝓝 (0 : 𝕜), g (z ^ 2) = f z := by
    filter_upwards [Metric.eball_mem_nhds (0 : 𝕜) hfr.r_pos] with z hz
    have hzsum : HasSum (fun n : ℕ => p n (fun _ => z)) (f z) := by
      simpa using hfr.hasSum hz
    have huz : HasSum (fun m : ℕ => z ^ m • p.coeff m) (f z) := by
      simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using hzsum
    have hoddz : ∀ k : ℕ, (fun m : ℕ => z ^ m • p.coeff m) (2 * k + 1) = 0 := by
      intro k
      have hc : p.coeff (2 * k + 1) = 0 := hodd (2 * k + 1) ⟨k, rfl⟩
      simp [hc]
    have hve : HasSum (fun k : ℕ => z ^ (2 * k) • p.coeff (2 * k)) (f z) := by
      simpa using (hasSum_even_subsequence (u := fun m : ℕ => z ^ m • p.coeff m) huz hoddz)
    have hqz : HasSum (fun k : ℕ => q k (fun _ => z ^ 2)) (f z) := by
      apply hve.congr_fun
      intro k
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
      rw [pow_mul z 2 k]
      rw [← hqcoeff k]
    have hqsum : q.sum (z ^ 2) = f z := by
      simpa [FormalMultilinearSeries.sum] using hqz.tsum_eq
    simpa [g] using hqsum
  exact ⟨g, hg_analytic, hg0, heq⟩

end Main

end Commons.Analysis.Analytic