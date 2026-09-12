import Mathlib
import Submission.FeketeLim
import Submission.ModelStarExterior
import Submission.ModelStarShell
import Submission.ModelStarDisk
import Submission.Commons.Analysis.Complex.norm_le_of_tendsto_punctured
import Submission.Commons.Analysis.Polynomial.tendsto_pow_mul_eval_inv_mul

/-!
# ModelStarChebyshev -- the lower bound `t_N(M) ≥ 1` for the model star

STATUS: research isolate (NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r`, which is holomorphic on the exterior
`{1 < ‖z‖}`, continuous on `{1 ≤ ‖z‖}` and satisfies `F(z)/z → 1` at `∞`, every
monic polynomial `P` of degree `N` satisfies

    `sup {‖P w‖ : w ∈ M} ≥ 1`,  `M = F '' unitCircle`,

("the transfinite diameter of `M` is at least `1`", i.e. the easy half of
Fekete's theorem with capacity `1`).  The proof is the maximum principle on the
punctured disk applied to `u ↦ u^N P(F(u⁻¹))` (which tends to `1` at `0`,
because `F(z)/z → 1`), followed by a compactness limit.

Consequences: `1 ≤ chebyshevNumber M N` and, by the Fekete/Chebyshev comparison,
`1 ≤ feketeNumber M N` for all `N ≥ 1`.  The latter is the boundedness input
of the non-atomicity lemma in the `(N1)` programme.
-/

noncomputable section

open scoped Real BigOperators Topology ENNReal Polynomial
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarChebyshev

open Submission.ModelStarMap
open Submission.ModelStarExterior (unitCircle modelStarImage mem_circle)
open Submission.ModelStarDisk (diskPhi diskPhi_zero continuousAt_diskPhi)
open Submission.ModelStarShell (modelF_differentiableAt)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ}

/-- `u ↦ u^N · P(F(u⁻¹))` is complex differentiable on the punctured unit disk. -/
lemma differentiableAt_assembly (hunit : ∀ k, ‖z₀ k‖ = 1) (P : ℂ[X]) (N : ℕ) {u : ℂ}
    (hu0 : u ≠ 0) (hu1 : ‖u‖ < 1) :
    DifferentiableAt ℂ (fun u : ℂ => u ^ N * P.eval (modelF z₀ r u⁻¹)) u := by
  have hFpt : DifferentiableAt ℂ (modelF z₀ r) u⁻¹ := by
    refine modelF_differentiableAt z₀ r (z := u⁻¹) ?_
    intro k
    rw [norm_inv, hunit k]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hu1
  fun_prop

/-- The punctured limit at the origin of the same function is `1`. -/
lemma tendsto_assembly (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) {P : ℂ[X]}
    (hP : P.Monic) {N : ℕ} (hN : P.natDegree = N) :
    Filter.Tendsto (fun u : ℂ => u ^ N * P.eval (modelF z₀ r u⁻¹))
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 1) := by
  have hkey := Commons.Analysis.Polynomial.tendsto_pow_mul_eval_inv_mul hP hN
    (D := fun u : ℂ => diskPhi z₀ r u)
    (continuousAt_diskPhi z₀ r hunit hr (by norm_num : ‖(0 : ℂ)‖ ≤ 1))
    (diskPhi_zero z₀ r)
  refine hkey.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
  rw [Submission.ModelStarDisk.modelF_inv_eq z₀ r hu]

/-- **The maximum principle bound**: for `R > 1` there is a point of the circle
of radius `R` at which `‖P(F ·)‖ ≥ R^N`. -/
theorem exists_norm_eval_ge_of_monic (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k)
    {P : ℂ[X]} (hP : P.Monic) {N : ℕ} (hN : P.natDegree = N) {R : ℝ} (hR : 1 < R) :
    ∃ z ∈ Metric.sphere (0 : ℂ) R, R ^ N ≤ ‖P.eval (modelF z₀ r z)‖ := by
  have hRpos : 0 < R := lt_trans one_pos hR
  have hRinv0 : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hRinv1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  obtain ⟨u, hu, hle⟩ := Commons.Analysis.Complex.norm_le_of_tendsto_punctured
    (f := fun u : ℂ => u ^ N * P.eval (modelF z₀ r u⁻¹)) (L := 1)
    (fun u hu0 hu1 => differentiableAt_assembly hunit P N (norm_pos_iff.mp hu0) hu1)
    (tendsto_assembly hunit hr hP hN) hRinv0 hRinv1
  have hunorm : ‖u‖ = R⁻¹ := by
    rw [Metric.mem_sphere, dist_zero_right] at hu; exact hu
  have hpos : 0 < (R⁻¹) ^ N := by positivity
  have hone : ((R⁻¹) ^ N)⁻¹ = R ^ N := by rw [inv_pow, inv_inv]
  refine ⟨u⁻¹, ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right, norm_inv, hunorm, inv_inv]
  · rw [norm_mul, norm_pow, hunorm] at hle
    have h2 : ((R⁻¹) ^ N)⁻¹ ≤ ‖P.eval (modelF z₀ r u⁻¹)‖ := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      simpa only [norm_one, mul_comm] using hle
    rwa [hone] at h2

/-- **The lower bound `1`**: some point of the model star has `‖P‖ ≥ 1`. -/
theorem exists_mem_modelStarImage_norm_eval_ge_one (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 < r k) {P : ℂ[X]} (hP : P.Monic) {N : ℕ} (hN : P.natDegree = N) :
    ∃ w ∈ modelStarImage z₀ r, 1 ≤ ‖P.eval w‖ := by
  classical
  have hz : ∀ n : ℕ, ∃ z ∈ Metric.sphere (0 : ℂ) (1 + 1 / ((n : ℝ) + 1)),
      1 ≤ ‖P.eval (modelF z₀ r z)‖ := by
    intro n
    have hR : 1 < 1 + 1 / ((n : ℝ) + 1) := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨z, hz, hle⟩ := exists_norm_eval_ge_of_monic hunit hr hP hN hR
    exact ⟨z, hz, le_trans (one_le_pow₀ hR.le) hle⟩
  choose z hzsphere hzge using hz
  obtain ⟨a, ha, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded
    (s := Metric.closedBall (0 : ℂ) 2) (isCompact_closedBall (0 : ℂ) 2).isBounded (fun n => by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z n‖ = 1 + 1 / ((n : ℝ) + 1) := by
        have := hzsphere n
        rwa [Metric.mem_sphere, dist_zero_right] at this
      rw [h1]
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith)
  have ha1 : ‖a‖ = 1 := by
    have h1 : Tendsto (fun n : ℕ => ‖z (φ n)‖) atTop (𝓝 ‖a‖) :=
      (continuous_norm.tendsto a).comp hlim
    have h2 : Tendsto (fun n : ℕ => ‖z (φ n)‖) atTop (𝓝 1) := by
      have h3 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 1) := by
        have h4 : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
        have h5 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop h4
        simpa using tendsto_const_nhds.add h5
      refine h3.congr' ?_
      filter_upwards with n
      have h6 := hzsphere (φ n)
      rw [Metric.mem_sphere, dist_zero_right] at h6
      exact h6.symm
    exact tendsto_nhds_unique h1 h2
  refine ⟨modelF z₀ r a, ⟨a, ?_, rfl⟩, ?_⟩
  · rw [mem_circle, ha1]
  · have hFwithin : ContinuousWithinAt (modelF z₀ r) {z : ℂ | 1 ≤ ‖z‖} a :=
      (Submission.ModelStarExterior.modelF_continuousOn_closedExterior z₀ r hunit hr).continuousWithinAt
        (by rw [Set.mem_setOf_eq, ha1])
    have hlimWithin : Tendsto (z ∘ φ) atTop (𝓝[{z : ℂ | 1 ≤ ‖z‖}] a) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
      filter_upwards with n
      have h := hzsphere (φ n)
      rw [Metric.mem_sphere, dist_zero_right] at h
      show 1 ≤ ‖(z ∘ φ) n‖
      rw [Function.comp_apply, h]
      have h3 : (0 : ℝ) < 1 / ((φ n : ℝ) + 1) := by positivity
      linarith
    have hFa : Tendsto (fun n : ℕ => modelF z₀ r (z (φ n))) atTop (𝓝 (modelF z₀ r a)) :=
      hFwithin.tendsto.comp hlimWithin
    have hPe : Continuous (fun w : ℂ => P.eval w) := by fun_prop
    have htend : Tendsto (fun n : ℕ => ‖P.eval (modelF z₀ r (z (φ n)))‖) atTop
        (𝓝 ‖P.eval (modelF z₀ r a)‖) :=
      (hPe.continuousAt (x := modelF z₀ r a)).norm.tendsto.comp hFa
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (Eventually.of_forall (fun n => hzge (φ n)))


open Submission.FeketeLim (chebyshevNumber feketeNumber MonicDeg feketeNumber_one
  cheb_mul_le_fekete_succ_of_bounded chebyshevNumber_nonneg)

/-- **`t_N ≥ 1` for the model star.** -/
theorem one_le_chebyshevNumber_modelStar (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (N : ℕ) :
    1 ≤ chebyshevNumber (modelStarImage z₀ r) N := by
  have hK : IsCompact (modelStarImage z₀ r) :=
    Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr
  unfold chebyshevNumber
  refine le_csInf ?hne (fun c hc => ?_)
  · rcases hK.isBounded.exists_pos_norm_le with ⟨Rn, hRpos, hR⟩
    refine ⟨Rn ^ N, pow_nonneg hRpos.le N, (Polynomial.X : ℂ[X]) ^ N, ?_, ?_⟩
    · exact ⟨Polynomial.monic_X.pow N, Polynomial.natDegree_X_pow N⟩
    · intro z hz
      rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z) (hR z hz) N
  · obtain ⟨hc0, p, hp, hb⟩ := hc
    obtain ⟨w, hwM, hw⟩ := exists_mem_modelStarImage_norm_eval_ge_one hunit hr hp.1 hp.2
    exact le_trans hw (hb w hwM)

/-- **`m_N ≥ 1` for the model star** (the Fekete number is bounded below). -/
theorem one_le_feketeNumber_modelStar (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k)
    (hs : 0 < s) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ feketeNumber (modelStarImage z₀ r) N := by
  have hK : IsCompact (modelStarImage z₀ r) :=
    Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr
  have hne : (modelStarImage z₀ r).Nonempty :=
    ⟨0, ⟨z₀ ⟨0, hs⟩, Submission.ModelStarExterior.mem_circle.mpr (hunit _),
      Submission.ModelStarExterior.modelF_junction_eq_zero z₀ r hunit hr ⟨0, hs⟩⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  induction n with
  | zero => simpa using le_of_eq (feketeNumber_one hne).symm
  | succ k ih =>
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hpos : 0 < feketeNumber (modelStarImage z₀ r) (k + 1) :=
        lt_of_lt_of_le zero_lt_one (ih hk)
      have hstep := cheb_mul_le_fekete_succ_of_bounded hne hK.isBounded (n := k + 1) hk hpos
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ chebyshevNumber (modelStarImage z₀ r) (k + 1)
              * feketeNumber (modelStarImage z₀ r) (k + 1) :=
              mul_le_mul (one_le_chebyshevNumber_modelStar hunit hr (k + 1)) (ih hk)
                zero_le_one (chebyshevNumber_nonneg hK.isBounded hk)
        _ ≤ feketeNumber (modelStarImage z₀ r) ((k + 1) + 1) := hstep

end Submission.ModelStarChebyshev
