/-
  Area `WilC4aRW`: complexifying a real power series.

  Given a real power series `p` on `ℝ^N` of positive radius, this file builds its
  complexification `cplxSeries p` on `ℂ^N`: the complex power series obtained by reading the
  same coefficients in the standard basis at the complex argument.  The two facts needed by
  `Work.WilC4aRW.Extend.complexify` are

  * `cplxSeries_apply_diag`: on real points `cplxIncl x`, the `n`-th term of `cplxSeries p`
    agrees with the `n`-th term of the real series `p`;
  * `norm_cplxSeries_le`: `‖cplxSeries p n‖ ≤ N^n * ‖p n‖`, hence the complexified series has
    positive radius whenever `p` does (`cplxSeries_radius_pos`, `le_radius_cplxSeries`).
-/
import Mathlib
import Submission.Work.WilC4aRW.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators NNReal ENNReal

namespace Work.WilC4aRW.Extend

open ContinuousMultilinearMap

/-! ## 1. The complexified power series -/

/-- The monomial `ℂ`-multilinear map `(v_k)_{k<n} ↦ ∏_k v_k (i k)` on `(ℂ^N)^n`. -/
def monomialML {N : ℕ} (n : ℕ) (i : Fin n → Fin N) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => (Fin N → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
    (fun k => ContinuousLinearMap.proj (R := ℂ) (i k))

@[simp] theorem monomialML_apply {N : ℕ} (n : ℕ) (i : Fin n → Fin N)
    (v : Fin n → Fin N → ℂ) :
    monomialML n i v = ∏ k, v k (i k) := by
  simp [monomialML, List.prod_ofFn]

/-- The complexification of a real formal power series on `ℝ^N`: the power series with the
same coefficients, read on the standard basis of `ℂ^N`. -/
def cplxSeries {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) :
    FormalMultilinearSeries ℂ (Fin N → ℂ) ℂ :=
  fun n => ∑ i : Fin n → Fin N,
    ((p n (fun k => Pi.single (i k) (1 : ℝ))) : ℂ) • monomialML n i

theorem cplxSeries_apply {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ)
    (v : Fin n → Fin N → ℂ) :
    cplxSeries p n v = ∑ i : Fin n → Fin N,
      ((p n (fun k => Pi.single (i k) (1 : ℝ))) : ℂ) * ∏ k, v k (i k) := by
  simp [cplxSeries, smul_eq_mul]

/-! ## 2. The diagonal of the complexified series and the norms -/

theorem sum_single_expand {N : ℕ} (x : Fin N → ℝ) :
    x = ∑ j : Fin N, x j • Pi.single j (1 : ℝ) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have h := Fintype.sum_pi_single i x
  simp only [Pi.single_apply] at h
  exact h.symm

/-- Expansion of a continuous multilinear form on `ℝ^N` in the standard basis. -/
theorem map_diag_expand {N n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin N → ℝ)) ℝ) (x : Fin N → ℝ) :
    A (fun _ : Fin n => x) =
      ∑ i : Fin n → Fin N, (∏ k, x (i k)) • A (fun k => Pi.single (i k) (1 : ℝ)) := by
  have hx : (fun _ : Fin n => x) =
      (fun k : Fin n => ∑ j : Fin N, x j • Pi.single j (1 : ℝ)) := by
    funext k; exact sum_single_expand x
  rw [hx]
  rw [show A (fun k : Fin n => ∑ j : Fin N, x j • Pi.single j (1 : ℝ)) =
      ∑ i : Fin n → Fin N, A (fun k => x (i k) • Pi.single (i k) (1 : ℝ)) from
    MultilinearMap.map_sum A.toMultilinearMap (fun k j => x j • Pi.single j (1 : ℝ))]
  exact Finset.sum_congr rfl fun i _ =>
    MultilinearMap.map_smul_univ A.toMultilinearMap (fun k => x (i k))
      (fun k => Pi.single (i k) (1 : ℝ))

/-- On real points, the terms of the complexified series are the real terms. -/
theorem cplxSeries_apply_diag {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ)
    (x : Fin N → ℝ) :
    cplxSeries p n (fun _ : Fin n => cplxIncl x) = (p n (fun _ : Fin n => x) : ℂ) := by
  rw [cplxSeries_apply, map_diag_expand (p n) x, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_prod]
  simp only [cplxIncl_apply]
  exact mul_comm _ _

theorem norm_proj_le_one {N : ℕ} (j : Fin N) :
    ‖(ContinuousLinearMap.proj (R := ℂ) j : (Fin N → ℂ) →L[ℂ] ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x j

theorem norm_monomialML_le {N : ℕ} (n : ℕ) (i : Fin n → Fin N) : ‖monomialML n i‖ ≤ 1 := by
  rw [monomialML]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin, one_mul]
  exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => norm_proj_le_one (i k))

/-- The operator norm of the `n`-th term of the complexified series is bounded by `N^n` times
the operator norm of the `n`-th term of the real series. -/
theorem norm_cplxSeries_le {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) (n : ℕ) :
    ‖cplxSeries p n‖ ≤ (N : ℝ) ^ n * ‖p n‖ := by
  rw [cplxSeries]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i : Fin n → Fin N,
      ‖((p n (fun k => Pi.single (i k) (1 : ℝ))) : ℂ) • monomialML n i‖ ≤ ‖p n‖ := by
    intro i
    have h2 : ‖p n (fun k => Pi.single (i k) (1 : ℝ))‖ ≤ ‖p n‖ := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
      simp only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one]
    calc ‖((p n (fun k => Pi.single (i k) (1 : ℝ))) : ℂ) • monomialML n i‖
        = ‖((p n (fun k => Pi.single (i k) (1 : ℝ))) : ℂ)‖ * ‖monomialML n i‖ :=
          norm_smul _ _
      _ = ‖p n (fun k => Pi.single (i k) (1 : ℝ))‖ * ‖monomialML n i‖ := by simp
      _ ≤ ‖p n‖ * 1 := mul_le_mul h2 (norm_monomialML_le n i) (norm_nonneg _) (norm_nonneg _)
      _ = ‖p n‖ := mul_one _
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  have hconst : ∑ _i : Fin n → Fin N, ‖p n‖ = (N : ℝ) ^ n * ‖p n‖ := by
    have hcard : (Finset.univ : Finset (Fin n → Fin N)).card = N ^ n := by
      simp
    rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_pow]
  rw [hconst]

/-- If `↑ε < p.radius` then the complexified series converges at least on the ball of radius
`ε / (N+1)`. -/
theorem le_radius_cplxSeries {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ) {ε : ℝ≥0}
    (hε : (ε : ℝ≥0∞) < p.radius) :
    ((ε / (N + 1) : ℝ≥0) : ℝ≥0∞) ≤ (cplxSeries p).radius := by
  set s : ℝ≥0 := ε / (N + 1) with hsdef
  have hsN : (N : ℝ≥0) * s ≤ ε := by
    have h1 : (N : ℝ≥0) * s ≤ (N + 1) * s := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ≥0) ≤ s)
      exact_mod_cast Nat.le_succ N
    have h2 : (N + 1) * s = ε := by
      rw [hsdef, mul_div_cancel₀ ε (by positivity : (N + 1 : ℝ≥0) ≠ 0)]
    exact h1.trans_eq h2
  have hsum : Summable fun n : ℕ => ‖cplxSeries p n‖ * (s : ℝ) ^ n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (p.summable_norm_mul_pow (r := (N : ℝ≥0) * s)
        (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hsN) hε))
    have hcoe : (((N : ℝ≥0) * s : ℝ≥0) : ℝ) = (N : ℝ) * (s : ℝ) := by
      simp [NNReal.coe_mul]
    calc ‖cplxSeries p n‖ * (s : ℝ) ^ n
        ≤ ((N : ℝ) ^ n * ‖p n‖) * (s : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (norm_cplxSeries_le p n) (by positivity)
      _ = ‖p n‖ * (((N : ℝ≥0) * s : ℝ≥0) : ℝ) ^ n := by
          rw [hcoe, mul_pow]; ring
  exact (cplxSeries p).le_radius_of_summable hsum

/-- The complexified series has positive radius whenever the real one does. -/
theorem cplxSeries_radius_pos {N : ℕ} (p : FormalMultilinearSeries ℝ (Fin N → ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (cplxSeries p).radius := by
  obtain ⟨ε, hεpos, hεlt⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ (ε : ℝ≥0∞) < p.radius := by
    obtain ⟨r, hr0, hrb⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp (show (0 : ℝ≥0∞) < p.radius from hp)
    exact ⟨r, ENNReal.coe_pos.mp hr0, hrb⟩
  refine lt_of_lt_of_le ?_ (le_radius_cplxSeries p hεlt)
  exact ENNReal.coe_pos.mpr (div_pos hεpos (by positivity))

end Work.WilC4aRW.Extend
