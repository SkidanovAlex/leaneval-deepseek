import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

namespace Work.BourgainPlan.Maximal

/-!
# Convergence of the partial block-symbol sums `mtaBlkSymSum` to `mtaFullSym`

The partial sum `mtaBlkSymSum P K ε S ξ = Σ_{|s| ≤ S} mtaBlkSym P K ε s ξ` of the block symbols
telescopes (see `mtaBlkSymSum_eq`) to

`Σ_{k<K} ε k · μ_k(ξ) · (θ (2^{dk - S} ξ) − θ (2^{dk + S + 1} ξ))`,

where `θ = dyadTheta` is the smooth bump of `exists_dyadic_frequency_bump`.  For every fixed `ξ` and
every `k` the first factor tends to `1` and the second to `0` as `S → ∞` (indeed the dyadic frequency
runs off to `−∞`, resp. `+∞`), so the partial sum converges to `Σ_{k<K} ε k · μ_k(ξ) = mtaFullSym`.
-/

open Filter Finset

/-- At frequency `0` the symbol `μ_k` vanishes (because `polyProfile` is `1` there). -/
lemma muSym_zero (P : Polynomial ℤ) (k : ℕ) : muSym P k 0 = 0 := by
  simp [muSym, polyProfile_zero]

/-- For every finite scale `c` the dyadic argument `2^{c - S} ξ` lands in the region `|·| ≤ 1`
eventually, where `dyadTheta = 1`. -/
lemma eventually_dyadTheta_small_eq_one (ξ : ℝ) (c : ℤ) :
    ∀ᶠ S : ℕ in Filter.atTop, dyadTheta ((2:ℝ)^(c + -(S:ℤ)) * ξ) = 1 := by
  have hpow : Filter.Tendsto (fun S : ℕ => ((2:ℝ)^S)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hf : Filter.Tendsto (fun S : ℕ => (2:ℝ)^(c + -(S:ℤ))) Filter.atTop (nhds 0) := by
    have hfun : (fun S : ℕ => (2:ℝ)^(c + -(S:ℤ))) = fun S : ℕ => (2:ℝ)^c * ((2:ℝ)^S)⁻¹ := by
      funext S
      rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_neg, zpow_natCast]
    rw [hfun]
    simpa using (tendsto_const_nhds.mul hpow :
      Filter.Tendsto (fun S : ℕ => (2:ℝ)^c * ((2:ℝ)^S)⁻¹) _ (nhds ((2:ℝ)^c * 0)))
  have hmul : Filter.Tendsto (fun S : ℕ => (2:ℝ)^(c + -(S:ℤ)) * |ξ|) Filter.atTop (nhds 0) := by
    simpa using hf.mul_const |ξ|
  filter_upwards [hmul.eventually_lt_const (show (0:ℝ) < 1 by norm_num)] with S hS
  refine dyadTheta_spec.2.2.1 _ ?_
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _)]
  linarith

/-- For every finite scale `c` and every `ξ ≠ 0` the dyadic argument `2^{c + S + 1} ξ` leaves the
region `|·| ≤ 2` eventually, where `dyadTheta = 0`. -/
lemma eventually_dyadTheta_large_eq_zero (ξ : ℝ) (c : ℤ) (hξ : ξ ≠ 0) :
    ∀ᶠ S : ℕ in Filter.atTop, dyadTheta ((2:ℝ)^(c + ((S:ℤ)+1)) * ξ) = 0 := by
  have hpow : Filter.Tendsto (fun S : ℕ => (2:ℝ)^(c + ((S:ℤ)+1))) Filter.atTop Filter.atTop := by
    have hfun : (fun S : ℕ => (2:ℝ)^(c + ((S:ℤ)+1))) = fun S : ℕ => (2:ℝ)^(c+1) * (2:ℝ)^S := by
      funext S
      have h : c + ((S:ℤ)+1) = (c+1) + (S:ℤ) := by ring
      rw [h, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_natCast]
    rw [hfun]
    exact Filter.Tendsto.const_mul_atTop (zpow_pos (by norm_num : (0:ℝ) < 2) _)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hbig : Filter.Tendsto (fun S : ℕ => (2:ℝ)^(c + ((S:ℤ)+1)) * |ξ|) Filter.atTop Filter.atTop :=
    hpow.atTop_mul_const (abs_pos.mpr hξ)
  filter_upwards [hbig.eventually_ge_atTop 2] with S hS
  refine dyadTheta_spec.2.2.2.1 _ ?_
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) _)]
  linarith

/-- At frequency `0` the partial block-symbol sum equals the full symbol: both sides reduce to `0`,
the telescoped bump factor being `θ 0 − θ 0 = 0` and `μ_k(0) = 0`. -/
lemma mtaBlkSymSum_zero (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (S : ℕ) :
    mtaBlkSymSum P K ε S 0 = mtaFullSym P K ε 0 := by
  rw [mtaBlkSymSum_eq, mtaFullSym]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [muSym, polyProfile_zero, dyadTheta_spec.2.2.1]

theorem mtaBlkSymSum_tendsto (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (ξ : ℝ) :
    Filter.Tendsto (fun S : ℕ => Work.BourgainPlan.Maximal.mtaBlkSymSum P K ε S ξ) Filter.atTop
      (nhds (Work.BourgainPlan.Maximal.mtaFullSym P K ε ξ)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    have h : (fun S : ℕ => mtaBlkSymSum P K ε S 0) = fun _ => mtaFullSym P K ε 0 :=
      funext (fun S => mtaBlkSymSum_zero P K ε S)
    rw [h]
    exact tendsto_const_nhds
  · have hcongr : ∀ᶠ S : ℕ in Filter.atTop,
        mtaFullSym P K ε ξ = mtaBlkSymSum P K ε S ξ := by
      have h1 : ∀ᶠ S : ℕ in Filter.atTop, ∀ k ∈ Finset.range K,
          dyadTheta ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ) + -(S:ℤ)) * ξ) = 1 := by
        rw [Finset.eventually_all]
        exact fun k _ => eventually_dyadTheta_small_eq_one ξ ((P.natDegree:ℤ)*(k:ℤ))
      have h2 : ∀ᶠ S : ℕ in Filter.atTop, ∀ k ∈ Finset.range K,
          dyadTheta ((2:ℝ)^((P.natDegree:ℤ)*(k:ℤ) + ((S:ℤ)+1)) * ξ) = 0 := by
        rw [Finset.eventually_all]
        exact fun k _ => eventually_dyadTheta_large_eq_zero ξ ((P.natDegree:ℤ)*(k:ℤ)) hξ
      filter_upwards [h1, h2] with S hS1 hS2
      have hmain : mtaBlkSymSum P K ε S ξ = mtaFullSym P K ε ξ := by
        rw [mtaBlkSymSum_eq, mtaFullSym]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [hS1 k hk, hS2 k hk]
        simp
      exact hmain.symm
    exact Filter.Tendsto.congr' hcongr tendsto_const_nhds

end Work.BourgainPlan.Maximal
