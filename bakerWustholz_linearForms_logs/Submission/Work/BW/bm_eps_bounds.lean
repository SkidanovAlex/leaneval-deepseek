import Mathlib
import Submission.Work.BW.bm_base
import Submission.Work.BW.mahlerDefs
import Submission.Work.BW.mahler_numeric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- **Bounds on the normalising parameters** (Blanksby–Montgomery, Acta Arith. 18 (1971), §3).

Let `P ∈ ℤ[X]` be monic of degree `n = 2N` with `N ≥ 2` and Mahler measure
`M(P) ≤ 1 + 1/(52 n log 6n)`, and let `w : Fin N → ℂ` represent the `N` inverse pairs of roots,
so that `∏_j ‖w_j‖ = M(P)^{-1}` (hypothesis `hprod`).  Put `ρ' = rhoP N = 1 - 1/(12N)`,
`K = KK N = ⌊(54/5)·N·log(12N)⌋₊` and `ε_j := min ρ' (‖w_j‖^K)`.  Then `exp(-1/A0) ≤ ε_j` for
every `j` (with `A0 = 48/5`), `ε_j ≤ ρ'`, and `exp(-2/A0) ≤ ∏_j ε_j`.

Maths: `∏_j ‖w_j‖ = M^{-1}` gives `‖w_j‖ ≥ M^{-1}`, hence `‖w_j‖^K ≥ M^{-K} ≥ exp(-1/A0)`,
because `K·log M(P) ≤ 1/A0` follows from `M(P) ≤ 1 + 1/(52·2N·log 12N)`, `log(1+x) ≤ x`, and
`A0·K ≤ 52·2N·log(12N)` (from `Work.BW.mahler_numeric`); also `ρ' ≥ 11/12 ≥ exp(-1/A0)`.  For the
product, `min a b ≥ a·b` for `a,b ∈ [0,1]` gives
`∏_j ε_j ≥ (ρ')^N · M^{-K} ≥ (11/12)·exp(-1/A0) ≥ exp(-2/A0)` (Bernoulli). -/
theorem bm_eps_bounds (P : Polynomial ℤ) (hP : P.Monic)
    (hM : (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      1 + 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ))))
    {N : ℕ} (hN : 2 ≤ N) (hN2 : P.natDegree = 2 * N) (w : Fin N → ℂ)
    (hw1 : ∀ j, ‖w j‖ ≤ 1)
    (hprod : (∏ j, ‖w j‖)⁻¹ = (P.map (Int.castRingHom ℂ)).mahlerMeasure) :
    (∀ j, Real.exp (-(1/A0)) ≤ min (rhoP N) (‖w j‖ ^ (KK N)))
    ∧ (∀ j, min (rhoP N) (‖w j‖ ^ (KK N)) ≤ rhoP N)
    ∧ Real.exp (-(2/A0)) ≤ ∏ j, min (rhoP N) (‖w j‖ ^ (KK N)) := by
  -- ## Step 1: `K · log M(P) ≤ 1/A₀`
  have hMpos : 0 < (P.map (Int.castRingHom ℂ)).mahlerMeasure :=
    lt_of_lt_of_le zero_lt_one (one_le_mahler P hP)
  have hn : (P.natDegree : ℝ) = 2 * (N : ℝ) := by rw [hN2]; push_cast; ring
  have hnum : (KK N : ℝ) * Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure) ≤ 1 / A0 := by
    set c : ℝ := 52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ)) with hcdef
    have hN2r : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hnpos : (0:ℝ) < (P.natDegree : ℝ) := by rw [hn]; linarith
    have hcpos : 0 < c := by
      rw [hcdef]
      have h1 : (1:ℝ) < 6 * (P.natDegree : ℝ) := by rw [hn]; linarith
      exact mul_pos (mul_pos (by norm_num) hnpos) (Real.log_pos h1)
    have hnum' : A0 * (KK N : ℝ) ≤ c := by
      rw [hcdef, hn]; exact (mahler_numeric hN).2.1
    have hlogM : Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure) ≤ 1 / c := by
      have h1 : Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure) ≤ Real.log (1 + 1 / c) := by
        apply Real.log_le_log hMpos
        rw [hcdef]; exact hM
      have h2 : Real.log (1 + 1 / c) ≤ 1 / c := by
        have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / c by positivity)
        linarith
      linarith
    have hKc : (KK N : ℝ) ≤ c / A0 := by
      have hA0 : 0 < A0 := by unfold A0; norm_num
      rw [le_div_iff₀ hA0]; linarith
    have hKnn : (0:ℝ) ≤ (KK N : ℝ) := Nat.cast_nonneg _
    calc (KK N : ℝ) * Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure)
        ≤ (KK N : ℝ) * (1 / c) := mul_le_mul_of_nonneg_left hlogM hKnn
      _ = (KK N : ℝ) / c := by ring
      _ ≤ (c / A0) / c := div_le_div_of_nonneg_right hKc hcpos.le
      _ = 1 / A0 := by field_simp
  -- ## Step 2: `exp(-1/A₀) ≤ (M(P)⁻¹)^K`
  have hexpM : Real.exp (-(1/A0))
      ≤ ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ^ (KK N) := by
    have h1 : -(1/A0)
        ≤ -((KK N : ℝ) * Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure)) := by
      linarith [hnum]
    have h2 := Real.exp_le_exp.mpr h1
    have hkey : Real.exp (-((KK N : ℝ)
          * Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure)))
        = ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ^ (KK N) := by
      rw [show -((KK N : ℝ) * Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure))
            = (KK N : ℝ) * (- Real.log ((P.map (Int.castRingHom ℂ)).mahlerMeasure)) by ring,
          Real.exp_nat_mul, Real.exp_neg, Real.exp_log hMpos]
    rwa [hkey] at h2
  -- ## Step 3: `∏ ‖w_j‖ = M(P)⁻¹`, hence `‖w_j‖ ≥ M(P)⁻¹`
  have hMfac : (∏ j, ‖w j‖) = ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ := by
    rw [← hprod, inv_inv]
  have hz_ge : ∀ j, ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ≤ ‖w j‖ := by
    intro j
    have hkey : (∏ k : Fin N, ‖w k‖) ≤ ‖w j‖ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun k => ‖w k‖) (Finset.mem_univ j)]
      have hle1 : (∏ k ∈ Finset.univ.erase j, ‖w k‖) ≤ 1 :=
        Finset.prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => hw1 k)
      have h0 : (0:ℝ) ≤ ‖w j‖ := norm_nonneg _
      calc ‖w j‖ * (∏ k ∈ Finset.univ.erase j, ‖w k‖) ≤ ‖w j‖ * 1 :=
            mul_le_mul_of_nonneg_left hle1 h0
        _ = ‖w j‖ := mul_one _
    rw [← hMfac]
    exact hkey
  have hzpow_ge : ∀ j, Real.exp (-(1/A0)) ≤ ‖w j‖ ^ (KK N) := by
    intro j
    have h0 : 0 ≤ ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ := inv_nonneg.mpr hMpos.le
    exact hexpM.trans (pow_le_pow_left₀ h0 (hz_ge j) (KK N))
  -- ## Step 4: elementary facts about `ρ' = 1 - 1/(12N)`
  have hρle1 : rhoP N ≤ 1 := by
    unfold rhoP
    have : (0:ℝ) ≤ 1/(12*(N:ℝ)) := by positivity
    linarith
  have hρnn : 0 ≤ rhoP N := by
    unfold rhoP
    have hN2r : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have : (1:ℝ)/(12*(N:ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hzpow_le1 : ∀ j, ‖w j‖ ^ (KK N) ≤ 1 :=
    fun j => pow_le_one₀ (norm_nonneg _) (hw1 j)
  have hzpow_nn : ∀ j, 0 ≤ ‖w j‖ ^ (KK N) := fun j => pow_nonneg (norm_nonneg _) _
  -- ## Step 5: `min ρ' b ≥ ρ'·b` for `b ∈ [0,1]`, and the product identity
  have hmin_ge : ∀ j, rhoP N * ‖w j‖ ^ (KK N) ≤ min (rhoP N) (‖w j‖ ^ (KK N)) := by
    intro j
    apply le_min
    · exact mul_le_of_le_one_right hρnn (hzpow_le1 j)
    · exact mul_le_of_le_one_left (hzpow_nn j) hρle1
  have hprod_eq : (∏ j, rhoP N * ‖w j‖ ^ (KK N))
      = rhoP N ^ N * ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ^ (KK N) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, hMfac, Finset.card_univ,
      Fintype.card_fin]
  -- ## Step 6: `exp(-1/A₀) ≤ 11/12`
  have hexp_1112 : Real.exp (-(1/A0)) ≤ (11:ℝ)/12 := by
    have hA0 : (1:ℝ)/A0 = 5/48 := by unfold A0; norm_num
    rw [hA0, Real.exp_neg]
    have hle : (5/48:ℝ) + 1 ≤ Real.exp (5/48) := Real.add_one_le_exp _
    have hpos : (0:ℝ) < (5/48:ℝ) + 1 := by norm_num
    have hinv : (Real.exp (5/48))⁻¹ ≤ ((5/48:ℝ) + 1)⁻¹ := inv_anti₀ hpos hle
    have hnum2 : (((5/48:ℝ) + 1)⁻¹) = 48/53 := by norm_num
    have hfin : (48:ℝ)/53 ≤ 11/12 := by norm_num
    rw [hnum2] at hinv
    linarith
  -- ## Step 7: `ρ'^N ≥ 11/12` (Bernoulli)
  have hrho_ge : (11:ℝ)/12 ≤ rhoP N ^ N := by
    have hN2r : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have ha : (-2:ℝ) ≤ -(1/(12*(N:ℝ))) := by
      have : (1:ℝ)/(12*(N:ℝ)) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have hB := one_add_mul_le_pow ha N
    have h1 : (1:ℝ) + (N:ℝ) * (-(1/(12*(N:ℝ)))) = 11/12 := by
      have hNne : (N:ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have h2 : (1:ℝ) + -(1/(12*(N:ℝ))) = rhoP N := by
      unfold rhoP; ring
    rwa [h1, h2] at hB
  -- ## Assembly
  have hexpρ : Real.exp (-(1/A0)) ≤ rhoP N := (mahler_numeric hN).2.2.1
  refine ⟨fun j => le_min hexpρ (hzpow_ge j), fun j => min_le_left _ _, ?_⟩
  have hstep1 : rhoP N ^ N * ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ^ (KK N)
      ≤ ∏ j, min (rhoP N) (‖w j‖ ^ (KK N)) := by
    rw [← hprod_eq]
    exact Finset.prod_le_prod₀ (fun j _ => mul_nonneg hρnn (hzpow_nn j)) (fun j _ => hmin_ge j)
  have hstep2 : (11:ℝ)/12 * Real.exp (-(1/A0))
      ≤ rhoP N ^ N * ((P.map (Int.castRingHom ℂ)).mahlerMeasure)⁻¹ ^ (KK N) :=
    mul_le_mul hrho_ge hexpM (Real.exp_pos _).le (pow_nonneg hρnn N)
  have hstep3 : Real.exp (-(2/A0)) ≤ (11:ℝ)/12 * Real.exp (-(1/A0)) := by
    have heq : Real.exp (-(2/A0))
        = Real.exp (-(1/A0)) * Real.exp (-(1/A0)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hexp_1112 (Real.exp_pos _).le
  linarith [hstep1, hstep2, hstep3]

end Work.BW
