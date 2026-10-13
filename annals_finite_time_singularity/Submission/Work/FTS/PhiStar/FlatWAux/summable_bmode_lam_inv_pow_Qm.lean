import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Series.Deleg.mode_series_summable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm`

Absolute summability of the resummed angular series `Σ_m b_m λ_m^{-j} Q_m(θ)`,
`b_m = bmode m ψ`, `λ_m = lam m = 2m(2m+5)`, `Q_m = eFam m / sin 2θ`, for `j ≥ 1` and
`θ ∈ (0, π/2)`.

The three inputs are the coefficient decay `hdec`, the angular growth `hgr` and the vanishing
`m = 0` coefficient `hb0`.

The proof reduces to the already established summability of `Σ_m (b_m/λ_m) e_m(θ)` with a
summable majorant (`Series.Deleg.mode_series_summable`, whose growth hypothesis `(m+1)^{3/2}`
is implied by the linear growth `2m+1` used here), together with the elementary observation
that for `m ≥ 1` the reciprocal power `λ_m^{-j}` (`j ≥ 1`) is dominated by `λ_m^{-1}`: the
fact that `Q_m = e_m / sin 2θ` only contributes the constant factor `(sin 2θ)^{-1}`.
-/

/-- On the open interval the divisor `sin 2θ` of the divided angular mode is positive. -/
private lemma s2_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_pos
    (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

/-- The eigenvalue `λ_m = 2m(2m+5)` is positive for `m ≥ 1`. -/
private lemma lam_pos_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : (0 : ℝ) < (m : ℝ) := by linarith
  have h3 : (0 : ℝ) < 2 * (m : ℝ) + 5 := by linarith
  have h := mul_pos (mul_pos two_pos h2) h3
  simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using h

/-- The eigenvalue `λ_m = 2m(2m+5)` is at least `1` for `m ≥ 1`. -/
private lemma one_le_lam_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h4 : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h5 : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by linarith
  have h6 : (0 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h' : (1 : ℝ) ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5) :=
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * (m : ℝ)) * (2 * (m : ℝ) + 5) := mul_le_mul h4 h5 (by norm_num) h6
  simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using h'

/-- The linear growth hypothesis `|e_m| ≤ C (2m+1)` implies the growth `|e_m| ≤ 3C (m+1)^{3/2}`
used by `Series.Deleg.mode_series_summable`. -/
private lemma eFam_growth_three_halves {Cg : ℝ} (hCg : 0 < Cg)
    (hgr : ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ 3 * Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
  intro m θ' hθ'
  have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpow : (2 * (m : ℝ) + 1) ≤ 3 * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
    have h1 : ((m : ℝ) + 1) ^ (1 : ℝ) ≤ ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
    rw [Real.rpow_one] at h1
    nlinarith
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ Cg * (2 * (m : ℝ) + 1) := hgr m θ' hθ'
    _ ≤ Cg * (3 * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hCg)
    _ = 3 * Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by ring

theorem summable_bmode_lam_inv_pow_Qm (ψ : ℝ → ℝ) (θ : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1)) :
    Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * Work.FTS.PhiStar.FlatWAux.Qm m θ) := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  -- the summable majorant of the mode series `Σ_m (b_m/λ_m) e_m(θ)`
  obtain ⟨M, hMnn, hMsum, hMbd⟩ :=
    (Work.FTS.PhiStar.Series.Deleg.mode_series_summable ψ ⟨Cd, hCd, hdec⟩
      ⟨3 * Cg, by linarith, eFam_growth_three_halves hCg hgr⟩).1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs2 : 0 < Work.Construction.s2 θ := s2_pos_of_mem_Ioo hθ
  refine Summable.of_norm_bounded (g := fun m : ℕ => M m / Work.Construction.s2 θ)
    (hMsum.div_const (Work.Construction.s2 θ)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    simp only [zero_mul, abs_zero]
    exact div_nonneg (hMnn 0) (le_of_lt hs2)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lam_pos_of_one_le hm1
    have hinvnn : 0 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ :=
      le_of_lt (inv_pos.mpr hLpos)
    -- `λ_m^{-j} ≤ λ_m^{-1}` for `j ≥ 1`
    have hpowle : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := by
      have h := pow_le_pow_of_le_one hinvnn
        (inv_le_one_of_one_le₀ (one_le_lam_of_one_le hm1)) hj
      simpa using h
    have hMstep : |Work.FTS.PhiStar.Series.bmode m ψ
          * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M m := by
      have h := hMbd m θ hθI
      rwa [div_eq_mul_inv] at h
    calc |Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * Work.FTS.PhiStar.FlatWAux.Qm m θ|
        = |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          simp only [Work.FTS.PhiStar.FlatWAux.Qm, abs_mul, abs_pow, abs_div,
            abs_of_nonneg hinvnn, abs_of_pos hs2]
          ring
      _ ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs2)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowle (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.FTS.PhiStar.Series.bmode m ψ * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ| / Work.Construction.s2 θ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hinvnn]
      _ ≤ M m / Work.Construction.s2 θ :=
          div_le_div_of_nonneg_right hMstep (le_of_lt hs2)

end Work.FTS.PhiStar.FlatWAux
