import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.FlatWAux.WtDerivAux.summable_lam_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

theorem WtBound (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ|
          ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2))
    (hflat : ∃ C : ℝ, 0 < C ∧
      Work.FTS.VocabO2.FlatW 7 (fun z θ => ψ θ / Work.Construction.s2 θ) C) :
    ∃ Kw : ℕ → ℝ, (∀ j : ℕ, 0 ≤ Kw j) ∧
      ∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ θ : ℝ,
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
          |Work.FTS.PhiStar.FlatWAux.Wt ψ j θ| ≤ Kw j := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨CQf, hCQf, hQ⟩ := hQ
  have hCQ : 0 ≤ CQf 0 := hCQf 0
  obtain ⟨Cf, hCf, hflat⟩ := hflat
  -- the summable angular series majorant and its value `T`
  set T : ℝ := ∑' m : ℕ,
    (2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) with hTdef
  have hlamnn : ∀ m : ℕ, 0 ≤ Gegenbauer.lam m := by
    intro m; simp only [Gegenbauer.lam]; positivity
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    exact tsum_nonneg (fun m => div_nonneg (by positivity)
      (mul_nonneg (hlamnn m) (Real.sqrt_nonneg _)))
  have hbase : Summable (fun m : ℕ => Cd * CQf 0 *
      ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) :=
    WtDerivAux.summable_lam_sqrt.mul_left (Cd * CQf 0)
  refine ⟨fun _ => max Cf (Cd * CQf 0 * T),
    fun j => le_trans hCf.le (le_max_left _ _), ?_⟩
  intro j hj θ hθ
  rcases j with _ | k
  · -- `j = 0`: `Wt ψ 0 = ψ / sin 2θ` is bounded by the `FlatW` hypothesis
    have h := (hflat 1 θ one_pos hθ.1 hθ.2).1 0 (by norm_num)
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
    exact le_trans h (le_max_left _ _)
  · -- `j = k + 1`: the resummed series, bounded termwise by the summable majorant
    have hpt : ∀ m : ℕ,
        |Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1) * Qm m θ|
        ≤ Cd * CQf 0 * ((2 * (m : ℝ) + 1)
            / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- `m = 0`: the summand vanishes since `λ_0 = 0`
        subst hm
        have hzero : ((Gegenbauer.lam 0)⁻¹) ^ (k + 1) = 0 := by
          rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
          exact zero_pow (Nat.succ_ne_zero k)
        rw [hzero, mul_zero, zero_mul, abs_zero]
        simp [Gegenbauer.lam]
      · -- `m ≥ 1`
        have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hlam_pos : 0 < Gegenbauer.lam m := by
          simp only [Gegenbauer.lam]; push_cast; nlinarith
        have hlam1 : 1 ≤ Gegenbauer.lam m := by
          simp only [Gegenbauer.lam]; push_cast; nlinarith
        have hNpos : 0 < 2 * (m : ℝ) + 1 := by positivity
        have hinvnn : 0 ≤ ((Gegenbauer.lam m)⁻¹) ^ (k + 1) :=
          pow_nonneg (inv_nonneg.mpr hlam_pos.le) _
        have hinv_le : ((Gegenbauer.lam m)⁻¹) ^ (k + 1) ≤ (Gegenbauer.lam m)⁻¹ := by
          rw [pow_succ]
          calc (Gegenbauer.lam m)⁻¹ ^ k * (Gegenbauer.lam m)⁻¹
              ≤ 1 * (Gegenbauer.lam m)⁻¹ :=
                mul_le_mul_of_nonneg_right
                  (pow_le_one₀ (inv_nonneg.mpr hlam_pos.le)
                    ((inv_le_one₀ hlam_pos).mpr hlam1))
                  (inv_nonneg.mpr hlam_pos.le)
            _ = (Gegenbauer.lam m)⁻¹ := one_mul _
        have hQm : |Qm m θ| ≤ CQf 0 * (2 * (m : ℝ) + 1) ^ 2 := by
          have h := hQ m hm 0 (by norm_num) θ hθ
          simpa [iteratedDeriv_zero] using h
        have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
            ≤ Cd / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hdec m hm
        rw [abs_mul, abs_mul, abs_of_nonneg hinvnn]
        calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * |Qm m θ|
            ≤ (Cd / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                * (Gegenbauer.lam m)⁻¹ * (CQf 0 * (2 * (m : ℝ) + 1) ^ 2) := by
              gcongr
          _ = Cd * CQf 0 * ((2 * (m : ℝ) + 1) ^ 2
                / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) := by
              ring
          _ ≤ Cd * CQf 0 * ((2 * (m : ℝ) + 1)
                / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
              have hNL : (2 * (m : ℝ) + 1) / Gegenbauer.lam m ≤ 1 := by
                rw [div_le_one hlam_pos]; simp only [Gegenbauer.lam]; push_cast; nlinarith
              have hkey : (2 * (m : ℝ) + 1) ^ 2
                    / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                  ≤ (2 * (m : ℝ) + 1)
                    / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
                have hsplit : (2 * (m : ℝ) + 1) ^ 2
                      / ((Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
                    = ((2 * (m : ℝ) + 1) / Gegenbauer.lam m)
                      * ((2 * (m : ℝ) + 1)
                        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
                  ring
                rw [hsplit]
                exact mul_le_of_le_one_left (by positivity) hNL
              exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hCd.le hCQ)
    have hsum : Summable (fun m : ℕ =>
        Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1) * Qm m θ) :=
      Summable.of_norm_bounded hbase (fun m => by rw [Real.norm_eq_abs]; exact hpt m)
    have hWt : Wt ψ (k + 1) θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ := rfl
    rw [hWt]
    calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ|
        = ‖∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ‖ := norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Qm m θ| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, Cd * CQf 0 * ((2 * (m : ℝ) + 1)
            / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) :=
            Summable.tsum_le_tsum hpt hsum.norm hbase
      _ = Cd * CQf 0 * T := by rw [tsum_mul_left, hTdef]
      _ ≤ max Cf (Cd * CQf 0 * T) := le_max_right _ _

end Work.FTS.PhiStar.FlatWAux
