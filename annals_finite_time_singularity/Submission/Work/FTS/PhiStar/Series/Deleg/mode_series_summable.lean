import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

local notation "bm" => Work.FTS.PhiStar.Series.bmode
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam

/-- The eigenvalue `lam m = 2m(2m+5)` is positive for `m ≥ 1`. -/
lemma lamF_pos {m : ℕ} (hm : 1 ≤ m) : 0 < lamF m := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  show 0 < 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  nlinarith

/-- `4 (m:ℝ)² ≤ lam m` for `m ≥ 1`. -/
lemma four_sq_le_lamF {m : ℕ} (hm : 1 ≤ m) : 4 * (m : ℝ) ^ 2 ≤ lamF m := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  show 4 * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  nlinarith

/-- The pointwise decay of the mode series: the hypothesis `hdec` on the coefficients together
with the growth hypothesis `hgr` on the eigenvectors gives the summable majorant
`max (Cd*Cg) 1 · m^{-5/2}`. -/
lemma mode_bound (ψ : ℝ → ℝ) {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |bm m ψ| ≤ Cd / (lamF m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |eF m θ| ≤ Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :
    ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(bm m ψ / lamF m) * eF m θ| ≤ max (Cd * Cg) 1 * (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
  intro m θ hθ
  by_cases hm : m = 0
  · subst hm
    have hz : ((0 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) = 0 := by
      rw [show ((0 : ℕ) : ℝ) = 0 by norm_num, Real.zero_rpow (by norm_num)]
    have hlz : lamF 0 = 0 := by simp [Work.FTS.PhiStar.Gegenbauer.lam]
    rw [hlz, div_zero, zero_mul, abs_zero, hz, mul_zero]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hxpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have hlam_pos : 0 < lamF m := lamF_pos hm1
    have hlam_ge : 4 * (m : ℝ) ^ 2 ≤ lamF m := four_sq_le_lamF hm1
    have hsqrt_pos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hden : 0 < (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (pow_pos hlam_pos 2) hsqrt_pos
    -- step 1: `|bm m ψ| / lam m ≤ Cd / ((lam m)² √(2m+1))`
    have hstep : |bm m ψ| / lamF m ≤ Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
      calc |bm m ψ| / lamF m
          ≤ (Cd / (lamF m * Real.sqrt (2 * (m : ℝ) + 1))) / lamF m :=
            div_le_div_of_nonneg_right (hdec m hm1) (le_of_lt hlam_pos)
        _ = Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
            rw [div_div]
            congr 1
            ring
    -- step 2: `((m+1)^{3/2} ≤ 16 m^{3/2}`
    have hY : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by
      have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
      have h1 : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ (2 * (m : ℝ)) ^ ((3 / 2 : ℝ)) :=
        Real.rpow_le_rpow (by linarith) hle (by norm_num)
      have h2 : (2 * (m : ℝ)) ^ ((3 / 2 : ℝ))
          = (2 : ℝ) ^ ((3 / 2 : ℝ)) * (m : ℝ) ^ ((3 / 2 : ℝ)) :=
        Real.mul_rpow (by norm_num) (le_of_lt hxpos)
      have h3 : (2 : ℝ) ^ ((3 / 2 : ℝ)) ≤ 16 := by
        have hh : (2 : ℝ) ^ ((3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        have h4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
        linarith
      calc ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) ≤ (2 * (m : ℝ)) ^ ((3 / 2 : ℝ)) := h1
        _ = (2 : ℝ) ^ ((3 / 2 : ℝ)) * (m : ℝ) ^ ((3 / 2 : ℝ)) := h2
        _ ≤ 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hxpos) _)
    -- step 3: the denominator dominates `16 m⁴ √1`
    have hD16 : 16 * (m : ℝ) ^ (4 : ℝ) ≤ (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
      have h4 : (m : ℝ) ^ (4 : ℝ) = (m : ℝ) ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hsq : 16 * (m : ℝ) ^ (4 : ℝ) ≤ (lamF m) ^ 2 := by
        rw [h4]
        nlinarith [sq_nonneg (lamF m - 4 * (m : ℝ) ^ 2), hlam_ge]
      have hs1 : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
        Real.one_le_sqrt.mpr (by linarith)
      calc 16 * (m : ℝ) ^ (4 : ℝ) = 16 * (m : ℝ) ^ (4 : ℝ) * 1 := by ring
        _ ≤ (lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
            mul_le_mul hsq hs1 (by norm_num) (le_of_lt (pow_pos hlam_pos 2))
    -- step 4: the exponent bookkeeping `m^{-5/2} · m⁴ = m^{3/2}`
    have hbr : (m : ℝ) ^ (-(5 / 2 : ℝ)) * (16 * (m : ℝ) ^ (4 : ℝ))
        = 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by
      have hrr : (m : ℝ) ^ (-(5 / 2 : ℝ)) * (m : ℝ) ^ (4 : ℝ)
          = (m : ℝ) ^ ((3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      calc (m : ℝ) ^ (-(5 / 2 : ℝ)) * (16 * (m : ℝ) ^ (4 : ℝ))
          = 16 * ((m : ℝ) ^ (-(5 / 2 : ℝ)) * (m : ℝ) ^ (4 : ℝ)) := by ring
        _ = 16 * (m : ℝ) ^ ((3 / 2 : ℝ)) := by rw [hrr]
    -- the key inequality
    have hkey : ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))
          / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))
        ≤ (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [div_le_iff₀ hden]
      have h := mul_le_mul_of_nonneg_left hD16
        (Real.rpow_nonneg (le_of_lt hxpos) (-(5 / 2 : ℝ)))
      rw [hbr] at h
      linarith
    -- assemble
    have hprod : |bm m ψ| / lamF m * |eF m θ|
        ≤ (Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))) :=
      mul_le_mul hstep (hgr m θ hθ) (abs_nonneg _)
        (div_nonneg (le_of_lt hCd) (le_of_lt hden))
    calc |(bm m ψ / lamF m) * eF m θ|
        = |bm m ψ| / lamF m * |eF m θ| := by
          rw [abs_mul, abs_div, abs_of_pos hlam_pos]
      _ ≤ (Cd / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))) := hprod
      _ = Cd * Cg * (((m : ℝ) + 1) ^ ((3 / 2 : ℝ))
            / ((lamF m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) := by
          field_simp
      _ ≤ max (Cd * Cg) 1 * (m : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul (le_max_left _ _) hkey
            (div_nonneg
              (le_of_lt (Real.rpow_pos_of_pos (by linarith : 0 < (m : ℝ) + 1) _))
              (le_of_lt hden))
            (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))

theorem mode_series_summable (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) :
    (∃ M : ℕ → ℝ, (∀ m : ℕ, 0 ≤ M m) ∧ Summable M ∧
        ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
          |(Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M m)
      ∧ ContinuousOn
          (fun θ => ∑' m : ℕ,
            (Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  set A : ℝ := max (Cd * Cg) 1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKle : Cd * Cg ≤ A := by
    rw [hAdef]
    exact le_max_left _ _
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ (-(5 / 2 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(5 / 2 : ℝ)))).mpr (by norm_num)
  have hMsum : Summable (fun m : ℕ => A * (m : ℝ) ^ (-(5 / 2 : ℝ))) := hbase.mul_left A
  have hbd : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * (m : ℝ) ^ (-(5 / 2 : ℝ)) := by
    intro m θ hθ
    have h := mode_bound ψ hCd hCg hdec hgr m θ hθ
    rwa [hAdef]
  refine ⟨?_, ?_⟩
  · exact ⟨fun m => A * (m : ℝ) ^ (-(5 / 2 : ℝ)),
      fun m => mul_nonneg (le_of_lt hApos) (Real.rpow_nonneg (Nat.cast_nonneg m) _),
      hMsum, hbd⟩
  · refine continuousOn_tsum (u := fun m : ℕ => A * (m : ℝ) ^ (-(5 / 2 : ℝ))) ?_ hMsum ?_
    · intro m
      have hcont : Continuous (fun θ : ℝ =>
          (Work.FTS.PhiStar.Series.bmode m ψ / Work.FTS.PhiStar.Gegenbauer.lam m)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
        rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
            = (fun θ : ℝ => Real.cos θ
                * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
        exact (Real.continuous_cos.mul
          ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
            Real.continuous_sin)).const_mul _
      exact hcont.continuousOn
    · intro m θ hθ
      rw [Real.norm_eq_abs]
      exact hbd m θ hθ

end Work.FTS.PhiStar.Series.Deleg
