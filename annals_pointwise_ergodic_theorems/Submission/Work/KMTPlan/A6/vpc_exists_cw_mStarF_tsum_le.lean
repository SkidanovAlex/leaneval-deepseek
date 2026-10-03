/-
# Uniform `ℓ¹`-bound for the coefficient kernel of the §6 tensor factor `m_* = η_{≤-2u}`

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial averages*,
Ann. of Math. 195 (3) 2022, §6: the model operator `B^{l₁,l₂,m_Ẑ}_{m_*}` of the large-scale
analysis has tensor factor `m_* = η_{≤-2u} = etaCut kmtEta (-(2u))`
(`Work.KMTAreas.A7.mStarF u`), and the kernel estimates need the *absolute* convergence of its
coefficient kernel `cw m_* j = ∫ m_*(θ) e(-jθ) dθ`, with a bound **uniform in `u`**.

The point is that `mStarF u = fun θ => kmtEta (R θ)` with `R = 2^{2u} ≥ 1`: `m_*` is a bump of
inverse width `R` supported in `[-1/R, 1/R]`, with `‖m_*‖_∞ ≤ 1`, `‖m_*'‖_∞ ≤ C R`,
`‖m_*''‖_∞ ≤ C R²` for an absolute constant `C`.  Lemma `crude-mult`(ii) of the paper (in the
kernel form `Work.KMTAreas.A7.CwTsumLe`, proved in this workspace from the two integrations by
parts plus the abstract `ℤ`-estimate `TsumIntLeOfBounds`) then gives `∑_j ‖cw m_* j‖ ≤ Cw · C₀`
with `C₀` independent of `u` -- exactly the "uniform in the auxiliary scale" statement needed
downstream.  Summability itself is automatic from the quadratic Fourier decay
(`Work.KMTAreas.A7.cw_etaCut_decay`).

So the whole content is one application of `CwTsumLe` to the rescaled bump, the only work being
the bookkeeping of the rescaled derivatives and of the support.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.CwTsumLe
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform

namespace Work.KMTPlan.A6

open Work.KMTAreas.A7
open Work.KMTContract

private lemma summable_norm_cw_mStarF (u : ℕ) :
    Summable (fun j : ℤ => ‖cw (mStarF u) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

theorem vpc_exists_cw_mStarF_tsum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖)
      ∧ (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖) ≤ C := by
  obtain ⟨Cc, _hCcpos, hCw⟩ := CwTsumLe
  obtain ⟨_M0, M1, M2, _hM0, _hM1, _hM2, hcdEta, _hb0, hb1, hb2, _hz0, hz1, hz2, hdEta, hdEta2⟩ :=
    kmtEta_deriv_bounds
  set C0 : ℝ := max 1 (max M1 M2) with hC0def
  have hC0pos : 0 < C0 := by rw [hC0def]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC0ge1 : 1 ≤ C0 := by rw [hC0def]; exact le_max_left _ _
  have hC00 : 0 ≤ C0 := hC0pos.le
  have h_eta : ∀ y : ℝ, ‖kmtEta y‖ ≤ C0 := fun y => le_trans (norm_kmtEta_le y) hC0ge1
  have h_d1 : ∀ y : ℝ, ‖deriv kmtEta y‖ ≤ C0 := by
    intro y
    rw [hC0def]
    by_cases h : |y| ≤ 1
    · exact le_trans (hb1 y h) (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [hz1 y (le_of_lt (not_le.mp h))]
      simp only [norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
  have h_d2 : ∀ y : ℝ, ‖iteratedDeriv 2 kmtEta y‖ ≤ C0 := by
    intro y
    rw [hC0def]
    by_cases h : |y| ≤ 1
    · exact le_trans (hb2 y h) (le_trans (le_max_right _ _) (le_max_right _ _))
    · rw [hz2 y (le_of_lt (not_le.mp h))]
      simp only [norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
  refine ⟨max 1 (Cc * C0), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro u
  set R : ℝ := (2 : ℝ) ^ (2 * u) with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hmeq : mStarF u = fun θ : ℝ => kmtEta (R * θ) := by
    funext θ
    have hpow : (2 * (u : ℤ)) = ((2 * u : ℕ) : ℤ) := by push_cast; ring
    have hz : (2 : ℝ) ^ (-(2 * (u : ℤ))) = R⁻¹ := by
      rw [zpow_neg, hpow, zpow_natCast, hRdef]
    simp only [mStarF, Work.Analysis.IonescuWainger.etaCut]
    rw [hz, div_inv_eq_mul, mul_comm θ R]
  have hderiv1 : ∀ θ : ℝ, deriv (mStarF u) θ = R • deriv kmtEta (R * θ) := by
    intro θ
    have hlin : HasDerivAt (fun y : ℝ => R * y) R θ := by
      simpa using (hasDerivAt_id θ).const_mul R
    have hcomp : HasDerivAt (fun y : ℝ => kmtEta (R * y)) (R • deriv kmtEta (R * θ)) θ :=
      (hdEta (R * θ)).scomp θ hlin
    rw [hmeq]
    exact hcomp.deriv
  have hderiv2 : ∀ θ : ℝ, deriv (deriv (mStarF u)) θ = R • (R • iteratedDeriv 2 kmtEta (R * θ)) := by
    intro θ
    have hd1fun : deriv (mStarF u) = fun θ : ℝ => R • deriv kmtEta (R * θ) := funext hderiv1
    rw [hd1fun]
    have hlin : HasDerivAt (fun y : ℝ => R * y) R θ := by
      simpa using (hasDerivAt_id θ).const_mul R
    have hinner : HasDerivAt (fun y : ℝ => deriv kmtEta (R * y))
        (R • iteratedDeriv 2 kmtEta (R * θ)) θ :=
      (hdEta2 (R * θ)).scomp θ hlin
    exact (hinner.const_smul R).deriv
  have hsupp : ∀ θ : ℝ, 1 / R < |θ| → mStarF u θ = 0 := by
    intro θ hθ
    rw [hmeq]
    have hlt : 1 < |R * θ| := by
      rw [abs_mul, abs_of_pos hRpos]
      have h := mul_lt_mul_of_pos_left hθ hRpos
      rwa [mul_one_div, div_self hRpos.ne'] at h
    exact kmtEta_zero (le_of_lt hlt)
  have hm0 : ∀ θ : ℝ, ‖mStarF u θ‖ ≤ C0 := fun θ => by
    rw [hmeq]; exact h_eta (R * θ)
  have hm1 : ∀ θ : ℝ, ‖deriv (mStarF u) θ‖ ≤ C0 * R := fun θ => by
    rw [hderiv1 θ, norm_smul, Real.norm_of_nonneg hRpos.le]
    calc R * ‖deriv kmtEta (R * θ)‖ ≤ R * C0 :=
          mul_le_mul_of_nonneg_left (h_d1 (R * θ)) hRpos.le
      _ = C0 * R := by ring
  have hm2 : ∀ θ : ℝ, ‖deriv (deriv (mStarF u)) θ‖ ≤ C0 * R ^ 2 := fun θ => by
    rw [hderiv2 θ, norm_smul, norm_smul, Real.norm_of_nonneg hRpos.le]
    calc R * (R * ‖iteratedDeriv 2 kmtEta (R * θ)‖) ≤ R * (R * C0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h_d2 (R * θ)) hRpos.le) hRpos.le
      _ = C0 * R ^ 2 := by ring
  have hcd : ContDiff ℝ 2 (mStarF u) := by
    rw [hmeq]
    have hlin : ContDiff ℝ 2 (fun θ : ℝ => R * θ) := by
      simpa using (contDiff_const (𝕜 := ℝ) (c := R)).mul (contDiff_id (𝕜 := ℝ))
    exact hcdEta.comp hlin
  have hbound := hCw (mStarF u) C0 R hC00 hR1 hcd hm0 hm1 hm2 hsupp
  exact ⟨summable_norm_cw_mStarF u, le_trans hbound (le_max_right _ _)⟩

end Work.KMTPlan.A6
