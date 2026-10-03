import Mathlib
import Submission.Work.KMTAreas.A7.cut_discharge

/-!
# The `mStarF` cutoff is `1` on the support of the bump `varphiN`

The KMT model operator of §6--§8 carries the symbol `m_* = η_{≤-2u} = mStarF u` on the first
tensor factor, and it is applied to the modulated bump `φ_{N,t}` (a rescaled difference of the
fixed cutoff `η`).  The functional calculus behind the model operator requires `m_* ≡ 1` on the
support of `φ_{N,t}`; in the *main regime* `k₁ + 1 + 2u ≤ Log N` this holds, and that is the
content of this file:

* `etaCut_kmtEta_eq_one_of_abs_mul_zpow_le` — the cutoff `η_{≤k}(θ) = η(θ/2^k)` equals `1`
  as soon as `|θ| · 2^{-k} ≤ 1/2` (the region where the *argument* `θ/2^k` lies in `[-1/2,1/2]`);
* `abs_mul_zpow_le_half_of_varphiN` — the support estimate
  `|θ| ≤ 2^{k₁ - Log N}` of the bump `φ_N` (proved as `Work.KMTAreas.A7.varphiN_support`)
  combines with the regime condition to give `|θ| · 2^{2u} ≤ 1/2`;
* `mStarF_eq_one_of_varphiN_ne` — the two together.
-/

namespace Work.KMTAreas.A7Rep

open Work.Analysis.IonescuWainger

/-- **The cutoff `η_{≤k}` equals `1` on the region `|θ| · 2^{-k} ≤ 1/2`.**  Indeed
`η_{≤k}(θ) = η(θ/2^k)` and `η = 1` on `[-1/2,1/2]`, while `|θ/2^k| = |θ| · 2^{-k}`. -/
theorem etaCut_kmtEta_eq_one_of_abs_mul_zpow_le {k : ℤ} {θ : ℝ}
    (h : |θ| * (2 : ℝ) ^ (-k) ≤ 1 / 2) :
    Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ = 1 := by
  rw [Work.Analysis.IonescuWainger.etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  have hk : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hmul : |θ| * ((2 : ℝ) ^ k)⁻¹ ≤ 1 / 2 := by simpa only [zpow_neg] using h
  have h1 : |θ| ≤ (1 / 2) * (2 : ℝ) ^ k := by
    have := mul_le_mul_of_nonneg_right hmul (le_of_lt hk)
    rwa [mul_assoc, inv_mul_cancel₀ hk.ne', mul_one] at this
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  exact h1

/-- **The main regime puts the support of the bump inside the region where `mStarF u` is `1`.**

For `k₁ + 1 + 2u ≤ Log N`, every `θ` with `φ_N(θ) ≠ 0` satisfies `|θ| · 2^{2u} ≤ 1/2`:
the bump's support is `|θ| ≤ 2^{k₁ - Log N} ≤ 2^{-1-2u}`. -/
theorem abs_mul_zpow_le_half_of_varphiN {N k₁ U : ℕ} {θ : ℝ}
    (h : (k₁ : ℤ) + 1 + 2 * (U : ℤ) ≤ Work.Analysis.EndVar.logN N)
    (hθ : Work.KMTAreas.A7.varphiN N k₁ θ ≠ 0) :
    |θ| * (2 : ℝ) ^ (2 * (U : ℤ)) ≤ 1 / 2 := by
  have hsupp := Work.KMTAreas.A7.varphiN_support N k₁ θ hθ
  have hcast : ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      = (((k₁ : ℤ) - Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_intCast] at hsupp
  have hle : (k₁ : ℤ) - Work.Analysis.EndVar.logN N ≤ -(1 + 2 * (U : ℤ)) := by omega
  have hmono : (2 : ℝ) ^ ((k₁ : ℤ) - Work.Analysis.EndVar.logN N)
      ≤ (2 : ℝ) ^ (-(1 + 2 * (U : ℤ))) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
  have hfac : (2 : ℝ) ^ (-(1 + 2 * (U : ℤ))) * (2 : ℝ) ^ (2 * (U : ℤ)) = 1 / 2 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show -(1 + 2 * (U : ℤ)) + 2 * (U : ℤ) = -1 by ring, zpow_neg_one]
    norm_num
  calc |θ| * (2 : ℝ) ^ (2 * (U : ℤ))
      ≤ (2 : ℝ) ^ (-(1 + 2 * (U : ℤ))) * (2 : ℝ) ^ (2 * (U : ℤ)) :=
        mul_le_mul_of_nonneg_right (le_trans hsupp hmono) (le_of_lt (zpow_pos (by norm_num) _))
    _ = 1 / 2 := hfac

/-- **The symbol `mStarF u = η_{≤-2u}` is `1` on the support of `varphiN N k₁`**, in the main
regime `k₁ + 1 + 2u ≤ Log N`. -/
theorem mStarF_eq_one_of_varphiN_ne (N k₁ U : ℕ)
    (h : (k₁ : ℤ) + 1 + 2 * (U : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    ∀ θ : ℝ, Work.KMTAreas.A7.varphiN N k₁ θ ≠ 0 → Work.KMTAreas.A7.mStarF U θ = 1 := by
  intro θ hθ
  have hb := abs_mul_zpow_le_half_of_varphiN (N := N) (k₁ := k₁) (U := U) h hθ
  have hcut : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
      (-(2 * (U : ℤ))) θ = 1 :=
    etaCut_kmtEta_eq_one_of_abs_mul_zpow_le (k := -(2 * (U : ℤ)))
      (by simpa only [neg_neg] using hb)
  simpa only [Work.KMTAreas.A7.mStarF] using hcut

end Work.KMTAreas.A7Rep
