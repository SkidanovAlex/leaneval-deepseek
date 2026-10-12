import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.arith_aKH_div_sell_le`

At the FS §10 parameter point `FSParamsView E` the quantity `a·K_H/(s·ℓ)` is a
pure power of the diluteness `t = μa³`:

  `a·K_H/(s·ℓ) = t^{99/1292}`,

because `K_H = X^{-549/4}`, `s = X`, `ℓ = K_ℓ(μa)^{-1/2} = X^{-3/2}(μa)^{-1/2}`
and `(μa)^{1/2}·a = (μa³)^{1/2} = t^{1/2}`.  Hence it vanishes as `t → 0`, which
is the statement of the target lemma.

Exponents: `1/2 - 549/1292 - 1/323 + 3/646 = 99/1292`.
-/

noncomputable section

open scoped BigOperators
open Work.BoseB7 Work.BoseBox

namespace Work.BoseK15

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- `a·(μa)^{1/2} = (μa³)^{1/2}`, for `a, μ > 0`: this is the identity that
converts the potential strength `a` and the healing-length side `ℓ` into the
diluteness `t = μa³`. -/
lemma ascat_mul_sqrt_mu_ascat (E : Q3Env Mode) (hv : FSParamsView E) :
    E.aScat * (E.mu * E.aScat) ^ (1 / 2 : ℝ) = hv.t ^ (1 / 2 : ℝ) := by
  have ha : 0 < E.aScat := hv.a_pos
  have hμ : 0 < E.mu := Work.BoseB7.mu_pos E hv
  have h1 : (E.mu * E.aScat) ^ (1 / 2 : ℝ) = E.mu ^ (1 / 2 : ℝ) * E.aScat ^ (1 / 2 : ℝ) :=
    Real.mul_rpow hμ.le ha.le
  have h2 : E.aScat * E.aScat ^ (1 / 2 : ℝ) = E.aScat ^ (3 / 2 : ℝ) := by
    calc E.aScat * E.aScat ^ (1 / 2 : ℝ)
        = E.aScat ^ (1 : ℝ) * E.aScat ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = E.aScat ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add ha 1 (1 / 2)).symm
      _ = E.aScat ^ (3 / 2 : ℝ) := by congr 1; norm_num
  have h3 : (E.aScat ^ 3) ^ (1 / 2 : ℝ) = E.aScat ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast E.aScat 3, ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have h4 : (E.mu * E.aScat ^ 3) ^ (1 / 2 : ℝ) = E.mu ^ (1 / 2 : ℝ) * E.aScat ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hμ.le (pow_nonneg ha.le 3), h3]
  calc E.aScat * (E.mu * E.aScat) ^ (1 / 2 : ℝ)
      = E.aScat * (E.mu ^ (1 / 2 : ℝ) * E.aScat ^ (1 / 2 : ℝ)) := by rw [h1]
    _ = E.mu ^ (1 / 2 : ℝ) * (E.aScat * E.aScat ^ (1 / 2 : ℝ)) := by ring
    _ = E.mu ^ (1 / 2 : ℝ) * E.aScat ^ (3 / 2 : ℝ) := by rw [h2]
    _ = (E.mu * E.aScat ^ 3) ^ (1 / 2 : ℝ) := h4.symm
    _ = hv.t ^ (1 / 2 : ℝ) := by rw [hv.mu_eq]

/-- `K_H·(s·K_ℓ)^{-1} = t^{-547/1292}`: the `fsXp` bookkeeping for `K_H = X^{-549/4}`,
`s = X`, `K_ℓ = X^{-3/2}` (the `(μa)^{-1/2}` of `ℓ` is kept out). -/
lemma KH_s_Kl_fsXp (E : Q3Env Mode) (hv : FSParamsView E) :
    fsXp hv.t (-(549 / 4)) * (fsXp hv.t 1 * fsXp hv.t (-(3 / 2)))⁻¹
      = hv.t ^ (-(547 / 1292) : ℝ) := by
  have ht0 : 0 < hv.t := hv.t_pos
  have h1 : fsXp hv.t 1 * fsXp hv.t (-(3 / 2)) = fsXp hv.t (-(1 / 2)) := by
    rw [fsXp_mul ht0]
    congr 1
    norm_num
  have h2 : (fsXp hv.t (-(1 / 2)))⁻¹ = fsXp hv.t (1 / 2) := by
    rw [fsXp_inv ht0]
    congr 1
    norm_num
  have h3 : fsXp hv.t (-(549 / 4)) * fsXp hv.t (1 / 2) = fsXp hv.t (-(547 / 4)) := by
    rw [fsXp_mul ht0]
    congr 1
    norm_num
  have h4 : fsXp hv.t (-(547 / 4)) = hv.t ^ (-(547 / 1292) : ℝ) := by
    rw [fsXp]
    congr 1
    norm_num
  calc fsXp hv.t (-(549 / 4)) * (fsXp hv.t 1 * fsXp hv.t (-(3 / 2)))⁻¹
      = fsXp hv.t (-(549 / 4)) * (fsXp hv.t (-(1 / 2)))⁻¹ := by rw [h1]
    _ = fsXp hv.t (-(549 / 4)) * fsXp hv.t (1 / 2) := by rw [h2]
    _ = fsXp hv.t (-(547 / 4)) := h3
    _ = hv.t ^ (-(547 / 1292) : ℝ) := h4

theorem arith_aKH_div_sell_le (c : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → E.aScat * E.KH / (E.s * E.ell) ≤ c := by
  refine ⟨min 1 (c ^ 20), lt_min one_pos (pow_pos hc 20), ?_⟩
  intro Mode _ _ E hv ht
  have ht0 : 0 < hv.t := hv.t_pos
  have ht1 : hv.t ≤ 1 := le_trans ht (min_le_left _ _)
  have ht2 : hv.t ≤ c ^ 20 := le_trans ht (min_le_right _ _)
  have hμa : 0 < E.mu * E.aScat := mul_pos (Work.BoseB7.mu_pos E hv) hv.a_pos
  have hell : E.ell = fsXp hv.t (-(3 / 2)) * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ) := by
    rw [hv.ell_eq, Work.BoseB7.side, hv.Kl_eq]
  have hratio : E.aScat * E.KH / (E.s * E.ell) = hv.t ^ (99 / 1292 : ℝ) := by
    have hD : ((E.mu * E.aScat) ^ (-(1 / 2) : ℝ))⁻¹ = (E.mu * E.aScat) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hμa.le, inv_inv]
    have hsub : ((fsXp hv.t 1 * fsXp hv.t (-(3 / 2))) * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ))⁻¹
        = (E.mu * E.aScat) ^ (1 / 2 : ℝ) *
          (fsXp hv.t 1 * fsXp hv.t (-(3 / 2)))⁻¹ := by
      conv_lhs => rw [mul_inv_rev]
      rw [hD]
    rw [hell, hv.s_eq, Work.BoseB7.KH_val E hv]
    have hstep : E.aScat * fsXp hv.t (-(549 / 4)) /
          (fsXp hv.t 1 * (fsXp hv.t (-(3 / 2)) * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ)))
        = (E.aScat * (E.mu * E.aScat) ^ (1 / 2 : ℝ)) *
          (fsXp hv.t (-(549 / 4)) * (fsXp hv.t 1 * fsXp hv.t (-(3 / 2)))⁻¹) := by
      rw [← mul_assoc, div_eq_mul_inv, hsub]
      ring
    rw [hstep, ascat_mul_sqrt_mu_ascat E hv, KH_s_Kl_fsXp E hv]
    rw [← Real.rpow_add ht0]
    congr 1
    norm_num
  rw [hratio]
  have h1 : hv.t ^ (99 / 1292 : ℝ) ≤ hv.t ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
  have h2 : hv.t ^ (1 / 20 : ℝ) ≤ (c ^ 20) ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow ht0.le ht2 (by norm_num)
  have h3 : (c ^ 20) ^ (1 / 20 : ℝ) = c := by
    have he : (↑(20 : ℕ) : ℝ) * (1 / 20) = 1 := by norm_num
    rw [← Real.rpow_natCast c 20, ← Real.rpow_mul hc.le, he, Real.rpow_one]
  calc hv.t ^ (99 / 1292 : ℝ) ≤ hv.t ^ (1 / 20 : ℝ) := h1
    _ ≤ (c ^ 20) ^ (1 / 20 : ℝ) := h2
    _ = c := h3

end Work.BoseK15
