import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Statements
import Submission.Work.BoseB7A.arith_aKH_div_dsell_le
import Submission.Work.BoseB7A.arith_aKH_le_ell
import Submission.Work.BoseB7A.arith_aKH_log_div_dsell_le
import Submission.Work.BoseB7A.int_A_ge
import Submission.Work.BoseB7A.int_term_lowKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.estIntegralOneA` — FS `lem:EstimateIntegral` (`eq:CompIntegrals-Final`)

This file proves the headline `EstIntegralOneA K₀` of `Statements.lean`: from the
kernel interface `IntKernel K₀ R F E gHat` (the B4/B6 obligations of
`lem:EstimateIntegral`) and the FS parameter view, the `P_H` lattice sum
`ℓ⁻³Σ_{k∈P_H}Ŵ₁(k)α_k` is within `C ρ_za K_H⁻¹` of `ρ_zŴ₁ω(0)`, for a constant
`C = 2000 (max K₀ 1)^5 + 2000` and the threshold `t₀ = 2^{-323}`.

The proof decomposes the error as in FS's proof of `eq:CompIntegrals-Final`
(each piece is one lemma of this file):

* `estIntegralOneA_decomposition` — the triangle-inequality decomposition of
  `ρ_zŴ₁ω(0) − ℓ⁻³Σ_{P_H}Ŵ₁α` into the five pieces below
  (`IntKernel.omega_lattice` against the *full* lattice sum, the low-momentum
  tail `k ∉ P_H`, the `ĝ − Ŵ₁` difference, the `𝒜 − k²` difference, and the
  second-order `α`-correction `alpha_secondOrder_bound`);
* `estIntegralOneA_gHat_term` — the `ĝ − Ŵ₁` piece (an `ε = K_H⁻¹` AM-GM plus
  `sum_W1sq`, `sum_diff` and `(R/ℓ)² ≤ K_H⁻¹`);
* `estIntegralOneA_A_diff_term` — the `𝒜 − k²` piece (split into the `ρ|Ŵ₁|`
  part, `sum_inv4`, and the `k² − τ` kinetic part, `sum_inv3`/`sum_W1sq`);
* `estIntegralOneA_cubic_term` — the second-order `α` piece (`sum_inv6`);
* `Work.BoseB7A.int_term_lowKernel` — the low-momentum tail (`low_sum`).

The scalar arithmetic of the FS parameter point is in the companion lemmas
`arith_KH_sqrt_t_le_Kl`, `arith_aKH_le_ell`, `arith_aKH_div_dsell_le`,
`arith_aKH_log_div_dsell_le`, `int_A_ge` (all in this directory).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

lemma estIntegralOneA_Kc_ge_one (K₀ : ℝ) : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _

lemma estIntegralOneA_K0_le_Kc5 (K₀ : ℝ) : K₀ ≤ (max K₀ 1) ^ 5 := by
  have h1 : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _
  have h2 : max K₀ 1 ≤ (max K₀ 1) ^ 5 := by
    have h3 : (1 : ℝ) ≤ (max K₀ 1) ^ 4 := one_le_pow₀ h1
    calc max K₀ 1 = max K₀ 1 * 1 := by ring
      _ ≤ max K₀ 1 * (max K₀ 1) ^ 4 := mul_le_mul_of_nonneg_left h3 (le_trans zero_le_one h1)
      _ = (max K₀ 1) ^ 5 := by ring
  exact le_trans (le_max_left _ _) h2

lemma estIntegralOneA_K0_div2_mul_le {K₀ x : ℝ} (hx : 0 ≤ x) :
    K₀ / 2 * x ≤ 200 * (max K₀ 1) ^ 5 * x := by
  have h : K₀ / 2 ≤ 200 * (max K₀ 1) ^ 5 := by
    have h1 := estIntegralOneA_K0_le_Kc5 K₀
    have h2 : (1 : ℝ) ≤ (max K₀ 1) ^ 5 := one_le_pow₀ (estIntegralOneA_Kc_ge_one K₀)
    linarith
  exact mul_le_mul_of_nonneg_right h hx


lemma estIntegralOneA_norm_pos {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    {k : Mode} (hk : k ∈ F.PHset E) : 0 < ‖F.kmom k‖ := by
  have hkPH : F.PH E.KH E.aScat k :=
    (Finset.mem_filter.mp (by simpa [Work.BoseB7.FockData.PHset] using hk)).2
  have h0 : 0 < 1 / (2 * E.KH * E.aScat) := by
    have h1 : 0 < E.aScat := hv.a_pos
    have h2 : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
    positivity
  have h1 : (1 : ℝ) / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hkPH
  linarith

lemma estIntegralOneA_gHat_term {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E)
    (hK₀ : 0 ≤ K₀) (hR : (R / E.ell) ^ 2 ≤ E.KH⁻¹) :
    E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)
      ≤ 200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹ := by
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKHinv : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKH.le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 < E.ell ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hKc1 : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _
  have hKc : K₀ ≤ max K₀ 1 := le_max_left _ _
  have hpt : ∀ k ∈ F.PHset E,
      |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)
        ≤ E.KH⁻¹ * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 / 4)
          + E.KH * ((gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 / 4) := by
    intro k hk
    have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv hk
    have hne : ‖F.kmom k‖ ^ 2 ≠ 0 := by positivity
    have ham : 2 * |E.W1 k| * |gHat k - E.W1 k|
        ≤ E.KH⁻¹ * E.W1 k ^ 2 + E.KH * (gHat k - E.W1 k) ^ 2 := by
      have hexp : 0 ≤ (|E.W1 k| - |gHat k - E.W1 k| * E.KH) ^ 2 := sq_nonneg _
      have h1 : |E.W1 k| ^ 2 = E.W1 k ^ 2 := sq_abs _
      have h2 : |gHat k - E.W1 k| ^ 2 = (gHat k - E.W1 k) ^ 2 := sq_abs _
      have hmul : (2 * |E.W1 k| * |gHat k - E.W1 k|) * E.KH
          ≤ (E.KH⁻¹ * E.W1 k ^ 2 + E.KH * (gHat k - E.W1 k) ^ 2) * E.KH := by
        have h3 : (E.KH⁻¹ * E.W1 k ^ 2 + E.KH * (gHat k - E.W1 k) ^ 2) * E.KH
            = E.W1 k ^ 2 + E.KH ^ 2 * (gHat k - E.W1 k) ^ 2 := by
          field_simp
        rw [h3]
        nlinarith [hexp, h1, h2]
      by_contra hcon
      simp only [not_le] at hcon
      have hc := mul_lt_mul_of_pos_right hcon hKH
      linarith [hmul, hc]
    have hx4 : 0 < 4 * ‖F.kmom k‖ ^ 2 := by positivity
    have hstep : |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)
        = (2 * |E.W1 k| * |gHat k - E.W1 k|) / (4 * ‖F.kmom k‖ ^ 2) := by ring
    rw [hstep]
    refine le_trans (div_le_div_of_nonneg_right ham hx4.le) ?_
    have heq : E.KH⁻¹ * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 / 4)
          + E.KH * ((gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 / 4)
        = (E.KH⁻¹ * E.W1 k ^ 2 + E.KH * (gHat k - E.W1 k) ^ 2) / (4 * ‖F.kmom k‖ ^ 2) := by
      field_simp
    rw [heq]
  have hsum : ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)
      ≤ E.KH⁻¹ * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) / 4)
          + E.KH * ((∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) / 4) := by
    calc ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)
        ≤ ∑ k ∈ F.PHset E, (E.KH⁻¹ * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 / 4)
            + E.KH * ((gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 / 4)) := Finset.sum_le_sum hpt
      _ = E.KH⁻¹ * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) / 4)
            + E.KH * ((∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) / 4) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_div, Finset.sum_div]
  have hB1 : E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
      ≤ K₀ * E.aScat := hK.sum_W1sq
  have hB2 : E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2)
      ≤ K₀ * E.aScat * (R / E.ell) ^ 4 := hK.sum_diff
  have hmain : E.ell ^ (-(3 : ℝ)) *
      (∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ (E.KH⁻¹ * (K₀ * E.aScat) + E.KH * (K₀ * E.aScat * (R / E.ell) ^ 4)) / 4 := by
    calc E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
        ≤ E.ell ^ (-(3 : ℝ)) * (E.KH⁻¹ * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) / 4)
            + E.KH * ((∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) / 4)) :=
          mul_le_mul_of_nonneg_left hsum hℓ3.le
      _ = (E.KH⁻¹ * (E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2))
            + E.KH * (E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2))) / 4 := by
          ring
      _ ≤ (E.KH⁻¹ * (K₀ * E.aScat) + E.KH * (K₀ * E.aScat * (R / E.ell) ^ 4)) / 4 := by
          have h1 := mul_le_mul_of_nonneg_left hB1 hKHinv
          have h2 := mul_le_mul_of_nonneg_left hB2 hKH.le
          linarith
  have hR4 : (R / E.ell) ^ 4 ≤ (E.KH⁻¹) ^ 2 := by
    calc (R / E.ell) ^ 4 = ((R / E.ell) ^ 2) ^ 2 := by ring
      _ ≤ (E.KH⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) hR 2
  have hb : E.KH * (E.aScat * (R / E.ell) ^ 4) ≤ E.aScat * E.KH⁻¹ := by
    calc E.KH * (E.aScat * (R / E.ell) ^ 4) = E.aScat * (E.KH * (R / E.ell) ^ 4) := by ring
      _ ≤ E.aScat * ((E.KH⁻¹) ^ 2 * E.KH) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          calc E.KH * (R / E.ell) ^ 4 ≤ E.KH * (E.KH⁻¹) ^ 2 :=
                mul_le_mul_of_nonneg_left hR4 hKH.le
            _ = (E.KH⁻¹) ^ 2 * E.KH := by ring
      _ = E.aScat * E.KH⁻¹ := by field_simp
  have hb2 : E.KH * (K₀ * E.aScat * (R / E.ell) ^ 4) ≤ K₀ * E.aScat * E.KH⁻¹ := by
    have h3 := mul_le_mul_of_nonneg_left hb hK₀
    linarith [h3]
  have hfin : (E.KH⁻¹ * (K₀ * E.aScat) + E.KH * (K₀ * E.aScat * (R / E.ell) ^ 4)) / 4
      ≤ 200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹ := by
    have hmid : E.KH⁻¹ * (K₀ * E.aScat) + E.KH * (K₀ * E.aScat * (R / E.ell) ^ 4)
        ≤ 2 * (K₀ * E.aScat * E.KH⁻¹) := by linarith
    have h4 : (2 * (K₀ * E.aScat * E.KH⁻¹)) / 4 = (K₀ / 2) * E.aScat * E.KH⁻¹ := by ring
    have h5 : (K₀ / 2) * E.aScat * E.KH⁻¹ ≤ 200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹ := by
      have h6 := estIntegralOneA_K0_div2_mul_le (K₀ := K₀) (x := E.aScat * E.KH⁻¹)
        (by positivity : (0 : ℝ) ≤ E.aScat * E.KH⁻¹)
      have h7 : (K₀ / 2) * E.aScat * E.KH⁻¹ = K₀ / 2 * (E.aScat * E.KH⁻¹) := by ring
      have h8 : 200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹
          = 200 * (max K₀ 1) ^ 5 * (E.aScat * E.KH⁻¹) := by ring
      linarith [h6]
    linarith [hmid, h4, h5]
  linarith [hmain, hfin]

lemma estIntegralOneA_cubic_term {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E)
    (hK₀ : 0 ≤ K₀) (hAge : ∀ k ∈ F.PHset E, ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k) :
    E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
  have ha : 0 < E.aScat := hv.a_pos
  have hρ : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 < E.ell ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hpt : ∀ k ∈ F.PHset E,
      2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
        ≤ 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 / ‖F.kmom k‖ ^ 6 := by
    intro k hk
    have hA : ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k := hAge k hk
    have hkPH : F.PH E.KH E.aScat k :=
      (Finset.mem_filter.mp (by simpa [Work.BoseB7.FockData.PHset] using hk)).2
    have hx : 0 < ‖F.kmom k‖ := by
      have h0 : 0 < 1 / (2 * E.KH * E.aScat) := by positivity
      have h1 : (1 : ℝ) / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hkPH
      linarith
    have hApos : 0 < E.A k := by
      have : 0 < ‖F.kmom k‖ ^ 2 / 3 := by positivity
      linarith
    have hW : E.W1 k ^ 4 ≤ (K₀ * E.aScat) ^ 4 := by
      have h1 : |E.W1 k| ≤ K₀ * E.aScat := hK.W1_le k
      have h2 : |E.W1 k| ^ 4 ≤ (K₀ * E.aScat) ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 4
      have h3 : |E.W1 k| ^ 4 = E.W1 k ^ 4 := by
        calc |E.W1 k| ^ 4 = (|E.W1 k| ^ 2) ^ 2 := by ring
          _ = (E.W1 k ^ 2) ^ 2 := by rw [sq_abs]
          _ = E.W1 k ^ 4 := by ring
      rwa [h3] at h2
    have hinv : 1 / E.A k ^ 3 ≤ 27 / ‖F.kmom k‖ ^ 6 := by
      have h1 : ‖F.kmom k‖ ^ 6 ≤ 27 * E.A k ^ 3 := by
        have h3 : ‖F.kmom k‖ ^ 2 ≤ 3 * E.A k := by linarith
        have h2 : (‖F.kmom k‖ ^ 2) ^ 3 ≤ (3 * E.A k) ^ 3 :=
          pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ‖F.kmom k‖ ^ 2) h3 3
        calc ‖F.kmom k‖ ^ 6 = (‖F.kmom k‖ ^ 2) ^ 3 := by ring
          _ ≤ (3 * E.A k) ^ 3 := h2
          _ = 27 * E.A k ^ 3 := by ring
      have hx6 : 0 < ‖F.kmom k‖ ^ 6 := by positivity
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < E.A k ^ 3) hx6]
      linarith
    have h2ρ : 0 ≤ 2 * E.rho ^ 3 := by positivity
    have hK0a : 0 ≤ K₀ * E.aScat := mul_nonneg hK₀ ha.le
    have h2 : 0 ≤ 2 * E.rho ^ 3 * (K₀ * E.aScat) ^ 4 :=
      mul_nonneg h2ρ (pow_nonneg hK0a 4)
    have hAinv : 0 ≤ 1 / E.A k ^ 3 := div_nonneg zero_le_one (pow_nonneg hApos.le 3)
    calc 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
        = 2 * E.rho ^ 3 * E.W1 k ^ 4 * (1 / E.A k ^ 3) := by ring
      _ ≤ 2 * E.rho ^ 3 * (K₀ * E.aScat) ^ 4 * (1 / E.A k ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW h2ρ) hAinv
      _ ≤ 2 * E.rho ^ 3 * (K₀ * E.aScat) ^ 4 * (27 / ‖F.kmom k‖ ^ 6) :=
          mul_le_mul_of_nonneg_left hinv h2
      _ = 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 / ‖F.kmom k‖ ^ 6 := by ring
  have hsum : ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
      ≤ 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    calc 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
        ≤ 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 / ‖F.kmom k‖ ^ 6 := hpt k hk
      _ = 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 * (1 / ‖F.kmom k‖ ^ 6) := by ring
  have h6 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6
      ≤ K₀ * (E.KH * E.aScat) ^ 3 := hK.sum_inv6
  have hmain : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
      ≤ 54 * K₀ ^ 5 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3 := by
    calc E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
        ≤ E.ell ^ (-(3 : ℝ)) *
            (54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6) :=
          mul_le_mul_of_nonneg_left hsum hℓ3.le
      _ = 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 *
            (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6) := by ring
      _ ≤ 54 * E.rho ^ 3 * K₀ ^ 4 * E.aScat ^ 4 * (K₀ * (E.KH * E.aScat) ^ 3) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 54 * K₀ ^ 5 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3 := by ring
  have ht : hv.t ^ 2 * E.KH ^ 4 ≤ 1 := by
    have hKH4 : E.KH ^ 4 = Work.BoseBox.fsXp hv.t (-549) := by
      rw [KH_val E hv, Work.BoseBox.fsXp_pow hv.t_pos.le]
      congr 1
      norm_num
    have ht2 : hv.t ^ 2 = Work.BoseBox.fsXp hv.t 646 := by
      conv_lhs => rw [Work.BoseBox.delta_eq_fsXp hv.t_pos.le]
      rw [Work.BoseBox.fsXp_pow hv.t_pos.le]
      congr 1
      norm_num
    rw [hKH4, ht2, Work.BoseBox.fsXp_mul hv.t_pos]
    rw [show (646 : ℝ) + -549 = 97 by norm_num]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hfac : E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4 ≤ 9 / 4 := by
    have h3 : E.rho ^ 2 * E.aScat ^ 6 ≤ 9 / 4 * (hv.t ^ 2) := by
      have h1 : E.rho ≤ 3 * E.mu / 2 := Work.BoseB7.rho_le E hv
      have h2 : E.rho ^ 2 ≤ (3 * E.mu / 2) ^ 2 := by nlinarith [hρ]
      have h2b : E.rho ^ 2 * E.aScat ^ 6 ≤ (3 * E.mu / 2) ^ 2 * E.aScat ^ 6 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : E.mu ^ 2 * E.aScat ^ 6 = hv.t ^ 2 := by
        rw [← hv.mu_eq]; ring
      have h5 : (3 * E.mu / 2) ^ 2 * E.aScat ^ 6 = 9 / 4 * (E.mu ^ 2 * E.aScat ^ 6) := by ring
      rw [h5, h4] at h2b
      exact h2b
    calc E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4
        ≤ (9 / 4 * hv.t ^ 2) * E.KH ^ 4 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 9 / 4 * (hv.t ^ 2 * E.KH ^ 4) := by ring
      _ ≤ 9 / 4 * 1 := by linarith
      _ = 9 / 4 := by ring
  have hfinal : 54 * K₀ ^ 5 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
    have hKc1 : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _
    have hKc : K₀ ≤ max K₀ 1 := le_max_left _ _
    have hρa : 0 ≤ E.rho * E.aScat * E.KH⁻¹ := by positivity
    have hkey : E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3 ≤ 9 / 4 * (E.rho * E.aScat * E.KH⁻¹) := by
      have h1 : E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3
          = (E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4) * (E.rho * E.aScat * E.KH⁻¹) := by
        field_simp
      rw [h1]
      calc (E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4) * (E.rho * E.aScat * E.KH⁻¹)
          ≤ (9 / 4) * (E.rho * E.aScat * E.KH⁻¹) := mul_le_mul_of_nonneg_right hfac hρa
        _ = 9 / 4 * (E.rho * E.aScat * E.KH⁻¹) := rfl
    have h3 : 54 * K₀ ^ 5 * (9 / 4) ≤ 200 * (max K₀ 1) ^ 5 := by
      have h4 : K₀ ^ 5 ≤ (max K₀ 1) ^ 5 := pow_le_pow_left₀ hK₀ hKc 5
      have h5 : (1 : ℝ) ≤ (max K₀ 1) ^ 5 := one_le_pow₀ hKc1
      nlinarith
    calc 54 * K₀ ^ 5 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3
        = 54 * K₀ ^ 5 * (E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 3) := by ring
      _ ≤ 54 * K₀ ^ 5 * (9 / 4 * (E.rho * E.aScat * E.KH⁻¹)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (54 * K₀ ^ 5 * (9 / 4)) * (E.rho * E.aScat * E.KH⁻¹) := by ring
      _ ≤ 200 * (max K₀ 1) ^ 5 * (E.rho * E.aScat * E.KH⁻¹) :=
          mul_le_mul_of_nonneg_right h3 hρa
      _ = 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by ring
  linarith [hmain, hfinal]

lemma estIntegralOneA_A_diff_term {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E)
    (hK₀ : 0 ≤ K₀) (hAge : ∀ k ∈ F.PHset E, ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k)
    (hsmall : E.aScat * E.KH / (E.d * E.s * E.ell) ≤ 1)
    (hlog : E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH) ≤ 1) :
    E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
          (2 * ‖F.kmom k‖ ^ 2 * E.A k)
      ≤ 400 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
  have ha : 0 < E.aScat := hv.a_pos
  have hρ : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKHinv : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKH.le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 < E.ell ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hd : 0 < E.d := by rw [d_val E hv]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hds : 0 < E.d * E.s * E.ell := by positivity
  -- pointwise
  have hpt : ∀ k ∈ F.PHset E,
      E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
        ≤ 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
          + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := by
    intro k hk
    have hkPH : F.PH E.KH E.aScat k :=
      (Finset.mem_filter.mp (by simpa [Work.BoseB7.FockData.PHset] using hk)).2
    have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv hk
    have hx2 : 0 < ‖F.kmom k‖ ^ 2 := by positivity
    have hA : ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k := hAge k hk
    have hApos : 0 < E.A k := by
      have : 0 < ‖F.kmom k‖ ^ 2 / 3 := by positivity
      linarith
    have hAeq : E.A k = E.tau k + E.rho * E.W1 k := hK.A_eq k
    have htau := hK.tau_PH k hkPH
    have htau1 : 0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k := htau.1
    have htau2 : ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) := htau.2
    have hW := hK.W1_le k
    have hds : 0 < E.d * E.s * E.ell := by
      have h1 : 0 < E.d := by
        rw [d_val E hv]; exact Work.BoseBox.fsXp_pos hv.t_pos
      have h2 : 0 < E.s := by
        rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
      positivity
    -- |A - k²| ≤ (k² - τ) + ρ|W1|
    have hsplit : |E.A k - ‖F.kmom k‖ ^ 2| ≤ (‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k| := by
      have h1 : E.A k - ‖F.kmom k‖ ^ 2 = -(‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * E.W1 k := by
        rw [hAeq]; ring
      rw [h1]
      have h2 : |-(‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * E.W1 k|
          ≤ |-(‖F.kmom k‖ ^ 2 - E.tau k)| + |E.rho * E.W1 k| := abs_add_le _ _
      rw [abs_neg, abs_of_nonneg htau1, abs_mul, abs_of_nonneg hρ] at h2
      exact h2
    -- 1/(2k²A) ≤ 3/(2k⁴)
    have hinvA : 1 / (2 * ‖F.kmom k‖ ^ 2 * E.A k) ≤ 3 / (2 * ‖F.kmom k‖ ^ 4) := by
      have h1 : 1 / E.A k ≤ 3 / ‖F.kmom k‖ ^ 2 := by
        rw [div_le_div_iff₀ hApos hx2]
        linarith [hA]
      calc 1 / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
          = (1 / ‖F.kmom k‖ ^ 2) * (1 / E.A k) * (1 / 2) := by ring
        _ ≤ (1 / ‖F.kmom k‖ ^ 2) * (3 / ‖F.kmom k‖ ^ 2) * (1 / 2) := by
            have h2 : 0 ≤ 1 / ‖F.kmom k‖ ^ 2 := by positivity
            have h3 : 0 ≤ (1 : ℝ) / 2 := by norm_num
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h2) le_rfl h3 (by positivity)
        _ = 3 / (2 * ‖F.kmom k‖ ^ 4) := by ring
    -- the two pieces
    have hnum : 0 ≤ E.rho * E.W1 k ^ 2 := by positivity
    have hstep1 : E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
        ≤ E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
            / (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by
      have h0 : 0 ≤ E.rho * E.W1 k ^ 2 := by positivity
      calc E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
          = (E.rho * E.W1 k ^ 2) * (|E.A k - ‖F.kmom k‖ ^ 2| / (2 * ‖F.kmom k‖ ^ 2 * E.A k)) := by ring
        _ ≤ (E.rho * E.W1 k ^ 2) *
              (((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|) / (2 * ‖F.kmom k‖ ^ 2 * E.A k)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsplit (by positivity)) h0
        _ = E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
            / (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by ring
    have hstep2 : E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
            / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
        ≤ 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
          + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := by
      have hX : 0 ≤ (‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k| :=
        add_nonneg htau1 (mul_nonneg hρ (abs_nonneg _))
      have h3 : E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
            / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
          ≤ E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
              * (3 / (2 * ‖F.kmom k‖ ^ 4)) := by
        have h0 : 0 ≤ E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|) :=
          mul_nonneg (by positivity) hX
        calc E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
              / (2 * ‖F.kmom k‖ ^ 2 * E.A k)
            = (E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|))
                * (1 / (2 * ‖F.kmom k‖ ^ 2 * E.A k)) := by ring
          _ ≤ (E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|))
                * (3 / (2 * ‖F.kmom k‖ ^ 4)) := mul_le_mul_of_nonneg_left hinvA h0
      refine le_trans h3 ?_
      -- expand and bound
      have hW3 : E.W1 k ^ 2 * |E.W1 k| ≤ K₀ ^ 3 * E.aScat ^ 3 := by
        have h2 : |E.W1 k| ^ 3 ≤ (K₀ * E.aScat) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hW 3
        have h3 : E.W1 k ^ 2 * |E.W1 k| = |E.W1 k| ^ 3 := by
          rw [show |E.W1 k| ^ 3 = |E.W1 k| ^ 2 * |E.W1 k| by ring, sq_abs]
        rw [h3]
        calc |E.W1 k| ^ 3 ≤ (K₀ * E.aScat) ^ 3 := h2
          _ = K₀ ^ 3 * E.aScat ^ 3 := by ring
      have htau3 : ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) := htau2
      -- piece 1
      have hp1 : E.rho * E.W1 k ^ 2 * (‖F.kmom k‖ ^ 2 - E.tau k) * (3 / (2 * ‖F.kmom k‖ ^ 4))
          ≤ 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3) := by
        have h0 : 0 ≤ E.rho * E.W1 k ^ 2 := by positivity
        have h1 : E.rho * E.W1 k ^ 2 * (‖F.kmom k‖ ^ 2 - E.tau k) * (3 / (2 * ‖F.kmom k‖ ^ 4))
            ≤ E.rho * E.W1 k ^ 2 * (2 * ‖F.kmom k‖ / (E.d * E.s * E.ell)) * (3 / (2 * ‖F.kmom k‖ ^ 4)) := by
          have h2 : E.rho * E.W1 k ^ 2 * (‖F.kmom k‖ ^ 2 - E.tau k)
              ≤ E.rho * E.W1 k ^ 2 * (2 * ‖F.kmom k‖ / (E.d * E.s * E.ell)) :=
            mul_le_mul_of_nonneg_left htau3 h0
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
        refine le_trans h1 (le_of_eq ?_)
        field_simp
      -- piece 2
      have hp2 : E.rho * E.W1 k ^ 2 * (E.rho * |E.W1 k|) * (3 / (2 * ‖F.kmom k‖ ^ 4))
          ≤ 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := by
        have h2 : E.rho * E.W1 k ^ 2 * (E.rho * |E.W1 k|) = E.rho ^ 2 * (E.W1 k ^ 2 * |E.W1 k|) := by ring
        rw [h2]
        have h3 : E.rho ^ 2 * (E.W1 k ^ 2 * |E.W1 k|) ≤ E.rho ^ 2 * (K₀ ^ 3 * E.aScat ^ 3) :=
          mul_le_mul_of_nonneg_left hW3 (by positivity)
        have h4 : E.rho ^ 2 * (K₀ ^ 3 * E.aScat ^ 3) * (3 / (2 * ‖F.kmom k‖ ^ 4))
            = 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := by ring
        calc E.rho ^ 2 * (E.W1 k ^ 2 * |E.W1 k|) * (3 / (2 * ‖F.kmom k‖ ^ 4))
            ≤ E.rho ^ 2 * (K₀ ^ 3 * E.aScat ^ 3) * (3 / (2 * ‖F.kmom k‖ ^ 4)) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := h4
      calc E.rho * E.W1 k ^ 2 * ((‖F.kmom k‖ ^ 2 - E.tau k) + E.rho * |E.W1 k|)
              * (3 / (2 * ‖F.kmom k‖ ^ 4))
          = E.rho * E.W1 k ^ 2 * (‖F.kmom k‖ ^ 2 - E.tau k) * (3 / (2 * ‖F.kmom k‖ ^ 4))
            + E.rho * E.W1 k ^ 2 * (E.rho * |E.W1 k|) * (3 / (2 * ‖F.kmom k‖ ^ 4)) := by ring
        _ ≤ 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
              + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4) := add_le_add hp1 hp2
    linarith [hstep1, hstep2]
  have hsum0 : ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
          (2 * ‖F.kmom k‖ ^ 2 * E.A k)
      ≤ ∑ k ∈ F.PHset E, (3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
          + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4)) :=
    Finset.sum_le_sum hpt
  -- pointwise comparison on the far region ‖k‖ ≥ 1/a
  have hpt2 : ∀ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
      E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3 ≤ E.aScat * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
    intro k hk
    have hkP : k ∈ F.PHset E := (Finset.mem_filter.mp hk).1
    have hkgt : 1 / E.aScat < ‖F.kmom k‖ := not_le.mp (Finset.mem_filter.mp hk).2
    have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv hkP
    have h1 : (1 : ℝ) / ‖F.kmom k‖ ^ 3 ≤ E.aScat / ‖F.kmom k‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : E.aScat * (1 / E.aScat) < E.aScat * ‖F.kmom k‖ :=
        mul_lt_mul_of_pos_left hkgt ha
      have h4 : E.aScat * (1 / E.aScat) = 1 := by
        rw [mul_one_div, div_self (ne_of_gt ha)]
      rw [h4] at h3
      nlinarith [h3, hx]
    calc E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3 = E.W1 k ^ 2 * (1 / ‖F.kmom k‖ ^ 3) := by ring
      _ ≤ E.W1 k ^ 2 * (E.aScat / ‖F.kmom k‖ ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = E.aScat * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by ring
  have hsum1 : E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)
      ≤ K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2 := by
    have hsplit : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3
        = (∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)
          + (∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3) :=
      (Finset.sum_filter_add_sum_filter_not (F.PHset E) (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat)
        (fun k => E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)).symm
    rw [hsplit, mul_add]
    refine add_le_add ?_ ?_
    · have h1 : ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3
          ≤ ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
              K₀ ^ 2 * E.aScat ^ 2 / ‖F.kmom k‖ ^ 3 := by
        apply Finset.sum_le_sum
        intro k hk
        have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv (Finset.mem_filter.mp hk).1
        have hW2 : E.W1 k ^ 2 ≤ K₀ ^ 2 * E.aScat ^ 2 := by
          have h3 : |E.W1 k| ^ 2 ≤ (K₀ * E.aScat) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hK.W1_le k) 2
          rwa [sq_abs, mul_pow] at h3
        exact div_le_div_of_nonneg_right hW2 (by positivity)
      calc E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)
          ≤ E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
              K₀ ^ 2 * E.aScat ^ 2 / ‖F.kmom k‖ ^ 3) :=
            mul_le_mul_of_nonneg_left h1 hℓ3.le
        _ = K₀ ^ 2 * E.aScat ^ 2 *
            (E.ell ^ (-(3 : ℝ)) *
              ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
                1 / ‖F.kmom k‖ ^ 3) := by
            have h2 : (∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
                  K₀ ^ 2 * E.aScat ^ 2 / ‖F.kmom k‖ ^ 3)
                = K₀ ^ 2 * E.aScat ^ 2 *
                  (∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat),
                    1 / ‖F.kmom k‖ ^ 3) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            rw [h2]
            ring
        _ ≤ K₀ ^ 2 * E.aScat ^ 2 * (K₀ * (1 + Real.log E.KH)) :=
            mul_le_mul_of_nonneg_left hK.sum_inv3 (by positivity)
        _ = K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) := by ring
    · have hsub : (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)) ⊆ F.PHset E :=
        Finset.filter_subset _ _
      have hle : ∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
          ≤ ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
      have h1 : ∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3
          ≤ E.aScat * (∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hpt2
      calc E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)
          ≤ E.ell ^ (-(3 : ℝ)) * (E.aScat *
              (∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
                E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) := mul_le_mul_of_nonneg_left h1 hℓ3.le
        _ = E.aScat * (E.ell ^ (-(3 : ℝ)) *
              (∑ k ∈ (F.PHset E).filter (fun k => ¬ (‖F.kmom k‖ ≤ 1 / E.aScat)),
                E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) := by ring
        _ ≤ E.aScat * (E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hℓ3.le) ha.le
        _ ≤ E.aScat * (K₀ * E.aScat) := mul_le_mul_of_nonneg_left hK.sum_W1sq ha.le
        _ = K₀ * E.aScat ^ 2 := by ring
  have hmain1 : E.ell ^ (-(3 : ℝ)) *
        (∑ k ∈ F.PHset E, 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3))
      ≤ 3 * E.rho / (E.d * E.s * E.ell) *
        (K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2) := by
    have h1 : ∑ k ∈ F.PHset E, 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
        = 3 * E.rho / (E.d * E.s * E.ell) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv hk
      field_simp
    rw [h1]
    calc E.ell ^ (-(3 : ℝ)) *
          (3 * E.rho / (E.d * E.s * E.ell) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3)
        = 3 * E.rho / (E.d * E.s * E.ell) *
          (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 3) := by ring
      _ ≤ 3 * E.rho / (E.d * E.s * E.ell) *
          (K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2) :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
  have hmain2 : E.ell ^ (-(3 : ℝ)) *
        (∑ k ∈ F.PHset E, 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4))
      ≤ 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH := by
    have h1 : ∑ k ∈ F.PHset E, 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4)
        = 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / 2 * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [h1]
    calc E.ell ^ (-(3 : ℝ)) *
          (3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / 2 * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4)
        = 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / 2 *
          (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4) := by ring
      _ ≤ 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / 2 * (K₀ * E.KH * E.aScat) :=
          mul_le_mul_of_nonneg_left hK.sum_inv4 (by positivity)
      _ = 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH := by ring
  -- parameter arithmetic
  have htKH : hv.t * E.KH ^ 2 ≤ 1 := by
    have hKH2 : E.KH ^ 2 = Work.BoseBox.fsXp hv.t (-(549 / 2)) := by
      rw [KH_val E hv, Work.BoseBox.fsXp_pow hv.t_pos.le]
      congr 1
      norm_num
    calc hv.t * E.KH ^ 2 = Work.BoseBox.fsXp hv.t 323 * Work.BoseBox.fsXp hv.t (-(549 / 2)) := by
          nth_rewrite 1 [Work.BoseBox.delta_eq_fsXp hv.t_pos.le]
          rw [hKH2]
      _ = Work.BoseBox.fsXp hv.t (97 / 2) := by
          rw [Work.BoseBox.fsXp_mul hv.t_pos, show (323 : ℝ) + -(549 / 2) = 97 / 2 by norm_num]
      _ ≤ 1 := Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hρa3 : E.rho * E.aScat ^ 3 * E.KH ^ 2 ≤ 3 / 2 := by
    have h1 : E.rho ≤ 3 * E.mu / 2 := Work.BoseB7.rho_le E hv
    have h2 : E.rho * E.aScat ^ 3 * E.KH ^ 2 ≤ (3 * E.mu / 2) * E.aScat ^ 3 * E.KH ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (3 * E.mu / 2) * E.aScat ^ 3 * E.KH ^ 2 = 3 / 2 * (hv.t * E.KH ^ 2) := by
      rw [← hv.mu_eq]; ring
    linarith [h2, h3, htKH]
  have hfin1 : 3 * E.rho / (E.d * E.s * E.ell) *
        (K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2)
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
    have hfac : 3 * E.rho / (E.d * E.s * E.ell) *
          (K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2)
        = 3 * E.rho * E.aScat * E.KH⁻¹ *
            (E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ^ 3 * (1 + Real.log E.KH)
              + E.aScat * E.KH / (E.d * E.s * E.ell) * K₀) := by
      field_simp
    rw [hfac]
    have h1 : E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH) ≤ 1 := hlog
    have h2 : E.aScat * E.KH / (E.d * E.s * E.ell) ≤ 1 := hsmall
    have hb : E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ^ 3 * (1 + Real.log E.KH)
          + E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ≤ K₀ ^ 3 + K₀ := by
      have h3 : E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ^ 3 * (1 + Real.log E.KH)
          ≤ K₀ ^ 3 := by
        have h4 : E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ^ 3 * (1 + Real.log E.KH)
            = (E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH)) * K₀ ^ 3 := by ring
        rw [h4]
        exact mul_le_of_le_one_left (by positivity) h1
      have h5 : E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ≤ K₀ :=
        mul_le_of_le_one_left hK₀ h2
      linarith
    have hc : 3 * E.rho * E.aScat * E.KH⁻¹ * (K₀ ^ 3 + K₀)
        ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
      have h11 : (3 : ℝ) * (K₀ ^ 3 + K₀) ≤ 200 * (max K₀ 1) ^ 5 := by
        have h7 : K₀ ^ 3 ≤ (max K₀ 1) ^ 5 := by
          have h8 : K₀ ^ 3 ≤ (max K₀ 1) ^ 3 := pow_le_pow_left₀ hK₀ (le_max_left _ _) 3
          have h9 : (max K₀ 1) ^ 3 ≤ (max K₀ 1) ^ 5 :=
            pow_le_pow_right₀ (estIntegralOneA_Kc_ge_one K₀) (by norm_num)
          linarith
        have h10 : K₀ ≤ (max K₀ 1) ^ 5 := estIntegralOneA_K0_le_Kc5 K₀
        have h12 : (1 : ℝ) ≤ (max K₀ 1) ^ 5 := one_le_pow₀ (estIntegralOneA_Kc_ge_one K₀)
        linarith
      calc 3 * E.rho * E.aScat * E.KH⁻¹ * (K₀ ^ 3 + K₀)
          = (3 * (K₀ ^ 3 + K₀)) * (E.rho * E.aScat * E.KH⁻¹) := by ring
        _ ≤ (200 * (max K₀ 1) ^ 5) * (E.rho * E.aScat * E.KH⁻¹) :=
            mul_le_mul_of_nonneg_right h11 (by positivity)
        _ = 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by ring
    calc 3 * E.rho * E.aScat * E.KH⁻¹ *
          (E.aScat * E.KH / (E.d * E.s * E.ell) * K₀ ^ 3 * (1 + Real.log E.KH)
            + E.aScat * E.KH / (E.d * E.s * E.ell) * K₀)
        ≤ 3 * E.rho * E.aScat * E.KH⁻¹ * (K₀ ^ 3 + K₀) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := hc
  have hfin2 : 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
    have hkey : E.rho ^ 2 * E.aScat ^ 4 * E.KH
        = (E.rho * E.aScat ^ 3 * E.KH ^ 2) * (E.rho * E.aScat * E.KH⁻¹) := by
      field_simp
    have hfac : 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH
        = (3 / 2 * K₀ ^ 4) *
            ((E.rho * E.aScat ^ 3 * E.KH ^ 2) * (E.rho * E.aScat * E.KH⁻¹)) := by
      have e1 : 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH
          = (3 / 2 * K₀ ^ 4) * (E.rho ^ 2 * E.aScat ^ 4 * E.KH) := by ring
      rw [e1, hkey]
    rw [hfac]
    have h1 : (3 / 2 * K₀ ^ 4) * (3 / 2) ≤ 200 * (max K₀ 1) ^ 5 := by
      have h2 : K₀ ^ 4 ≤ (max K₀ 1) ^ 5 := by
        have h3 : K₀ ^ 4 ≤ (max K₀ 1) ^ 4 := pow_le_pow_left₀ hK₀ (le_max_left _ _) 4
        have h4 : (max K₀ 1) ^ 4 ≤ (max K₀ 1) ^ 5 :=
          pow_le_pow_right₀ (estIntegralOneA_Kc_ge_one K₀) (by norm_num)
        linarith
      have h5 : (1 : ℝ) ≤ (max K₀ 1) ^ 5 := one_le_pow₀ (estIntegralOneA_Kc_ge_one K₀)
      nlinarith
    have h6 : 0 ≤ E.rho * E.aScat * E.KH⁻¹ := by positivity
    calc (3 / 2 * K₀ ^ 4) * ((E.rho * E.aScat ^ 3 * E.KH ^ 2) * (E.rho * E.aScat * E.KH⁻¹))
        ≤ (3 / 2 * K₀ ^ 4) * ((3 / 2) * (E.rho * E.aScat * E.KH⁻¹)) := by
          have hK04 : 0 ≤ 3 / 2 * K₀ ^ 4 := mul_nonneg (by norm_num) (pow_nonneg hK₀ 4)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρa3 h6) hK04
      _ = ((3 / 2 * K₀ ^ 4) * (3 / 2)) * (E.rho * E.aScat * E.KH⁻¹) := by ring
      _ ≤ (200 * (max K₀ 1) ^ 5) * (E.rho * E.aScat * E.KH⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h6
      _ = 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by ring
  have hmain3 : E.ell ^ (-(3 : ℝ)) *
        (∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
          (2 * ‖F.kmom k‖ ^ 2 * E.A k))
      ≤ 3 * E.rho / (E.d * E.s * E.ell) *
          (K₀ ^ 3 * E.aScat ^ 2 * (1 + Real.log E.KH) + K₀ * E.aScat ^ 2)
        + 3 / 2 * K₀ ^ 4 * E.rho ^ 2 * E.aScat ^ 4 * E.KH := by
    have h1 : E.ell ^ (-(3 : ℝ)) *
          (∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
            (2 * ‖F.kmom k‖ ^ 2 * E.A k))
        ≤ E.ell ^ (-(3 : ℝ)) *
          (∑ k ∈ F.PHset E, (3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
            + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4))) :=
      mul_le_mul_of_nonneg_left hsum0 hℓ3.le
    have h2 : E.ell ^ (-(3 : ℝ)) *
          (∑ k ∈ F.PHset E, (3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3)
            + 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4)))
        = E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, 3 * E.rho * E.W1 k ^ 2 / (E.d * E.s * E.ell * ‖F.kmom k‖ ^ 3))
          + E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, 3 * E.rho ^ 2 * K₀ ^ 3 * E.aScat ^ 3 / (2 * ‖F.kmom k‖ ^ 4)) := by
      rw [Finset.sum_add_distrib]
      ring
    linarith [h1, h2, hmain1, hmain2]
  linarith [hmain3, hfin1, hfin2]


lemma estIntegralOneA_decomposition {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E) :
    |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
      ≤ E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
        + E.rho * (E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
              |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2))
        + E.rho * (E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
        + E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
              (2 * ‖F.kmom k‖ ^ 2 * E.A k)
        + E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3 := by
  have hρ : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 ≤ E.ell ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hℓ _).le
  set Q := (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k) with hQ
  set Sall := ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2) with hSall
  set SP := ∑ k ∈ F.PHset E, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2) with hSP
  set SQ := ∑ k ∈ Q, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2) with hSQ
  set UP := ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 / (2 * E.A k) with hUP
  have hsplit : Sall = SP + SQ := by
    rw [hSall, hSP, hSQ, hQ]
    exact (Finset.sum_filter_add_sum_filter_not (Work.BoseB7.excited Mode)
      (F.PH E.KH E.aScat) (fun k => E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2))).symm
  have hkey : E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)
      = E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
        + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)
        + (E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP)
        + (E.ell ^ (-(3 : ℝ)) * UP
            - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)) := by
    rw [hsplit]
    ring
  have htri : |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
        + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)
        + (E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP)
        + (E.ell ^ (-(3 : ℝ)) * UP
            - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k))|
      ≤ |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)|
        + |E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)|
        + |E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP|
        + |E.ell ^ (-(3 : ℝ)) * UP
            - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)| := by
    have h1 : |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
          + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)
          + (E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP)
          + (E.ell ^ (-(3 : ℝ)) * UP
              - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k))|
        ≤ |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
            + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)
            + (E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP)|
          + |E.ell ^ (-(3 : ℝ)) * UP
              - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)| :=
      abs_add_le _ _
    have h2 : |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
            + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)
            + (E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP)|
        ≤ |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
            + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)|
          + |E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP| :=
      abs_add_le _ _
    have h3 : |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)
            + E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)|
        ≤ |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)|
          + |E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)| :=
      abs_add_le _ _
    linarith
  have h1 : |E.rho * (E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall)|
      = E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) * Sall| := by
    rw [abs_mul, abs_of_nonneg hρ]
  have h2 : |E.rho * (E.ell ^ (-(3 : ℝ)) * SQ)|
      ≤ E.rho * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ Q, |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2)) := by
    rw [abs_mul, abs_of_nonneg hρ, abs_mul, abs_of_nonneg hℓ3, hSQ]
    apply mul_le_mul_of_nonneg_left _ hρ
    apply mul_le_mul_of_nonneg_left _ hℓ3
    calc |∑ k ∈ Q, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
        ≤ ∑ k ∈ Q, |E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Q, |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖F.kmom k‖ ^ 2)]
  have h3 : |E.ell ^ (-(3 : ℝ)) * (E.rho * SP) - E.ell ^ (-(3 : ℝ)) * UP|
      ≤ E.rho * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
        + E.ell ^ (-(3 : ℝ)) *
          (∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
            (2 * ‖F.kmom k‖ ^ 2 * E.A k)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hℓ3, hSP, hUP]
    have hsub : E.rho * (∑ k ∈ F.PHset E, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2))
        - (∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 / (2 * E.A k))
        = ∑ k ∈ F.PHset E, (E.rho * E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)
            - E.rho * E.W1 k ^ 2 / (2 * E.A k)) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsub]
    have hpt : ∀ k ∈ F.PHset E,
        |E.rho * E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2) - E.rho * E.W1 k ^ 2 / (2 * E.A k)|
          ≤ E.rho * (|E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
            + E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
              (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by
      intro k hk
      have hkPH : F.PH E.KH E.aScat k :=
        (Finset.mem_filter.mp (by simpa [Work.BoseB7.FockData.PHset] using hk)).2
      have hA : 0 < E.A k := hK.A_pos k hkPH
      have hx : 0 < ‖F.kmom k‖ := estIntegralOneA_norm_pos F E hv hk
      have hid : 1 / (2 * ‖F.kmom k‖ ^ 2) - 1 / (2 * E.A k)
          = (E.A k - ‖F.kmom k‖ ^ 2) / (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by
        field_simp
      have hdec : E.rho * E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)
            - E.rho * E.W1 k ^ 2 / (2 * E.A k)
          = E.rho * E.W1 k * (gHat k - E.W1 k) / (2 * ‖F.kmom k‖ ^ 2)
            + E.rho * E.W1 k ^ 2 * ((E.A k - ‖F.kmom k‖ ^ 2) /
                (2 * ‖F.kmom k‖ ^ 2 * E.A k)) := by
        rw [← hid]
        ring
      rw [hdec]
      have e1 : |E.rho * E.W1 k * (gHat k - E.W1 k) / (2 * ‖F.kmom k‖ ^ 2)|
          = E.rho * (|E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)) := by
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖F.kmom k‖ ^ 2),
          abs_mul, abs_mul, abs_of_nonneg hρ]
        ring
      have e2 : |E.rho * E.W1 k ^ 2 * ((E.A k - ‖F.kmom k‖ ^ 2) /
            (2 * ‖F.kmom k‖ ^ 2 * E.A k))|
          = E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
              (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hρ (sq_nonneg (E.W1 k))), abs_div,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖F.kmom k‖ ^ 2 * E.A k)]
        ring
      rw [← e1, ← e2]
      exact abs_add_le _ _
    have e : (∑ k ∈ F.PHset E, (E.rho * (|E.W1 k| * |gHat k - E.W1 k| /
            (2 * ‖F.kmom k‖ ^ 2))
          + E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
            (2 * ‖F.kmom k‖ ^ 2 * E.A k)))
        = E.rho * (∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
          + ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
            (2 * ‖F.kmom k‖ ^ 2 * E.A k) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    calc E.ell ^ (-(3 : ℝ)) *
          |∑ k ∈ F.PHset E, (E.rho * E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)
            - E.rho * E.W1 k ^ 2 / (2 * E.A k))|
        ≤ E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, |E.rho * E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)
              - E.rho * E.W1 k ^ 2 / (2 * E.A k)|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hℓ3
      _ ≤ E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, (E.rho * (|E.W1 k| * |gHat k - E.W1 k| /
                (2 * ‖F.kmom k‖ ^ 2))
              + E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
                (2 * ‖F.kmom k‖ ^ 2 * E.A k))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hℓ3
      _ = E.rho * (E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2)))
          + E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
              (2 * ‖F.kmom k‖ ^ 2 * E.A k)) := by
          rw [e]
          ring
  have h4 : |E.ell ^ (-(3 : ℝ)) * UP
        - E.ell ^ (-(3 : ℝ)) * (∑ k ∈ F.PHset E, E.W1 k * E.alpha k)|
      ≤ E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hℓ3, hUP]
    have hpt : ∀ k ∈ F.PHset E,
        |E.rho * E.W1 k ^ 2 / (2 * E.A k) - E.W1 k * E.alpha k|
          ≤ 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3 := by
      intro k hk
      have hkPH : F.PH E.KH E.aScat k :=
        (Finset.mem_filter.mp (by simpa [Work.BoseB7.FockData.PHset] using hk)).2
      have hA : 0 < E.A k := hK.A_pos k hkPH
      have h2 : 2 * |E.B k| ≤ E.A k := hK.AB_kernel k hkPH
      have h3 := Work.BoseB7.alpha_secondOrder_bound (E := E) hℓ hA (hK.B_eq k) h2
      rw [abs_sub_comm]
      exact h3
    rw [← Finset.sum_sub_distrib]
    calc E.ell ^ (-(3 : ℝ)) *
          |∑ k ∈ F.PHset E, (E.rho * E.W1 k ^ 2 / (2 * E.A k) - E.W1 k * E.alpha k)|
        ≤ E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, |E.rho * E.W1 k ^ 2 / (2 * E.A k) - E.W1 k * E.alpha k|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hℓ3
      _ ≤ E.ell ^ (-(3 : ℝ)) *
            (∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hℓ3
  rw [hkey]
  linarith [htri, h1, h2, h3, h4]

/-- **FS `lem:EstimateIntegral` (`eq:CompIntegrals-Final`), corrected and absolute.** -/
theorem estIntegralOneA (K₀ : ℝ) : Work.BoseB7A.EstIntegralOneA K₀ := by
  unfold Work.BoseB7A.EstIntegralOneA
  refine ⟨2000 * (max K₀ 1) ^ 5 + 2000, (1 / 2) ^ 323, by positivity, by positivity, ?_⟩
  intro Mode hACG hFin hDec F E hv R gHat ht hR hK
  have ha : 0 < E.aScat := hv.a_pos
  have hρ : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKHinv : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKH.le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 < E.ell ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hd : 0 < E.d := by rw [d_val E hv]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hKc : (1 : ℝ) ≤ max K₀ 1 := estIntegralOneA_Kc_ge_one K₀
  -- `0 ≤ K₀`: otherwise `IntKernel.sum_W1sq` is contradictory
  have hK₀ : 0 ≤ K₀ := by
    by_contra hcon
    have hcon' : K₀ < 0 := not_le.mp hcon
    have hL : 0 ≤ E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
      mul_nonneg hℓ3.le (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (by positivity)))
    have hlt : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 < 0 :=
      lt_of_le_of_lt hK.sum_W1sq (by nlinarith)
    linarith
  -- the scalar facts at the parameter point
  have h8 : 8 * (E.KH * E.aScat) ≤ E.d * E.s * E.ell := by
    have h := arith_aKH_div_dsell_le E hv ht
    have hds : 0 < E.d * E.s * E.ell := by positivity
    rw [div_le_iff₀ hds] at h
    linarith
  have hsmall : E.aScat * E.KH / (E.d * E.s * E.ell) ≤ 1 :=
    le_trans (arith_aKH_div_dsell_le E hv ht) (by norm_num)
  have hlog : E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH) ≤ 1 :=
    arith_aKH_log_div_dsell_le E hv ht
  have hAge : ∀ k ∈ F.PHset E, ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k :=
    int_A_ge F E R gHat K₀ hK hv h8
  have hAKH : E.aScat * E.KH ≤ E.ell := arith_aKH_le_ell E hv
  -- the decomposition
  have hdec := estIntegralOneA_decomposition F E R gHat K₀ hK hv
  -- piece 1: the discretisation error of `ω(0)`
  have hT1 : E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
      ≤ (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹ := by
    have hom := hK.omega_lattice
    have h1 : E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
        ≤ E.rho * (K₀ * E.aScat ^ 2 / E.ell) := mul_le_mul_of_nonneg_left hom hρ
    have hratio : E.aScat ^ 2 / E.ell ≤ E.aScat * E.KH⁻¹ := by
      have h2 : E.aScat / E.ell ≤ E.KH⁻¹ := by
        rw [div_le_iff₀ hℓ]
        rw [show E.KH⁻¹ * E.ell = E.ell / E.KH by ring, le_div_iff₀ hKH]
        linarith [hAKH]
      calc E.aScat ^ 2 / E.ell = E.aScat * (E.aScat / E.ell) := by ring
        _ ≤ E.aScat * E.KH⁻¹ := mul_le_mul_of_nonneg_left h2 ha.le
    have h3 : E.rho * (K₀ * E.aScat ^ 2 / E.ell) ≤ E.rho * ((max K₀ 1) * E.aScat * E.KH⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      calc K₀ * E.aScat ^ 2 / E.ell = K₀ * (E.aScat ^ 2 / E.ell) := by ring
        _ ≤ (max K₀ 1) * (E.aScat * E.KH⁻¹) :=
            mul_le_mul (le_max_left _ _) hratio (by positivity) (by positivity)
        _ = (max K₀ 1) * E.aScat * E.KH⁻¹ := by ring
    have h4 : E.rho * ((max K₀ 1) * E.aScat * E.KH⁻¹)
        = (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹ := by ring
    linarith [h1, h3, h4.le, h4.ge]
  -- piece 2: the low-momentum tail
  have hT2 : E.rho * (E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    int_term_lowKernel F E R gHat K₀ hK hv hK₀
  -- piece 3: the `ĝ − Ŵ₁` difference
  have hT3 : E.rho * (E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
    have h := estIntegralOneA_gHat_term F E R gHat K₀ hK hv hK₀ hR
    calc E.rho * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
        ≤ E.rho * (200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹) :=
          mul_le_mul_of_nonneg_left h hρ
      _ = 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by ring
  -- piece 4: the `𝒜 − k²` difference
  have hT4 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
          (2 * ‖F.kmom k‖ ^ 2 * E.A k)
      ≤ 400 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    estIntegralOneA_A_diff_term F E R gHat K₀ hK hv hK₀ hAge hsmall hlog
  -- piece 5: the second-order `α` correction
  have hT5 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    estIntegralOneA_cubic_term F E R gHat K₀ hK hv hK₀ hAge
  -- assemble
  have hX : 0 ≤ E.rho * E.aScat * E.KH⁻¹ := by positivity
  have htot : (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 400 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
      ≤ (2000 * (max K₀ 1) ^ 5 + 2000) * E.rho * E.aScat * E.KH⁻¹ := by
    have h1 : (max K₀ 1) ≤ (max K₀ 1) ^ 5 := by
      have h2 : (1 : ℝ) ≤ (max K₀ 1) ^ 4 := one_le_pow₀ hKc
      calc max K₀ 1 = max K₀ 1 * 1 := by ring
        _ ≤ max K₀ 1 * (max K₀ 1) ^ 4 :=
            mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hKc)
        _ = (max K₀ 1) ^ 5 := by ring
    nlinarith [hX, h1, hKc, pow_nonneg (le_trans zero_le_one hKc) 5]
  linarith [hdec, hT1, hT2, hT3, hT4, hT5, htot]

end Work.BoseB7A
