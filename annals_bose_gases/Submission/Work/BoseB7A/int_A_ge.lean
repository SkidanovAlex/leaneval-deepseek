import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7A

theorem int_A_ge {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E)
    (h8 : 8 * (E.KH * E.aScat) ≤ E.d * E.s * E.ell) :
    ∀ k ∈ F.PHset E, ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k := by
  /- On `P_H`, `𝒜_k ≥ ‖k‖²/3`.

  Write `x = ‖k‖`, `L = d·s·ℓ`, `τ = E.tau k`, `B = E.B k`.  The three inputs are

  * `F.PH`: `x ≥ 1/(2K_Ha)`, which with the hypothesis `h8 : 8K_Ha ≤ L` gives
    `4 ≤ x·L` (multiply `h8` by `x > 0` and use `x·2K_Ha ≥ 1`);
  * `IntKernel.tau_PH`: `τ ≤ x²` and `x² - τ ≤ 2x/L`, so `τ ≥ x² - 2x/L ≥ x²/2`
    (the last step is `2x/L ≤ x²/2`, i.e. exactly `4 ≤ x·L`);
  * `IntKernel.AB_kernel` with `B_eq`: `2|B| ≤ 𝒜`, so `B ≥ -𝒜/2`.

  With `𝒜 = τ + B` this gives `𝒜 ≥ τ - 𝒜/2 ≥ x²/2 - 𝒜/2`, hence `𝒜 ≥ x²/3`. -/
  intro k hk
  rw [Work.BoseB7.FockData.PHset, Finset.mem_filter] at hk
  obtain ⟨_hkex, hkPH⟩ := hk
  -- positivity of the cut-off and of `x`
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have h2Ka : 0 < 2 * E.KH * E.aScat := by nlinarith
  have hx2 : 1 ≤ ‖F.kmom k‖ * (2 * E.KH * E.aScat) := (div_le_iff₀ h2Ka).mp hkPH
  have hxpos : 0 < ‖F.kmom k‖ := by nlinarith
  have hLpos : 0 < E.d * E.s * E.ell := lt_of_lt_of_le (by nlinarith) h8
  -- `h8` times `x > 0`
  have h8x : 8 * (E.KH * E.aScat) * ‖F.kmom k‖ ≤ E.d * E.s * E.ell * ‖F.kmom k‖ :=
    mul_le_mul_of_nonneg_right h8 hxpos.le
  have h4 : (4 : ℝ) ≤ 8 * (E.KH * E.aScat) * ‖F.kmom k‖ := by nlinarith
  have hxL : 4 ≤ ‖F.kmom k‖ * (E.d * E.s * E.ell) := by nlinarith
  have hτ := hK.tau_PH k hkPH
  have hAB := hK.AB_kernel k hkPH
  have hT : E.tau k = E.A k - E.B k := by
    have h1 := hK.A_eq k
    have h2 := hK.B_eq k
    linarith
  -- `2x/L ≤ x²/2`
  have hkey : 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) ≤ ‖F.kmom k‖ ^ 2 / 2 := by
    rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hxL, hxpos]
  have hBhigh : E.B k ≤ E.A k - ‖F.kmom k‖ ^ 2 / 2 := by
    have := hτ.2
    rw [hT] at this
    linarith
  have hBlow : -(E.A k / 2) ≤ E.B k := by
    have := neg_abs_le (E.B k)
    linarith
  nlinarith [hBhigh, hBlow]

end Work.BoseB7A
