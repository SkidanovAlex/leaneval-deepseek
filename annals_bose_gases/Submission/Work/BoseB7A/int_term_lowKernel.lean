import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.int_term_lowKernel` — FS `lem:EstimateIntegral`, the low-momentum part

This is the *low-kernel* (low-momentum) piece of FS's `lem:EstimateIntegral`
(`Papers/fournais_solovej/final_v2.tex`, proof of `eq:CompIntegrals-Final`):
the lattice sum over the modes **outside** the high-momentum region `P_H`,
paired against the true kernel `ĝ`,

  `ρ_z · ℓ⁻³ Σ_{k ∈ excited, k ∉ P_H} |Ŵ₁(k)ĝ(k)| / (2‖k‖²)`.

FS estimate it by the `‖k‖⁻²` bound `Σ_{k ∉ P_H} ‖k‖⁻² ≲ K_H⁻¹ a⁻¹` (the
low-momentum counting, the `N-INT` companion of the kernel's `low_sum` field),
which is exactly the `IntKernel.low_sum` field.  The two ingredients are:

* pointwise, on the low region, both kernels are bounded by `K₀ a`
  (`IntKernel.W1_le`, `IntKernel.gHat_le`), so
  `|Ŵ₁(k)ĝ(k)|/(2‖k‖²) ≤ (K₀a)²/2 · ‖k‖⁻²`;
* the low-momentum counting `ℓ⁻³ Σ_{k ∉ P_H} ‖k‖⁻² ≤ K₀/(K_H a)`
  (`IntKernel.low_sum`).

Multiplying, the low-kernel integral term is at most
`ρ_z · K₀³a/(2K_H) ≤ 200 (max K₀ 1)⁵ ρ_z a K_H⁻¹` — the shape needed by
`eq:CompIntegrals-Final`, where the constant only has to be absolute
(`200 (max K₀ 1)⁵`; the `K₀ ≥ 1` case is the honest one and `K₀ ≤ 1` is
absorbed by the `1`).

The whole content is the abstract inequality `arith_core` below; the rest is
reading off the two kernel fields and the positivity of FS's parameters
(`ρ_z > 0`, `a > 0`, `K_H ≥ 1`, `ℓ > 0`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

/-- **The pure arithmetic of the low-kernel term.**  If `T` is a quantity
bounded by `(K₀a)²/2 · S` and `S` satisfies the low-momentum counting
`ℓ⁻³S ≤ K₀/(K_H a)`, then the `ρ`-weighted, `ℓ⁻³`-rescaled `T` is at most
`200 (max K₀ 1)⁵ ρ a K_H⁻¹`.

All hypotheses are nonnegativity/positivity of the parameters together with the
two bounds; `K₀³/2 ≤ 200 (max K₀ 1)⁵` is the only arithmetic input
(`K₀³ ≤ (max K₀ 1)⁵`, since `max K₀ 1 ≥ 1` and `max K₀ 1 ≥ K₀`). -/
private lemma arith_core {ρ a ℓ KH K₀ S T : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hKH : 1 ≤ KH) (hℓ : 0 < ℓ) (hK₀ : 0 ≤ K₀)
    (hT : T ≤ (K₀ * a) ^ 2 / 2 * S)
    (hbound : ℓ ^ (-(3 : ℝ)) * S ≤ K₀ / (KH * a)) :
    ρ * (ℓ ^ (-(3 : ℝ)) * T) ≤ 200 * (max K₀ 1) ^ 5 * ρ * a * KH⁻¹ := by
  have hℓ3 : 0 < ℓ ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hc : 0 ≤ (K₀ * a) ^ 2 / 2 := by positivity
  have hρa : 0 ≤ ρ * a * KH⁻¹ := by
    have : 0 < KH := lt_of_lt_of_le zero_lt_one hKH
    positivity
  have hm1 : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _
  have hm5 : (1 : ℝ) ≤ (max K₀ 1) ^ 5 := one_le_pow₀ hm1
  have hK3 : K₀ ^ 3 ≤ (max K₀ 1) ^ 5 := by
    by_cases h : K₀ ≤ 1
    · rw [max_eq_right h]
      simpa using pow_le_pow_left₀ hK₀ h 3
    · have h1 : (1 : ℝ) ≤ K₀ := le_of_lt (not_le.mp h)
      rw [max_eq_left h1]
      exact pow_le_pow_right₀ h1 (by norm_num)
  have hm3 : K₀ ^ 3 / 2 ≤ 200 * (max K₀ 1) ^ 5 := by
    nlinarith [hK3, hm5, pow_nonneg hK₀ 3]
  have hstep : ℓ ^ (-(3 : ℝ)) * ((K₀ * a) ^ 2 / 2 * S) =
      (K₀ * a) ^ 2 / 2 * (ℓ ^ (-(3 : ℝ)) * S) := by ring
  have hkey : ρ * ((K₀ * a) ^ 2 / 2 * (K₀ / (KH * a))) =
      (K₀ ^ 3 / 2) * (ρ * a * KH⁻¹) := by
    have hKH0 : KH ≠ 0 := by positivity
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp
  calc ρ * (ℓ ^ (-(3 : ℝ)) * T)
      ≤ ρ * (ℓ ^ (-(3 : ℝ)) * ((K₀ * a) ^ 2 / 2 * S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hℓ3.le) hρ
    _ = ρ * ((K₀ * a) ^ 2 / 2 * (ℓ ^ (-(3 : ℝ)) * S)) := by rw [hstep]
    _ ≤ ρ * ((K₀ * a) ^ 2 / 2 * (K₀ / (KH * a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hc) hρ
    _ = (K₀ ^ 3 / 2) * (ρ * a * KH⁻¹) := hkey
    _ ≤ (200 * (max K₀ 1) ^ 5) * (ρ * a * KH⁻¹) :=
        mul_le_mul_of_nonneg_right hm3 hρa
    _ = 200 * (max K₀ 1) ^ 5 * ρ * a * KH⁻¹ := by ring

theorem int_term_lowKernel {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (R : ℝ) (gHat : Mode → ℝ)
    (K₀ : ℝ) (hK : Work.BoseB7A.IntKernel K₀ R F E gHat) (hv : Work.BoseB7.FSParamsView E)
    (hK₀ : 0 ≤ K₀) :
    E.rho * (E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
  -- FS's parameters: `ρ_z ≥ 0`, `a > 0`, `K_H ≥ 1`, `ℓ > 0`.
  have hρ : (0 : ℝ) ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have ha : (0 : ℝ) < E.aScat := Work.BoseB7.a_pos E hv
  have hKH : (1 : ℝ) ≤ E.KH := hv.one_le_KH
  have hℓ : (0 : ℝ) < E.ell := Work.BoseB7.ell_pos E hv
  -- Step 1: pointwise, the two kernels on the low region are bounded by `K₀a`.
  have hpt : ∀ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
      |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2) ≤
        (K₀ * E.aScat) ^ 2 / (2 * ‖F.kmom k‖ ^ 2) := by
    intro k _
    rw [abs_mul]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc |E.W1 k| * |gHat k| ≤ (K₀ * E.aScat) * (K₀ * E.aScat) :=
          mul_le_mul (hK.W1_le k) (hK.gHat_le k) (abs_nonneg _) (by positivity)
      _ = (K₀ * E.aScat) ^ 2 := by ring
  -- Step 2: sum, and factor out the `‖k‖⁻²` sum.
  have hS1 : (∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
        |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2)) ≤
      ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
        (K₀ * E.aScat) ^ 2 / (2 * ‖F.kmom k‖ ^ 2) := Finset.sum_le_sum hpt
  have hS2 : (∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
        (K₀ * E.aScat) ^ 2 / (2 * ‖F.kmom k‖ ^ 2)) =
      (K₀ * E.aScat) ^ 2 / 2 *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          1 / ‖F.kmom k‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hT : (∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
        |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2)) ≤
      (K₀ * E.aScat) ^ 2 / 2 *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          1 / ‖F.kmom k‖ ^ 2 := by
    rw [hS2] at hS1
    exact hS1
  -- Step 3: the low-momentum counting of the kernel interface.
  exact arith_core hρ ha hKH hℓ hK₀ hT hK.low_sum

end Work.BoseB7A
