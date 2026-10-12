import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.sum_W1sq_le_new` — FS `eq.I2` with the *weighted* lattice sum

The same estimate as `Work.BoseK15.sum_W1sq_le`,

    `ℓ⁻³ Σ_{q ∈ P_H^q} Ŵ₁(q)²/‖q‖² ≤ K₀ a`,

but derived from the **scaled weighted lattice sum** `K15Input.sum_wt`

    `ℓ⁻³ Σ_{q ∈ P_H^q} (1+‖q‖)⁻⁴ ‖q‖⁻² ≤ Cwt · a`

together with the *lower* bound `K15Input.K₀_wt` on the chapter constant
(`8 Cw² Cwt a ≤ K₀`) — no extra `hsmall` hypothesis is needed.

The pointwise bound is FS's decay of `Ŵ₁` (`eq:W1-g` with the `(1+‖p‖)⁻²` decay,
`K15Input.W1_decay`) squared:

    `Ŵ₁(q)² / ‖q‖² ≤ (Cw a)² (1+‖q‖)⁻⁴ ‖q‖⁻²   (q ∈ P_H^q)`

(indeed `|Ŵ₁(p)| ≤ Cw a (1+‖p‖)⁻²` unconditionally, so no region condition is
used at all).  Multiplying by `ℓ⁻³`, summing and applying `sum_wt` gives
`≤ (Cw a)² Cwt a = Cw² Cwt a³`, and `K₀_wt` with `a ≤ 1` bounds this by

    `Cw² Cwt a³ = a·(Cw² Cwt a²) ≤ a·(Cw² Cwt a) ≤ a·(8 Cw² Cwt a) ≤ a K₀`.

Since `K15Input` carries `aScat_pos`, there are no degenerate `a` cases.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

theorem sum_W1sq_le_new {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E) :
    E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
        E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 ≤ K₀ * E.aScat := by
  have hell3pos : 0 < E.ell ^ (-(3 : ℝ)) := by
    rw [← h.ell_eq_E]; exact Real.rpow_pos_of_pos h.ell_pos _
  -- `x^{-2} = (x²)⁻¹`
  have hrpow2 : ∀ x : ℝ, 0 ≤ x → x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx 2, show x ^ (2 : ℝ) = x ^ 2 from Real.rpow_natCast x 2]
  -- `x^{-4} = ((x²)⁻¹)²`
  have hrpow4 : ∀ x : ℝ, 0 ≤ x → x ^ (-(4 : ℝ)) = ((x ^ 2)⁻¹) ^ 2 := by
    intro x hx
    have hh : x ^ (-(((4 : ℕ) : ℝ))) = ((x ^ 2)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hx, Real.rpow_natCast, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact (inv_pow (x ^ 2) 2).symm
    exact hh
  -- the pointwise bound: decay of `Ŵ₁` squared, divided by `‖q‖²`
  have hpx : ∀ q : Mode, E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 ≤
      (h.Cw * E.aScat) ^ 2 *
        ((1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) * (‖h.kmom q‖ ^ 2)⁻¹) := by
    intro q
    have hApos : 0 < (1 + ‖h.kmom q‖) ^ 2 := by positivity
    have hle : |h.W1f (h.kmom q)| ≤ h.Cw * E.aScat * ((1 + ‖h.kmom q‖) ^ 2)⁻¹ := by
      have h2 := (le_div_iff₀ hApos).mpr (h.W1_decay (h.kmom q))
      rwa [div_eq_mul_inv] at h2
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
    rw [mul_pow] at hsq
    have hW1sq : E.W1 q ^ 2 ≤ (h.Cw * E.aScat) ^ 2 * (1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) := by
      rw [h.W1_eq q, ← sq_abs, hrpow4 (1 + ‖h.kmom q‖) (by positivity)]
      exact hsq
    have hstep := mul_le_mul_of_nonneg_right hW1sq
      (by positivity : (0 : ℝ) ≤ (‖h.kmom q‖ ^ 2)⁻¹)
    calc E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
        = E.W1 q ^ 2 * (‖h.kmom q‖ ^ 2)⁻¹ := by rw [h.kmom_eq q, div_eq_mul_inv]
      _ ≤ ((h.Cw * E.aScat) ^ 2 * (1 + ‖h.kmom q‖) ^ (-(4 : ℝ))) *
            (‖h.kmom q‖ ^ 2)⁻¹ := hstep
      _ = (h.Cw * E.aScat) ^ 2 *
            ((1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) * (‖h.kmom q‖ ^ 2)⁻¹) := by ring
  set Sw : ℝ := ∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
        (1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) * (‖h.kmom q‖ ^ 2)⁻¹ with hSw
  set Sf : ℝ := ∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
        E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 with hSf
  have hsum : Sf ≤ (h.Cw * E.aScat) ^ 2 * Sw := by
    rw [hSf, hSw, Finset.mul_sum]
    exact Finset.sum_le_sum (fun q _ => hpx q)
  -- `sum_wt` is stated with `‖·‖^{-2}`; convert the termwise `(‖·‖²)⁻¹`
  have hwt : E.ell ^ (-(3 : ℝ)) * Sw ≤ h.Cwt := by
    rw [hSw]
    have hcongr : (∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
          (1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) * (‖h.kmom q‖ ^ 2)⁻¹)
        = ∑ q ∈ (Work.BoseB7.excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
          (1 + ‖h.kmom q‖) ^ (-(4 : ℝ)) * ‖h.kmom q‖ ^ (-(2 : ℝ)) :=
      Finset.sum_congr rfl (fun q _ => by rw [hrpow2 ‖h.kmom q‖ (norm_nonneg _)])
    rw [hcongr]
    exact h.sum_wt
  -- the arithmetic: `Cw² Cwt a² ≤ a K₀` from `8 Cw² Cwt ≤ K₀` and `a ≤ 1`
  have hcw2 : 0 ≤ h.Cw ^ 2 * h.Cwt := mul_nonneg (pow_nonneg h.Cw_nonneg 2) h.Cwt_nonneg
  have hfinal : (h.Cw * E.aScat) ^ 2 * h.Cwt ≤ K₀ * E.aScat := by
    have ha2 : E.aScat ^ 2 ≤ E.aScat := by
      nlinarith [mul_le_mul_of_nonneg_left h.aScat_le_one (le_of_lt h.aScat_pos)]
    have h1 : h.Cw ^ 2 * h.Cwt * E.aScat ^ 2 ≤ h.Cw ^ 2 * h.Cwt * E.aScat :=
      mul_le_mul_of_nonneg_left ha2 hcw2
    have h2 : h.Cw ^ 2 * h.Cwt ≤ 8 * h.Cw * h.Cw * h.Cwt := by nlinarith [hcw2]
    calc (h.Cw * E.aScat) ^ 2 * h.Cwt
        = (h.Cw ^ 2 * h.Cwt) * E.aScat ^ 2 := by ring
      _ ≤ (h.Cw ^ 2 * h.Cwt) * E.aScat := mul_le_mul_of_nonneg_left ha2 hcw2
      _ ≤ (8 * h.Cw * h.Cw * h.Cwt) * E.aScat :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt h.aScat_pos)
      _ ≤ K₀ * E.aScat := mul_le_mul_of_nonneg_right h.K₀_wt (le_of_lt h.aScat_pos)
  calc E.ell ^ (-(3 : ℝ)) * Sf
      ≤ E.ell ^ (-(3 : ℝ)) * ((h.Cw * E.aScat) ^ 2 * Sw) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hell3pos)
    _ = (h.Cw * E.aScat) ^ 2 * (E.ell ^ (-(3 : ℝ)) * Sw) := by ring
    _ ≤ (h.Cw * E.aScat) ^ 2 * h.Cwt :=
        mul_le_mul_of_nonneg_left hwt (by positivity)
    _ ≤ K₀ * E.aScat := hfinal

end Work.BoseK15
