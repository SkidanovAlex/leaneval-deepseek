import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.smallness_conj8` — the scattering-length/`K_H` factor at FS's parameters

At FS's parameter point (`FSParamsView E`, diluteness `t = μa³ ∈ (0,1]`,
`X = (μa³)^{1/323}`) the quantity

  `a·K_H·(1 + log K_H)/(d·s·ℓ)`

has a *free* scattering length in the numerator and a *free* `ℓ` in the
denominator, but the combination `a/ℓ` is a pure monomial in `X`:

  `a/ℓ = a(μa)^{1/2}/K_ℓ = (μa³)^{1/2}/K_ℓ = √t/X^{-3/2} = X^{163}`.

Hence (using `K_H = X^{-549/4}`, `d = X⁶`, `s = X`)

  `a·K_H/(d·s·ℓ) = X^{163}·X^{-549/4}·X^{-7} = X^{75/4}`,

and, since `log K_H = log(X^{-549/4}) = (549/4)·log(1/X)`,

  `a·K_H·(1 + log K_H)/(d·s·ℓ) = X^{75/4} + (549/4)·X^{75/4}·log(1/X)`.

The target inequality is then two monotone comparisons with `X ≤ τ ≤ 1`:
`X^{75/4} ≤ τ^{75/4}` and

  `X^{75/4}·log(1/X) = (X·log(1/X))·X^{71/4} ≤ X^{71/4} ≤ τ^{71/4}`,

where `X·log(1/X) ≤ 1` follows from `Real.log_le_self` applied to `X⁻¹`
(`log y ≤ y` for `y ≥ 0`, then multiply by `X`).
-/

noncomputable section

namespace Work.BoseB7A

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- `log (fsXp t c) = (c/323)·log t` for `t > 0`. -/
lemma log_fsXp {t c : ℝ} (ht : 0 < t) : Real.log (fsXp t c) = (c / 323) * Real.log t := by
  rw [fsXp, Real.log_rpow ht]

/-- **The scattering length cancels**: at FS's parameter point `a/ℓ = X^{163}`,
because `a/ℓ = a(μa)^{1/2}/K_ℓ = (μa³)^{1/2}/K_ℓ = √t/X^{-3/2} = X^{163}`. -/
lemma aScat_div_ell (E : Q3Env Mode) (hv : FSParamsView E) :
    E.aScat / E.ell = fsXp hv.t 163 := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hmu : 0 < E.mu := mu_pos E hv
  have hmua : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.ell_eq, side]
  -- `K_ℓ·X^{163} = X^{-3/2}·X^{163} = X^{323/2} = √t`
  have hKl163 : E.Kl * fsXp hv.t 163 = hv.t ^ (1 / 2 : ℝ) := by
    rw [hv.Kl_eq, fsXp_mul ht]
    rw [show (-(3 / 2 : ℝ) + 163) = 323 / 2 by norm_num]
    rw [fsXp, show (323 / 2 : ℝ) / 323 = 1 / 2 by norm_num]
  -- `(μa)^{-1/2}·√t = a`
  have hkey : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) * hv.t ^ (1 / 2 : ℝ) = E.aScat := by
    have h1 : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ))
        = ((E.mu * E.aScat) ^ (-(1 : ℝ))) ^ (1 / 2 : ℝ) := by
      rw [show (-(1 / 2 : ℝ)) = (-(1 : ℝ)) * (1 / 2) by norm_num, Real.rpow_mul hmua.le]
    have h2 : (E.mu * E.aScat) ^ (-(1 : ℝ)) * hv.t = E.aScat ^ 2 := by
      rw [Real.rpow_neg hmua.le, Real.rpow_one, ← hv.mu_eq]
      calc (E.mu * E.aScat)⁻¹ * (E.mu * E.aScat ^ 3)
          = (E.mu * E.aScat)⁻¹ * ((E.mu * E.aScat) * E.aScat ^ 2) := by ring
        _ = E.aScat ^ 2 := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmua), one_mul]
    rw [h1, ← Real.mul_rpow (Real.rpow_nonneg hmua.le _) ht.le, h2, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq ha.le]
  have hellmul : fsXp hv.t 163 * E.ell = E.aScat := by
    calc fsXp hv.t 163 * E.ell
        = (E.Kl * fsXp hv.t 163) * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
          rw [hell]; ring
      _ = hv.t ^ (1 / 2 : ℝ) * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by rw [hKl163]
      _ = E.aScat := by rw [mul_comm, hkey]
  rw [div_eq_iff (ne_of_gt (ell_pos E hv))]
  exact hellmul.symm

theorem smallness_conj8 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) {τ : ℝ}
    (hτ1 : τ ≤ 1) (hX : Work.BoseBox.fsXp hv.t 1 ≤ τ) :
    E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell) ≤
      τ ^ (75 / 4 : ℝ) + (549 / 4) * τ ^ (71 / 4 : ℝ) := by
  have ht : 0 < hv.t := hv.t_pos
  have hXpos : 0 < fsXp hv.t 1 := fsXp_pos ht
  have hXnonneg : 0 ≤ fsXp hv.t 1 := hXpos.le
  -- `τ ≤ 1` is not needed for this bound (only `X ≤ τ` is); it is recorded here.
  have hτ1' : τ ≤ 1 := hτ1
  -- the monomial values
  have hKH : E.KH = fsXp hv.t (-(549 / 4)) := KH_val E hv
  have hd : E.d = fsXp hv.t 6 := d_val E hv
  have hs : E.s = fsXp hv.t 1 := hv.s_eq
  have haell : E.aScat / E.ell = fsXp hv.t 163 := aScat_div_ell E hv
  -- non-vanishing
  have hellne : E.ell ≠ 0 := ne_of_gt (ell_pos E hv)
  have hdne : E.d ≠ 0 := by rw [hd]; exact ne_of_gt (fsXp_pos ht)
  have hsne : E.s ≠ 0 := by rw [hs]; exact ne_of_gt hXpos
  -- `log K_H = (549/4)·log (1/X)`
  have hlog : Real.log E.KH = (549 / 4) * Real.log (fsXp hv.t 1)⁻¹ := by
    rw [hKH, log_fsXp ht, Real.log_inv, log_fsXp ht]
    ring
  -- the closed form of the left-hand side
  have hmain : E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell)
      = fsXp hv.t (75 / 4) * (1 + Real.log E.KH) := by
    have hfac : E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell)
        = (E.aScat / E.ell) * (E.KH / (E.d * E.s)) * (1 + Real.log E.KH) := by
      field_simp
    have hKHds : E.KH / (E.d * E.s) = fsXp hv.t (-(577 / 4)) := by
      have hexp : (-(549 / 4 : ℝ)) + (-(6 + 1)) = -(577 / 4) := by norm_num
      rw [hKH, hd, hs, div_eq_mul_inv, fsXp_mul ht, fsXp_inv ht, fsXp_mul ht, hexp]
    have hexp : (163 : ℝ) + (-(577 / 4)) = 75 / 4 := by norm_num
    rw [hfac, haell, hKHds, fsXp_mul ht, hexp]
  -- `X log(1/X) ≤ 1`
  have hXL : fsXp hv.t 1 * Real.log (fsXp hv.t 1)⁻¹ ≤ 1 := by
    have h1 : Real.log (fsXp hv.t 1)⁻¹ ≤ (fsXp hv.t 1)⁻¹ :=
      Real.log_le_self (inv_nonneg.mpr hXnonneg)
    calc fsXp hv.t 1 * Real.log (fsXp hv.t 1)⁻¹
        ≤ fsXp hv.t 1 * (fsXp hv.t 1)⁻¹ := mul_le_mul_of_nonneg_left h1 hXnonneg
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hXpos)
  -- the two monotone comparisons
  have hA : fsXp hv.t (75 / 4) ≤ τ ^ (75 / 4 : ℝ) := by
    have h1 : fsXp hv.t (75 / 4) = (fsXp hv.t 1) ^ (75 / 4 : ℝ) := by
      rw [fsXp_rpow ht.le]; congr 1; ring
    rw [h1]
    exact Real.rpow_le_rpow hXnonneg hX (by norm_num)
  have h72 : fsXp hv.t (71 / 4) ≤ τ ^ (71 / 4 : ℝ) := by
    have h1 : fsXp hv.t (71 / 4) = (fsXp hv.t 1) ^ (71 / 4 : ℝ) := by
      rw [fsXp_rpow ht.le]; congr 1; ring
    rw [h1]
    exact Real.rpow_le_rpow hXnonneg hX (by norm_num)
  have hB' : fsXp hv.t (75 / 4) * Real.log (fsXp hv.t 1)⁻¹ ≤ τ ^ (71 / 4 : ℝ) := by
    have h75 : fsXp hv.t (75 / 4) = fsXp hv.t 1 * fsXp hv.t (71 / 4) := by
      rw [fsXp_mul ht]; congr 1; norm_num
    calc fsXp hv.t (75 / 4) * Real.log (fsXp hv.t 1)⁻¹
        = (fsXp hv.t 1 * Real.log (fsXp hv.t 1)⁻¹) * fsXp hv.t (71 / 4) := by
          rw [h75]; ring
      _ ≤ 1 * fsXp hv.t (71 / 4) := mul_le_mul_of_nonneg_right hXL (fsXp_nonneg ht.le)
      _ = fsXp hv.t (71 / 4) := one_mul _
      _ ≤ τ ^ (71 / 4 : ℝ) := h72
  have hB : fsXp hv.t (75 / 4) * Real.log E.KH ≤ (549 / 4) * τ ^ (71 / 4 : ℝ) := by
    rw [hlog]
    calc fsXp hv.t (75 / 4) * ((549 / 4) * Real.log (fsXp hv.t 1)⁻¹)
        = (549 / 4) * (fsXp hv.t (75 / 4) * Real.log (fsXp hv.t 1)⁻¹) := by ring
      _ ≤ (549 / 4) * τ ^ (71 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hB' (by norm_num)
  calc E.aScat * E.KH * (1 + Real.log E.KH) / (E.d * E.s * E.ell)
      = fsXp hv.t (75 / 4) * (1 + Real.log E.KH) := hmain
    _ = fsXp hv.t (75 / 4) + fsXp hv.t (75 / 4) * Real.log E.KH := by ring
    _ ≤ τ ^ (75 / 4 : ℝ) + (549 / 4) * τ ^ (71 / 4 : ℝ) := add_le_add hA hB

end Work.BoseB7A
