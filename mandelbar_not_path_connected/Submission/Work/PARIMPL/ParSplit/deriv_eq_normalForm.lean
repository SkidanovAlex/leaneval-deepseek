import Mathlib
import Submission.Work.PARIMPL.ParSplit.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- The one-sided computation behind `deriv_eq_normalForm`: if `F (m + s * ζ)` equals
`m + s * (ζ + (ζ ^ 2 - b ^ 2) * h ζ)` for every `ζ` and `h` is differentiable at `b`, then
`deriv F` at `m + s * b` is `1 + 2 * b * h b`.

(Applying this with `b = a` and with `b = -a`, using `(-a) ^ 2 = a ^ 2`, yields the two halves
of the requested statement.) -/
lemma deriv_eq_normalForm_aux {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m s b : ℂ} (hs : s ≠ 0)
    {h : ℂ → ℂ} (hh : ∀ ζ, F (m + s * ζ) = m + s * (ζ + (ζ ^ 2 - b ^ 2) * h ζ))
    (hdb : DifferentiableAt ℂ h b) :
    deriv F (m + s * b) = 1 + 2 * b * h b := by
  -- derivative of the normal form `ζ ↦ ζ ^ 2 - b ^ 2`
  have hd1 : HasDerivAt (fun ζ : ℂ => ζ ^ 2 - b ^ 2) (2 * b) b := by
    have h1 := (hasDerivAt_pow 2 b).sub_const (b ^ 2)
    simpa using h1
  -- product rule for `ζ ↦ (ζ ^ 2 - b ^ 2) * h ζ`
  have hd3 : HasDerivAt (fun ζ : ℂ => (ζ ^ 2 - b ^ 2) * h ζ) (2 * b * h b) b := by
    have h3 := hd1.mul hdb.hasDerivAt
    convert h3 using 1
    ring
  -- derivative of `ζ ↦ ζ + (ζ ^ 2 - b ^ 2) * h ζ`
  have hd4 : HasDerivAt (fun ζ : ℂ => ζ + (ζ ^ 2 - b ^ 2) * h ζ) (1 + 2 * b * h b) b :=
    (hasDerivAt_id b).add hd3
  -- derivative of the whole normal form `ζ ↦ m + s * (ζ + (ζ ^ 2 - b ^ 2) * h ζ)`
  have hG : HasDerivAt (fun ζ : ℂ => m + s * (ζ + (ζ ^ 2 - b ^ 2) * h ζ))
      (s * (1 + 2 * b * h b)) b :=
    (hd4.const_mul s).const_add m
  -- derivative of the affine inner map `ζ ↦ m + s * ζ`
  have hg : HasDerivAt (fun ζ : ℂ => m + s * ζ) s b := by
    have h1 := ((hasDerivAt_id b).const_mul s).const_add m
    simpa using h1
  -- chain rule: `ζ ↦ F (m + s * ζ)` has derivative `deriv F (m + s * b) * s`
  have hFg : HasDerivAt (fun ζ : ℂ => F (m + s * ζ)) (deriv F (m + s * b) * s) b :=
    HasDerivAt.comp b ((hF (m + s * b)).hasDerivAt) hg
  -- the same function, seen through the normal form
  have e1 : deriv (fun ζ : ℂ => F (m + s * ζ)) b = s * (1 + 2 * b * h b) := by
    rw [show (fun ζ : ℂ => F (m + s * ζ))
          = (fun ζ : ℂ => m + s * (ζ + (ζ ^ 2 - b ^ 2) * h ζ)) from funext hh]
    exact hG.deriv
  have e2 : deriv (fun ζ : ℂ => F (m + s * ζ)) b = deriv F (m + s * b) * s := hFg.deriv
  have hmain : deriv F (m + s * b) * s = (1 + 2 * b * h b) * s := by
    rw [← e2, e1, mul_comm s (1 + 2 * b * h b)]
  exact mul_right_cancel₀ hs hmain

theorem deriv_eq_normalForm {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m s a : ℂ} (hs : s ≠ 0)
    {h : ℂ → ℂ} (hh : ∀ ζ, F (m + s * ζ) = m + s * (ζ + (ζ ^ 2 - a ^ 2) * h ζ))
    (hda : DifferentiableAt ℂ h a) (hdna : DifferentiableAt ℂ h (-a)) :
    deriv F (m + s * a) = 1 + 2 * a * h a ∧
      deriv F (m - s * a) = 1 - 2 * a * h (-a) := by
  have hpos : deriv F (m + s * a) = 1 + 2 * a * h a :=
    deriv_eq_normalForm_aux hF hs hh hda
  have hh' : ∀ ζ, F (m + s * ζ) = m + s * (ζ + (ζ ^ 2 - (-a) ^ 2) * h ζ) := by
    intro ζ
    rw [neg_sq]
    exact hh ζ
  have hneg : deriv F (m + s * (-a)) = 1 + 2 * (-a) * h (-a) :=
    deriv_eq_normalForm_aux hF hs hh' hdna
  refine ⟨hpos, ?_⟩
  rw [show (m - s * a : ℂ) = m + s * (-a) by ring,
      show (1 - 2 * a * h (-a) : ℂ) = 1 + 2 * (-a) * h (-a) by ring]
  exact hneg

end Work.PARIMPL.ParSplit
