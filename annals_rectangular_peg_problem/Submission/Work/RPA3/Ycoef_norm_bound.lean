import Mathlib
import Submission.Work.RPA3.follow_family_defs

/-!
# RPA3, D3: the norm bound on the tangential correction coefficients `Ycoef`

`Ycoef L H τ x t` is the coefficient pair expressing the defect
`W = X_H(ℓ τ (x,t)) - ∂_τℓ(τ,x,t)` in the basis `(∂_xℓ, ∂_tℓ)` of the Lagrangian
slice; it is `Gram⁻¹` applied to the pairings of `W` with the two generators.

Here we bound it in terms of the *crude* inputs one has in the follow-the-family
argument: a bound `m0` on the Hamiltonian field, bounds `mx`, `mt` on the slice
derivatives, a bound `mu` on `∂_τℓ`, and a strictly positive lower bound `c` on the
Gram determinant.

The whole content is `Ycoef` = `Gram⁻¹ · (pairings)` combined with

* the triangle inequality for the defect `W = X_H - ∂_τℓ`,
* Cauchy–Schwarz for the inner product `ip` on `PS = ℝ⁴` in the product (max) norm,
  with the crude constant `4` (`ip_abs_le_four`, one factor for each coordinate),
* and the elementary scalar inequality `ycoef_arith` for a single component of the
  Gram inverse.

With `|gramC| ≤ 4 mt²`, `|gramB| ≤ 4 mx mt`, `|⟪W,∂_xℓ⟫| ≤ 4 (m0+mu) mx` and
`|⟪W,∂_tℓ⟫| ≤ 4 (m0+mu) mt`, each component of `Ycoef` is at most
`32 mx mt (m0+mu)(mx+mt)/c`, and the norm on `ℝ × ℝ` is the maximum of the two
component norms.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- Cauchy–Schwarz for the Euclidean inner product `ip` on `PS = ℝ⁴`, in the product
(max) norm, with the crude constant `4` (one factor per coordinate).  The constant `4` is
sharp for this norm, e.g. at `a = b = ((1,1),(1,1))` one has `ip a b = 4` and `‖a‖ = ‖b‖ = 1`. -/
theorem ip_abs_le_four (a b : PS) : |ip a b| ≤ 4 * ‖a‖ * ‖b‖ := by
  have ha1 : |a.1.1| ≤ ‖a‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_fst_le (x := a.1)) (norm_fst_le (x := a))
  have ha2 : |a.1.2| ≤ ‖a‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_snd_le (x := a.1)) (norm_fst_le (x := a))
  have ha3 : |a.2.1| ≤ ‖a‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_fst_le (x := a.2)) (norm_snd_le (x := a))
  have ha4 : |a.2.2| ≤ ‖a‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_snd_le (x := a.2)) (norm_snd_le (x := a))
  have hb1 : |b.1.1| ≤ ‖b‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_fst_le (x := b.1)) (norm_fst_le (x := b))
  have hb2 : |b.1.2| ≤ ‖b‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_snd_le (x := b.1)) (norm_fst_le (x := b))
  have hb3 : |b.2.1| ≤ ‖b‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_fst_le (x := b.2)) (norm_snd_le (x := b))
  have hb4 : |b.2.2| ≤ ‖b‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_snd_le (x := b.2)) (norm_snd_le (x := b))
  have hp1 : |a.1.1 * b.1.1| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul ha1 hb1 (abs_nonneg _) (norm_nonneg _)
  have hp2 : |a.1.2 * b.1.2| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul ha2 hb2 (abs_nonneg _) (norm_nonneg _)
  have hp3 : |a.2.1 * b.2.1| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul ha3 hb3 (abs_nonneg _) (norm_nonneg _)
  have hp4 : |a.2.2 * b.2.2| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul ha4 hb4 (abs_nonneg _) (norm_nonneg _)
  have htri : |ip a b| ≤
      |a.1.1 * b.1.1| + |a.1.2 * b.1.2| + |a.2.1 * b.2.1| + |a.2.2 * b.2.2| := by
    rw [ip]
    have h1 := abs_add_le (a.1.1 * b.1.1 + a.1.2 * b.1.2 + a.2.1 * b.2.1) (a.2.2 * b.2.2)
    have h2 := abs_add_le (a.1.1 * b.1.1 + a.1.2 * b.1.2) (a.2.1 * b.2.1)
    have h3 := abs_add_le (a.1.1 * b.1.1) (a.1.2 * b.1.2)
    linarith
  linarith [htri, hp1, hp2, hp3, hp4]

/-- Scalar engine for the `Ycoef` bound: one component of a Gram inverse, bounded from the
crude Cauchy–Schwarz inputs.  The hypotheses are exactly the bounds produced by
`ip_abs_le_four`: `|gc| ≤ 4 mt²`, `|gb| ≤ 4 mx mt`, `|p| ≤ 4 M mx`, `|q| ≤ 4 M mt`, together
with the positive lower bound `c` on the determinant `gd`. -/
theorem ycoef_arith (gc gb gd p q c mx mt M : ℝ)
    (hgd : c ≤ gd) (hc : 0 < c)
    (hgc : |gc| ≤ 4 * mt ^ 2) (hgb : |gb| ≤ 4 * mx * mt)
    (hp : |p| ≤ 4 * M * mx) (hq : |q| ≤ 4 * M * mt)
    (hmx : 0 ≤ mx) (hmt : 0 ≤ mt) (hM : 0 ≤ M) :
    |(gc * p - gb * q) / gd| ≤ 32 * mx * mt * M * (mx + mt) / c := by
  have hgdpos : 0 < gd := lt_of_lt_of_le hc hgd
  have h1 : |gc * p| ≤ 4 * mt ^ 2 * (4 * M * mx) := by
    rw [abs_mul]
    exact mul_le_mul hgc hp (abs_nonneg _) (by positivity)
  have h2 : |gb * q| ≤ 4 * mx * mt * (4 * M * mt) := by
    rw [abs_mul]
    exact mul_le_mul hgb hq (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hmx) hmt)
  have htri : |gc * p - gb * q| ≤ |gc * p| + |gb * q| := by
    have h := abs_sub_le (gc * p) 0 (gb * q)
    simpa using h
  have hnum : |gc * p - gb * q| ≤ 32 * M * mx * mt ^ 2 := by
    nlinarith [htri, h1, h2]
  have hNnn : 0 ≤ 32 * M * mx * mt ^ 2 := by positivity
  have hdiv : |(gc * p - gb * q) / gd| ≤ 32 * M * mx * mt ^ 2 / c := by
    rw [abs_div, abs_of_pos hgdpos]
    calc |gc * p - gb * q| / gd ≤ 32 * M * mx * mt ^ 2 / gd :=
          div_le_div_of_nonneg_right hnum (le_of_lt hgdpos)
      _ ≤ 32 * M * mx * mt ^ 2 / c :=
          div_le_div_of_nonneg_left hNnn hc hgd
  have hfin : 32 * M * mx * mt ^ 2 / c ≤ 32 * mx * mt * M * (mx + mt) / c := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hc)
    nlinarith [hmx, hmt, hM, mul_nonneg hM hmx, mul_nonneg (mul_nonneg hM hmx) hmt,
      mul_nonneg hM hmt, sq_nonneg mx]
  exact le_trans hdiv hfin

theorem Ycoef_norm_bound (L : Work.RPA3.LagFamilyAll) (H : ℝ → Work.RPA3.PS → ℝ) (τ x t : ℝ)
    (m0 mx mt mu c : ℝ)
    (hm0 : ‖Work.RPA3.hamVF (H τ) (L.ℓ τ (x, t))‖ ≤ m0)
    (hmx : ‖Work.RPA3.dX L τ x t‖ ≤ mx) (hmt : ‖Work.RPA3.dT L τ x t‖ ≤ mt)
    (hmu : ‖Work.RPA3.dTau L τ x t‖ ≤ mu)
    (hc : c ≤ Work.RPA3.gramDet L τ x t) (hcpos : 0 < c)
    (hm0n : 0 ≤ m0) (hmxn : 0 ≤ mx) (hmtn : 0 ≤ mt) (hmun : 0 ≤ mu) :
    ‖Work.RPA3.Ycoef L H τ x t‖ ≤ 32 * mx * mt * (m0 + mu) * (mx + mt) / c := by
  have hW : ‖Wvec L H τ x t‖ ≤ m0 + mu := by
    rw [Wvec]
    exact le_trans (norm_sub_le _ _) (add_le_add hm0 hmu)
  have hMnn : 0 ≤ m0 + mu := add_nonneg hm0n hmun
  -- the pairings of the defect with the two slice generators
  have hpX : |ip (Wvec L H τ x t) (dX L τ x t)| ≤ 4 * (m0 + mu) * mx := by
    have h1 := ip_abs_le_four (Wvec L H τ x t) (dX L τ x t)
    have h2 : ‖Wvec L H τ x t‖ * ‖dX L τ x t‖ ≤ (m0 + mu) * mx :=
      mul_le_mul hW hmx (norm_nonneg _) hMnn
    nlinarith [h1, h2]
  have hpT : |ip (Wvec L H τ x t) (dT L τ x t)| ≤ 4 * (m0 + mu) * mt := by
    have h1 := ip_abs_le_four (Wvec L H τ x t) (dT L τ x t)
    have h2 : ‖Wvec L H τ x t‖ * ‖dT L τ x t‖ ≤ (m0 + mu) * mt :=
      mul_le_mul hW hmt (norm_nonneg _) hMnn
    nlinarith [h1, h2]
  -- the Gram entries
  have hga : |gramA L τ x t| ≤ 4 * mx ^ 2 := by
    have h1 := ip_abs_le_four (dX L τ x t) (dX L τ x t)
    have h2 : ‖dX L τ x t‖ * ‖dX L τ x t‖ ≤ mx * mx :=
      mul_le_mul hmx hmx (norm_nonneg _) hmxn
    simp only [gramA]
    nlinarith [h1, h2]
  have hgb : |gramB L τ x t| ≤ 4 * mx * mt := by
    have h1 := ip_abs_le_four (dX L τ x t) (dT L τ x t)
    have h2 : ‖dX L τ x t‖ * ‖dT L τ x t‖ ≤ mx * mt :=
      mul_le_mul hmx hmt (norm_nonneg _) hmxn
    simp only [gramB]
    nlinarith [h1, h2]
  have hgc : |gramC L τ x t| ≤ 4 * mt ^ 2 := by
    have h1 := ip_abs_le_four (dT L τ x t) (dT L τ x t)
    have h2 : ‖dT L τ x t‖ * ‖dT L τ x t‖ ≤ mt * mt :=
      mul_le_mul hmt hmt (norm_nonneg _) hmtn
    simp only [gramC]
    nlinarith [h1, h2]
  -- the two components of `Ycoef`, by definition of the Gram inverse
  have hY1 : (Ycoef L H τ x t).1 = (gramC L τ x t * ip (Wvec L H τ x t) (dX L τ x t)
      - gramB L τ x t * ip (Wvec L H τ x t) (dT L τ x t)) / gramDet L τ x t := rfl
  have hY2 : (Ycoef L H τ x t).2 = (gramA L τ x t * ip (Wvec L H τ x t) (dT L τ x t)
      - gramB L τ x t * ip (Wvec L H τ x t) (dX L τ x t)) / gramDet L τ x t := rfl
  have hb1 : |(Ycoef L H τ x t).1| ≤ 32 * mx * mt * (m0 + mu) * (mx + mt) / c := by
    rw [hY1]
    exact ycoef_arith (gramC L τ x t) (gramB L τ x t) (gramDet L τ x t)
      (ip (Wvec L H τ x t) (dX L τ x t)) (ip (Wvec L H τ x t) (dT L τ x t))
      c mx mt (m0 + mu) hc hcpos hgc hgb hpX hpT hmxn hmtn hMnn
  have hb2 : |(Ycoef L H τ x t).2| ≤ 32 * mx * mt * (m0 + mu) * (mx + mt) / c := by
    rw [hY2]
    have hgb' : |gramB L τ x t| ≤ 4 * mt * mx := by nlinarith [hgb]
    have hthis := ycoef_arith (gramA L τ x t) (gramB L τ x t) (gramDet L τ x t)
      (ip (Wvec L H τ x t) (dT L τ x t)) (ip (Wvec L H τ x t) (dX L τ x t))
      c mt mx (m0 + mu) hc hcpos hga hgb' hpT hpX hmtn hmxn hMnn
    have hEq : 32 * mt * mx * (m0 + mu) * (mt + mx) / c
        = 32 * mx * mt * (m0 + mu) * (mx + mt) / c := by ring
    rwa [hEq] at hthis
  -- the norm on `ℝ × ℝ` is the maximum of the two component norms
  have hnorm : ‖Ycoef L H τ x t‖ = max |(Ycoef L H τ x t).1| |(Ycoef L H τ x t).2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [hnorm]
  exact max_le hb1 hb2

end Work.RPA3
