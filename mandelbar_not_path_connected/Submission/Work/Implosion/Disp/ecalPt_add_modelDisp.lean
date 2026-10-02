import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Disp

open Complex

/-! ## Helper lemmas: the Écalle point map in terms of `ecalE`

The point map `ζ(u) = a·(s+1)/(s−1)` with `s = e^{2au}` depends only on `s`.  This
is the observation that makes the target identity purely about the multiplier
`ecalE`, which is exactly what the multiplier identities of `Disp.lean` control.
-/

/-- `ecalPt` is a function of `ecalE` alone. -/
theorem ecalPt_congr {a x y : ℂ} (h : ecalE a x = ecalE a y) :
    ecalPt a x = ecalPt a y := by
  simp only [ecalPt]
  rw [h]

/-- The Écalle point is never the fixed point `a` (when `a ≠ 0`): the two ends of
the cylinder correspond to `s = ∞` and `s = 0`, not to the fixed points. -/
theorem ecalPt_ne_left (a u : ℂ) (ha : a ≠ 0) (hs : ecalE a u ≠ 1) :
    ecalPt a u ≠ a := by
  intro h
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hsub := ecalPt_sub a u hs
  rw [h, sub_self] at hsub
  rw [eq_comm, div_eq_zero_iff] at hsub
  rcases hsub with h' | h'
  · exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ha) h'
  · exact hd h'

/-- The Écalle point is never the fixed point `−a`. -/
theorem ecalPt_ne_right (a u : ℂ) (ha : a ≠ 0) (hs : ecalE a u ≠ 1) :
    ecalPt a u ≠ -a := by
  have hE0 : ecalE a u ≠ 0 := Complex.exp_ne_zero (2 * a * u)
  intro h
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hadd := ecalPt_add a u hs
  rw [h, neg_add_cancel] at hadd
  rw [eq_comm, div_eq_zero_iff] at hadd
  rcases hadd with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ha) h''
    · exact hE0 h''
  · exact hd h'

/-- The normal form does not return the fixed point `a` as long as the
`(ζ+a)`-denominator perturbation `1 + A₂` is non-zero (no critical preimage
issue): `f(ζ) = a` forces `ζ = a`. -/
theorem normalForm_ne_left (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hs : ecalE a u ≠ 1) (h2 : 1 + dispNum2 a h u ≠ 0) :
    normalForm a h (ecalPt a u) ≠ a := by
  have hζ : ecalPt a u ≠ a := ecalPt_ne_left a u ha hs
  have hprod : (ecalPt a u - a) * (1 + dispNum2 a h u) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hζ) h2
  intro hh
  have hsub := normalForm_sub_left a h (ecalPt a u)
  rw [hh, sub_self] at hsub
  exact hprod hsub.symm

/-- The normal form does not return the fixed point `−a` as long as the
`(ζ−a)`-denominator perturbation `1 + A₁` is non-zero. -/
theorem normalForm_ne_right (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hs : ecalE a u ≠ 1) (h1 : 1 + dispNum1 a h u ≠ 0) :
    normalForm a h (ecalPt a u) ≠ -a := by
  have hζ : ecalPt a u ≠ -a := ecalPt_ne_right a u ha hs
  have hprod : (ecalPt a u + a) * (1 + dispNum1 a h u) ≠ 0 :=
    mul_ne_zero (fun hc => hζ (by linear_combination hc)) h1
  intro hh
  have hadd := normalForm_add_left a h (ecalPt a u)
  rw [hh, neg_add_cancel] at hadd
  exact hprod hadd.symm

/-- **The displacement model is exact on the Écalle cylinder.**  Adding the
explicit displacement `Φ(u)` to the coordinate `u` produces, under the point map
`ζ`, exactly one iterate of the local normal form `f`: `ecalPt` is determined by
the multiplier `ecalE`, and the two multipliers `ecalE(u + Φ(u))` and
`ecalE(u(f(ζ(u))))` agree by the exact multiplier identities of `Disp.lean`.  -/
theorem ecalPt_add_modelDisp (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hs : ecalE a u ≠ 1) (h1 : 1 + dispNum1 a h u ≠ 0) (h2 : 1 + dispNum2 a h u ≠ 0) :
    ecalPt a (u + modelDisp a h u) = normalForm a h (ecalPt a u) := by
  have hζne_a : ecalPt a u ≠ a := ecalPt_ne_left a u ha hs
  have hNF_ne_a : normalForm a h (ecalPt a u) ≠ a := normalForm_ne_left a h u ha hs h2
  have hNF_ne_na : normalForm a h (ecalPt a u) ≠ -a := normalForm_ne_right a h u ha hs h1
  have hmob : mobius a (normalForm a h (ecalPt a u)) ≠ 0 := by
    rw [mobius]
    intro hm
    rw [div_eq_zero_iff] at hm
    rcases hm with hm | hm
    · exact hNF_ne_na (by linear_combination hm)
    · exact hNF_ne_a (by linear_combination hm)
  -- `ecalPt` at the model map inverts the normal form.
  have hmodel : ecalPt a (modelMap a h u) = normalForm a h (ecalPt a u) := by
    rw [modelMap]
    exact ecalPt_ecalCoord a (normalForm a h (ecalPt a u)) ha hNF_ne_a hNF_ne_na
  -- the two multipliers agree
  have hE : ecalE a (u + modelDisp a h u) = ecalE a (modelMap a h u) := by
    rw [ecalE_add_modelDisp a h u ha h2 h1, ecalE_modelMap a h u ha hs hζne_a h2 hmob]
  exact (ecalPt_congr hE).trans hmodel

end Work.Implosion.Disp
