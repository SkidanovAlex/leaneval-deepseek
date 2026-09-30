import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_div
import Submission.Work.CurveBasics.Curve.BCSquare.L_divMap
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Divisor.le_antisymm
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/--
**Linear equivalence is reflected by base change of divisors.**

Two divisors `D`, `E` on `C` are linearly equivalent, i.e. `D - E` is the divisor of a nonzero
rational function on `C`, if and only if their pullbacks `S.divMap D`, `S.divMap E` under a
base-change square `S : BCSquare C C'` are linearly equivalent on `C'`.

The non-trivial direction uses the base-change statement `L_divMap` for Riemann-Roch spaces:
if `div g = divMap D - divMap E` on `C'`, then `g` and `g⁻¹` exhibit the Riemann-Roch spaces
`L (D - E)` and `L (E - D)` on `C` as non-zero; two nonzero elements `h₁`, `h₂` of these have
`div (h₁ h₂) ≥ 0`, hence `div (h₁ h₂) = 0` (an effective principal divisor has degree `0`), so
`div h₁ = -div h₂`, and the two defining inequalities pin `div h₁ = D - E` exactly.
-/
theorem linEquiv_divMap_iff {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (D E : Curve.Div C) :
    (∃ h : C'.functionField, h ≠ 0 ∧ C'.div h = S.divMap D - S.divMap E) ↔
      (∃ h : C.functionField, h ≠ 0 ∧ C.div h = D - E) := by
  classical
  constructor
  · rintro ⟨g, hgne, hgdiv⟩
    have hM : C'.div g = S.divMap (D - E) := by rw [hgdiv, map_sub]
    -- `g ∈ L'(-divMap (D-E))` and `g⁻¹ ∈ L'(divMap (D-E))`
    have hg₁ : g ∈ C'.L (S.divMap (-(D - E))) := by
      rw [Curve.mem_L_iff]
      right
      intro Q'
      rw [Finsupp.add_apply, map_neg, Finsupp.neg_apply, hM]
      simp
    have hg₂ : g⁻¹ ∈ C'.L (S.divMap (D - E)) := by
      rw [Curve.mem_L_iff]
      right
      intro Q'
      rw [Finsupp.add_apply, Work.CurveBasics.Order.div_inv C' hgne, hM]
      simp
    -- hence the Riemann-Roch spaces on `C` are nontrivial
    have hL1 : C.L (-(D - E)) ≠ ⊥ := by
      intro hbot
      rw [L_divMap S (-(D - E)), hbot] at hg₁
      exact hgne (by simpa using hg₁)
    have hL2 : C.L (D - E) ≠ ⊥ := by
      intro hbot
      rw [L_divMap S (D - E), hbot] at hg₂
      exact inv_ne_zero hgne (by simpa using hg₂)
    obtain ⟨h₂, hh₂mem, hh₂ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL2
    obtain ⟨h₁, hh₁mem, hh₁ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL1
    -- pointwise bounds
    have hle₁ : Curve.Div.le (D - E) (C.div h₁) :=
      Curve.Div.le_iff.mpr (fun Q => by
        rcases (Curve.mem_L_iff C).mp hh₁mem with h0 | heff
        · exact absurd h0 hh₁ne
        · rw [Curve.div_apply]
          simpa using (Curve.isEffective_div_add_iff C).mp heff Q)
    have hle₂ : Curve.Div.le (-(D - E)) (C.div h₂) :=
      Curve.Div.le_iff.mpr (fun Q => by
        rcases (Curve.mem_L_iff C).mp hh₂mem with h0 | heff
        · exact absurd h0 hh₂ne
        · rw [Curve.div_apply]
          exact (Curve.isEffective_div_add_iff C).mp heff Q)
    -- `div (h₁ h₂)` is effective, hence (being principal) of degree `0`, hence zero
    have heff : (C.div (h₁ * h₂)).IsEffective := by
      intro Q
      have h1 : (D - E) Q ≤ (C.div h₁) Q := Curve.Div.le_iff.mp hle₁ Q
      have h2 : (-(D - E)) Q ≤ (C.div h₂) Q := Curve.Div.le_iff.mp hle₂ Q
      rw [Finsupp.neg_apply] at h2
      rw [Curve.div_mul C hh₁ne hh₂ne, Finsupp.add_apply]
      linarith
    have hdiv0 : C.div (h₁ * h₂) = 0 :=
      (Work.CurveBasics.Divisor.deg_eq_zero_iff heff).mp
        (Work.CurveBasics.Order.deg_div C (h₁ * h₂))
    have hsum : C.div h₁ + C.div h₂ = 0 := by
      rw [← Curve.div_mul C hh₁ne hh₂ne, hdiv0]
    have hdiv₁ : C.div h₁ = -C.div h₂ := eq_neg_of_add_eq_zero_left hsum
    have hle₂' : Curve.Div.le (C.div h₁) (D - E) := by
      rw [Curve.Div.le_iff]
      intro Q
      have h2 : (-(D - E)) Q ≤ (C.div h₂) Q := Curve.Div.le_iff.mp hle₂ Q
      rw [Finsupp.neg_apply] at h2
      have hd : (C.div h₁) Q = -(C.div h₂) Q := by rw [hdiv₁, Finsupp.neg_apply]
      rw [hd]
      linarith
    exact ⟨h₁, hh₁ne, (Work.CurveBasics.Divisor.le_antisymm hle₁ hle₂').symm⟩
  · rintro ⟨h, hhne, hdiv⟩
    refine ⟨S.fieldMap.hom h, ?_, ?_⟩
    · intro h0
      exact hhne (fieldMap_injective S (by simpa using h0))
    · rw [← divMap_div S hhne, hdiv, map_sub]

end Work.CurveBasics.Curve.BCSquare
