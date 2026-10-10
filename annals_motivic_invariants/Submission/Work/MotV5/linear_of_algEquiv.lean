import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open Polynomial IntermediateField

/-- A `𝕜`-algebra automorphism of `𝕜(X)` whose value on `X` has a pole at infinity
(`1 ≤ intDegree`, `intDegree = num.natDegree - denom.natDegree`) is an affine map `X ↦ cX + d`,
`c ≠ 0`.  This is the degree-`1` case of "every automorphism of `𝕜(X)` is Möbius".

Route (`RatFunc.finrank_eq_max_natDegree` does the work; no Gauss-lemma/extension-degree
argument is needed).  Put `f := α RatFunc.X`.
1. `(⊤ : IntermediateField 𝕜 (RatFunc 𝕜)).map (α : RatFunc 𝕜 →ₐ[𝕜] RatFunc 𝕜) = ⊤` (surjectivity
   of `α`), and `IntermediateField.adjoin_map` + `RatFunc.adjoin_X (K := 𝕜)`
   (`𝕜⟮RatFunc.X⟯ = ⊤`) show this equals `IntermediateField.adjoin 𝕜 {α RatFunc.X}`; hence
   `𝕜⟮f⟯ = ⊤`.  (After the rewrite the goal `𝕜⟮↑α RatFunc.X⟯ = 𝕜⟮α RatFunc.X⟯` closes by `rfl`.)
2. `RatFunc.finrank_eq_max_natDegree f : Module.finrank (↥𝕜⟮f⟯) (RatFunc 𝕜)
   = max f.num.natDegree f.denom.natDegree`, and `IntermediateField.finrank_top` turns the
   left-hand side into `1`.
3. `RatFunc.intDegree f = f.num.natDegree - f.denom.natDegree`, so `1 ≤ intDegree f` with both
   `≤ 1` forces `f.num.natDegree = 1` and `f.denom.natDegree = 0`.
4. `f.denom` is monic (`RatFunc.monic_denom`) of `natDegree 0`, so (`Polynomial.eq_C_of_natDegree_eq_zero`
   and `leadingCoeff = coeff 0`) `f.denom = 1`; `RatFunc.num_div_denom` then gives
   `f = algebraMap _ f.num`.
5. `Polynomial.natDegree_eq_one` gives `c ≠ 0`, `d` with `Polynomial.C c * Polynomial.X + Polynomial.C d = f.num`;
   push `algebraMap` through with `RatFunc.algebraMap_C`, `RatFunc.algebraMap_X`, `map_add`, `map_mul`. -/
theorem linear_of_algEquiv {𝕜 : Type} [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (h : 1 ≤ (α RatFunc.X).intDegree) :
    ∃ c d : 𝕜, c ≠ 0 ∧ α RatFunc.X = RatFunc.C c * RatFunc.X + RatFunc.C d := by
  set f := α RatFunc.X with hf
  -- Step 1: `f` generates `𝕜(X)` over `𝕜`, because it is the image of `X` under the automorphism.
  have hgen : (⊤ : IntermediateField 𝕜 (RatFunc 𝕜)) = 𝕜⟮α RatFunc.X⟯ := by
    have h2 := IntermediateField.adjoin_map 𝕜 ({RatFunc.X} : Set (RatFunc 𝕜))
      (α : RatFunc 𝕜 →ₐ[𝕜] RatFunc 𝕜)
    rw [RatFunc.adjoin_X, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      AlgEquiv.fieldRange_eq_top] at h2
    exact h2
  have htop : 𝕜⟮f⟯ = ⊤ := by rw [hf]; exact hgen.symm
  -- Step 2: the extension degree of `𝕜⟮f⟯ ⊆ 𝕜(X)` is `max f.num.natDegree f.denom.natDegree`,
  -- and it is `1` because `𝕜⟮f⟯ = ⊤`.
  have hfin : Module.finrank (↥𝕜⟮f⟯) (RatFunc 𝕜) = 1 := by
    rw [htop]
    exact IntermediateField.finrank_top
  have hmax : max f.num.natDegree f.denom.natDegree = 1 := by
    rw [← RatFunc.finrank_eq_max_natDegree f]
    exact hfin
  -- Step 3: the degree condition `1 ≤ intDegree f` then pins both degrees down.
  have hint : (1 : ℤ) ≤ (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := h
  have hnum : f.num.natDegree = 1 := by
    have h2 : f.num.natDegree ≤ 1 := le_trans (le_max_left _ _) (le_of_eq hmax)
    omega
  have hden : f.denom.natDegree = 0 := by
    omega
  -- Step 4: `f.denom = 1`, so `f` is the image of a polynomial, namely `f.num`.
  have hden1 : f.denom = 1 := by
    have hm := RatFunc.monic_denom f
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hden] at hm
    rw [Polynomial.eq_C_of_natDegree_eq_zero hden, hm, Polynomial.C_1]
  have hnumdiv : f = algebraMap (Polynomial 𝕜) (RatFunc 𝕜) f.num := by
    have h3 := RatFunc.num_div_denom f
    rw [hden1, map_one, div_one] at h3
    exact h3.symm
  -- Step 5: a degree-`1` polynomial is `c·X + d` with `c ≠ 0`, and `algebraMap` is injective on
  -- polynomials of degree `≤ 1`.
  obtain ⟨c, hc, d, hd⟩ := Polynomial.natDegree_eq_one.mp hnum
  refine ⟨c, d, hc, ?_⟩
  rw [hnumdiv, ← hd, map_add, map_mul]
  simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_X]

end Work.MotV5
