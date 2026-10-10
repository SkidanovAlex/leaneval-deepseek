import Mathlib
import Submission.Work.PointlessIndexFive.All
import Submission.Work.Arithmetic.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PointlessTwist.Constants

open WeierstrassCurve

/-- **Silverman, *AEC*, Proposition A.1.2.**  For an elliptic Weierstrass model `W` over any field
with `j(W) ≠ 1728`, every automorphism of `W` (every admissible change of variables preserving `W`)
has order dividing `2` or `6`.

This is the case split performed for the Tate normal form in
`Work.PointlessIndexFive.nonempty_fiveTorsionCurve`, restated for an arbitrary elliptic model:
* characteristic `2`: `1728 = 0`, so `j ≠ 0`, which forces `a₁ ≠ 0`, and
  `Work.PointlessIndexFive.hasGoodAut_char_two` bounds the order by `2`;
* characteristic `3`: `1728 = 0`, so `j ≠ 0` forces `c₄ ≠ 0`; completing the square with
  `u = 1, s = -a₁ / 2, t = -a₃ / 2` puts the model in the form `a₁ = a₃ = 0`, where `c₄ = a₂ ^ 2`
  (because `16 = 1` and `48 = 0`), so `a₂ ≠ 0`, and
  `Work.PointlessIndexFive.hasGoodAut_char_three` bounds the order by `2` or `6`;
* remaining characteristics: put `W` in short form via
  `Work.PointlessIndexFive.exists_short_variableChange`; `j ≠ 1728` gives `a₆ ≠ 0`
  (`Work.PointlessIndexFive.a₆_ne_zero_of_short`), and `Work.PointlessIndexFive.hasGoodAut_short`
  bounds the order by `2` or `6`. -/
theorem hasGoodAut_of_j_ne {𝕜 : Type} [Field 𝕜] (W : WeierstrassCurve 𝕜) [W.IsElliptic]
    (hj : W.j ≠ 1728) : Work.PointlessIndexFive.HasGoodAut W := by
  by_cases htwo : (2 : 𝕜) = 0
  · -- **characteristic `2`**: `1728 = 0`, so `j ≠ 0`; and `j = 0` whenever `a₁ = 0`
    haveI : CharP 𝕜 2 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr htwo
    have h1728 : (1728 : 𝕜) = 0 := by
      have h : ((1728 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
      simpa using h
    have hj0 : W.j ≠ 0 := fun h0 => hj (by rw [h0, h1728])
    exact Work.PointlessIndexFive.hasGoodAut_char_two W
      (fun h => hj0 (WeierstrassCurve.j_eq_zero_of_char_two (W := W) h))
  · by_cases hthree : (3 : 𝕜) = 0
    · -- **characteristic `3`**: `1728 = 0`, so `j ≠ 0` and hence `c₄ ≠ 0`; complete the square
      -- with `u = 1`, `r = 0`, `s = -a₁ / 2`, `t = -a₃ / 2` to reach `a₁ = a₃ = 0`
      haveI : CharP 𝕜 3 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr hthree
      have h2ne : (2 : 𝕜) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : 𝕜) = 0 := by simpa using h
        rw [CharP.cast_eq_zero_iff 𝕜 3] at h'
        norm_num at h'
      have h1728 : (1728 : 𝕜) = 0 := by
        have h : ((1728 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
        simpa using h
      have hj0 : W.j ≠ 0 := fun h0 => hj (by rw [h0, h1728])
      have hc4ne : W.c₄ ≠ 0 := fun h => hj0 (WeierstrassCurve.j_eq_zero (W := W) h)
      set C₀ : WeierstrassCurve.VariableChange 𝕜 := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩ with hC₀def
      have ha1' : (C₀ • W).a₁ = 0 := by
        rw [WeierstrassCurve.variableChange_a₁, hC₀def]
        simp only [Units.val_one, inv_one, one_mul]
        field_simp
        first | refl_ring1 | ring
      have ha3' : (C₀ • W).a₃ = 0 := by
        rw [WeierstrassCurve.variableChange_a₃, hC₀def]
        simp only [Units.val_one, inv_one, one_pow, one_mul, zero_mul, add_zero]
        field_simp
        first | refl_ring1 | ring
      -- in characteristic `3` the completed model has `c₄ = a₂ ^ 2` (`16 = 1`, `48 = 0`)
      have hc4' : (C₀ • W).c₄ = (C₀ • W).a₂ ^ 2 := by
        have h16 : (16 : 𝕜) = 1 := by
          have h : ((16 : ℕ) : 𝕜) = ((1 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
          simpa using h
        have h48 : (48 : 𝕜) = 0 := by
          have h : ((48 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
          simpa using h
        have step : (C₀ • W).c₄ = 16 * (C₀ • W).a₂ ^ 2 - 48 * (C₀ • W).a₄ := by
          rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha1', ha3']
          first | refl_ring1 | ring
        rw [step, h16, h48]
        first | refl_ring1 | ring
      -- `c₄` is unchanged by `C₀` (`u = 1`), so `a₂ ^ 2 = c₄ ≠ 0`
      have ha2ne : (C₀ • W).a₂ ≠ 0 := by
        intro h
        have hcc : (C₀ • W).c₄ = 0 := by rw [hc4', h]; ring
        rw [WeierstrassCurve.variableChange_c₄] at hcc
        simp only [hC₀def, Units.val_one, inv_one, one_pow, one_mul] at hcc
        exact hc4ne hcc
      exact Work.PointlessIndexFive.hasGoodAut_of_smul_eq C₀ rfl
        (Work.PointlessIndexFive.hasGoodAut_char_three (C₀ • W) ha1' ha3' ha2ne)
    · -- **characteristic `≠ 2, 3`**: put `W` in short form and use Silverman A.1.2 for short models
      have h2ne : (2 : 𝕜) ≠ 0 := htwo
      have h3ne : (3 : 𝕜) ≠ 0 := hthree
      obtain ⟨C, a₄, a₆, hC⟩ := Work.PointlessIndexFive.exists_short_variableChange h2ne h3ne W
      haveI : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).IsElliptic :=
        hC ▸ (inferInstance : (C • W).IsElliptic)
      have hj'' : (C • W).j ≠ 1728 := by
        rw [WeierstrassCurve.variableChange_j]
        exact hj
      have hj' : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).j ≠ 1728 := by
        simpa only [← hC] using hj''
      exact Work.PointlessIndexFive.hasGoodAut_of_smul_eq C hC
        (Work.PointlessIndexFive.hasGoodAut_short a₄ a₆ h2ne h3ne
          (Work.PointlessIndexFive.a₆_ne_zero_of_short a₄ a₆ h2ne hj'))

end Work.PointlessTwist.Constants
