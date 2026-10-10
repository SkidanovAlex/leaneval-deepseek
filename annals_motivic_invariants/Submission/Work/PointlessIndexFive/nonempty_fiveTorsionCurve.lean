import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.GoodAut
import Submission.Work.PointlessIndexFive.hasGoodAut_char_two
import Submission.Work.PointlessIndexFive.hasGoodAut_char_three
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

namespace Work.PointlessIndexFive

open WeierstrassCurve WeierstrassCurve.Affine
open Work.TorsorExistence

/-- **Putting a Weierstrass model into short form** when `2` and `3` are invertible: there is an
admissible change of variables `C` with `C • W = ⟨0, 0, 0, a₄, a₆⟩` for some `a₄, a₆`.

This is the interface form of Mathlib's `WeierstrassCurve.exists_variableChange_isShortNF`
(`IsShortNF` is exactly `a₁ = a₂ = a₃ = 0`), used to reduce Silverman *AEC* A.1.2 in
characteristic `≠ 2, 3` to the short-model statement `Work.Arithmetic.Aut_orderOf_dvd_of_short`
(via `Work.PointlessIndexFive.hasGoodAut_short` and the transport
`Work.PointlessIndexFive.hasGoodAut_of_smul_eq`). -/
theorem exists_short_variableChange {𝕜 : Type} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (W : WeierstrassCurve 𝕜) :
    ∃ (C : WeierstrassCurve.VariableChange 𝕜) (a₄ a₆ : 𝕜),
      C • W = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜) := by
  haveI := invertibleOfNonzero h2
  haveI := invertibleOfNonzero h3
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_isShortNF W
  exact ⟨C, (C • W).a₄, (C • W).a₆, by
    ext
    · exact hC.a₁
    · exact hC.a₂
    · exact hC.a₃
    · rfl
    · rfl⟩

/-- **Step (B) of the paper's proof, with the Silverman A.1.2 datum attached, in every
characteristic.**  Over any infinite field there is an elliptic curve with `j ≠ 1728`, a rational
point of exact order `5`, and every automorphism of order dividing `2` or `6`: a
`Work.TorsorExistence.FiveTorsionCurve`.

This is the input that the paper's twist construction needs and that the parent chapter's two
separate ingredients (`nonempty_fiveTorsionPoint`: the Tate normal form for `X₁(5)`, and
`nonempty_orderAutCurve`: Silverman A.1.2 as data for a *different* curve) do not provide
separately.  Route: the Tate normal form with a good parameter (`Tate.exists_tate_param`,
`Tate.tate_five_smul`) plus Silverman, *AEC*, Proposition A.1.2 for that curve, split by
characteristic (`≠ 2, 3` via the short model and `Work.Arithmetic.Aut_orderOf_dvd_of_short`; `2` and
`3` by a coefficient comparison for the Tate model, where `j ≠ 1728` means `j ≠ 0`). -/
theorem nonempty_fiveTorsionCurve {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [Infinite 𝕜] :
    Nonempty (Work.TorsorExistence.FiveTorsionCurve 𝕜) := by
  classical
  obtain ⟨c, hΔne, hjne⟩ := Work.TorsorExistence.Tate.exists_tate_param (𝕜 := 𝕜)
  have hΔ : (Tate.tateCurve c).Δ ≠ 0 := by rw [Tate.tateCurve_Δ]; exact hΔne
  have hEll : (Tate.tateCurve c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    exact isUnit_iff_ne_zero.mpr hΔ
  haveI := hEll
  have hc0 : c ≠ 0 := fun hc => hΔne (by rw [hc]; ring)
  have hns00 : Nonsingular (Tate.tateCurve c) 0 0 :=
    (equation_iff_nonsingular (W := Tate.tateCurve c)).mp (Tate.tateCurve_equation_zero c)
  let T : Point (Tate.tateCurve c) := Point.some 0 0 hns00
  have h5T : (5 : ℕ) • T = 0 := Tate.tate_five_smul c hc0 hns00
  have hPne : T ≠ 0 := Point.some_ne_zero hns00
  have hj : (Tate.tateCurve c).j ≠ 1728 := by
    intro h
    have hc4 : (Tate.tateCurve c).c₄ ^ 3 = 1728 * (Tate.tateCurve c).Δ := by
      have h2 := congrArg (fun t => (Tate.tateCurve c).Δ * t) h
      rw [WeierstrassCurve.j_eq] at h2
      rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul,
        mul_comm ((Tate.tateCurve c).Δ) 1728] at h2
      exact h2
    rw [Tate.tateCurve_c₄, Tate.tateCurve_Δ] at hc4
    exact hjne hc4
  -- **Silverman, *AEC*, A.1.2 for the Tate model**, split by characteristic
  have hgood : HasGoodAut (Tate.tateCurve c) := by
    by_cases htwo : (2 : 𝕜) = 0
    · -- **characteristic `2`**: the Tate model has `a₁ = 1 - c ≠ 0` (since `j ≠ 0 = 1728`)
      haveI : CharP 𝕜 2 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr htwo
      have h1728 : (1728 : 𝕜) = 0 := by
        have h : ((1728 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
        simpa using h
      have hj0 : (Tate.tateCurve c).j ≠ 0 := fun h0 => hj (by rw [h0, h1728])
      exact hasGoodAut_char_two (Tate.tateCurve c)
        (fun h => hj0 (WeierstrassCurve.j_eq_zero_of_char_two (W := Tate.tateCurve c) h))
    · by_cases hthree : (3 : 𝕜) = 0
      · -- **characteristic `3`**: complete the square (with `u = 1`) to reach `a₁ = a₃ = 0`;
        -- then `c₄ = a₂ ^ 2` and `c₄ ≠ 0` (since `j ≠ 0 = 1728`), so `a₂ ≠ 0`
        haveI : CharP 𝕜 3 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr hthree
        have h2ne3 : (2 : 𝕜) ≠ 0 := by
          intro h
          have h' : ((2 : ℕ) : 𝕜) = 0 := by simpa using h
          rw [CharP.cast_eq_zero_iff 𝕜 3] at h'
          norm_num at h'
        set C₀ : WeierstrassCurve.VariableChange 𝕜 := ⟨1, 0, -(1 - c) / 2, c / 2⟩ with hC₀def
        have ha1' : (C₀ • Tate.tateCurve c).a₁ = 0 := by
          rw [WeierstrassCurve.variableChange_a₁, hC₀def]
          simp only [Tate.tateCurve, Units.val_one, inv_one]
          field_simp
          first | refl_ring1 | ring
        have ha3' : (C₀ • Tate.tateCurve c).a₃ = 0 := by
          rw [WeierstrassCurve.variableChange_a₃, hC₀def]
          simp only [Tate.tateCurve, Units.val_one, inv_one]
          field_simp
          first | refl_ring1 | ring
        have hc4' : (C₀ • Tate.tateCurve c).c₄ = (C₀ • Tate.tateCurve c).a₂ ^ 2 := by
          have h16 : (16 : 𝕜) = 1 := by
            have h : ((16 : ℕ) : 𝕜) = ((1 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
            simpa using h
          have h48 : (48 : 𝕜) = 0 := by
            have h : ((48 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
            simpa using h
          have step : (C₀ • Tate.tateCurve c).c₄
              = 16 * (C₀ • Tate.tateCurve c).a₂ ^ 2
                - 48 * (C₀ • Tate.tateCurve c).a₄ := by
            rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha1', ha3']
            first | refl_ring1 | ring
          rw [step, h16, h48]
          first | refl_ring1 | ring
        have hj0 : (Tate.tateCurve c).j ≠ 0 := by
          have h1728 : (1728 : 𝕜) = 0 := by
            have h : ((1728 : ℕ) : 𝕜) = ((0 : ℕ) : 𝕜) := by rw [CharP.cast_eq_iff_mod_eq]
            simpa using h
          intro h0
          exact hj (by rw [h0, h1728])
        have hc4ne : (Tate.tateCurve c).c₄ ≠ 0 := by
          intro hc4
          exact hj0 (WeierstrassCurve.j_eq_zero (W := Tate.tateCurve c) hc4)
        have ha2ne : (C₀ • Tate.tateCurve c).a₂ ≠ 0 := by
          intro h
          have hcc : (C₀ • Tate.tateCurve c).c₄ = 0 := by rw [hc4']; rw [h]; ring
          rw [WeierstrassCurve.variableChange_c₄] at hcc
          simp only [hC₀def, Units.val_one, inv_one, one_pow, one_mul] at hcc
          exact hc4ne hcc
        exact hasGoodAut_of_smul_eq C₀ rfl
          (hasGoodAut_char_three (C₀ • Tate.tateCurve c) ha1' ha3' ha2ne)
      · -- **characteristic `≠ 2, 3`**: put the Tate model in short form and use Silverman A.1.2
        -- for short models
        have h2ne : (2 : 𝕜) ≠ 0 := htwo
        have h3ne : (3 : 𝕜) ≠ 0 := hthree
        obtain ⟨C, a₄, a₆, hC⟩ := exists_short_variableChange h2ne h3ne (Tate.tateCurve c)
        haveI : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).IsElliptic :=
          hC ▸ (inferInstance : (C • Tate.tateCurve c).IsElliptic)
        have hj'' : (C • Tate.tateCurve c).j ≠ 1728 := by
          rw [WeierstrassCurve.variableChange_j]
          exact hj
        have hj' : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).j ≠ 1728 := by
          simpa only [← hC] using hj''
        exact hasGoodAut_of_smul_eq C hC (hasGoodAut_short a₄ a₆ h2ne h3ne
          (a₆_ne_zero_of_short a₄ a₆ h2ne hj'))
  exact ⟨{ E := Tate.tateCurve c
           isElliptic := hEll
           j_ne := hj
           P := T
           P_ne_zero := hPne
           five_smul := h5T
           order_aut := hgood }⟩

end Work.PointlessIndexFive
