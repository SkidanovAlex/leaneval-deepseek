import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.TranslationDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# An explicit characteristic-5 Klein datum

This file fixes the explicit `Work.MotV.KleinData` used to prove
`Work.MotV5.exists_kleinData5`: the elliptic curve `y² - y = x³ - x²` (Tate normal form `c = 1`,
the curve `11a3`), `a = b = 1`, and the five Klein coordinates

```
κ₀ = 1
κ₁ = 1 + x - y - x² - x·y
κ₂ = -1 - 2x - 2x² - x·y
κ₃ = -1 + 2x - 2x² + x·y
κ₄ = y - x² + x·y
```

as elements of `L(5·O) = ⟨1, x, y, x², x·y⟩`.  In characteristic 5 the five Pfaffian quadrics
`p₀, …, p₄` of `Work.MotK.kleinP 1 1` vanish on these five functions, i.e. the corresponding map
`E → ℙ⁴` lands on the Klein quintic `C_{1,1}`; the coordinates were found by solving the
Pfaffian relations over `𝔽₅`.

## Hints for the characteristic-5 identities

* Do **not** unfold `D5` with `simp only [D5]`: `Affine.FunctionField` is an `OreLocalization`, and
  unfolding `D5` changes the instance arguments of the function field, after which `simp` can no
  longer match its lemmas.  Use the `rfl`-lemma `D5_coord` to unfold the coordinate matrix only.
* The unfolding of `kleinCoord` is done with
  `simp only [Work.MotV.kleinCoord]; rw [Fin.sum_univ_five]` followed by
  `simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]`.
* The scalar coefficients live in the function field as `algebraMap L _ (algebraMap 𝕜 L c)`;
  rewrite them with `simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg]`.
* The Weierstrass relation is `Work.MotC2.genX_genY_relation`, which for this curve reads
  `Y ^ 2 - Y = X ^ 3 - X ^ 2`, i.e. `Y ^ 2 - Y - X ^ 3 + X ^ 2 = 0`.
* For each `k` the polynomial `p k` satisfies
  `p k = Q k * (Y ^ 2 - Y - X ^ 3 + X ^ 2) + 5 * S k` where `Q`, `S` are the explicit
  polynomials below (`k = 0` has `Q = 2X + 1`, `S = X²(X² - Y)`, …); this is a `ring` identity
  over `ℤ`, and `5 = 0` in characteristic five.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV5
noncomputable section

/-- The explicit Klein datum over a field `𝕜`. -/
def D5 (𝕜 : Type) [Field 𝕜] : Work.MotV.KleinData 𝕜 where
  a := 1
  b := 1
  E := ⟨0, -1, -1, 0, 0⟩
  coord :=
    ![![1, 0, 0, 0, 0],
      ![1, 1, -1, -1, -1],
      ![-1, -2, 0, -2, -1],
      ![-1, 2, 0, -2, 1],
      ![0, 0, 1, -1, 1]]

@[simp] lemma D5_a (𝕜 : Type) [Field 𝕜] : (D5 𝕜).a = 1 := rfl
@[simp] lemma D5_b (𝕜 : Type) [Field 𝕜] : (D5 𝕜).b = 1 := rfl

/-- The Weierstrass coefficients of the base curve of `D5`, unfolded. -/
@[simp] lemma D5_E_a₁ (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E.a₁ = 0 := rfl
@[simp] lemma D5_E_a₂ (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E.a₂ = -1 := rfl
@[simp] lemma D5_E_a₃ (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E.a₃ = -1 := rfl
@[simp] lemma D5_E_a₄ (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E.a₄ = 0 := rfl
@[simp] lemma D5_E_a₆ (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E.a₆ = 0 := rfl

/-- The coordinate matrix of `D5`, unfolded. -/
lemma D5_coord (𝕜 : Type) [Field 𝕜] :
    (D5 𝕜).coord =
      ![![1, 0, 0, 0, 0],
        ![1, 1, -1, -1, -1],
        ![-1, -2, 0, -2, -1],
        ![-1, 2, 0, -2, 1],
        ![0, 0, 1, -1, 1]] := rfl

/-- The base curve of `D5`. -/
lemma D5_E (𝕜 : Type) [Field 𝕜] : (D5 𝕜).E = ⟨0, -1, -1, 0, 0⟩ := rfl

/-- The function field coordinate `X = x` of the base-changed curve. -/
abbrev XX (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Affine.FunctionField ((D5 𝕜).E.baseChange L) :=
  Work.MotV.genX ((D5 𝕜).E.baseChange L)

/-- The function field coordinate `Y = y` of the base-changed curve. -/
abbrev YY (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Affine.FunctionField ((D5 𝕜).E.baseChange L) :=
  Work.MotV.genY ((D5 𝕜).E.baseChange L)

section Arithmetic

variable (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]

/-- A natural number not divisible by `5` is nonzero in a field of characteristic `5`. -/
lemma natcast_ne_zero_of_not_dvd (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {n : ℕ} (h : ¬ 5 ∣ n) :
    (n : 𝕜) ≠ 0 := by
  intro hh
  exact h ((CharP.cast_eq_zero_iff 𝕜 5 n).mp hh)

/-- `D5` is an elliptic curve: its discriminant is `-11`, which is nonzero in characteristic 5. -/
theorem D5_isElliptic : (D5 𝕜).E.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, D5_E]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num
  exact natcast_ne_zero_of_not_dvd 𝕜 (by norm_num)

attribute [local instance] D5_isElliptic

/-- The `j`-invariant of `D5` is `4096 / (-11)`, which is nonzero in characteristic 5. -/
theorem D5_j_ne_zero : (D5 𝕜).E.j ≠ 0 := by
  rw [WeierstrassCurve.j_eq, D5_E]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, WeierstrassCurve.c₄]
  norm_num
  exact ⟨natcast_ne_zero_of_not_dvd 𝕜 (by norm_num), natcast_ne_zero_of_not_dvd 𝕜 (by norm_num)⟩

/-- The `j`-invariant of `D5` is not `1728` in characteristic 5. -/
theorem D5_j_ne : (D5 𝕜).E.j ≠ 1728 := by
  rw [WeierstrassCurve.j_eq, D5_E]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, WeierstrassCurve.c₄]
  norm_num
  intro h
  have h11 : (11 : 𝕜) ≠ 0 := natcast_ne_zero_of_not_dvd 𝕜 (by norm_num)
  have hm : (11 : 𝕜) * (-(11⁻¹ * 4096)) = 11 * (1728 : 𝕜) := by rw [h]
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ h11, one_mul] at hm
  have hm2 : (-4096 : 𝕜) = 19008 := by rw [hm]; norm_num
  have h0 : (23104 : 𝕜) = 0 := by linear_combination -hm2
  exact natcast_ne_zero_of_not_dvd 𝕜 (by norm_num) h0

/-- There is no primitive fifth root of unity in a field of characteristic 5. -/
theorem no_primRoot_five (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L)
    (hζ : IsPrimitiveRoot ζ 5) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  have h5 : (ζ - 1) ^ 5 = 0 := by
    rw [sub_pow_char, hζ.pow_eq_one]
    norm_num
  have h1 : ζ = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (n := 5) (by norm_num)).mp h5)
  exact hζ.ne_one (by norm_num) h1

/-- The `T_diag` field of `Good` for `D5` is vacuous in characteristic 5. -/
theorem D5_T_diag :
    ∀ (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L), IsPrimitiveRoot ζ 5 →
      ∃ σ : Affine.FunctionField ((D5 𝕜).E.baseChange L) ≃ₐ[L]
          Affine.FunctionField ((D5 𝕜).E.baseChange L),
        ∀ i, σ (Work.MotV.kleinCoord (D5 𝕜) L i / Work.MotV.kleinCoord (D5 𝕜) L 0) =
          algebraMap L _ ζ ^ (i : ℕ) *
            (Work.MotV.kleinCoord (D5 𝕜) L i / Work.MotV.kleinCoord (D5 𝕜) L 0) := by
  intro L _ _ ζ hζ
  exact (no_primRoot_five 𝕜 L ζ hζ).elim

/-- The `a² - ab - b²` condition for `D5`: `1 - 1 - 1 = -1 ≠ 0` in characteristic 5. -/
theorem D5_smooth : (D5 𝕜).a ^ 2 - (D5 𝕜).a * (D5 𝕜).b - (D5 𝕜).b ^ 2 ≠ 0 := by
  simp only [D5_a, D5_b]
  norm_num

/-- The base-changed Weierstrass coefficients of `D5`. -/
lemma D5_baseChange_a₁ (L : Type) [Field L] [Algebra 𝕜 L] :
    ((D5 𝕜).E.baseChange L).a₁ = 0 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, D5_E_a₁, map_zero]

lemma D5_baseChange_a₂ (L : Type) [Field L] [Algebra 𝕜 L] :
    ((D5 𝕜).E.baseChange L).a₂ = -1 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂, D5_E_a₂, map_neg, map_one]

lemma D5_baseChange_a₃ (L : Type) [Field L] [Algebra 𝕜 L] :
    ((D5 𝕜).E.baseChange L).a₃ = -1 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃, D5_E_a₃, map_neg, map_one]

lemma D5_baseChange_a₄ (L : Type) [Field L] [Algebra 𝕜 L] :
    ((D5 𝕜).E.baseChange L).a₄ = 0 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄, D5_E_a₄, map_zero]

lemma D5_baseChange_a₆ (L : Type) [Field L] [Algebra 𝕜 L] :
    ((D5 𝕜).E.baseChange L).a₆ = 0 := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆, D5_E_a₆, map_zero]

end Arithmetic

end
end Work.MotV5
