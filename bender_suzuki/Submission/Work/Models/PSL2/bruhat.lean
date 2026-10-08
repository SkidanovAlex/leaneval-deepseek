import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Bruhat decomposition of `SL(2,F)`, `F` of characteristic `2`

`Work.Models.PSL2.B` is the standard Borel of `SL(2,F)` (upper triangular matrices) and
`Work.Models.PSL2.w` is the Weyl element `!![0,1;1,0]`.  We prove

`SL(2,F) = B ∪ B w B`   (`Work.Models.PSL2.bruhat`),

i.e. an element of `SL(2,F)` is either upper triangular, or is `b₁ w b₂` with `b₁, b₂` upper
triangular.  This is the rank-one Bruhat decomposition for the split torus with trivial
character group (`F` of characteristic `2`), which is the `SL(2,F)`-case of the BN-pair axioms
for the Bender group models.

The proof is the classical explicit computation.  Write `g = !![a,b;c,d]`, so that
`a * d - b * c = 1`.  If `c = 0`, then `g` is upper triangular.  If `c ≠ 0`, put

`b₁ = !![c⁻¹, a; 0, c]`  and  `b₂ = !![1, d c⁻¹; 0, 1]`,

both of determinant `1` (and upper triangular); the matrix identity of
`bruhat_matrix_identity` below — the non-trivial entry is `c⁻¹ + a d c⁻¹ = b`, which holds
because `a d = 1 + b c` in characteristic `2` — gives `b₁ w b₂ = g`.

Characteristic `2` is used only in two places: `-` on `F` is `+` (`CharTwo.sub_eq_add`), so
that the determinant condition reads `a d + b c = 1`, and `x + x = 0`
(`CharTwo.add_self_eq_zero`).
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The explicit matrix identity behind the Bruhat decomposition: for `c ≠ 0` and
`a * d - b * c = 1` over a field of characteristic `2`,
`!![c⁻¹, a; 0, c] * !![0, 1; 1, 0] * !![1, d c⁻¹; 0, 1] = !![a, b; c, d]`.

Indeed the products compute to `!![a, c⁻¹ + a d c⁻¹; c, d]`, and `c⁻¹ + a d c⁻¹ = b` because
multiplying by `c` turns it into `1 + a d = b c`, which is `a d - b c = 1` again in
characteristic `2`. -/
lemma bruhat_matrix_identity (a b c d : F) (hc : c ≠ 0) (h : a * d - b * c = 1) :
    (!![c⁻¹, a; 0, c] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] * !![1, d * c⁻¹; 0, 1]
      = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  have h1 : a * d + b * c = 1 := by
    rw [← CharTwo.sub_eq_add]
    exact h
  rw [← h1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add, mul_comm]

theorem bruhat {F : Type*} [Field F] [CharP F 2] (g : Work.Models.SL2 F) :
    g ∈ Work.Models.PSL2.B (F := F) ∨
      ∃ b₁ ∈ Work.Models.PSL2.B (F := F), ∃ b₂ ∈ Work.Models.PSL2.B (F := F),
        g = b₁ * Work.Models.PSL2.w (F := F) * b₂ := by
  -- the determinant condition on the entries of `g`
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · -- upper triangular: the first alternative
    exact Or.inl hc
  · -- otherwise the explicit factorisation `g = b₁ * w * b₂`
    right
    let b₁ : Work.Models.SL2 F :=
      ⟨!![((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹, (g : Matrix (Fin 2) (Fin 2) F) 0 0; 0,
        (g : Matrix (Fin 2) (Fin 2) F) 1 0], by rw [det_fin_two_of]; simp [hc]⟩
    let b₂ : Work.Models.SL2 F :=
      ⟨!![1, (g : Matrix (Fin 2) (Fin 2) F) 1 1 * ((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹; 0, 1],
        by rw [det_fin_two_of]; simp⟩
    refine ⟨b₁, ?_, b₂, ?_, ?_⟩
    · change (b₁ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp [b₁]
    · change (b₂ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp [b₂]
    · apply Subtype.ext
      show (g : Matrix (Fin 2) (Fin 2) F) = (b₁ : Matrix (Fin 2) (Fin 2) F) *
        (Work.Models.PSL2.w (F := F) : Matrix (Fin 2) (Fin 2) F) * (b₂ : Matrix (Fin 2) (Fin 2) F)
      rw [Work.Models.PSL2.w_coe]
      show (g : Matrix (Fin 2) (Fin 2) F) = (!![((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹,
          (g : Matrix (Fin 2) (Fin 2) F) 0 0; 0, (g : Matrix (Fin 2) (Fin 2) F) 1 0] :
            Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] *
          !![1, (g : Matrix (Fin 2) (Fin 2) F) 1 1 * ((g : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹; 0, 1]
      rw [bruhat_matrix_identity _ _ _ _ hc hdet]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

end Work.Models.PSL2
