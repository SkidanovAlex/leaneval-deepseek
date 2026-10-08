import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.B_le_normalizer_U`

The standard Borel `B` (the upper triangular matrices of `SL(2,F)`, `F` a field of
characteristic `2`) normalizes the unipotent radical `U = {1 + t E₀₁ | t ∈ F}` of `B`.

The content is the explicit computation

`Work.Models.PSL2.B_conj_unip` : for `g ∈ B` and `t : F`,

`g * unip t * g⁻¹ = unip (g₀₀² * t)`,

i.e. conjugation by an upper triangular matrix is again a transvection. Since `B` is a
subgroup, `g⁻¹ ∈ B` as well, so this gives both directions of the normalizer condition
`h ∈ U ↔ g h g⁻¹ ∈ U`.

Characteristic `2` is used twice: for `-x = x` (so that the inverse of `!![a,b;0,d]` is
`!![d,b;0,a]`) and for `x + x = 0` (in the cancellation of the two equal `g₀₀ g₀₁` terms).
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The `(0,1)`-entry identity behind the conjugation computation: for an upper triangular
matrix `!![a,b;0,d]` with `a d = 1`, the entry `a b + (a t + b) a` equals `a² t`, the two
`a b` terms cancelling in characteristic `2`. -/
lemma mul_add_mul_self (a b t : F) : a * b + (a * t + b) * a = a ^ 2 * t := by
  ring_nf
  rw [mul_two, CharTwo.add_self_eq_zero, zero_add]

/-- Conjugation of the transvection `unip t = 1 + t E₀₁` by an upper triangular matrix `g`
of `SL(2,F)`, `F` of characteristic `2`: the result is again a transvection, namely
`unip (g₀₀² t)`.

Indeed for `g = !![a,b;0,d]` (so `a d = 1` and `g⁻¹ = !![d,b;0,a]` in characteristic `2`)
the triple product is `!![1, a b + (a t + b) a; 0, 1]`, and `a b + (a t + b) a = a² t`. -/
lemma B_conj_unip {g : SL2 F} (hg : g ∈ B (F := F)) (t : F) :
    g * unip t * g⁻¹ = unip (((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
  -- the determinant condition reads `a * d = 1` for an upper triangular matrix
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    rwa [h10, mul_zero, sub_zero] at h
  have hdet' : (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [mul_comm]; exact hdet
  -- the explicit inverse of an upper triangular matrix in characteristic `2`
  have hinv : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, (g : Matrix (Fin 2) (Fin 2) F) 0 1;
         0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, CharTwo.neg_eq]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, hinv, unip_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hdet, hdet', pow_two,
      CharTwo.add_self_eq_zero]
  -- the only surviving entry is `a b + (a t + b) a`, which equals `a² t` by char. 2
  ring_nf
  rw [mul_two, CharTwo.add_self_eq_zero, zero_add]

/-- `B` normalizes the unipotent radical `U`: an upper triangular matrix `g` sends the
transvection `unip t` to the transvection `unip (g₀₀² t)`, and the same holds for
`g⁻¹ ∈ B`, which gives both directions of the normalizer condition. -/
theorem B_le_normalizer_U {F : Type*} [Field F] [CharP F 2] :
    Work.Models.PSL2.B (F := F) ≤ Subgroup.normalizer
      ((Work.Models.PSL2.U (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, B_conj_unip hg t⟩
  · intro hh
    have heq : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [heq]
    obtain ⟨t, ht⟩ := hh
    rw [ht]
    exact ⟨_, by simpa using B_conj_unip (B.inv_mem hg) t⟩

end Work.Models.PSL2
