import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Module Matrix
open NumberField

/-- **Field discriminant vs. an integral basis.**  For a `ℚ`-basis `b` of the number field `F` all
of whose elements are algebraic integers, the field discriminant is bounded in absolute value by
`discr ℚ b`.

Key step: express the basis `b` in the `ℤ`-basis `NumberField.RingOfIntegers.basis F` of `𝓞 F`
(possible since each `b i` is integral, so the coordinate matrix `A` is over `ℤ`); then
`Algebra.discr_of_matrix_vecMul` gives `discr ℚ b = (det A)² * discr ℚ (integralBasis F)`, and
`NumberField.coe_discr` identifies `discr ℚ (integralBasis F) = (NumberField.discr F : ℚ)`.
Since `b` is a `ℚ`-basis, `det A ≠ 0`, so `(det A)² ≥ 1` and `|disc F| ≤ |disc ℚ b|`. -/
theorem discr_le_discr_of_isIntegral_basis {F : Type*} [Field F] [NumberField F]
    (b : Module.Basis (Fin (Module.finrank ℚ F)) ℚ F) (hint : ∀ i, IsIntegral ℤ (b i)) :
    |((NumberField.discr F : ℤ) : ℝ)| ≤
      |((Algebra.discr ℚ (b : Fin (Module.finrank ℚ F) → F) : ℚ) : ℝ)| := by
  classical
  -- Reindex everything by the index type of the `ℤ`-basis of `𝓞 F`.
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 F)) = Module.finrank ℚ F := by
    rw [← finrank_eq_card_chooseBasisIndex ℤ (𝓞 F), NumberField.RingOfIntegers.rank F]
  let e : Free.ChooseBasisIndex ℤ (𝓞 F) ≃ Fin (Module.finrank ℚ F) :=
    Fintype.equivFinOfCardEq hcard
  let b' : Basis (Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ F := b.reindex e.symm
  let b₀ : Basis (Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ F := NumberField.integralBasis F
  -- `b'` again consists of algebraic integers, hence lies in `𝓞 F`.
  have hint' : ∀ i, IsIntegral ℤ (b' i) := by
    intro i
    simp only [b', Basis.reindex_apply, Equiv.symm_symm]
    exact hint (e i)
  -- Reindexing does not change the discriminant.
  have hdiscr_b : Algebra.discr ℚ (b' : _ → F) = Algebra.discr ℚ (b : _ → F) := by
    have h := Algebra.discr_reindex ℚ b e.symm
    simpa [b', Basis.coe_reindex] using h
  -- The elements of `𝓞 F` corresponding to `b'`, and the (integer) coordinate matrix of `b'`
  -- in the `ℤ`-basis `RingOfIntegers.basis F`.
  let c : Free.ChooseBasisIndex ℤ (𝓞 F) → 𝓞 F := NumberField.RingOfIntegers.restrict b' hint'
  let A : Matrix (Free.ChooseBasisIndex ℤ (𝓞 F)) (Free.ChooseBasisIndex ℤ (𝓞 F)) ℤ :=
    (NumberField.RingOfIntegers.basis F).toMatrix c
  -- The coordinate matrix of `b'` in the `ℚ`-basis `integralBasis F`.
  let P : Matrix (Free.ChooseBasisIndex ℤ (𝓞 F)) (Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ :=
    b₀.toMatrix b'
  have hcoe : ∀ j, b' j = algebraMap (𝓞 F) F (c j) := fun j => rfl
  -- `P` is the image of the integer matrix `A` under `ℤ → ℚ`.
  have hP : P = A.map (algebraMap ℤ ℚ) := by
    ext i j
    rw [show P i j = (NumberField.integralBasis F).repr (b' j) i from rfl]
    rw [hcoe j, NumberField.integralBasis_repr_apply]
    rfl
  -- `b'` is obtained from the basis `b₀` by the matrix `P`.
  have hvec : (b₀ ᵥ* P.map (algebraMap ℚ F)) = (b' : _ → F) := by
    rw [show P = b₀.toMatrix b' from rfl]
    exact Basis.toMatrix_map_vecMul b₀ (b' : _ → F)
  -- The discriminant formula: `discr ℚ b' = (det P)² * disc F`.
  have hdiscr_eq : Algebra.discr ℚ (b' : _ → F) = P.det ^ 2 * (NumberField.discr F : ℚ) := by
    rw [← hvec, Algebra.discr_of_matrix_vecMul]
    rw [show Algebra.discr ℚ (b₀ : _ → F) = (NumberField.discr F : ℚ) from
      (NumberField.coe_discr F).symm]
  -- `det P ≠ 0`, because `P` is a change-of-basis matrix between two bases.
  have hdetP : P.det ≠ 0 := by
    have h := Basis.toMatrix_mul_toMatrix_flip b₀ b'
    have h2 : P.det * (b'.toMatrix b₀).det = 1 := by
      rw [← Matrix.det_mul, h, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one h2
  -- `det P` is an integer.
  have hdetP' : P.det = (A.det : ℚ) := by
    have h := RingHom.map_det (algebraMap ℤ ℚ) A
    rw [RingHom.mapMatrix_apply] at h
    rw [hP, ← h]
    rfl
  have hdetA : A.det ≠ 0 := fun h0 => hdetP (by rw [hdetP', h0, Int.cast_zero])
  -- Hence `(det P)² ≥ 1`.
  have hsqZ : (1 : ℤ) ≤ A.det ^ 2 := by
    have h := sq_pos_of_ne_zero hdetA
    omega
  have hcast : (P.det : ℝ) = ((A.det : ℤ) : ℝ) := by
    rw [hdetP']
    exact Rat.cast_intCast A.det
  have hsqR : (1 : ℝ) ≤ (P.det : ℝ) ^ 2 := by
    rw [hcast]
    have h : (1 : ℝ) ≤ ((A.det : ℤ) : ℝ) ^ 2 := by exact_mod_cast hsqZ
    exact h
  have hQ : Algebra.discr ℚ (b : Fin (Module.finrank ℚ F) → F)
      = P.det ^ 2 * (NumberField.discr F : ℚ) := by
    rw [← hdiscr_b, hdiscr_eq]
  have hmain : ((Algebra.discr ℚ (b : Fin (Module.finrank ℚ F) → F) : ℚ) : ℝ)
      = (P.det : ℝ) ^ 2 * ((NumberField.discr F : ℤ) : ℝ) := by
    rw [hQ, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast]
  rw [hmain, abs_mul, abs_of_nonneg (sq_nonneg (P.det : ℝ))]
  have hc := abs_nonneg (((NumberField.discr F : ℤ) : ℝ))
  nlinarith [hsqR, hc]

end Work.BW
