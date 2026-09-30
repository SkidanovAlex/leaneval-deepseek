import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.mobius_height

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Möbius transformation of a Lorentz matrix fixing `∞`

A Lorentz matrix `A` (`Aᵀ J A = J`, `A 4 4 > 0`) that fixes the null vector `infty = (0,0,0,1,1)`
acts on the upper half space model as a "vertical" similarity with scaling factor `1`, i.e. as a
Euclidean isometry of the horizontal coordinates:

`mobius A q = (x ↦ O x + b, q 3)` with `Oᵀ O = 1`.

This is the statement that the stabiliser of `∞` inside the (identity component of the) Lorentz
group is the group of horospherical isometries `ℝ³ ⋊ O(3)`, the Euclidean isometry group of the
horospheres `q 3 = const`.

The analytic content is elementary.  Writing `P = hypOfUHS q` and using that `A ∞ = ∞` together
with the Lorentz isometry property, the difference `(A P)₄ − (A P)₃ = P₄ − P₃ = 1/q₃` is
preserved, so `mobius A q` keeps the height `q 3` and its first three coordinates equal
`(A P)ᵢ q₃`.  Because `Aᵢ₃ + Aᵢ₄ = 0` for `i ≤ 2` (from `A ∞ = ∞`), the terms involving
`(‖q‖² ± 1)/(2q₃)` combine into the constant `−Aᵢ₃`, giving

`mobius A q i = Aᵢ₀ q₀ + Aᵢ₁ q₁ + Aᵢ₂ q₂ − Aᵢ₃`   for `i = 0,1,2`,

which is exactly the Euclidean affine map `x ↦ O x + b` with `O` the top left `3 × 3` block of `A`
and `b = (−A₀₃, −A₁₃, −A₂₃)`.  The orthogonality `Oᵀ O = 1` follows from the diagonal entries of
`Aᵀ J A = J` restricted to the spatial indices, together with `A₃ⱼ = A₄ⱼ` (`j ≤ 2`) which again is
`A ∞ = ∞` in disguise.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

namespace MobiusVertical

/-- The horizontal coordinates `Fin 3 ↪ Fin 4` of the upper half space model. -/
abbrev c3 : Fin 3 → Fin 4 := Fin.castSucc

/-- The spatial coordinates `Fin 3 ↪ Fin 5` of the Lorentz space. -/
abbrev e3 : Fin 3 → Fin 5 := fun i => Fin.castLE (by norm_num : 3 ≤ 5) i

/-- The `∞`-coordinates of the first three spatial indices vanish. -/
theorem infty_e3 (i : Fin 3) : infty (e3 i) = 0 := by fin_cases i <;> rfl

/-- The embedding `Fin 3 ↪ Fin 5` of the spatial coordinates is injective. -/
theorem e3_injective : Function.Injective e3 := by
  intro a b hab
  have h := congrArg Fin.val hab
  simp [e3] at h
  exact Fin.ext h

/-- None of the spatial indices is the timelike index `4`. -/
theorem e3_ne_four (k : Fin 3) : e3 k ≠ 4 := by
  intro hk
  have h := congrArg Fin.val hk
  simp [e3] at h
  omega

/-- For a Lorentz matrix fixing `∞ = (0,0,0,1,1)` the relation `A *ᵥ ∞ = ∞` reads
`Aᵢ₃ + Aᵢ₄ = ∞ᵢ`; in particular `Aᵢ₃ + Aᵢ₄ = 0` for a spatial index `i`. -/
theorem hcol3 {A : Matrix (Fin 5) (Fin 5) ℝ} (hN : A *ᵥ infty = infty) (i : Fin 3) :
    A (e3 i) 3 + A (e3 i) 4 = 0 := by
  have h := congrFun hN (e3 i)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five] at h
  rw [infty_e3 i] at h
  fin_cases i <;>
    · simp [e3, infty_apply_zero, infty_apply_one, infty_apply_two] at h ⊢
      linarith

/-- Multiplication of a basis vector: `(A *ᵥ e_j) k = A k j * c`. -/
theorem mulVec_single_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (j : Fin 5) (c : ℝ) (k : Fin 5) :
    (A *ᵥ Pi.single j c) k = A k j * c := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- For a Lorentz matrix fixing `∞`, the third and fourth rows of `A` agree on the spatial
columns: `A₃ⱼ = A₄ⱼ` for `j ≤ 2`. -/
theorem row_three_eq_four {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A *ᵥ infty = infty) (j : Fin 3) : A 3 (e3 j) = A 4 (e3 j) := by
  have h := lorentz_mulVec_infty hA hN (Pi.single (e3 j) (1:ℝ))
  rw [lorentz_left_infty, lorentz_left_infty] at h
  simp only [mulVec_single_apply] at h
  fin_cases j <;>
    · simp [e3] at h ⊢
      linarith

/-- The entries of `Aᵀ J A = J`: for a Lorentz matrix,
`∑ p A p k (if p = 4 then -1 else 1) A p l = J k l`. -/
theorem entry_identity {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) (k l : Fin 5) :
    ∑ p : Fin 5, A p k * (if p = 4 then (-1:ℝ) else 1) * A p l
      = (if k = l then (if k = 4 then -1 else 1) else 0) := by
  have h : (Aᵀ * J * A) k l = (J : Matrix (Fin 5) (Fin 5) ℝ) k l := by rw [hA.1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal_apply] at h
  have hinner : ∀ j : Fin 5,
      (∑ i : Fin 5, A i k * (if i = j then (if i = 4 then (-1:ℝ) else 1) else 0))
        = A j k * (if j = 4 then -1 else 1) := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [ite_eq_right hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [hinner] at h
  exact h

/-- **The top left `3 × 3` block of a Lorentz matrix fixing `∞` is orthogonal.** -/
theorem orthog {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A *ᵥ infty = infty) :
    (A.submatrix e3 e3)ᵀ * (A.submatrix e3 e3) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply]
  rw [Fin.sum_univ_three]
  change A 0 (e3 k) * A 0 (e3 l) + A 1 (e3 k) * A 1 (e3 l) + A 2 (e3 k) * A 2 (e3 l)
      = (if k = l then 1 else 0)
  have hk := row_three_eq_four hA hN k
  have hl := row_three_eq_four hA hN l
  have he := entry_identity hA (e3 k) (e3 l)
  rw [Fin.sum_univ_five] at he
  simp only [Fin.isValue, Fin.reduceEq, reduceIte] at he
  rw [ite_eq_right (e3_ne_four k)] at he
  have hR : (if e3 k = e3 l then (1:ℝ) else 0) = (if k = l then 1 else 0) := by
    by_cases h : k = l
    · subst h; simp
    · rw [ite_eq_right (fun hh => h (e3_injective hh)), ite_eq_right h]
  rw [hR] at he
  rw [hk, hl] at he
  linarith

/-- The spatial coordinates of `A *ᵥ hypOfUHS q`: for `i ≤ 2`,
`(A *ᵥ hypOfUHS q)ᵢ = (Aᵢ₀ q₀ + Aᵢ₁ q₁ + Aᵢ₂ q₂ − Aᵢ₃)/q₃`. -/
theorem mulVec_hypOfUHS_apply {A : Matrix (Fin 5) (Fin 5) ℝ} (hN : A *ᵥ infty = infty)
    {q : E4} (hq3 : q 3 ≠ 0) (i : Fin 3) :
    (A *ᵥ hypOfUHS q) (e3 i) =
      (∑ j : Fin 3, A (e3 i) (e3 j) * q (c3 j) - A (e3 i) 3) / q 3 := by
  have hcol := hcol3 hN i
  have h4 : A (e3 i) 4 = - A (e3 i) 3 := by linarith
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp only [hypOfUHS_apply_zero, hypOfUHS_apply_one, hypOfUHS_apply_two,
    hypOfUHS_apply_three, hypOfUHS_apply_four, h4]
  rw [Fin.sum_univ_three]
  change A (e3 i) 0 * (q 0 / q 3) + A (e3 i) 1 * (q 1 / q 3) + A (e3 i) 2 * (q 2 / q 3)
        + A (e3 i) 3 * ((‖q‖ ^ 2 - 1) / (2 * q 3)) + -A (e3 i) 3 * ((‖q‖ ^ 2 + 1) / (2 * q 3))
      = (A (e3 i) 0 * q 0 + A (e3 i) 1 * q 1 + A (e3 i) 2 * q 2 - A (e3 i) 3) / q 3
  field_simp
  ring

/-- The spatial coordinates of `mobius A q` for a Lorentz matrix `A` fixing `∞`:
`mobius A q i = Aᵢ₀ q₀ + Aᵢ₁ q₁ + Aᵢ₂ q₂ − Aᵢ₃` for `i ≤ 2`. -/
theorem mobius_apply {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A *ᵥ infty = infty) {q : E4} (hq : 0 < q 3) (i : Fin 3) :
    mobius A q (c3 i) = ∑ j : Fin 3, A (e3 i) (e3 j) * q (c3 j) - A (e3 i) 3 := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have hkey : (A *ᵥ hypOfUHS q) 4 - (A *ᵥ hypOfUHS q) 3 = (q 3)⁻¹ := by
    have h := lorentz_mulVec_infty hA hN (hypOfUHS q)
    rw [lorentz_left_infty, lorentz_left_infty] at h
    have hP := hypOfUHS_four_sub_three hq3
    linarith
  have hu := mulVec_hypOfUHS_apply hN hq3 i
  have hui : uhsOfHyp (A *ᵥ hypOfUHS q) (c3 i)
      = (A *ᵥ hypOfUHS q) (e3 i) * ((A *ᵥ hypOfUHS q) 4 - (A *ᵥ hypOfUHS q) 3)⁻¹ := by
    fin_cases i <;>
      simp [c3, e3, uhsOfHyp_apply_zero, uhsOfHyp_apply_one, uhsOfHyp_apply_two]
  rw [mobius, hui, hkey, inv_inv, hu]
  field_simp

end MobiusVertical

open MobiusVertical in
/-- **A Lorentz matrix fixing the ideal point `∞` acts on the upper half space model as a
Euclidean isometry of the horizontal coordinates with the height fixed.**  There is an orthogonal
`3 × 3` matrix `O` (`Oᵀ O = 1`) and a translation vector `b` such that
`mobius A q = euclidAction O b q = (x ↦ O x + b, q 3)` for every point `q` of the upper half
space. -/
theorem mobius_vertical {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A.mulVec infty = infty) :
    ∃ (O : Matrix (Fin 3) (Fin 3) ℝ) (b : E4), O.transpose * O = 1 ∧
      ∀ q : E4, 0 < q 3 → mobius A q = euclidAction O b q := by
  refine ⟨A.submatrix e3 e3, !₂[-(A 0 3), -(A 1 3), -(A 2 3), 0], orthog hA hN, ?_⟩
  intro q hq
  ext j
  fin_cases j
  · change mobius A q (c3 (0 : Fin 3)) =
      euclidAction (A.submatrix e3 e3) !₂[-A 0 3, -A 1 3, -A 2 3, 0] q (c3 (0 : Fin 3))
    rw [mobius_apply hA hN hq (0 : Fin 3)]
    simp [euclidAction, e3, c3, Fin.sum_univ_three]
    ring
  · change mobius A q (c3 (1 : Fin 3)) =
      euclidAction (A.submatrix e3 e3) !₂[-A 0 3, -A 1 3, -A 2 3, 0] q (c3 (1 : Fin 3))
    rw [mobius_apply hA hN hq (1 : Fin 3)]
    simp [euclidAction, e3, c3, Fin.sum_univ_three]
    ring
  · change mobius A q (c3 (2 : Fin 3)) =
      euclidAction (A.submatrix e3 e3) !₂[-A 0 3, -A 1 3, -A 2 3, 0] q (c3 (2 : Fin 3))
    rw [mobius_apply hA hN hq (2 : Fin 3)]
    simp [euclidAction, e3, c3, Fin.sum_univ_three]
    ring
  · change mobius A q (3 : Fin 4) =
      euclidAction (A.submatrix e3 e3) !₂[-A 0 3, -A 1 3, -A 2 3, 0] q (3 : Fin 4)
    rw [mobius_height hA hN hq]
    simp [euclidAction]

end Work.HypModel
