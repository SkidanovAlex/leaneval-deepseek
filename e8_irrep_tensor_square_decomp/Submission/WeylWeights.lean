import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Finset.Card
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
import Submission.Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive
import Submission.Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv

/-!
# The weight lattice and the simple reflections for `E₈`

**Coordinates.**  A weight `v : Fin 8 → R` is written in the `ω`-basis of the weight lattice:
`v i = ⟨v, αᵢ∨⟩`.  In these coordinates

* the fundamental weights are the standard basis vectors, and the highest weight `ω₁ + ω₈` of the
  target representation is `lam = e₀ + e₇` (`lam_apply_of_ne`);
* the Weyl vector `ρ` (characterised by `⟨ρ, αᵢ∨⟩ = 1`) is the constant vector `1` (`rho`);
* a weight is **dominant** when all its coordinates are `≥ 0` (`IsDominant`);
* the simple reflection at the node `i` acts by `(sᵢv)ⱼ = vⱼ - vᵢ Aᵢⱼ` (`sref`), is an involution
  (`sref_involutive`) and satisfies `(sᵢv)ᵢ = -vᵢ` (`sref_apply_self`);
* reflecting a weight with a negative `i`-th coordinate weakly increases every *other* coordinate
  (`sref_coord_le`), makes the `i`-th coordinate positive (`sref_apply_pos`), and hence **strictly
  decreases the number of negative coordinates** (`card_neg_sref_lt`).  This last fact is the
  termination argument of the "reflect into the dominant chamber" algorithm: it can be run at most
  eight times.
* the invariant bilinear form is `⟪v, w⟫ = v ⬝ A⁻¹ w` (`form`); it is symmetric (`form_symm`),
  positive definite (`form_posDef`, deduced from the positive definiteness of the `E₈` Cartan
  matrix `Commons.LinearAlgebra.Matrix.Cartan.E8_posDef`), and the simple reflections are
  isometries for it (`sref_isometry`, from
  `Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv`).

The two remaining inputs for the Weyl character theory are (i) the list of the 240 roots in these
`ω`-coordinates (obtainable from the explicit root system of `Submission.E8RootSystem` by applying
the Cartan matrix) and the fact that the simple reflections permute them, and (ii) the sign/length
function of the Weyl group.
-/

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators

namespace Submission.WeylWeights

open Commons.LinearAlgebra.Matrix.Cartan

/-- The `E₈` Cartan matrix. -/
abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-- The `E₈` Cartan matrix over `ℚ`. -/
abbrev E8q : Matrix (Fin 8) (Fin 8) ℚ := CartanMatrix.E₈.map (Int.castRingHom ℚ)

/-- Weights in the `ω`-basis, over `ℤ`. -/
abbrev Wint : Type := Fin 8 → ℤ

/-- Weights in the `ω`-basis, over `ℚ`. -/
abbrev Wq : Type := Fin 8 → ℚ

lemma E8_diag (i : Fin 8) : E8 i i = 2 := E8_diag_offdiag_symm.2.1 i
lemma E8_symm (i j : Fin 8) : E8 i j = E8 j i := E8_diag_offdiag_symm.1 i j
lemma E8_offdiag_le (i j : Fin 8) (h : i ≠ j) : E8 i j ≤ 0 := by
  rcases E8_diag_offdiag_symm.2.2 i j h with h0 | h1
  · simp only [E8, h0, le_refl]
  · simp only [E8, h1]; norm_num

/-- The simple reflection at the node `i` acting on weights: `(sᵢv)ⱼ = vⱼ - vᵢ Aᵢⱼ`. -/
def sref {R : Type*} [CommRing R] (i : Fin 8) (v : Fin 8 → R) : Fin 8 → R :=
  fun j => v j - v i * (E8 i j : R)

@[simp] lemma sref_apply {R : Type*} [CommRing R] (i : Fin 8) (v : Fin 8 → R) (j : Fin 8) :
    sref i v j = v j - v i * (E8 i j : R) := rfl

lemma sref_involutive {R : Type*} [CommRing R] (i : Fin 8) :
    Function.Involutive (sref (R := R) i) :=
  Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive E8 (fun i => E8_diag i) i

@[simp] lemma sref_apply_self {R : Type*} [CommRing R] (i : Fin 8) (v : Fin 8 → R) :
    sref i v i = -v i := by
  rw [sref_apply, E8_diag]
  push_cast
  ring

/-- The fundamental chamber: a weight is dominant when all its coroot-pairing coordinates are
nonnegative. -/
def IsDominant (v : Wq) : Prop := ∀ i, 0 ≤ v i

lemma isDominant_iff (v : Wq) : IsDominant v ↔ ∀ i, 0 ≤ v i := Iff.rfl

/-- **The effect of a simple reflection on the coordinates.**  If `v i < 0` then reflecting at `i`
makes the `i`-th coordinate positive (`sref_apply_pos`) and *weakly decreases* every other
coordinate (`sref_coord_le`).  (The termination of the "reflect into the dominant chamber"
algorithm therefore cannot use the coordinate signs; the correct measure is the number of positive
roots paired negatively with the weight, which drops by exactly one at each step, using that a
simple reflection permutes the positive roots other than `αᵢ`.) -/
lemma sref_coord_le (i : Fin 8) {v : Wq} (hi : v i < 0) (j : Fin 8) (hj : j ≠ i) :
    sref i v j ≤ v j := by
  rw [sref_apply]
  have hoff : (E8 i j : ℚ) ≤ 0 := by exact_mod_cast E8_offdiag_le i j (Ne.symm hj)
  have h1 : 0 ≤ -v i := by linarith
  have h2 : -v i * (E8 i j : ℚ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hoff
  linarith

/-- After reflecting at `i` (with `v i < 0`) the `i`-th coordinate is positive. -/
lemma sref_apply_pos (i : Fin 8) {v : Wq} (hi : v i < 0) : 0 < sref i v i := by
  rw [sref_apply_self]; linarith

/-- The set of nodes at which a weight has a negative coordinate. -/
def negSet (v : Wq) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => v j < 0)

lemma mem_negSet (v : Wq) (j : Fin 8) : j ∈ negSet v ↔ v j < 0 := by
  simp [negSet]

/-- The Weyl vector `ρ`, i.e. the weight with `⟨ρ, αᵢ∨⟩ = 1` for all `i`. -/
def rho : Wint := fun _ => 1

lemma rho_apply (i : Fin 8) : rho i = 1 := rfl

/-- The highest weight `ω₁ + ω₈` of the target representation. -/
def lam : Wint := fun i => if i = 0 ∨ i = 7 then 1 else 0

lemma lam_apply_zero : lam 0 = 1 := rfl
lemma lam_apply_seven : lam 7 = 1 := rfl

lemma lam_apply_of_ne (i : Fin 8) (h0 : i ≠ 0) (h7 : i ≠ 7) : lam i = 0 := by
  simp [lam, h0, h7]

/-- The Weyl-invariant bilinear form on weights: `⟪v, w⟫ = v ⬝ A⁻¹ w`. -/
def form (v w : Wq) : ℚ :=
  v ⬝ᵥ ((E8q)⁻¹).mulVec w

lemma inv_symm (i j : Fin 8) : (E8q)⁻¹ i j = (E8q)⁻¹ j i := by
  have h1 : Matrix.transpose E8q = E8q := by
    ext a b
    simp only [Matrix.transpose_apply, E8q, Matrix.map_apply, E8_symm]
  have h2 : Matrix.transpose ((E8q)⁻¹) = (E8q)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, h1]
  exact congrFun (congrFun h2 j) i

lemma form_symm (v w : Wq) : form v w = form w v := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inv_symm i j]
  ring

lemma E8q_det_ne_zero : E8q.det ≠ 0 := by
  have h : E8q.det = (1 : ℚ) := by
    rw [show E8q = CartanMatrix.E₈.map (Int.castRingHom ℚ) from rfl,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, (show CartanMatrix.E₈.det = 1 from CartanMatrix.E₈_det)]
    norm_num
  rw [h]; norm_num

/-- **The simple reflections are isometries for the Weyl-invariant form.** -/
lemma sref_isometry (i : Fin 8) (v w : Wq) : form (sref i v) (sref i w) = form v w :=
  Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv E8q
    (fun a b => by simp only [E8q, Matrix.map_apply, E8_symm])
    (fun a => by simp only [E8q, Matrix.map_apply, E8_diag]; norm_num)
    E8q_det_ne_zero i v w

end Submission.WeylWeights
