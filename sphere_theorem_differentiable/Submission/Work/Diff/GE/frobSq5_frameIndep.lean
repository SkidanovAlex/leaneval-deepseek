import Mathlib
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators RealInnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Frame independence of the squared Frobenius norm of a `k`-multilinear form

For a `k`-multilinear form `S` on a finite-dimensional real inner product space `V` the number
`∑ i₁ … i_k, (S (e i₁) … (e i_k))²` does not depend on the orthonormal frame `e`
(`e : Fin (finrank ℝ V) → V` orthonormal).

The proof is the classical induction "from the inside out".  We isolate

* `sum_sq_lin_frame_change` (`frob1`): the case of a *linear* functional `l : V →ₗ[ℝ] ℝ`, where
  both sums equal `‖w‖²` for the Riesz representative `w` of `l`
  (`InnerProductSpace.toDual`), using Parseval for the orthonormal basis built from `e`
  (`basisOfOrthonormalOfCardEqFinrank`, `OrthonormalBasis.sum_sq_inner_right`),
* the elementary rotations `rot2` … `rot5` of a sum over `ι` (`Finset.sum_comm`),
* and the "change one slot" lemmas `chg1` … `chg4`, each of which rotates the slot's index to the
  innermost position, applies the linear case to the functional obtained by evaluating the
  partially applied form at the already fixed frame vectors (`evalAt`), and rotates back.

`frobSq5_frameIndep` is the arity-5 case needed for `|∇Rm|²`.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

/-! ## Evaluating an iterated linear map in a fixed slot -/

/-- The evaluation `g ↦ g x` as a linear map. -/
def evalAt {W : Type*} [AddCommMonoid W] [Module ℝ W] (x : V) : (V →ₗ[ℝ] W) →ₗ[ℝ] W where
  toFun g := g x
  map_add' g h := by simp
  map_smul' c g := by simp

@[simp] lemma evalAt_apply {W : Type*} [AddCommMonoid W] [Module ℝ W] (x : V)
    (g : V →ₗ[ℝ] W) : evalAt x g = g x := rfl

/-! ## Rotations of multiple sums over one index type -/

lemma rot2 {ι : Type*} [Fintype ι] (X : ι → ι → ℝ) :
    (∑ a, ∑ b, X a b) = ∑ b, ∑ a, X a b := Finset.sum_comm

lemma rot3 {ι : Type*} [Fintype ι] (X : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, X a b c) = ∑ b, ∑ c, ∑ a, X a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)

lemma rot4 {ι : Type*} [Fintype ι] (X : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, X a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, X a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => rot3 (fun a c d => X a b c d))

lemma rot5sum {ι : Type*} [Fintype ι] (X : ι → ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, X a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, X a b c d e := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => rot4 (fun a c d e => X a b c d e))

/-! ## The linear case -/

/-- **Frame independence for a linear functional.**  If `e` and `f` are orthonormal families of
cardinality `finrank ℝ V`, then `∑ i, (l (e i))² = ∑ i, (l (f i))²`: both are `‖w‖²` for the Riesz
representative `w` of `l`. -/
theorem sum_sq_lin_frame_change {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℝ V) (l : V →ₗ[ℝ] ℝ) (e f : ι → V)
    (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ i, (l (e i)) ^ 2) = ∑ i, (l (f i)) ^ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty]
  · haveI := hι
    -- `e` and `f` are orthonormal bases
    let b : OrthonormalBasis ι ℝ V :=
      (basisOfOrthonormalOfCardEqFinrank he hcard).toOrthonormalBasis (by
        rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact he)
    have hb : (b : ι → V) = e := by
      rw [Module.Basis.coe_toOrthonormalBasis]
      exact coe_basisOfOrthonormalOfCardEqFinrank he hcard
    let b' : OrthonormalBasis ι ℝ V :=
      (basisOfOrthonormalOfCardEqFinrank hf hcard).toOrthonormalBasis (by
        rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hf)
    have hb' : (b' : ι → V) = f := by
      rw [Module.Basis.coe_toOrthonormalBasis]
      exact coe_basisOfOrthonormalOfCardEqFinrank hf hcard
    -- the Riesz representative of `l`
    let w : V := (InnerProductSpace.toDual ℝ V).symm l.toContinuousLinearMap
    have hw1 : (InnerProductSpace.toDual ℝ V) w = l.toContinuousLinearMap :=
      (InnerProductSpace.toDual ℝ V).apply_symm_apply l.toContinuousLinearMap
    have hw : ∀ v : V, l v = ⟪w, v⟫ := by
      intro v
      have h1 : ((InnerProductSpace.toDual ℝ V) w) v = ⟪w, v⟫ := rfl
      rw [hw1] at h1
      rw [← h1]; rfl
    have h1 : (∑ i, (l (e i)) ^ 2) = ‖w‖ ^ 2 := by
      rw [← OrthonormalBasis.sum_sq_inner_right b w]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hw, real_inner_comm, ← hb]
    have h2 : (∑ i, (l (f i)) ^ 2) = ‖w‖ ^ 2 := by
      rw [← OrthonormalBasis.sum_sq_inner_right b' w]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hw, real_inner_comm, ← hb']
    rw [h1, h2]

/-! ## Changing the frame in one slot

Each lemma changes the frame in a single slot of a `k`-multilinear form, the slots to the right
already holding `f` and the slots to the left being arbitrary.  The index of the changed slot is
rotated to the innermost position (`rot2` … `rot5`), the linear case is applied to the functional
`v ↦ S (fixed) v (fixed)` built with `evalAt`, and the rotation is undone. -/

/-- Change the frame in the 4th slot (3 fixed slots to the left). -/
theorem chg_slot4 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = Module.finrank ℝ V)
    (S : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (e f : ι → V) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ k, ∑ l, (S (e k) (f l)) ^ 2) = ∑ k, ∑ l, (S (f k) (f l)) ^ 2 := by
  calc (∑ k, ∑ l, (S (e k) (f l)) ^ 2)
      = ∑ l, ∑ k, (S (e k) (f l)) ^ 2 := rot2 (fun k l => (S (e k) (f l)) ^ 2)
    _ = ∑ l, ∑ k, (S (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          exact sum_sq_lin_frame_change hcard ((evalAt (f l)).comp S) e f he hf
    _ = ∑ k, ∑ l, (S (f k) (f l)) ^ 2 := (rot2 (fun k l => (S (f k) (f l)) ^ 2)).symm

/-- Change the frame in the 3rd slot (2 fixed slots to the left). -/
theorem chg_slot3 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = Module.finrank ℝ V)
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (e f : ι → V) (he : Orthonormal ℝ e)
    (hf : Orthonormal ℝ f) :
    (∑ j, ∑ k, ∑ l, (S (e j) (f k) (f l)) ^ 2)
      = ∑ j, ∑ k, ∑ l, (S (f j) (f k) (f l)) ^ 2 := by
  calc (∑ j, ∑ k, ∑ l, (S (e j) (f k) (f l)) ^ 2)
      = ∑ k, ∑ l, ∑ j, (S (e j) (f k) (f l)) ^ 2 :=
          rot3 (fun j k l => (S (e j) (f k) (f l)) ^ 2)
    _ = ∑ k, ∑ l, ∑ j, (S (f j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
          exact sum_sq_lin_frame_change hcard
            (((evalAt (f l)).comp (evalAt (f k))).comp S) e f he hf
    _ = ∑ j, ∑ k, ∑ l, (S (f j) (f k) (f l)) ^ 2 :=
          (rot3 (fun j k l => (S (f j) (f k) (f l)) ^ 2)).symm

/-- Change the frame in the 2nd slot (1 fixed slot to the left). -/
theorem chg_slot2 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = Module.finrank ℝ V)
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (e f : ι → V) (he : Orthonormal ℝ e)
    (hf : Orthonormal ℝ f) :
    (∑ i, ∑ j, ∑ k, ∑ l, (S (e i) (f j) (f k) (f l)) ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, (S (f i) (f j) (f k) (f l)) ^ 2 := by
  calc (∑ i, ∑ j, ∑ k, ∑ l, (S (e i) (f j) (f k) (f l)) ^ 2)
      = ∑ j, ∑ k, ∑ l, ∑ i, (S (e i) (f j) (f k) (f l)) ^ 2 :=
          rot4 (fun i j k l => (S (e i) (f j) (f k) (f l)) ^ 2)
    _ = ∑ j, ∑ k, ∑ l, ∑ i, (S (f i) (f j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun l _ => ?_)))
          exact sum_sq_lin_frame_change hcard
            ((((evalAt (f l)).comp (evalAt (f k))).comp (evalAt (f j))).comp S) e f he hf
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (S (f i) (f j) (f k) (f l)) ^ 2 :=
          (rot4 (fun i j k l => (S (f i) (f j) (f k) (f l)) ^ 2)).symm

/-- Change the frame in the 1st (outermost) slot, all other slots holding `f`. -/
theorem chg_slot1 {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = Module.finrank ℝ V)
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (e f : ι → V)
    (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (S (e m) (f i) (f j) (f k) (f l)) ^ 2)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (S (f m) (f i) (f j) (f k) (f l)) ^ 2 := by
  calc (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (S (e m) (f i) (f j) (f k) (f l)) ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, (S (e m) (f i) (f j) (f k) (f l)) ^ 2 :=
          rot5sum (fun m i j k l => (S (e m) (f i) (f j) (f k) (f l)) ^ 2)
    _ = ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, (S (f m) (f i) (f j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
            Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
          exact sum_sq_lin_frame_change hcard
            (((((evalAt (f l)).comp (evalAt (f k))).comp (evalAt (f j))).comp
              (evalAt (f i))).comp S) e f he hf
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (S (f m) (f i) (f j) (f k) (f l)) ^ 2 :=
          (rot5sum (fun m i j k l => (S (f m) (f i) (f j) (f k) (f l)) ^ 2)).symm

/-- The squared Frobenius norm `∑ T(e m)(e i)(e j)(e k)(e l)^2` of a 5-multilinear form on a
finite-dimensional real inner product space does not depend on the orthonormal frame used. -/
theorem frobSq5_frameIndep
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (e f : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (e i) (e j) (e k) (e l)) ^ 2)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (f m) (f i) (f j) (f k) (f l)) ^ 2 := by
  have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V := Fintype.card_fin _
  calc (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (e i) (e j) (e k) (e l)) ^ 2)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (e i) (e j) (e k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ =>
            Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))))
          exact sum_sq_lin_frame_change hcard (T (e m) (e i) (e j) (e k)) e f he hf
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (e i) (e j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ =>
            Finset.sum_congr rfl (fun j _ => ?_)))
          exact chg_slot4 hcard (T (e m) (e i) (e j)) e f he hf
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (e i) (f j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ => ?_))
          exact chg_slot3 hcard (T (e m) (e i)) e f he hf
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (e m) (f i) (f j) (f k) (f l)) ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          exact chg_slot2 hcard (T (e m)) e f he hf
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T (f m) (f i) (f j) (f k) (f l)) ^ 2 :=
          chg_slot1 hcard T e f he hf

end Work.Diff.GE
