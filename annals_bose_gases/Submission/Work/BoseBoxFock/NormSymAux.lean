import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.OneBodyKin.kinFT_decay_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.NormSymAux` — the vocabulary of the `|z|⁻⁶` kernel-decay estimate

This module fixes the two definitions the route to

`Work.BoseBoxFock.norm_symOp_le_of_dist`

needs, namely the iterated *directional* derivative along a list of directions and its third
`Fin 3`-sum ("the Laplacian cubed"), together with the elementary structural lemmas:

* `dIter f L` — iterate the directional derivative, the head of the list being the *outermost*
  derivative: `dIter f (v :: L) p = fderiv ℝ (dIter f L) p v`;
* `lap3 f = ∑_{a b c} dIter f [e_a,e_a,e_b,e_b,e_c,e_c]` — i.e. the classical `Δ³`, written as
  the explicit sum of the `27 = 3³` sixth-order directional derivatives.  The `27` is the
  constant in the target statement;
* `dIter_eq_iteratedFDeriv` — `dIter f L p` is the `|L|`-th iterated derivative of `f` at `p`
  evaluated on the directions of `L` (in order), so that it is bounded by the norm of
  `iteratedFDeriv ℝ |L| f p` (`norm_dIter_le`);
* `norm_lap3_apply_le` — the pointwise `27`-bound `‖lap3 f p‖ ≤ 27 ‖iteratedFDeriv ℝ 6 f p‖`.

The analytic contents (the identity `lap3 (kinFT u) = -kinFT (‖·‖⁶ u)`, the pairing identity
`∫ f · lap3 g = ∫ (lap3 f) · g` for compactly supported `g`, and the decay of the iterated
derivatives of `kinFT u`) are separate modules on top of this one.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The iterated directional derivative along a list -/

/-- Iterated directional derivative: `dIter f [] = f` and
`dIter f (v :: L) = fun p => fderiv ℝ (dIter f L) p v` — the head of the list is the outermost
derivative. -/
noncomputable def dIter (f : E3 → ℂ) : List E3 → E3 → ℂ
  | [] => f
  | v :: L => fun p => fderiv ℝ (dIter f L) p v

@[simp] lemma dIter_nil (f : E3 → ℂ) : dIter f [] = f := rfl

@[simp] lemma dIter_cons (f : E3 → ℂ) (v : E3) (L : List E3) :
    dIter f (v :: L) = fun p => fderiv ℝ (dIter f L) p v := rfl

/-- Evaluation of a continuous multilinear map at a fixed tuple, as a continuous linear map. -/
noncomputable def evalCLM {n : ℕ} (w : Fin n → E3) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    ({ toFun := fun m => m w
       map_add' := fun a b => by simp
       map_smul' := fun c a => by simp } :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) ℂ →ₗ[ℝ] ℂ)
    (∏ i, ‖w i‖) (fun m => by rw [mul_comm]; exact ContinuousMultilinearMap.le_opNorm m w)

@[simp] lemma evalCLM_apply {n : ℕ} (w : Fin n → E3)
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) ℂ) : evalCLM w m = m w := rfl

/-- The derivative of `p ↦ (iteratedFDeriv ℝ n f p) w`: evaluation commutes with `fderiv`. -/
lemma fderiv_iteratedFDeriv_apply_eval {n : ℕ} {f : E3 → ℂ} {p : E3}
    (hd : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ n f q) p) (w : Fin n → E3) :
    fderiv ℝ (fun q => iteratedFDeriv ℝ n f q w) p
      = (evalCLM w).comp (fderiv ℝ (fun q => iteratedFDeriv ℝ n f q) p) := by
  have h1 : HasFDerivAt (fun q => iteratedFDeriv ℝ n f q)
      (fderiv ℝ (fun q => iteratedFDeriv ℝ n f q) p) p := hd.hasFDerivAt
  have h2 : HasFDerivAt ((evalCLM w) ∘ fun q => iteratedFDeriv ℝ n f q)
      ((evalCLM w).comp (fderiv ℝ (fun q => iteratedFDeriv ℝ n f q) p)) p :=
    (evalCLM w).hasFDerivAt.comp p h1
  exact h2.fderiv

/-! ## 2. The "Laplacian cubed" as an explicit sum of `27` sixth-order derivatives -/

/-- The list of directions `[e_a,e_a,e_b,e_b,e_c,e_c]` attached to a triple `a b c`. -/
def lap3List (a b c : Fin 3) : List E3 :=
  [EuclideanSpace.single a (1 : ℝ), EuclideanSpace.single a (1 : ℝ),
   EuclideanSpace.single b (1 : ℝ), EuclideanSpace.single b (1 : ℝ),
   EuclideanSpace.single c (1 : ℝ), EuclideanSpace.single c (1 : ℝ)]

lemma norm_eq_one_of_mem_lap3List {a b c : Fin 3} {v : E3} (hv : v ∈ lap3List a b c) :
    ‖v‖ = 1 := by
  simp only [lap3List, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma length_lap3List (a b c : Fin 3) : (lap3List a b c).length = 6 := rfl

/-- The corpus's `Δ³`, written as the sum of the `27` sixth-order directional derivatives
`∂_a∂_a∂_b∂_b∂_c∂_c`, `a b c : Fin 3`. -/
noncomputable def lap3 (f : E3 → ℂ) : E3 → ℂ :=
  fun p => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) p

/-! ## 3. `dIter` is the iterated derivative evaluated on the tuple of directions -/

/-- `dIter f L p` is `iteratedFDeriv ℝ (L.length) f p` evaluated on the tuple of directions of
`L` (in order, the head first). -/
lemma dIter_eq_iteratedFDeriv (f : E3 → ℂ) (hf : ContDiff ℝ (⊤ : ENat) f)
    (L : List E3) (p : E3) :
    dIter f L p = iteratedFDeriv ℝ L.length f p (fun i => L.get i) := by
  induction L generalizing p with
  | nil => simp
  | cons v L ih =>
    rw [dIter_cons]
    change fderiv ℝ (dIter f L) p v = _
    rw [show (dIter f L) = fun q => iteratedFDeriv ℝ L.length f q (fun i => L.get i) from
      funext fun q => ih q]
    have hd : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ L.length f q) p :=
      (hf.iteratedFDeriv_right (m := (1 : WithTop ℕ∞)) (i := L.length)
        (show ((1 : WithTop ℕ∞) + ↑L.length : WithTop ℕ∞) ≤ ↑(⊤ : ENat) from by
          rw [show ((1 : WithTop ℕ∞) + ↑L.length : WithTop ℕ∞) = ↑((1 : ENat) + L.length)
            from rfl]
          exact WithTop.coe_le_coe.mpr le_top)).differentiable (by simp) |>.differentiableAt
    rw [fderiv_iteratedFDeriv_apply_eval (f := f) (n := L.length) hd (w := fun i => L.get i)]
    rw [ContinuousLinearMap.comp_apply, evalCLM_apply]
    show ((fderiv ℝ (fun q => iteratedFDeriv ℝ L.length f q) p) v) (fun i => L.get i)
      = iteratedFDeriv ℝ (L.length + 1) f p (fun i => (v :: L).get i)
    rw [iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) (x := p)
      (n := L.length) (m := fun i => (v :: L).get i)]
    simp only [List.get_cons_zero]
    congr 1

/-- Bound of a single iterated directional derivative by the norm of the iterated derivative,
for directions of norm `1`. -/
lemma norm_dIter_le (f : E3 → ℂ) (hf : ContDiff ℝ (⊤ : ENat) f) {L : List E3}
    (hL : ∀ v ∈ L, ‖v‖ = 1) (p : E3) :
    ‖dIter f L p‖ ≤ ‖iteratedFDeriv ℝ L.length f p‖ := by
  rw [dIter_eq_iteratedFDeriv f hf L p]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have h1 : ∏ i : Fin L.length, ‖(fun i => L.get i) i‖ = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [hL (L.get i) (List.get_mem _ _)]
  rw [h1, mul_one]

/-- **The `27`-bound**: the Laplacian cubed is controlled pointwise by the sixth iterated
derivative. -/
theorem norm_lap3_apply_le (f : E3 → ℂ) (hf : ContDiff ℝ (⊤ : ENat) f) (p : E3) :
    ‖lap3 f p‖ ≤ 27 * ‖iteratedFDeriv ℝ 6 f p‖ := by
  have h3 : ∀ (a b c : Fin 3), ‖dIter f (lap3List a b c) p‖ ≤ ‖iteratedFDeriv ℝ 6 f p‖ := by
    intro a b c
    have := norm_dIter_le f hf (L := lap3List a b c)
      (fun v hv => norm_eq_one_of_mem_lap3List hv) p
    rwa [length_lap3List] at this
  have h2 : ∀ (a b : Fin 3), ‖∑ c : Fin 3, dIter f (lap3List a b c) p‖
      ≤ 3 * ‖iteratedFDeriv ℝ 6 f p‖ := by
    intro a b
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c : Fin 3, ‖dIter f (lap3List a b c) p‖
        ≤ ∑ _c : Fin 3, ‖iteratedFDeriv ℝ 6 f p‖ := Finset.sum_le_sum (fun c _ => h3 a b c)
      _ = 3 * ‖iteratedFDeriv ℝ 6 f p‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have h1 : ∀ a : Fin 3, ‖∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) p‖
      ≤ 9 * ‖iteratedFDeriv ℝ 6 f p‖ := by
    intro a
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : Fin 3, ‖∑ c : Fin 3, dIter f (lap3List a b c) p‖
        ≤ ∑ _b : Fin 3, 3 * ‖iteratedFDeriv ℝ 6 f p‖ := Finset.sum_le_sum (fun b _ => h2 a b)
      _ = 9 * ‖iteratedFDeriv ℝ 6 f p‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num; ring
  calc ‖lap3 f p‖ = ‖∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) p‖ := rfl
    _ ≤ ∑ a : Fin 3, ‖∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) p‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : Fin 3, 9 * ‖iteratedFDeriv ℝ 6 f p‖ := Finset.sum_le_sum (fun a _ => h1 a)
    _ = 27 * ‖iteratedFDeriv ℝ 6 f p‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Work.BoseBoxFock
