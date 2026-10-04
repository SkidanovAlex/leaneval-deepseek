import Mathlib
import Submission.Work.Diff.GE.frobSq5_frameIndep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame independence of the squared Frobenius norm of a multilinear form

For a `N`-multilinear form `T` on a finite-dimensional real inner product space `V`, the number

`∑ w : Fin N → Fin (finrank ℝ V), (T (e (w 0), …, e (w (N-1))))²`

is the squared Frobenius norm of the tensor `T` and therefore does not depend on the orthonormal
frame `e` used to write it down.  This file proves that fact:

`frobSqN_frame_indep`.

## Proof

The measure of the frame enters only through the *linear* case: for a linear functional `l` and two
orthonormal bases `e`, `f` of the right cardinality, `∑ i, (l (e i))² = ∑ i, (l (f i))²`, since both
are `‖w‖²` for the Riesz representative `w` of `l` (Parseval).  This is
`Work.Diff.GE.sum_sq_lin_frame_change`, proved in the `|∇Rm|²` area.

Given that, we argue by induction on the arity `N`.

* `N = 0`: there is only one tuple of length `0`, so both sides are the same number.

* `N = n + 1`: split the sum at the first index (`sum_fin_succ_cons`), apply the induction
  hypothesis to the `n`-multilinear form obtained by fixing the first slot of `T`
  (`fixFirst T (e i)`), and then, for each fixed tuple `u` of the remaining slots, change the
  frame in the first slot with the linear case (`sum_sq_cons_frame_change`).  Recombining the
  sums (`Finset.sum_comm`) gives the claim for the two frames `f` only.

## Main results

* `Work.Diff.EXT.sum_fin_succ_cons`: splitting a sum over `Fin (n+1) → ι` at the first coordinate.
* `Work.Diff.EXT.fixFirst`: fixing the first slot of an `(n+1)`-multilinear form.
* `Work.Diff.EXT.sum_sq_cons_frame_change`: changing the frame in the first slot, linear case.
* `Work.Diff.EXT.frobSqN_aux`: the general statement for an arbitrary finite index type.
* `Work.Diff.EXT.frobSqN_frame_indep`: the statement for the index type `Fin (finrank ℝ V)`.
-/

namespace Work.Diff.EXT

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

/-- Splitting a sum over `Fin (n + 1) → ι` at the first coordinate: indexing functions
`Fin (n+1) → ι` by the pair (their value at `0`, their tail). -/
theorem sum_fin_succ_cons {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M]
    {n : ℕ} {G : (Fin (n+1) → ι) → M} :
    (∑ w, G w) = ∑ i : ι, ∑ v : Fin n → ι, G (Fin.cons i v) := by
  calc (∑ w : Fin (n+1) → ι, G w)
      = ∑ p : ι × (Fin n → ι), G (Fin.cons p.1 p.2) :=
        (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => ι)) G).symm
    _ = ∑ i : ι, ∑ v : Fin n → ι, G (Fin.cons i v) :=
        Fintype.sum_prod_type (fun p : ι × (Fin n → ι) => G (Fin.cons p.1 p.2))

/-- The first term of the tuple `w ↦ e (w ·)` is `e` applied to the first index, the tail is the
tail: `T (e (w ·)) = T (e (w 0), e (w 1), …)`. -/
theorem sum_sq_split {ι : Type*} [Fintype ι] {n : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin (n+1) => V) ℝ) (e : ι → V) :
    (∑ w : Fin (n+1) → ι, (T (fun s => e (w s))) ^ 2)
      = ∑ i : ι, ∑ v : Fin n → ι, (T (Fin.cons (e i) (fun j => e (v j)))) ^ 2 := by
  have h := sum_fin_succ_cons (G := fun w : Fin (n+1) → ι => (T (fun s => e (w s))) ^ 2)
  conv_lhs => rw [h]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun v _ => ?_))
  have hfun : (fun s : Fin (n+1) => e ((Fin.cons i v : Fin (n+1) → ι) s))
      = (Fin.cons (e i) (fun j => e (v j)) : Fin (n+1) → V) := by
    funext s; cases s using Fin.cases <;> simp
  exact congrArg (fun g : Fin (n+1) → V => (T g) ^ 2) hfun

/-- Fixing the first slot of an `(n+1)`-multilinear form to a vector `x` gives an `n`-multilinear
form `v ↦ T (x, v)`. -/
def fixFirst {n : ℕ} (T : MultilinearMap ℝ (fun _ : Fin (n+1) => V) ℝ) (x : V) :
    MultilinearMap ℝ (fun _ : Fin n => V) ℝ :=
  MultilinearMap.mk' (fun v => T (Fin.cons x v))
    (fun v k a b => by simp only [Fin.cons_update, MultilinearMap.map_update_add])
    (fun v k c a => by simp only [Fin.cons_update, MultilinearMap.map_update_smul])

@[simp] lemma fixFirst_apply {n : ℕ} (T : MultilinearMap ℝ (fun _ : Fin (n+1) => V) ℝ) (x : V)
    (v : Fin n → V) : fixFirst T x v = T (Fin.cons x v) := rfl

/-- **Changing the frame in the first slot.**  For a fixed `n`-tuple `u` of vectors, the function
`x ↦ T (x, u)` is a *linear* functional, so the square sum over the frame is frame independent. -/
theorem sum_sq_cons_frame_change {n : ℕ} {ι : Type*} [Fintype ι]
    (T : MultilinearMap ℝ (fun _ : Fin (n+1) => V) ℝ) (u : Fin n → V) (e f : ι → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ i : ι, (T (Fin.cons (e i) u)) ^ 2) = ∑ i : ι, (T (Fin.cons (f i) u)) ^ 2 := by
  have h := Work.Diff.GE.sum_sq_lin_frame_change (V := V) (ι := ι) hcard
    (T.toLinearMap (Fin.cons (0 : V) u) 0) e f he hf
  simpa [MultilinearMap.toLinearMap_apply, Fin.update_cons_zero] using h

/-- **Frame independence of the squared Frobenius norm, general index type.**  For any finite
index type `ι` with `card ι = finrank ℝ V` the sum `∑ w, (T (e ∘ w))²` is the same for the two
orthonormal families `e` and `f`. -/
theorem frobSqN_aux {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = Module.finrank ℝ V) :
    ∀ (N : ℕ) (T : MultilinearMap ℝ (fun _ : Fin N => V) ℝ) (e f : ι → V),
      Orthonormal ℝ e → Orthonormal ℝ f →
      (∑ w : Fin N → ι, (T (fun s => e (w s))) ^ 2)
        = ∑ w : Fin N → ι, (T (fun s => f (w s))) ^ 2 := by
  intro N
  induction N with
  | zero =>
      intro T e f _ _
      refine Finset.sum_congr rfl (fun w _ => ?_)
      have h : (fun s : Fin 0 => e (w s)) = (fun s : Fin 0 => f (w s)) := by
        funext s; exact Fin.elim0 s
      rw [h]
  | succ n ih =>
      intro T e f he hf
      calc (∑ w : Fin (n+1) → ι, (T (fun s => e (w s))) ^ 2)
          = ∑ i : ι, ∑ v : Fin n → ι, (T (Fin.cons (e i) (fun j => e (v j)))) ^ 2 :=
              sum_sq_split T e
        _ = ∑ i : ι, ∑ v : Fin n → ι, (T (Fin.cons (e i) (fun j => f (v j)))) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have h := ih (fixFirst T (e i)) e f he hf
              simpa using h
        _ = ∑ v : Fin n → ι, ∑ i : ι, (T (Fin.cons (e i) (fun j => f (v j)))) ^ 2 :=
              Finset.sum_comm
        _ = ∑ v : Fin n → ι, ∑ i : ι, (T (Fin.cons (f i) (fun j => f (v j)))) ^ 2 := by
              refine Finset.sum_congr rfl (fun v _ => ?_)
              exact sum_sq_cons_frame_change T (fun j => f (v j)) e f hcard he hf
        _ = ∑ i : ι, ∑ v : Fin n → ι, (T (Fin.cons (f i) (fun j => f (v j)))) ^ 2 :=
              Finset.sum_comm
        _ = ∑ w : Fin (n+1) → ι, (T (fun s => f (w s))) ^ 2 :=
              (sum_sq_split T f).symm

end

/-- **Frame independence of the squared Frobenius norm of an `N`-multilinear form.**  For a
finite-dimensional real inner product space `V` and two orthonormal frames
`e, f : Fin (finrank ℝ V) → V`, the sum of the squares of the `N`-fold evaluations of a
multilinear form `T` is the same in both frames. -/
theorem frobSqN_frame_indep
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [CompleteSpace V] (N : ℕ)
    (T : MultilinearMap ℝ (fun _ : Fin N => V) ℝ)
    (e f : Fin (Module.finrank ℝ V) → V) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    (∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => e (w s))) ^ 2)
      = ∑ w : Fin N → Fin (Module.finrank ℝ V), (T (fun s => f (w s))) ^ 2 :=
  frobSqN_aux (V := V) (Fintype.card_fin (Module.finrank ℝ V)) N T e f he hf

end Work.Diff.EXT
