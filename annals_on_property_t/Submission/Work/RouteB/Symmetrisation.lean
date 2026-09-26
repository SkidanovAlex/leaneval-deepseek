import Submission.Work.RouteB.Ascend
import Submission.Commons.Algebra.Ring.sq_sum_eq_sum_sq_add_partition

open OnPropertyT
open scoped BigOperators

set_option autoImplicit false

namespace Submission.RouteB

/-!
# The cone of sums of hermitian squares

The symmetrisation step of the paper (Method I/II) reasons entirely with the
`Σ²` order: the elements `Sq_n`, `Op_n`, the images `σ(y)` of a sum of squares
`y` under the permutation action, and finite sums of these, are all sums of
hermitian squares.  This file provides the closure properties:

* `IsSOS_add`, `IsSOS_finset_sum` — finite sums of sums of squares;
* `IsSOS_map` — the image of a sum of squares under a ring homomorphism
  commuting with `star` (e.g. the symmetrisation `permRingHom σ` of
  `PermAction.lean`).

The conversion from an index-type sum to a *Finset* sum (the definition used in
`ChallengeDeps.PropertyT`) is
`Commons.Algebra.Star.sum_sq_fintype_eq_finset`; the `√2`-rotation version is
`RouteB.merge_sq_fintype`.
-/

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [DecidableEq A]

/-- `x` is a sum of hermitian squares, in the Finset form of the challenge
statement. -/
def IsSOS (x : A) : Prop := ∃ ξ : Finset A, x = ∑ y ∈ ξ, star y * y

/-- Hermitian squares over an index type are Finset sums of hermitian squares. -/
theorem isSOS_of_fintype {ι : Type*} [Fintype ι] (y : ι → A) :
    IsSOS (∑ i, star (y i) * y i) := by
  classical
  obtain ⟨ζ, hζ⟩ := merge_sq_fintype y
  exact ⟨ζ, hζ⟩

/-- A sum of two sums of hermitian squares is a sum of hermitian squares. -/
theorem IsSOS.add {x y : A} (hx : IsSOS x) (hy : IsSOS y) : IsSOS (x + y) := by
  classical
  obtain ⟨ξ, hξ⟩ := hx
  obtain ⟨η, hη⟩ := hy
  have hsum : x + y
      = ∑ i : (ξ ⊕ η), star (Sum.elim (fun z : ξ => (z : A)) (fun z : η => (z : A)) i)
          * Sum.elim (fun z : ξ => (z : A)) (fun z : η => (z : A)) i := by
    rw [hξ, hη, Fintype.sum_sum_type, ← Finset.sum_coe_sort ξ
        (fun z => star (z : A) * (z : A)), ← Finset.sum_coe_sort η
        (fun z => star (z : A) * (z : A))]
    simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hsum]
  exact isSOS_of_fintype _

/-- A finite sum of sums of hermitian squares is a sum of hermitian squares. -/
theorem IsSOS.finset_sum {ι : Type*} (s : Finset ι) {f : ι → A}
    (h : ∀ i ∈ s, IsSOS (f i)) : IsSOS (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The image of a sum of hermitian squares under a ring homomorphism commuting
with `star` (for example the symmetrisation by a permutation) is again a sum of
hermitian squares. -/
theorem IsSOS.map {B : Type*} [Ring B] [StarRing B] [Algebra ℝ B] [StarModule ℝ B]
    [DecidableEq B] (f : A →+* B)
    (hf : ∀ x : A, f (star x) = star (f x)) {x : A} (hx : IsSOS x) : IsSOS (f x) := by
  classical
  obtain ⟨ξ, hξ⟩ := hx
  have hmap : f x = ∑ i : ξ, star (f (i : A)) * f (i : A) := by
    rw [hξ, map_sum, ← Finset.sum_coe_sort ξ
      (fun z => f (star (z : A) * (z : A)))]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hf])
  rw [hmap]
  exact isSOS_of_fintype _

/-! ## The paper's `Sq_n + Adj_n + Op_n = Δ_n²`

The definitions and the squaring identity of Kaluba–Kielak–Nowak in the abstract
form of a finite set of "edges" `E` with the adjacent/opposite relations
partitioning `E \ {e}`. -/

section Squaring
variable {ι : Type*} [DecidableEq ι] (E : Finset ι) (D : ι → A)
  (adj op : ι → Finset ι)

/-- `Sq_n = ∑_e Δ_e²`. -/
noncomputable def Sq : A := ∑ e ∈ E, D e ^ 2

/-- `Adj_n = ∑_e Δ_e ∑_{f adjacent to e} Δ_f`. -/
noncomputable def Adj : A := ∑ e ∈ E, D e * ∑ f ∈ adj e, D f

/-- `Op_n = ∑_e Δ_e ∑_{f opposite to e} Δ_f`. -/
noncomputable def Op : A := ∑ e ∈ E, D e * ∑ f ∈ op e, D f

/-- **The paper's `sum of sq adj op`.**  With `adj`/`op` partitioning
`E \ {e}` for every `e ∈ E`,
`(∑_{e∈E} Δ_e)² = Sq + Adj + Op`, i.e. `Δ_n² = Sq_n + Adj_n + Op_n`. -/
theorem sq_sum_eq_sq_add_adj_add_op
    (hadj : ∀ e ∈ E, adj e ⊆ E.erase e) (hop : ∀ e ∈ E, op e ⊆ E.erase e)
    (hdisj : ∀ e ∈ E, Disjoint (adj e) (op e))
    (hcover : ∀ e ∈ E, ∀ f ∈ E, f ≠ e → f ∈ adj e ∨ f ∈ op e) :
    (∑ e ∈ E, D e) ^ 2 = Sq E D + Adj E D adj + Op E D op :=
  Commons.Algebra.Ring.sq_sum_eq_sum_sq_add_partition E D adj op hadj hop hdisj hcover

/-- `Sq` is a sum of hermitian squares (`Sq_n ∈ Σ²`), provided each `Δ_e` is
self-adjoint (which holds for the edge-Laplacians: they are Laplacians of
symmetric generating sets). -/
theorem isSOS_Sq (hsa : ∀ e ∈ E, star (D e) = D e) : IsSOS (Sq E D) := by
  classical
  have h : Sq E D = ∑ e ∈ E, star (D e) * D e := by
    simp only [Sq]
    exact Finset.sum_congr rfl (fun e he => by rw [hsa e he, sq])
  rw [h, ← Finset.sum_coe_sort E (fun e => star (D e) * D e)]
  exact isSOS_of_fintype _

end Squaring

end Submission.RouteB