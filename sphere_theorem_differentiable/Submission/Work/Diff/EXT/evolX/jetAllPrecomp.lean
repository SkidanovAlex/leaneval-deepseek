import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Precomposition of a packed operator with a permutation of its slots

`Work.Diff.EXT.evolX.slotPerm e b` extends a permutation `e` of the `K` slots of a packed operator
to the tuples of `Work.Diff.EXT.jetAll`: the identity on the first `b` entries (the differentiation
directions) and `e` on the last `K` entries (the slots).

The target `Work.Diff.EXT.evolX.jetAllPrecomp` says that the `b`-fold covariant jet of the operator
`S` precomposed with the slot permutation `e` is the `b`-fold covariant jet of `S` on the
`slotPerm e b`-permuted tuple.  This is the naturality (functoriality) of the jet construction under
the *linear* reparametrisation of the slots `G ↦ G ∘ e` — the fact that makes the combinatorics of
the composition ladder (`Work.Diff.EXT.evolX.St`, `StO`) independent of the order in which the slots
of the tower are listed.

## The proof

Induction on the jet order `b`.  The base case `b = 0` is the definition of `jetAll` at order zero.

The step uses the definitional unfolding `jetAll g (b+1) K S = extStep g (jetAll g b K S)`: the
inductive hypothesis rewrites the inner operator, and the bookkeeping that is left is exactly the
compatibility of one `extStep` with the pair `(slotPerm e b, slotPerm e (b+1))`:

* `slotPerm e (b+1) 0 = 0` — the new differentiation direction is untouched;
* `slotPerm e (b+1) i.succ = (slotPerm e b i).succ` — the *tails* of the tuples agree;
* `slotPerm e b` is injective, hence a bijection of `Fin (K+b)` — so the Leibniz-correction sums can
  be reindexed (`Work.Diff.EXT.evolX.Fintype.sum_bijective`).

The abstract bookkeeping is isolated in
`Work.Diff.EXT.evolX.precomp_extStep_compPerm` (for an arbitrary operator `T`, an arbitrary
injective `τ` and an arbitrary `σ` with `σ 0 = 0` and `σ i.succ = (τ i).succ`), and the sum
reindexing in `Work.Diff.EXT.evolX.precomp_sum_update_comp`.

Every declaration in this module is fully proved (there are no unfinished proofs here).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Elementary properties of `slotPerm` -/

/-- `slotPerm` is the identity on the first `b` entries (the differentiation directions). -/
theorem precomp_slotPerm_apply_of_lt {K : ℕ} (e : Fin K ≃ Fin K) {b : ℕ} {i : Fin (K + b)}
    (h : (i : ℕ) < b) : slotPerm e b i = i := by
  rw [slotPerm]; exact dite_eq_left h

/-- `slotPerm` on an entry of the slot block: the value is shifted by `b` and permuted by `e`. -/
theorem precomp_slotPerm_val_of_not_lt {K : ℕ} (e : Fin K ≃ Fin K) {b : ℕ} {i : Fin (K + b)}
    (h : ¬ (i : ℕ) < b) :
    (slotPerm e b i : ℕ) = b + (e ⟨(i : ℕ) - b, by omega⟩).val := by
  rw [slotPerm]; simp only [dite_eq_right h]

/-- `slotPerm` commutes with `Fin.succ`: the tail of a `(b+1)`-tuple is the `b`-tuple with its slots
permuted. -/
theorem precomp_slotPerm_succ {K : ℕ} (e : Fin K ≃ Fin K) (b : ℕ) (i : Fin (K + b)) :
    slotPerm e (b + 1) i.succ = (slotPerm e b i).succ := by
  apply Fin.ext
  rw [Fin.val_succ]
  by_cases h : (i : ℕ) < b
  · have h1 : ((i.succ : Fin (K + b + 1)) : ℕ) < b + 1 := by rw [Fin.val_succ]; omega
    rw [precomp_slotPerm_apply_of_lt (b := b + 1) e (i := (i.succ : Fin (K + (b+1)))) h1,
      precomp_slotPerm_apply_of_lt (b := b) e h, Fin.val_succ]
  · have h1 : ¬ ((i.succ : Fin (K + b + 1)) : ℕ) < b + 1 := by rw [Fin.val_succ]; omega
    rw [precomp_slotPerm_val_of_not_lt (b := b + 1) e (i := (i.succ : Fin (K + (b+1)))) h1,
      precomp_slotPerm_val_of_not_lt (b := b) e h]
    have hsub : ((i.succ : Fin (K + b + 1)) : ℕ) - (b + 1) = (i : ℕ) - b := by
      rw [Fin.val_succ]; omega
    have hfin : e ⟨((i.succ : Fin (K + b + 1)) : ℕ) - (b + 1), by omega⟩ =
        e ⟨(i : ℕ) - b, by omega⟩ := by
      congr 1
      apply Fin.ext
      exact hsub
    rw [hfin]
    omega

/-- `slotPerm e b` is injective (it is the identity on the first `b` entries and `e` on the rest). -/
theorem precomp_slotPerm_injective {K : ℕ} (e : Fin K ≃ Fin K) (b : ℕ) :
    Function.Injective (slotPerm e b) := by
  intro i j hij
  by_cases hi : (i : ℕ) < b <;> by_cases hj : (j : ℕ) < b
  · rw [precomp_slotPerm_apply_of_lt e hi, precomp_slotPerm_apply_of_lt e hj] at hij
    exact hij
  · have hv := congrArg Fin.val hij
    rw [precomp_slotPerm_apply_of_lt e hi, precomp_slotPerm_val_of_not_lt e hj] at hv
    omega
  · have hv := congrArg Fin.val hij
    rw [precomp_slotPerm_apply_of_lt e hj, precomp_slotPerm_val_of_not_lt e hi] at hv
    omega
  · have hv := congrArg Fin.val hij
    rw [precomp_slotPerm_val_of_not_lt e hi, precomp_slotPerm_val_of_not_lt e hj] at hv
    have h4 : (⟨(i : ℕ) - b, by omega⟩ : Fin K) = ⟨(j : ℕ) - b, by omega⟩ := by
      refine e.injective (Fin.ext ?_)
      omega
    apply Fin.ext
    have h5 : (i : ℕ) - b = (j : ℕ) - b := congrArg Fin.val h4
    omega

/-- `slotPerm e b` is a bijection of `Fin (K+b)` (an injective self-map of a finite type). -/
theorem precomp_slotPerm_bijective {K : ℕ} (e : Fin K ≃ Fin K) (b : ℕ) :
    Function.Bijective (slotPerm e b) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨precomp_slotPerm_injective e b, rfl⟩

/-! ## The bookkeeping of one `extStep` -/

/-- **`Function.update` along an injective reindexing.**  Updating the entry `τ t` of a tuple and
then reindexing by `τ` is the same as reindexing first and then updating the entry `t`. -/
theorem precomp_update_comp_inj {ι : Type*} [DecidableEq ι] {α : Type*} (τ : ι → ι)
    (hτ : Function.Injective τ) (f : ι → α) (t : ι) (Y : α) :
    (fun i => Function.update f (τ t) Y (τ i)) = Function.update (fun i => f (τ i)) t Y := by
  funext i
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i = t
  · subst h; simp
  · have hne : τ i ≠ τ t := fun hc => h (hτ hc)
    simp [h, hne]

/-- **The Leibniz-correction sums of `extStep` are invariant under an injective reindexing.**  The
sum, over the entries `s` of a tuple, of a function of the tuple with the `s`-th entry replaced by
`Y s` (after reindexing by `τ`), equals the sum over `t` of the same function applied to the tuple
reindexed by `τ` with its `t`-th entry replaced by `Y (τ t)`. -/
theorem precomp_sum_update_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {α β : Type*}
    [AddCommMonoid β] (T : (ι → α) → β) (G Y : ι → α) (τ : ι → ι) (hτ : Function.Injective τ) :
    (∑ s : ι, T (fun i => (Function.update G s (Y s)) (τ i)))
      = ∑ t : ι, T (Function.update (fun i => G (τ i)) t (Y (τ t))) := by
  have hb : Function.Bijective τ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hτ, rfl⟩
  have h1 : (∑ s : ι, T (fun i => (Function.update G s (Y s)) (τ i)))
      = ∑ t : ι, T (fun i => (Function.update G (τ t) (Y (τ t))) (τ i)) :=
    (Fintype.sum_bijective τ hb
      (fun t => T (fun i => (Function.update G (τ t) (Y (τ t))) (τ i)))
      (fun s => T (fun i => (Function.update G s (Y s)) (τ i))) (fun t => rfl)).symm
  rw [h1]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [precomp_update_comp_inj τ hτ G t (Y (τ t))]

/-- **One `extStep` is compatible with a permutation of the slots.**  If `τ` reindexes the slots of
a tuple of arity `K` and `σ` extends it to arity `K+1` by fixing `0` and commuting with `Fin.succ`,
then the covariant derivative of the operator `T` precomposed with the slot permutation `τ` on the
tuple `F` is the covariant derivative of `T` on the `σ`-permuted tuple. -/
theorem precomp_extStep_compPerm {K : ℕ} (g : Submission.Diff.SMet I M)
    {T : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ}
    {τ : Fin K → Fin K} (hτ : Function.Injective τ)
    {F : Fin (K+1) → Work.Diff.EXT.TField (I := I) (M := M)}
    {σ : Fin (K+1) → Fin (K+1)} (hσ0 : σ 0 = 0)
    (hσ : ∀ i : Fin K, σ i.succ = (τ i).succ) :
    Work.Diff.EXT.extStep (I := I) (M := M) g (fun G y => T (fun i => G (τ i)) y) F
      = Work.Diff.EXT.extStep (I := I) (M := M) g T (fun i => F (σ i)) := by
  unfold Work.Diff.EXT.extStep
  funext y
  beta_reduce
  have hGtau : (fun i : Fin K => F (τ i).succ) = (fun i : Fin K => F (σ i.succ)) := by
    funext i; rw [hσ i]
  have hfun : (fun y' : M => T (fun i : Fin K => F (τ i).succ) y')
      = T (fun i : Fin K => F (σ i.succ)) := by
    rw [hGtau]
  have hF0 : F (0 : Fin (K+1)) = F (σ 0) := by rw [hσ0]
  have hY : ∀ t : Fin K, dirF g (F (τ t).succ) (F (σ 0)) = dirF g (F (σ t.succ)) (F (σ 0)) := by
    intro t; rw [hσ t]
  rw [hfun, hF0]
  congr 1
  rw [precomp_sum_update_comp (fun W : Fin K → Work.Diff.EXT.TField (I := I) (M := M) => T W y)
      (fun i : Fin K => F i.succ) (fun s : Fin K => dirF g (F s.succ) (F (σ 0))) τ hτ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  show T (Function.update (fun i : Fin K => F (τ i).succ) t
      (dirF g (F (τ t).succ) (F (σ 0)))) y
    = T (Function.update (fun i : Fin K => F (σ i.succ)) t
      (dirF g (F (σ t.succ)) (F (σ 0)))) y
  rw [hGtau, hY t]

/-! ## The target -/

/-- **Precomposition of a packed operator with a permutation of its slots.**  The `b`-fold covariant
jet of the operator `S` precomposed with the slot permutation `e` on the tuple `F` equals the
`b`-fold covariant jet of `S` on the tuple `F` with its slots permuted by `slotPerm e b` (the
differentiation directions, the first `b` entries of `F`, are untouched). -/
theorem jetAllPrecomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) {K : ℕ} (e : Fin K ≃ Fin K)
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) :
    ∀ (b : ℕ) (F : Fin (K + b) → Work.Diff.EXT.TField (I := I) (M := M)),
      Work.Diff.EXT.jetAll g b K (fun F' y => S (fun i => F' (e i)) y) F
        = Work.Diff.EXT.jetAll g b K S
            (fun i => F (Work.Diff.EXT.evolX.slotPerm e b i)) := by
  intro b
  induction b with
  | zero =>
    intro F
    show (fun y => S (fun i => F (e i)) y) = S (fun i => F (slotPerm e 0 i))
    funext y
    congr 1
    funext i
    apply congrArg F
    apply Fin.ext
    rw [precomp_slotPerm_val_of_not_lt (b := 0) e (i := i) (by omega)]
    simp
  | succ L ih =>
    intro F
    change Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.jetAll g L K (fun F' y => S (fun i => F' (e i)) y)) F
      = Work.Diff.EXT.extStep (I := I) (M := M) g (Work.Diff.EXT.jetAll g L K S)
          (fun i => F (slotPerm e (L + 1) i))
    rw [show Work.Diff.EXT.jetAll g L K (fun F' y => S (fun i => F' (e i)) y)
        = (fun (G : Fin (K + L) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
            Work.Diff.EXT.jetAll g L K S (fun i => G (slotPerm e L i)) y) from funext ih]
    exact precomp_extStep_compPerm g (precomp_slotPerm_injective e L)
      (precomp_slotPerm_apply_of_lt e (b := L + 1) (i := (0 : Fin (K + (L+1)))) (by simp))
      (fun i => precomp_slotPerm_succ e L i)

end Work.Diff.EXT.evolX
