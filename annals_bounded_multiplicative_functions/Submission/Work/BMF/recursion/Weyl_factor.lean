import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

open scoped BigOperators

/-!
# Factoring the `m`-fold moment sum into powers of a Weyl sum

This file proves `Work.BMF.recursion.Weyl_factor`: the exponential sum over `s`-tuples of the
moments of the tuple is the `s`-th power of the one-variable Weyl sum.

The two ingredients are

* additivity of the moment vector of a tuple, together with the fact that `UnitAddTorus.mFourier`
  turns sums of exponent vectors into products of characters, and
* the standard product formula `Finset.sum_pow'` for summing a product over all functions
  `Fin m → β`, i.e. `∑_{x ∈ (univ : Fin m → β)} ∏_i f (x i) = (∑_b f b) ^ m`.

We also record two companion facts about the Weyl sums `Weyl` and `WeylMod` from
`Submission.Work.BMF.recursion.Defs`: the partition of `Weyl` into its residue classes modulo `p`
(for `1 ≤ p`), and the description of `WeylMod` as the restricted one-variable sum.
-/

noncomputable section

open Classical

/-- `UnitAddTorus.mFourier` turns a finite sum of exponent vectors into a product of characters:
`mFourier (Σ_{i ∈ s} v i) θ = ∏_{i ∈ s} mFourier (v i) θ`. -/
lemma mFourier_finset_sum {d ι : Type*} [Fintype d] (s : Finset ι) (v : ι → d → ℤ)
    (θ : UnitAddTorus d) :
    UnitAddTorus.mFourier (∑ i ∈ s, v i) θ = ∏ i ∈ s, UnitAddTorus.mFourier (v i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, UnitAddTorus.mFourier_add, ih]

/-- The moment vector of a tuple is the sum of the moment vectors of its entries. -/
lemma powerSums_eq_sum_mom1 {k s X : ℕ} (x : Tup s X) :
    Submission.Vinogradov.powerSums k x = ∑ i : Fin s, mom1 k (x i).1 := by
  funext j
  rw [Finset.sum_apply]
  simp only [Submission.Vinogradov.powerSums, mom1]
  push_cast
  rfl

/-- `Submission.Vinogradov.ExpSum`, evaluated at `θ`, written as the sum over all tuples of the
product of the one-variable characters `mFourier (mom1 k (x i)) θ`. -/
lemma ExpSum_eq_sum_prod_mom1 {k m Q : ℕ} (θ : UnitAddTorus (Fin (k + 1))) :
    Submission.Vinogradov.ExpSum (s := m) (k := k) (X := Q) θ
      = ∑ x : Tup m Q, ∏ i : Fin m, UnitAddTorus.mFourier (mom1 k (x i).1) θ := by
  simp only [Submission.Vinogradov.ExpSum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [powerSums_eq_sum_mom1 x]
  exact mFourier_finset_sum Finset.univ (fun i : Fin m => mom1 k (x i).1) θ

/-- Summing a product over all functions `Fin m → β` factorises:
`∑_{x : Fin m → β} ∏_i f (x i) = (∑_b f b) ^ m`. Restatement of `Finset.sum_pow'`
in terms of `Finset.univ` on a function type. -/
lemma sum_fin_fun_prod {β M : Type*} [Fintype β] [DecidableEq β] [CommSemiring M]
    (f : β → M) (m : ℕ) :
    ∑ x : Fin m → β, ∏ i, f (x i) = (∑ b, f b) ^ m := by
  simpa using (Finset.sum_pow' (Finset.univ : Finset β) f m).symm

private def fin1ArrowEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun a := fun _ => a
  left_inv f := by funext i; fin_cases i; rfl
  right_inv _ := rfl

/-- The Weyl sum as a sum over the one-variable moments indexed by the *type* `Finset.Icc 1 Q`. -/
lemma Weyl_apply (k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    Weyl k Q θ = ∑ a : Finset.Icc 1 Q, UnitAddTorus.mFourier (mom1 k a.1) θ := by
  change Submission.Vinogradov.ExpSum (s := 1) (k := k) (X := Q) θ = _
  simp only [Submission.Vinogradov.ExpSum]
  rw [show (∑ x : Tup 1 Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ)
      = ∑ x : Tup 1 Q, UnitAddTorus.mFourier (mom1 k (x 0).1) θ from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [powerSums_eq_sum_mom1 x, Fin.sum_univ_one]]
  rw [Fintype.sum_equiv (fin1ArrowEquiv (Finset.Icc 1 Q))
        (fun x : Fin 1 → Finset.Icc 1 Q => UnitAddTorus.mFourier (mom1 k (x 0).1) θ)
        (fun a : Finset.Icc 1 Q => UnitAddTorus.mFourier (mom1 k a.1) θ)
        (fun x => rfl)]

/-- The Weyl sum as a sum over the one-variable moments indexed by the *finset* `Finset.Icc 1 Q`. -/
lemma Weyl_apply_finset (k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    Weyl k Q θ = ∑ x ∈ Finset.Icc 1 Q, UnitAddTorus.mFourier (mom1 k x) θ := by
  rw [Weyl_apply]
  exact Finset.sum_attach (Finset.Icc 1 Q) (fun x => UnitAddTorus.mFourier (mom1 k x) θ)

/-- **(B)** `WeylMod p k Q y` is the one-variable Weyl sum restricted to the integers `x ≤ Q`
with `x ≡ y (mod p)`. -/
lemma WeylMod_apply (p k Q y : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    WeylMod p k Q y θ
      = ∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p),
          UnitAddTorus.mFourier (mom1 k x) θ := by
  rw [WeylMod, Finset.sum_apply]

/-- Partition of a sum over `[1,Q]` into the fibres of `x ↦ x % p` (needs `1 ≤ p`). -/
lemma sum_Icc_eq_sum_modFibers {M : Type*} [AddCommMonoid M] {p Q : ℕ} (hp : 1 ≤ p)
    (g : ℕ → M) :
    ∑ x ∈ Finset.Icc 1 Q, g x
      = ∑ y ∈ Finset.range p, ∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p),
          g x := by
  rw [show (∑ y ∈ Finset.range p, ∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p), g x)
      = ∑ y ∈ Finset.range p, ∑ x ∈ Finset.Icc 1 Q,
          (if x % p = y % p then g x else 0) from
    Finset.sum_congr rfl (fun y _ => Finset.sum_filter _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (x % p)]
  · simp
  · intro b hb hne
    rw [Finset.mem_range] at hb
    rw [Nat.mod_eq_of_lt hb, ite_eq_right (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ (by omega))) h

/-- **(A)** The Weyl sum is the sum of its restrictions to the residue classes modulo `p`
(for `1 ≤ p`; without this hypothesis every `x` would be missed and the identity fails). -/
lemma Weyl_eq_sum_WeylMod {p k Q : ℕ} (hp : 1 ≤ p) :
    Weyl k Q = ∑ y ∈ Finset.range p, WeylMod p k Q y := by
  funext θ
  rw [Finset.sum_apply, Weyl_apply_finset]
  rw [sum_Icc_eq_sum_modFibers hp (fun x => UnitAddTorus.mFourier (mom1 k x) θ)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [WeylMod_apply]

/-- **The `m`-fold moment sum is the `m`-th power of the Weyl sum.**
`Submission.Vinogradov.ExpSum (s := m) (k := k) (X := Q)` is `θ ↦ Σ_{x ∈ [1,Q]^m} e(θ·moments(x))`,
and the moment vector is additive over the components of the tuple, so the sum factorises as the
`m`-th power of the one-variable sum `Weyl k Q = Σ_{1 ≤ x ≤ Q} e(θ·(1,x,…,x^k))`
(`Submission.Work.BMF.recursion.Defs`).  Proof by induction on `m`, using
`UnitAddTorus.mFourier_add` (checked: `mFourier (m+n) x = mFourier m x * mFourier n x`) and
`Finset.sum_product`/`Fin.sum_univ_succ`.  `^` on functions is the pointwise Pi power.

This is the elementary factorisation used to rewrite `∫ ‖ExpSum (s := m)‖²` as `∫ ‖Weyl‖^{2m}`.
Two companion facts should be proved in the same file as helper lemmas:
(A) for `1 ≤ p`, the partition `Weyl k Q = ∑ y ∈ Finset.range p, WeylMod p k Q y` (every `x ∈ [1,Q]`
lies in exactly one class `x % p < p`; without `1 ≤ p` this is false);
(B) for `1 ≤ p`, `WeylMod p k Q y = ∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p),
e(θ·mom1 k x)`, where `mom1` is defined in `Defs.lean`. -/
theorem Weyl_factor (k m Q : ℕ) :
    Submission.Vinogradov.ExpSum (s := m) (k := k) (X := Q) = (Weyl k Q) ^ m := by
  funext θ
  rw [Pi.pow_apply]
  rw [ExpSum_eq_sum_prod_mom1 (k := k) (m := m) (Q := Q) θ]
  rw [sum_fin_fun_prod (fun a : Finset.Icc 1 Q => UnitAddTorus.mFourier (mom1 k a.1) θ) m]
  rw [Weyl_apply]

end

end Work.BMF.recursion
