import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# Tuple bookkeeping for the superorthogonal Khintchine inequality

Tao (arXiv:2008.05066) Theorem `sys-ortho`(i) expands `‖∑_{i∈S} f_i‖^{2r}` into the `r`-fold product
`⟨∑ f, ∑ f⟩^r`, i.e. a sum over tuples `(a_1,b_1,…,a_r,b_r) ∈ S^{2r}`.  The natural Lean index for
such a tuple is a map `q : Fin r → ι × ι`; the associated `2r`-tuple of indices is `tupleOf q`.

The hypothesis of `sys-ortho`(i) concerns exactly those `2r`-tuples that carry a *nonce*, i.e. an
index value occurring exactly once (Tao, Definition `nonceflower`(i)); the tuples surviving the
hypothesis are the *nonce-free* ones, `NonceFreeTuple`.
-/

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The `2r`-tuple of indices associated to a tuple of pairs `q : Fin r → ι × ι`: the first `r`
entries are the first coordinates, the last `r` entries the second coordinates. -/
def tupleOf {ι : Type*} {r : ℕ} (q : Fin r → ι × ι) : Fin r ⊕ Fin r → ι
  | Sum.inl k => (q k).1
  | Sum.inr k => (q k).2

/-- A tuple of pairs is **nonce-free** when the associated `2r`-tuple carries no nonce, i.e. every
index value that occurs occurs at least twice. -/
def NonceFreeTuple {ι : Type*} (r : ℕ) (q : Fin r → ι × ι) : Prop :=
  ¬ HasNonceTuple (tupleOf q)

instance {ι : Type*} [DecidableEq ι] (r : ℕ) : DecidablePred (NonceFreeTuple (ι := ι) r) :=
  fun q => by unfold NonceFreeTuple HasNonceTuple tupleOf; infer_instance

@[simp]
theorem tupleOf_inl {ι : Type*} {r : ℕ} (q : Fin r → ι × ι) (k : Fin r) :
    tupleOf q (Sum.inl k) = (q k).1 := rfl

@[simp]
theorem tupleOf_inr {ι : Type*} {r : ℕ} (q : Fin r → ι × ι) (k : Fin r) :
    tupleOf q (Sum.inr k) = (q k).2 := rfl

theorem nonceFreeTuple_iff {ι : Type*} {r : ℕ} (q : Fin r → ι × ι) :
    NonceFreeTuple r q ↔ ∀ j : Fin r ⊕ Fin r, ∃ k : Fin r ⊕ Fin r, k ≠ j ∧ tupleOf q k = tupleOf q j := by
  simp only [NonceFreeTuple, HasNonceTuple, not_exists, not_forall, not_not, exists_prop]

end Work.BourgainPlan.IonescuWainger
