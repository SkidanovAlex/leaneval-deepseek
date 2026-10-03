import Mathlib
import Submission.Work.Peluse.SwapC.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

open Work.Peluse

/-!
# Permutation invariance of the multiset box sum

`pbox d q₁ q₂ M S f` is the `2^d`-th power of the multiset box norm along the `d` slots
`q₁ k[M] − q₂ k[M]`.  Permuting the slot index `k ↦ σ k` (and reindexing the two shift tuples and
the sign patterns accordingly) leaves it unchanged.  This is the elementary combinatorial fact
needed to present a concatenation of slots in any order.

The proof is a reindexing at the level of the multiset box sum `mCubeSum`:

* `pboxPermSign σ` is the reindexing of the sign patterns `ω ↦ ω ∘ σ⁻¹` (it preserves `weight`);
* `pboxPermTuple_cornerShift` computes `cornerShift (v ∘ σ) (v' ∘ σ) ω = cornerShift v v' (ω ∘ σ⁻¹)`;
* `pboxPerm_cubeProduct` applies this to the cube product (so the sign pattern may be reindexed);
* `pboxPermTuple d X σ` is the reindexing `h ↦ h ∘ σ⁻¹` of the shift tuples;
* `mCubeSum_perm_slots` puts the two together.
-/

/-- Reindexing of the sign patterns by a permutation of the slots: `ω ↦ ω ∘ σ⁻¹`.  It is a
bijection of `Fin d → Bool` preserving `weight`. -/
def pboxPermSign {d : ℕ} (σ : Equiv.Perm (Fin d)) : (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun ω := fun j => ω (σ.symm j)
  invFun ω := fun j => ω (σ j)
  left_inv ω := by funext j; simp
  right_inv ω := by funext j; simp

/-- Reindexing of the shift tuples by a permutation of the slots: `h ↦ h ∘ σ⁻¹`. -/
def pboxPermTuple (d : ℕ) (X : Type) (σ : Equiv.Perm (Fin d)) :
    (Fin d → X) ≃ (Fin d → X) where
  toFun h := fun j => h (σ.symm j)
  invFun h := fun j => h (σ j)
  left_inv h := by funext j; simp
  right_inv h := by funext j; simp

lemma pboxPermSign_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → Bool) :
    pboxPermSign σ ω = fun j => ω (σ.symm j) := rfl

lemma pboxPermTuple_apply (d : ℕ) (X : Type) (σ : Equiv.Perm (Fin d)) (h : Fin d → X) :
    pboxPermTuple d X σ h = fun j => h (σ.symm j) := rfl

/-- `weight` is invariant under a permutation of the slots. -/
lemma pboxPermSign_weight {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → Bool) :
    weight (fun i => ω (σ i)) = weight ω := by
  rw [Work.Peluse.weight, Work.Peluse.weight]
  refine Finset.card_bij (fun i _ => σ i) (fun i hi => ?_)
    (fun i₁ _ i₂ _ h => σ.injective h) (fun j hj => ?_)
  · simpa using hi
  · exact ⟨σ.symm j, by simpa using hj, by simp⟩

/-- `weight` is preserved by the reindexing `pboxPermSign`. -/
lemma pboxPermSign_weight_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → Bool) :
    weight (pboxPermSign σ ω) = weight ω := by
  rw [pboxPermSign_apply]
  exact pboxPermSign_weight σ.symm ω

/-- `cornerShift` after reindexing the shifts along a permutation of the slots is `cornerShift` of
the reindexed sign pattern. -/
lemma pboxPermTuple_cornerShift {d : ℕ} (σ : Equiv.Perm (Fin d)) (v v' : Fin d → ℤ)
    (ω : Fin d → Bool) :
    cornerShift (fun i => v (σ i)) (fun i => v' (σ i)) ω
      = cornerShift v v' (pboxPermSign σ ω) := by
  rw [pboxPermSign_apply]
  simp only [cornerShift]
  rw [← Equiv.sum_comp σ (fun j => if ω (σ.symm j) then v j else v' j)]
  exact Finset.sum_congr rfl (fun i _ => by rw [Equiv.symm_apply_apply])

/-- **The cube product is invariant under a permutation of the slots.**  Reindexing the sign
patterns by `pboxPermSign σ` (which preserves `weight`) converts the shifts `v ∘ σ`, `v' ∘ σ` back
into `v`, `v'`. -/
lemma pboxPerm_cubeProduct {d : ℕ} (σ : Equiv.Perm (Fin d)) (v v' : Fin d → ℤ)
    (g : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin d → Bool, (star^[weight ω])
        (g (x + cornerShift (fun i => v (σ i)) (fun i => v' (σ i)) ω)))
      = ∏ ω : Fin d → Bool, (star^[weight ω]) (g (x + cornerShift v v' ω)) := by
  rw [← Equiv.prod_comp (pboxPermSign σ)
        (fun ω : Fin d → Bool => (star^[weight ω]) (g (x + cornerShift v v' ω)))]
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  rw [pboxPermTuple_cornerShift, pboxPermSign_weight_apply]

/-- Reindexing a double sum over shift tuples by `h ↦ h ∘ σ⁻¹`. -/
lemma pboxPerm_sum_sum {X : Type} [Fintype X] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (B : (Fin d → X) → (Fin d → X) → ℂ) :
    (∑ h : Fin d → X, ∑ h' : Fin d → X, B (pboxPermTuple d X σ h) (pboxPermTuple d X σ h'))
      = ∑ h : Fin d → X, ∑ h' : Fin d → X, B h h' := by
  rw [Equiv.sum_comp (pboxPermTuple d X σ)
    (fun k => ∑ h' : Fin d → X, B k (pboxPermTuple d X σ h'))]
  exact Finset.sum_congr rfl (fun k _ =>
    Equiv.sum_comp (pboxPermTuple d X σ) (fun k' => B k k'))

/-- **Permutation invariance of the multiset box sum.**  Permuting the slot index `k ↦ σ k` in the
direction family `ν` leaves `mCubeSum` unchanged: reindex the two shift tuples by
`H ↦ H ∘ σ⁻¹`, the sign patterns by `ω ↦ ω ∘ σ⁻¹`, and use the identity
`cornerShift (ν k (H k)) (ν k (H' k)) (ω ∘ σ⁻¹) = cornerShift (ν (σ k) (H (σ k))) … ω`. -/
lemma mCubeSum_perm_slots {X : Type} [Fintype X] (d : ℕ) (σ : Equiv.Perm (Fin d))
    (ν : Fin d → X → ℤ) (S : Finset ℤ) (g : ℤ → ℂ) :
    mCubeSum d X (fun k => ν (σ k)) S (fun _ => g) = mCubeSum d X ν S (fun _ => g) := by
  simp only [mCubeSum]
  congr 1
  have key : ∀ h h' : Fin d → X,
      (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (g (x + cornerShift (fun k => ν (σ k) (h k)) (fun k => ν (σ k) (h' k)) ω)))
      = (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (g (x + cornerShift (fun k => ν k ((pboxPermTuple d X σ h) k))
                           (fun k => ν k ((pboxPermTuple d X σ h') k)) ω))) := by
    intro h h'
    have h1 : (fun k => (fun j => ν j ((pboxPermTuple d X σ h) j)) (σ k))
        = fun k => ν (σ k) (h k) := by
      funext k
      rw [pboxPermTuple_apply]
      simp
    have h2 : (fun k => (fun j => ν j ((pboxPermTuple d X σ h') j)) (σ k))
        = fun k => ν (σ k) (h' k) := by
      funext k
      rw [pboxPermTuple_apply]
      simp
    rw [← h1, ← h2]
    exact tsum_congr (fun x => pboxPerm_cubeProduct σ
      (fun j => ν j ((pboxPermTuple d X σ h) j))
      (fun j => ν j ((pboxPermTuple d X σ h') j)) g x)
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => key h h'))]
  exact pboxPerm_sum_sum σ (fun h h' => ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (g (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω)))

/-- **Permutation invariance of the multiset box sum.**  Permuting the slots leaves `pbox`
unchanged: reindex the two shift tuples by `H ↦ H ∘ σ` and the sign pattern by `ω ↦ ω ∘ σ⁻¹`
(which preserves `weight`).  Needed to present the concatenated slots in any order (`concatStep`,
`concatAll`). -/
theorem pbox_perm (d : ℕ) (σ : Equiv.Perm (Fin d)) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    Work.Peluse.LadderP.Swap.pbox d (fun k => q₁ (σ k)) (fun k => q₂ (σ k)) M S f
      = Work.Peluse.LadderP.Swap.pbox d q₁ q₂ M S f := by
  rw [pbox_eq_mCubeSum, pbox_eq_mCubeSum]
  congr 1
  exact mCubeSum_perm_slots d σ (fun k m => Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) m) S f

end Work.Peluse.SwapC
