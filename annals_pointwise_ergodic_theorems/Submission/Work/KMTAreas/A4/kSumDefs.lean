/-
# The `k`-fold sumset of a finite set of integers

Vocabulary for the amplification step `Work.KMTAreas.A4.invWeylAmplify`
(Green--Tao, *Quadratic uniformity of the Möbius function*, Lemma 3.1(ii)).

`kSum T k` is the `k`-fold sumset `T + T + ⋯ + T` (`k` copies of `T`), with the convention
`kSum T 0 = {0}`.  It is the object on which Green--Tao's amplification argument is run: if
`T ⊆ [-N,N]` is `δ₂`-dense and every `n ∈ T` satisfies `‖β n‖ ≤ δ₁`, then `kSum T k` sits in
`[-kN,kN]`, still has density `≳ δ₂` (the density is *preserved*, not squared), and every one of
its elements satisfies `‖β n‖ ≤ k δ₁`.

The two-set sumset is exposed as `addSet` so that the statements of the lemmas below do not
depend on the `Pointwise` scoped notation for `+` on `Finset`.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Work.KMTAreas.A4

/-- The pointwise sumset of two finite sets of integers: `addSet A B = {a + b | a ∈ A, b ∈ B}`. -/
noncomputable def addSet (A B : Finset ℤ) : Finset ℤ := A + B

theorem mem_addSet {A B : Finset ℤ} {x : ℤ} :
    x ∈ addSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x := Finset.mem_add

theorem addSet_nonempty {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (addSet A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a + b, mem_addSet.mpr ⟨a, ha, b, hb, rfl⟩⟩

/-- The `k`-fold sumset of `T ⊆ ℤ`: `kSum T 0 = {0}` and `kSum T (n+1) = addSet T (kSum T n)`. -/
noncomputable def kSum (T : Finset ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | (n + 1) => addSet T (kSum T n)

@[simp] theorem kSum_zero (T : Finset ℤ) : kSum T 0 = {0} := rfl

theorem kSum_succ (T : Finset ℤ) (n : ℕ) : kSum T (n + 1) = addSet T (kSum T n) := rfl

theorem kSum_nonempty (T : Finset ℤ) (hT : T.Nonempty) : ∀ k, (kSum T k).Nonempty := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ n ih => exact addSet_nonempty hT ih

end Work.KMTAreas.A4
