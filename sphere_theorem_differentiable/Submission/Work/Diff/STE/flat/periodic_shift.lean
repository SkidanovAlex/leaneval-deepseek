import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Invariance of the iterated derivatives of a `1`-periodic function under integer translations

If `N : (Fin n → ℝ) × W → G` is `1`-periodic in the first (Euclidean) variable, then `N` is
invariant under translation of that variable by an integer vector.  Since the translation
`z ↦ z + (v, 0)` is an isometry with derivative the identity, the iterated Fréchet derivatives of
`N` at `(x + v, w)` and at `(x, w)` agree.

The main statement is `Work.Diff.STE.flat.periodic_shift`.
-/

namespace Work.Diff.STE.flat

/-- A `1`-periodic function is invariant under translation by any integer multiple of a
coordinate unit vector. -/
private lemma periodic1_zsmul_single_int {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (i : Fin n) (m : ℤ) (x : Fin n → ℝ) :
    f (x + m • Pi.single i (1:ℝ)) = f x :=
  (show Function.Periodic f (Pi.single i (1:ℝ)) from hf i).zsmul m x

/-- A `1`-periodic function is invariant under translation by an arbitrary integer vector. -/
private lemma periodic1_add_intVec {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (c : Fin n → ℤ) (x : Fin n → ℝ) :
    f (x + (fun i => (c i : ℝ))) = f x := by
  have hsum : (∑ i, (c i) • Pi.single i (1:ℝ)) = (fun i => (c i : ℝ)) := by
    funext j
    simp only [Finset.sum_apply, zsmul_eq_mul]
    simp [Pi.single_apply, Finset.sum_ite_eq]
  have key : ∀ s : Finset (Fin n), ∀ y : Fin n → ℝ,
      f (y + (∑ i ∈ s, (c i) • Pi.single i (1:ℝ))) = f y := by
    intro s
    induction s using Finset.induction with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      have hsplit : y + ∑ i ∈ insert a s, (c i) • Pi.single i (1:ℝ)
          = (y + ∑ i ∈ s, (c i) • Pi.single i (1:ℝ)) + (c a) • Pi.single a (1:ℝ) := by
        rw [Finset.sum_insert ha]; abel
      rw [hsplit, periodic1_zsmul_single_int hf a (c a) (y + _)]
      exact ih y
  have hh := key Finset.univ x
  rw [hsum] at hh
  exact hh

theorem periodic_shift {n : ℕ} {W G : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (N : (Fin n → ℝ) × W → G)
    (hper : ∀ w : W, Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => N (x, w)))
    (k : Fin n → ℤ) (w : W) (j : ℕ) (x : Fin n → ℝ) :
    iteratedFDeriv ℝ j N (x + (fun i => (k i : ℝ)), w)
      = iteratedFDeriv ℝ j N (x, w) := by
  set a : (Fin n → ℝ) × W := ((fun i => (k i : ℝ)), 0) with ha
  -- `N` is invariant under the translation `z ↦ z + a`
  have hfun : (fun z : (Fin n → ℝ) × W => N (z + a)) = N := by
    funext z
    obtain ⟨z₁, z₂⟩ := z
    simpa [a] using periodic1_add_intVec (hper z₂) k z₁
  -- the iterated derivative commutes with translation, and the derivative of a translation is the
  -- identity, so the iterated derivative is simply evaluated at the translated point
  have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := N) j a (x, w)
  rw [hfun] at hshift
  have hpt : (x, w) + a = (x + (fun i => (k i : ℝ)), w) := by
    ext <;> simp [a]
  rw [hshift, hpt]

end Work.Diff.STE.flat
