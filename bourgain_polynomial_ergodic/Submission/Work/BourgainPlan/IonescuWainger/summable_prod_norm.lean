import Mathlib

/-!
# Finite products of summable nonnegative sequences are summable

If `u i : ℤ → ℝ` is summable and nonnegative for every `i : Fin (n + 1)`, then the
pointwise product `m ↦ ∏ i, u i m` is summable.

The key input is that for counting measure `ℓ¹ ⊆ ℓ²`, so a pointwise product of two
summable sequences is summable; here we only need the nonnegative case, where the
domination `f m * g m ≤ (∑' f) * g m` is immediate.
-/

namespace Work.BourgainPlan.IonescuWainger

/-- Pointwise product of two summable nonnegative real sequences on `ℤ` is summable. -/
lemma summable_mul_of_nonneg {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ m, 0 ≤ f m) (hg0 : ∀ m, 0 ≤ g m) : Summable fun m => f m * g m :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (hf0 m) (hg0 m))
    (fun m => mul_le_mul_of_nonneg_right (hf.le_tsum m (fun j _ => hf0 j)) (hg0 m))
    (hg.mul_left (∑' m, f m))

theorem summable_prod_norm {n : ℕ} (u : Fin (n + 1) → ℤ → ℝ) (hu : ∀ i, Summable (u i))
    (hu0 : ∀ i m, 0 ≤ u i m) : Summable fun m => ∏ i, u i m := by
  induction n with
  | zero => simpa using hu 0
  | succ n ih =>
    have h0 : Summable (u 0) := hu 0
    have htail : Summable (fun m => ∏ i : Fin (n + 1), u i.succ m) :=
      ih (fun i => u i.succ) (fun i => hu i.succ) (fun i m => hu0 i.succ m)
    have hg0 : ∀ m, 0 ≤ ∏ i : Fin (n + 1), u i.succ m :=
      fun m => Finset.prod_nonneg (fun i _ => hu0 i.succ m)
    have h := summable_mul_of_nonneg h0 htail (fun m => hu0 0 m) hg0
    simpa [Fin.prod_univ_succ] using h

end Work.BourgainPlan.IonescuWainger
