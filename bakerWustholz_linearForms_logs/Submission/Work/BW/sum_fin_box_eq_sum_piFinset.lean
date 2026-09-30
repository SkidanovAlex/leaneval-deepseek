import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Sums over the box `{t' : Fin q → Fin (N+1) // ∀ m, t' m ≤ t m}` of `Fin (N+1)`-valued
functions can be computed as sums over the corresponding box `Fintype.piFinset (fun m => range (t m + 1))`
of `ℕ`-valued functions, when every `t m ≤ N`.  (The map `t' ↦ (fun m => (t' m : ℕ))` is a bijection
between the two boxes.) -/
theorem sum_fin_box_eq_sum_piFinset {q : ℕ} {M : Type*} [AddCommMonoid M]
    (t : Fin q → ℕ) (N : ℕ) (hN : ∀ m, t m ≤ N) (g : (Fin q → ℕ) → M) :
    (∑ t' ∈ (Finset.univ : Finset (Fin q → Fin (N + 1))).filter
        (fun t' => ∀ m, (t' m : ℕ) ≤ t m), g (fun m => (t' m : ℕ)))
      = ∑ n ∈ Fintype.piFinset (fun m : Fin q => Finset.range (t m + 1)), g n := by
  classical
  refine Finset.sum_bij (fun t' _ => fun m => (t' m : ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    have ha' : ∀ m, (a m : ℕ) ≤ t m := (Finset.mem_filter.mp ha).2
    rw [Fintype.mem_piFinset]
    intro m
    simp only [Finset.mem_range]
    have := ha' m
    omega
  · intro a₁ ha₁ a₂ ha₂ h
    funext m
    apply Fin.ext
    have := congrFun h m
    simpa using this
  · intro b hb
    have hb' : ∀ m, b m ∈ Finset.range (t m + 1) := Fintype.mem_piFinset.mp hb
    refine ⟨fun m => ⟨b m, ?_⟩, ?_, ?_⟩
    · have := hb' m
      simp only [Finset.mem_range] at this
      have := hN m
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro m
      have := hb' m
      simp only [Finset.mem_range] at this
      omega
    · funext m
      simp
  · intro a ha
    rfl

end Work.BW
