import Mathlib

namespace Work.MainP

theorem crtBijection {S : ℕ} {lab : List ℕ}
    (hinj : ∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j)
    (hlt : ∀ i < S, lab.getD i 0 < S) :
    ∃ σ : Equiv.Perm (Fin S), ∀ i : Fin S, (σ i : ℕ) = lab.getD (i : ℕ) 0 := by
  let f : Fin S → Fin S := fun i => ⟨lab.getD (i : ℕ) 0, hlt (i : ℕ) i.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h : lab.getD (i : ℕ) 0 = lab.getD (j : ℕ) 0 := by
      have := congrArg Fin.val hij
      simpa [f] using this
    exact Fin.ext (hinj (i : ℕ) i.isLt (j : ℕ) j.isLt h)
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hf
  refine ⟨Equiv.ofBijective f ⟨hf, hsurj⟩, ?_⟩
  intro i
  simp [Equiv.ofBijective_apply, f]

end Work.MainP
