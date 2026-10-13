import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.HCF.surj_fiber_card
import Submission.Work.DSM5b.HCF.tupDel_injective_iff_fiber

namespace Work.DSM5b.HCF

/-- **The collision structure of a surjection `Fin (n+2) → Fin (n+1)`.**

A surjection `v : Fin (n+2) → Fin (n+1)` has a unique *collision pair* `i₁ < i₂` with
`v i₁ = v i₂`: the fibres of `v` are `n+1` non-empty subsets of an `n+2`-element set, so exactly
one value is attained twice and all others once (`surj_fiber_card`).  Deleting the `i`-th entry of
`v` therefore yields an injective tuple exactly when `i` is one of the two collision indices
(`tupDel_injective_iff_fiber`). -/
theorem collision_structure {n : ℕ} (v : Fin (n + 2) → Fin (n + 1))
    (hv : Function.Surjective v) :
    ∃ i₁ i₂ : Fin (n + 2), i₁ < i₂ ∧ v i₁ = v i₂ ∧
      ∀ i : Fin (n + 2), Function.Injective (Work.DSM5b.tupDel i v) ↔ (i = i₁ ∨ i = i₂) := by
  classical
  -- `v` is surjective, so exactly one fibre has two elements and all others have one.
  obtain ⟨y₀, hy₀, hy₀'⟩ := Work.DSM5b.HCF.surj_fiber_card v hv
  -- the doubled fibre consists of the two collision indices `a` and `b`
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.mp hy₀
  have memF : ∀ {y : Fin (n + 1)} {x : Fin (n + 2)},
      x ∈ (Finset.univ.filter (fun i : Fin (n + 2) => v i = y)) ↔ v x = y := by
    intro y x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem : ∀ x : Fin (n + 2), v x = y₀ ↔ (x = a ∨ x = b) := by
    intro x
    rw [← memF (y := y₀) (x := x), hF]
    simp
  have hva : v a = y₀ := (hmem a).mpr (Or.inl rfl)
  have hvb : v b = y₀ := (hmem b).mpr (Or.inr rfl)
  -- deleting the `i`-th entry is injective iff `v i` is the doubled value
  have key : ∀ i : Fin (n + 2),
      Function.Injective (Work.DSM5b.tupDel i v) ↔ (i = a ∨ i = b) := by
    intro i
    rw [Work.DSM5b.HCF.tupDel_injective_iff_fiber v hv i]
    constructor
    · intro h
      by_contra hne
      have hne' : v i ≠ y₀ := fun hc => hne ((hmem i).mp hc)
      have h1 := hy₀' (v i) hne'
      rw [h1] at h
      omega
    · intro h
      have h2 : v i = y₀ := (hmem i).mpr h
      rw [h2, hy₀]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact ⟨a, b, hlt, by rw [hva, hvb], key⟩
  · exact absurd heq hab
  · exact ⟨b, a, hgt, by rw [hvb, hva], fun i => by rw [key i]; exact or_comm⟩

end Work.DSM5b.HCF
