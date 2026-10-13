import Submission.Work.Wilkies.Defs

/-!
# Area D (truncation) — bookkeeping for `Set.alg` and `Set.trans`

This file is the base layer of area D of the wilkies development.  Everything in
`Submission/Work/WilkiesD/` imports it.

The two facts that the truncation argument rests on are

* `X_M ⊆ X  ⇒  X_M.alg ⊆ X.alg` (`alg_mono`, used through `notMem_alg_of_subset`), and
* the resulting transfer of the counting hypothesis `T ⊆ degreeHeightLE X.trans g H`
  to the smaller set `X_M` (`subset_degreeHeightLE_trans`).

`Set.alg` and `Set.trans` themselves are frozen in `Submission/Work/Wilkies/Defs.lean`
(`WilkiesConjecture.Set.alg`, `WilkiesConjecture.Set.trans`); we only add API.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesD
open WilkiesDesign WilkiesConjecture

/-- `Set.alg` is the union of the connected infinite semialgebraic subsets, hence monotone:
a subset relation of ambient sets gives a subset relation of their `alg` parts. -/
theorem alg_mono {n : ℕ} {A B : Set (Fin n → ℝ)} (h : A ⊆ B) : A.alg ⊆ B.alg := by
  intro x hx
  simp only [Set.alg, Set.sSup_eq_sUnion, Set.mem_sUnion] at hx ⊢
  obtain ⟨Y, ⟨hYA, hYsem, hYinf, hYconn⟩, hxY⟩ := hx
  exact ⟨Y, ⟨hYA.trans h, hYsem, hYinf, hYconn⟩, hxY⟩

/-- Contrapostive form of `alg_mono`: a point outside `B.alg` is outside `A.alg` for `A ⊆ B`. -/
theorem notMem_alg_of_subset {n : ℕ} {A B : Set (Fin n → ℝ)} (h : A ⊆ B) {x : Fin n → ℝ}
    (hx : x ∉ B.alg) : x ∉ A.alg := fun hc => hx (alg_mono h hc)

/-- Membership in the union `Set.alg`, unfolded. -/
theorem mem_alg_iff {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ A.alg ↔ ∃ Y : Set (Fin n → ℝ), Y ⊆ A ∧ IsSemialgebraic Y ∧ Y.Infinite ∧
      IsConnected Y ∧ x ∈ Y := by
  simp only [Set.alg, Set.sSup_eq_sUnion, Set.mem_sUnion]
  constructor
  · rintro ⟨Y, ⟨⟨hYA, hYsem, hYinf, hYconn⟩, hxY⟩⟩
    exact ⟨Y, hYA, hYsem, hYinf, hYconn, hxY⟩
  · rintro ⟨Y, hYA, hYsem, hYinf, hYconn, hxY⟩
    exact ⟨Y, ⟨⟨hYA, hYsem, hYinf, hYconn⟩, hxY⟩⟩

/-- `Set.alg` is contained in the original set. -/
theorem alg_subset {n : ℕ} {A : Set (Fin n → ℝ)} : A.alg ⊆ A := by
  intro x hx
  rw [mem_alg_iff] at hx
  exact hx.choose_spec.1 (hx.choose_spec.2.2.2.2)

/-- Every connected infinite semialgebraic set contained in `A` is contained in `A.alg`.
This is the introduction rule for `Set.alg`. -/
theorem subset_alg_of_semialgebraic {n : ℕ} {A V : Set (Fin n → ℝ)} (hVA : V ⊆ A)
    (hV : IsSemialgebraic V) (hinf : V.Infinite) (hconn : IsConnected V) : V ⊆ A.alg := by
  intro x hxV
  rw [mem_alg_iff]
  exact ⟨V, hVA, hV, hinf, hconn, hxV⟩

/-- Membership in `X.trans = X \ X.alg`, unfolded. -/
theorem mem_trans {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ A.trans ↔ x ∈ A ∧ x ∉ A.alg := by
  simp only [Set.trans, Set.mem_sdiff]

/-- `Set.trans` is contained in the original set. -/
theorem trans_subset {n : ℕ} {A : Set (Fin n → ℝ)} : A.trans ⊆ A := by
  intro x hx; rw [mem_trans] at hx; exact hx.1

/-- A point of `A` that is not in `A.alg` lies in `A.trans`. -/
theorem mem_trans_of_notMem_alg {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ A) (h : x ∉ A.alg) : x ∈ A.trans := by
  rw [mem_trans]; exact ⟨hx, h⟩

/-- **Truncation transfer.**  If `X_M ⊆ X` and the finite set `T` consists of points of
`degreeHeightLE X.trans g H` that all also lie in `X_M`, then `T` is contained in
`degreeHeightLE X_M.trans g H` as well.  This is `X_M.alg ⊆ X.alg` in the form the
counting statement of area H consumes. -/
theorem subset_degreeHeightLE_trans {n : ℕ} {X XM : Set (Fin n → ℝ)} {g H : ℕ}
    {T : Finset (Fin n → ℝ)}
    (hsub : XM ⊆ X) (hT : (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X.trans g H)
    (hTM : (↑T : Set (Fin n → ℝ)) ⊆ XM) :
    (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE XM.trans g H := by
  intro x hxT
  have hx := hT hxT
  have hxtrans : x ∈ X.trans := hx.1
  rw [mem_trans] at hxtrans
  refine ⟨?_, hx.2⟩
  rw [mem_trans]
  exact ⟨hTM hxT, notMem_alg_of_subset hsub hxtrans.2⟩

end Work.WilkiesD
