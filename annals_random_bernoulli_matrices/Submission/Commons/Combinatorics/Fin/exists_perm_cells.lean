import Mathlib.Data.Fintype.EquivFin

namespace Commons.Combinatorics.Fin

open Equiv Finset

theorem exists_perm_cells {n m : ℕ} (A B : Fin m → Finset (Fin n))
    (hcard : ∀ i, (A i).card = (B i).card)
    (hcoverA : ∀ x : Fin n, ∃ i : Fin m, x ∈ A i)
    (huniqA : ∀ x : Fin n, ∀ i j : Fin m, x ∈ A i → x ∈ A j → i = j)
    (hcoverB : ∀ x : Fin n, ∃ i : Fin m, x ∈ B i)
    (huniqB : ∀ x : Fin n, ∀ i j : Fin m, x ∈ B i → x ∈ B j → i = j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m, (A i).image (fun x => σ x) = B i := by
  classical
  -- per-index equivalence between the part A i and the part B i
  let φ : ∀ i : Fin m, {x : Fin n // x ∈ A i} ≃ {x : Fin n // x ∈ B i} := fun i =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_coe (A i), Fintype.card_coe (B i)]
      exact hcard i)
  -- a choice of the (unique) part containing each point
  let ind : Fin n → Fin m := fun x => Classical.choose (hcoverA x)
  have hind : ∀ x : Fin n, x ∈ A (ind x) := fun x => Classical.choose_spec (hcoverA x)
  let indB : Fin n → Fin m := fun x => Classical.choose (hcoverB x)
  have hindB : ∀ x : Fin n, x ∈ B (indB x) := fun x => Classical.choose_spec (hcoverB x)
  -- projection from the disjoint union over A-parts
  let projA : (Σ i : Fin m, {x : Fin n // x ∈ A i}) → Fin n := fun p => p.2.1
  have hbijA : Function.Bijective projA := by
    constructor
    · intro p q hpq
      rcases p with ⟨i, a⟩
      rcases q with ⟨j, b⟩
      change a.1 = b.1 at hpq
      have haj : a.1 ∈ A j := by
        rw [hpq]
        exact b.2
      have hij : i = j := huniqA a.1 i j a.2 haj
      subst j
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        exact Subtype.ext hpq
    · intro x
      refine ⟨(⟨ind x, ⟨x, hind x⟩⟩ : Σ i : Fin m, {x : Fin n // x ∈ A i}), ?_⟩
      rfl
  let projB : (Σ i : Fin m, {x : Fin n // x ∈ B i}) → Fin n := fun p => p.2.1
  have hbijB : Function.Bijective projB := by
    constructor
    · intro p q hpq
      rcases p with ⟨i, a⟩
      rcases q with ⟨j, b⟩
      change a.1 = b.1 at hpq
      have haj : a.1 ∈ B j := by
        rw [hpq]
        exact b.2
      have hij : i = j := huniqB a.1 i j a.2 haj
      subst j
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        exact Subtype.ext hpq
    · intro x
      refine ⟨(⟨indB x, ⟨x, hindB x⟩⟩ : Σ i : Fin m, {x : Fin n // x ∈ B i}), ?_⟩
      rfl
  let eA : (Σ i : Fin m, {x : Fin n // x ∈ A i}) ≃ Fin n := Equiv.ofBijective projA hbijA
  let eB : (Σ i : Fin m, {x : Fin n // x ∈ B i}) ≃ Fin n := Equiv.ofBijective projB hbijB
  let ψ : (Σ i : Fin m, {x : Fin n // x ∈ A i}) ≃ (Σ i : Fin m, {x : Fin n // x ∈ B i}) :=
    Equiv.sigmaCongrRight φ
  let σ : Equiv.Perm (Fin n) := (eA.symm).trans (ψ.trans eB)
  have symmA_eq : ∀ {x : Fin n} {i : Fin m} (h : x ∈ A i),
      eA.symm x = (⟨i, ⟨x, h⟩⟩ : Σ i : Fin m, {x : Fin n // x ∈ A i}) := by
    intro x i h
    apply eA.injective
    simp [eA, projA]
  have hσ_eq : ∀ {x : Fin n} {i : Fin m} (h : x ∈ A i), σ x = (φ i ⟨x, h⟩).1 := by
    intro x i h
    unfold σ
    simp [eA, eB, projA, projB, ψ, symmA_eq h]
  refine ⟨σ, ?_⟩
  intro i
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rcases (Finset.mem_image.mp hy) with ⟨x, hxA, hxy⟩
    have hφy : (φ i ⟨x, hxA⟩).1 = y := (hσ_eq hxA).symm.trans hxy
    have hm : (φ i ⟨x, hxA⟩).1 ∈ B i := (φ i ⟨x, hxA⟩).2
    simpa [hφy] using hm
  · intro hyB
    let a : {x : Fin n // x ∈ A i} := (φ i).symm ⟨y, hyB⟩
    have ha_map : (φ i) a = ⟨y, hyB⟩ := by
      simp [a]
    have ha_mem : a.1 ∈ A i := a.2
    have hσa : σ a.1 = y := by
      rw [hσ_eq a.2]
      exact congrArg Subtype.val ha_map
    refine Finset.mem_image.mpr ?_
    exact ⟨a.1, ha_mem, hσa⟩

end Commons.Combinatorics.Fin