import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

/-- A product over a nonempty index type with an empty or infinite fibre has `Nat.card` zero. -/
theorem natCard_pi_eq_zero_of_exists_eq_zero {ι : Type} (Z : ι → Type)
    (h : ∃ i, Nat.card (Z i) = 0) : Nat.card ((i : ι) → Z i) = 0 := by
  classical
  rw [Nat.card_eq_zero]
  by_cases hempty : ∃ j, IsEmpty (Z j)
  · exact Or.inl ⟨fun f => hempty.elim fun j hj => hj.false (f j)⟩
  · refine Or.inr ?_
    have hne : ∀ j, Nonempty (Z j) := fun j => not_isEmpty_iff.mp fun hj => hempty ⟨j, hj⟩
    obtain ⟨i, hi⟩ := h
    rw [Nat.card_eq_zero] at hi
    rcases hi with hi | hi
    · exact absurd hi (not_isEmpty_iff.mpr (hne i))
    · haveI := hi
      refine Infinite.of_injective
        (fun z : Z i => Function.update (fun j => Classical.choice (hne j)) i z) ?_
      intro z z' hzz'
      have h1 := congrFun hzz' i
      simpa [Function.update_self] using h1

/-- If every fibre of `Z` is nonempty and only finitely many fibres are not singletons, then the
product is finite and its `Nat.card` is the product of the (finitely many) fibre cardinalities. -/
theorem natCard_pi_eq_prod_of_finite_support {ι : Type} (Z : ι → Type)
    (hZ : ∀ i, Nat.card (Z i) ≠ 0)
    (hS : (setOf (fun i => Nat.card (Z i) ≠ 1)).Finite) :
    Nat.card ((i : ι) → Z i) = ∏ i ∈ hS.toFinset, Nat.card (Z i) := by
  classical
  haveI : Fintype {i // Nat.card (Z i) ≠ 1} := hS.fintype
  haveI hsub : ∀ i : {j // ¬ (Nat.card (Z j) ≠ 1)}, Subsingleton (Z i.1) :=
    fun i => (Nat.card_eq_one_iff_unique.mp (not_not.mp i.2)).1
  haveI hne' : ∀ i : {j // ¬ (Nat.card (Z j) ≠ 1)}, Nonempty (Z i.1) :=
    fun i => (Nat.card_eq_one_iff_unique.mp (not_not.mp i.2)).2
  have hB : Nat.card ((i : {j // ¬ (Nat.card (Z j) ≠ 1)}) → Z i.1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  calc Nat.card ((i : ι) → Z i)
      = Nat.card (((i : {j // Nat.card (Z j) ≠ 1}) → Z i.1) ×
          ((i : {j // ¬ (Nat.card (Z j) ≠ 1)}) → Z i.1)) :=
        Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun j => Nat.card (Z j) ≠ 1) Z)
    _ = Nat.card ((i : {j // Nat.card (Z j) ≠ 1}) → Z i.1) *
        Nat.card ((i : {j // ¬ (Nat.card (Z j) ≠ 1)}) → Z i.1) := Nat.card_prod _ _
    _ = (∏ i : {j // Nat.card (Z j) ≠ 1}, Nat.card (Z i.1)) * 1 := by rw [Nat.card_pi, hB]
    _ = ∏ i ∈ hS.toFinset, Nat.card (Z i) := by
        rw [mul_one]
        exact (Finset.prod_subtype (p := fun i => Nat.card (Z i) ≠ 1) hS.toFinset
          (fun x => Set.Finite.mem_toFinset hS) (fun i => Nat.card (Z i))).symm

/-- If every fibre of `Z` is nonempty and infinitely many fibres are not singletons, then the
product is infinite, so its `Nat.card` is zero. -/
theorem natCard_pi_eq_zero_of_infinite_support {ι : Type} (Z : ι → Type)
    (hZ : ∀ i, Nat.card (Z i) ≠ 0)
    (hS : ¬ (setOf (fun i => Nat.card (Z i) ≠ 1)).Finite) :
    Nat.card ((i : ι) → Z i) = 0 := by
  classical
  have hne : ∀ i, Nonempty (Z i) := fun i => (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero (hZ i))).1
  haveI hSinf : Infinite {i // Nat.card (Z i) ≠ 1} := (Set.not_finite.mp hS).to_subtype
  have hemb : ∀ i : {i // Nat.card (Z i) ≠ 1}, Fin 2 ↪ Z i.1 := fun i => by
    have h0 : Nat.card (Z i.1) ≠ 0 := hZ i.1
    have h2 : 2 ≤ Nat.card (Z i.1) := by omega
    exact (Fin.castLEEmb h2).trans (Nat.equivFinOfCardPos h0).symm.toEmbedding
  haveI : Infinite ((i : {i // Nat.card (Z i) ≠ 1}) → Fin 2) := inferInstance
  have hΦ : Function.Injective
      (fun (f : (i : {i // Nat.card (Z i) ≠ 1}) → Fin 2) (i : ι) =>
        if h : Nat.card (Z i) ≠ 1 then (hemb ⟨i, h⟩) (f ⟨i, h⟩) else Classical.choice (hne i)) := by
    intro f g hfg
    funext i
    have h1 := congrFun hfg i.1
    dsimp only at h1
    rw [dif_pos i.2, dif_pos i.2] at h1
    exact (hemb ⟨i.1, i.2⟩).injective h1
  exact @Nat.card_eq_zero_of_infinite _ (Infinite.of_injective _ hΦ)

theorem natCard_pi_congr {ι : Type} (X Y : ι → Type)
    (h : ∀ i, Nat.card (X i) = Nat.card (Y i)) :
    Nat.card ((i : ι) → X i) = Nat.card ((i : ι) → Y i) := by
  classical
  by_cases hz : ∃ i, Nat.card (X i) = 0
  · have hzY : ∃ i, Nat.card (Y i) = 0 := by
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, by rw [← h i]; exact hi⟩
    rw [natCard_pi_eq_zero_of_exists_eq_zero X hz,
        natCard_pi_eq_zero_of_exists_eq_zero Y hzY]
  · push_neg at hz
    have hzY : ∀ i, Nat.card (Y i) ≠ 0 := fun i => by rw [← h i]; exact hz i
    have hS : setOf (fun i => Nat.card (X i) ≠ 1) = setOf (fun i => Nat.card (Y i) ≠ 1) := by
      ext i
      exact iff_of_eq (congrArg (fun n : ℕ => n ≠ 1) (h i))
    by_cases hfin : (setOf (fun i => Nat.card (X i) ≠ 1)).Finite
    · have hfinY : (setOf (fun i => Nat.card (Y i) ≠ 1)).Finite := hS ▸ hfin
      rw [natCard_pi_eq_prod_of_finite_support X hz hfin,
          natCard_pi_eq_prod_of_finite_support Y hzY hfinY]
      have hfs : hfinY.toFinset = hfin.toFinset := by
        ext i
        rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
        exact (iff_of_eq (congrFun hS i)).symm
      rw [hfs]
      exact Finset.prod_congr rfl (fun i _ => h i)
    · have hfinY : ¬ (setOf (fun i => Nat.card (Y i) ≠ 1)).Finite := hS ▸ hfin
      rw [natCard_pi_eq_zero_of_infinite_support X hz hfin,
          natCard_pi_eq_zero_of_infinite_support Y hzY hfinY]

end NK.GlobalCFTdeep.Herbrand
