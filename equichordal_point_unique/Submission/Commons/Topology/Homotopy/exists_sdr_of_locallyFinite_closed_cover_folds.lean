import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval

namespace Commons.Topology.Homotopy

/-- Gluing lemma: a locally finite closed cover whose members are each folded into `C` (the folds
agreeing on the overlaps because those lie in `C`, where all folds are the identity) assembles
into a strong deformation retraction of the whole space onto `C`. -/
theorem exists_sdr_of_locallyFinite_closed_cover_folds {X : Type*} [TopologicalSpace X]
    {ι : Type*} (K : ι → Set X) (C : Set X)
    (hKc : ∀ i, IsClosed (K i)) (hlf : LocallyFinite K) (hcov : (⋃ i, K i) = Set.univ)
    (hKC : ∀ i j, i ≠ j → K i ∩ K j ⊆ C)
    (hC : @Topology.CWComplex X _ C)
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ C hC n))
    (φ : ∀ i, X × unitInterval → X)
    (hφc : ∀ i, ContinuousOn (φ i) (K i ×ˢ (Set.univ : Set unitInterval)))
    (hφ0 : ∀ i ⦃x : X⦄, x ∈ K i → φ i (x, 0) = x)
    (hφ1 : ∀ i ⦃x : X⦄, x ∈ K i → φ i (x, 1) ∈ K i ∧ φ i (x, 1) ∈ C)
    (hφfix : ∀ i ⦃x : X⦄, x ∈ C → ∀ t : unitInterval, φ i (x, t) = x) :
    ∃ (S : Set X) (hC' : @Topology.CWComplex X _ S),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ S hC' n)) ∧
      ∃ H : X × unitInterval → X, Continuous H ∧ (∀ x : X, H (x, 0) = x) ∧
        (∀ x : X, H (x, 1) ∈ S) ∧ (∀ x : X, x ∈ S → ∀ t : unitInterval, H (x, t) = x) := by
  classical
  -- every point lies in some `K i`
  have hmem : ∀ x : X, ∃ i, x ∈ K i := by
    intro x
    have : x ∈ (⋃ i, K i) := by rw [hcov]; exact Set.mem_univ x
    exact Set.mem_iUnion.mp this
  -- two folds agree wherever both pieces meet
  have hagree : ∀ (p : X × unitInterval) (i j : ι), p.1 ∈ K i → p.1 ∈ K j → φ i p = φ j p := by
    intro p i j hi hj
    by_cases hij : i = j
    · subst hij; rfl
    · have hpC : p.1 ∈ C := hKC i j hij ⟨hi, hj⟩
      have h1 : φ i p = p.1 := hφfix i hpC p.2
      have h2 : φ j p = p.1 := hφfix j hpC p.2
      rw [h1, h2]
  -- the glued map
  let g : X × unitInterval → X := fun p => φ (Classical.choose (hmem p.1)) p
  have hg : ∀ (p : X × unitInterval) (i : ι), p.1 ∈ K i → g p = φ i p :=
    fun p i hi => hagree p (Classical.choose (hmem p.1)) i (Classical.choose_spec (hmem p.1)) hi
  have hcont : Continuous g := by
    have hlf' : LocallyFinite (fun i => K i ×ˢ (Set.univ : Set unitInterval)) :=
      hlf.prod_right (fun _ => Set.univ)
    have hcov' : (⋃ i, K i ×ˢ (Set.univ : Set unitInterval)) = Set.univ := by
      rw [← Set.iUnion_prod_const, hcov, Set.univ_prod_univ]
    refine hlf'.continuous hcov' (fun i => (hKc i).prod isClosed_univ) (fun i => ?_)
    refine (hφc i).congr ?_
    exact fun p hp => hg p i hp.1
  refine ⟨C, hC, hdim, g, hcont, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hmem x
    rw [hg (x, 0) i hi, hφ0 i hi]
  · intro x
    obtain ⟨i, hi⟩ := hmem x
    rw [hg (x, 1) i hi]
    exact (hφ1 i hi).2
  · intro x hx t
    obtain ⟨i, hi⟩ := hmem x
    rw [hg (x, t) i hi]
    exact hφfix i hx t

end Commons.Topology.Homotopy