import Mathlib
import Submission.Subspace.HyperplaneHeight
import Submission.Commons.Logic.Equiv.exists_equiv_zero_one
import Submission.Subspace.ApproxSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Submission.Subspace

variable {n : ℕ}

/-! ## 1. Pigeonhole over the coordinate pairs

The height dichotomy produces, for each hyperplane of a family, a *pair* of coordinates
`(a, j)` with `a ≠ j` for which the "ratio" certificate holds.  The rest of the machinery
(the projective Roth lemma, the non-vanishing lemma) works in the *chart* of a *fixed* pair
`(0, 1)`; this section reduces an arbitrary family of certificates to a fixed pair, losing
only the factor `(n+1)^2`. -/

/-- **Pigeonhole over the coordinate pairs.**  If every element of a finite set satisfies `P`
for some off-diagonal pair of coordinates, then some off-diagonal pair is satisfied by at
least `1/(n+1)^2` of the set. -/
theorem exists_pair_card_le {ι : Type*} [Fintype ι] (hn : 1 ≤ n) (s : Finset ι)
    (P : ι → Fin (n + 1) → Fin (n + 1) → Prop)
    (h : ∀ i ∈ s, ∃ a j, a ≠ j ∧ P i a j) :
    ∃ (a j : Fin (n + 1)) (t : Finset ι), a ≠ j ∧ t ⊆ s ∧ (∀ i ∈ t, P i a j) ∧
      s.card ≤ (n + 1) ^ 2 * t.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h01 : (0 : Fin (n + 1)) ≠ 1 := by
      have h1 : (1 : Fin (n+1)) = ⟨1, by omega⟩ := by
        ext
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1]
      intro h
      exact Nat.zero_ne_one (by simpa using congrArg Fin.val h)
    refine ⟨0, 1, ∅, h01, Finset.empty_subset _, ?_, by simp⟩
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  · have hw : ∀ i : ι, i ∈ s → ∃ p : Fin (n + 1) × Fin (n + 1), p.1 ≠ p.2 ∧ P i p.1 p.2 := by
      intro i hi
      obtain ⟨a, j, haj, hP⟩ := h i hi
      exact ⟨(a, j), haj, hP⟩
    let χ : ι → Fin (n + 1) × Fin (n + 1) :=
      fun i => if hi : i ∈ s then Classical.choose (hw i hi) else (0, 0)
    have hχ : ∀ i ∈ s, (χ i).1 ≠ (χ i).2 ∧ P i (χ i).1 (χ i).2 := by
      intro i hi
      have h1 : χ i = Classical.choose (hw i hi) := dif_pos hi
      rw [h1]
      exact Classical.choose_spec (hw i hi)
    set O : Finset (Fin (n + 1) × Fin (n + 1)) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2) with hO
    have hmap : Set.MapsTo χ (↑s) (↑O) := by
      intro i hi
      simp only [hO, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hχ i hi).1
    have hOne : O.Nonempty := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨χ i, hmap hi⟩
    obtain ⟨p₀, hp₀O, hmax⟩ :=
      Finset.exists_max_image O (fun p => (s.filter (fun i => χ i = p)).card) hOne
    have hp₀ : p₀.1 ≠ p₀.2 := by
      simpa only [hO, Finset.mem_filter, Finset.mem_univ, true_and] using hp₀O
    have hsum : s.card = ∑ p ∈ O, (s.filter (fun i => χ i = p)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    have hbound : s.card ≤ O.card * (s.filter (fun i => χ i = p₀)).card := by
      rw [hsum]
      calc ∑ p ∈ O, (s.filter (fun i => χ i = p)).card
          ≤ ∑ _p ∈ O, (s.filter (fun i => χ i = p₀)).card :=
            Finset.sum_le_sum (fun p hp => hmax p hp)
        _ = O.card * (s.filter (fun i => χ i = p₀)).card := by
            rw [Finset.sum_const, smul_eq_mul]
    have hsub : s.filter (fun i => χ i = p₀) ⊆ s.filter (fun i => P i p₀.1 p₀.2) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, by rw [← hi.2]; exact (hχ i hi.1).2⟩
    have hOcard : O.card ≤ (n + 1) ^ 2 := by
      have h1 : O.card ≤ Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
        Finset.card_le_univ O
      rw [Fintype.card_prod, Fintype.card_fin] at h1
      calc O.card ≤ (n + 1) * (n + 1) := h1
        _ = (n + 1) ^ 2 := (pow_two _).symm
    refine ⟨p₀.1, p₀.2, s.filter (fun i => P i p₀.1 p₀.2), hp₀, Finset.filter_subset _ _,
      fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
    calc s.card ≤ O.card * (s.filter (fun i => χ i = p₀)).card := hbound
      _ ≤ (n + 1) ^ 2 * (s.filter (fun i => P i p₀.1 p₀.2)).card :=
          Nat.mul_le_mul hOcard (Finset.card_le_card hsub)

/-! ## 2. Relabelling the coordinates

Given a permutation `τ` of the coordinates (the new `j`-th coordinate is the old `τ j`-th),
the system `(L, γ)` can be relabelled to `(reindexMatrix L τ, γ)`: under the identification
`x̃ ↦ x̃ ∘ τ.symm` of the new coordinates with the old ones the approximation domains, hence
the approximation spaces, correspond; a normal `b` becomes the normal `b ∘ τ`.  In particular
a ratio certificate for the pair `(τ 0, τ 1)` becomes one for `(0, 1)`. -/

/-- Relabelling the coordinates of the coefficient matrix: the new `j`-th column is the old
`τ j`-th column. -/
def reindexMatrix {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (τ : Fin (n + 1) ≃ Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  L.submatrix id τ

@[simp] lemma reindexMatrix_apply {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (τ : Fin (n + 1) ≃ Fin (n + 1)) (i j : Fin (n + 1)) :
    reindexMatrix L τ i j = L i (τ j) := rfl

/-- The linear equivalence identifying the new coordinates with the old ones:
`x̃ ↦ x̃ ∘ τ.symm`. -/
noncomputable def coordEquiv {n : ℕ} (τ : Fin (n + 1) ≃ Fin (n + 1)) :
    (Fin (n + 1) → ℚ) ≃ₗ[ℚ] (Fin (n + 1) → ℚ) :=
  LinearEquiv.funCongrLeft ℚ ℚ τ.symm

@[simp] lemma coordEquiv_apply {n : ℕ} (τ : Fin (n + 1) ≃ Fin (n + 1)) (x : Fin (n + 1) → ℚ)
    (k : Fin (n + 1)) : coordEquiv τ x k = x (τ.symm k) := by
  simp [coordEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- The approximation domain of the relabelled system is the image of the original one. -/
lemma mem_approxBox_reindex {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ : Fin (n + 1) → ℝ) (Q : ℝ) (τ : Fin (n + 1) ≃ Fin (n + 1)) (y : Fin (n + 1) → ℤ) :
    y ∈ approxBox (reindexMatrix L τ) γ Q ↔ (y ∘ τ.symm) ∈ approxBox L γ Q := by
  have hsum : ∀ i : Fin (n + 1),
      (∑ j, L i j * (((y ∘ τ.symm) j : ℤ) : ℂ)) = ∑ j, L i (τ j) * ((y j : ℤ) : ℂ) := by
    intro i
    rw [← Equiv.sum_comp τ (fun k => L i k * (((y ∘ τ.symm) k : ℤ) : ℂ))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  simp only [approxBox, Set.mem_ofPred_eq, reindexMatrix_apply]
  constructor
  · intro h i
    rw [hsum i]
    exact h i
  · intro h i
    rw [← hsum i]
    exact h i

/-- The approximation space of the relabelled system. -/
lemma approxSpace_reindex {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ : Fin (n + 1) → ℝ) (Q : ℝ) (τ : Fin (n + 1) ≃ Fin (n + 1)) :
    approxSpace (reindexMatrix L τ) γ Q
      = (approxSpace L γ Q).map (coordEquiv τ).symm.toLinearMap := by
  have hcast : ∀ y : Fin (n + 1) → ℤ,
      (coordEquiv τ).symm (intCastVec y) = intCastVec (y ∘ τ) := by
    intro y
    have h2 : (coordEquiv τ) (intCastVec (y ∘ τ)) = intCastVec y := by
      funext k
      simp [coordEquiv_apply, intCastVec, Function.comp_def]
    rw [← h2]
    exact LinearEquiv.symm_apply_apply (coordEquiv τ) (intCastVec (y ∘ τ))
  have hbox : intCastVec '' approxBox (reindexMatrix L τ) γ Q
      = (coordEquiv τ).symm '' (intCastVec '' approxBox L γ Q) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y ∘ τ.symm) ∈ approxBox L γ Q :=
        (mem_approxBox_reindex L γ Q τ y).mp hy
      refine ⟨intCastVec (y ∘ τ.symm), ⟨y ∘ τ.symm, hy', rfl⟩, ?_⟩
      rw [hcast]
      congr 1
      funext k
      simp [Function.comp_def]
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : (y ∘ τ) ∈ approxBox (reindexMatrix L τ) γ Q := by
        refine (mem_approxBox_reindex L γ Q τ (y ∘ τ)).mpr ?_
        have h1 : (y ∘ τ) ∘ τ.symm = y := by funext k; simp [Function.comp_def]
        rw [h1]; exact hy
      exact ⟨y ∘ τ, hy', hcast y⟩
  unfold approxSpace
  rw [hbox, Submodule.map_span]
  rfl

/-- The `ℚ`-dimension is preserved by the relabelling. -/
lemma finrank_approxSpace_reindex {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ : Fin (n + 1) → ℝ) (Q : ℝ) (τ : Fin (n + 1) ≃ Fin (n + 1)) :
    Module.finrank ℚ (approxSpace (reindexMatrix L τ) γ Q)
      = Module.finrank ℚ (approxSpace L γ Q) := by
  rw [approxSpace_reindex, LinearEquiv.finrank_map_eq]

/-- A normal of the original space becomes a normal of the relabelled space. -/
lemma normal_reindex {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (γ : Fin (n + 1) → ℝ) (Q : ℝ) (τ : Fin (n + 1) ≃ Fin (n + 1)) (b : Fin (n + 1) → ℤ)
    (hb : ∀ x : Fin (n + 1) → ℚ,
      x ∈ approxSpace L γ Q ↔ ∑ j, (b j : ℚ) * x j = 0) :
    ∀ x : Fin (n + 1) → ℚ,
      x ∈ approxSpace (reindexMatrix L τ) γ Q ↔ ∑ j, (((b ∘ τ) j : ℤ) : ℚ) * x j = 0 := by
  intro x
  have hmem : x ∈ approxSpace (reindexMatrix L τ) γ Q
      ↔ (coordEquiv τ) x ∈ approxSpace L γ Q := by
    rw [approxSpace_reindex]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
      have h1 : (coordEquiv τ) x = y := by
        rw [← hyx]
        exact LinearEquiv.apply_symm_apply (coordEquiv τ) y
      rwa [h1]
    · intro hx
      exact Submodule.mem_map.mpr
        ⟨(coordEquiv τ) x, hx, LinearEquiv.symm_apply_apply (coordEquiv τ) x⟩
  have hsumid : (∑ j, (b j : ℚ) * ((coordEquiv τ) x) j) = ∑ j, ((b (τ j) : ℤ) : ℚ) * x j := by
    rw [← Equiv.sum_comp τ (fun k => (b k : ℚ) * ((coordEquiv τ) x) k)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [coordEquiv_apply, Equiv.symm_apply_apply]
  rw [hmem, hb ((coordEquiv τ) x), hsumid, Function.comp_def]

/-! ## 3. The pair reduction -/

/-- **Pair reduction.**  From a family of hyperplanes each carrying a ratio certificate for
*some* pair of coordinates, extract a subfamily of density `≥ 1/(n+1)^2` on which a *fixed*
pair works, and relabel the coordinates so that this pair becomes `(0, 1)`. -/
theorem pair_reduction {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (γ : Fin (n + 1) → ℝ) (θ : ℝ)
    {ι : Type*} [Fintype ι] (s : Finset ι) (Q : ι → ℝ) (b : ι → Fin (n + 1) → ℤ)
    (hb : ∀ i ∈ s, b i ≠ 0)
    (hker : ∀ i ∈ s, ∀ x : Fin (n + 1) → ℚ,
      x ∈ approxSpace L γ (Q i) ↔ ∑ j, (b i j : ℚ) * x j = 0)
    (hfr : ∀ i ∈ s, Module.finrank ℚ (approxSpace L γ (Q i)) = n)
    (hcert : ∀ i ∈ s, ∃ a j, a ≠ j ∧ b i a ≠ 0 ∧
      θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ))) :
    ∃ (τ : Fin (n + 1) ≃ Fin (n + 1)) (t : Finset ι), t ⊆ s ∧
      s.card ≤ (n + 1) ^ 2 * t.card ∧
      ∀ i ∈ t, (b i ∘ τ) ≠ 0 ∧ (b i ∘ τ) 0 ≠ 0 ∧
        (∀ x : Fin (n + 1) → ℚ,
          x ∈ approxSpace (reindexMatrix L τ) γ (Q i) ↔
            ∑ j, (((b i ∘ τ) j : ℤ) : ℚ) * x j = 0) ∧
        Module.finrank ℚ (approxSpace (reindexMatrix L τ) γ (Q i)) = n ∧
        θ * Real.log (Q i) ≤
          Height.logHeight₁ (-(((b i ∘ τ) 1 : ℤ) : ℚ) / (((b i ∘ τ) 0 : ℤ) : ℚ)) := by
  classical
  obtain ⟨a, j, t, haj, hts, htP, hcard⟩ := exists_pair_card_le hn s
    (fun i a j => b i a ≠ 0 ∧
      θ * Real.log (Q i) ≤ Height.logHeight₁ (((b i j : ℤ) : ℚ) / ((b i a : ℤ) : ℚ)))
    (fun i hi => hcert i hi)
  obtain ⟨τ, hτ0, hτ1⟩ := Commons.Logic.Equiv.exists_equiv_zero_one haj
  refine ⟨τ, t, hts, hcard, ?_⟩
  intro i hi
  obtain ⟨hba, hle⟩ := htP i hi
  have hone : (b i ∘ τ) 0 = b i a := by rw [Function.comp_apply, hτ0]
  have htwo : (b i ∘ τ) 1 = b i j := by rw [Function.comp_apply, hτ1]
  have hbne : (b i ∘ τ) ≠ 0 := by
    intro h
    apply hb i (hts hi)
    funext k
    have h1 := congrFun h (τ.symm k)
    simpa [Function.comp_def] using h1
  refine ⟨hbne, by rw [hone]; exact hba, normal_reindex L γ (Q i) τ (b i) (hker i (hts hi)),
    by rw [finrank_approxSpace_reindex]; exact hfr i (hts hi), ?_⟩
  rw [hone, htwo]
  refine le_trans hle ?_
  rw [show (-(↑(b i j)) : ℚ) / (↑(b i a)) = -((↑(b i j) : ℚ) / ↑(b i a)) by ring]
  rw [Height.logHeight₁_neg]

end Submission.Subspace

