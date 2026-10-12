import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sectorSliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceF_symm` — the slice of a sector is symmetric in its slots

`Work.BoseBoxFock.sliceF e S Φ y` (`sectorSliceDefs`) is the sector state `slotExact e S Φ` read as
a function of the slots of `S` at the complement configuration `y`, transported to the standard
index type `Fin S.card` along `S.equivFin`.  This module proves that it is **symmetric** in those
slots: any permutation of the `S`-slots (i.e. of `Fin S.card`) leaves the slice unchanged.  This is
the invariance that lets the slice be compared with the model space `Sym^{S.card}(V_ℂ)`
(`complexRealise`).

The proof is in three independent layers.

* **`slotInt_comp_perm`** — the slot projection permutes its slots: for a state `Φ` symmetric under
  all permutations of the slots, projecting the slots of `T` in the permuted configuration `x ∘ τ`
  is the same as projecting the slots of `τ '' T` in the configuration `x`.  This is proved by
  induction on `T` on top of the peel lemma `slotInt_peelMB`
  (`slotInt e (S ∪ {i}) Φ = slotProj1 e i (slotInt e S Φ)`): after peeling the last slot, the
  single-slot projection only involves the *pointwise* identity
  `update (x ∘ τ) a w = (update x (τ a) w) ∘ τ` and the symmetry of `Φ`; no measure theory beyond
  the peel lemma is needed.
* **`slotExact_comp_perm`** — the same for the sector `slotExact e S Φ = Σ_{T ⊇ S} (-1)^{|T|-|S|}
  slotProj e T Φ`: when `τ` preserves `S` setwise, the map `T ↦ τ '' T` permutes the index set
  `{T | S ⊆ T}` (cardinality preserving), so the inclusion–exclusion sum is unchanged.
* **`pairCoord_comp_sliceF`** — the combinatorial identification: composing the `S`-slots with a
  permutation `σ` of `Fin S.card` is the same as composing the whole configuration with the
  permutation `permExtend S β` of `Fin n` that acts as `β = S.equivFin.symm ∘ σ ∘ S.equivFin` on
  `S` and fixes the complement pointwise.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The pointwise identity for `Function.update` -/

/-- Permuting the slots commutes with `Function.update`, up to the permutation. -/
theorem permUpdate_comp {n : ℕ} (τ : Equiv.Perm (Fin n)) (x : Fin n → Ω)
    (a : Fin n) (w : Ω) :
    Function.update (x ∘ τ) a w = (Function.update x (τ a) w) ∘ τ := by
  funext j
  simp only [Function.comp_apply, Function.update_apply]
  by_cases h : j = a
  · simp [h]
  · have hne : τ j ≠ τ a := fun hh => h (τ.injective hh)
    simp [h, hne]

/-! ## 2. The slot projection permutes its slots -/

/-- **The slot projection permutes its slots.**  If `Φ` is symmetric under all slot permutations,
then projecting the slots of `T` in the permuted configuration `x ∘ τ` is the same as projecting
the slots of `τ '' T` in the configuration `x`. -/
theorem slotInt_comp_perm {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (Φ : (Fin n → Ω) → ℂ) (hΦsym : ∀ τ : Equiv.Perm (Fin n), (fun x => Φ (x ∘ τ)) = Φ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    ∀ (T : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (x : Fin n → Ω),
      slotInt e T Φ (x ∘ τ) = slotInt e (T.map τ.toEmbedding) Φ x := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro τ x
    rw [Finset.map_empty, slotInt_empty]
    exact congrFun (hΦsym τ) x
  | insert a s ha ih =>
    intro τ x
    have hins : insert a s = s ∪ {a} := by rw [Finset.insert_eq, Finset.union_comm]
    rw [hins]
    -- peel the slot `a`
    have hpeel : slotInt e (s ∪ {a}) Φ = slotProj1 e a (slotInt e s Φ) :=
      slotInt_peelMB e he hec ha Φ hΦm hΦb
    -- the slot `a` peeled off the permuted set
    have hτa : τ a ∉ s.map τ.toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨b, hb, hba⟩
      exact ha (τ.injective hba ▸ hb)
    have hpeel2 : slotInt e (s.map τ.toEmbedding ∪ {τ a}) Φ
        = slotProj1 e (τ a) (slotInt e (s.map τ.toEmbedding) Φ) :=
      slotInt_peelMB e he hec hτa Φ hΦm hΦb
    have hmap : Finset.map τ.toEmbedding (s ∪ {a}) = s.map τ.toEmbedding ∪ {τ a} := by
      rw [Finset.map_union, Finset.map_singleton, Equiv.toEmbedding_apply]
    rw [hmap, hpeel, hpeel2]
    simp only [slotProj1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.comp_apply, permUpdate_comp τ x a w]
    rw [ih τ (Function.update x (τ a) w)]

/-! ## 3. The sector `slotExact` is invariant under permutations preserving `S` -/

/-- `S ⊆ T` pushes forward along a permutation preserving `S`. -/
theorem subset_map_perm {n : ℕ} {S T : Finset (Fin n)} {τ : Equiv.Perm (Fin n)}
    (hτ : ∀ i, i ∈ S ↔ τ i ∈ S) (h : S ⊆ T) : S ⊆ T.map τ.toEmbedding := by
  intro j hj
  rw [Finset.mem_map]
  exact ⟨τ.symm j, h ((hτ (τ.symm j)).mpr (by simpa using hj)), by simp⟩

theorem map_symm_map_toEmbedding {n : ℕ} (τ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (s.map τ.symm.toEmbedding).map τ.toEmbedding = s := by
  rw [Finset.map_map]
  have h : τ.symm.toEmbedding.trans τ.toEmbedding = Function.Embedding.refl (Fin n) :=
    Function.Embedding.ext (fun x => by simp)
  rw [h, Finset.map_refl]

/-- **The sector is invariant under permutations of the slots preserving `S`.**  For a symmetric
state `Φ` and a permutation `τ` of the slots with `i ∈ S ↔ τ i ∈ S`, the sector `slotExact e S Φ`
is unchanged by precomposing with `τ`. -/
theorem slotExact_comp_perm {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (Φ : (Fin n → Ω) → ℂ) (hΦsym : ∀ τ : Equiv.Perm (Fin n), (fun x => Φ (x ∘ τ)) = Φ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C)
    (S : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (hτ : ∀ i, i ∈ S ↔ τ i ∈ S) :
    (fun x : Fin n → Ω => slotExact e S Φ (x ∘ τ)) = slotExact e S Φ := by
  funext x
  simp only [slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_bij (fun T _ => T.map τ.toEmbedding) ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, subset_map_perm hτ hT.2⟩
  · intro T₁ _ T₂ _ h
    exact Finset.map_inj.mp h
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨b.map τ.symm.toEmbedding, ?_, map_symm_map_toEmbedding τ b⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, subset_map_perm ?_ hb.2⟩
    intro i
    have h := hτ (τ.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  · intro T _
    rw [Finset.card_map]
    simp only [slotProj_eq_slotInt]
    rw [slotInt_comp_perm e he hec Φ hΦsym hΦm hΦb T τ x]

/-! ## 4. Extending a permutation of the `S`-slots to a permutation of all the slots -/

/-- Extend a permutation `β` of the slot set `S` to a permutation of `Fin n` by the identity on
the complement. -/
def permExtend {n : ℕ} (S : Finset (Fin n)) (β : {i // i ∈ S} ≃ {i // i ∈ S}) :
    Equiv.Perm (Fin n) where
  toFun i := if h : i ∈ S then (β ⟨i, h⟩).1 else i
  invFun i := if h : i ∈ S then (β.symm ⟨i, h⟩).1 else i
  left_inv i := by
    by_cases h : i ∈ S
    · have h2 : (β ⟨i, h⟩).1 ∈ S := (β ⟨i, h⟩).2
      simp only [dif_pos h, dif_pos h2]
      have hsub : (⟨(β ⟨i, h⟩).1, h2⟩ : {i // i ∈ S}) = β ⟨i, h⟩ := Subtype.ext rfl
      rw [hsub, Equiv.symm_apply_apply]
    · simp only [dif_neg h]
  right_inv i := by
    by_cases h : i ∈ S
    · have h3 : (β.symm ⟨i, h⟩).1 ∈ S := (β.symm ⟨i, h⟩).2
      simp only [dif_pos h, dif_pos h3]
      have hsub : (⟨(β.symm ⟨i, h⟩).1, h3⟩ : {i // i ∈ S}) = β.symm ⟨i, h⟩ := Subtype.ext rfl
      rw [hsub, Equiv.apply_symm_apply]
    · simp only [dif_neg h]

theorem permExtend_apply {n : ℕ} (S : Finset (Fin n)) (β : {i // i ∈ S} ≃ {i // i ∈ S})
    (i : Fin n) : permExtend S β i = if h : i ∈ S then (β ⟨i, h⟩).1 else i := rfl

/-- `permExtend` preserves `S` setwise. -/
theorem permExtend_mem {n : ℕ} {S : Finset (Fin n)} {β : {i // i ∈ S} ≃ {i // i ∈ S}}
    {i : Fin n} : i ∈ S ↔ permExtend S β i ∈ S := by
  rw [permExtend_apply]
  by_cases h : i ∈ S
  · rw [dif_pos h]
    exact ⟨fun _ => (β ⟨i, h⟩).2, fun _ => h⟩
  · rw [dif_neg h]

/-- **Composing the `S`-slots with a permutation of `Fin S.card` is a slot permutation of the
whole configuration.** -/
theorem pairCoord_comp_sliceF {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin S.card))
    (u : Fin S.card → Ω) (y : {i // i ∉ S} → Ω) :
    pairCoord S (fun i => u (σ (S.equivFin i))) y
      = (pairCoord S (fun i => u (S.equivFin i)) y) ∘
          permExtend S ((S.equivFin.trans σ).trans S.equivFin.symm) := by
  set β : {i // i ∈ S} ≃ {i // i ∈ S} := (S.equivFin.trans σ).trans S.equivFin.symm with hβ
  have hβapply : ∀ j : {i // i ∈ S}, S.equivFin (β j) = σ (S.equivFin j) := by
    intro j
    simp only [hβ, Equiv.trans_apply, Equiv.apply_symm_apply]
  funext j
  rw [Function.comp_apply, permExtend_apply]
  by_cases hj : j ∈ S
  · rw [dif_pos hj, pairCoord_mem S (fun i => u (σ (S.equivFin i))) y j hj,
      pairCoord_mem S (fun i => u (S.equivFin i)) y (β ⟨j, hj⟩).1 (β ⟨j, hj⟩).2]
    exact congrArg u (hβapply ⟨j, hj⟩).symm
  · rw [dif_neg hj, pairCoord_notMem S (fun i => u (σ (S.equivFin i))) y j hj,
      pairCoord_notMem S (fun i => u (S.equivFin i)) y j hj]

/-! ## 5. The target -/

theorem sliceF_symm {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    ∀ σ : Equiv.Perm (Fin S.card),
      (fun u : Fin S.card → EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.sliceF e S Φ y (u ∘ σ)) = Work.BoseBoxFock.sliceF e S Φ y := by
  intro σ
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  funext u
  show slotExact e S Φ (pairCoord S (fun i => u (σ (S.equivFin i))) y)
      = slotExact e S Φ (pairCoord S (fun i => u (S.equivFin i)) y)
  rw [pairCoord_comp_sliceF S σ u y]
  exact congrFun (slotExact_comp_perm e he hec Φ hΦsym hΦm hΦb S _ fun i => permExtend_mem) _

end Work.BoseBoxFock
