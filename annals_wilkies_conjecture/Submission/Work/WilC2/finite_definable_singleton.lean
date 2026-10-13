/-
  Area C2 (WilC2): `finite_definable_singleton`.

  Every element of a finite `A`-definable set is itself `A`-definable.  The mathematical input is
  the ordered-field fact that the graph of `≤` is `LRc`-definable via `x ≤ y ↔ ∃ z, x + z * z = y`
  (which holds in a model of `TR` because every nonnegative element is a square, `model_exists_sq`).

  With order available the induction is straightforward: the minimum of a nonempty finite
  definable set `E` is definable over the same parameters (`{min E} = {x ∈ E | ∀ y ∈ E, x ≤ y}`),
  and then one removes it and repeats on the finite definable set `E \ {min E}`.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC2.Basic
import Submission.Work.WilC4.sup_exists_dcl

noncomputable section
open Classical

namespace Work.WilC2

open FirstOrder FirstOrder.Language
open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## 1. The order is definable -/

/-- If every nonnegative element of `M` is a square, then the graph of `≤` is `LRc`-definable,
because `x ≤ y ↔ ∃ z, x + z * z = y`. -/
lemma definable_le {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [LRc.Structure M] [ringToLRc.IsExpansionOn M]
    {A : Set M} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    {α : Type*} (i j : α) : A.Definable LRc {v : α → M | v i ≤ v j} := by
  refine Set.Definable.mono ?_ (Set.empty_subset A)
  rw [Set.empty_definable_iff]
  refine ⟨liftR ![i, j] leF, ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_ofPred_eq]
  have hv : (v ∘ ![i, j]) = ![v i, v j] := by
    funext k; fin_cases k <;> rfl
  rw [liftR_realize ![i, j] leF v, hv]
  exact (leF_realize_le hsq (v i) (v j)).symm

/-- **The minimum of an `A`-definable set is definable.**  If `E` is `A`-definable and every
nonnegative element of `M` is a square, then the set `{x ∈ E | ∀ y ∈ E, x ≤ y}` — which is
`{min E}` when `E` is nonempty and `∅` otherwise — is `A`-definable. -/
lemma definable_min_set {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [LRc.Structure M] [ringToLRc.IsExpansionOn M]
    {A E : Set M} (hE : A.Definable₁ LRc E)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    A.Definable₁ LRc {x : M | x ∈ E ∧ ∀ y : M, y ∈ E → x ≤ y} := by
  have hE' : A.Definable LRc {v : Fin 1 → M | v 0 ∈ E} := hE
  -- the `y ∈ E` part on `(Fin 1 ⊕ Fin 1)`-tuples
  have hP : A.Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr (0 : Fin 1)) ∈ E} := by
    have h := hE'.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    convert h using 1
    ext w
    simp [Function.comp_apply]
  -- the `x ≤ y` part
  have hQ : A.Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inl (0 : Fin 1)) ≤ w (Sum.inr (0 : Fin 1))} :=
    definable_le hsq (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1))
  -- `y ∈ E → x ≤ y`
  have hR : A.Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → M |
        w (Sum.inr (0 : Fin 1)) ∈ E → w (Sum.inl (0 : Fin 1)) ≤ w (Sum.inr (0 : Fin 1))} := by
    have h := hP.compl.union hQ
    convert h using 1
    ext w
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
    tauto
  -- universally quantify `y`
  have hR' : A.Definable LRc
      {v : Fin 1 → M | ∀ u : Fin 1 → M, u 0 ∈ E → v 0 ≤ u 0} := by
    have h := hR.forall_of_finite (α := Fin 1) (β := Fin 1)
    convert h using 1
    ext v
    simp only [Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr]
  have h := hE'.inter hR'
  have hset : {v : Fin 1 → M | v 0 ∈ {x : M | x ∈ E ∧ ∀ y : M, y ∈ E → x ≤ y}} =
      {v : Fin 1 → M | v 0 ∈ E} ∩
        {v : Fin 1 → M | ∀ u : Fin 1 → M, u 0 ∈ E → v 0 ≤ u 0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun u hu => h2 (u 0) hu⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy => h2 (fun _ => y) hy⟩
  unfold Set.Definable₁
  rw [hset]
  exact h

/-! ## 2. The theorem -/

theorem finite_definable_singleton
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {A : Set M} {E : Set M}
    (hE : A.Definable₁ WilkiesDesign.CG.LRc E) (hfin : E.Finite) :
    ∀ e ∈ E, A.Definable₁ WilkiesDesign.CG.LRc {e} := by
  classical
  haveI : ringToLRc.IsExpansionOn M := instRingToLRcIsExpansionOn M
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  -- `Definable₁` is closed under set difference
  have hsub : ∀ {s t : Set M}, A.Definable₁ LRc s → A.Definable₁ LRc t →
      A.Definable₁ LRc (s \ t) := by
    intro s t hs ht
    have h : {v : Fin 1 → M | v 0 ∈ s \ t} =
        {v : Fin 1 → M | v 0 ∈ s} \ {v : Fin 1 → M | v 0 ∈ t} := by
      ext v; simp [Set.mem_sdiff]
    unfold Set.Definable₁ at hs ht ⊢
    rw [h]
    exact hs.sdiff ht
  -- main induction on the number of elements
  have key : ∀ s : Finset M, A.Definable₁ LRc ((s : Set M)) →
      ∀ e ∈ s, A.Definable₁ LRc ({e} : Set M) := by
    refine fun s => Finset.eraseInduction
      (p := fun t : Finset M =>
        A.Definable₁ LRc ((t : Set M)) → ∀ e ∈ t, A.Definable₁ LRc ({e} : Set M)) ?_ s
    intro s ih hs e he
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · simp at he
    · have hleast := Finset.isLeast_min' s hne
      have hSm := definable_min_set (A := A) hs hsq
      have hsing : {x : M | x ∈ (s : Set M) ∧ ∀ y : M, y ∈ (s : Set M) → x ≤ y}
          = {s.min' hne} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, hle⟩
          exact le_antisymm (hle _ hleast.1) (hleast.2 hx)
        · rintro rfl
          exact ⟨hleast.1, fun y hy => hleast.2 hy⟩
      have hmin : A.Definable₁ LRc ({s.min' hne} : Set M) := hsing ▸ hSm
      by_cases h : e = s.min' hne
      · subst h; exact hmin
      · have he' : e ∈ s.erase (s.min' hne) := Finset.mem_erase.mpr ⟨h, he⟩
        have ht_def : A.Definable₁ LRc (((s.erase (s.min' hne)) : Finset M) : Set M) := by
          rw [Finset.coe_erase]
          exact hsub hs hmin
        exact ih (s.min' hne) hleast.1 ht_def e he'
  intro e he
  have hE' : A.Definable₁ LRc (((hfin.toFinset) : Finset M) : Set M) := by
    rw [hfin.coe_toFinset]; exact hE
  exact key hfin.toFinset hE' e (Finset.mem_coe.mp (by simpa [hfin.coe_toFinset] using he))

end Work.WilC2
