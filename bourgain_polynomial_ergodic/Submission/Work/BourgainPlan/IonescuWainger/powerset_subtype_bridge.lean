import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# Bridging `Finset ↥S` and the powerset of `S`

A family of sets `A : Finset ℕ` with `A ⊆ S` is the same thing as a family of subsets of the subtype
`↥S`.  This file records the dictionary (`phiSet S : Finset ↥S → Finset ℕ` and its inverse
`psiSet S`), the transport of the sums occurring in the layer-wise sunflower bound across it, and the
transfer of the Erdős–Rado sunflower hypothesis.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

variable {S : Finset ℕ}

/-- The canonical embedding `↥S ↪ ℕ`. -/
def subEmb (S : Finset ℕ) : ↥S ↪ ℕ := Function.Embedding.subtype (fun x => x ∈ S)

/-- A subset `A` of the subtype `↥S` read off as a subset of `ℕ`. -/
def phiSet (S : Finset ℕ) (A : Finset ↥S) : Finset ℕ := A.map (subEmb S)

/-- The preimage of a finite set of naturals under `↥S ↪ ℕ`. -/
def psiSet (S : Finset ℕ) (T : Finset ℕ) : Finset ↥S :=
  (Finset.univ : Finset ↥S).filter (fun x => (x : ℕ) ∈ T)

lemma phiSet_injective : Function.Injective (phiSet S) := fun a b h => by
  simpa [phiSet, subEmb] using h

/-- `phiSet` as an embedding of `Finset`s. -/
def phiEmb (S : Finset ℕ) : Finset ↥S ↪ Finset ℕ := ⟨phiSet S, phiSet_injective⟩

lemma mem_phiSet (A : Finset ↥S) (x : ↥S) : (x : ℕ) ∈ phiSet S A ↔ x ∈ A := by
  simp [phiSet, subEmb, Finset.mem_map]

lemma mem_psiSet (T : Finset ℕ) (x : ↥S) : x ∈ psiSet S T ↔ (x : ℕ) ∈ T := by
  simp [psiSet]

lemma phiSet_subset (A : Finset ↥S) : phiSet S A ⊆ S := by
  intro y hy
  rw [phiSet, subEmb, Finset.mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  exact x.2

lemma phiSet_card (A : Finset ↥S) : (phiSet S A).card = A.card := by
  simp [phiSet, subEmb]

lemma phiSet_mem_powerset (A : Finset ↥S) : phiSet S A ∈ S.powerset :=
  Finset.mem_powerset.mpr (phiSet_subset A)

lemma psiSet_phiSet (A : Finset ↥S) : psiSet S (phiSet S A) = A := by
  ext x
  rw [mem_psiSet, mem_phiSet]

lemma phiSet_psiSet {T : Finset ℕ} (hT : T ⊆ S) : phiSet S (psiSet S T) = T := by
  ext y
  constructor
  · intro hy
    rw [phiSet, subEmb, Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [mem_psiSet] at hx
  · intro hy
    rw [phiSet, subEmb, Finset.mem_map]
    exact ⟨⟨y, hT hy⟩, by rw [mem_psiSet]; exact hy, rfl⟩

lemma phiSet_disjoint (A B : Finset ↥S) :
    Disjoint A B ↔ Disjoint (phiSet S A) (phiSet S B) := by
  constructor
  · intro h
    rw [Finset.disjoint_left] at h ⊢
    intro x hx hx'
    rw [phiSet, subEmb, Finset.mem_map] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hba⟩ := hx'
    exact h ha (Subtype.ext hba ▸ hb)
  · intro h
    rw [Finset.disjoint_left] at h ⊢
    intro x hx hx'
    exact h (by rw [mem_phiSet]; exact hx) (by rw [mem_phiSet]; exact hx')

lemma phiSet_union (A B : Finset ↥S) : phiSet S (A ∪ B) = phiSet S A ∪ phiSet S B := by
  simp [phiSet, Finset.map_union]

lemma phiSet_univ : phiSet S (Finset.univ : Finset ↥S) = S := by
  rw [phiSet, subEmb, ← Finset.attach_eq_univ, Finset.attach_map_val]

lemma phiSet_sdiff_univ (D B : Finset ↥S) :
    B ⊆ (Finset.univ : Finset ↥S) \ D ↔ phiSet S B ⊆ S \ phiSet S D := by
  rw [Finset.subset_sdiff, Finset.subset_sdiff]
  exact ⟨fun h => ⟨fun y hy => (phiSet_subset B hy), (by
      rw [Finset.disjoint_left] at h ⊢
      intro x hx hx'
      rw [phiSet, subEmb, Finset.mem_map] at hx hx'
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, hba⟩ := hx'
      exact h.2 ha (Subtype.ext hba ▸ hb))⟩,
    fun h => ⟨Finset.subset_univ B, (by
      rw [Finset.disjoint_left] at h ⊢
      intro x hx hx'
      exact h.2 (by rw [mem_phiSet]; exact hx) (by rw [mem_phiSet]; exact hx'))⟩⟩

lemma disjoint_psiSet (D : Finset ↥S) (B' : Finset ℕ) (h : B' ⊆ S \ phiSet S D) :
    Disjoint (psiSet S B') D := by
  rw [Finset.disjoint_left]
  intro x hx hxD
  have h1 : (x : ℕ) ∈ B' := (mem_psiSet B' x).mp hx
  have h2 : (x : ℕ) ∈ phiSet S D := (mem_phiSet D x).mpr hxD
  exact (Finset.mem_sdiff.mp (h h1)).2 h2

lemma card_psiSet (B' : Finset ℕ) (hB : B' ⊆ S) : (psiSet S B').card = B'.card := by
  rw [← phiSet_card (psiSet S B'), phiSet_psiSet hB]

/-! ## Transport of the sums -/

/-- **`piFinset` sums are sums over tuples of subtypes.** -/
lemma sum_piFinset_eq_sum_tuple_subtype {β : Type*} [DecidableEq β] (F : Finset β) {r : ℕ}
    (g : (Fin r → β) → ℝ) :
    (∑ B ∈ Fintype.piFinset (fun _ : Fin r => F), g B)
      = ∑ B : (i : Fin r) → ↥F, g (fun i => (B i).1) := by
  classical
  refine Finset.sum_bij' (fun B hB => fun i => ⟨B i, (Fintype.mem_piFinset.mp hB) i⟩)
    (fun B _ => fun i => (B i).1) ?_ ?_ ?_ ?_ ?_
  · intro B _; exact Finset.mem_univ _
  · intro B _; rw [Fintype.mem_piFinset]; intro i; exact (B i).2
  · intro B hB; funext i; rfl
  · intro B _; funext i; exact Subtype.ext rfl
  · intro B hB; rfl

/-- **Tuples over a filtered subtype against tuples over the subtype with an indicator.** -/
lemma sum_tuple_subtype_ite {β : Type*} [DecidableEq β] (F : Finset β) (p : β → Prop)
    [DecidablePred p] {r : ℕ} (g : (Fin r → β) → ℝ) :
    (∑ B : (i : Fin r) → ↥F, (if (∀ i, p ((B i).1)) then g (fun i => (B i).1) else 0))
      = ∑ B : (i : Fin r) → ↥(F.filter p), g (fun i => (B i).1) := by
  classical
  rw [← sum_piFinset_eq_sum_tuple_subtype F (fun B => if (∀ i, p (B i)) then g B else 0),
    ← sum_piFinset_eq_sum_tuple_subtype (F.filter p) g,
    ← Finset.sum_filter]
  have h : (Fintype.piFinset (fun _ : Fin r => F)).filter (fun B => ∀ i, p (B i))
      = Fintype.piFinset (fun _ : Fin r => F.filter p) := by
    ext B
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [h]

/-- **Tuples over all of `Finset ↥S` against tuples over a `piFinset`.** -/
lemma sum_all_tuples_ite_piFinset {r : ℕ} (F : Finset (Finset ↥S))
    (g : (Fin r → Finset ↥S) → ℝ) :
    (∑ B : Fin r → Finset ↥S, (if (∀ i, B i ∈ F) then g B else 0))
      = ∑ B ∈ Fintype.piFinset (fun _ : Fin r => F), g B := by
  classical
  rw [← Finset.sum_filter]
  have h : (Finset.univ : Finset (Fin r → Finset ↥S)).filter (fun B => ∀ i, B i ∈ F)
      = Fintype.piFinset (fun _ : Fin r => F) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [h]

/-- **Transport of a sum over the powerset of `S` to a sum over the subsets of `↥S`.** -/
lemma sum_powerset_eq_sum_subtype {P : ℕ → Prop} [DecidablePred P] (g : Finset ℕ → ℤ → ℂ)
    (x : ℤ) :
    (∑ A ∈ S.powerset.filter (fun A => P A.card), ‖g A x‖ ^ 2)
      = ∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => P A.card),
          ‖g (phiSet S A) x‖ ^ 2 := by
  classical
  refine Finset.sum_bij' (fun A _ => psiSet S A) (fun T _ => phiSet S T) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_filter] at hA ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [card_psiSet A (Finset.mem_powerset.mp hA.1)]
    exact hA.2
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨phiSet_mem_powerset T, by rw [phiSet_card]; exact hT.2⟩
  · intro A hA
    rw [phiSet_psiSet (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)]
  · intro T _; exact psiSet_phiSet T
  · intro A hA
    rw [phiSet_psiSet (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)]

/-- **Transport of the outer sum over the powerset of `S` to the sum over the subsets of `↥S`.** -/
lemma sum_powerset_filter_eq_sum_subtype {P : ℕ → Prop} [DecidablePred P]
    (F : Finset ↥S → ℝ) :
    (∑ A₀ ∈ S.powerset.filter (fun A => P A.card), F (psiSet S A₀))
      = ∑ A₀ ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => P A.card), F A₀ := by
  classical
  refine Finset.sum_bij' (fun A _ => psiSet S A) (fun T _ => phiSet S T) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_filter] at hA ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [card_psiSet A (Finset.mem_powerset.mp hA.1)]
    exact hA.2
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨phiSet_mem_powerset T, by rw [phiSet_card]; exact hT.2⟩
  · intro A hA
    rw [phiSet_psiSet (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)]
  · intro T _; exact psiSet_phiSet T
  · intro A _; rfl

/-- **The tuples of petals over `(univ \ D).powerset.filter (·.card ≤ m)` correspond, under
`phiSet S`, to the tuples of petals over `(S \ phiSet S D).powerset.filter (·.card ≤ m)`.** -/
lemma sum_tuples_powerset_eq_sum_tuples_powerset (D : Finset ↥S) {m r : ℕ}
    (g : (Fin r → Finset ℕ) → ℝ) :
    (∑ A : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset.filter
          (fun B => B.card ≤ m)),
        g (fun i => phiSet S ((A i).1)))
      = ∑ A : (i : Fin r) → ↥((S \ phiSet S D).powerset.filter (fun B => B.card ≤ m)),
        g (fun i => (A i).1) := by
  classical
  have key : ∀ (A : (i : Fin r) → ↥((S \ phiSet S D).powerset.filter
      (fun B => B.card ≤ m))) (i : Fin r), (A i).1 ⊆ S := fun A i =>
    (Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1).trans Finset.sdiff_subset
  refine Finset.sum_bij'
    (fun A _ => fun i => ⟨phiSet S ((A i).1), Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((phiSet_sdiff_univ D ((A i).1)).mp
        (Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1)),
       by rw [phiSet_card]; exact (Finset.mem_filter.mp (A i).2).2⟩⟩)
    (fun A _ => fun i => ⟨psiSet S ((A i).1), Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _,
        disjoint_psiSet D ((A i).1) (Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1)⟩),
       by rw [card_psiSet ((A i).1) (key A i)]; exact (Finset.mem_filter.mp (A i).2).2⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro A _; exact Finset.mem_univ _
  · intro A _; exact Finset.mem_univ _
  · intro A _; funext i; exact Subtype.ext (psiSet_phiSet ((A i).1))
  · intro A _; funext i; exact Subtype.ext (phiSet_psiSet (key A i))
  · intro A _; rfl

/-- The Erdős–Rado sunflower hypothesis transfers from the subsets of `S` to the subsets of `↥S`. -/
lemma hsun_subtype {k k' r M : ℕ} (hk' : k' ≤ k)
    (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A) :
    ∀ T : Finset (Finset ↥S), (∀ A ∈ T, A.card ≤ k') → M ≤ T.card →
      ∃ A : Fin r → Finset ↥S, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A := by
  classical
  intro T hcard hMT
  have hsub : ∀ b ∈ T.map (phiEmb S), b ⊆ S := by
    intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨a, -, rfl⟩ := hb
    exact phiSet_subset a
  have hcard2 : ∀ b ∈ T.map (phiEmb S), b.card ≤ k := by
    intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨a, ha, hba⟩ := hb
    rw [← hba]
    change (phiSet S a).card ≤ k
    rw [phiSet_card]
    exact le_trans (hcard a ha) hk'
  have hM2 : M ≤ (T.map (phiEmb S)).card := by rw [Finset.card_map]; exact hMT
  obtain ⟨A, hA, hAinj, hAsun⟩ := hsun (T.map (phiEmb S)) hsub hcard2 hM2
  choose C hCT hCA using fun i => (Finset.mem_map.mp (hA i))
  have hCA' : ∀ i, phiSet S (C i) = A i := fun i => hCA i
  refine ⟨C, hCT, ?_, ?_⟩
  · intro i j hij
    exact hAinj (by rw [← hCA' i, ← hCA' j, hij])
  · obtain ⟨K, hKsub, hKdisj⟩ := hAsun
    refine ⟨psiSet S K, ?_, ?_⟩
    · intro i x hx
      have hxK : (x : ℕ) ∈ K := (mem_psiSet K x).mp hx
      rw [← mem_phiSet, hCA' i]
      exact hKsub i hxK
    · intro i j hij
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨hxi1, hxi2⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hxj1, hxj2⟩ := Finset.mem_sdiff.mp hx'
      have hxi : (x : ℕ) ∈ A i \ K := Finset.mem_sdiff.mpr
        ⟨by rw [← hCA' i]; exact (mem_phiSet (C i) x).mpr hxi1,
         fun h => hxi2 ((mem_psiSet K x).mpr h)⟩
      have hxj : (x : ℕ) ∈ A j \ K := Finset.mem_sdiff.mpr
        ⟨by rw [← hCA' j]; exact (mem_phiSet (C j) x).mpr hxj1,
         fun h => hxj2 ((mem_psiSet K x).mpr h)⟩
      exact (Finset.disjoint_left.mp (hKdisj i j hij)) hxi hxj

end Work.BourgainPlan.IonescuWainger
