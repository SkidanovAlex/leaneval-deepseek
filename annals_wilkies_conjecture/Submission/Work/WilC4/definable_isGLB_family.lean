/-
  WilC4/definable_isGLB_family :

      theorem definable_isGLB_family {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
          (hS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc S) :
          (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
            {u : Fin (n + 1) → ℝ |
              IsGLB {t : ℝ | Fin.snoc (Fin.init u) t ∈ S} (u (Fin.last n))}

  If `S ⊆ ℝⁿ⁺¹` is `∅`-definable in `LRc`, then so is the set of tuples `u` whose *last*
  coordinate is the infimum of the vertical fibre of `S` over `Fin.init u`.

  `IsGLB A γ` unfolds to `(∀ t ∈ A, γ ≤ t) ∧ ∀ b, ((∀ t ∈ A, b ≤ t) → b ≤ γ)`, so the target
  set is `_{u} (∀t, P(u,t) → γ ≤ t) ∧ (∀b, (∀t, P(u,t) → b ≤ t) → b ≤ γ)`, where
  `P(u,t) := Fin.snoc (Fin.init u) t ∈ S` and `γ := u (Fin.last n)`.

  The proof splits the two conjuncts.

  * The *lower bound* conjunct is `∀t` of a definable condition on `(u,t)`; the definable
    condition is a Boolean combination of `P` (a `Sfib`, a pullback of `S` along the
    `(u,t) ↦ Fin.snoc (Fin.init u) t` reindexing) and the coordinate inequality `γ ≤ t`.
    The `∀t` is the finite universal quantifier of `Definable.forall_of_finite` over the
    index type `Fin 1`.

  * The *greatest lower bound* conjunct is `∀b, (∃t, P(u,t) ∧ t < b) ∨ b ≤ γ`; the inner
    `∃t` is the finite existential quantifier of `Definable.exists_of_finite`, again over
    `Fin 1`, and the outer `∀b` is another finite universal quantifier.

  The two quantified variables `t` and `b` live in `Ix1 = Fin (n+1) ⊕ Fin 1` and
  `Ix2 = (Fin (n+1) ⊕ Fin 1) ⊕ Fin 1`, so that all the quantifiers are over the last summand
  of a sum index type, exactly the shape `Definable.exists_of_finite` / `forall_of_finite`
  require.  This file is self contained: everything it needs is `Set.Definable`'s Boolean
  algebra, `preimage_comp` (for the `Sfib` pullbacks) and the two finite quantifier lemmas,
  plus the `univ`-definability of the order of `ℝ` from `DiagDefs`.
-/
import Mathlib
import Submission.Work.WilC4.DiagDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

namespace Work.WilC4

namespace GLBFam

/-! ## 0. Two logical helpers -/

/-- The `hl`-versus-`Fin 1` bookkeeping: quantifying over `Fin 1 → ℝ` is quantifying over `ℝ`. -/
lemma forall_fin_one_fun {Φ : ℝ → Prop} :
    (∀ t : Fin 1 → ℝ, Φ (t 0)) ↔ (∀ τ : ℝ, Φ τ) :=
  ⟨fun h τ => h (fun _ => τ), fun h t => h (t 0)⟩

/-- `g ∘ Fin.snoc p x` computed coordinatewise. -/
lemma snoc_comp {n : ℕ} {ρ : Type} (g : ρ → ℝ) (p : Fin n → ρ) (x : ρ) :
    g ∘ Fin.snoc p x = Fin.snoc (fun i => g (p i)) (g x) := by
  funext i
  refine Fin.lastCases (by simp) (fun j => by simp) i

/-- `IsGLB` in the "lower bound / least upper bound of lower bounds" form used below. -/
lemma isGLB_iff' {A : Set ℝ} {γ : ℝ} :
    IsGLB A γ ↔ (∀ t, t ∈ A → γ ≤ t) ∧ (∀ b, (∀ t, t ∈ A → b ≤ t) → b ≤ γ) := by
  simp only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_ofPred_eq]

/-! ## 1. The order of `ℝ` is `∅`-definable in `LRc` -/

theorem definable_le_coord {σ : Type} (a c : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g a ≤ g c} := by
  have h := definable_le_LRc (σ := σ) (MvPolynomial.X a) (MvPolynomial.X c)
  rw [definable_univ_iff_empty] at h
  simpa using h

theorem definable_lt_coord {σ : Type} (a c : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g a < g c} := by
  have h := (definable_le_coord (σ := σ) c a).compl
  simpa [Set.compl_ofPred, not_le] using h

/-! ## 2. Index types -/

/-- Index of the pair `(u, t)`: the `Fin (n+1)` block is `u`, the `Fin 1` block is `t`. -/
abbrev Ix1 (n : ℕ) := Fin (n + 1) ⊕ Fin 1

/-- Index of the triple `(u, b, t)`: the first block is `(u, b)`, the last is `t`. -/
abbrev Ix2 (n : ℕ) := (Fin (n + 1) ⊕ Fin 1) ⊕ Fin 1

/-! ## 3. The `S`-fibre condition -/

/-- `Sfib S ρ iu it` is the set of `g : ρ → ℝ` such that the tuple `Fin.snoc (Fin.init (g ∘ iu))
(g (it 0))` lies in `S`: the "graph of the fibre" condition `P`.  It is the pullback of `S`
along `g ↦ g ∘ (iu, it)`. -/
def Sfib {n : ℕ} (S : Set (Fin (n+1) → ℝ)) (ρ : Type) (iu : Fin (n+1) → ρ) (it : Fin 1 → ρ) :
    Set (ρ → ℝ) :=
  {g | Fin.snoc (fun i : Fin n => g (iu (Fin.castSucc i))) (g (it 0)) ∈ S}

theorem Sfib_definable {n : ℕ} (S : Set (Fin (n+1) → ℝ))
    (hS : (∅ : Set ℝ).Definable LRc S)
    (ρ : Type) (iu : Fin (n+1) → ρ) (it : Fin 1 → ρ) :
    (∅ : Set ℝ).Definable LRc (Sfib S ρ iu it) := by
  have h := hS.preimage_comp (Fin.snoc (fun i : Fin n => iu (Fin.castSucc i)) (it 0))
  have heq : Sfib S ρ iu it =
      (fun g : ρ → ℝ => g ∘ Fin.snoc (fun i : Fin n => iu (Fin.castSucc i)) (it 0)) ⁻¹' S := by
    ext g
    simp only [Sfib, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [snoc_comp]
  rw [heq]; exact h

/-! ## 4. The two conjuncts -/

section Main

variable {n : ℕ} (S : Set (Fin (n+1) → ℝ))

/-- The `∀t` condition of the lower bound: `P(u,t) → γ ≤ t`. -/
def C1 : Set (Ix1 n → ℝ) :=
  (Sfib S (Ix1 n) Sum.inl Sum.inr)ᶜ ∪ {g : Ix1 n → ℝ | g (Sum.inl (Fin.last n)) ≤ g (Sum.inr 0)}

/-- The set of those `u` for which `u (Fin.last n)` is a lower bound. -/
def LB : Set (Fin (n+1) → ℝ) := {u | ∀ t : Fin 1 → ℝ, Sum.elim u t ∈ C1 S}

/-- `P` in the `(u, b, t)` context. -/
def A2 : Set (Ix2 n → ℝ) := Sfib S (Ix2 n) (fun i => Sum.inl (Sum.inl i)) Sum.inr

/-- The condition `P(u,t) ∧ t < b` on `(u, b, t)`. -/
def Qset : Set (Ix2 n → ℝ) := A2 S ∩ {g : Ix2 n → ℝ | g (Sum.inr 0) < g (Sum.inl (Sum.inr 0))}

/-- The condition `b ≤ u (Fin.last n)` on `(u, b, t)` (independent of `t`). -/
def Rset : Set (Ix2 n → ℝ) :=
  {g : Ix2 n → ℝ | g (Sum.inl (Sum.inr 0)) ≤ g (Sum.inl (Sum.inl (Fin.last n)))}

/-- The body of the `∃t` quantifier: `Qset ∪ Rset`. -/
def Scond : Set (Ix2 n → ℝ) := Qset S ∪ Rset

/-- The set of `(u,b)` for which `b` is not a lower bound or `b ≤ u (Fin.last n)`: this is
`(∃t, P(u,t) ∧ t < b) ∨ b ≤ u (Fin.last n)`. -/
def UB : Set (Ix1 n → ℝ) := {w | ∃ t : Fin 1 → ℝ, Sum.elim w t ∈ Scond S}

/-- The set of those `u` for which `u (Fin.last n)` is the *greatest* lower bound. -/
def TB : Set (Fin (n+1) → ℝ) := {u | ∀ b : Fin 1 → ℝ, Sum.elim u b ∈ UB S}

/-! ### 4.1 Definability of the two conjuncts -/

theorem C1_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (C1 S) :=
  ((Sfib_definable S hS (Ix1 n) Sum.inl Sum.inr).compl).union (definable_le_coord _ _)

theorem LB_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (LB S) :=
  (C1_definable S hS).forall_of_finite (α := Fin (n+1)) (β := Fin 1)

theorem A2_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (A2 S) :=
  Sfib_definable S hS (Ix2 n) (fun i => Sum.inl (Sum.inl i)) Sum.inr

theorem Qset_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (Qset S) :=
  (A2_definable S hS).inter (definable_lt_coord _ _)

theorem Rset_definable : (∅ : Set ℝ).Definable LRc (Rset (n := n)) := definable_le_coord _ _

theorem Scond_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (Scond S) :=
  (Qset_definable S hS).union Rset_definable

theorem UB_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (UB S) :=
  (Scond_definable S hS).exists_of_finite (α := Ix1 n) (β := Fin 1)

theorem TB_definable (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (TB S) :=
  (UB_definable S hS).forall_of_finite (α := Fin (n+1)) (β := Fin 1)

/-! ### 4.2 Membership descriptions -/

lemma mem_C1 (u : Fin (n+1) → ℝ) (t : Fin 1 → ℝ) :
    Sum.elim u t ∈ C1 S ↔ (Fin.snoc (Fin.init u) (t 0) ∈ S → u (Fin.last n) ≤ t 0) := by
  simp only [C1, Sfib, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
    Sum.elim_inl, Sum.elim_inr, Fin.init]
  tauto

lemma mem_LB (u : Fin (n+1) → ℝ) :
    u ∈ LB S ↔ ∀ τ : ℝ, (Fin.snoc (Fin.init u) τ ∈ S → u (Fin.last n) ≤ τ) := by
  rw [LB]
  simp only [Set.mem_ofPred_eq]
  rw [show (∀ t : Fin 1 → ℝ, Sum.elim u t ∈ C1 S) ↔
    (∀ t : Fin 1 → ℝ, (Fin.snoc (Fin.init u) (t 0) ∈ S → u (Fin.last n) ≤ t 0)) from
    forall_congr' fun t => mem_C1 S u t]
  constructor
  · intro h τ; exact h (fun _ => τ)
  · intro h t; exact h (t 0)

lemma mem_Scond (u : Fin (n+1) → ℝ) (b t : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u b) t ∈ Scond S ↔
      (Fin.snoc (Fin.init u) (t 0) ∈ S ∧ t 0 < b 0) ∨ b 0 ≤ u (Fin.last n) := by
  simp only [Scond, Qset, Rset, A2, Sfib, Set.mem_union, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Fin.init]
  tauto

lemma mem_UB (u : Fin (n+1) → ℝ) (b : Fin 1 → ℝ) :
    Sum.elim u b ∈ UB S ↔
      ((∃ τ : ℝ, Fin.snoc (Fin.init u) τ ∈ S ∧ τ < b 0) ∨ b 0 ≤ u (Fin.last n)) := by
  simp only [UB, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_Scond] at ht
    rcases ht with ⟨h1, h2⟩ | h2
    · exact Or.inl ⟨t 0, h1, h2⟩
    · exact Or.inr h2
  · rintro (⟨τ, h1, h2⟩ | h2)
    · exact ⟨fun _ => τ, by rw [mem_Scond]; exact Or.inl ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, by rw [mem_Scond]; exact Or.inr h2⟩

lemma mem_TB (u : Fin (n+1) → ℝ) :
    u ∈ TB S ↔ ∀ β : ℝ, ((∀ τ : ℝ, Fin.snoc (Fin.init u) τ ∈ S → β ≤ τ) →
      β ≤ u (Fin.last n)) := by
  rw [TB]
  simp only [Set.mem_ofPred_eq]
  rw [show (∀ b : Fin 1 → ℝ, Sum.elim u b ∈ UB S) ↔
    (∀ b : Fin 1 → ℝ,
      ((∃ τ : ℝ, Fin.snoc (Fin.init u) τ ∈ S ∧ τ < b 0) ∨ b 0 ≤ u (Fin.last n))) from
    forall_congr' fun b => mem_UB S u b]
  constructor
  · intro h β
    rcases h (fun _ => β) with ⟨τ, h1, h2⟩ | h2
    · intro hA; exact absurd (hA τ h1) (not_le.mpr h2)
    · intro _; exact h2
  · intro h b
    by_cases hA : ∀ τ : ℝ, Fin.snoc (Fin.init u) τ ∈ S → b 0 ≤ τ
    · exact Or.inr (h (b 0) hA)
    · simp only [not_forall, not_imp, not_le] at hA
      obtain ⟨τ, h1, h2⟩ := hA
      exact Or.inl ⟨τ, h1, h2⟩

/-! ### 4.3 Assembly -/

theorem target_eq :
    {u : Fin (n+1) → ℝ | IsGLB {t : ℝ | Fin.snoc (Fin.init u) t ∈ S} (u (Fin.last n))}
      = LB S ∩ TB S := by
  ext u
  simp only [Set.mem_ofPred_eq]
  rw [Set.mem_inter_iff, mem_LB S u, mem_TB S u, isGLB_iff']
  simp only [Set.mem_ofPred_eq]

end Main

end GLBFam

theorem definable_isGLB_family {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc S) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {u : Fin (n + 1) → ℝ | IsGLB {t : ℝ | Fin.snoc (Fin.init u) t ∈ S} (u (Fin.last n))} := by
  rw [GLBFam.target_eq S]
  exact (GLBFam.LB_definable S hS).inter (GLBFam.TB_definable S hS)

end Work.WilC4
