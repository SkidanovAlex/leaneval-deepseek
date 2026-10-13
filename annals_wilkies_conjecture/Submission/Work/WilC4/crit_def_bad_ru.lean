/-
  WilC4/crit_def_bad_ru : the `RUpart` piece of `Work.WilC4.crit_def_bad`.

  Everything here is `∅`-definability bookkeeping on top of `crit_def_bad_aux`:
  * `shape_lemma2` is the quantifier shape `∃(ε,δ,y), O ∧ ∀(t,w) ∉ B` in the
    `exists_of_finite`/`forall_of_finite` form (the `∀`-block is encoded by the complement of a
    finite existential);
  * `RUO`/`RUB` are the outer/bad sets for `RUpart`, `mem_RUO`/`mem_RUB` read off their meaning
    on the explicit coordinates;
  * `badRU_part_definable` is the resulting definability of `RUpart`.
-/
import Mathlib
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilC4.CritDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-- **Shared quantifier shape.**  If `O ⊆ ℝ^{k+1+3}` and `B ⊆ ℝ^{k+1+3+2}` are `∅`-definable then
the set of `v` for which some `(ε,δ,y)` satisfies `O` and no `(t,w)` satisfies `B` is
`∅`-definable.  The `∀(t,w)` is the complement of the finite existential over `Fin 2`. -/
theorem shape_lemma2 {O : Set (ρ3 k → ℝ)} {B : Set (ρR k → ℝ)}
    (hO : (∅ : Set ℝ).Definable LRc O) (hB : (∅ : Set ℝ).Definable LRc B) :
    (∅ : Set ℝ).Definable LRc
      {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ O ∧
        ∀ u2 : Fin 2 → ℝ, Sum.elim (Sum.elim v u) u2 ∉ B} := by
  have h1 : (∅ : Set ℝ).Definable LRc
      (O ∩ ({w : ρ3 k → ℝ | ∃ u2 : Fin 2 → ℝ, Sum.elim w u2 ∈ B})ᶜ) :=
    hO.inter (hB.exists_of_finite (α := ρ3 k) (β := Fin 2)).compl
  have h2 := h1.exists_of_finite (α := Fin (k+1)) (β := Fin 3)
  have hset : {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ,
        Sum.elim v u ∈ (O ∩ ({w : ρ3 k → ℝ | ∃ u2 : Fin 2 → ℝ, Sum.elim w u2 ∈ B})ᶜ)}
      = {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ O ∧
          ∀ u2 : Fin 2 → ℝ, Sum.elim (Sum.elim v u) u2 ∉ B} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨u, hO', hnot⟩
      exact ⟨u, hO', fun u2 hmem => hnot ⟨u2, hmem⟩⟩
    · rintro ⟨u, hO', hnot⟩
      exact ⟨u, hO', fun hcon => by obtain ⟨u2, hu2⟩ := hcon; exact hnot u2 hu2⟩
  rw [hset] at h2
  exact h2

/-! ## The outer and bad sets of `RUpart` -/

/-- The outer conditions of `RUpart` on `(v, ε, δ, y)`: `0 < ε`, `0 < δ` and `(x,y) ∈ Y`. -/
def RUO (Y : Set (Fin (k+2) → ℝ)) : Set (ρ3 k → ℝ) :=
  ({x : ρ3 k → ℝ | 0 < x (Sum.inr 0)} ∩ {x : ρ3 k → ℝ | 0 < x (Sum.inr 1)}) ∩
    GrSub Y e3 v03 y3

/-- The bad conditions of `RUpart` on `(v, ε, δ, y, t, w)`. -/
def RUB (Y : Set (Fin (k+2) → ℝ)) : Set (ρR k → ℝ) :=
  (({x : ρR k → ℝ | x v0R < x tR} ∩ {x : ρR k → ℝ | x tR < x v0R + x delR}) ∩
    GrSub Y eR tR wR) ∩ {x : ρR k → ℝ | x wR < x yR + x epsR}

lemma elim_e3_tup {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    (Sum.elim v u) ∘ (e3 ∘ Fin.succ) = tup v := by
  funext j; rfl

lemma elimR_eR_tup {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} {u2 : Fin 2 → ℝ} :
    (Sum.elim (Sum.elim v u) u2) ∘ (eR ∘ Fin.succ) = tup v := by
  funext j; rfl

lemma mem_RUO {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    Sum.elim v u ∈ RUO Y ↔
      (0 < u 0 ∧ 0 < u 1 ∧ Fin.cons (v 0) (Fin.cons (u 2) (tup v)) ∈ Y) := by
  simp only [RUO, GrSub, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq,
    elim_e3_tup, Sum.elim_inl, Sum.elim_inr, v03, y3]
  tauto

lemma mem_RUB {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ}
    {u2 : Fin 2 → ℝ} :
    Sum.elim (Sum.elim v u) u2 ∈ RUB Y ↔
      ((v 0 < u2 0 ∧ u2 0 < v 0 + u 1) ∧
        Fin.cons (u2 0) (Fin.cons (u2 1) (tup v)) ∈ Y) ∧ u2 1 < u 2 + u 0 := by
  simp only [RUB, GrSub, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq,
    elimR_eR_tup, Sum.elim_inl, Sum.elim_inr, v0R, tR, delR, wR, yR, epsR]

/-- `RUpart Y` is `∅`-definable. -/
theorem badRU_part_definable {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (RUpart Y) := by
  have hO : (∅ : Set ℝ).Definable LRc (RUO Y) :=
    ((definable_lt_const (ρ := ρ3 k) 0 (Sum.inr 0)).inter
      (definable_lt_const (ρ := ρ3 k) 0 (Sum.inr 1))).inter
      (GrSub_definable hY e3 v03 y3)
  have hB : (∅ : Set ℝ).Definable LRc (RUB Y) :=
    (((real_definable_lt v0R tR).inter (definable_lt_add tR v0R delR)).inter
      (GrSub_definable hY eR tR wR)).inter (definable_lt_add wR yR epsR)
  have h := shape_lemma2 hO hB
  have hset : {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ RUO Y ∧
        ∀ u2 : Fin 2 → ℝ, Sum.elim (Sum.elim v u) u2 ∉ RUB Y} = RUpart Y := by
    ext v
    simp only [RUpart, Set.mem_setOf_eq, Set.mem_ofPred_eq, CGr]
    constructor
    · rintro ⟨u, huO, huB⟩
      rw [mem_RUO] at huO
      refine ⟨u 0, u 1, u 2, huO.1, huO.2.1, huO.2.2, ?_⟩
      intro t hvt htw w hCGr
      by_contra hcon
      push_neg at hcon
      refine huB ![t, w] ?_
      rw [mem_RUB]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simpa using hvt
      · simpa using htw
      · simpa using hCGr
      · simpa using hcon
    · rintro ⟨ε, δ, y, h1, h2, h3, h4⟩
      refine ⟨![ε, δ, y], ?_, ?_⟩
      · rw [mem_RUO]
        refine ⟨?_, ?_, ?_⟩
        · simpa using h1
        · simpa using h2
        · simpa using h3
      · intro u2
        rw [mem_RUB]
        rintro ⟨⟨⟨hvt, htw⟩, hGr⟩, hlt⟩
        have h5 := h4 (u2 0) hvt htw (u2 1) hGr
        have hlt' : u2 1 < y + ε := by simpa using hlt
        linarith
  rw [hset] at h
  exact h

end Work.WilC4
