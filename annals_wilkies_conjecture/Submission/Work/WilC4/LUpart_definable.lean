/-
  WilC4/LUpart_definable : the `LUpart` piece of `Work.WilC4.crit_def_bad`.

  `LUpart Y` is the set of `v = (x, c)` for which there are `ε > 0`, `δ > 0` and a value `y` of
  the fibre of `Y` at `(x,c)` such that *all* values of the fibre on `(x-δ, x)` are at least
  `y + ε`.  The point is that the inner `∀ t, ∀ w` is *guarded*:

    `(∀ t, x-δ < t → t < x → ∀ w, (t,w) ∈ Y → y+ε ≤ w)`
      ⟺ `¬ ∃ t, ∃ w, (x-δ < t ∧ t < x ∧ (t,w) ∈ Y ∧ w < y+ε)`,

  so that the whole definition has the shape `∃(ε,δ,y), O ∧ ∀(t,w) ∉ B` with `O` and `B`
  *first-order* (given by bounded formulas in `LRc`).  `shape_lemma_LU` packages the quantifier
  bookkeeping, `LUO`/`LUB` are the outer and bad sets, and the definability of `O` and `B` is the
  elementary `LRc` bookkeeping of `crit_def_bad_aux`.
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

/-! ## 1. The quantifier shape -/

/-- **Shared quantifier shape.**  If `O ⊆ ℝ^{k+1+3}` and `B ⊆ ℝ^{k+1+3+2}` are `∅`-definable then
the set of `v` for which some `(ε,δ,y)` satisfies `O` and no `(t,w)` satisfies `B` is
`∅`-definable.  The `∀(t,w)` is the complement of the finite existential over `Fin 2`. -/
theorem shape_lemma_LU {O : Set (ρ3 k → ℝ)} {B : Set (ρR k → ℝ)}
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
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨u, hO', hnot⟩
      exact ⟨u, hO', fun u2 hmem => hnot ⟨u2, hmem⟩⟩
    · rintro ⟨u, hO', hnot⟩
      exact ⟨u, hO', fun hcon => by obtain ⟨u2, hu2⟩ := hcon; exact hnot u2 hu2⟩
  rw [hset] at h2
  exact h2

/-! ## 2. The outer and bad sets of `LUpart` -/

/-- The outer conditions of `LUpart` on `(v, ε, δ, y)`: `0 < ε`, `0 < δ` and `(x,y) ∈ Y`. -/
def LUO (Y : Set (Fin (k+2) → ℝ)) : Set (ρ3 k → ℝ) :=
  ({x : ρ3 k → ℝ | 0 < x (Sum.inr 0)} ∩ {x : ρ3 k → ℝ | 0 < x (Sum.inr 1)}) ∩
    GrSub Y e3 v03 y3

/-- The bad conditions of `LUpart` on `(v, ε, δ, y, t, w)`: `t` lies in the left half-interval
`(x-δ, x)`, `(t,w) ∈ Y` and `w < y+ε` (the negation of the required lower bound at `t`). -/
def LUB (Y : Set (Fin (k+2) → ℝ)) : Set (ρR k → ℝ) :=
  (({x : ρR k → ℝ | x v0R < x delR + x tR} ∩ {x : ρR k → ℝ | x tR < x v0R}) ∩
    GrSub Y eR tR wR) ∩ {x : ρR k → ℝ | x wR < x yR + x epsR}

/-- The parameter tail of `Sum.elim v u` read along `e3` is `tup v`. -/
lemma elim_e3_tup_LU {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    (Sum.elim v u) ∘ (e3 ∘ Fin.succ) = tup v := by
  funext j; rfl

/-- The parameter tail of `Sum.elim (Sum.elim v u) u2` read along `eR` is `tup v`. -/
lemma elimR_eR_tup_LU {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} {u2 : Fin 2 → ℝ} :
    (Sum.elim (Sum.elim v u) u2) ∘ (eR ∘ Fin.succ) = tup v := by
  funext j; rfl

/-- On the explicit coordinates `(v, ε, δ, y)`, `LUO` reads off the outer conditions. -/
lemma mem_LUO {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    Sum.elim v u ∈ LUO Y ↔
      (0 < u 0 ∧ 0 < u 1 ∧ Fin.cons (v 0) (Fin.cons (u 2) (tup v)) ∈ Y) := by
  simp only [LUO, GrSub, Set.mem_inter_iff, Set.mem_ofPred_eq,
    elim_e3_tup_LU, Sum.elim_inl, Sum.elim_inr, v03, y3]
  tauto

/-- On the explicit coordinates `(v, ε, δ, y, t, w)`, `LUB` reads off the bad conditions. -/
lemma mem_LUB {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ}
    {u2 : Fin 2 → ℝ} :
    Sum.elim (Sum.elim v u) u2 ∈ LUB Y ↔
      ((v 0 < u 1 + u2 0 ∧ u2 0 < v 0) ∧
        Fin.cons (u2 0) (Fin.cons (u2 1) (tup v)) ∈ Y) ∧ u2 1 < u 2 + u 0 := by
  simp only [LUB, GrSub, Set.mem_inter_iff, Set.mem_ofPred_eq,
    elimR_eR_tup_LU, Sum.elim_inl, Sum.elim_inr, v0R, delR, tR, wR, yR, epsR]

/-! ## 3. The result -/

theorem LUpart_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.LUpart Y) := by
  have hO : (∅ : Set ℝ).Definable LRc (LUO Y) :=
    ((definable_lt_const (ρ := ρ3 k) 0 (Sum.inr 0)).inter
      (definable_lt_const (ρ := ρ3 k) 0 (Sum.inr 1))).inter
      (GrSub_definable hY e3 v03 y3)
  have hB : (∅ : Set ℝ).Definable LRc (LUB Y) :=
    (((definable_lt_add v0R delR tR).inter (real_definable_lt tR v0R)).inter
      (GrSub_definable hY eR tR wR)).inter (definable_lt_add wR yR epsR)
  have h := shape_lemma_LU hO hB
  have hset : {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ LUO Y ∧
        ∀ u2 : Fin 2 → ℝ, Sum.elim (Sum.elim v u) u2 ∉ LUB Y} = LUpart Y := by
    ext v
    simp only [LUpart, Set.mem_ofPred_eq, CGr]
    constructor
    · rintro ⟨u, huO, huB⟩
      rw [mem_LUO] at huO
      refine ⟨u 0, u 1, u 2, huO.1, huO.2.1, huO.2.2, ?_⟩
      intro t hvt htw w hGr
      by_contra hcon
      have hcon' : w < u 2 + u 0 := not_le.mp hcon
      refine huB ![t, w] ?_
      rw [mem_LUB]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have hgain : v 0 < u 1 + t := by linarith
        simpa using hgain
      · simpa using htw
      · simpa using hGr
      · simpa using hcon'
    · rintro ⟨ε, δ, y, h1, h2, h3, h4⟩
      refine ⟨![ε, δ, y], ?_, ?_⟩
      · rw [mem_LUO]
        refine ⟨?_, ?_, ?_⟩
        · simpa using h1
        · simpa using h2
        · simpa using h3
      · intro u2
        rw [mem_LUB]
        rintro ⟨⟨⟨hvt, htw⟩, hGr⟩, hlt⟩
        have hvt' : v 0 < δ + u2 0 := by simpa using hvt
        have hlt' : u2 1 < y + ε := by simpa using hlt
        have h5 := h4 (u2 0) (by linarith) htw (u2 1) hGr
        linarith
  rw [hset] at h
  exact h

end Work.WilC4
