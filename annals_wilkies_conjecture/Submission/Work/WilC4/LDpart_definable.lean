/-
  WilC4/LDpart_definable : `∅`-definability of the one-sided bad family `LDpart`.

  `LDpart Y` is the set of `v : ℝ^{k+1}` for which there are `ε, δ, y` with `0 < ε`, `0 < δ`,
  `(v 0, y, tup v) ∈ Y` and *every* value `w` of the fibre of `Y` over the parameter `tup v`
  on the left interval `(v 0 - δ, v 0)` satisfies `w + ε ≤ y`.

  This is an instance of the quantifier shape handled by `shape_lemma` in
  `crit_def_bad_aux`: the "outer" set

    `LDpartO Y = GrSub Y e3 v03 y3 ∩ {0 < ε} ∩ {0 < δ}`

  (the substitution of the argument `v 0`, the value `y` and the parameter tail `tup v` into `Y`,
  together with the positivity conditions) and the "bad" set

    `LDpartB Y = GrSub Y eR tR wR ∩ {v0 - δ < t} ∩ {t < v0} ∩ {y < w + ε}`

  (a point `(t,w)` of the fibre above the left interval whose value is *too large*).
  Since the negation of the required universal statement is exactly membership of `(t,w)` in the
  bad set, `LDpart Y` is the set of `v` for which some `(ε,δ,y)` satisfies the outer conditions
  and no `(t,w)` satisfies the bad ones.
-/
import Mathlib
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilC4.CritDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-- The "outer" set of `LDpart`: the substitution of `(v 0, y, tup v)` into `Y`, together with
`0 < ε` and `0 < δ`, over the parameter block `(v, ε, δ, y) = ρ3 k`. -/
private def LDpartO (Y : Set (Fin (k+2) → ℝ)) : Set (ρ3 k → ℝ) :=
  GrSub Y e3 v03 y3 ∩ {p | 0 < p eps3} ∩ {p | 0 < p del3}

/-- The "bad" set of `LDpart`: a point `(t,w)` of the fibre above the left interval
`(v 0 - δ, v 0)` whose value is too large (`y < w + ε`), over the parameter block
`(v, ε, δ, y, t, w) = ρR k`. -/
private def LDpartB (Y : Set (Fin (k+2) → ℝ)) : Set (ρR k → ℝ) :=
  GrSub Y eR tR wR ∩ {g | g v0R < g tR + g delR} ∩ {g | g tR < g v0R} ∩
    {g | g yR < g wR + g epsR}

/-- Membership in `LDpartO`, in the coordinates `(v, ε, δ, y)`. -/
private theorem LDpart_mem_O_iff (Y : Set (Fin (k+2) → ℝ)) (v : Fin (k+1) → ℝ)
    (u : Fin 3 → ℝ) :
    Sum.elim v u ∈ LDpartO Y ↔ 0 < u 0 ∧ 0 < u 1 ∧ CGr Y (tup v) (v 0) (u 2) := by
  simp only [LDpartO, Set.mem_inter_iff, Set.mem_ofPred_eq, GrSub]
  constructor
  · rintro ⟨⟨hg, h1⟩, h2⟩
    have hcomp : (Sum.elim v u) ∘ (e3 ∘ Fin.succ) = tup v := by funext i; rfl
    rw [hcomp] at hg
    exact ⟨h1, h2, hg⟩
  · rintro ⟨h1, h2, h3⟩
    have hcomp : (Sum.elim v u) ∘ (e3 ∘ Fin.succ) = tup v := by funext i; rfl
    exact ⟨⟨by rw [hcomp]; exact h3, h1⟩, h2⟩

/-- Membership in `LDpartO` for the explicit triple `u = (ε,δ,y)`. -/
private theorem LDpart_mem_O_iff' (Y : Set (Fin (k+2) → ℝ)) (v : Fin (k+1) → ℝ)
    (ε δ y : ℝ) :
    Sum.elim v ![ε, δ, y] ∈ LDpartO Y ↔ 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y := by
  rw [LDpart_mem_O_iff]
  refine ⟨fun ⟨h1,h2,h3⟩ => ⟨?_,?_,h3⟩, fun ⟨h1,h2,h3⟩ => ⟨?_,?_,h3⟩⟩
  · simpa using h1
  · simpa using h2
  · simpa using h1
  · simpa using h2

/-- Membership in `LDpartB`, in the coordinates `(v, ε, δ, y, t, w)`. -/
private theorem LDpart_mem_B_iff (Y : Set (Fin (k+2) → ℝ)) (g : ρR k → ℝ) :
    g ∈ LDpartB Y ↔ CGr Y (tup (g ∘ eR)) (g tR) (g wR) ∧
      g v0R < g tR + g delR ∧ g tR < g v0R ∧ g yR < g wR + g epsR := by
  simp only [LDpartB, Set.mem_inter_iff, Set.mem_ofPred_eq, GrSub]
  constructor
  · rintro ⟨⟨⟨hg, h1⟩, h2⟩, h3⟩
    have hcomp : g ∘ (eR ∘ Fin.succ) = tup (g ∘ eR) := by funext i; rfl
    rw [hcomp] at hg
    exact ⟨hg, h1, h2, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hcomp : g ∘ (eR ∘ Fin.succ) = tup (g ∘ eR) := by funext i; rfl
    exact ⟨⟨⟨by rw [hcomp]; exact h1, h2⟩, h3⟩, h4⟩

/-- Membership of `p : ρ3 k → ℝ` in the projection of `LDpartB` to the `ρ3 k`-coordinates: this
is exactly "there is a bad point `(t,w)` for `p`". -/
private theorem LDpart_mem_piB_iff (Y : Set (Fin (k+2) → ℝ)) (p : ρ3 k → ℝ) :
    p ∈ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' LDpartB Y) ↔
      ∃ t w : ℝ, CGr Y (tup (p ∘ e3)) t w ∧ p v03 < t + p del3 ∧ t < p v03 ∧
        p y3 < w + p eps3 := by
  constructor
  · rintro ⟨g, hg, hgp⟩
    rw [LDpart_mem_B_iff] at hg
    obtain ⟨hC, h1, h2, h3⟩ := hg
    have hv0 : g v0R = p v03 := by rw [← hgp]; rfl
    have hdl : g delR = p del3 := by rw [← hgp]; rfl
    have hy : g yR = p y3 := by rw [← hgp]; rfl
    have he : g epsR = p eps3 := by rw [← hgp]; rfl
    have htup : tup (g ∘ eR) = tup (p ∘ e3) := by rw [← hgp]; funext i; rfl
    refine ⟨g tR, g wR, ?_, ?_, ?_, ?_⟩
    · rwa [htup] at hC
    · rw [← hv0, ← hdl]; exact h1
    · rw [← hv0]; exact h2
    · rw [← hy, ← he]; exact h3
  · rintro ⟨t, w, hC, h1, h2, h3⟩
    refine ⟨Sum.elim p ![t, w], ?_, ?_⟩
    · rw [LDpart_mem_B_iff]
      have htup : tup ((Sum.elim p ![t, w]) ∘ eR) = tup (p ∘ e3) := by funext i; rfl
      have ht : (Sum.elim p ![t, w]) tR = t := rfl
      have hw : (Sum.elim p ![t, w]) wR = w := rfl
      have hv0 : (Sum.elim p ![t, w]) v0R = p v03 := rfl
      have hdl : (Sum.elim p ![t, w]) delR = p del3 := rfl
      have hy : (Sum.elim p ![t, w]) yR = p y3 := rfl
      have he : (Sum.elim p ![t, w]) epsR = p eps3 := rfl
      exact ⟨by rw [htup, ht, hw]; exact hC, by rw [hv0, ht, hdl]; exact h1,
        by rw [ht, hv0]; exact h2, by rw [hy, hw, he]; exact h3⟩
    · funext i; rfl

/-- The previous characterization for an explicit triple `(ε,δ,y)`, i.e. with
`p = Sum.elim v ![ε,δ,y]`. -/
private theorem LDpart_mem_piB_iff' (Y : Set (Fin (k+2) → ℝ)) (v : Fin (k+1) → ℝ)
    (ε δ y : ℝ) :
    Sum.elim v ![ε, δ, y] ∈
        ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' LDpartB Y) ↔
      ∃ t w : ℝ, CGr Y (tup v) t w ∧ v 0 < t + δ ∧ t < v 0 ∧ y < w + ε := by
  rw [LDpart_mem_piB_iff]
  have hcomp : (Sum.elim v ![ε, δ, y]) ∘ e3 = v := by funext i; rfl
  refine ⟨fun ⟨t,w,hC,h1,h2,h3⟩ => ⟨t,w,?_,?_,?_,?_⟩,
    fun ⟨t,w,hC,h1,h2,h3⟩ => ⟨t,w,?_,?_,?_,?_⟩⟩
  · rwa [hcomp] at hC
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · rwa [hcomp]
  · simpa using h1
  · simpa using h2
  · simpa using h3

/-- The same characterization for a general triple `u : Fin 3 → ℝ`, stated fully in the
coordinates `(v, u 0, u 1, u 2)`. -/
private theorem LDpart_mem_piB_gen (Y : Set (Fin (k+2) → ℝ)) (v : Fin (k+1) → ℝ)
    (u : Fin 3 → ℝ) :
    Sum.elim v u ∈ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' LDpartB Y) ↔
      ∃ t w : ℝ, CGr Y (tup v) t w ∧ v 0 < t + u 1 ∧ t < v 0 ∧ u 2 < w + u 0 := by
  rw [LDpart_mem_piB_iff]
  have hcomp : (Sum.elim v u) ∘ e3 = v := by funext i; rfl
  refine ⟨fun ⟨t,w,hC,h1,h2,h3⟩ => ⟨t,w,?_,?_,?_,?_⟩,
    fun ⟨t,w,hC,h1,h2,h3⟩ => ⟨t,w,?_,?_,?_,?_⟩⟩
  · rwa [hcomp] at hC
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · rwa [hcomp]
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem LDpart_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.LDpart Y) := by
  have hO : (∅ : Set ℝ).Definable LRc (LDpartO Y) := by
    refine ((GrSub_definable hY e3 v03 y3).inter ?_).inter ?_
    · exact definable_lt_const 0 eps3
    · exact definable_lt_const 0 del3
  have hB : (∅ : Set ℝ).Definable LRc (LDpartB Y) := by
    refine (((GrSub_definable hY eR tR wR).inter (definable_lt_add v0R tR delR)).inter
      (real_definable_lt tR v0R)).inter (definable_lt_add yR wR epsR)
  have hset : LDpart Y = {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ,
      Sum.elim v u ∈ LDpartO Y ∧
      Sum.elim v u ∉ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' LDpartB Y)} := by
    ext v
    simp only [LDpart, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ε, δ, y, hε, hδ, hgr, hbad⟩
      refine ⟨![ε, δ, y], ?_, ?_⟩
      · rw [LDpart_mem_O_iff']; exact ⟨hε, hδ, hgr⟩
      · rw [LDpart_mem_piB_iff']
        rintro ⟨t, w, hC, h1, h2, h3⟩
        exact absurd (hbad t (by linarith) h2 w hC) (by linarith)
    · rintro ⟨u, huO, hunotB⟩
      rw [LDpart_mem_O_iff] at huO
      obtain ⟨h1, h2, h3⟩ := huO
      refine ⟨u 0, u 1, u 2, h1, h2, h3, ?_⟩
      intro t ht1 ht2 w hC
      by_contra hcon
      have hcon' : u 2 < w + u 0 := not_le.mp hcon
      exact hunotB ((LDpart_mem_piB_gen Y v u).mpr ⟨t, w, hC, by linarith, ht2, hcon'⟩)
  rw [hset]
  exact shape_lemma hO hB

end Work.WilC4
