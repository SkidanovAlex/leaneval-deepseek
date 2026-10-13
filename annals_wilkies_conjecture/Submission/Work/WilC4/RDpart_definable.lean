/-
  WilC4/RDpart_definable : `∅`-definability of the one-sided "bad" family `RDpart`.

  `RDpart Y` (`crit_def_bad_aux`) is: some `(ε, δ, y)` with `0 < ε`, `0 < δ`, `(x,y) ∈ Y` and
  **every** value of the fibre on `(x, x+δ)` at most `y - ε`.  The proof is a direct application
  of the shared quantifier bookkeeping `shape_lemma` (`crit_def_bad_aux` §5), with

  * the outer set `rdp_outer Y ⊆ ℝ^{ρ3}` on the block `(v, ε, δ, y)`: `0 < ε`, `0 < δ` and the
    graph-substitution of `Y` at the argument `v 0`, the value `y` and the parameter tail `tup v`;
  * the bad set `rdp_bad Y ⊆ ℝ^{ρR}` on the block `(v, ε, δ, y, t, w)`: `(t, w)` is a value of the
    fibre at `t`, `t` lies in the interval `(v 0, v 0 + δ)`, and `w + ε ≤ y` **fails**.

  The only work beyond `shape_lemma` is reading the graph-substitutions through `CGr`
  (`grSub_e3_iff`, `grSub_eR_iff`) and the two elementary translations `mem_rdp_outer` and
  `mem_rdp_bad`.
-/
import Mathlib
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilC4.CritDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc TR rexpL)

variable {k : ℕ}

/-! ## 1. The two graph-substitutions, read through `CGr` -/

/-- Membership of a point `Sum.elim v u` of the `(v, ε, δ, y)` block in the graph-substitution of
`Y` along `e3` (substituting the argument `v 0`, the value `y = u 2` and the tail `tup v`). -/
lemma grSub_e3_iff {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    (Sum.elim v u) ∈ GrSub Y e3 v03 y3 ↔ CGr Y (tup v) (v 0) (u 2) := by
  simp only [GrSub, CGr, Set.mem_ofPred_eq, v03, y3, Sum.elim_inl, Sum.elim_inr]
  rw [show (Sum.elim v u ∘ (Sum.inl ∘ Fin.succ)) = (tup v : Fin k → ℝ) from rfl]

/-- Membership of a point `g` of the `(v, ε, δ, y, t, w)` block in the graph-substitution of `Y`
along `eR` (substituting the argument `g tR`, the value `g wR` and the parameter tail read off
the first block). -/
lemma grSub_eR_iff {Y : Set (Fin (k+2) → ℝ)} {g : ρR k → ℝ} :
    g ∈ GrSub Y eR tR wR ↔ CGr Y (tup (fun i => g (eR i))) (g tR) (g wR) := by
  simp only [GrSub, CGr, Set.mem_ofPred_eq, tR, wR]
  rw [show (g ∘ (eR ∘ Fin.succ)) = tup (fun i => g (eR i)) from rfl]

/-! ## 2. The outer and the bad set -/

/-- The "outer" set of `RDpart` on the block `(v, ε, δ, y)`: `0 < ε`, `0 < δ` and
`(v 0, y)` a value of the fibre at `tup v`. -/
def rdp_outer (Y : Set (Fin (k+2) → ℝ)) : Set (ρ3 k → ℝ) :=
  {x | 0 < x eps3 ∧ 0 < x del3} ∩ GrSub Y e3 v03 y3

/-- The "bad" set of `RDpart` on the block `(v, ε, δ, y, t, w)`: `t ∈ (v 0, v 0 + δ)`, `w` a value
of the fibre at `t`, and `w + ε ≤ y` fails. -/
def rdp_bad (Y : Set (Fin (k+2) → ℝ)) : Set (ρR k → ℝ) :=
  GrSub Y eR tR wR ∩ {g | g v0R < g tR} ∩ {g | g tR < g v0R + g delR} ∩
    {g | ¬ (g wR + g epsR ≤ g yR)}

lemma rdp_outer_definable {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (rdp_outer Y) :=
  ((definable_lt_const (0:ℝ) eps3).inter (definable_lt_const (0:ℝ) del3)).inter
    (GrSub_definable hY e3 v03 y3)

lemma rdp_bad_definable {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (rdp_bad Y) :=
  (((GrSub_definable hY eR tR wR).inter (real_definable_lt v0R tR)).inter
    (definable_lt_add tR v0R delR)).inter (definable_le_sum wR epsR yR).compl

/-! ## 3. Reading the two sets in coordinates -/

lemma mem_rdp_outer {Y : Set (Fin (k+2) → ℝ)} {v : Fin (k+1) → ℝ} {u : Fin 3 → ℝ} :
    (Sum.elim v u) ∈ rdp_outer Y ↔ 0 < u 0 ∧ 0 < u 1 ∧ CGr Y (tup v) (v 0) (u 2) := by
  rw [rdp_outer, Set.mem_inter_iff, Set.mem_ofPred_eq, grSub_e3_iff]
  simp only [eps3, del3, Sum.elim_inr]
  tauto

/-- Membership in `rdp_bad` for a point `g` of `ℝ^{ρR}` whose restriction to the first block is
`Sum.elim v u`: the conditions are stated in the coordinates `(g tR, g wR)` of the second block
and `(u 0, u 1, u 2)` of the first. -/
lemma mem_rdp_bad {Y : Set (Fin (k+2) → ℝ)} {g : ρR k → ℝ} {v : Fin (k+1) → ℝ}
    {u : Fin 3 → ℝ} (hg : g ∘ (Sum.inl : ρ3 k → ρR k) = Sum.elim v u) :
    g ∈ rdp_bad Y ↔ v 0 < g tR ∧ g tR < v 0 + u 1 ∧ CGr Y (tup v) (g tR) (g wR) ∧
      ¬ (g wR + u 0 ≤ u 2) := by
  have htail : (fun i : Fin (k+1) => g (eR i)) = v := by
    funext i
    have h := congrFun hg (Sum.inl i)
    simpa [Function.comp_apply, Sum.elim_inl] using h
  have h1 : g ∈ GrSub Y eR tR wR ↔ CGr Y (tup v) (g tR) (g wR) := by
    rw [grSub_eR_iff, htail]
  have h2 : g v0R = v 0 := by
    have h := congrFun hg (Sum.inl 0)
    simpa [Function.comp_apply, Sum.elim_inl, v0R] using h
  have h3 : g delR = u 1 := by
    have h := congrFun hg (Sum.inr (1:Fin 3))
    simpa [Function.comp_apply, Sum.elim_inr, delR] using h
  have h4 : g epsR = u 0 := by
    have h := congrFun hg (Sum.inr (0:Fin 3))
    simpa [Function.comp_apply, Sum.elim_inr, epsR] using h
  have h5 : g yR = u 2 := by
    have h := congrFun hg (Sum.inr (2:Fin 3))
    simpa [Function.comp_apply, Sum.elim_inr, yR] using h
  rw [rdp_bad, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq, h1, h2, h3, h4, h5]
  tauto

/-! ## 4. The target -/

theorem RDpart_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.RDpart Y) := by
  have hmain := shape_lemma (k := k) (O := rdp_outer Y) (B := rdp_bad Y)
    (rdp_outer_definable hY) (rdp_bad_definable hY)
  have hset : {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ rdp_outer Y ∧
      Sum.elim v u ∉ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' rdp_bad Y)}
      = RDpart Y := by
    ext v
    rw [RDpart]
    simp only [Set.mem_ofPred_eq]
    constructor
    · -- the `(ε, δ, y)` of the shape lemma witness both `rdp_outer` and `RDpart`
      rintro ⟨u, hO, hnot⟩
      rw [mem_rdp_outer] at hO
      obtain ⟨hε, hδ, hgr⟩ := hO
      refine ⟨u 0, u 1, u 2, hε, hδ, hgr, ?_⟩
      intro t ht1 ht2 w hgrw
      -- a violating pair `(t, w)` would put `Sum.elim (Sum.elim v u) ![t, w]` into the bad set
      by_contra hle
      have hgc : (Sum.elim (Sum.elim v u) ![t, w]) ∘ (Sum.inl : ρ3 k → ρR k)
          = Sum.elim v u := by
        funext z
        rfl
      refine hnot ?_
      rw [Set.mem_image]
      exact ⟨Sum.elim (Sum.elim v u) ![t, w],
        (mem_rdp_bad hgc).mpr ⟨ht1, ht2, hgrw, hle⟩, hgc⟩
    · -- conversely `(ε, δ, y)` gives the point `Sum.elim v ![ε, δ, y]` of the outer set
      rintro ⟨ε, δ, y, hε, hδ, hgr, hmon⟩
      refine ⟨![ε, δ, y], ?_, ?_⟩
      · rw [mem_rdp_outer]
        exact ⟨hε, hδ, hgr⟩
      · intro hmem
        rw [Set.mem_image] at hmem
        obtain ⟨g, hgB, hgcomp⟩ := hmem
        rw [mem_rdp_bad hgcomp] at hgB
        obtain ⟨ht1, ht2, hgrw, hnotle⟩ := hgB
        exact hnotle (hmon (g tR) ht1 ht2 (g wR) hgrw)
  rw [hset] at hmain
  exact hmain

end Work.WilC4
