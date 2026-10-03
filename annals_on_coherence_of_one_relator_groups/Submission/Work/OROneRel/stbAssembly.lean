/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Assembly of the Schreier tree-basis theorem

This file assembles the proof of `Work.OROneRel.schreier_tree_basis` from the definitions and the
development algebra of `Submission/Work/OROneRel/stbDefs.lean`.  The single "geometric" input is the
identity `hedge`: the development of the loop word of an edge of non-trivial loop class is the symbol
of that edge.  Everything in this file is a consequence of `hedge` and of the elementary algebra of
`stbDev`; the geometric input itself is supplied by

* `Work.OROneRel.stb_tree_step` (the letters of `toWord (t k)` are tree edges),
* `Work.OROneRel.stbDev_treePath_up` / `stbDev_treePath_down` (the development vanishes on the tree
  paths),
* `Work.OROneRel.stbDev_edgeWord` (`hedge`),

which are imported in `Submission/Work/OROneRel/schreier_tree_basis.lean`.

## Contents

* `stbToClasses_eq_gaugeMap` -- the class map of the development is the gauge map of the decorated
  word;
* `stbToClasses_dev` -- hence the telescoping identity
  `stbToClasses t c (stbDev t c i L) = t i * mk L * (t (i + lsig c L))⁻¹`;
* `stb_mk_edgeWord`, `stbExpand_mk` -- the expansion of a word in the basis represents the class map;
* `stbExpand_dev` -- and the development of the expansion is the word itself (this uses `hedge` once
  per letter);
* `stbToClasses_injective` -- hence the class map is injective;
* `stbToClasses_range_ker` -- and its range is exactly `ker (cohom c)`;
* `stb_schreier_of` -- the isomorphism of the statement.
-/
import Mathlib
import Submission.Work.OROneRel.stbDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.mk_expand

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## `mk` of the elementary words -/

theorem stb_mk_nil {β : Type*} : FreeGroup.mk ([] : List (β × Bool)) = 1 := rfl

theorem stb_mk_cons_true {β : Type*} (a : β) (L : List (β × Bool)) :
    FreeGroup.mk ((a, true) :: L) = FreeGroup.of a * FreeGroup.mk L := by
  rw [show ((a, true) :: L : List (β × Bool)) = [(a, true)] ++ L from rfl, stb_mk_append,
    stb_mk_singleton_true]

theorem stb_mk_cons_false {β : Type*} (a : β) (L : List (β × Bool)) :
    FreeGroup.mk ((a, false) :: L) = (FreeGroup.of a)⁻¹ * FreeGroup.mk L := by
  rw [show ((a, false) :: L : List (β × Bool)) = [(a, false)] ++ L from rfl, stb_mk_append,
    stb_mk_singleton_false]

/-! ## The weight of `wordOf` and the unfolding of the loop word -/

/-- The weight of the reduced word of an element is the cohomological weight of the element. -/
theorem stb_lsig_wordOf (c : α → ℤ) (v : FreeGroup α) :
    lsig c (wordOf v) = (cohom c v).toAdd := by
  have h := cohom_mk c (wordOf v)
  rw [mk_wordOf] at h
  exact (congrArg Multiplicative.toAdd h).symm

/-- The loop word of an edge, unfolded: the tree path up, the edge, the tree path back. -/
theorem stbEdgeWord_eta (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbEdgeWord t c e = wordOf (t e.2) ++ [(e.1, true)] ++
      FreeGroup.invRev (wordOf (t (e.2 + c e.1))) := rfl

/-! ## The class map on a symbol -/

/-- The loop class of an edge is the gauge-map value of its symbol. -/
theorem stbLoop_eq_gaugeMap_of (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    stbLoop t c e = gaugeMap t c (FreeGroup.of e) := by
  rw [gaugeMap_of, stbLoop]

/-- The class map sends the symbol of a traversal to the loop class of its edge, with the sign of
the traversal (and to `1` when the edge is a tree edge, in which case the loop class is `1`). -/
theorem stbToClasses_edge (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    stbToClasses t c (stbEdge t c e b) =
      (bif b then stbLoop t c e else (stbLoop t c e)⁻¹) := by
  by_cases h : stbLoop t c e = 1
  · cases b
    · rw [stbEdge_false_of_eq_one t c e h, map_one]
      simp [h]
    · rw [stbEdge_true_of_eq_one t c e h, map_one]
      simp [h]
  · cases b
    · rw [stbEdge_false_of_ne t c e h, map_inv, stbToClasses_of]
      rfl
    · rw [stbEdge_true_of_ne t c e h, stbToClasses_of]
      rfl

/-! ## The class map of the development is the gauge map of the decorated word -/

theorem stbToClasses_eq_gaugeMap (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ)
    (L : List (α × Bool)) :
    stbToClasses t c (stbDev t c i L) = gaugeMap t c (FreeGroup.mk (decor c i L)) := by
  induction L generalizing i with
  | nil =>
    rw [stbDev_nil, map_one, show decor c i ([] : List (α × Bool)) = [] from rfl, stb_mk_nil,
      map_one]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [show decor c i ((a, false) :: L)
          = ((a, i - c a), false) :: decor c (i - c a) L from rfl, stbDev_cons_false, map_mul,
        stb_mk_cons_false, map_mul, ih (i - c a), stbToClasses_edge, stbLoop_eq_gaugeMap_of]
      simp only [cond_false, map_inv]
    · rw [show decor c i ((a, true) :: L)
          = ((a, i), true) :: decor c (i + c a) L from rfl, stbDev_cons_true, map_mul,
        stb_mk_cons_true, map_mul, ih (i + c a), stbToClasses_edge, stbLoop_eq_gaugeMap_of]
      simp only [cond_true]

/-- **The telescoping identity of the development**: the class map of the development of a word read
from level `i` is `t i * (the word) * (t (i + weight))⁻¹`. -/
theorem stbToClasses_dev (t : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    stbToClasses t c (stbDev t c i L) = t i * FreeGroup.mk L * (t (i + lsig c L))⁻¹ := by
  rw [stbToClasses_eq_gaugeMap, gauge_decor]

/-! ## The expansion represents the class map -/

/-- A loop word has weight `0`. -/
theorem stb_lsig_edgeWord (t : ℤ → FreeGroup α) (c : α → ℤ)
    (ht : ∀ k : ℤ, cohom c (t k) = Multiplicative.ofAdd k) (e : α × ℤ) :
    lsig c (stbEdgeWord t c e) = 0 := by
  rw [stbEdgeWord_eta, stb_lsig_append, stb_lsig_append, stb_lsig_singleton_true,
    stb_lsig_invRev, stb_lsig_wordOf, stb_lsig_wordOf, ht e.2, ht (e.2 + c e.1)]
  simp only [toAdd_ofAdd]
  ring

theorem stb_mk_edgeWord (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    FreeGroup.mk (stbEdgeWord t c e) = stbLoop t c e := by
  rw [stbEdgeWord_eta, stb_mk_append, stb_mk_append, mk_wordOf, stb_mk_singleton_true,
    stb_mk_invRev, mk_wordOf, stbLoop]

theorem stb_mk_edgeWordSigned (t : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    FreeGroup.mk (stbEdgeWordSigned t c e b) =
      (bif b then stbLoop t c e else (stbLoop t c e)⁻¹) := by
  cases b
  · rw [show stbEdgeWordSigned t c e false = FreeGroup.invRev (stbEdgeWord t c e) from rfl,
      stb_mk_invRev, stb_mk_edgeWord]
    rfl
  · rw [show stbEdgeWordSigned t c e true = stbEdgeWord t c e from rfl, stb_mk_edgeWord]
    rfl

/-- **The expansion of a word in the Schreier basis represents the class map.** -/
theorem stbExpand_mk (t : ℤ → FreeGroup α) (c : α → ℤ) (w : FreeGroup (stbBeta t c)) :
    FreeGroup.mk (stbExpand t c w) = stbToClasses t c w := by
  letI := stbBetaDecidableEq t c
  have hpt : ∀ p : stbBeta t c × Bool,
      FreeGroup.mk (stbEdgeWordSigned t c p.1.1 p.2) =
        (bif p.2 then stbLoop t c p.1.1 else (stbLoop t c p.1.1)⁻¹) :=
    fun p => stb_mk_edgeWordSigned t c p.1.1 p.2
  have key : FreeGroup.mk (((FreeGroup.toWord w).map
        (fun p : stbBeta t c × Bool => stbEdgeWordSigned t c p.1.1 p.2)).flatten)
      = FreeGroup.lift (fun e : stbBeta t c => stbLoop t c e.1)
          (FreeGroup.mk (FreeGroup.toWord w)) :=
    mk_flatten_expand (fun p : stbBeta t c × Bool => stbEdgeWordSigned t c p.1.1 p.2)
      (fun e : stbBeta t c => stbLoop t c e.1) hpt (FreeGroup.toWord w)
  calc FreeGroup.mk (stbExpand t c w)
      = FreeGroup.mk (((FreeGroup.toWord w).map
          (fun p : stbBeta t c × Bool => stbEdgeWordSigned t c p.1.1 p.2)).flatten) := rfl
    _ = FreeGroup.lift (fun e : stbBeta t c => stbLoop t c e.1)
          (FreeGroup.mk (FreeGroup.toWord w)) := key
    _ = FreeGroup.lift (fun e : stbBeta t c => stbLoop t c e.1) w := by rw [FreeGroup.mk_toWord]
    _ = stbToClasses t c w := rfl

/-! ## The development of the expansion -/

/-- **The development of the expansion of a word in the basis is the word itself.**  This uses the
geometric input `hedge` once per letter of the word. -/
theorem stbExpand_dev (t : ℤ → FreeGroup α) (c : α → ℤ)
    (ht : ∀ k : ℤ, cohom c (t k) = Multiplicative.ofAdd k)
    (hedgeT : ∀ (e : α × ℤ) (h : stbLoop t c e ≠ 1),
      stbDev t c 0 (stbEdgeWord t c e) = FreeGroup.of (⟨e, h⟩ : stbBeta t c))
    (hedgeF : ∀ (e : α × ℤ) (h : stbLoop t c e ≠ 1),
      stbDev t c 0 (FreeGroup.invRev (stbEdgeWord t c e)) =
        (FreeGroup.of (⟨e, h⟩ : stbBeta t c))⁻¹)
    (w : FreeGroup (stbBeta t c)) : stbDev t c 0 (stbExpand t c w) = w := by
  letI := stbBetaDecidableEq t c
  have hlsig : ∀ e : α × ℤ, lsig c (stbEdgeWord t c e) = 0 := stb_lsig_edgeWord t c ht
  have hpiece : ∀ x ∈ (FreeGroup.toWord w).map
      (fun p => stbEdgeWordSigned t c p.1.1 p.2), lsig c x = 0 := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, b⟩ := p
    cases b
    · rw [show stbEdgeWordSigned t c e.1 false = FreeGroup.invRev (stbEdgeWord t c e.1) from rfl,
        stb_lsig_invRev, hlsig, neg_zero]
    · rw [show stbEdgeWordSigned t c e.1 true = stbEdgeWord t c e.1 from rfl, hlsig]
  have hdev : ∀ p ∈ FreeGroup.toWord w,
      stbDev t c 0 (stbEdgeWordSigned t c p.1.1 p.2) =
        (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) := by
    intro p _
    cases hb : p.2
    · rw [show stbEdgeWordSigned t c p.1.1 false =
          FreeGroup.invRev (stbEdgeWord t c p.1.1) from rfl, hedgeF p.1.1 p.1.2]
      rfl
    · rw [show stbEdgeWordSigned t c p.1.1 true = stbEdgeWord t c p.1.1 from rfl,
        hedgeT p.1.1 p.1.2]
      rfl
  rw [stbExpand, stb_dev_map_flatten_of_lsig_eq_zero t c
    (FreeGroup.toWord w) (fun p => stbEdgeWordSigned t c p.1.1 p.2) hpiece 0]
  rw [List.map_congr_left hdev, ← stb_mk_eq_prod_map_signed (FreeGroup.toWord w),
    FreeGroup.mk_toWord]

/-! ## The class map is injective and its range is the kernel -/

theorem stbToClasses_injective (t : ℤ → FreeGroup α) (c : α → ℤ)
    (hdev : ∀ w : FreeGroup (stbBeta t c), stbDev t c 0 (stbExpand t c w) = w) :
    Function.Injective (stbToClasses t c) := by
  intro x y hxy
  have h1 : stbToClasses t c (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : FreeGroup.mk (stbExpand t c (x * y⁻¹)) = 1 := by
    rw [stbExpand_mk]; exact h1
  have h3 : stbDev t c 0 (stbExpand t c (x * y⁻¹)) = 1 :=
    stbDev_eq_one_of_mk_eq_one t c 0 h2
  have h4 := hdev (x * y⁻¹)
  have h5 : x * y⁻¹ = 1 := h4.symm.trans h3
  rwa [mul_inv_eq_one] at h5

/-- The class map has range contained in the kernel of `cohom c`: every loop class has weight `0`. -/
theorem cohom_stbToClasses (t : ℤ → FreeGroup α) (c : α → ℤ)
    (ht : ∀ k : ℤ, cohom c (t k) = Multiplicative.ofAdd k) (w : FreeGroup (stbBeta t c)) :
    cohom c (stbToClasses t c w) = 1 := by
  have hcomp : (cohom c).comp (stbToClasses t c) = 1 := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, MonoidHom.one_apply, stbToClasses_of, stbLoop, map_mul, map_mul,
      map_inv, cohom_of, ht e.1.2, ht (e.1.2 + c e.1.1), ofAdd_add, mul_inv_cancel]
  exact DFunLike.congr_fun hcomp w

/-- **The range of the class map is the kernel of `cohom c`.** -/
theorem stbToClasses_range_ker (t : ℤ → FreeGroup α) (c : α → ℤ)
    (ht0 : t 0 = 1) (ht : ∀ k : ℤ, cohom c (t k) = Multiplicative.ofAdd k)
    (g : ↥(cohom c).ker) :
    ∃ w : FreeGroup (stbBeta t c), stbToClasses t c w = (g : FreeGroup α) := by
  refine ⟨stbDev t c 0 (wordOf (g : FreeGroup α)), ?_⟩
  have hg : cohom c (g : FreeGroup α) = 1 := MonoidHom.mem_ker.mp g.2
  have hlsig : lsig c (wordOf (g : FreeGroup α)) = 0 := by
    rw [stb_lsig_wordOf, hg]
    rfl
  rw [stbToClasses_dev, ht0, one_mul, mk_wordOf, hlsig, add_zero, ht0, inv_one, mul_one]

/-! ## The isomorphism -/

/-- **The Schreier tree basis.**  If the development of the loop word of an edge of non-trivial loop
class is the symbol of that edge (`hedge`), then the class map is an isomorphism onto the kernel of
`cohom c`, sending the symbol of `e` to the loop class of `e`. -/
theorem stb_schreier_of {α : Type u} (c : α → ℤ) (t : ℤ → FreeGroup α)
    (ht0 : t 0 = 1) (ht : ∀ k : ℤ, cohom c (t k) = Multiplicative.ofAdd k)
    (hedgeT : ∀ (e : α × ℤ) (h : stbLoop t c e ≠ 1),
      stbDev t c 0 (stbEdgeWord t c e) = FreeGroup.of (⟨e, h⟩ : stbBeta t c))
    (hedgeF : ∀ (e : α × ℤ) (h : stbLoop t c e ≠ 1),
      stbDev t c 0 (FreeGroup.invRev (stbEdgeWord t c e)) =
        (FreeGroup.of (⟨e, h⟩ : stbBeta t c))⁻¹) :
    ∃ (e : FreeGroup {p : α × ℤ // t p.2 * FreeGroup.of p.1 * (t (p.2 + c p.1))⁻¹ ≠ 1} ≃*
        ↥(Work.OROneRel.cohom c).ker),
      ∀ p : {p : α × ℤ // t p.2 * FreeGroup.of p.1 * (t (p.2 + c p.1))⁻¹ ≠ 1},
        ((e (FreeGroup.of p) : ↥(Work.OROneRel.cohom c).ker) : FreeGroup α) =
          t p.1.2 * FreeGroup.of p.1.1 * (t (p.1.2 + c p.1.1))⁻¹ := by
  have hdev : ∀ w : FreeGroup (stbBeta t c), stbDev t c 0 (stbExpand t c w) = w :=
    stbExpand_dev t c ht hedgeT hedgeF
  have hinj : Function.Injective (stbToClasses t c) := stbToClasses_injective t c hdev
  let ψ : FreeGroup (stbBeta t c) →* ↥(Work.OROneRel.cohom c).ker :=
    (stbToClasses t c).codRestrict _ fun w => MonoidHom.mem_ker.mpr (cohom_stbToClasses t c ht w)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact hinj (by simpa [ψ] using congrArg Subtype.val hxy)
  have hψsurj : Function.Surjective ψ := by
    intro g
    obtain ⟨w, hw⟩ := stbToClasses_range_ker t c ht0 ht g
    refine ⟨w, ?_⟩
    refine Subtype.ext ?_
    change ((ψ w : ↥(Work.OROneRel.cohom c).ker) : FreeGroup α) = (g : FreeGroup α)
    rw [show ((ψ w : ↥(Work.OROneRel.cohom c).ker) : FreeGroup α) = stbToClasses t c w from rfl,
      hw]
  refine ⟨MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩, ?_⟩
  intro p
  show ((ψ (FreeGroup.of p) : ↥(Work.OROneRel.cohom c).ker) : FreeGroup α) =
    t p.1.2 * FreeGroup.of p.1.1 * (t (p.1.2 + c p.1.1))⁻¹
  simp only [ψ, MonoidHom.codRestrict_apply, stbToClasses_of, stbLoop]

end Work.OROneRel
