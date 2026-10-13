/-
  WilC4/ulpm_crit — the "niceness" lemma of the C4 route.

  For a `∅`-definable family of graphs `Y ⊆ ℝ^{k+2}` there are a uniform bound `N` and a
  `∅`-definable breakpoint family `B ⊆ ℝ^{k+1}` with at most `N` points per fibre such that on
  every interval `(a,b)` avoiding `B_c`:

  * the domain of the fibre function is all of `(a,b)` or disjoint from it,
  * the zero set of the fibre function is all of `(a,b)` or disjoint from it,
  * the fibre function is continuous on `(a,b)`.

  The breakpoints are `BndDom ∪ BndZero ∪ Bad` (`CritDefs.lean`): the boundary points of the
  domain and of the zero set, and the *one-sidedly bad* points at which the fibre map is far from
  its value on one side.  All the definability and uniform-finiteness inputs are proved in sibling
  files (`crit_def_bnd`, `crit_def_bad`, `crit_unif`, `crit_im_bound`, `crit_def_germ`,
  `crit_germ_oc2`, `crit_bad_noInterval`, `crit_fail_mem_bad`); this file assembles them.

  The elementary order-theoretic lemmas used in the assembly (`ordConnected_cover_subinterval`,
  `subinterval_of_accumulate`, `Ioo_subset_of_no_bnd`, …) live in `CritDefs.lean`.

  Probe scaffolding (not imported by anything): the `_`-prefixed files in this directory
  (`_crit_probe*.lean`, `_crit_stmt_chk.lean`, `_encard_chk.lean`, `_critdefs_build.txt`,
  `_ulpm_build.txt`, …) were used while developing; they contain no deliverable.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.crit_unif
import Submission.Work.WilC4.crit_def_bnd
import Submission.Work.WilC4.crit_def_bad
import Submission.Work.WilC4.crit_im_bound
import Submission.Work.WilC4.crit_def_germ
import Submission.Work.WilC4.crit_germ_oc2
import Submission.Work.WilC4.crit_bad_noInterval
import Submission.Work.WilC4.crit_fail_mem_bad

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open scoped ENat
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## 1. Boundary points of the domain and of the zero set -/

/-- The fibre of `BndDom` is the boundary of the fibre domain. -/
@[simp] lemma bndDom_fibre {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ BndDom Y ↔ WilC2.IsBnd (DomFib Y c) x := by
  rw [mem_bndDom, tup_cons]
  rfl

/-- The fibre of `BndZero` is the boundary of the fibre zero set. -/
@[simp] lemma bndZero_fibre {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x : ℝ} :
    Fin.cons x c ∈ BndZero Y ↔ WilC2.IsBnd (ZeroFib Y c) x := by
  rw [mem_bndZero, tup_cons]
  rfl

/-- **Domain dichotomy.**  An interval avoiding the boundary family and meeting the domain of the
fibre is contained in that domain. -/
theorem dom_dichotomy {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ}
    (hbnd : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ BndDom Y) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hxD : x ∈ DomFib Y c) : Set.Ioo a b ⊆ DomFib Y c := by
  refine Ioo_subset_of_no_bnd (D := DomFib Y c) (fun z hz hbz => hbnd z hz ?_) hx hxD
  rwa [bndDom_fibre]

/-- **Zero-set dichotomy.**  An interval avoiding the boundary family and meeting the zero set of
the fibre is contained in that zero set. -/
theorem zero_dichotomy {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {a b : ℝ}
    (hbnd : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ BndZero Y) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hxD : x ∈ ZeroFib Y c) : Set.Ioo a b ⊆ ZeroFib Y c := by
  refine Ioo_subset_of_no_bnd (D := ZeroFib Y c) (fun z hz hbz => hbnd z hz ?_) hx hxD
  rwa [bndZero_fibre]

/-! ## 2. Finiteness of the bad-point fibres -/

/-- **`Bad_c` is finite.**  If none of the four one-sided bad families contains a whole interval
inside its `c`-fibre (`crit_bad_noInterval`), then that fibre of `Bad` is finite: o-minimality
turns each of the four fibres into a finite union of order convex sets, and a union of finitely
many point-sets is finite. -/
theorem bad_finite_of_noInterval {Y : Set (Fin (k + 2) → ℝ)} (hOM : OMinModels) {c : Fin k → ℝ}
    (hRUd : (Set.univ : Set ℝ).Definable₁ LRc {x : ℝ | Fin.cons x c ∈ BadRU Y})
    (hRDd : (Set.univ : Set ℝ).Definable₁ LRc {x : ℝ | Fin.cons x c ∈ BadRD Y})
    (hLUd : (Set.univ : Set ℝ).Definable₁ LRc {x : ℝ | Fin.cons x c ∈ BadLU Y})
    (hLDd : (Set.univ : Set ℝ).Definable₁ LRc {x : ℝ | Fin.cons x c ∈ BadLD Y})
    (hnoInt : (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRU Y)) ∧
      (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadRD Y)) ∧
      (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLU Y)) ∧
      (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → Fin.cons x c ∈ BadLD Y))) :
    {x : ℝ | Fin.cons x c ∈ Bad Y}.Finite := by
  classical
  haveI : ℝ ⊨ TR := inferInstanceAs (ℝ ⊨ LRc.completeTheory ℝ)
  -- a definable set is either finite or contains a nondegenerate interval
  have key : ∀ S : Set ℝ, (Set.univ : Set ℝ).Definable₁ LRc S →
      (∀ u v : ℝ, u < v → ¬ (∀ x : ℝ, u < x → x < v → x ∈ S)) → S.Finite := by
    intro S hSd hno
    by_contra hfin
    obtain ⟨s, hs, hX⟩ := hOM ℝ {p : Fin 1 → ℝ | p 0 ∈ S} hSd
    have hSeq : S = ⋃₀ (s : Set (Set ℝ)) := by
      ext x
      have h := Set.ext_iff.mp hX (fun _ : Fin 1 => x)
      simpa using h
    -- some piece contains two distinct points
    have hpiece : ∃ I ∈ s, ∃ x ∈ I, ∃ y ∈ I, x < y := by
      by_contra hcon
      push_neg at hcon
      have hpt : ∀ I ∈ s, (I : Set ℝ).Subsingleton := by
        intro I hI
        refine fun x hx y hy => ?_
        by_contra hxy
        rcases lt_or_gt_of_ne hxy with h | h
        · exact absurd h (not_lt.mpr (hcon I hI x hx y hy))
        · exact absurd h (not_lt.mpr (hcon I hI y hy x hx))
      refine hfin ?_
      refine (s.finite_toSet.biUnion fun I hI => (hpt I hI).finite).subset ?_
      intro x hx
      obtain ⟨I, hI, hxI⟩ := Set.mem_sUnion.mp (hSeq ▸ hx)
      exact Set.mem_biUnion hI hxI
    obtain ⟨I, hI, x, hxI, y, hyI, hxy⟩ := hpiece
    exact hno x y hxy fun z hz1 hz2 =>
      hSeq ▸ Set.subset_sUnion_of_mem hI
        ((hs I hI).out' hxI hyI ⟨le_of_lt hz1, le_of_lt hz2⟩)
  have h1 : {x : ℝ | Fin.cons x c ∈ BadRU Y}.Finite :=
    key _ hRUd fun u v huv h => hnoInt.1 u v huv h
  have h2 : {x : ℝ | Fin.cons x c ∈ BadRD Y}.Finite :=
    key _ hRDd fun u v huv h => hnoInt.2.1 u v huv h
  have h3 : {x : ℝ | Fin.cons x c ∈ BadLU Y}.Finite :=
    key _ hLUd fun u v huv h => hnoInt.2.2.1 u v huv h
  have h4 : {x : ℝ | Fin.cons x c ∈ BadLD Y}.Finite :=
    key _ hLDd fun u v huv h => hnoInt.2.2.2 u v huv h
  have hBad_eq : {x : ℝ | Fin.cons x c ∈ Bad Y} =
      ({x : ℝ | Fin.cons x c ∈ BadRU Y} ∪ {x : ℝ | Fin.cons x c ∈ BadRD Y}) ∪
        ({x : ℝ | Fin.cons x c ∈ BadLU Y} ∪ {x : ℝ | Fin.cons x c ∈ BadLD Y}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, mem_bad]
    tauto
  rw [hBad_eq]
  exact (h1.union h2).union (h3.union h4)

theorem ulpm_crit {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels) (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') :
    ∃ N : ℕ, ∃ B : Set (Fin (k + 1) → ℝ), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B ∧
      (∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N) ∧
      ∀ c : Fin k → ℝ, ∀ a b : ℝ, a < b →
        (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
        ((∃ x ∈ Set.Ioo a b, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y) →
            (∀ x ∈ Set.Ioo a b, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y)) ∧
        ((∃ x ∈ Set.Ioo a b, Fin.cons x (Fin.cons 0 c) ∈ Y) →
            (∀ x ∈ Set.Ioo a b, Fin.cons x (Fin.cons 0 c) ∈ Y)) ∧
        (∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b,
            ∀ y y' : ℝ, |x' - x| < δ → Fin.cons x (Fin.cons y c) ∈ Y →
            Fin.cons x' (Fin.cons y' c) ∈ Y → |y' - y| < ε) := by
  -- the boundary families: definability and pointwise finiteness
  obtain ⟨hBDdef, hBZdef, hBDfin⟩ := crit_def_bnd (k := k) Y hY hOM
  -- the four one-sided bad families: definability of the families and of their fibres
  obtain ⟨hRUdef, hRDdef, hLUdef, hLDdef, hBfib⟩ := crit_def_bad (k := k) Y hY
  have hBadDef : (∅ : Set ℝ).Definable LRc (Bad Y) := by
    rw [Bad]
    exact ((hRUdef.union hRDdef).union hLUdef).union hLDdef
  -- uniform bounds for the boundary families
  obtain ⟨N₁, hN₁⟩ := crit_unif (k := k) hOM (BndDom Y) hBDdef fun c => (hBDfin c).1
  obtain ⟨N₂, hN₂⟩ := crit_unif (k := k) hOM (BndZero Y) hBZdef fun c => (hBDfin c).2
  -- the uniform finiteness of the image family
  obtain ⟨Nim, hIm⟩ := crit_im_bound (k := k) hOM Y hY
  -- the parametric germ families and the order-convex decompositions
  obtain ⟨_hDomDef, _hWDef, hLmDef, hHmDef, hLpDef, hHpDef, hLADef, hHADef⟩ :=
    crit_def_germ (k := k) Y hY
  obtain ⟨hLset, hHset⟩ := crit_germ_oc2 (k := k) hOM Y hLADef hHADef
  -- a fibre of `Bad` contains no interval, hence is finite
  have hnoInt :=
    crit_bad_noInterval (k := k) hOM Y hY hfun ⟨Nim, hIm⟩ hLset hHset hLmDef hHmDef hLpDef hHpDef
  have hBadFin : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ Bad Y}.Finite := fun c =>
    bad_finite_of_noInterval (k := k) hOM (hBfib c).1 (hBfib c).2.1 (hBfib c).2.2.1
      (hBfib c).2.2.2 (hnoInt c)
  obtain ⟨N₃, hN₃⟩ := crit_unif (k := k) hOM (Bad Y) hBadDef hBadFin
  refine ⟨N₁ + N₂ + N₃, (BndDom Y ∪ BndZero Y) ∪ Bad Y, ?_, ?_, ?_⟩
  · exact (hBDdef.union hBZdef).union hBadDef
  · intro c
    have hfib : {x : ℝ | Fin.cons x c ∈ (BndDom Y ∪ BndZero Y) ∪ Bad Y} =
        ({x : ℝ | Fin.cons x c ∈ BndDom Y} ∪ {x : ℝ | Fin.cons x c ∈ BndZero Y}) ∪
          {x : ℝ | Fin.cons x c ∈ Bad Y} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [hfib]
    calc ((({x : ℝ | Fin.cons x c ∈ BndDom Y} ∪ {x : ℝ | Fin.cons x c ∈ BndZero Y}) ∪
            {x : ℝ | Fin.cons x c ∈ Bad Y}).encard)
        ≤ (({x : ℝ | Fin.cons x c ∈ BndDom Y} ∪ {x : ℝ | Fin.cons x c ∈ BndZero Y}).encard +
            ({x : ℝ | Fin.cons x c ∈ Bad Y}).encard) := Set.encard_union_le _ _
      _ ≤ (({x : ℝ | Fin.cons x c ∈ BndDom Y}).encard +
            ({x : ℝ | Fin.cons x c ∈ BndZero Y}).encard +
              ({x : ℝ | Fin.cons x c ∈ Bad Y}).encard) := by
          exact add_le_add (Set.encard_union_le _ _) le_rfl
      _ ≤ ((N₁ + N₂ + N₃ : ℕ) : ENat) := by
          have h1 := hN₁ c
          have h2 := hN₂ c
          have h3 := hN₃ c
          calc ({x : ℝ | Fin.cons x c ∈ BndDom Y}).encard +
                ({x : ℝ | Fin.cons x c ∈ BndZero Y}).encard +
                  ({x : ℝ | Fin.cons x c ∈ Bad Y}).encard
              ≤ (N₁ : ENat) + (N₂ : ENat) + (N₃ : ENat) := add_le_add (add_le_add h1 h2) h3
            _ = ((N₁ + N₂ + N₃ : ℕ) : ENat) := by
                rw [Nat.cast_add, Nat.cast_add]
  · intro c a b hab hBav
    have hNotDom : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ BndDom Y := fun x hx hmem =>
      hBav x hx (Or.inl (Or.inl hmem))
    have hNotZero : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ BndZero Y := fun x hx hmem =>
      hBav x hx (Or.inl (Or.inr hmem))
    have hNotBad : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bad Y := fun x hx hmem =>
      hBav x hx (Or.inr hmem)
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx, y, hxy⟩
      have hsub := dom_dichotomy (Y := Y) (c := c) hNotDom hx (⟨y, hxy⟩ : x ∈ DomFib Y c)
      exact fun z hz => hsub hz
    · rintro ⟨x, hx, hx0⟩
      have hsub := zero_dichotomy (Y := Y) (c := c) hNotZero hx hx0
      exact fun z hz => hsub hz
    · intro x hx ε hε
      by_cases hxdom : ∃ y : ℝ, CGr Y c x y
      · by_contra hcon
        have hsub := dom_dichotomy (Y := Y) (c := c) hNotDom hx hxdom
        refine hNotBad x hx (crit_fail_mem_bad (k := k) hOM Y hY hfun hx.1 hx.2 hsub ?_)
        intro hAll
        exact hcon (hAll ε hε)
      · refine ⟨1, one_pos, fun x' hx' y y' _ hxy _ => ?_⟩
        exact absurd ⟨y, hxy⟩ hxdom

end Work.WilC4
