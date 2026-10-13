import Mathlib
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilkiesH.Cell.isCell_nonempty

/-!
# The flat frontier lemma — the "bad cell" invariant

This file sets up the vocabulary for the proof of `Work.WilkiesH.Strat.frontier_thin_flat`,
the codimension-one (flat) step of the stratification input.

The mathematical picture.  Let `A ⊆ ℝⁿ` be an `Ω`-set.  Choose a cylindrical decomposition
compatible with `A` (`SOMin.SharpCD`).  Every cell `κ` of the decomposition is either a
*band* cell `C ⊙ (a,b)` (the complement of `C` in the product `C × ℝ`, over a base cell
`C ⊆ ℝ^{n-1}`) or a *graph* cell (a graph of a function over `C`).  A graph cell is an
(it is contained in a graph, hence has empty interior); a point of a band cell `κ` over `C`
is an interior point of `κ` — hence of any `A ⊇ κ` — as soon as its base point lies in
`int C`.  Consequently the points of `A` that are limits of points outside `A` lie in the
graph cells, or in the band cells over the "boundary part" `C \ int C` of the base cells.
Iterating this description along the base of the decomposition produces the set `badCell`
below: the invariant that must be covered is a *finite union of sets each of which is either
a graph (fibrewise `≤ 1` point) or a cylinder over a lower-dimensional invariant*; such a
union has empty interior (see `Work.WilkiesH.Strat.badCell_thin`).

## Main definitions

* `fibre u A` — the vertical fibre of `A ⊆ ℝ^{n+1}` over `u : ℝⁿ`;
* `cyl A` — the cylinder `{z | Fin.init z ∈ A}` over `A ⊆ ℝⁿ`;
* `base A` — the base (projection to the first coordinates) of `A ⊆ ℝ^{n+1}`;
* `IsGraphCell A` — `A` is a graph over its own base;
* `badCell n A` — the "thin part" of `A ⊆ ℝⁿ`, defined by recursion on `n`: a graph cell is
  entirely thin, and a band cell is thin over the thin part of its base;
* `Fr A` — the points of `A` every box around which contains a point outside `A`.

The two facts about cells that make the recursion computable (`IsCell` is an inductive
predicate, so it is the only available source of cell structure) are
`isGraphCell_of_graph` and `not_isGraphCell_of_band`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-! ## 1. Elementary lemmas about `Fin.snoc` and `Fin.init` -/

@[simp] theorem init_apply {n : ℕ} (z : Fin (n + 1) → ℝ) (i : Fin n) :
    Fin.init z i = z (Fin.castSucc i) := rfl

@[simp] theorem init_snoc {n : ℕ} (u : Fin n → ℝ) (t : ℝ) :
    Fin.init (Fin.snoc u t : Fin (n + 1) → ℝ) = u := by simp

@[simp] theorem snoc_last {n : ℕ} (u : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc u t : Fin (n + 1) → ℝ) (Fin.last n) = t := by simp

@[simp] theorem snoc_castSucc {n : ℕ} (u : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (Fin.snoc u t : Fin (n + 1) → ℝ) (Fin.castSucc i) = u i := by simp

@[simp] theorem snoc_init_self {n : ℕ} (z : Fin (n + 1) → ℝ) :
    Fin.snoc (Fin.init z) (z (Fin.last n)) = z := Fin.snoc_init_self z

theorem snoc_injective {n : ℕ} {u u' : Fin n → ℝ} {t t' : ℝ}
    (h : (Fin.snoc u t : Fin (n + 1) → ℝ) = Fin.snoc u' t') : t = t' ∧ u = u' :=
  ⟨by simpa using congrFun h (Fin.last n), by simpa using congrArg Fin.init h⟩

/-! ## 2. Boxes -/

theorem boxAround_eq_ball {n : ℕ} (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    boxAround x ε = Metric.ball x ε := by
  ext y
  rw [mem_boxAround, Metric.mem_ball, dist_pi_lt_iff hε]
  simp [Real.dist_eq]

theorem isOpen_boxAround {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) : IsOpen (boxAround x ε) := by
  rcases n with _ | n
  · have h : boxAround x ε = Set.univ := by
      ext y; simp [mem_boxAround]
    rw [h]; exact isOpen_univ
  · by_cases h : ε ≤ 0
    · have h' : boxAround x ε = ∅ := by
        ext y
        simp only [mem_boxAround, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨⟨0, Nat.succ_pos n⟩, not_lt.mpr (h.trans (abs_nonneg _))⟩
      rw [h']; exact isOpen_empty
    · rw [boxAround_eq_ball x (not_le.mp h)]; exact Metric.isOpen_ball

theorem mem_interior_iff_boxAround {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ interior A ↔ ∃ ε > 0, boxAround x ε ⊆ A := by
  constructor
  · intro hx
    rw [mem_interior_iff_mem_nhds] at hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hx
    refine ⟨ε / 2, by linarith, fun y hy => hball ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith : (0 : ℝ) < ε)]
    intro i
    rw [Real.dist_eq]
    have h2 : |y i - x i| < ε / 2 := mem_boxAround.mp hy i
    linarith
  · rintro ⟨ε, hε, hsub⟩
    exact (interior_maximal hsub (isOpen_boxAround x ε))
      (mem_boxAround.mpr (fun i => by rw [sub_self, abs_zero]; exact hε))

theorem not_mem_interior_iff {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∉ interior A ↔ ∀ ε > 0, ∃ y : Fin n → ℝ, (∀ i, |y i - x i| < ε) ∧ y ∉ A := by
  constructor
  · intro hx ε hε
    by_contra hc
    push_neg at hc
    exact hx (mem_interior_iff_boxAround.mpr ⟨ε, hε, fun y hy => hc y (mem_boxAround.mp hy)⟩)
  · rintro h hx
    obtain ⟨ε, hε, hsub⟩ := mem_interior_iff_boxAround.mp hx
    obtain ⟨y, hy, hyA⟩ := h ε hε
    exact hyA (hsub (mem_boxAround.mpr hy))

theorem interior_eq_empty_iff {n : ℕ} (A : Set (Fin n → ℝ)) :
    interior A = ∅ ↔ ∀ x : Fin n → ℝ, ∀ ε > 0, ∃ y : Fin n → ℝ,
      (∀ i, |y i - x i| < ε) ∧ y ∉ A := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x ε hε => (not_mem_interior_iff.mp (h x)) ε hε,
    fun h x => not_mem_interior_iff.mpr (h x)⟩

theorem mem_boxAround_snoc {n : ℕ} {u : Fin n → ℝ} {t : ℝ} {x : Fin (n + 1) → ℝ}
    {ε : ℝ} :
    (Fin.snoc u t : Fin (n + 1) → ℝ) ∈ boxAround x ε ↔
      (∀ i, |u i - Fin.init x i| < ε) ∧ |t - x (Fin.last n)| < ε := by
  rw [mem_boxAround]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castSucc i), by simpa using h (Fin.last n)⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using h2
    · simpa using h1 j

/-! ## 3. Fibres, cylinders and bases -/

/-- The vertical fibre of `A ⊆ ℝ^{n+1}` over the base point `u`. -/
def fibre {n : ℕ} (u : Fin n → ℝ) (A : Set (Fin (n + 1) → ℝ)) : Set ℝ :=
  {t | (Fin.snoc u t : Fin (n + 1) → ℝ) ∈ A}

@[simp] theorem mem_fibre {n : ℕ} {u : Fin n → ℝ} {A : Set (Fin (n + 1) → ℝ)} {t : ℝ} :
    t ∈ fibre u A ↔ (Fin.snoc u t : Fin (n + 1) → ℝ) ∈ A := Iff.rfl

/-- The cylinder over `A ⊆ ℝⁿ` inside `ℝ^{n+1}`. -/
def cyl {n : ℕ} (A : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) := {z | Fin.init z ∈ A}

@[simp] theorem mem_cyl {n : ℕ} {A : Set (Fin n → ℝ)} {z : Fin (n + 1) → ℝ} :
    z ∈ cyl A ↔ Fin.init z ∈ A := Iff.rfl

theorem cyl_mono {n : ℕ} {A B : Set (Fin n → ℝ)} (h : A ⊆ B) : cyl A ⊆ cyl (n := n) B :=
  fun _ hz => h hz

/-- The base of `A ⊆ ℝ^{n+1}`: the projection onto the first `n` coordinates. -/
def base {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) : Set (Fin n → ℝ) := Fin.init '' A

theorem mem_base {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} {u : Fin n → ℝ} :
    u ∈ base A ↔ ∃ z ∈ A, Fin.init z = u := Iff.rfl

theorem base_eq_projLast {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) : base A = projLast A := by
  ext x
  constructor
  · rintro ⟨z, hz, hxz⟩
    refine ⟨z (Fin.last n), ?_⟩
    rw [← hxz, Fin.snoc_init_self]; exact hz
  · rintro ⟨t, ht⟩
    exact ⟨Fin.snoc x t, ht, init_snoc x t⟩

theorem mem_base_iff {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} {u : Fin n → ℝ} :
    u ∈ base A ↔ ∃ t : ℝ, (Fin.snoc u t : Fin (n + 1) → ℝ) ∈ A := by
  rw [mem_base]
  constructor
  · rintro ⟨z, hz, huz⟩
    refine ⟨z (Fin.last n), ?_⟩
    rw [← huz, Fin.snoc_init_self]; exact hz
  · rintro ⟨t, ht⟩
    exact ⟨Fin.snoc u t, ht, init_snoc u t⟩

/-! ## 4. Graph cells -/

/-- `IsGraphCell A` for `A ⊆ ℝ^{n+1}`: `A` is the graph of a function on its own base, i.e.
every vertical fibre of `A` meets `A` in at most one point, and every point of the base has
its corresponding point in `A`. -/
def IsGraphCell {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∃ f : (Fin n → ℝ) → ℝ, ∀ z : Fin (n + 1) → ℝ,
    z ∈ A ↔ (Fin.init z ∈ base A ∧ z (Fin.last n) = f (Fin.init z))

/-- The graph function of a graph cell. -/
def graphFun {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : IsGraphCell A) : (Fin n → ℝ) → ℝ :=
  Classical.choose h

theorem graphFun_spec {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : IsGraphCell A) :
    ∀ z : Fin (n + 1) → ℝ,
      z ∈ A ↔ (Fin.init z ∈ base A ∧ z (Fin.last n) = graphFun h (Fin.init z)) :=
  Classical.choose_spec h

theorem graphFun_mem {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : IsGraphCell A) {z : Fin (n + 1) → ℝ}
    (hz : z ∈ A) : z (Fin.last n) = graphFun h (Fin.init z) :=
  ((graphFun_spec h z).mp hz).2

/-- The fibre of a graph cell has at most one point. -/
theorem fibre_graphCell {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : IsGraphCell A) {u : Fin n → ℝ} :
    fibre u A ⊆ {graphFun h u} := by
  intro t ht
  rw [Set.mem_singleton_iff]
  have hz : (Fin.snoc u t : Fin (n + 1) → ℝ) ∈ A := ht
  have h2 := graphFun_mem h hz
  rwa [init_snoc, snoc_last] at h2

theorem base_graph {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} :
    base {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = C := by
  ext u
  constructor
  · rintro ⟨z, hz, huz⟩
    rw [← huz]; exact hz.1
  · intro hu
    exact ⟨Fin.snoc u (f u), ⟨by simpa using hu, by simp⟩, init_snoc u (f u)⟩

theorem isGraphCell_of_graph {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} :
    IsGraphCell {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  refine ⟨f, fun z => ?_⟩
  rw [base_graph]
  exact Iff.rfl

theorem base_band {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (hab : ∀ x ∈ C, a x < b x) :
    base {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = C := by
  ext u
  constructor
  · rintro ⟨z, hz, huz⟩
    rw [← huz]; exact hz.1
  · intro hu
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab u hu)
    exact ⟨Fin.snoc u t, ⟨by simpa using hu, by simpa using ht1, by simpa using ht2⟩,
      init_snoc u t⟩

/-- A band cell over a nonempty base is not a graph over its base: its fibres contain two
distinct points. -/
theorem not_isGraphCell_of_band {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (hC : IsCell n C) (hab : ∀ x ∈ C, a x < b x) :
    ¬ IsGraphCell {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  rintro ⟨f, hf⟩
  obtain ⟨u, hu⟩ := Work.WilkiesH.Cell.isCell_nonempty hC
  obtain ⟨t₁, ht1a, ht1b⟩ := EReal.lt_iff_exists_real_btwn.mp (hab u hu)
  obtain ⟨t₂, ht2a, ht2b⟩ := EReal.lt_iff_exists_real_btwn.mp ht1b
  have hz₁ : (Fin.snoc u t₁ : Fin (n + 1) → ℝ) ∈
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} :=
    ⟨by simpa using hu, by simpa using ht1a, by simpa using ht1b⟩
  have hz₂ : (Fin.snoc u t₂ : Fin (n + 1) → ℝ) ∈
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} :=
    ⟨by simpa using hu, by simpa using lt_trans ht1a ht2a, by simpa using ht2b⟩
  have h₁ : t₁ = f u := by simpa using ((hf (Fin.snoc u t₁)).mp hz₁).2
  have h₂ : t₂ = f u := by simpa using ((hf (Fin.snoc u t₂)).mp hz₂).2
  have hlt : t₁ < t₂ := by
    have : ((t₁ : ℝ) : EReal) < ((t₂ : ℝ) : EReal) := ht2a
    exact_mod_cast this
  rw [h₁, h₂] at hlt
  exact lt_irrefl _ hlt

/-! ## 5. The bad (thin) part of a set -/

/-- The "bad" (thin) part of `A ⊆ ℝⁿ`, defined by recursion on `n`: a graph cell is entirely
bad; a band cell is bad over the bad part of its base. -/
def badCell : (n : ℕ) → Set (Fin n → ℝ) → Set (Fin n → ℝ)
  | 0, _ => ∅
  | n + 1, A => if IsGraphCell A then A else A ∩ cyl (badCell n (base A))

theorem badCell_zero (A : Set (Fin 0 → ℝ)) : badCell 0 A = ∅ := rfl

theorem badCell_succ {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    badCell (n + 1) A = if IsGraphCell A then A else A ∩ cyl (badCell n (base A)) := rfl

theorem badCell_of_graph {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : IsGraphCell A) :
    badCell (n + 1) A = A := by
  rw [badCell_succ]; simp [h]

theorem badCell_of_not_graph {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (h : ¬ IsGraphCell A) :
    badCell (n + 1) A = A ∩ cyl (badCell n (base A)) := by
  rw [badCell_succ]; simp [h]

theorem badCell_subset {n : ℕ} (A : Set (Fin n → ℝ)) : badCell n A ⊆ A := by
  rcases n with _ | n
  · rw [badCell_zero]; exact Set.empty_subset _
  · by_cases h : IsGraphCell A
    · rw [badCell_of_graph h]
    · rw [badCell_of_not_graph h]; exact Set.inter_subset_left

/-- The union of the bad parts of the cells of a finite family of cells. -/
def badUnion {n : ℕ} (CD : Finset (Set (Fin n → ℝ))) : Set (Fin n → ℝ) :=
  ⋃ κ ∈ CD, badCell n κ

theorem mem_badUnion {n : ℕ} {CD : Finset (Set (Fin n → ℝ))} {x : Fin n → ℝ} :
    x ∈ badUnion CD ↔ ∃ κ ∈ CD, x ∈ badCell n κ := by
  simp [badUnion]

/-- The union of the graph cells of a finite family of cells. -/
def graphPart {n : ℕ} (CD : Finset (Set (Fin (n + 1) → ℝ))) : Set (Fin (n + 1) → ℝ) :=
  {z | ∃ κ ∈ CD, IsGraphCell κ ∧ z ∈ κ}

/-! ## 6. The frontier part -/

/-- `Fr A`: the points of `A` every box around which contains a point outside `A`. -/
def Fr {n : ℕ} (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | x ∈ A ∧ ∀ ε > 0, ∃ y : Fin n → ℝ, (∀ i, |y i - x i| < ε) ∧ y ∉ A}

theorem mem_Fr {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ Fr A ↔ x ∈ A ∧ ∀ ε > 0, ∃ y : Fin n → ℝ, (∀ i, |y i - x i| < ε) ∧ y ∉ A :=
  Iff.rfl

theorem Fr_subset {n : ℕ} (A : Set (Fin n → ℝ)) : Fr A ⊆ A := fun _ hx => hx.1

theorem notMem_interior_of_mem_Fr {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ Fr A) : x ∉ interior A :=
  not_mem_interior_iff.mpr hx.2

theorem mem_Fr_of_mem_notMem_interior {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ A) (h : x ∉ interior A) : x ∈ Fr A :=
  ⟨hx, not_mem_interior_iff.mp h⟩

end Work.WilkiesH.Strat
