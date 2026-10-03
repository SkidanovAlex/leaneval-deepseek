/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The `Z`-domain window of the `Z`-cover of a one-relator complex

This file is the first, purely combinatorial, stage of the `Z`-domain route to
`Work.OROneRel.magnus_step_root_no_eps_zero` (see
`Submission/Work/OROneRel/NOTES_magnus_step_root_no_eps_zero.md`, SESSION 8 §5, for the shape of the
argument).  It contains definitions and the elementary facts, so that lemma requests may import it.

## The level graph

Fix a weight `c : α → ℤ`.  The `Z`-cover `Y` of the one-relator complex of `⟨α | u^l⟩` associated
with the character `χ (x) = c x` (for `c` with `Σ c x * eps x u = 0` and `gcd c = 1`) has

* vertices the levels `ℤ`;
* one edge `(x,i)` from level `i` to level `i + c x`, for every generator `x` and level `i`;
* one `2`-cell at every level `i`, attached along the lift of `u^l` based at `i` — a *closed* walk
  precisely because `Σ c x * eps x u = 0`.

The deck transformation `t` sends the level `i` to `i + 1`, hence the edge `(x,i)` to `(x,i+1)`.

## The window

`winEdge c N` is the set of edges of `Y` with both endpoints in the level window `[0,N]`; the
subcomplex it spans (together with the `2`-cells whose attaching walk is supported there) is
Linton's `Z`-domain as soon as `N` is large enough — Linton, *One-relator hierarchies*,
arXiv 2202.11324, Prop. 4.9 (`tree_existence`), specialised to a rose.  The three `Z`-domain axioms
are listed in `IsZDomain`.

The *content* of the route is the splitting `G ≅ HNN (π₁ D, π₁ (D ∩ tD), π₁ (D ∩ tD), conj_t)` of
Linton Prop. 2.2.19, which is not formalised here.
-/
import Mathlib

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The level graph of the `Z`-cover -/

/-- The (undirected) edges of the `Z`-cover of the rose on `α`: the edge `(x,i)` runs from level `i`
to level `i + c x`. -/
abbrev LvEdge (α : Type u) := α × ℤ

/-- The source level of the edge `(x,i)`. -/
def lvSrc (_c : α → ℤ) (e : LvEdge α) : ℤ := e.2

/-- The target level of the edge `(x,i)`. -/
def lvTgt (c : α → ℤ) (e : LvEdge α) : ℤ := e.2 + c e.1

@[simp] theorem lvSrc_def (c : α → ℤ) (e : LvEdge α) : lvSrc c e = e.2 := rfl
@[simp] theorem lvTgt_def (c : α → ℤ) (e : LvEdge α) : lvTgt c e = e.2 + c e.1 := rfl

/-- The deck transformation: the translate `t ^ k · (x,i) = (x, i+k)`. -/
def lvShift (k : ℤ) (e : LvEdge α) : LvEdge α := (e.1, e.2 + k)

@[simp] theorem lvShift_fst (k : ℤ) (e : LvEdge α) : (lvShift k e).1 = e.1 := rfl
@[simp] theorem lvShift_snd (k : ℤ) (e : LvEdge α) : (lvShift k e).2 = e.2 + k := rfl

@[simp] theorem lvSrc_shift (c : α → ℤ) (k : ℤ) (e : LvEdge α) :
    lvSrc c (lvShift k e) = lvSrc c e + k := rfl

@[simp] theorem lvTgt_shift (c : α → ℤ) (k : ℤ) (e : LvEdge α) :
    lvTgt c (lvShift k e) = lvTgt c e + k := by simp [lvTgt, lvShift]; ring

@[simp] theorem lvShift_zero (e : LvEdge α) : lvShift 0 e = e := by simp [lvShift]

theorem lvShift_add (k l : ℤ) (e : LvEdge α) : lvShift k (lvShift l e) = lvShift (k + l) e := by
  ext <;> simp [lvShift] <;> ring

/-- The set of levels spanned by a set of edges. -/
def lvLevels (c : α → ℤ) (D : Set (LvEdge α)) : Set ℤ :=
  {i | ∃ e ∈ D, lvSrc c e = i ∨ lvTgt c e = i}

/-! ## Windows of levels -/

/-- **The window of width `N`**: the edges of the cover whose two endpoints both lie in `[0,N]`. -/
def winEdge (c : α → ℤ) (N : ℤ) (e : LvEdge α) : Prop := 0 ≤ e.2 ∧ e.2 + c e.1 ≤ N

/-- The translate `t^k e = (x, e.2 + k)` of a window edge lies in the window `[0,N]` exactly when its
source `e.2 + k` is `≥ 0` and its target `e.2 + k + c x` is `≤ N`.  This is the elementary form of
"the translates of a window are windows", which makes the nestedness axiom of a `Z`-domain automatic
for windows. -/
theorem winEdge_shift_iff {c : α → ℤ} {N : ℤ} {e : LvEdge α} {k : ℤ} :
    winEdge c N (lvShift k e) ↔ 0 ≤ e.2 + k ∧ e.2 + c e.1 ≤ N - k := by
  simp only [winEdge, lvShift_snd, lvShift_fst]
  constructor <;> intro h <;> exact ⟨h.1, by omega⟩

/-- **Every edge orbit of the cover meets a long enough window**: for `N ≥ max_x |c x|` the edge
`(x, i)` with `i = 0` (if `c x ≥ 0`) or `i = -c x` (otherwise) has both endpoints in `[0,N]`. -/
theorem winEdge_covers {c : α → ℤ} {N : ℤ} (hN : ∀ x : α, |c x| ≤ N) (x : α) :
    ∃ i : ℤ, winEdge c N (x, i) := by
  have hcx : -(N) ≤ c x ∧ c x ≤ N := abs_le.mp (hN x)
  by_cases h : 0 ≤ c x
  · exact ⟨0, by simp only [winEdge]; omega⟩
  · refine ⟨-c x, ?_⟩
    simp only [winEdge]
    constructor <;> omega

/-- **The nestedness axiom for windows**: if the translate `t^i e` of an edge of the window still
lies in the window (i.e. `t^i e ∈ D ∩ t^i D` for `i ≥ 1`), then so does `t^j e` for every
`1 ≤ j ≤ i` — the translated windows `[k, N+k] ∩ [0,N] = [k,N]` shrink with `k`. -/
theorem winEdge_nested {c : α → ℤ} {N : ℤ} {e : LvEdge α} (he : winEdge c N e) {i : ℤ}
    (hiD : winEdge c N (lvShift i e)) :
    ∀ j : ℤ, 1 ≤ j → j ≤ i → winEdge c N (lvShift j e) := by
  intro j hj hji
  simp only [winEdge] at he
  rw [winEdge_shift_iff] at hiD ⊢
  exact ⟨by omega, by omega⟩

/-- `D ∩ tD` for the window: since `e ∈ tD` means `t^{-1} e ∈ D`, the intersection consists exactly
of the window edges whose source level is `≥ 1`.  (This is the window `[1,N]`.) -/
theorem winEdge_inter {c : α → ℤ} {N : ℤ} {e : LvEdge α} :
    (winEdge c N e ∧ winEdge c N (lvShift (-1) e)) ↔ 1 ≤ e.2 ∧ e.2 + c e.1 ≤ N := by
  rw [winEdge_shift_iff]
  simp only [winEdge]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, -⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, h2⟩, by omega, by omega⟩

/-- The window `[1,N]` (`= D ∩ tD`) is non-empty as soon as `N ≥ 1` and there is a *negatively*
weighted generator — which is automatic for the weights of the route, where `Σ c x * eps x u = 0`
and all `eps x u ≠ 0` force the signs of `c` to be mixed. -/
theorem winEdge_inter_nonempty {c : α → ℤ} {N : ℤ} (hN : 1 ≤ N) {x : α} (hx : c x < 0) :
    ∃ e : LvEdge α, winEdge c N e ∧ winEdge c N (lvShift (-1) e) :=
  ⟨(x, 1), by
    rw [winEdge_inter]
    refine ⟨le_refl 1, ?_⟩
    show (1 : ℤ) + c x ≤ N
    omega⟩

/-! ## Connectivity of the intersection, and `Z`-domains -/

/-- Levels `l` and `m` are joined by a chain of edges of `S`. -/
def lvJoined (c : α → ℤ) (S : Set (LvEdge α)) (l m : ℤ) : Prop :=
  Relation.ReflTransGen
    (fun a b : ℤ => ∃ e ∈ S, (lvSrc c e = a ∧ lvTgt c e = b) ∨ (lvSrc c e = b ∧ lvTgt c e = a))
    l m

/-- **A `Z`-domain of the level graph** (Linton, arXiv 2202.11324, §3), specialised to the cover of
a rose.  `D` is a set of edges such that

1. every edge orbit of the cover meets `D` (`Z · D = Y`);
2. the intersections with the translates are nested: `D ∩ t^i D ⊆ D ∩ tD ∩ … ∩ t^i D` for `i > 0`;
3. `D ∩ t D` is non-empty and connected (its levels are joined by its edges). -/
structure IsZDomain (c : α → ℤ) (D : Set (LvEdge α)) : Prop where
  /-- (cdt1) every edge orbit of the cover meets `D`. -/
  covers : ∀ x : α, ∃ i : ℤ, (x, i) ∈ D
  /-- (cdt2) the intersections with the translates are nested. -/
  nested : ∀ e ∈ D, ∀ i : ℤ, 1 ≤ i → lvShift (-i) e ∈ D →
    ∀ j : ℤ, 1 ≤ j → j ≤ i → lvShift (-j) e ∈ D
  /-- (cdt3a) `D ∩ tD` is non-empty. -/
  inter_nonempty : ∃ e : LvEdge α, e ∈ D ∧ lvShift (-1) e ∈ D
  /-- (cdt3b) `D ∩ tD` is connected. -/
  inter_connected : ∀ l m : ℤ,
    l ∈ lvLevels c {e | e ∈ D ∧ lvShift (-1) e ∈ D} →
    m ∈ lvLevels c {e | e ∈ D ∧ lvShift (-1) e ∈ D} →
    lvJoined c {e | e ∈ D ∧ lvShift (-1) e ∈ D} l m

end Work.OROneRel
