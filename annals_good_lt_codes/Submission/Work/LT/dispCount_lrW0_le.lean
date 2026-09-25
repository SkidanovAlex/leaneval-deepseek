import Mathlib
import Submission.Work.LT.lr_sound_defs

/-!
# `dispCount (lrW0 …) ≤ 2 Δ |rejectSet …|`

The initial assignment `lrW0` of the DELLM local-search algorithm agrees, at every vertex
whose true local view is already a tensor codeword, with that true view, and is `0` at the
remaining ("rejecting") vertices.

The geometric point is that a disputed edge always has a rejecting endpoint.  An `A`-edge
`(β,g,i)` joins the vertices `(0,β,g)` and `(1,β,A i * g)`, whose *true* local views agree
on row `i` (`lrView_row`): so if the two assigned views disagreed there, one of the two
vertices must have replaced its true view by `0`, i.e. must be rejecting.  There are `Δ`
`A`-edges through a given vertex (one per label `i`) and `Δ` `B`-edges, so the number of
disputed `A`-edges is at most `Δ · |rejectSet|`, and similarly for the `B`-edges; the total
is at most `2 Δ |rejectSet|`.

We prove the two counting statements by exhibiting an *injection* from the disputed `A`-edges
(resp. `B`-edges) into `rejectSet × Fin Δ`: pick a rejecting endpoint (the first one if it is
rejecting, otherwise the second, which is then forced to be rejecting by the lemma above) and
remember the label.  The injection is inverted by `arejInv` (resp. `brejInv`), which recovers
the edge from its rejecting endpoint and its label.
-/

namespace Work.LT

open Classical

variable {G : Type} [Group G] {Δ : ℕ}

/-- Every disputed `A`-edge has a rejecting endpoint: the `A`-edge `(β,g,i)` is disputed only
if `(0,β,g)` or `(1,β,A i * g)` is rejecting. -/
lemma reject_of_disputeA [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (β : Fin 2) (g : G) (i : Fin Δ)
    (h : disputeA A (lrW0 A B CA CB f) β g i) :
    ((0 : Fin 2), β, g) ∈ rejectSet A B CA CB f ∨
      ((1 : Fin 2), β, A i * g) ∈ rejectSet A B CA CB f := by
  rcases h with ⟨j, hj⟩
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h0, h1⟩ := hc
  rw [lrW0_eq_view_of_not_mem_rejectSet A B CA CB f (0, β, g) h0,
      lrW0_eq_view_of_not_mem_rejectSet A B CA CB f (1, β, A i * g) h1] at hj
  exact hj (lrView_row A B β g i j f)

/-- Every disputed `B`-edge has a rejecting endpoint: the `B`-edge `(α,g,j)` is disputed only
if `(α,0,g)` or `(α,1,g * B j)` is rejecting. -/
lemma reject_of_disputeB [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (α : Fin 2) (g : G) (j : Fin Δ)
    (h : disputeB B (lrW0 A B CA CB f) α g j) :
    ((α, (0 : Fin 2), g) : Fin 2 × Fin 2 × G) ∈ rejectSet A B CA CB f ∨
      ((α, (1 : Fin 2), g * B j) : Fin 2 × Fin 2 × G) ∈ rejectSet A B CA CB f := by
  rcases h with ⟨i, hi⟩
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h0, h1⟩ := hc
  rw [lrW0_eq_view_of_not_mem_rejectSet A B CA CB f (α, 0, g) h0,
      lrW0_eq_view_of_not_mem_rejectSet A B CA CB f (α, 1, g * B j) h1] at hi
  exact hi (lrView_col A B α g i j f)

/-- For an `A`-edge `p = (β,g,i)` marked with a set `R` of vertices, send it to the
type-`0` endpoint `(0,β,g)` together with the label `i` if that endpoint lies in `R`, and to
the type-`1` endpoint `(1,β,A i * g)` together with `i` otherwise. -/
noncomputable def arejMap (A : Fin Δ → G) (R : Finset (Fin 2 × Fin 2 × G))
    (p : Fin 2 × G × Fin Δ) : (Fin 2 × Fin 2 × G) × Fin Δ :=
  if (((0 : Fin 2), p.1, p.2.1) ∈ R) then ((((0 : Fin 2), p.1, p.2.1)), p.2.2)
  else ((((1 : Fin 2), p.1, A p.2.2 * p.2.1)), p.2.2)

/-- Inverse of `arejMap` on the disputed `A`-edges: from a vertex `v = (α,β,g')` and a label
`i`, recover the `A`-edge of label `i` having `v` as endpoint. -/
noncomputable def arejInv (A : Fin Δ → G) (v : Fin 2 × Fin 2 × G) (i : Fin Δ) :
    Fin 2 × G × Fin Δ :=
  if v.1 = 0 then (v.2.1, v.2.2, i) else (v.2.1, (A i)⁻¹ * v.2.2, i)

/-- For a `B`-edge `p = (α,g,j)` marked with a set `R` of vertices, send it to the
type-`0` endpoint `(α,0,g)` together with the label `j` if that endpoint lies in `R`, and to
the type-`1` endpoint `(α,1,g * B j)` together with `j` otherwise. -/
noncomputable def brejMap (B : Fin Δ → G) (R : Finset (Fin 2 × Fin 2 × G))
    (p : Fin 2 × G × Fin Δ) : (Fin 2 × Fin 2 × G) × Fin Δ :=
  if (((p.1, (0 : Fin 2), p.2.1)) ∈ R) then (((p.1, (0 : Fin 2), p.2.1)), p.2.2)
  else (((p.1, (1 : Fin 2), p.2.1 * B p.2.2)), p.2.2)

/-- Inverse of `brejMap` on the disputed `B`-edges. -/
noncomputable def brejInv (B : Fin Δ → G) (v : Fin 2 × Fin 2 × G) (j : Fin Δ) :
    Fin 2 × G × Fin Δ :=
  if v.2.1 = 0 then (v.1, v.2.2, j) else (v.1, v.2.2 * (B j)⁻¹, j)

/-- `arejInv` inverts `arejMap` on disputed `A`-edges. -/
lemma arejInv_arejMap [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (p : Fin 2 × G × Fin Δ)
    (hp : p ∈ Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)) :
    arejInv A (arejMap A (rejectSet A B CA CB f) p).1
      (arejMap A (rejectSet A B CA CB f) p).2 = p := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  by_cases h0 : ((0 : Fin 2), p.1, p.2.1) ∈ rejectSet A B CA CB f
  · simp [arejMap, arejInv, h0]
  · have h1 : ((1 : Fin 2), p.1, A p.2.2 * p.2.1) ∈ rejectSet A B CA CB f :=
      (reject_of_disputeA A B CA CB f p.1 p.2.1 p.2.2 hp).resolve_left h0
    simp [arejMap, arejInv, h0]

/-- `brejInv` inverts `brejMap` on disputed `B`-edges. -/
lemma brejInv_brejMap [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (p : Fin 2 × G × Fin Δ)
    (hp : p ∈ Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)) :
    brejInv B (brejMap B (rejectSet A B CA CB f) p).1
      (brejMap B (rejectSet A B CA CB f) p).2 = p := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  by_cases h0 : ((p.1, (0 : Fin 2), p.2.1) : Fin 2 × Fin 2 × G) ∈ rejectSet A B CA CB f
  · simp [brejMap, brejInv, h0]
  · have h1 : ((p.1, (1 : Fin 2), p.2.1 * B p.2.2) : Fin 2 × Fin 2 × G) ∈
        rejectSet A B CA CB f :=
      (reject_of_disputeB A B CA CB f p.1 p.2.1 p.2.2 hp).resolve_left h0
    simp [brejMap, brejInv, h0]

/-- The disputed `A`-edges number at most `Δ · |rejectSet|`: they inject into
`rejectSet × Fin Δ`. -/
lemma card_disputeA_lrW0_le [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card
      ≤ (rejectSet A B CA CB f).card * Δ := by
  classical
  set R := rejectSet A B CA CB f
  have hmaps : ∀ p ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      arejMap A R p ∈ (R ×ˢ (Finset.univ : Finset (Fin Δ))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : ((0 : Fin 2), p.1, p.2.1) ∈ R
    · simp [arejMap, h0]
    · have h1 : ((1 : Fin 2), p.1, A p.2.2 * p.2.1) ∈ R :=
        (reject_of_disputeA A B CA CB f p.1 p.2.1 p.2.2 hp).resolve_left h0
      simp [arejMap, h0, h1]
  have hinj : ∀ p ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      ∀ q ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      arejMap A R p = arejMap A R q → p = q := by
    intro p hp q hq heq
    rw [← arejInv_arejMap A B CA CB f p hp, heq, arejInv_arejMap A B CA CB f q hq]
  have hcard := Finset.card_le_card_of_injOn (arejMap A R) hmaps hinj
  have h2 : (R ×ˢ (Finset.univ : Finset (Fin Δ))).card = R.card * Δ := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  omega

/-- The disputed `B`-edges number at most `Δ · |rejectSet|`: they inject into
`rejectSet × Fin Δ`. -/
lemma card_disputeB_lrW0_le [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card
      ≤ (rejectSet A B CA CB f).card * Δ := by
  classical
  set R := rejectSet A B CA CB f
  have hmaps : ∀ p ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      brejMap B R p ∈ (R ×ˢ (Finset.univ : Finset (Fin Δ))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : ((p.1, (0 : Fin 2), p.2.1) : Fin 2 × Fin 2 × G) ∈ R
    · simp [brejMap, h0]
    · have h1 : ((p.1, (1 : Fin 2), p.2.1 * B p.2.2) : Fin 2 × Fin 2 × G) ∈ R :=
        (reject_of_disputeB A B CA CB f p.1 p.2.1 p.2.2 hp).resolve_left h0
      simp [brejMap, h0, h1]
  have hinj : ∀ p ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      ∀ q ∈ (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)),
      brejMap B R p = brejMap B R q → p = q := by
    intro p hp q hq heq
    rw [← brejInv_brejMap A B CA CB f p hp, heq, brejInv_brejMap A B CA CB f q hq]
  have hcard := Finset.card_le_card_of_injOn (brejMap B R) hmaps hinj
  have h2 : (R ×ˢ (Finset.univ : Finset (Fin Δ))).card = R.card * Δ := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  omega

/-- The initial assignment of the DELLM local-search algorithm has at most `2 Δ |rejectSet|`
disputed edges: every disputed edge has a rejecting endpoint, and a vertex is an endpoint of
at most `Δ` `A`-edges and at most `Δ` `B`-edges. -/
lemma dispCount_lrW0_le {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2) :
    Work.LT.dispCount A B (Work.LT.lrW0 A B CA CB f) ≤
      2 * Δ * (Work.LT.rejectSet A B CA CB f).card := by
  have hA := card_disputeA_lrW0_le A B CA CB f
  have hB := card_disputeB_lrW0_le A B CA CB f
  have hsum : dispCount A B (lrW0 A B CA CB f) =
      (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card +
      (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
        disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card := rfl
  rw [hsum]
  calc (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
          disputeA A (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card +
        (Finset.univ.filter (fun p : Fin 2 × G × Fin Δ =>
          disputeB B (lrW0 A B CA CB f) p.1 p.2.1 p.2.2)).card
      ≤ (rejectSet A B CA CB f).card * Δ + (rejectSet A B CA CB f).card * Δ :=
        Nat.add_le_add hA hB
    _ = 2 * Δ * (rejectSet A B CA CB f).card := by ring

end Work.LT
