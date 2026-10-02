import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleSetup
import Submission.Work.Deep.Prob.LLL.lovaszLocalLemma_symmetric
import Submission.Work.Deep.Prob.LLL.lll_exists
import Submission.Work.Deep.Prob.Spaces
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Conc.prob_inter_eq_mul_of_determined
import Submission.Work.Deep.Kahn.lllPolyBound

/-!
# The Lovász-local-lemma step of the regularised one-round nibble

`Work.Deep.Kahn.nibbleExistsGood` is the step of the proof of the regularised one-round
nibble (`Work.Deep.Kahn.nibbleRegularised`) that produces a *single* round outcome `ω`
satisfying both per-round estimates.  Two families of bad events are considered:

* `A e` (one for every edge `e`): `e` is not kept in the round, and more than
  `Λ (1 - s) + η Λ` colours of its list are used at `e`;
* `B (x,γ)` (one for every pair `(x,γ)` that occurs, i.e. `γ ∈ L e` for some `e ∋ x`):
  the number of edges through `x` carrying `γ` that are coloured or that have `γ` used at
  them is less than `D - (newDeg + ηD)`.

The two hypotheses of `nibbleExistsGood` give each of these events probability at most
`exp (-D ^ (1/4))`.  The conclusion is that some outcome avoids all of them: this is the
Lovász local lemma, and the dependence structure is provided by the *finite supports*

* `supp1 e = {e} ∪ ovNbrs e`, where `ovNbrs e` consists of the edges `f ≠ e` meeting `e`
  whose list meets `L e`: the predicate `Round.kept ω e` depends only on the coordinates
  of the edges in `supp1 e` (an edge with a disjoint list can never block `e`);
* `supp2 e = ⋃_{f ∈ supp1 e} supp1 f`, the support of the `A`-event at `e`;
* `suppPair x γ = ⋃_{f ∈ colThru x γ} supp2 f`, the support of the `B`-event at `(x,γ)`.

The size of the support of an event and the number of events whose support meets a given
edge are both polynomial in `C` and `D`: every bound is a union bound over vertices, and the
only input is the regularised colour-degree hypothesis, which says that through a vertex `x`
a colour `γ` lies in the list of exactly `D` edges (`C Λ D` for the `C`-vertex edge `e` with
its `Λ` colours, and `C Λ` for the pairs `(x,γ)` with `γ ∈ L e`, `x ∈ e`).  Hence the
symmetric Lovász local lemma applies.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}
variable {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
variable {L : 𝓗 → Finset (Fin c)}

/- The auxiliary vocabulary of the Lovász-local-lemma step lives in its own namespace, to
avoid any clash with other modules defining similarly named objects. -/
namespace NibbleLLL

/-! ## The dependence structure of the round -/

/-- The edges `f ≠ e` meeting `e` whose list meets the list of `e`. -/
def ovNbrs (e : 𝓗) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ (L f ∩ L e).Nonempty)

/-- The one-step support of the predicate `Round.kept ω e`: `e` itself together with the
edges that can block it. -/
def supp1 (e : 𝓗) : Finset 𝓗 := insert e (ovNbrs (L := L) e)

/-- The two-step support of the `A`-event at `e`. -/
def supp2 (e : 𝓗) : Finset 𝓗 := (supp1 (L := L) e).biUnion (fun f => supp1 (L := L) f)

/-- The edges through `x` whose list contains `γ`. -/
def colThru (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => x ∈ (f : Set (Fin n)) ∧ γ ∈ L f)

/-- The support of the `B`-event at the pair `(x,γ)`. -/
def suppPair (x : Fin n) (γ : Fin c) : Finset 𝓗 :=
  (colThru (L := L) x γ).biUnion (fun f => supp2 (L := L) f)

lemma mem_ovNbrs {e f : 𝓗} :
    f ∈ ovNbrs (L := L) e ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ (L f ∩ L e).Nonempty := by
  classical
  simp [ovNbrs]

lemma mem_supp1 {e f : 𝓗} :
    f ∈ supp1 (L := L) e ↔ f = e ∨ (f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ (L f ∩ L e).Nonempty) := by
  classical
  rw [supp1, Finset.mem_insert, mem_ovNbrs]

lemma mem_supp2 {e f : 𝓗} :
    f ∈ supp2 (L := L) e ↔ ∃ g ∈ supp1 (L := L) e, f ∈ supp1 (L := L) g := by
  classical
  simp [supp2]

lemma mem_colThru {x : Fin n} {γ : Fin c} {f : 𝓗} :
    f ∈ colThru (L := L) x γ ↔ x ∈ (f : Set (Fin n)) ∧ γ ∈ L f := by
  classical
  simp [colThru]

lemma mem_suppPair {x : Fin n} {γ : Fin c} {f : 𝓗} :
    f ∈ suppPair (L := L) x γ ↔ ∃ g ∈ colThru (L := L) x γ, f ∈ supp2 (L := L) g := by
  classical
  simp [suppPair]

/-- A member of `supp1 e` has its own one-step support inside `supp2 e`. -/
lemma supp1_subset_supp2 {e f : 𝓗} (hf : f ∈ supp1 (L := L) e) :
    supp1 (L := L) f ⊆ supp2 (L := L) e :=
  fun _ hg => mem_supp2.mpr ⟨f, hf, hg⟩

lemma supp1_subset_supp2_self (e : 𝓗) : supp1 (L := L) e ⊆ supp2 (L := L) e :=
  supp1_subset_supp2 (Finset.mem_insert_self e _)

/-- The one-step support of a member of `colThru x γ` sits inside `suppPair x γ`. -/
lemma supp2_subset_suppPair {x : Fin n} {γ : Fin c} {f : 𝓗}
    (hf : f ∈ colThru (L := L) x γ) :
    supp2 (L := L) f ⊆ suppPair (L := L) x γ :=
  fun _ hg => mem_suppPair.mpr ⟨f, hf, hg⟩

/-! ## The predicate `Round.kept` depends only on the one-step support -/

section Kept

variable {K : ℕ} [NeZero K]

/-- The activation of `e` depends only on the coordinate of `e`. -/
lemma active_congr {ω ω' : Round.Space K 𝓗 L} {e : 𝓗} (h : ω e = ω' e) :
    Round.active ω e ↔ Round.active ω' e := by
  unfold Round.active
  rw [h]

/-- The colour of `e` depends only on the coordinate of `e`. -/
lemma colour_congr {ω ω' : Round.Space K 𝓗 L} {e : 𝓗} (h : ω e = ω' e) :
    Round.colour ω e = Round.colour ω' e := by
  unfold Round.colour
  rw [h]

/-- An edge outside the one-step support of `e` and `≠ e` meets `e` in a vertex but has a
list disjoint from the list of `e`. -/
lemma inter_empty_of_not_mem_supp1 {e g : 𝓗} (hg : g ∉ supp1 (L := L) e) (hge : g ≠ e)
    (hm : ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) : L g ∩ L e = ∅ := by
  classical
  by_contra hne
  exact hg (mem_supp1.mpr (Or.inr ⟨hge, hm, Finset.nonempty_iff_ne_empty.mpr hne⟩))

/-- Colours of edges with disjoint lists are distinct. -/
lemma colour_ne_of_inter_empty {ω : Round.Space K 𝓗 L} {e g : 𝓗} (h : L g ∩ L e = ∅) :
    Round.colour ω g ≠ Round.colour ω e := by
  intro hc
  have h1 : Round.colour ω g ∈ L g := Round.colour_mem ω g
  have h2 : Round.colour ω e ∈ L e := Round.colour_mem ω e
  have h2' : Round.colour ω g ∈ L e := by rw [hc]; exact h2
  have hmem : Round.colour ω g ∈ L g ∩ L e := Finset.mem_inter.mpr ⟨h1, h2'⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

/-- **`Round.kept ω e` depends only on the coordinates in `supp1 e`.** -/
theorem kept_congr {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ supp1 (L := L) e, ω g = ω' g) : (Round.kept ω e ↔ Round.kept ω' e) := by
  classical
  have he : e ∈ supp1 (L := L) e := Finset.mem_insert_self e _
  have hact := active_congr (h e he)
  have hcol := colour_congr (h e he)
  rw [Round.kept_iff, Round.kept_iff]
  constructor
  · rintro ⟨hactω, h2⟩
    refine ⟨hact.mp hactω, fun g hge hmeet hactg hcolg => ?_⟩
    by_cases hgs : g ∈ supp1 (L := L) e
    · have hga : Round.active ω g ↔ Round.active ω' g := active_congr (h g hgs)
      have hgc : Round.colour ω g = Round.colour ω' g := colour_congr (h g hgs)
      refine h2 g hge hmeet (hga.mpr hactg) ?_
      rw [hgc, hcolg, hcol]
    · have hemp : L g ∩ L e = ∅ := inter_empty_of_not_mem_supp1 hgs hge hmeet
      exact colour_ne_of_inter_empty (ω := ω') hemp hcolg
  · rintro ⟨hactω, h2⟩
    refine ⟨hact.mpr hactω, fun g hge hmeet hactg hcolg => ?_⟩
    by_cases hgs : g ∈ supp1 (L := L) e
    · have hga : Round.active ω g ↔ Round.active ω' g := active_congr (h g hgs)
      have hgc : Round.colour ω g = Round.colour ω' g := colour_congr (h g hgs)
      refine h2 g hge hmeet (hga.mp hactg) ?_
      rw [← hgc, hcolg, hcol]
    · have hemp : L g ∩ L e = ∅ := inter_empty_of_not_mem_supp1 hgs hge hmeet
      exact colour_ne_of_inter_empty (ω := ω) hemp hcolg

end Kept

/-! ## The colours used at an edge depend only on the two-step support -/

section Used

variable {K : ℕ} [NeZero K]

/-- Membership in `usedColours` phrased with an explicit witness edge. -/
lemma mem_usedColours_iff (ω : Round.Space K 𝓗 L) (e : 𝓗) (γ : Fin c) :
    γ ∈ Round.usedColours ω e ↔ ∃ f : 𝓗, Round.kept ω f ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ Round.colour ω f = γ := by
  classical
  rw [Round.usedColours, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hc⟩
    rw [Finset.mem_filter] at hf
    exact ⟨f, hf.2.1, hf.2.2, hc⟩
  · rintro ⟨f, hk, hm, hc⟩
    exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hk, hm⟩, hc⟩

/-- **The colours of `L e` used at `e` depend only on the coordinates in `supp2 e`.** -/
lemma inter_usedColours_congr {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ supp2 (L := L) e, ω g = ω' g) :
    L e ∩ Round.usedColours ω e = L e ∩ Round.usedColours ω' e := by
  classical
  ext γ
  rw [Finset.mem_inter, Finset.mem_inter]
  constructor
  · rintro ⟨hγ, hwit⟩
    obtain ⟨f, hk, hmeet, hcol⟩ := (mem_usedColours_iff ω e γ).mp hwit
    have hf1 : f ∈ supp1 (L := L) e := by
      by_cases hfe : f = e
      · exact mem_supp1.mpr (Or.inl hfe)
      · exact mem_supp1.mpr (Or.inr ⟨hfe, hmeet,
          ⟨γ, Finset.mem_inter.mpr ⟨by rw [← hcol]; exact Round.colour_mem ω f, hγ⟩⟩⟩)
    have hf2 : f ∈ supp2 (L := L) e := supp1_subset_supp2_self e hf1
    have hk' : Round.kept ω' f :=
      (kept_congr (fun g hg => h g (supp1_subset_supp2 hf1 hg))).mp hk
    have hcol' : Round.colour ω' f = γ := by
      rw [← hcol]; exact (colour_congr (h f hf2)).symm
    exact ⟨hγ, (mem_usedColours_iff ω' e γ).mpr ⟨f, hk', hmeet, hcol'⟩⟩
  · rintro ⟨hγ, hwit⟩
    obtain ⟨f, hk, hmeet, hcol⟩ := (mem_usedColours_iff ω' e γ).mp hwit
    have hf1 : f ∈ supp1 (L := L) e := by
      by_cases hfe : f = e
      · exact mem_supp1.mpr (Or.inl hfe)
      · exact mem_supp1.mpr (Or.inr ⟨hfe, hmeet,
          ⟨γ, Finset.mem_inter.mpr ⟨by rw [← hcol]; exact Round.colour_mem ω' f, hγ⟩⟩⟩)
    have hf2 : f ∈ supp2 (L := L) e := supp1_subset_supp2_self e hf1
    have hk' : Round.kept ω f :=
      (kept_congr (ω := ω') (ω' := ω)
        (fun g hg => (h g (supp1_subset_supp2 hf1 hg)).symm)).mp hk
    have hcol' : Round.colour ω f = γ := by
      rw [← hcol]; exact colour_congr (h f hf2)
    exact ⟨hγ, (mem_usedColours_iff ω e γ).mpr ⟨f, hk', hmeet, hcol'⟩⟩

end Used

/-! ## The bad events and the support function -/

/-- The bad `A`-event at the edge `e`: `e` is not kept, and more than
`Λ (1 - retention) + η Λ` colours of `L e` are used at `e`. -/
def badA (C D Λ : ℕ) (ε η : ℝ) {K : ℕ} [NeZero K] (e : 𝓗) :
    Set (Round.Space K 𝓗 L) :=
  {ω | ¬ Round.kept ω e ∧
    (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) <
      (((L e) ∩ Round.usedColours ω e).card : ℝ)}

/-- The bad `B`-event at the pair `(x,γ)`: fewer than `D - (newDeg + ηD)` edges through `x`
carrying `γ` are coloured or have `γ` used at them. -/
def badB (C D Λ : ℕ) (ε η : ℝ) {K : ℕ} [NeZero K] (x : Fin n) (γ : Fin c) :
    Set (Round.Space K 𝓗 L) :=
  {ω | ((Round.keptCount ω x γ + Round.usedCount ω x γ : ℕ) : ℝ) <
      (D : ℝ) - (newDeg Λ C D K + η * (D : ℝ))}

/-- The pairs `(x,γ)` that occur in the instance (`γ ∈ L e` for some edge `e ∋ x`). -/
abbrev Occ : Type := {p : Fin n × Fin c // ∃ e : 𝓗, p.1 ∈ (e : Set (Fin n)) ∧ p.2 ∈ L e}

/-- The index type of the bad events: the edges and the occurring pairs. -/
abbrev BadIdx : Type := 𝓗 ⊕ Occ (L := L)

instance instFintypeOcc : Fintype (Occ (L := L)) := by
  classical
  dsimp only [Occ]
  infer_instance

/-- The bad event attached to an index. -/
def badEvent (C D Λ : ℕ) (ε η : ℝ) {K : ℕ} [NeZero K] :
    BadIdx (L := L) → Set (Round.Space K 𝓗 L) :=
  Sum.elim (fun e : 𝓗 => badA C D Λ ε η e)
    (fun p => badB C D Λ ε η p.1.1 p.1.2)

/-- The support of the event at an index. -/
def suppOf : BadIdx (L := L) → Finset 𝓗 :=
  Sum.elim (fun e : 𝓗 => supp2 (L := L) e) (fun p => suppPair (L := L) p.1.1 p.1.2)

/-- The dependence set of the LLL: the events whose support meets the support of `i`. -/
def depSet (i : BadIdx (L := L)) : Finset (BadIdx (L := L)) := by
  classical
  exact Finset.univ.filter (fun j => j ≠ i ∧
    (suppOf (L := L) j ∩ suppOf (L := L) i).Nonempty)

lemma suppOf_inl (e : 𝓗) : suppOf (L := L) (Sum.inl e) = supp2 (L := L) e := rfl

lemma suppOf_inr (p : Occ (L := L)) :
    suppOf (L := L) (Sum.inr p) = suppPair (L := L) p.1.1 p.1.2 := rfl

/-! ## The bad events depend only on their supports -/

section Events

variable {K : ℕ} [NeZero K]

/-- **The `A`-event depends only on the coordinates in `supp2 e`.** -/
lemma badA_congr (C D Λ : ℕ) (ε η : ℝ) {ω ω' : Round.Space K 𝓗 L} {e : 𝓗}
    (h : ∀ g ∈ supp2 (L := L) e, ω g = ω' g) :
    (ω ∈ badA C D Λ ε η e ↔ ω' ∈ badA C D Λ ε η e) := by
  have hk : Round.kept ω e ↔ Round.kept ω' e :=
    kept_congr (fun g hg => h g (supp1_subset_supp2_self e hg))
  have hcard : (L e ∩ Round.usedColours ω e).card = (L e ∩ Round.usedColours ω' e).card :=
    congrArg Finset.card (inter_usedColours_congr h)
  simp only [badA, Set.mem_ofPred_eq, hk, hcard]

/-- **The `B`-event depends only on the coordinates in `suppPair x γ`.** -/
lemma badB_congr (C D Λ : ℕ) (ε η : ℝ) {ω ω' : Round.Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    (h : ∀ g ∈ suppPair (L := L) x γ, ω g = ω' g) :
    (ω ∈ badB C D Λ ε η x γ ↔ ω' ∈ badB C D Λ ε η x γ) := by
  have hk : ∀ f : 𝓗, f ∈ colThru (L := L) x γ → (Round.kept ω f ↔ Round.kept ω' f) :=
    fun f hf => kept_congr
      (fun g hg => h g (supp2_subset_suppPair hf (supp1_subset_supp2_self f hg)))
  have hsets : ∀ (f : 𝓗), x ∈ (f : Set (Fin n)) → (γ ∈ L f) →
      (γ ∈ Round.usedColours ω f ↔ γ ∈ Round.usedColours ω' f) := by
    intro f hxf hγf
    have hf : f ∈ colThru (L := L) x γ := mem_colThru.mpr ⟨hxf, hγf⟩
    have hiff := inter_usedColours_congr (e := f)
      (fun g hg => h g (supp2_subset_suppPair hf hg))
    constructor
    · intro huc
      exact (Finset.mem_inter.mp (hiff ▸ Finset.mem_inter.mpr ⟨hγf, huc⟩)).2
    · intro huc
      exact (Finset.mem_inter.mp (hiff.symm ▸ Finset.mem_inter.mpr ⟨hγf, huc⟩)).2
  have hkc : Round.keptCount ω x γ = Round.keptCount ω' x γ := by
    unfold Round.keptCount
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hkept, hxf, hγf⟩
      exact ⟨(hk f (mem_colThru.mpr ⟨hxf, hγf⟩)).mp hkept, hxf, hγf⟩
    · rintro ⟨hkept, hxf, hγf⟩
      exact ⟨(hk f (mem_colThru.mpr ⟨hxf, hγf⟩)).mpr hkept, hxf, hγf⟩
  have huc : Round.usedCount ω x γ = Round.usedCount ω' x γ := by
    unfold Round.usedCount
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hnk, hxf, hγf, hused⟩
      exact ⟨fun hkf => hnk ((hk f (mem_colThru.mpr ⟨hxf, hγf⟩)).mpr hkf), hxf, hγf,
        (hsets f hxf hγf).mp hused⟩
    · rintro ⟨hnk, hxf, hγf, hused⟩
      exact ⟨fun hkf => hnk ((hk f (mem_colThru.mpr ⟨hxf, hγf⟩)).mp hkf), hxf, hγf,
        (hsets f hxf hγf).mpr hused⟩
  simp only [badB, Set.mem_ofPred_eq, hkc, huc]

/-- The event at an index depends only on the coordinates in its support. -/
lemma badEvent_congr (C D Λ : ℕ) (ε η : ℝ) (i : BadIdx (L := L))
    {ω ω' : Round.Space K 𝓗 L}
    (h : ∀ g ∈ suppOf (L := L) i, ω g = ω' g) :
    (ω ∈ badEvent C D Λ ε η i ↔ ω' ∈ badEvent C D Λ ε η i) := by
  rcases i with e | p
  · exact badA_congr C D Λ ε η h
  · exact badB_congr C D Λ ε η h

end Events

/-! ## Counting: the support sizes and the dependence degree -/

/-- The one-step support-size bound `1 + C Λ D`. -/
def SM (C Λ D : ℕ) : ℕ := 1 + C * Λ * D

/-- The number of events whose support contains a given edge. -/
def BB (C Λ D : ℕ) : ℕ := SM C Λ D * SM C Λ D * (1 + C * Λ)

/-- A uniform bound on the size of the support of an event. -/
def suppBound (C Λ D : ℕ) : ℕ := D * (SM C Λ D * SM C Λ D)

/-- A uniform bound on the size of the dependence set. -/
def depBound (C Λ D : ℕ) : ℕ := suppBound C Λ D * BB C Λ D

/-- The polynomial bound on the dependence degree used by the local lemma. -/
def DepDeg (C D : ℕ) : ℕ := 10 ^ 6 * C ^ 10 * D ^ 10

section Counting

/-- The number of edges through an occurring pair `(x,γ)` is `D`. -/
lemma card_colThru_eq {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (x : Fin n) (γ : Fin c) (h : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) :
    (colThru (L := L) x γ).card = D := by
  classical
  rw [← hdeg x γ h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- The number of edges through any pair `(x,γ)` is at most `D`. -/
lemma card_colThru_le {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (x : Fin n) (γ : Fin c) : (colThru (L := L) x γ).card ≤ D := by
  classical
  by_cases h : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e
  · rw [card_colThru_eq hsize hlist hdeg x γ h]
  · have hempty : colThru (L := L) x γ = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨f, hf⟩
      rw [mem_colThru] at hf
      exact h ⟨f, hf.1, hf.2⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le D

/-- **The colour-neighbourhood bound**: the edges `≠ e` meeting `e` whose list meets `L e`
number at most `C Λ D`. -/
lemma card_ovNbrs_le {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (e : 𝓗) : (ovNbrs (L := L) e).card ≤ C * Λ * D := by
  classical
  have hsub : ovNbrs (L := L) e ⊆ (ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).biUnion
      (fun x => (L e).biUnion (fun γ => colThru (L := L) x γ)) := by
    intro f hf
    rw [mem_ovNbrs] at hf
    obtain ⟨-, hmeet, hne⟩ := hf
    obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγf, hγe⟩ := Finset.mem_inter.mp hγ
    obtain ⟨v, hvf, hve⟩ := hmeet
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · rw [ErdosFaberLovaszConjecture.mem_verts]; exact hve
    · rw [Finset.mem_biUnion]
      exact ⟨γ, hγe, mem_colThru.mpr ⟨hvf, hγf⟩⟩
  calc (ovNbrs (L := L) e).card
      ≤ ((ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).biUnion
          (fun x => (L e).biUnion (fun γ => colThru (L := L) x γ))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ x ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)),
          ((L e).biUnion (fun γ => colThru (L := L) x γ)).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)),
          ∑ γ ∈ L e, (colThru (L := L) x γ).card :=
        Finset.sum_le_sum (fun x _ => Finset.card_biUnion_le)
    _ ≤ ∑ x ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)), ∑ γ ∈ L e, D :=
        Finset.sum_le_sum (fun x _ =>
          Finset.sum_le_sum (fun γ _ => card_colThru_le hsize hlist hdeg x γ))
    _ = ∑ x ∈ ErdosFaberLovaszConjecture.verts (e : Set (Fin n)), ((L e).card * D) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_const, smul_eq_mul]
    _ = (ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).card * ((L e).card * D) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = C * (Λ * D) := by
        have h1 : (ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).card = C := hsize e
        rw [h1, hlist e]
    _ = C * Λ * D := by ring

/-- The one-step support has size at most `SM C Λ D`. -/
lemma card_supp1_le {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (e : 𝓗) : (supp1 (L := L) e).card ≤ SM C Λ D := by
  classical
  have h := Finset.card_insert_le e (ovNbrs (L := L) e)
  have h2 := card_ovNbrs_le hsize hlist hdeg e
  show (insert e (ovNbrs (L := L) e)).card ≤ SM C Λ D
  simp only [SM]
  omega

/-- The two-step support has size at most `(SM C Λ D)^2`. -/
lemma card_supp2_le {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (e : 𝓗) : (supp2 (L := L) e).card ≤ SM C Λ D * SM C Λ D := by
  classical
  calc (supp2 (L := L) e).card
      ≤ ∑ f ∈ supp1 (L := L) e, (supp1 (L := L) f).card := Finset.card_biUnion_le
    _ ≤ ∑ f ∈ supp1 (L := L) e, SM C Λ D :=
        Finset.sum_le_sum (fun f _ => card_supp1_le hsize hlist hdeg f)
    _ = (supp1 (L := L) e).card * SM C Λ D := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ SM C Λ D * SM C Λ D :=
        Nat.mul_le_mul_right _ (card_supp1_le hsize hlist hdeg e)

/-- The support of a pair-event has size at most `D * (SM C Λ D)^2`. -/
lemma card_suppPair_le {C D Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (x : Fin n) (γ : Fin c) :
    (suppPair (L := L) x γ).card ≤ D * (SM C Λ D * SM C Λ D) := by
  classical
  calc (suppPair (L := L) x γ).card
      ≤ ∑ f ∈ colThru (L := L) x γ, (supp2 (L := L) f).card := Finset.card_biUnion_le
    _ ≤ ∑ f ∈ colThru (L := L) x γ, SM C Λ D * SM C Λ D :=
        Finset.sum_le_sum (fun f _ => card_supp2_le hsize hlist hdeg f)
    _ = (colThru (L := L) x γ).card * (SM C Λ D * SM C Λ D) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ D * (SM C Λ D * SM C Λ D) :=
        Nat.mul_le_mul_right _ (card_colThru_le hsize hlist hdeg x γ)

/-- A uniform bound on the size of the support of a bad event. -/
lemma card_suppOf_le {C D Λ : ℕ} (hD : 1 ≤ D)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (i : BadIdx (L := L)) : (suppOf (L := L) i).card ≤ suppBound C Λ D := by
  classical
  rcases i with e | p
  · refine le_trans (card_supp2_le hsize hlist hdeg e) ?_
    simp only [suppBound]
    exact Nat.le_trans (le_refl _) (Nat.mul_le_mul_right _ hD) |> fun h => by simpa using h
  · exact card_suppPair_le hsize hlist hdeg p.1.1 p.1.2

end Counting
/-! ## Symmetry of the support relation -/

lemma mem_supp1_symm {e f : 𝓗} : f ∈ supp1 (L := L) e ↔ e ∈ supp1 (L := L) f := by
  rw [mem_supp1, mem_supp1]
  constructor
  · rintro (rfl | ⟨hfe, hmeet, hne⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hfe.symm, by rwa [Set.inter_comm], by rwa [Finset.inter_comm]⟩
  · rintro (rfl | ⟨hef, hemeet, hene⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hef.symm, by rwa [Set.inter_comm], by rwa [Finset.inter_comm]⟩

lemma mem_supp2_symm {e f : 𝓗} : f ∈ supp2 (L := L) e ↔ e ∈ supp2 (L := L) f := by
  rw [mem_supp2, mem_supp2]
  constructor
  · rintro ⟨h, hh, hf⟩
    exact ⟨h, mem_supp1_symm.mpr hf, mem_supp1_symm.mp hh⟩
  · rintro ⟨h, hh, hf⟩
    exact ⟨h, mem_supp1_symm.mpr hf, mem_supp1_symm.mp hh⟩

section Count2

/-- The occurring pairs whose first coordinate lies in `f` and whose second coordinate lies in
the list of `f` number at most `C Λ`. -/
lemma card_occ_colThru_le {C Λ : ℕ}
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ) (f : 𝓗) :
    ((Finset.univ : Finset (Occ (L := L))).filter
        (fun p => f ∈ colThru (L := L) p.1.1 p.1.2)).card ≤ C * Λ := by
  classical
  set T : Finset (Occ (L := L)) := (Finset.univ).filter
    (fun p => f ∈ colThru (L := L) p.1.1 p.1.2) with hT
  have hinj : Function.Injective (fun p : Occ (L := L) => (p.1.1, p.1.2)) := by
    intro p q hpq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpq
    exact Subtype.ext (Prod.ext h1 h2)
  have himg : T.image (fun p : Occ (L := L) => (p.1.1, p.1.2))
      = (ErdosFaberLovaszConjecture.verts (f : Set (Fin n))) ×ˢ (L f) := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, hpq⟩ := hq
      rw [hT, Finset.mem_filter] at hp
      rw [mem_colThru] at hp
      rw [← hpq]
      exact Finset.mem_product.mpr
        ⟨(ErdosFaberLovaszConjecture.mem_verts (f : Set (Fin n)) p.1.1).mpr hp.2.1, hp.2.2⟩
    · intro hq
      rw [Finset.mem_product] at hq
      rw [Finset.mem_image]
      refine ⟨⟨q, ⟨f, (ErdosFaberLovaszConjecture.mem_verts (f : Set (Fin n)) q.1).mp hq.1,
        hq.2⟩⟩, ?_, rfl⟩
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, mem_colThru.mpr ?_⟩
      exact ⟨(ErdosFaberLovaszConjecture.mem_verts (f : Set (Fin n)) q.1).mp hq.1, hq.2⟩
  have hcard : T.card = ((ErdosFaberLovaszConjecture.verts (f : Set (Fin n))) ×ˢ (L f)).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  rw [hcard, Finset.card_product]
  have h1 : (ErdosFaberLovaszConjecture.verts (f : Set (Fin n))).card = C := hsize f
  rw [h1, hlist f]

/-- The events whose support contains a given edge number at most `BB C Λ D`. -/
lemma card_mem_suppOf_le {C D Λ : ℕ} (hD : 1 ≤ D)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (g : 𝓗) :
    ((Finset.univ : Finset (BadIdx (L := L))).filter
        (fun j => g ∈ suppOf (L := L) j)).card ≤ BB C Λ D := by
  classical
  set S₁ : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter (fun e => g ∈ supp2 (L := L) e) with hS₁
  set S₂ : Finset (Occ (L := L)) := (Finset.univ : Finset (Occ (L := L))).filter
    (fun p => g ∈ suppPair (L := L) p.1.1 p.1.2) with hS₂
  have hsub : ((Finset.univ : Finset (BadIdx (L := L))).filter
      (fun j => g ∈ suppOf (L := L) j)) ⊆ (S₁.image Sum.inl) ∪ (S₂.image Sum.inr) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rcases j with e | p
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨e, by rw [hS₁, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj.2⟩, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨p, by rw [hS₂, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj.2⟩, rfl⟩))
  have hcard1 : (S₁.image (Sum.inl : 𝓗 → BadIdx (L := L))).card = S₁.card :=
    Finset.card_image_of_injective _ (fun a b h => Sum.inl_injective h)
  have hcard2 : (S₂.image (Sum.inr : Occ (L := L) → BadIdx (L := L))).card = S₂.card :=
    Finset.card_image_of_injective _ (fun a b h => Sum.inr_injective h)
  have hbound1 : S₁.card ≤ SM C Λ D * SM C Λ D := by
    have hsub1 : S₁ ⊆ supp2 (L := L) g := by
      intro e he
      rw [hS₁, Finset.mem_filter] at he
      exact mem_supp2_symm.mp he.2
    calc S₁.card ≤ (supp2 (L := L) g).card := Finset.card_le_card hsub1
      _ ≤ SM C Λ D * SM C Λ D := card_supp2_le hsize hlist hdeg g
  have hbound2 : S₂.card ≤ SM C Λ D * SM C Λ D * (C * Λ) := by
    have hsub2 : S₂ ⊆ (supp2 (L := L) g).biUnion
        (fun f => (Finset.univ : Finset (Occ (L := L))).filter
          (fun p => f ∈ colThru (L := L) p.1.1 p.1.2)) := by
      intro p hp
      rw [hS₂, Finset.mem_filter] at hp
      have hp2 := hp.2
      rw [mem_suppPair] at hp2
      obtain ⟨f, hf, hgf⟩ := hp2
      rw [Finset.mem_biUnion]
      refine ⟨f, mem_supp2_symm.mpr hgf, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hf⟩
    calc S₂.card
        ≤ ((supp2 (L := L) g).biUnion (fun f => (Finset.univ : Finset (Occ (L := L))).filter
            (fun p => f ∈ colThru (L := L) p.1.1 p.1.2))).card := Finset.card_le_card hsub2
      _ ≤ ∑ f ∈ supp2 (L := L) g, ((Finset.univ : Finset (Occ (L := L))).filter
            (fun p => f ∈ colThru (L := L) p.1.1 p.1.2)).card := Finset.card_biUnion_le
      _ ≤ ∑ f ∈ supp2 (L := L) g, C * Λ :=
          Finset.sum_le_sum (fun f _ => card_occ_colThru_le hsize hlist f)
      _ = (supp2 (L := L) g).card * (C * Λ) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ SM C Λ D * SM C Λ D * (C * Λ) :=
          Nat.mul_le_mul_right _ (card_supp2_le hsize hlist hdeg g)
  calc ((Finset.univ : Finset (BadIdx (L := L))).filter
        (fun j => g ∈ suppOf (L := L) j)).card
      ≤ ((S₁.image Sum.inl) ∪ (S₂.image Sum.inr)).card := Finset.card_le_card hsub
    _ ≤ (S₁.image Sum.inl).card + (S₂.image Sum.inr).card := Finset.card_union_le _ _
    _ = S₁.card + S₂.card := by rw [hcard1, hcard2]
    _ ≤ SM C Λ D * SM C Λ D + SM C Λ D * SM C Λ D * (C * Λ) := add_le_add hbound1 hbound2
    _ = BB C Λ D := by
        simp only [BB]
        ring

/-- The dependence set of an event has size at most `depBound C Λ D`. -/
lemma card_depSet_le {C D Λ : ℕ} (hD : 1 ≤ D)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (hlist : ∀ e : 𝓗, (L e).card = Λ)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    (i : BadIdx (L := L)) : (depSet (L := L) i).card ≤ depBound C Λ D := by
  classical
  have hsub : depSet (L := L) i ⊆ (suppOf (L := L) i).biUnion
      (fun g => (Finset.univ : Finset (BadIdx (L := L))).filter
        (fun j => g ∈ suppOf (L := L) j)) := by
    intro j hj
    rw [depSet, Finset.mem_filter] at hj
    obtain ⟨-, -, hne⟩ := hj
    obtain ⟨g, hg⟩ := hne
    obtain ⟨hgj, hgi⟩ := Finset.mem_inter.mp hg
    rw [Finset.mem_biUnion]
    refine ⟨g, hgi, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hgj⟩
  calc (depSet (L := L) i).card
      ≤ ((suppOf (L := L) i).biUnion
          (fun g => (Finset.univ : Finset (BadIdx (L := L))).filter
            (fun j => g ∈ suppOf (L := L) j))).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ suppOf (L := L) i, ((Finset.univ : Finset (BadIdx (L := L))).filter
          (fun j => g ∈ suppOf (L := L) j)).card := Finset.card_biUnion_le
    _ ≤ ∑ g ∈ suppOf (L := L) i, BB C Λ D :=
        Finset.sum_le_sum (fun g _ => card_mem_suppOf_le hD hsize hlist hdeg g)
    _ = (suppOf (L := L) i).card * BB C Λ D := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ suppBound C Λ D * BB C Λ D :=
        Nat.mul_le_mul_right _ (card_suppOf_le hD hsize hlist hdeg i)
    _ = depBound C Λ D := rfl

/-- The polynomial bound on the dependence degree. -/
lemma depBound_le_DepDeg {C Λ D : ℕ} (hC : 2 ≤ C) (hD : 1 ≤ D) (hΛ : Λ ≤ 10 * C * D) :
    depBound C Λ D ≤ DepDeg C D := by
  have hC1 : 1 ≤ C := by omega
  have hC2 : 1 ≤ C ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ C * C := Nat.mul_le_mul hC1 hC1
      _ = C ^ 2 := by ring
  have hD2 : 1 ≤ D ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ D * D := Nat.mul_le_mul hD hD
      _ = D ^ 2 := by ring
  have hCD2 : 1 ≤ C ^ 2 * D ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ C ^ 2 * D ^ 2 := Nat.mul_le_mul hC2 hD2
  have hkey1 : SM C Λ D ≤ 11 * C ^ 2 * D ^ 2 := by
    have h1 : C * Λ * D ≤ C * (10 * C * D) * D := by
      calc C * Λ * D = (C * D) * Λ := by ring
        _ ≤ (C * D) * (10 * C * D) := Nat.mul_le_mul_left _ hΛ
        _ = C * (10 * C * D) * D := by ring
    have h2 : C * (10 * C * D) * D = 10 * C ^ 2 * D ^ 2 := by ring
    simp only [SM]
    have h3 : 1 + C * Λ * D ≤ 1 + 10 * C ^ 2 * D ^ 2 := by
      rw [← h2]; exact Nat.add_le_add_left h1 1
    calc 1 + C * Λ * D ≤ 1 + 10 * C ^ 2 * D ^ 2 := h3
      _ ≤ C ^ 2 * D ^ 2 + 10 * C ^ 2 * D ^ 2 := Nat.add_le_add_right hCD2 _
      _ = 11 * C ^ 2 * D ^ 2 := by ring
  have hkey2 : 1 + C * Λ ≤ 11 * C ^ 2 * D := by
    have h1 : C * Λ ≤ C * (10 * C * D) := Nat.mul_le_mul_left C hΛ
    have h2 : C * (10 * C * D) = 10 * C ^ 2 * D := by ring
    have h3 : 1 ≤ C ^ 2 * D := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ C ^ 2 * D := Nat.mul_le_mul hC2 hD
    rw [h2] at h1
    calc 1 + C * Λ ≤ C ^ 2 * D + 10 * C ^ 2 * D := Nat.add_le_add h3 h1
      _ = 11 * C ^ 2 * D := by ring
  have hSM2 : SM C Λ D * SM C Λ D ≤ (11 * C ^ 2 * D ^ 2) * (11 * C ^ 2 * D ^ 2) :=
    Nat.mul_le_mul hkey1 hkey1
  calc depBound C Λ D
      = D * (SM C Λ D * SM C Λ D) * (SM C Λ D * SM C Λ D * (1 + C * Λ)) := rfl
    _ ≤ D * ((11 * C ^ 2 * D ^ 2) * (11 * C ^ 2 * D ^ 2)) *
          ((11 * C ^ 2 * D ^ 2) * (11 * C ^ 2 * D ^ 2) * (11 * C ^ 2 * D)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ hSM2) ?_
        exact Nat.mul_le_mul hSM2 hkey2
    _ = 161051 * C ^ 10 * D ^ 10 := by ring
    _ ≤ DepDeg C D := by
        have hnum : (161051 : ℕ) ≤ 10 ^ 6 := by norm_num
        calc 161051 * C ^ 10 * D ^ 10 ≤ 10 ^ 6 * C ^ 10 * D ^ 10 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hnum)
          _ = DepDeg C D := rfl

end Count2

/-! ## The bridge between the uniform `Conc.prob` and `FinProbSpace.uniform` -/

lemma conc_prob_eq_uniform_prob {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Set Ω) :
    Work.Deep.Conc.prob E = (Work.Deep.Prob.FinProbSpace.uniform Ω).prob E := by
  have hpt : ∀ ω : Ω, E.indicator (fun _ => (Fintype.card Ω : ℝ)⁻¹) ω
      = E.indicator (fun _ => (1 : ℝ)) ω * (Fintype.card Ω : ℝ)⁻¹ := by
    intro ω
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  rw [Work.Deep.Conc.prob, Work.Deep.Conc.expect, Work.Deep.Prob.FinProbSpace.prob]
  simp only [Work.Deep.Prob.FinProbSpace.uniform]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => (hpt ω).symm)

/-! ## Independence of the bad events with disjoint supports -/

section Indep

variable {K : ℕ} [NeZero K] [Nonempty (Round.Space K 𝓗 L)]

/-- **Two bad events with disjoint supports are independent** (in the product measure of the
round).  This is the independence hypothesis of the symmetric Lovász local lemma. -/
lemma indepOfCompls_badEvent (C D Λ : ℕ) (ε η : ℝ)
    (i : BadIdx (L := L)) (T : Finset (BadIdx (L := L)))
    (hT : ∀ j ∈ T, j ∉ depSet (L := L) i ∧ j ≠ i) :
    (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).indepOfCompls
      (badEvent C D Λ ε η i) (badEvent C D Λ ε η) T := by
  classical
  have hneFib : ∀ e : 𝓗, Nonempty (Round.Coord K 𝓗 L e) :=
    fun e => ⟨(Classical.arbitrary (Round.Space K 𝓗 L)) e⟩
  have hdisj : Disjoint (suppOf (L := L) i)
      (T.biUnion (fun j => suppOf (L := L) j)) := by
    rw [Finset.disjoint_left]
    intro g hgS hgR
    rw [Finset.mem_biUnion] at hgR
    obtain ⟨j, hj, hgj⟩ := hgR
    have hcon : (suppOf (L := L) j ∩ suppOf (L := L) i).Nonempty :=
      ⟨g, Finset.mem_inter.mpr ⟨hgj, hgS⟩⟩
    have hmem : j ∈ depSet (L := L) i := by
      rw [depSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hT j hj).2, hcon⟩
    exact (hT j hj).1 hmem
  have hdetX : ∀ ω ω' : Round.Space K 𝓗 L,
      (∀ g ∈ suppOf (L := L) i, ω g = ω' g) →
      (ω ∈ badEvent C D Λ ε η i ↔ ω' ∈ badEvent C D Λ ε η i) :=
    fun _ _ h => badEvent_congr C D Λ ε η i h
  have hdetY : ∀ ω ω' : Round.Space K 𝓗 L,
      (∀ g ∈ T.biUnion (fun j => suppOf (L := L) j), ω g = ω' g) →
      (ω ∈ ⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ ↔
        ω' ∈ ⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ) := by
    intro ω ω' h
    have hmem : ∀ j ∈ T, (ω ∈ (badEvent C D Λ ε η j)ᶜ ↔
        ω' ∈ (badEvent C D Λ ε η j)ᶜ) := by
      intro j hj
      have hsub : suppOf (L := L) j ⊆ T.biUnion (fun j => suppOf (L := L) j) :=
        fun g hg => Finset.mem_biUnion.mpr ⟨j, hj, hg⟩
      exact not_congr (badEvent_congr C D Λ ε η j (fun g hg => h g (hsub hg)))
    rw [Set.mem_iInter₂, Set.mem_iInter₂]
    exact forall₂_congr hmem
  have hconc : Work.Deep.Conc.prob
      ((badEvent C D Λ ε η i) ∩ ⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ)
      = Work.Deep.Conc.prob (badEvent C D Λ ε η i) *
        Work.Deep.Conc.prob (⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ) :=
    Work.Deep.Conc.prob_inter_eq_mul_of_determined (π := fun e : 𝓗 => Round.Coord K 𝓗 L e)
      hneFib hdisj hdetX hdetY
  show (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
      ((badEvent C D Λ ε η i) ∩ ⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ)
      = (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
          (badEvent C D Λ ε η i) *
        (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
          (⋂ j ∈ T, (badEvent C D Λ ε η j)ᶜ)
  rw [← conc_prob_eq_uniform_prob, ← conc_prob_eq_uniform_prob, ← conc_prob_eq_uniform_prob]
  exact hconc

end Indep

end NibbleLLL

theorem nibbleExistsGood {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Dmin : ℝ, 0 < Dmin ∧ ∀ (n c : ℕ)
      (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ) [NeZero K],
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      (∀ e : 𝓗,
        Work.Deep.Conc.prob {ω : Work.Deep.Kahn.Round.Space K 𝓗 L |
          ¬ Work.Deep.Kahn.Round.kept ω e ∧
            (Λ : ℝ) * (1 - Work.Deep.Kahn.retention Λ C D K) + η * (Λ : ℝ) <
              (((L e) ∩ Work.Deep.Kahn.Round.usedColours ω e).card : ℝ)}
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4))) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Work.Deep.Conc.prob {ω : Work.Deep.Kahn.Round.Space K 𝓗 L |
          ((Work.Deep.Kahn.Round.keptCount ω x γ + Work.Deep.Kahn.Round.usedCount ω x γ : ℕ) : ℝ)
            < (D : ℝ) - (Work.Deep.Kahn.newDeg Λ C D K + η * (D : ℝ))}
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4))) →
      ∃ ω : Work.Deep.Kahn.Round.Space K 𝓗 L,
        (∀ e : 𝓗, ¬ Work.Deep.Kahn.Round.kept ω e →
          Work.Deep.Kahn.newLambda Λ C D K - η * (Λ : ℝ) ≤
            ((L e \ Work.Deep.Kahn.Round.usedColours ω e).card : ℝ)) ∧
        (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
          ((Work.Deep.Kahn.Round.residualCount ω x γ : ℕ) : ℝ) ≤
            Work.Deep.Kahn.newDeg Λ C D K + η * (D : ℝ)) := by
  refine ⟨(2 : ℝ) ^ 80, by positivity, ?_⟩
  intro n c 𝓗 instF L D Λ K instK hD hΛ hK hηK h16 hlin hsize hlist hdeg hεD hΛ10 hDmin
    hlogD hKD hCKD hUsed hKept
  classical
  -- the round space is nonempty
  haveI hSpaceNe : Nonempty (Round.Space K 𝓗 L) :=
    ⟨fun e => (⟨0, by omega⟩, ⟨0, by rw [hlist e]; omega⟩)⟩
  -- the numerical hypotheses in ℕ
  have hΛ10' : Λ ≤ 10 * C * D := by exact_mod_cast hΛ10
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hCD : C ≤ D := by
    have h1 : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
      have hη0 : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
      linarith [hCKD]
    have h2 : (D : ℝ) ^ ((1 : ℝ) / 9) ≤ (D : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (x := (D : ℝ)) hD1R
        (by norm_num : ((1 : ℝ) / 9) ≤ 1)
    exact_mod_cast (le_trans h1 h2)
  -- the three hypotheses of the local lemma
  have hp : ∀ i : NibbleLLL.BadIdx (L := L),
      (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).prob
        (NibbleLLL.badEvent C D Λ ε η i) ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by
    intro i
    rcases i with e | p
    · rw [← NibbleLLL.conc_prob_eq_uniform_prob]
      exact hUsed e
    · rw [← NibbleLLL.conc_prob_eq_uniform_prob]
      exact hKept p.1.1 p.1.2 p.2
  have hd : ∀ i : NibbleLLL.BadIdx (L := L),
      (NibbleLLL.depSet (L := L) i).card ≤ NibbleLLL.DepDeg C D := by
    intro i
    refine le_trans (NibbleLLL.card_depSet_le hD hsize hlist hdeg i) ?_
    exact NibbleLLL.depBound_le_DepDeg hC hD hΛ10'
  have hindep : ∀ i (T : Finset (NibbleLLL.BadIdx (L := L))),
      (∀ j ∈ T, j ∉ NibbleLLL.depSet (L := L) i ∧ j ≠ i) →
      (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L)).indepOfCompls
        (NibbleLLL.badEvent C D Λ ε η i) (NibbleLLL.badEvent C D Λ ε η) T :=
    fun i T hT => NibbleLLL.indepOfCompls_badEvent C D Λ ε η i T hT
  have hpd : Real.exp 1 * Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) *
      (((NibbleLLL.DepDeg C D : ℕ) : ℝ) + 1) ≤ 1 := by
    have h := lllPolyBound (C := C) (D := D) (by omega) hCD hDmin
    simpa [NibbleLLL.DepDeg, Nat.cast_add, Nat.cast_one] using h
  -- the local lemma
  obtain ⟨ω, hω⟩ := Work.Deep.Prob.LLL.lll_exists
    (Work.Deep.Prob.FinProbSpace.uniform (Round.Space K 𝓗 L))
    (NibbleLLL.badEvent C D Λ ε η) (NibbleLLL.depSet (L := L)) hp hd hindep hpd
  refine ⟨ω, ?_, ?_⟩
  · -- the list-size estimate at an uncoloured edge
    intro e hne
    have hbad : ω ∉ NibbleLLL.badA C D Λ ε η e := hω (Sum.inl e)
    rw [NibbleLLL.badA, Set.mem_ofPred_eq] at hbad
    push_neg at hbad
    have hcard : ((L e ∩ Round.usedColours ω e).card : ℝ)
        ≤ (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) := hbad hne
    have hcle : (L e ∩ Round.usedColours ω e).card ≤ Λ := by
      calc (L e ∩ Round.usedColours ω e).card ≤ (L e).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = Λ := hlist e
    have hsdiff : (L e \ Round.usedColours ω e).card
        = Λ - (L e ∩ Round.usedColours ω e).card := by
      rw [Finset.card_sdiff, hlist e, Finset.inter_comm]
    rw [hsdiff, Nat.cast_sub hcle, newLambda]
    have hkey : (Λ : ℝ) * retention Λ C D K - η * (Λ : ℝ)
        = (Λ : ℝ) - ((Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ)) := by ring
    rw [hkey]
    linarith
  · -- the colour-degree estimate at an occurring pair
    intro x γ hocc
    have hbad : ω ∉ NibbleLLL.badB C D Λ ε η x γ := by
      have h1 : ω ∉ NibbleLLL.badEvent C D Λ ε η
          (Sum.inr (⟨(x, γ), hocc⟩ : NibbleLLL.Occ (L := L))) := hω _
      simpa [NibbleLLL.badEvent] using h1
    rw [NibbleLLL.badB, Set.mem_ofPred_eq] at hbad
    push_neg at hbad
    -- the partition of the colour-neighbourhood
    set Cc : Finset 𝓗 := NibbleLLL.colThru (L := L) x γ with hCc
    set A₁ : Finset 𝓗 := Cc.filter (fun f => Round.kept ω f) with hA₁
    set A₂ : Finset 𝓗 := Cc.filter (fun f => ¬ Round.kept ω f ∧ γ ∈ Round.usedColours ω f)
      with hA₂
    set A₃ : Finset 𝓗 := Cc.filter (fun f => ¬ Round.kept ω f ∧ γ ∉ Round.usedColours ω f)
      with hA₃
    have hkc : Round.keptCount ω x γ = A₁.card := by
      unfold Round.keptCount
      rw [hA₁, hCc]
      congr 1
      ext f
      simp only [NibbleLLL.mem_colThru, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have huc : Round.usedCount ω x γ = A₂.card := by
      unfold Round.usedCount
      rw [hA₂, hCc]
      congr 1
      ext f
      simp only [NibbleLLL.mem_colThru, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hres : Round.residualCount ω x γ = A₃.card := by
      unfold Round.residualCount
      rw [hA₃, hCc]
      congr 1
      ext f
      simp only [NibbleLLL.mem_colThru, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hunion : A₁ ∪ A₂ ∪ A₃ = Cc := by
      rw [hA₁, hA₂, hA₃, hCc]
      ext f
      simp only [NibbleLLL.mem_colThru, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨hf, -⟩ | ⟨hf, -, -⟩) | ⟨hf, -, -⟩)
        · exact hf
        · exact hf
        · exact hf
      · intro hf
        by_cases hk : Round.kept ω f
        · exact Or.inl (Or.inl ⟨hf, hk⟩)
        · by_cases huse : γ ∈ Round.usedColours ω f
          · exact Or.inl (Or.inr ⟨hf, hk, huse⟩)
          · exact Or.inr ⟨hf, hk, huse⟩
    have hdisjA' : Disjoint A₁ A₂ := by
      rw [Finset.disjoint_left]
      intro f hf1 hf2
      rw [hA₁, Finset.mem_filter] at hf1
      rw [hA₂, Finset.mem_filter] at hf2
      exact hf2.2.1 hf1.2
    have hdisjA : Disjoint (A₁ ∪ A₂) A₃ := by
      rw [Finset.disjoint_left]
      intro f hf hf3
      rw [hA₃, Finset.mem_filter] at hf3
      rw [Finset.mem_union] at hf
      rcases hf with hf | hf
      · rw [hA₁, Finset.mem_filter] at hf
        exact hf3.2.1 hf.2
      · rw [hA₂, Finset.mem_filter] at hf
        exact hf3.2.2 hf.2.2
    have hpart : Round.keptCount ω x γ + Round.usedCount ω x γ + Round.residualCount ω x γ
        = D := by
      rw [hkc, huc, hres, ← NibbleLLL.card_colThru_eq hsize hlist hdeg x γ hocc, ← hCc,
        ← hunion, Finset.card_union_of_disjoint hdisjA,
        Finset.card_union_of_disjoint hdisjA']
    have hkcuc : Round.keptCount ω x γ + Round.usedCount ω x γ ≤ D := by omega
    have hreseq : Round.residualCount ω x γ
        = D - (Round.keptCount ω x γ + Round.usedCount ω x γ) := by omega
    rw [hreseq, Nat.cast_sub hkcuc]
    linarith

end

end Work.Deep.Kahn
