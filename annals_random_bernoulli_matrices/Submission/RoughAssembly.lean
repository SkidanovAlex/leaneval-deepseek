import Mathlib
import Submission.Sec3Tower
import Submission.RoughDecay
import Submission.RoughDecay2
import Submission.RoughProduct
import Submission.Admissible
import Submission.Commons.Nat.Card.cardReal_le_of_cover
import Submission.Commons.Nat.Card.card_triple_cover

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Step 9 — from the descendant triple to the count of event points

The two halves of the rough-decay counting argument:

- deterministic side (`Submission.RoughDecay2.event_descendant`): a tuple `x`
  whose averaged function is large gives a root `t₀`, a {0,1}-pattern `v` and a
  level set `I` with `|I| = ⌈η·(n:ℝ)⌉`, all of whose levels do not decay;
- product side (`Submission.RoughProduct.rough_product_bound`): for an
  admissible family, the number of tuples at which all levels of a level set
  do not decay is at most `q^{#(good levels)}·∏|A_j|`.

This module assembles the union bound:

  `#(event points) ≤ |D0| · 2^ℓ · C(ℓ, ⌈η·(n:ℝ)⌉) · q^{⌈η·(n:ℝ)⌉ − ⌈δ₀·(n:ℝ)⌉} · ∏|A_j|`

where `D0` is the finite superset of the possible roots (bound `|D0| ≤
4N²n^{5/2}`-type is Step 10) and `q` is the per-level fraction.  The
containment `Event ⊆ ⋃` over the triples (with root in `D0`) is the
hypothesis `hCover`; it will be discharged (from the walk structure) in the
final assembly.
-/

open scoped BigOperators

namespace Submission.RoughAssembly

attribute [local instance] Classical.propDecidable

open Submission.Sec3Tower
open Submission.Sec3
open Submission.RoughDecay
open Submission.RoughDecay2
open Submission.RoughProduct
open Submission.Admissible
open Submission.IntFun
open Submission.ProdCount
open Commons.Nat.Card

/-- The event: the level-`ℓ` averaged function of `x` is large somewhere. -/
def eventPred {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (L N n : ℝ) (ε : ℝ)
    (x : Fin ℓ → ℤ) : Prop :=
  ∃ t : ℤ, flvl f p x ℓ (Nat.le_refl ℓ) t >
    max (L / (N * Real.sqrt n)) (((1 - (p : ℝ) + ε) ^ ℓ) * esup f)

/-- The number of levels below `δ₀·(n:ℝ)` is at most `⌈δ₀·(n:ℝ)⌉`. -/
lemma count_levels_below {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (ℓ n : ℕ) :
    ((Finset.range ℓ).filter (fun m : ℕ => (m : ℝ) < δ₀ * (n : ℝ))).card ≤ Nat.ceil (δ₀ * (n : ℝ)) := by
  classical
  have hle : ((Finset.range ℓ).filter (fun m : ℕ => (m : ℝ) < δ₀ * (n : ℝ))).card ≤
      ((Finset.range (Nat.ceil (δ₀ * (n : ℝ)))).card) := by
    exact Finset.card_le_card (by
      intro m hm
      have hmL : (m : ℝ) < δ₀ * (n : ℝ) := (Finset.mem_filter.mp hm).2
      have hceil : (m : ℝ) < (Nat.ceil (δ₀ * (n : ℝ)) : ℝ) :=
        lt_of_lt_of_le hmL (Nat.le_ceil (δ₀ * (n : ℝ)))
      have hmnat : m < Nat.ceil (δ₀ * (n : ℝ)) := by exact_mod_cast hceil
      exact Finset.mem_range.mpr hmnat)
  have hcard : ((Finset.range (Nat.ceil (δ₀ * (n : ℝ)))).card) = Nat.ceil (δ₀ * (n : ℝ)) := by
    exact Finset.card_range _
  rwa [hcard] at hle

/-- The per-triple count: for a level set `I ⊆ Fin ℓ`, the number of tuples at
which every level `m ∈ I` does not decay (along the descendant of `t₀` with
pattern `v`) is at most `q^{#(good levels in I)} · ∏|A_j|`. -/
theorem per_triple_count_le {n : ℕ} (hn1 : 1 ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδle : δ₀ ≤ δ) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε L : ℝ} (hε0 : 0 < ε) (hL0 : 0 < L) {N : ℕ} (hN1 : 1 ≤ N)
    {ℓ : ℕ} {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {A : Fin ℓ → Finset ℤ} (hAdm : Admissible N n ℓ δ A)
    {v : Fin ℓ → ℤ} (t₀ : ℤ) {I : Finset (Fin ℓ)}
    (Cq₁ : ℝ) (hCq₁pos : 0 < Cq₁) (Cq₂ : ℝ) (hCq₂pos : 0 < Cq₂)
    (hPer₁ : RoughDecay2.perStepProp Cq₁) (hPer₂ : RoughDecay2.twoArmProp Cq₂) :
    (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) (I.image (fun m : Fin ℓ => m.val))
        t₀ A v ℓ (Nat.le_refl ℓ) : ℝ) ≤
      (∏ m ∈ (I.image (fun m : Fin ℓ => m.val)).filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m),
        ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))) *
        (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  let I' : Finset ℕ := I.image (fun m : Fin ℓ => m.val)
  let G' : Finset ℕ := I'.filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m)
  have hGI' : G' ⊆ I' := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hIlt' : ∀ m ∈ I', m < ℓ := by
    intro m hm
    rcases (Finset.mem_image.mp hm) with ⟨m₀, hm₀, hmval⟩
    rw [← hmval]
    exact m₀.isLt
  have hG' : ∀ m : ℕ, m ∈ G' ↔ m ∈ I' ∧ δ₀ * (n : ℝ) ≤ m := by
    intro m
    simp [G', I']
  have hmain := rough_product_bound (n := n) hn1 (δ₀ := δ₀) hδ₀ (δ := δ) hδle hslack
      (p := p) hp₀ hp₁ (ε := ε) hε0 (L := L) hL0 (N := N) hN1 (ℓ := ℓ) (f := f)
      hfpos hfsum hfmass (A := A) hAdm (v := v) (t₀ := t₀) (I := I') (G := G') hGI' hIlt' hG'
      Cq₁ hCq₁pos Cq₂ hCq₂pos hPer₁ hPer₂
  -- hmain : countPre … I' … ≤ (∏ m∈G' q)·∏_j |A j|
  simpa [I', G'] using hmain


/-! ## Pure union-bound helpers (pieces (i), (v)) -/

/-- Filtering by "there exists an index making `Q` true" costs at most the sum
over the indices of the per-index filters. -/
lemma card_filter_exists_le {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β)
    (Q : β → α → Prop) :
    (s.filter (fun x : α => ∃ y ∈ t, Q y x)).card ≤
      ∑ y ∈ t, (s.filter (fun x : α => Q y x)).card := by
  classical
  have hsub : s.filter (fun x : α => ∃ y ∈ t, Q y x) ⊆
      t.biUnion (fun y : β => s.filter (fun x : α => Q y x)) := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨y, hy, hQ⟩
    exact Finset.mem_biUnion.mpr ⟨y, hy, (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hQ⟩)⟩
  have hle : (s.filter (fun x : α => ∃ y ∈ t, Q y x)).card ≤
      (t.biUnion (fun y : β => s.filter (fun x : α => Q y x))).card :=
    Finset.card_le_card hsub
  have hsum : (t.biUnion (fun y : β => s.filter (fun x : α => Q y x))).card ≤
      ∑ y ∈ t, (s.filter (fun x : α => Q y x)).card := by
    classical
    refine Finset.induction_on t ?_ ?_
    · simp
    · intro y₀ t₀ hnot ih
      rw [Finset.biUnion_insert]
      calc
        ((s.filter (fun x : α => Q y₀ x) ∪
            (t₀.biUnion (fun y : β => s.filter (fun x : α => Q y x)))).card)
            ≤ (s.filter (fun x : α => Q y₀ x)).card +
                (t₀.biUnion (fun y : β => s.filter (fun x : α => Q y x))).card :=
              Finset.card_union_le _ _
        _ ≤ (s.filter (fun x : α => Q y₀ x)).card +
                (∑ y ∈ t₀, (s.filter (fun x : α => Q y x)).card) := by
            exact Nat.add_le_add_left ih _
        _ = (∑ y ∈ insert y₀ t₀, (s.filter (fun x : α => Q y x)).card) := by
            rw [Finset.sum_insert hnot]
  exact le_trans hle hsum

/-- The abstract union bound: if every `P`-point of `s` is `Q`-good for some
index in `t`, and each index has at most `B` good points, then `#P ≤ |t|·B`. -/
lemma count_le_of_cover {α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β)
    (P : α → Prop) (Q : β → α → Prop) (B : ℕ)
    (hcover : ∀ x ∈ s, P x → ∃ y ∈ t, Q y x)
    (hbound : ∀ y ∈ t, (s.filter (fun x : α => Q y x)).card ≤ B) :
    (s.filter (fun x : α => P x)).card ≤ t.card * B := by
  classical
  have hsub : s.filter (fun x : α => P x) ⊆
      s.filter (fun x : α => ∃ y ∈ t, Q y x) := by
    intro x hx
    have hx1 := (Finset.mem_filter.mp hx).1
    have hx2 := (Finset.mem_filter.mp hx).2
    rcases hcover x hx1 hx2 with ⟨y, hy, hQ⟩
    exact Finset.mem_filter.mpr ⟨hx1, ⟨y, hy, hQ⟩⟩
  have hle1 : (s.filter (fun x : α => P x)).card ≤
      (s.filter (fun x : α => ∃ y ∈ t, Q y x)).card := Finset.card_le_card hsub
  have hle2 : (s.filter (fun x : α => ∃ y ∈ t, Q y x)).card ≤
      ∑ y ∈ t, (s.filter (fun x : α => Q y x)).card := card_filter_exists_le s t Q
  have hle3 : (∑ y ∈ t, (s.filter (fun x : α => Q y x)).card) ≤ ∑ y ∈ t, B := by
    exact Finset.sum_le_sum (by intro y hy; exact hbound y hy)
  calc
    (s.filter (fun x : α => P x)).card ≤
        (s.filter (fun x : α => ∃ y ∈ t, Q y x)).card := hle1
    _ ≤ ∑ y ∈ t, (s.filter (fun x : α => Q y x)).card := hle2
    _ ≤ ∑ y ∈ t, B := hle3
    _ = t.card * B := by simp [Finset.sum_const]


/-- Piece (ii): a tuple at which every level `m ∈ I` does not decay (with the
full pattern `v`) belongs to the `countPre` filter over the level set
`I.image (fun m => m.val)` (where the pattern is the `ℓ`-prefix of `v`, i.e.
`v` itself). -/
lemma level_image_subset {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {T : ℝ}
    {v : Fin ℓ → ℤ} {t₀ : ℤ} {A : Fin ℓ → Finset ℤ} {I : Finset (Fin ℓ)}
    (x : Fin ℓ → ℤ) (hx : x ∈ prodFinset ℓ A)
    (hgood : ∀ m ∈ I, levelCond f p T x v t₀ m.val (m.isLt)) :
    x ∈ ((prodFinset ℓ (preCoord (Nat.le_refl ℓ) A)).filter
      (fun y : Fin ℓ → ℤ => ∀ m : ℕ,
        m ∈ I.image (fun m : Fin ℓ => m.val) → ∀ h : m < ℓ,
          levelCond f p T y (preFun (Nat.le_refl ℓ) v) t₀ m h)) := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · have heq : prodFinset ℓ (preCoord (Nat.le_refl ℓ) A) = prodFinset ℓ A := by
      exact prodFinset_congr (by
        intro j
        dsimp [preCoord])
    rwa [heq]
  · intro m hm h
    rcases (Finset.mem_image.mp hm) with ⟨m₀, hm₀, hmval⟩
    subst m
    have hg := hgood m₀ hm₀
    have hpat : preFun (Nat.le_refl ℓ) v = v := by
      funext j
      dsimp [preFun]
    have hcong := levelCond_pattern_congr (f := f) (p := p) (T := T) (x := x)
        (w₁ := preFun (Nat.le_refl ℓ) v) (w₂ := v) hpat (t₀ := t₀) (m := m₀.val) (hm := m₀.isLt)
    have hg' : levelCond f p T x (preFun (Nat.le_refl ℓ) v) t₀ m₀.val m₀.isLt := (hcong).1 hg
    simpa [levelCond_proof_irrel] using hg'


/-- The {0,1}-valued pattern `v` is the indicator of its own support. -/
lemma indicator_support_eq {ℓ : ℕ} {v : Fin ℓ → ℤ}
    (hv : ∀ j : Fin ℓ, v j = 0 ∨ v j = 1) :
    (fun j : Fin ℓ => if j ∈ (Finset.univ : Finset (Fin ℓ)).filter (fun j => v j = 1) then 1 else 0) = v := by
  classical
  funext j
  by_cases h : v j = 1
  · have hj : j ∈ (Finset.univ : Finset (Fin ℓ)).filter (fun j => v j = 1) := by
      simp [h]
    simp [hj, h]
  · have hvj : v j = 0 := by
      rcases hv j with hv0 | hv1
      · exact hv0
      · exact False.elim (h hv1)
    have hj : j ∉ (Finset.univ : Finset (Fin ℓ)).filter (fun j => v j = 1) := by
      intro hj'
      exact h (Finset.mem_filter.mp hj').2
    simp [hj, hvj]

/-- The triple-space element produced by the cover hypothesis. -/
def tripleSpace (D0 : Finset ℤ) (K ℓ : ℕ) : Finset ((ℤ × Finset (Fin ℓ)) × Finset (Fin ℓ)) :=
  ((D0.product ((Finset.univ : Finset (Fin ℓ)).powerset)).product
    (Finset.powersetCard K (Finset.univ : Finset (Fin ℓ))))

/-- Goodness of a tuple for a triple `(t₀, S, I)`: all levels `m ∈ I` do not
decay along the descendant of `t₀` with pattern `indicator S`. -/
def goodTriple {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) (t₀ : ℤ)
    (S : Finset (Fin ℓ)) (I : Finset (Fin ℓ)) (x : Fin ℓ → ℤ) : Prop :=
  ∀ m ∈ I, levelCond f p T x (fun j : Fin ℓ => if j ∈ S then 1 else 0) t₀ m.val (m.isLt)

/-- Piece (i): the cover hypothesis `hCover` yields, for every event point, a
triple in `tripleSpace` at which the point is good. -/
lemma triple_cover {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {T : ℝ}
    (D0 : Finset ℤ) (K : ℕ) (A : Fin ℓ → Finset ℤ) (Ev : (Fin ℓ → ℤ) → Prop)
    (hCover : ∀ x ∈ prodFinset ℓ A, Ev x →
      ∃ t₀ ∈ D0, ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
        ∃ I : Finset (Fin ℓ), I.card = K ∧
          ∀ m ∈ I, levelCond f p T x v t₀ m.val (m.isLt)) :
    ∀ x ∈ prodFinset ℓ A, Ev x →
      ∃ pr : (ℤ × Finset (Fin ℓ)) × Finset (Fin ℓ), pr ∈ tripleSpace D0 K ℓ ∧
        goodTriple f p T pr.1.1 pr.1.2 pr.2 x := by
  classical
  intro x hx hEv
  rcases hCover x hx hEv with ⟨t₀, ht₀, v, hv, I, hIcard, hIgood⟩
  let S : Finset (Fin ℓ) := (Finset.univ : Finset (Fin ℓ)).filter (fun j : Fin ℓ => v j = 1)
  refine ⟨((t₀, S), I), ?_, ?_⟩
  · -- membership in tripleSpace
    dsimp [tripleSpace]
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_product]
      constructor
      · exact ht₀
      · rw [Finset.mem_powerset]
        intro j hj
        simp
    · rw [Finset.mem_powersetCard]
      constructor
      · intro j hj
        simp
      · exact hIcard
  · -- goodness with indicator S
    have hind : (fun j : Fin ℓ => if j ∈ S then 1 else 0) = v := by
      dsimp [S]
      exact indicator_support_eq hv
    dsimp [goodTriple]
    intro m hm
    have hg := hIgood m hm
    have hcong := levelCond_pattern_congr (f := f) (p := p) (T := T) (x := x)
        (w₁ := fun j : Fin ℓ => if j ∈ S then 1 else 0) (w₂ := v) hind
        (t₀ := t₀) (m := m.val) (hm := m.isLt)
    exact (hcong).2 hg


/-- Piece (iv): in a level set `I ⊆ Fin ℓ` the number of good levels (values
`≥ δ₀·(n:ℝ)`) is at least `|I| − ⌈δ₀·(n:ℝ)⌉`. -/
lemma good_levels_ge {ℓ n : ℕ} (I : Finset (Fin ℓ)) {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) :
    I.card - Nat.ceil (δ₀ * (n : ℝ)) ≤
      ((I.image (fun m : Fin ℓ => m.val)).filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m)).card := by
  classical
  let I' : Finset ℕ := I.image (fun m : Fin ℓ => m.val)
  let G : Finset ℕ := I'.filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m)
  let B : Finset ℕ := I'.filter (fun m : ℕ => ¬ δ₀ * (n : ℝ) ≤ m)
  have hcardI' : I'.card = I.card := by
    dsimp [I']
    exact Finset.card_image_of_injective I (Fin.val_injective)
  have hGI : G.card + B.card = I'.card := by
    simpa [G, B] using (Finset.card_filter_add_card_filter_not (s := I')
      (fun m : ℕ => δ₀ * (n : ℝ) ≤ m))
  have hBsub : B ⊆ (Finset.range ℓ).filter (fun m : ℕ => (m : ℝ) < δ₀ * (n : ℝ)) := by
    intro m hm
    have hm1 : m ∈ I' := (Finset.mem_filter.mp hm).1
    have hm2 : ¬ δ₀ * (n : ℝ) ≤ m := (Finset.mem_filter.mp hm).2
    have hmLt : (m : ℝ) < δ₀ * (n : ℝ) := lt_of_not_ge hm2
    have hmℓ : m < ℓ := by
      rcases (Finset.mem_image.mp hm1) with ⟨m₀, hm₀, hmval⟩
      rw [← hmval]
      exact m₀.isLt
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmℓ, hmLt⟩
  have hBcard : B.card ≤ Nat.ceil (δ₀ * (n : ℝ)) := by
    exact le_trans (Finset.card_le_card hBsub) (count_levels_below hδ₀ ℓ n)
  have hsum : I.card ≤ G.card + Nat.ceil (δ₀ * (n : ℝ)) := by
    calc
      I.card = I'.card := hcardI'.symm
      _ = G.card + B.card := hGI.symm
      _ ≤ G.card + Nat.ceil (δ₀ * (n : ℝ)) := by
        exact Nat.add_le_add_left hBcard G.card
  have hgoal : I.card - Nat.ceil (δ₀ * (n : ℝ)) ≤ G.card := (Nat.sub_le_iff_le_add).mpr hsum
  simpa [G, I'] using hgoal

/-- The product over the good levels of `q` is at most `q^{|I|−⌈δ₀n⌉}` when
`0 ≤ q ≤ 1`. -/
lemma goodprod_le {ℓ n : ℕ} (I : Finset (Fin ℓ)) {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∏ m ∈ (I.image (fun m : Fin ℓ => m.val)).filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m), q) ≤
      q ^ (I.card - Nat.ceil (δ₀ * (n : ℝ))) := by
  classical
  have hge := good_levels_ge (n := n) I hδ₀
  rw [Finset.prod_const]
  exact pow_le_pow_of_le_one hq0 hq1 hge

/-- The Step-9 assembly theorem (union bound over the triples).  `hCover`
(Event ⟹ a triple with root in `D0`) is the walk-containment hypothesis,
discharged in the final assembly.  The per-step constants `Cq₁`, `Cq₂` are
shared across every triple, so the per-level fraction
`q := 2p(Cq₁+Cq₂)/(εL√(δ₀p))` is uniform (hypothesis `hq1` makes `q ≤ 1`). -/
theorem event_count_le {n : ℕ} (hn1 : 1 ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδle : δ₀ ≤ δ) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) {L : ℝ} (hL0 : 0 < L)
    {N : ℕ} (hN1 : 1 ≤ N) {ℓ : ℕ} (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ ηdec p ε)
    {A : Fin ℓ → Finset ℤ} (hAdm : Admissible N n ℓ δ A) {D0 : Finset ℤ}
    (Cq₁ : ℝ) (hCq₁pos : 0 < Cq₁) (Cq₂ : ℝ) (hCq₂pos : 0 < Cq₂)
    (hPer₁ : perStepProp Cq₁) (hPer₂ : twoArmProp Cq₂)
    (hq1 : ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤ 1)
    (hCover : ∀ x ∈ prodFinset ℓ A, eventPred f p L (N : ℝ) (n : ℝ) ε x →
      ∃ t₀ ∈ D0, ∃ v : Fin ℓ → ℤ, (∀ j : Fin ℓ, v j = 0 ∨ v j = 1) ∧
        ∃ I : Finset (Fin ℓ), I.card = Nat.ceil (η * (n : ℝ)) ∧
          ∀ m ∈ I, levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) x v t₀ m.val (m.isLt)) :
    ((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        eventPred f p L (N : ℝ) (n : ℝ) ε x)).card ≤
      (D0.card : ℝ) * (2 : ℝ) ^ ℓ * ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
        (((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ^
          ((Nat.ceil (η * (n : ℝ))) - (Nat.ceil (δ₀ * (n : ℝ))))) *
        (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  let K : ℕ := Nat.ceil (η * (n : ℝ))
  let q : ℝ := (2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))
  let Ev : (Fin ℓ → ℤ) → Prop := fun x => eventPred f p L (N : ℝ) (n : ℝ) ε x
  let B : ℝ := q ^ (K - Nat.ceil (δ₀ * (n : ℝ))) * (∏ j : Fin ℓ, ((A j).card : ℝ))
  -- (i)+(ii): the cover over the triple space
  have hcv : ∀ x ∈ prodFinset ℓ A, Ev x →
      ∃ pr : (ℤ × Finset (Fin ℓ)) × Finset (Fin ℓ), pr ∈ tripleSpace D0 K ℓ ∧
        goodTriple f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) pr.1.1 pr.1.2 pr.2 x := by
    intro x hx hEv
    exact triple_cover (f := f) (p := p) (T := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
        D0 K A Ev hCover x hx hEv
  -- per-triple bound (piece (iii)+(iv)); to be assembled next
  let cnt : (ℤ × Finset (Fin ℓ)) × Finset (Fin ℓ) → ℕ := fun pr =>
    ((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        goodTriple f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) pr.1.1 pr.1.2 pr.2 x)).card
  have hb : ∀ pr ∈ tripleSpace D0 K ℓ, (cnt pr : ℝ) ≤ B := by
    intro pr hpr
    let t₀ : ℤ := pr.1.1
    let S : Finset (Fin ℓ) := pr.1.2
    let I : Finset (Fin ℓ) := pr.2
    let v : Fin ℓ → ℤ := fun j : Fin ℓ => if j ∈ S then 1 else 0
    have hIcard : I.card = K := by
      exact (Finset.mem_powersetCard.mp (Finset.mem_product.mp hpr).2).2
    -- (a) every good point belongs to the countPre filter over the level image
    have hinc : (prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
          goodTriple f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) t₀ S I x) ⊆
        ((prodFinset ℓ (preCoord (Nat.le_refl ℓ) A)).filter (fun y : Fin ℓ → ℤ =>
          ∀ m : ℕ, m ∈ I.image (fun m : Fin ℓ => m.val) → ∀ h : m < ℓ,
            levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) y (preFun (Nat.le_refl ℓ) v) t₀ m h)) := by
      intro x hx
      have hx1 : x ∈ prodFinset ℓ A := (Finset.mem_filter.mp hx).1
      have hgoodx : ∀ m ∈ I, levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) x v t₀ m.val (m.isLt) := by
        intro m hm
        exact (Finset.mem_filter.mp hx).2 m hm
      exact level_image_subset (f := f) (p := p) (T := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
          (v := v) (t₀ := t₀) (A := A) (I := I) x hx1 hgoodx
    have hcnt : cnt pr ≤ countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
          (I.image (fun m : Fin ℓ => m.val)) t₀ A v ℓ (Nat.le_refl ℓ) := by
      have hcard' : (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
            (I.image (fun m : Fin ℓ => m.val)) t₀ A v ℓ (Nat.le_refl ℓ)) =
          (((prodFinset ℓ (preCoord (Nat.le_refl ℓ) A)).filter (fun y : Fin ℓ → ℤ =>
            ∀ m : ℕ, m ∈ I.image (fun m : Fin ℓ => m.val) → ∀ h : m < ℓ,
              levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) y (preFun (Nat.le_refl ℓ) v) t₀ m h)).card) := by
        dsimp [countPre, v]
      dsimp [cnt]
      rw [hcard']
      exact Finset.card_le_card hinc
    -- (b) per-triple count bound (shared constants)
    have hper := per_triple_count_le hn1 hδ₀ hδle hslack hp₀ hp₁ hε0 hL0 hN1 hfpos hfsum hfmass
        hAdm (v := v) (t₀ := t₀) (I := I) Cq₁ hCq₁pos Cq₂ hCq₂pos hPer₁ hPer₂
    -- (c) exponent collapse
    have hq0 : 0 ≤ q := by
      dsimp [q]
      positivity
    have hq1' : q ≤ 1 := by
      dsimp [q]
      exact hq1
    have hgood := goodprod_le (n := n) I (δ₀ := δ₀) (by exact le_of_lt hδ₀) (q := q) hq0 hq1'
    have hprod0 : 0 ≤ (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
      exact Finset.prod_nonneg (by intro j hj; exact_mod_cast (Nat.zero_le (A j).card))
    calc
      (cnt pr : ℝ) ≤ (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
            (I.image (fun m : Fin ℓ => m.val)) t₀ A v ℓ (Nat.le_refl ℓ) : ℝ) := by
            exact_mod_cast hcnt
      _ ≤ (∏ m ∈ (I.image (fun m : Fin ℓ => m.val)).filter (fun m : ℕ => δ₀ * (n : ℝ) ≤ m),
              ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))) *
            (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
            simpa [q] using hper
      _ ≤ q ^ (I.card - Nat.ceil (δ₀ * (n : ℝ))) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hgood hprod0
      _ = B := by
            rw [hIcard]
  -- (v): the union bound
  have hc := cardReal_le_of_cover (s := prodFinset ℓ A) (t := tripleSpace D0 K ℓ)
      Ev (fun pr : (ℤ × Finset (Fin ℓ)) × Finset (Fin ℓ) =>
        fun x : Fin ℓ → ℤ => goodTriple f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) pr.1.1 pr.1.2 pr.2 x)
      B (by intro x hx hEv; exact hcv x hx hEv) (by intro pr hpr; exact hb pr hpr)
  -- final arithmetic: #Event ≤ |D0|·2^ℓ·C(ℓ,K)·q^{K−⌈δ₀n⌉}·∏|A|
  have htriple : (tripleSpace D0 K ℓ).card = D0.card * 2 ^ ℓ * (ℓ.choose K) := by
    exact card_triple_cover D0 K ℓ
  calc
    (((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ => Ev x)).card : ℝ)
        ≤ (tripleSpace D0 K ℓ).card * B := hc
    _ = (D0.card : ℝ) * (2 : ℝ) ^ ℓ * ((ℓ.choose K) : ℝ) *
          q ^ (K - Nat.ceil (δ₀ * (n : ℝ))) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
          rw [htriple]
          dsimp [B]
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
          ring

end Submission.RoughAssembly
