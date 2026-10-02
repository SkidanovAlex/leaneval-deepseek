import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup

/-!
# `Work.Deep.Kahn.Round`: the vocabulary of the `uncolActCount` concentration

The statistic `uncolActCount ω x γ` counts the *activated but blocked* `γ`-edges through `x`
(the paper's `uncolActivatedNbrsRV`; Kang--Kelly--Kühn--Methuku--Osthus, arXiv:2109.11438,
Section `section:nibble`).  This module fixes the vocabulary of its concentration argument.

For the fixed pair `(x,γ)`:

* `colThru x γ` — the set of `γ`-edges through `x` (there are `D` of them in a regularised
  instance);
* `colThruCols x γ` — the colours occurring in the lists of those edges;
* `conflictAt ω x γ δ` — the number of activated `δ`-edges through `x` whose colour is `δ`
  (the paper's `conflictsRV`);
* `excSet x γ ℓ` — the **exceptional outcomes**: some colour `δ ∈ colThruCols x γ` is the
  colour of at least `ℓ` activated `γ`-edges through `x`;
* `uncolActSet ω x γ` — the edges counted by `uncolActCount ω x γ`;
* `IsBlocker ω e f` — `f` is a *blocker* of `e`: a different activated edge meeting `e` whose
  colour is `colour ω e`;
* `blockerOf ω x γ e` — a chosen blocker of a counted edge;
* `certSet ω x γ` — the certificate set of the Bruhn--Joos argument: the counted edges
  together with their chosen blockers.

Off `excSet x γ ℓ` the multiplicity of a blocker is at most `C + ℓ`: a blocker either contains
`x` (then it is one of the at most `ℓ - 1` activated `δ`-edges through `x`, `blkFib_le_of_mem_x`)
or meets `e` at a vertex `≠ x`, and then linearity bounds its multiplicity by `|w| = C`
(`blkFib_le_of_not_mem_x`).  That is the input of the certificate hypothesis of
`Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand` for the statistic `-uncolActCount`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ}

/-! ## The `γ`-edges through `x` -/

/-- The `γ`-edges through the vertex `x`. -/
def colThru (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun e : 𝓗 => x ∈ (e : Set (Fin n)) ∧ γ ∈ L e)

@[simp] lemma mem_colThru {x : Fin n} {γ : Fin c} {e : 𝓗} :
    e ∈ colThru (L := L) x γ ↔ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e := by
  classical
  simp [colThru]

/-- The colours occurring in the lists of the `γ`-edges through `x`. -/
def colThruCols (x : Fin n) (γ : Fin c) : Finset (Fin c) := by
  classical
  exact (colThru (L := L) x γ).biUnion (fun e => L e)

lemma mem_colThruCols {x : Fin n} {γ δ : Fin c} :
    δ ∈ colThruCols (L := L) x γ ↔ ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧ δ ∈ L e := by
  classical
  rw [colThruCols, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hδ⟩
    exact ⟨e, (mem_colThru.mp he).1, (mem_colThru.mp he).2, hδ⟩
  · rintro ⟨e, h1, h2, h3⟩
    exact ⟨e, mem_colThru.mpr ⟨h1, h2⟩, h3⟩

/-- The number of activated `δ`-edges through `x` that carry `γ` in their list and whose
colour is `δ` (the paper's `conflictsRV_{x,δ}`). -/
def conflictAt [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (δ : Fin c) : ℕ := by
  classical
  exact ((colThru (L := L) x γ).filter
    (fun e : 𝓗 => δ ∈ L e ∧ active ω e ∧ colour ω e = δ)).card

/-- **The exceptional outcomes** of the certificate argument. -/
def excSet [NeZero K] (x : Fin n) (γ : Fin c) (ℓ : ℕ) : Set (Space K 𝓗 L) :=
  {ω | ∃ δ ∈ colThruCols (L := L) x γ, ℓ ≤ conflictAt (L := L) ω x γ δ}

lemma not_mem_excSet_iff [NeZero K] {x : Fin n} {γ : Fin c} {ℓ : ℕ} {ω : Space K 𝓗 L} :
    ω ∉ excSet (L := L) x γ ℓ ↔
      ∀ δ ∈ colThruCols (L := L) x γ, conflictAt (L := L) ω x γ δ < ℓ := by
  classical
  rw [excSet, Set.mem_ofPred_eq]
  constructor
  · intro h δ hδ
    exact Nat.lt_of_not_le fun hle => h ⟨δ, hδ, hle⟩
  · rintro h ⟨δ, hδ, hle⟩
    exact absurd (h δ hδ) (by omega)

lemma mem_excSet_iff [NeZero K] {x : Fin n} {γ : Fin c} {ℓ : ℕ} {ω : Space K 𝓗 L} :
    ω ∈ excSet (L := L) x γ ℓ ↔
      ∃ δ ∈ colThruCols (L := L) x γ, ℓ ≤ conflictAt (L := L) ω x γ δ := Iff.rfl

/-- The set of edges counted by `uncolActCount ω x γ`. -/
def uncolActSet [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact (colThru (L := L) x γ).filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e)

lemma active_congr [NeZero K] {ω ω' : Space K 𝓗 L} {e : 𝓗} (h : ω e = ω' e) :
    (active ω e ↔ active ω' e) := by
  have h1 : (ω e).1 = (ω' e).1 := congrArg Prod.fst h
  simp only [active, h1]

lemma colour_congr [NeZero K] {ω ω' : Space K 𝓗 L} {e : 𝓗} (h : ω e = ω' e) :
    colour ω e = colour ω' e := by
  have h1 : (ω e).2 = (ω' e).2 := congrArg Prod.snd h
  simp only [colour, h1]

lemma mem_uncolActSet [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗} :
    e ∈ uncolActSet (K := K) ω x γ ↔
      x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧ active ω e ∧ ¬ kept ω e := by
  classical
  rw [uncolActSet, Finset.mem_filter, mem_colThru]
  tauto

lemma uncolActSet_card [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    (uncolActSet (K := K) ω x γ).card = uncolActCount (K := K) (L := L) ω x γ := by
  classical
  have h : uncolActSet (K := K) ω x γ
      = Finset.univ.filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e ∧
          x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) := by
    ext e
    simp only [uncolActSet, colThru, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp only [h, uncolActCount]

lemma uncolActSet_subset_colThru [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    uncolActSet (K := K) ω x γ ⊆ colThru (L := L) x γ := by
  intro e he
  exact mem_colThru.mpr ⟨(mem_uncolActSet.mp he).1, (mem_uncolActSet.mp he).2.1⟩

/-! ## The potential blockers of an edge at a colour -/

/-- The *potential blockers* of `e` at the colour `δ`: the edges `f ≠ e` meeting `e` whose list
contains `δ`. -/
def blkOf (e : 𝓗) (δ : Fin c) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ δ ∈ L f)

@[simp] lemma mem_blkOf {e f : 𝓗} {δ : Fin c} :
    f ∈ blkOf (L := L) e δ ↔ f ≠ e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ δ ∈ L f := by
  classical
  simp [blkOf]

/-! ## Blockers and the certificate set -/

/-- `f` *blocks* `e` at `ω` when `f` is a different activated edge meeting `e` and carrying
the colour of `e`. -/
def IsBlocker [NeZero K] (ω : Space K 𝓗 L) (e f : 𝓗) : Prop :=
  f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧ active ω f ∧
    colour ω f = colour ω e

/-- An activated edge that is not kept has a blocker. -/
lemma exists_blocker_of_not_kept [NeZero K] {ω : Space K 𝓗 L} {e : 𝓗}
    (hact : active ω e) (hkept : ¬ kept ω e) : ∃ f : 𝓗, IsBlocker ω e f := by
  classical
  rw [kept] at hkept
  by_contra hno
  refine hkept ⟨hact, ?_⟩
  intro g hgne hmeet hgact hcol
  exact hno ⟨g, hgne, hmeet, hgact, hcol⟩

/-- A counted edge has a blocker. -/
lemma exists_blocker [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗}
    (he : e ∈ uncolActSet (K := K) ω x γ) : ∃ f : 𝓗, IsBlocker ω e f :=
  exists_blocker_of_not_kept (K := K) (mem_uncolActSet.mp he).2.2.1 (mem_uncolActSet.mp he).2.2.2

/-- The chosen blocker of the edge `e` (itself, if `e` is not counted). -/
def blockerOf [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) : 𝓗 :=
  if h : e ∈ uncolActSet (K := K) ω x γ then
    Classical.choose (exists_blocker (K := K) (x := x) (γ := γ) h)
  else e

lemma blockerOf_spec [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗}
    (he : e ∈ uncolActSet (K := K) ω x γ) : IsBlocker ω e (blockerOf (K := K) ω x γ e) := by
  classical
  rw [blockerOf, dif_pos he]
  exact Classical.choose_spec (exists_blocker (K := K) (x := x) (γ := γ) he)

lemma IsBlocker.mem_blkOf [NeZero K] {ω : Space K 𝓗 L} {e f : 𝓗} (h : IsBlocker ω e f) :
    f ∈ blkOf (L := L) e (colour ω e) := by
  obtain ⟨hne, hmeet, -, hcol⟩ := h
  exact (Work.Deep.Kahn.Round.mem_blkOf (L := L)).mpr ⟨hne, hmeet, hcol ▸ colour_mem ω f⟩

lemma blockerOf_eq_self_of_not_mem [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    {e : 𝓗} (he : e ∉ uncolActSet (K := K) ω x γ) : blockerOf (K := K) ω x γ e = e := by
  classical
  rw [blockerOf, dif_neg he]

/-- The certificate set of the Bruhn--Joos argument. -/
def certSet [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 :=
  uncolActSet (K := K) ω x γ ∪ (uncolActSet (K := K) ω x γ).image (blockerOf (K := K) ω x γ)

lemma mem_certSet [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗} :
    e ∈ certSet (K := K) ω x γ ↔
      e ∈ uncolActSet (K := K) ω x γ ∨
        ∃ e' ∈ uncolActSet (K := K) ω x γ, blockerOf (K := K) ω x γ e' = e := by
  classical
  simp only [certSet, Finset.mem_union, Finset.mem_image]

lemma uncolActSet_subset_certSet [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    uncolActSet (K := K) ω x γ ⊆ certSet (K := K) ω x γ :=
  Finset.subset_union_left

lemma certSet_card_le [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    (certSet (K := K) ω x γ).card ≤ 2 * (uncolActSet (K := K) ω x γ).card := by
  classical
  refine le_trans (Finset.card_union_le _ _) ?_
  have him := Finset.card_image_le (s := uncolActSet (K := K) ω x γ)
    (f := blockerOf (K := K) ω x γ)
  omega

/-! ## The multiplicity of a blocker -/

/-- The counted edges whose chosen blocker is `w`. -/
def blkFib [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (w : 𝓗) : Finset 𝓗 := by
  classical
  exact (uncolActSet (K := K) ω x γ).filter (fun e : 𝓗 => blockerOf (K := K) ω x γ e = w)

lemma mem_blkFib [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {w e : 𝓗} :
    e ∈ blkFib (K := K) ω x γ w ↔
      e ∈ uncolActSet (K := K) ω x γ ∧ blockerOf (K := K) ω x γ e = w := by
  classical
  rw [blkFib, Finset.mem_filter]

/-- Every edge of `blkFib ω x γ w` has colour `colour ω w`. -/
lemma colour_eq_of_mem_blkFib [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {w e : 𝓗}
    (he : e ∈ blkFib (K := K) ω x γ w) : colour ω e = colour ω w := by
  classical
  obtain ⟨heU, hbw⟩ := mem_blkFib.mp he
  have hspec := blockerOf_spec (K := K) (x := x) (γ := γ) heU
  rw [hbw] at hspec
  exact hspec.2.2.2.symm

/-- The multiplicity of the blocker `w` is bounded by `conflictAt ω x γ (colour ω w)`. -/
lemma blkFib_le_conflictAt [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (w : 𝓗) :
    (blkFib (K := K) ω x γ w).card ≤ conflictAt (L := L) ω x γ (colour ω w) := by
  classical
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨heU, _⟩ := mem_blkFib.mp he
  obtain ⟨h1, h2, h3, -⟩ := mem_uncolActSet.mp heU
  rw [Finset.mem_filter]
  exact ⟨mem_colThru.mpr ⟨h1, h2⟩, by
      rw [← colour_eq_of_mem_blkFib (K := K) he]; exact colour_mem ω e, h3,
    colour_eq_of_mem_blkFib (K := K) he⟩

/-- **Off the exceptional set, a blocker containing `x` has multiplicity at most `ℓ - 1`.** -/
lemma blkFib_le_of_mem_x [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {ℓ : ℕ}
    {w : 𝓗} (hω : ω ∉ excSet (L := L) x γ ℓ) (hxw : x ∈ (w : Set (Fin n))) :
    (blkFib (K := K) ω x γ w).card ≤ ℓ - 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty (blkFib (K := K) ω x γ w) with hempty | ⟨e0, he0⟩
  · rw [hempty]; simp
  · obtain ⟨heU, hbw⟩ := mem_blkFib.mp he0
    obtain ⟨h1, h2, -, -⟩ := mem_uncolActSet.mp heU
    have hcol : colour ω w ∈ colThruCols (L := L) x γ := by
      refine mem_colThruCols.mpr ⟨e0, h1, h2, ?_⟩
      rw [← colour_eq_of_mem_blkFib (K := K) he0]
      exact colour_mem ω e0
    have hlt := (not_mem_excSet_iff (L := L) (K := K)).mp hω (colour ω w) hcol
    have hle := blkFib_le_conflictAt (K := K) (L := L) ω x γ w
    omega

/-- **Off the exceptional set, a blocker not containing `x` has multiplicity at most `|w|`**,
by linearity: the edges containing both `x` and a given vertex `y ∈ w` number at most one. -/
lemma blkFib_le_of_not_mem_x [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    {w : 𝓗} (hlin : 𝓗.IsLinear) (hxw : x ∉ (w : Set (Fin n))) :
    (blkFib (K := K) ω x γ w).card ≤ edgeSize (w : Set (Fin n)) := by
  classical
  set s := blkFib (K := K) ω x γ w with hs
  -- pick, for `e ∈ s`, a vertex of `w ∩ e`
  have hpick : ∀ e ∈ s, ∃ y : Fin n, y ∈ (w : Set (Fin n)) ∧ y ∈ (e : Set (Fin n)) := by
    intro e he
    obtain ⟨heU, hbw⟩ := mem_blkFib.mp he
    have hspec := blockerOf_spec (K := K) (x := x) (γ := γ) heU
    rw [hbw] at hspec
    obtain ⟨-, hmeet, -, -⟩ := hspec
    obtain ⟨y, hyw, hye⟩ := hmeet
    exact ⟨y, hyw, hye⟩
  let φ : 𝓗 → Fin n := fun e => if h : e ∈ s then Classical.choose (hpick e h) else x
  have hφval : ∀ e (h : e ∈ s), φ e = Classical.choose (hpick e h) := by
    intro e h
    dsimp only [φ]
    rw [dif_pos h]
  have hφw : ∀ e ∈ s, φ e ∈ (w : Set (Fin n)) := by
    intro e he
    rw [hφval e he]
    exact (Classical.choose_spec (hpick e he)).1
  have hφe : ∀ e ∈ s, φ e ∈ (e : Set (Fin n)) := by
    intro e he
    rw [hφval e he]
    exact (Classical.choose_spec (hpick e he)).2
  -- `φ` is injective on `s` by linearity
  have hinj : Set.InjOn φ (↑s : Set 𝓗) := by
    intro e₁ h₁ e₂ h₂ heq
    by_contra hne
    have hmem1 : φ e₁ ∈ (e₁ : Set (Fin n)) := hφe e₁ h₁
    have hmem2 : φ e₁ ∈ (e₂ : Set (Fin n)) := by rw [heq]; exact hφe e₂ h₂
    have hxe1 : x ∈ (e₁ : Set (Fin n)) := (mem_uncolActSet.mp (mem_blkFib.mp h₁).1).1
    have hxe2 : x ∈ (e₂ : Set (Fin n)) := (mem_uncolActSet.mp (mem_blkFib.mp h₂).1).1
    have hw1 : φ e₁ ∈ (w : Set (Fin n)) := hφw e₁ h₁
    have hsub := hlin e₁.2 e₂.2 (fun hc => hne (Subtype.ext hc))
    have hxy : x ≠ φ e₁ := fun hc => hxw (hc ▸ hw1)
    exact hxy (hsub ⟨hxe1, hxe2⟩ ⟨hmem1, hmem2⟩)
  have hcard := Finset.card_image_of_injOn hinj
  have himage : (s.image φ).card ≤ (verts (w : Set (Fin n))).card := by
    refine Finset.card_le_card ?_
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hφw e he
  rw [edgeSize]
  rw [← hcard]
  exact himage

end Round

end

end Work.Deep.Kahn
