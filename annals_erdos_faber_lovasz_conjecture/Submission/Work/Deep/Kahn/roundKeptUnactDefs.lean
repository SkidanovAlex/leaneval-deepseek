import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.roundUncolDefs

/-!
# `Work.Deep.Kahn.Round`: the vocabulary of the `keptUnactCount` concentration

The statistic `keptUnactCount ω x γ` counts the *unactivated survivors* at the pair `(x,γ)`
(the paper's `keptUnactColsRV`; Kang--Kelly--Kühn--Methuku--Osthus, arXiv:2109.11438,
Section `section:nibble`): the edges `e ∋ x` with `γ ∈ L e` that are **not** activated and
are **not** blocked by any activated `γ`-edge meeting `e` at a vertex other than `x`.

This module fixes the vocabulary of its concentration argument.  For the fixed pair `(x,γ)`:

* `colThru x γ` (from `roundUncolDefs`) — the `γ`-edges through `x` (there are `D` of them in a
  regularised instance);
* `blockSet x γ e` — the *candidate blockers* of `e`: the edges `f` with `x ∉ f`, `γ ∈ L f`,
  `f ∩ e ≠ ∅` (their activation with colour `γ` removes `e` from the count);
* `IsBlocked ω x γ e` — `e` is blocked in the outcome `ω`;
* `counted ω x γ e := ¬ active ω e ∧ ¬ IsBlocked ω x γ e` — the predicate of the count, and
  `keptUnactSet ω x γ = (colThru x γ).filter (counted ω x γ)`;
* `pickBlock ω x γ e` — a chosen blocker of a blocked edge `e` (and `e` itself otherwise);
* `certSetK ω x γ` — the certificate set of the Bruhn--Joos argument: the `γ`-edges through `x`
  together with their chosen blockers.

The structural inputs of the certificate hypothesis of
`Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand_up` for the statistic `D - keptUnactCount ω x γ`
are proved here:

* `pickBlock_fiber_card_le` — a blocker `w` is the chosen blocker of at most `C` edges (by
  linearity: an edge through `x` meeting `w` is determined by the (unique) vertex of `w` it
  contains);
* `not_counted_of_not_counted` — if `e` and its chosen blocker keep their coordinates, the fact
  that `e` is *not* counted is preserved.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

variable {n c C : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)}

/-! ## The candidate blockers -/

/-- The *candidate blockers* of the edge `e` at the pair `(x,γ)`: the edges not containing `x`,
containing `γ` in their list, and meeting `e`.  These are exactly the edges whose activation with
colour `γ` removes `e` from the count `keptUnactCount ω x γ`. -/
def blockSet (x : Fin n) (γ : Fin c) (e : 𝓗) : Finset 𝓗 := by
  classical
  exact Finset.univ.filter (fun f : 𝓗 => x ∉ (f : Set (Fin n)) ∧ γ ∈ L f ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)

@[simp] lemma mem_blockSet {x : Fin n} {γ : Fin c} {e f : 𝓗} :
    f ∈ blockSet (L := L) x γ e ↔ x ∉ (f : Set (Fin n)) ∧ γ ∈ L f ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  simp [blockSet]

lemma not_mem_blockSet_self {x : Fin n} {γ : Fin c} {e : 𝓗}
    (hx : x ∈ (e : Set (Fin n))) : e ∉ blockSet (L := L) x γ e :=
  fun h => (mem_blockSet.mp h).1 hx

/-! ## The predicate counted by `keptUnactCount` -/

/-- `e` is *blocked* at `(x,γ)` by `ω`: some activated `γ`-edge not containing `x` meets `e`. -/
def IsBlocked [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) : Prop :=
  ∃ f : 𝓗, active ω f ∧ x ∉ (f : Set (Fin n)) ∧ colour ω f = γ ∧
    ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty

/-- Decidability of `IsBlocked`, for use in `Finset.filter` in *statements* (where no tactic
block is available to supply `Classical.propDecidable`). -/
instance decidableIsBlocked [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) :
    Decidable (IsBlocked ω x γ e) := by
  classical
  unfold IsBlocked
  infer_instance

lemma isBlocked_iff_blockSet [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) :
    IsBlocked ω x γ e ↔ ∃ f ∈ blockSet (L := L) x γ e, active ω f ∧ colour ω f = γ := by
  classical
  constructor
  · rintro ⟨f, ha, hx, hc, hint⟩
    exact ⟨f, mem_blockSet.mpr ⟨hx, hc ▸ colour_mem ω f, hint⟩, ha, hc⟩
  · rintro ⟨f, hf, ha, hc⟩
    obtain ⟨hx, -, hint⟩ := mem_blockSet.mp hf
    exact ⟨f, ha, hx, hc, hint⟩

/-- The predicate counted by `keptUnactCount ω x γ`: `e` is not activated and not blocked. -/
def counted [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) : Prop :=
  ¬ active ω e ∧ ¬ IsBlocked ω x γ e

lemma not_counted_iff [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗} :
    ¬ counted ω x γ e ↔ active ω e ∨ IsBlocked ω x γ e := by
  classical
  unfold counted
  tauto

/-- The set of edges counted by `keptUnactCount ω x γ`. -/
def keptUnactSet [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact (colThru (L := L) x γ).filter (counted ω x γ)

lemma mem_keptUnactSet [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗} :
    e ∈ keptUnactSet ω x γ ↔ e ∈ colThru (L := L) x γ ∧ counted ω x γ e := by
  classical
  simp [keptUnactSet]

/-- `keptUnactSet` re-expresses the filter defining `keptUnactCount`. -/
lemma keptUnactSet_eq [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    keptUnactSet ω x γ
      = Finset.univ.filter (fun e : 𝓗 => ¬ active ω e ∧ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧
          ∀ f : 𝓗, active ω f → x ∉ (f : Set (Fin n)) → colour ω f = γ →
            ¬ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) := by
  classical
  rw [show keptUnactSet ω x γ
      = (Finset.univ.filter (fun e : 𝓗 => x ∈ (e : Set (Fin n)) ∧ γ ∈ L e)).filter
          (counted ω x γ) from rfl]
  rw [Finset.filter_filter]
  refine Finset.filter_congr ?_
  intro e _
  simp only [counted, IsBlocked, not_exists]
  constructor
  · rintro ⟨⟨hxe, hγL⟩, hna, hblk⟩
    exact ⟨hna, hxe, hγL, fun f hf hxf hc hint => hblk f ⟨hf, hxf, hc, hint⟩⟩
  · rintro ⟨hna, hxe, hγL, hblk⟩
    exact ⟨⟨hxe, hγL⟩, hna, fun f ⟨hf, hxf, hc, hint⟩ => hblk f hf hxf hc hint⟩

lemma keptUnactCount_eq_card [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    keptUnactCount ω x γ = (keptUnactSet ω x γ).card := by
  rw [keptUnactSet_eq]
  rfl

lemma keptUnactSet_subset_colThru [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    keptUnactSet ω x γ ⊆ colThru (L := L) x γ :=
  Finset.filter_subset _ _

lemma keptUnactCount_le_colThru_card [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    keptUnactCount ω x γ ≤ (colThru (L := L) x γ).card := by
  rw [keptUnactCount_eq_card]
  exact Finset.card_le_card (keptUnactSet_subset_colThru ω x γ)

/-- The `γ`-edges through `x` number `D` when the colour degree of `(x,γ)` is `D`. -/
lemma colThru_card {D : ℕ}
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D)
    {x : Fin n} {γ : Fin c} (h : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) :
    (colThru (L := L) x γ).card = D := by
  classical
  have hh := hdeg x γ h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hh
  rw [show colThru (L := L) x γ
      = Finset.univ.filter (fun e : 𝓗 => x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) from rfl]
  exact hh

/-! ## The chosen blocker and the certificate set -/

/-- A chosen blocker of `e` when `e` is a blocked `γ`-edge through `x`, and `e` itself
otherwise. -/
def pickBlock [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) (e : 𝓗) : 𝓗 := by
  classical
  exact if h : e ∈ colThru (L := L) x γ ∧ ¬ active ω e ∧ IsBlocked ω x γ e then
    Classical.choose h.2.2
  else e

lemma pickBlock_spec [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗}
    (h : e ∈ colThru (L := L) x γ ∧ ¬ active ω e ∧ IsBlocked ω x γ e) :
    active ω (pickBlock ω x γ e) ∧ x ∉ (pickBlock ω x γ e : Set (Fin n)) ∧
      colour ω (pickBlock ω x γ e) = γ ∧
      (((pickBlock ω x γ e : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) := by
  rw [pickBlock, dif_pos h]
  exact Classical.choose_spec h.2.2

lemma pickBlock_eq_self_of_not [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗}
    (h : ¬ (e ∈ colThru (L := L) x γ ∧ ¬ active ω e ∧ IsBlocked ω x γ e)) :
    pickBlock ω x γ e = e := by
  rw [pickBlock, dif_neg h]

/-- The certificate set of the Bruhn--Joos argument: the `γ`-edges through `x` together with
their chosen blockers. -/
def certSetK [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 := by
  classical
  exact colThru (L := L) x γ ∪ (colThru (L := L) x γ).image (pickBlock ω x γ)

lemma certSetK_card_le [NeZero K] (ω : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    (certSetK ω x γ).card ≤ 2 * (colThru (L := L) x γ).card := by
  classical
  refine le_trans (Finset.card_union_le _ _) ?_
  have h := Finset.card_image_le (s := colThru (L := L) x γ) (f := pickBlock ω x γ)
  omega

lemma mem_certSetK_of_mem_colThru [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    {e : 𝓗} (he : e ∈ colThru (L := L) x γ) : e ∈ certSetK ω x γ :=
  Finset.mem_union_left _ he

lemma mem_certSetK_pickBlock [NeZero K] {ω : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗}
    (he : e ∈ colThru (L := L) x γ) : pickBlock ω x γ e ∈ certSetK ω x γ :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)

/-- **Preservation of "not counted".**  If `e` is a `γ`-edge through `x` and both `e` and its
chosen blocker keep their coordinates, then `e` is not counted at the new outcome. -/
lemma not_counted_of_not_counted [NeZero K] {ω ω' : Space K 𝓗 L} {x : Fin n} {γ : Fin c}
    {e : 𝓗} (he : e ∈ colThru (L := L) x γ) (h1 : ω e = ω' e)
    (h2 : ω (pickBlock ω x γ e) = ω' (pickBlock ω x γ e)) (h : ¬ counted ω x γ e) :
    ¬ counted ω' x γ e := by
  rw [not_counted_iff] at h ⊢
  by_cases hact : active ω e
  · exact Or.inl ((active_congr (K := K) h1).mp hact)
  · have hb : IsBlocked ω x γ e := h.resolve_left hact
    obtain ⟨ha, hx, hc, hint⟩ := pickBlock_spec (K := K) ⟨he, hact, hb⟩
    exact Or.inr ⟨pickBlock ω x γ e, (active_congr (K := K) h2).mp ha, hx,
      (colour_congr (K := K) h2) ▸ hc, hint⟩

/-! ## The multiplicity of a blocker -/

/-- **A blocker is the chosen blocker of at most `C` edges**, by linearity: the edges through `x`
meeting a given edge `w` are determined by the (unique) vertex of `w` that they contain. -/
lemma pickBlock_fiber_card_le [NeZero K] (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) = C) (ω : Space K 𝓗 L) (x : Fin n)
    (γ : Fin c) (w : 𝓗) :
    ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧ IsBlocked ω x γ e ∧
      pickBlock ω x γ e = w)).card ≤ C := by
  classical
  set S := (colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧ IsBlocked ω x γ e ∧
    pickBlock ω x γ e = w) with hS
  have memS : ∀ e : 𝓗, e ∈ S ↔ e ∈ colThru (L := L) x γ ∧ ¬ active ω e ∧
      IsBlocked ω x γ e ∧ pickBlock ω x γ e = w := by
    intro e
    simp only [hS, Finset.mem_filter]
  rcases Finset.eq_empty_or_nonempty S with hempty | ⟨e0, he0⟩
  · rw [hempty]; exact Nat.zero_le C
  · have hxw : x ∉ (w : Set (Fin n)) := by
      obtain ⟨h1, h2, h3, h4⟩ := (memS e0).mp he0
      obtain ⟨-, hxw, -, -⟩ := pickBlock_spec (K := K) ⟨h1, h2, h3⟩
      rwa [h4] at hxw
    have hpick : ∀ e ∈ S, ∃ y : Fin n, y ∈ (w : Set (Fin n)) ∧ y ∈ (e : Set (Fin n)) := by
      intro e he
      obtain ⟨h1, h2, h3, h4⟩ := (memS e).mp he
      obtain ⟨-, -, -, hint⟩ := pickBlock_spec (K := K) ⟨h1, h2, h3⟩
      rw [h4] at hint
      obtain ⟨y, hyw, hye⟩ := hint
      exact ⟨y, hyw, hye⟩
    let φ : 𝓗 → Fin n := fun e => if h : e ∈ S then Classical.choose (hpick e h) else x
    have hφval : ∀ e (h : e ∈ S), φ e = Classical.choose (hpick e h) := by
      intro e h; dsimp only [φ]; rw [dif_pos h]
    have hφw : ∀ e ∈ S, φ e ∈ (w : Set (Fin n)) := by
      intro e he; rw [hφval e he]; exact (Classical.choose_spec (hpick e he)).1
    have hφe : ∀ e ∈ S, φ e ∈ (e : Set (Fin n)) := by
      intro e he; rw [hφval e he]; exact (Classical.choose_spec (hpick e he)).2
    have hxe : ∀ e ∈ S, x ∈ (e : Set (Fin n)) := by
      intro e he; exact (mem_colThru.mp ((memS e).mp he).1).1
    have hinj : Set.InjOn φ (↑S : Set 𝓗) := by
      intro e₁ h₁ e₂ h₂ heq
      by_contra hne
      have hmem1 : φ e₁ ∈ (e₁ : Set (Fin n)) := hφe e₁ h₁
      have hmem2 : φ e₁ ∈ (e₂ : Set (Fin n)) := by rw [heq]; exact hφe e₂ h₂
      have hw1 : φ e₁ ∈ (w : Set (Fin n)) := hφw e₁ h₁
      have hsub := hlin e₁.2 e₂.2 (fun hc => hne (Subtype.ext hc))
      have hxeq : x = φ e₁ := hsub ⟨hxe e₁ h₁, hxe e₂ h₂⟩ ⟨hmem1, hmem2⟩
      exact hxw (hxeq.symm ▸ hw1)
    have hcard := Finset.card_image_of_injOn hinj
    have himage : (S.image φ).card ≤ (verts (w : Set (Fin n))).card := by
      refine Finset.card_le_card ?_
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨e, he, rfl⟩ := hy
      simpa [verts] using hφw e he
    have hfin : S.card ≤ C := by
      rw [← hcard, ← hsize w]
      exact himage
    exact hfin

end Round

end

end Work.Deep.Kahn
