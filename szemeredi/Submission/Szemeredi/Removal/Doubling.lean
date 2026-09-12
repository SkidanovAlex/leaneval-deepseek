import Mathlib
import Submission.Szemeredi.Removal.GCData

/-!
# The doubling construction (Tao, arXiv:math/0503572, §4)

For the Cauchy–Schwarz step of the generalized counting lemma one replaces the
hypergraph bundle `G` by a bundle of roughly twice the size, in which the complement
of the top edge `g₀` is duplicated.  The index set is
`κ̃ = (κ ∖ g₀) × Bool ⊕ g₀`, so that the `g₀` coordinates are shared between the two
copies.  This "single-copy" structure of the lower sets is exactly what makes the
`L²`-bound (H3) transport to the doubled bundle.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The index set of the doubled bundle: two copies of the complement of `g₀`, plus `g₀`. -/
abbrev DblIdx (g₀ : Finset κ) : Type _ :=
  ({k : κ // k ∉ g₀} × Bool) ⊕ {k : κ // k ∈ g₀}

/-- The projection of the doubled bundle. -/
def dblπ (π : κ → ι) (g₀ : Finset κ) : DblIdx g₀ → ι :=
  Sum.elim (fun a => π a.1.val) (fun b => π b.val)

@[simp] theorem dblπ_inl (π : κ → ι) (g₀ : Finset κ) (a : {k : κ // k ∉ g₀}) (i : Bool) :
    dblπ π g₀ (Sum.inl (a, i)) = π a.val := rfl

@[simp] theorem dblπ_inr (π : κ → ι) (g₀ : Finset κ) (b : {k : κ // k ∈ g₀}) :
    dblπ π g₀ (Sum.inr b) = π b.val := rfl

/-- The `i`-th embedding of `κ` into the doubled index set. -/
noncomputable def dblEmb (g₀ : Finset κ) (i : Bool) (k : κ) : DblIdx g₀ :=
  if hk : k ∈ g₀ then Sum.inr ⟨k, hk⟩ else Sum.inl (⟨k, hk⟩, i)

theorem dblEmb_injective (g₀ : Finset κ) (i : Bool) : Function.Injective (dblEmb g₀ i) := by
  intro k k' h
  by_cases hk : k ∈ g₀ <;> by_cases hk' : k' ∈ g₀
  · rw [dblEmb, dif_pos hk, dblEmb, dif_pos hk'] at h
    exact congrArg Subtype.val (Sum.inr.inj h)
  · rw [dblEmb, dif_pos hk, dblEmb, dif_neg hk'] at h
    exact absurd h (by simp)
  · rw [dblEmb, dif_neg hk, dblEmb, dif_pos hk'] at h
    exact absurd h (by simp)
  · rw [dblEmb, dif_neg hk, dblEmb, dif_neg hk'] at h
    exact congrArg (fun p : {k : κ // k ∉ g₀} × Bool => p.1.val) (Sum.inl.inj h)

theorem dblEmb_eq_inr (g₀ : Finset κ) (i : Bool) {k : κ} (hk : k ∈ g₀) :
    dblEmb g₀ i k = Sum.inr ⟨k, hk⟩ := dif_pos hk

theorem dblEmb_eq_inl (g₀ : Finset κ) (i : Bool) {k : κ} (hk : k ∉ g₀) :
    dblEmb g₀ i k = Sum.inl (⟨k, hk⟩, i) := dif_neg hk

/-- The `i`-th copy of a bundle edge `h` in the doubled bundle. -/
noncomputable def dblEdge (g₀ : Finset κ) (i : Bool) (h : Finset κ) : Finset (DblIdx g₀) :=
  h.image (dblEmb g₀ i)

@[simp] theorem mem_dblEdge (g₀ : Finset κ) (i : Bool) (h : Finset κ) (kk : DblIdx g₀) :
    kk ∈ dblEdge g₀ i h ↔ ∃ k ∈ h, dblEmb g₀ i k = kk := Finset.mem_image

theorem mem_dblEdge_inr (g₀ : Finset κ) (i : Bool) (h : Finset κ) (b : {k : κ // k ∈ g₀}) :
    Sum.inr b ∈ dblEdge g₀ i h ↔ b.val ∈ h := by
  rw [mem_dblEdge]
  constructor
  · rintro ⟨k, hk, hkb⟩
    by_cases hkg : k ∈ g₀
    · rw [dblEmb_eq_inr g₀ i hkg] at hkb
      rw [← congrArg Subtype.val (Sum.inr.inj hkb)]
      exact hk
    · rw [dblEmb_eq_inl g₀ i hkg] at hkb
      exact absurd hkb (by simp)
  · intro hb
    exact ⟨b.val, hb, dblEmb_eq_inr g₀ i b.2⟩

theorem mem_dblEdge_inl (g₀ : Finset κ) (i : Bool) (h : Finset κ)
    (a : {k : κ // k ∉ g₀}) (j : Bool) :
    Sum.inl (a, j) ∈ dblEdge g₀ i h ↔ a.val ∈ h ∧ j = i := by
  rw [mem_dblEdge]
  constructor
  · rintro ⟨k, hk, hka⟩
    by_cases hkg : k ∈ g₀
    · rw [dblEmb_eq_inr g₀ i hkg] at hka
      exact absurd hka (by simp)
    · rw [dblEmb_eq_inl g₀ i hkg] at hka
      have hproj := Sum.inl.inj hka
      have ha1 : (⟨k, hkg⟩ : {k : κ // k ∉ g₀}) = a := congrArg Prod.fst hproj
      have ha2 : i = j := congrArg Prod.snd hproj
      refine ⟨?_, ha2.symm⟩
      rw [← congrArg Subtype.val ha1]
      exact hk
  · rintro ⟨ha, hji⟩
    rw [hji]
    exact ⟨a.val, ha, dblEmb_eq_inl g₀ i a.2⟩

theorem dblEdge_card (g₀ : Finset κ) (i : Bool) (h : Finset κ) :
    (dblEdge g₀ i h).card = h.card :=
  Finset.card_image_of_injective h (dblEmb_injective g₀ i)

theorem dblEdge_mono (g₀ : Finset κ) (i : Bool) {h h' : Finset κ} (hh : h' ⊆ h) :
    dblEdge g₀ i h' ⊆ dblEdge g₀ i h := Finset.image_subset_image hh

theorem dblEdge_image (π : κ → ι) (g₀ : Finset κ) (i : Bool) (h : Finset κ) :
    (dblEdge g₀ i h).image (dblπ π g₀) = h.image π := by
  rw [dblEdge, Finset.image_image]
  congr 1
  funext k
  show dblπ π g₀ (dblEmb g₀ i k) = π k
  by_cases hk : k ∈ g₀
  · rw [dblEmb_eq_inr g₀ i hk]; rfl
  · rw [dblEmb_eq_inl g₀ i hk]; rfl

/-- For `h ⊆ g₀` the two copies of an edge coincide. -/
theorem dblEdge_eq_of_subset (g₀ : Finset κ) {h : Finset κ} (hh : h ⊆ g₀) (i : Bool) :
    dblEdge g₀ i h = dblEdge g₀ false h := by
  apply Finset.Subset.antisymm
  · intro kk hk
    rw [mem_dblEdge] at hk ⊢
    obtain ⟨k, hkk, rfl⟩ := hk
    exact ⟨k, hkk, (dblEmb_eq_inr g₀ false (hh hkk)).trans
      (dblEmb_eq_inr g₀ i (hh hkk)).symm⟩
  · intro kk hk
    rw [mem_dblEdge] at hk ⊢
    obtain ⟨k, hkk, rfl⟩ := hk
    exact ⟨k, hkk, (dblEmb_eq_inr g₀ i (hh hkk)).trans
      (dblEmb_eq_inr g₀ false (hh hkk)).symm⟩

/-- Every subset of `dblEdge g₀ i h` is itself of the form `dblEdge g₀ i h'`. -/
theorem subset_dblEdge (g₀ : Finset κ) (i : Bool) {h : Finset κ} {gg : Finset (DblIdx g₀)}
    (hg : gg ⊆ dblEdge g₀ i h) :
    ∃ h' ⊆ h, dblEdge g₀ i h' = gg := by
  classical
  refine ⟨h.filter (fun k => dblEmb g₀ i k ∈ gg), Finset.filter_subset _ _, ?_⟩
  apply Finset.Subset.antisymm
  · intro kk hk
    rw [mem_dblEdge] at hk
    obtain ⟨k, hkk, rfl⟩ := hk
    exact (Finset.mem_filter.mp hkk).2
  · intro kk hk
    have hk' := hg hk
    rw [mem_dblEdge] at hk'
    obtain ⟨k, hkk, rfl⟩ := hk'
    exact (mem_dblEdge g₀ i _ _).mpr ⟨k, Finset.mem_filter.mpr ⟨hkk, hk⟩, rfl⟩

/-- Injectivity of `dblπ` on a doubled edge. -/
theorem dblπ_injOn_dblEdge (π : κ → ι) (g₀ : Finset κ) (i : Bool) {h : Finset κ}
    (hinj : ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) :
    ∀ a ∈ dblEdge g₀ i h, ∀ b ∈ dblEdge g₀ i h, dblπ π g₀ a = dblπ π g₀ b → a = b := by
  intro a ha b hb hab
  rw [mem_dblEdge] at ha hb
  obtain ⟨ka, hka, rfl⟩ := ha
  obtain ⟨kb, hkb, rfl⟩ := hb
  rw [dblEmb, dblEmb] at hab
  by_cases hka' : ka ∈ g₀ <;> by_cases hkb' : kb ∈ g₀
  · rw [dif_pos hka', dif_pos hkb', dblπ_inr, dblπ_inr] at hab
    rw [hinj ka hka kb hkb hab]
  · rw [dif_pos hka', dif_neg hkb'] at hab
    rw [dblπ_inr, dblπ_inl] at hab
    exact (hkb' (hinj ka hka kb hkb hab ▸ hka')).elim
  · rw [dif_neg hka', dif_pos hkb'] at hab
    rw [dblπ_inl, dblπ_inr] at hab
    exact (hka' (hinj kb hkb ka hka hab.symm ▸ hkb')).elim
  · rw [dif_neg hka', dif_neg hkb', dblπ_inl, dblπ_inl] at hab
    rw [hinj ka hka kb hkb hab]


/-! ## The doubled hypergraph `G̃` -/

/-- The edges of `G` strictly below `g₀`. -/
noncomputable def Glt (G : Finset (Finset κ)) (g₀ : Finset κ) : Finset (Finset κ) :=
  G.filter (fun h => h ⊂ g₀)

/-- The edges of `G` incomparable with `g₀` of order at most `d'-1`. -/
noncomputable def Ggt (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) : Finset (Finset κ) :=
  G.filter (fun h => ¬ h ⊂ g₀ ∧ h.card ≤ d' - 1)

theorem mem_Glt {G : Finset (Finset κ)} {g₀ h : Finset κ} :
    h ∈ Glt G g₀ ↔ h ∈ G ∧ h ⊂ g₀ := Finset.mem_filter

theorem mem_Ggt {G : Finset (Finset κ)} {g₀ h : Finset κ} {d' : ℕ} :
    h ∈ Ggt G g₀ d' ↔ h ∈ G ∧ ¬ h ⊂ g₀ ∧ h.card ≤ d' - 1 := Finset.mem_filter

/-- The doubled hypergraph. -/
noncomputable def dblG (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) :
    Finset (Finset (DblIdx g₀)) :=
  ((Glt G g₀).image (dblEdge g₀ false) ∪ (Ggt G g₀ d').image (dblEdge g₀ false))
    ∪ (Ggt G g₀ d').image (dblEdge g₀ true)

theorem dblEmb_mem (g₀ : Finset κ) (i : Bool) (h : Finset κ) (k : κ) :
    dblEmb g₀ i k ∈ dblEdge g₀ i h ↔ k ∈ h := by
  rw [mem_dblEdge]
  exact ⟨fun ⟨k', hk', hkk⟩ => by rw [dblEmb_injective g₀ i hkk] at hk'; exact hk',
    fun hk => ⟨k, hk, rfl⟩⟩

theorem dblEdge_eq_of_eq (g₀ : Finset κ) (i : Bool) {h h' : Finset κ}
    (heq : dblEdge g₀ i h = dblEdge g₀ i h') : h = h' := by
  ext k
  rw [← dblEmb_mem g₀ i h k, ← dblEmb_mem g₀ i h' k, heq]

theorem dblEdge_false_ne_true (g₀ : Finset κ) {h h' : Finset κ} (hh : h ⊆ g₀)
    (hh' : ¬ h' ⊆ g₀) : dblEdge g₀ false h ≠ dblEdge g₀ true h' := by
  intro heq
  obtain ⟨k, hk, hkg⟩ : ∃ k ∈ h', k ∉ g₀ := by
    by_contra hc
    push_neg at hc
    exact hh' fun x hx => hc x hx
  have h1 : Sum.inl (⟨k, hkg⟩, true) ∈ dblEdge g₀ true h' :=
    (mem_dblEdge_inl g₀ true h' ⟨k, hkg⟩ true).mpr ⟨hk, rfl⟩
  have h2 : Sum.inl (⟨k, hkg⟩, true) ∉ dblEdge g₀ false h := by
    rw [mem_dblEdge_inl]
    rintro ⟨-, hj⟩
    exact Bool.noConfusion hj
  rw [heq] at h2
  exact h2 h1

theorem dblEdge_false_ne_true' (g₀ : Finset κ) {h h' : Finset κ} (hh : ¬ h ⊆ g₀)
    (hh' : h' ⊆ g₀) : dblEdge g₀ false h ≠ dblEdge g₀ true h' := by
  intro heq
  obtain ⟨k, hk, hkg⟩ : ∃ k ∈ h, k ∉ g₀ := by
    by_contra hc
    push_neg at hc
    exact hh fun x hx => hc x hx
  have h1 : Sum.inl (⟨k, hkg⟩, false) ∈ dblEdge g₀ false h :=
    (mem_dblEdge_inl g₀ false h ⟨k, hkg⟩ false).mpr ⟨hk, rfl⟩
  have h2 : Sum.inl (⟨k, hkg⟩, false) ∉ dblEdge g₀ true h' := by
    rw [mem_dblEdge_inl]
    rintro ⟨-, hj⟩
    exact Bool.noConfusion hj
  rw [heq] at h1
  exact h2 h1

theorem mem_dblG {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ} {gg : Finset (DblIdx g₀)} :
    gg ∈ dblG G g₀ d' ↔
      ∃ h ∈ G, (h ⊂ g₀ ∧ gg = dblEdge g₀ false h)
        ∨ (¬ h ⊂ g₀ ∧ h.card ≤ d' - 1 ∧ (gg = dblEdge g₀ false h ∨ gg = dblEdge g₀ true h)) := by
  classical
  have h1 : gg ∈ (Glt G g₀).image (dblEdge g₀ false) ↔
      ∃ h ∈ G, h ⊂ g₀ ∧ gg = dblEdge g₀ false h := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨h, hh, hge⟩
      exact ⟨h, (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2, hge.symm⟩
    · rintro ⟨h, hh, hlt, hge⟩
      exact ⟨h, Finset.mem_filter.mpr ⟨hh, hlt⟩, hge.symm⟩
  have h2 : gg ∈ (Ggt G g₀ d').image (dblEdge g₀ false) ↔
      ∃ h ∈ G, ¬ h ⊂ g₀ ∧ h.card ≤ d' - 1 ∧ gg = dblEdge g₀ false h := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨h, hh, hge⟩
      exact ⟨h, (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1,
        (Finset.mem_filter.mp hh).2.2, hge.symm⟩
    · rintro ⟨h, hh, hn, hc, hge⟩
      exact ⟨h, Finset.mem_filter.mpr ⟨hh, ⟨hn, hc⟩⟩, hge.symm⟩
  have h3 : gg ∈ (Ggt G g₀ d').image (dblEdge g₀ true) ↔
      ∃ h ∈ G, ¬ h ⊂ g₀ ∧ h.card ≤ d' - 1 ∧ gg = dblEdge g₀ true h := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨h, hh, hge⟩
      exact ⟨h, (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.1,
        (Finset.mem_filter.mp hh).2.2, hge.symm⟩
    · rintro ⟨h, hh, hn, hc, hge⟩
      exact ⟨h, Finset.mem_filter.mpr ⟨hh, ⟨hn, hc⟩⟩, hge.symm⟩
  rw [dblG, Finset.mem_union, Finset.mem_union, h1, h2, h3]
  constructor
  · intro hmem
    rcases hmem with hmem | hmem
    · rcases hmem with hmem | hmem
      · obtain ⟨h, hh, hlt, hge⟩ := hmem
        exact ⟨h, hh, Or.inl ⟨hlt, hge⟩⟩
      · obtain ⟨h, hh, hn, hc, hge⟩ := hmem
        exact ⟨h, hh, Or.inr ⟨hn, hc, Or.inl hge⟩⟩
    · obtain ⟨h, hh, hn, hc, hge⟩ := hmem
      exact ⟨h, hh, Or.inr ⟨hn, hc, Or.inr hge⟩⟩
  · rintro ⟨h, hh, hinl | hinr⟩
    · exact Or.inl (Or.inl ⟨h, hh, hinl.1, hinl.2⟩)
    · rcases hinr with ⟨hn, hc, h5 | h5⟩
      · exact Or.inl (Or.inr ⟨h, hh, hn, hc, h5⟩)
      · exact Or.inr ⟨h, hh, hn, hc, h5⟩

theorem dblG_card_le {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ} (hg₀ : g₀.card = d')
    {gg : Finset (DblIdx g₀)} (hg : gg ∈ dblG G g₀ d') : gg.card ≤ d' - 1 := by
  obtain ⟨h, _hh, hinl | hinr⟩ := (mem_dblG).mp hg
  · rw [hinl.2, dblEdge_card]
    have h1 : h.card < g₀.card := Finset.card_lt_card hinl.1
    omega
  · rcases hinr.2.2 with h1 | h1
    · rw [h1, dblEdge_card]; exact hinr.2.1
    · rw [h1, dblEdge_card]; exact hinr.2.1

/-- **`G̃` is closed under inclusion.** -/
theorem dblG_closed {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ}
    (hG : ∀ h ∈ G, ∀ h' ⊆ h, h' ∈ G) {gg : Finset (DblIdx g₀)} (hg : gg ∈ dblG G g₀ d')
    {gg' : Finset (DblIdx g₀)} (hgg' : gg' ⊆ gg) : gg' ∈ dblG G g₀ d' := by
  obtain ⟨h, hh, hinl | hinr⟩ := (mem_dblG).mp hg
  · obtain ⟨h', hh', heq⟩ := subset_dblEdge (g₀ := g₀) (i := false) (h := h) (gg := gg')
      (by rw [← hinl.2]; exact hgg')
    have hh'G : h' ∈ G := hG h hh h' hh'
    have h'sub : h' ⊆ g₀ := Subset.trans hh' hinl.1.1
    have h'ne : h' ≠ g₀ := fun heq' =>
      (Finset.ssubset_iff_subset_ne.mp hinl.1).2 (Subset.antisymm hinl.1.1 (heq' ▸ hh'))
    rw [mem_dblG]
    exact ⟨h', hh'G, Or.inl ⟨Finset.ssubset_iff_subset_ne.mpr ⟨h'sub, h'ne⟩, heq.symm⟩⟩
  · rcases hinr.2.2 with h1 | h1
    · obtain ⟨h', hh', heq⟩ := subset_dblEdge (g₀ := g₀) (i := false) (h := h) (gg := gg')
        (by rw [← h1]; exact hgg')
      have hh'G : h' ∈ G := hG h hh h' hh'
      rw [mem_dblG]
      by_cases h'sub : h' ⊂ g₀
      · exact ⟨h', hh'G, Or.inl ⟨h'sub, heq.symm⟩⟩
      · refine ⟨h', hh'G, Or.inr ⟨h'sub, ?_, Or.inl heq.symm⟩⟩
        have := Finset.card_le_card hh'
        omega
    · obtain ⟨h', hh', heq⟩ := subset_dblEdge (g₀ := g₀) (i := true) (h := h) (gg := gg')
        (by rw [← h1]; exact hgg')
      have hh'G : h' ∈ G := hG h hh h' hh'
      rw [mem_dblG]
      by_cases h'sub : h' ⊂ g₀
      · refine ⟨h', hh'G, Or.inl ⟨h'sub, ?_⟩⟩
        rw [← heq, dblEdge_eq_of_subset g₀ h'sub.1 true]
      · refine ⟨h', hh'G, Or.inr ⟨h'sub, ?_, Or.inr heq.symm⟩⟩
        have := Finset.card_le_card hh'
        omega

/-! ## The lifted data for the doubled bundle -/

/-- The lift of the ambient set family along a bundle edge, guarded to be empty
outside `G`. -/
noncomputable def AgOf (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (h : Finset κ) :
    Finset (BPt V π) :=
  if hh : h ∈ G then liftSet (V := V) π h (hinj h hh) (A (h.image π)) else ∅

theorem AgOf_of_mem (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G) :
    AgOf (V := V) A π G hinj h = liftSet (V := V) π h (hinj h hh) (A (h.image π)) :=
  dif_pos hh

/-- The lifted data for the doubled bundle. -/
noncomputable def AgOfDbl (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (i : Bool)
    (h : Finset κ) : Finset (BPt V (dblπ π g₀)) :=
  if hh : h ∈ G then
    liftSet (V := V) (dblπ π g₀) (dblEdge g₀ i h) (dblπ_injOn_dblEdge π g₀ i (hinj h hh))
      (A (h.image π))
  else ∅

theorem AgOfDbl_of_mem (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (i : Bool)
    {h : Finset κ} (hh : h ∈ G) :
    AgOfDbl (V := V) A π G g₀ hinj i h
      = liftSet (V := V) (dblπ π g₀) (dblEdge g₀ i h)
          (dblπ_injOn_dblEdge π g₀ i (hinj h hh)) (A (h.image π)) :=
  dif_pos hh


/-! ## The point space of the doubled bundle as a product -/

/-- The `g₀`-coordinates of a bundle. -/
abbrev W1 (π : κ → ι) (g₀ : Finset κ) : Type _ := (k : {k : κ // k ∈ g₀}) → V (π k.val)

/-- The extra copy of the complement of `g₀`. -/
abbrev W2 (π : κ → ι) (g₀ : Finset κ) : Type _ := (k : {k : κ // k ∉ g₀}) → V (π k.val)

/-- The inverse splitting of the doubled point space. -/
noncomputable def dblInv (π : κ → ι) (g₀ : Finset κ)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) : BPt V (dblπ π g₀) :=
  fun kk => match kk with
    | Sum.inl (a, false) => p.1.1 a
    | Sum.inl (a, true) => p.1.2 a
    | Sum.inr b => p.2 b

/-- The point space of the doubled bundle is the `g₀`-coordinates together with two
copies of its complement. -/
noncomputable def dblEquiv (π : κ → ι) (g₀ : Finset κ) :
    BPt V (dblπ π g₀) ≃ (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀ where
  toFun v := (((fun a => v (Sum.inl (a, false))), (fun a => v (Sum.inl (a, true)))),
    (fun b => v (Sum.inr b)))
  invFun := dblInv (V := V) π g₀
  left_inv v := by
    funext kk
    rcases kk with ⟨a, j⟩ | b
    · cases j <;> rfl
    · rfl
  right_inv p := by
    obtain ⟨⟨u₀, u₁⟩, w⟩ := p
    rfl

@[simp] theorem dblEquiv_symm_inl_false (π : κ → ι) (g₀ : Finset κ)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀)
    (a : {k : κ // k ∉ g₀}) :
    ((dblEquiv (V := V) π g₀).symm p) (Sum.inl (a, false)) = p.1.1 a := rfl

@[simp] theorem dblEquiv_symm_inl_true (π : κ → ι) (g₀ : Finset κ)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀)
    (a : {k : κ // k ∉ g₀}) :
    ((dblEquiv (V := V) π g₀).symm p) (Sum.inl (a, true)) = p.1.2 a := rfl

@[simp] theorem dblEquiv_symm_inr (π : κ → ι) (g₀ : Finset κ)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀)
    (b : {k : κ // k ∈ g₀}) :
    ((dblEquiv (V := V) π g₀).symm p) (Sum.inr b) = p.2 b := rfl

/-- Membership in the first lift of an edge. -/
theorem mem_liftSet_dblEdge_false (π : κ → ι) (g₀ : Finset κ) (A : Finset ι → Finset (Pt V))
    (h : Finset κ) (hinj : ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) :
    (dblEquiv (V := V) π g₀).symm p ∈ liftSet (V := V) (dblπ π g₀) (dblEdge g₀ false h)
        (dblπ_injOn_dblEdge π g₀ false hinj) (A (h.image π))
      ↔ combine (V := V) π g₀ p.2 p.1.1 ∈ liftSet (V := V) π h hinj (A (h.image π)) := by
  rw [mem_liftSet_iff, mem_liftSet_iff]
  refine exists_congr (fun x => and_congr_right (fun _ => ?_))
  constructor
  · intro hh k hk
    by_cases hkg : k ∈ g₀
    · have h1 := hh (Sum.inr ⟨k, hkg⟩) ((mem_dblEdge_inr g₀ false h ⟨k, hkg⟩).mpr hk)
      rw [combine_apply_mem (V := V) π g₀ p.2 p.1.1 hkg]
      simpa using h1
    · have h1 := hh (Sum.inl (⟨k, hkg⟩, false))
        ((mem_dblEdge_inl g₀ false h ⟨k, hkg⟩ false).mpr ⟨hk, rfl⟩)
      rw [combine_apply_notMem (V := V) π g₀ p.2 p.1.1 hkg]
      simpa using h1
  · intro hh kk hk
    rw [mem_dblEdge] at hk
    obtain ⟨k, hkk, rfl⟩ := hk
    by_cases hkg : k ∈ g₀
    · rw [dblEmb_eq_inr g₀ false hkg]
      have h1 := hh k hkk
      rw [combine_apply_mem (V := V) π g₀ p.2 p.1.1 hkg] at h1
      simpa using h1
    · rw [dblEmb_eq_inl g₀ false hkg]
      have h1 := hh k hkk
      rw [combine_apply_notMem (V := V) π g₀ p.2 p.1.1 hkg] at h1
      simpa using h1

/-- Membership in the second lift of an edge. -/
theorem mem_liftSet_dblEdge_true (π : κ → ι) (g₀ : Finset κ) (A : Finset ι → Finset (Pt V))
    (h : Finset κ) (hinj : ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) :
    (dblEquiv (V := V) π g₀).symm p ∈ liftSet (V := V) (dblπ π g₀) (dblEdge g₀ true h)
        (dblπ_injOn_dblEdge π g₀ true hinj) (A (h.image π))
      ↔ combine (V := V) π g₀ p.2 p.1.2 ∈ liftSet (V := V) π h hinj (A (h.image π)) := by
  rw [mem_liftSet_iff, mem_liftSet_iff]
  refine exists_congr (fun x => and_congr_right (fun _ => ?_))
  constructor
  · intro hh k hk
    by_cases hkg : k ∈ g₀
    · have h1 := hh (Sum.inr ⟨k, hkg⟩) ((mem_dblEdge_inr g₀ true h ⟨k, hkg⟩).mpr hk)
      rw [combine_apply_mem (V := V) π g₀ p.2 p.1.2 hkg]
      simpa using h1
    · have h1 := hh (Sum.inl (⟨k, hkg⟩, true))
        ((mem_dblEdge_inl g₀ true h ⟨k, hkg⟩ true).mpr ⟨hk, rfl⟩)
      rw [combine_apply_notMem (V := V) π g₀ p.2 p.1.2 hkg]
      simpa using h1
  · intro hh kk hk
    rw [mem_dblEdge] at hk
    obtain ⟨k, hkk, rfl⟩ := hk
    by_cases hkg : k ∈ g₀
    · rw [dblEmb_eq_inr g₀ true hkg]
      have h1 := hh k hkk
      rw [combine_apply_mem (V := V) π g₀ p.2 p.1.2 hkg] at h1
      simpa using h1
    · rw [dblEmb_eq_inl g₀ true hkg]
      have h1 := hh k hkk
      rw [combine_apply_notMem (V := V) π g₀ p.2 p.1.2 hkg] at h1
      simpa using h1


/-! ## The lifted data for the doubled bundle -/

/-- The injectivity of `dblπ` on an element of `G̃`. -/
noncomputable def dblInjOn (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) (π : κ → ι)
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (gg : Finset (DblIdx g₀))
    (hm : gg ∈ dblG G g₀ d') :
    ∀ a ∈ gg, ∀ b ∈ gg, dblπ π g₀ a = dblπ π g₀ b → a = b := by
  classical
  obtain ⟨H, hH, hcase⟩ := (mem_dblG).mp hm
  rcases hcase with ⟨_, heq⟩ | ⟨_, _, heq | heq⟩
  · exact heq.symm ▸ dblπ_injOn_dblEdge π g₀ false (hinj H hH)
  · exact heq.symm ▸ dblπ_injOn_dblEdge π g₀ false (hinj H hH)
  · exact heq.symm ▸ dblπ_injOn_dblEdge π g₀ true (hinj H hH)

/-- The lifted data of the doubled bundle. -/
noncomputable def AgDbl (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (gg : Finset (DblIdx g₀)) : Finset (BPt V (dblπ π g₀)) :=
  if hm : gg ∈ dblG G g₀ d' then
    liftSet (V := V) (dblπ π g₀) gg (dblInjOn G g₀ d' π hinj gg hm)
      (A (gg.image (dblπ π g₀)))
  else ∅

theorem AgDbl_of_mem (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    {gg : Finset (DblIdx g₀)} (hm : gg ∈ dblG G g₀ d') :
    AgDbl (V := V) A π G g₀ d' hinj gg
      = liftSet (V := V) (dblπ π g₀) gg (dblInjOn G g₀ d' π hinj gg hm)
          (A (gg.image (dblπ π g₀))) := dif_pos hm

theorem AgDbl_dblEdge_false (A : Finset ι → Finset (Pt V)) (π : κ → ι)
    (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ)
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G)
    (hm : dblEdge g₀ false h ∈ dblG G g₀ d') :
    AgDbl (V := V) A π G g₀ d' hinj (dblEdge g₀ false h)
      = liftSet (V := V) (dblπ π g₀) (dblEdge g₀ false h)
          (dblπ_injOn_dblEdge π g₀ false (hinj h hh)) (A (h.image π)) := by
  rw [AgDbl_of_mem (V := V) A π G g₀ d' hinj hm,
    show dblInjOn G g₀ d' π hinj (dblEdge g₀ false h) hm
        = dblπ_injOn_dblEdge π g₀ false (hinj h hh) from Subsingleton.elim _ _,
    dblEdge_image]

theorem AgDbl_dblEdge_true (A : Finset ι → Finset (Pt V)) (π : κ → ι)
    (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ)
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G)
    (hm : dblEdge g₀ true h ∈ dblG G g₀ d') :
    AgDbl (V := V) A π G g₀ d' hinj (dblEdge g₀ true h)
      = liftSet (V := V) (dblπ π g₀) (dblEdge g₀ true h)
          (dblπ_injOn_dblEdge π g₀ true (hinj h hh)) (A (h.image π)) := by
  rw [AgDbl_of_mem (V := V) A π G g₀ d' hinj hm,
    show dblInjOn G g₀ d' π hinj (dblEdge g₀ true h) hm
        = dblπ_injOn_dblEdge π g₀ true (hinj h hh) from Subsingleton.elim _ _,
    dblEdge_image]

theorem dblEdge_false_mem_dblG {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ}
    {h : Finset κ} (hh : h ∈ Glt G g₀) : dblEdge g₀ false h ∈ dblG G g₀ d' := by
  rw [mem_dblG]
  exact ⟨h, (mem_Glt.mp hh).1, Or.inl ⟨(mem_Glt.mp hh).2, rfl⟩⟩

theorem dblEdge_mem_dblG_gt {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ}
    {h : Finset κ} (hh : h ∈ Ggt G g₀ d') (i : Bool) : dblEdge g₀ i h ∈ dblG G g₀ d' := by
  rw [mem_dblG]
  refine ⟨h, (mem_Ggt.mp hh).1, Or.inr ⟨(mem_Ggt.mp hh).2.1, (mem_Ggt.mp hh).2.2, ?_⟩⟩
  cases i
  · exact Or.inl rfl
  · exact Or.inr rfl


/-! ## The product over the doubled hypergraph -/

theorem dblEdge_dblEmb_mem (g₀ : Finset κ) (i : Bool) (h : Finset κ) (k : κ) :
    dblEmb g₀ i k ∈ dblEdge g₀ i h ↔ k ∈ h := by
  rw [mem_dblEdge]
  exact ⟨fun ⟨k', hk', hkk⟩ => by rw [dblEmb_injective g₀ i hkk] at hk'; exact hk',
    fun hk => ⟨k, hk, rfl⟩⟩

theorem dblEdge_eq_of_eq' (g₀ : Finset κ) (i : Bool) {h h' : Finset κ}
    (heq : dblEdge g₀ i h = dblEdge g₀ i h') : h = h' := by
  ext k
  rw [← dblEdge_dblEmb_mem g₀ i h k, ← dblEdge_dblEmb_mem g₀ i h' k, heq]

/-- A `true` copy of an edge not contained in `g₀` differs from any `false` copy. -/
theorem dblEdge_true_ne_false (g₀ : Finset κ) {h h' : Finset κ} (hh : ¬ h' ⊆ g₀) :
    dblEdge g₀ true h' ≠ dblEdge g₀ false h := by
  intro heq
  obtain ⟨k, hk, hkg⟩ : ∃ k ∈ h', k ∉ g₀ := by
    by_contra hc
    push_neg at hc
    exact hh fun x hx => hc x hx
  have h1 : Sum.inl (⟨k, hkg⟩, true) ∈ dblEdge g₀ true h' :=
    (mem_dblEdge_inl g₀ true h' ⟨k, hkg⟩ true).mpr ⟨hk, rfl⟩
  have h2 : Sum.inl (⟨k, hkg⟩, true) ∉ dblEdge g₀ false h := by
    rw [mem_dblEdge_inl]
    rintro ⟨-, hj⟩
    exact Bool.noConfusion hj
  rw [heq] at h1
  exact h2 h1

theorem gt_not_subset {G : Finset (Finset κ)} {g₀ : Finset κ} {d' : ℕ} (hg₀ : g₀.card = d')
    (hd' : 1 ≤ d') {h : Finset κ} (hh : h ∈ Ggt G g₀ d') : ¬ h ⊆ g₀ := by
  intro hc
  have hc' : h.card ≤ d' - 1 := (mem_Ggt.mp hh).2.2
  refine (mem_Ggt.mp hh).2.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hc, ?_⟩)
  intro heq
  rw [heq, hg₀] at hc'
  omega

theorem disjoint_dblG_ff (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) :
    Disjoint ((Glt G g₀).image (dblEdge g₀ false))
      ((Ggt G g₀ d').image (dblEdge g₀ false)) := by
  rw [Finset.disjoint_left]
  intro gg hg₁ hg₂
  rw [Finset.mem_image] at hg₁ hg₂
  obtain ⟨h₁, hh₁, he₁⟩ := hg₁
  obtain ⟨h₂, hh₂, he₂⟩ := hg₂
  have hinj : h₁ = h₂ := dblEdge_eq_of_eq' g₀ false (he₁.trans he₂.symm)
  rw [hinj] at hh₁
  exact (mem_Ggt.mp hh₂).2.1 (mem_Glt.mp hh₁).2

theorem disjoint_dblG_ft (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d')
    (hd' : 1 ≤ d') :
    Disjoint ((Glt G g₀).image (dblEdge g₀ false))
      ((Ggt G g₀ d').image (dblEdge g₀ true)) := by
  rw [Finset.disjoint_left]
  intro gg hg₁ hg₂
  rw [Finset.mem_image] at hg₁ hg₂
  obtain ⟨h₁, hh₁, he₁⟩ := hg₁
  obtain ⟨h₂, hh₂, he₂⟩ := hg₂
  exact dblEdge_true_ne_false g₀ (h := h₁) (gt_not_subset hg₀ hd' hh₂) (he₂.trans he₁.symm)

theorem disjoint_dblG_tt (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d')
    (hd' : 1 ≤ d') :
    Disjoint ((Ggt G g₀ d').image (dblEdge g₀ false))
      ((Ggt G g₀ d').image (dblEdge g₀ true)) := by
  rw [Finset.disjoint_left]
  intro gg hg₁ hg₂
  rw [Finset.mem_image] at hg₁ hg₂
  obtain ⟨h₁, hh₁, he₁⟩ := hg₁
  obtain ⟨h₂, hh₂, he₂⟩ := hg₂
  exact dblEdge_true_ne_false g₀ (h := h₁) (gt_not_subset hg₀ hd' hh₂) (he₂.trans he₁.symm)

theorem prod_dblG (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d')
    (hd' : 1 ≤ d') (F : Finset (DblIdx g₀) → ℝ) :
    (∏ gg ∈ dblG G g₀ d', F gg)
      = (∏ h ∈ Glt G g₀, F (dblEdge g₀ false h))
        * ∏ h ∈ Ggt G g₀ d', (F (dblEdge g₀ false h) * F (dblEdge g₀ true h)) := by
  have hAB : Disjoint ((Glt G g₀).image (dblEdge g₀ false))
      ((Ggt G g₀ d').image (dblEdge g₀ false)) := disjoint_dblG_ff G g₀ d'
  have hAC : Disjoint (((Glt G g₀).image (dblEdge g₀ false))
      ∪ ((Ggt G g₀ d').image (dblEdge g₀ false)))
      ((Ggt G g₀ d').image (dblEdge g₀ true)) := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact Finset.disjoint_left.mp (disjoint_dblG_ft G g₀ d' hg₀ hd') hx hxc
    · exact Finset.disjoint_left.mp (disjoint_dblG_tt G g₀ d' hg₀ hd') hx hxc
  have e1 : Set.InjOn (dblEdge g₀ false) (Glt G g₀) :=
    fun _ _ _ _ hxy => dblEdge_eq_of_eq' g₀ false hxy
  have e2 : Set.InjOn (dblEdge g₀ false) (Ggt G g₀ d') :=
    fun _ _ _ _ hxy => dblEdge_eq_of_eq' g₀ false hxy
  have e3 : Set.InjOn (dblEdge g₀ true) (Ggt G g₀ d') :=
    fun _ _ _ _ hxy => dblEdge_eq_of_eq' g₀ true hxy
  rw [dblG]
  rw [Finset.prod_union (s₁ := (Glt G g₀).image (dblEdge g₀ false)
      ∪ (Ggt G g₀ d').image (dblEdge g₀ false))
      (s₂ := (Ggt G g₀ d').image (dblEdge g₀ true)) (f := F) hAC]
  rw [Finset.prod_union (s₁ := (Glt G g₀).image (dblEdge g₀ false))
      (s₂ := (Ggt G g₀ d').image (dblEdge g₀ false)) (f := F) hAB]
  rw [Finset.prod_image (s := Glt G g₀) (g := dblEdge g₀ false) (f := F) e1,
    Finset.prod_image (s := Ggt G g₀ d') (g := dblEdge g₀ false) (f := F) e2,
    Finset.prod_image (s := Ggt G g₀ d') (g := dblEdge g₀ true) (f := F) e3,
    Finset.prod_mul_distrib (s := Ggt G g₀ d') (f := fun h => F (dblEdge g₀ false h))
      (g := fun h => F (dblEdge g₀ true h))]
  ring


/-! ## The doubling identity -/

/-- The value of a lifted set at `combine π g₀ w u` does not depend on `u` when the edge is
contained in `g₀`. -/
theorem mem_AgOf_combine_iff (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h g₀ : Finset κ} (hh : h ∈ G)
    (hsub : h ⊆ g₀) (v : BPt V π) (u : W2 (V := V) π g₀) :
    combine (V := V) π g₀ (restrict (V := fun k => V (π k)) v g₀) u ∈ AgOf (V := V) A π G hinj h
      ↔ v ∈ AgOf (V := V) A π G hinj h := by
  rw [AgOf_of_mem (V := V) A π G hinj hh, mem_liftSet_iff, mem_liftSet_iff]
  refine exists_congr (fun x => and_congr_right (fun _ => ?_))
  constructor
  · intro h1 k hk
    have h2 := h1 k hk
    rwa [combine_apply_mem (V := V) π g₀ _ u (hsub hk)] at h2
  · intro h1 k hk
    have h2 := h1 k hk
    rw [combine_apply_mem (V := V) π g₀ _ u (hsub hk)]
    exact h2

theorem mem_AgOf_combine_congr (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G)
    {g₀ : Finset κ} (hsub : h ⊆ g₀) (w : W1 (V := V) π g₀) (u u' : W2 (V := V) π g₀) :
    combine (V := V) π g₀ w u ∈ AgOf (V := V) A π G hinj h
      ↔ combine (V := V) π g₀ w u' ∈ AgOf (V := V) A π G hinj h := by
  rw [AgOf_of_mem (V := V) A π G hinj hh, mem_liftSet_iff, mem_liftSet_iff]
  refine exists_congr (fun x => and_congr_right (fun _ => ?_))
  constructor
  · intro h1 k hk
    have h2 := h1 k hk
    rw [combine_apply_mem (V := V) π g₀ w u (hsub hk)] at h2
    rw [combine_apply_mem (V := V) π g₀ w u' (hsub hk)]
    exact h2
  · intro h1 k hk
    have h2 := h1 k hk
    rw [combine_apply_mem (V := V) π g₀ w u' (hsub hk)] at h2
    rw [combine_apply_mem (V := V) π g₀ w u (hsub hk)]
    exact h2

theorem indicator_congr {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {S' : Finset β} {x : α} {y : β} (h : x ∈ S ↔ y ∈ S') :
    SigAlg.indicator S x = SigAlg.indicator S' y := by
  by_cases hx : x ∈ S
  · rw [show SigAlg.indicator S x = (1 : ℝ) from by simp [SigAlg.indicator, hx],
      show SigAlg.indicator S' y = (1 : ℝ) from by simp [SigAlg.indicator, (h.mp hx)]]
  · rw [show SigAlg.indicator S x = (0 : ℝ) from by simp [SigAlg.indicator, hx],
      show SigAlg.indicator S' y = (0 : ℝ) from by
        simp only [SigAlg.indicator, if_neg (fun hy => hx (h.mpr hy))]]

/-- The `Glt` factor of the doubling identity. -/
noncomputable def Xw (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (w : W1 (V := V) π g₀) : ℝ :=
  ∏ h ∈ Glt G g₀, indicator (AgOf (V := V) A π G hinj h)
    (combine (V := V) π g₀ w (Classical.arbitrary (W2 (V := V) π g₀)))

/-- The `Ggt` factor of the doubling identity. -/
noncomputable def Pw (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (w : W1 (V := V) π g₀) (u : W2 (V := V) π g₀) : ℝ :=
  ∏ h ∈ Ggt G g₀ d', indicator (AgOf (V := V) A π G hinj h) (combine (V := V) π g₀ w u)

theorem Xw_of_restrict (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (v : BPt V π) :
    Xw (V := V) A π G g₀ hinj (restrict (V := fun k => V (π k)) v g₀)
      = ∏ h ∈ Glt G g₀, indicator (AgOf (V := V) A π G hinj h) v := by
  refine Finset.prod_congr rfl (fun h hh => ?_)
  exact indicator_congr (mem_AgOf_combine_iff (V := V) A π G hinj (mem_Glt.mp hh).1
    (mem_Glt.mp hh).2.1 v (Classical.arbitrary (W2 (V := V) π g₀)))


theorem indicator_AgDbl_dblEdge_false (A : Finset ι → Finset (Pt V)) (π : κ → ι)
    (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ)
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G)
    (hm : dblEdge g₀ false h ∈ dblG G g₀ d')
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) :
    indicator (AgDbl (V := V) A π G g₀ d' hinj (dblEdge g₀ false h))
        ((dblEquiv (V := V) π g₀).symm p)
      = indicator (AgOf (V := V) A π G hinj h) (combine (V := V) π g₀ p.2 p.1.1) :=
  indicator_congr (by
    rw [AgDbl_dblEdge_false (V := V) A π G g₀ d' hinj hh hm, AgOf_of_mem (V := V) A π G hinj hh]
    exact mem_liftSet_dblEdge_false π g₀ A h (hinj h hh) p)

theorem indicator_AgDbl_dblEdge_true (A : Finset ι → Finset (Pt V)) (π : κ → ι)
    (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ)
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) {h : Finset κ} (hh : h ∈ G)
    (hm : dblEdge g₀ true h ∈ dblG G g₀ d')
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) :
    indicator (AgDbl (V := V) A π G g₀ d' hinj (dblEdge g₀ true h))
        ((dblEquiv (V := V) π g₀).symm p)
      = indicator (AgOf (V := V) A π G hinj h) (combine (V := V) π g₀ p.2 p.1.2) :=
  indicator_congr (by
    rw [AgDbl_dblEdge_true (V := V) A π G g₀ d' hinj hh hm, AgOf_of_mem (V := V) A π G hinj hh]
    exact mem_liftSet_dblEdge_true π g₀ A h (hinj h hh) p)

/-- The product over the doubled hypergraph, evaluated at a split point. -/
theorem prod_dblG_split (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d') (hd' : 1 ≤ d')
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀) :
    (∏ gg ∈ dblG G g₀ d', indicator (AgDbl (V := V) A π G g₀ d' hinj gg)
        ((dblEquiv (V := V) π g₀).symm p))
      = Xw (V := V) A π G g₀ hinj p.2
        * (Pw (V := V) A π G g₀ d' hinj p.2 p.1.1
            * Pw (V := V) A π G g₀ d' hinj p.2 p.1.2) := by
  rw [prod_dblG G g₀ d' hg₀ hd']
  congr 1
  · refine Finset.prod_congr rfl (fun h hh => ?_)
    rw [indicator_AgDbl_dblEdge_false (V := V) A π G g₀ d' hinj (mem_Glt.mp hh).1
      (dblEdge_false_mem_dblG hh)]
    exact indicator_congr (mem_AgOf_combine_congr (V := V) A π G hinj (mem_Glt.mp hh).1
      (mem_Glt.mp hh).2.1 p.2 p.1.1 (Classical.arbitrary (W2 (V := V) π g₀)))
  · rw [Pw, Pw, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun h hh => ?_)
    rw [indicator_AgDbl_dblEdge_false (V := V) A π G g₀ d' hinj (mem_Ggt.mp hh).1
        (dblEdge_mem_dblG_gt hh false),
      indicator_AgDbl_dblEdge_true (V := V) A π G g₀ d' hinj (mem_Ggt.mp hh).1
        (dblEdge_mem_dblG_gt hh true)]


/-- The doubling identity, evaluated at a split point. -/
theorem avg_dblG_split (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d') (hd' : 1 ≤ d')
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) :
    avg (fun vv : BPt V (dblπ π g₀) =>
        ∏ gg ∈ dblG G g₀ d', indicator (AgDbl (V := V) A π G g₀ d' hinj gg) vv)
      = avg (fun p : (W2 (V := V) π g₀ × W2 (V := V) π g₀) × W1 (V := V) π g₀ =>
          Xw (V := V) A π G g₀ hinj p.2
            * (Pw (V := V) A π G g₀ d' hinj p.2 p.1.1
                * Pw (V := V) A π G g₀ d' hinj p.2 p.1.2)) :=
  (avg_equiv' (dblEquiv (V := V) π g₀).symm (fun vv : BPt V (dblπ π g₀) =>
      ∏ gg ∈ dblG G g₀ d', indicator (AgDbl (V := V) A π G g₀ d' hinj gg) vv)).symm.trans
    (by
      congr 1
      funext p
      exact prod_dblG_split A π G g₀ d' hg₀ hd' hinj p)


/-- **The doubling identity**: the counting expression on the doubled bundle is the square of
the second factor, averaged, times the first factor. -/
theorem avg_dblG_eq (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d') (hd' : 1 ≤ d')
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) :
    avg (fun vv : BPt V (dblπ π g₀) =>
        ∏ gg ∈ dblG G g₀ d', indicator (AgDbl (V := V) A π G g₀ d' hinj gg) vv)
      = avg (fun w : W1 (V := V) π g₀ =>
          Xw (V := V) A π G g₀ hinj w
            * (avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hinj w u)) ^ 2) := by
  rw [avg_dblG_split A π G g₀ d' hg₀ hd' hinj]
  rw [avg3 (α := W2 (V := V) π g₀) (β := W2 (V := V) π g₀) (γ := W1 (V := V) π g₀)
      (f := fun u₀ u₁ w => Xw (V := V) A π G g₀ hinj w
        * (Pw (V := V) A π G g₀ d' hinj w u₀ * Pw (V := V) A π G g₀ d' hinj w u₁))]
  congr 1
  funext w
  exact avg_avg_const_mul_sq (X := Xw (V := V) A π G g₀ hinj w)
    (g := fun u => Pw (V := V) A π G g₀ d' hinj w u)


/-- **The doubling identity**, in the form used by the Cauchy–Schwarz step, with the first
factor written as a function of the ambient point. -/
theorem avg_dblG_eq' (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    (g₀ : Finset κ) (d' : ℕ) (hg₀ : g₀.card = d') (hd' : 1 ≤ d')
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) :
    avg (fun vv : BPt V (dblπ π g₀) =>
        ∏ gg ∈ dblG G g₀ d', indicator (AgDbl (V := V) A π G g₀ d' hinj gg) vv)
      = avg (fun v : BPt V π =>
          Xw (V := V) A π G g₀ hinj (restrict (V := fun k => V (π k)) v g₀)
            * (avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hinj (restrict (V := fun k => V (π k)) v g₀) u)) ^ 2) := by
  rw [avg_dblG_eq A π G g₀ d' hg₀ hd' hinj]
  exact (avg_restrict_eq (V := fun k => V (π k)) g₀
    (fun w => Xw (V := V) A π G g₀ hinj w
      * (avg (fun u : W2 (V := V) π g₀ => Pw (V := V) A π G g₀ d' hinj w u)) ^ 2)).symm

end Szemeredi.Removal
