import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod

namespace Commons.Topology.Simplex

open Finset

/-! ## Auxiliary combinatorial lemmas -/

/-- If the fibres of a colouring `f` of a finite set `s` have one element more than there are
colours (`s.card = (s.image f).card + 1`, i.e. exactly one colour is repeated, twice), then the
number of vertices whose colour occurs at least twice is exactly `2`. -/
lemma sperner_card_filter_two_le_fiber_eq_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (hcard : s.card = (s.image f).card + 1) :
    (s.filter (fun a => 2 ≤ (s.filter (fun b => f b = f a)).card)).card = 2 := by
  classical
  set T := s.image f with hT
  set m : β → ℕ := fun c => (s.filter (fun b => f b = c)).card with hm
  have hm1 : ∀ c ∈ T, 1 ≤ m c := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    have : a ∈ s.filter (fun b => f b = f a) := by simp [ha]
    exact Finset.card_pos.mpr ⟨a, this⟩
  have hsum : ∑ c ∈ T, m c = s.card := (Finset.card_eq_sum_card_image f s).symm
  have hsum_sub : ∑ c ∈ T, (m c - 1) = 1 := by
    have h1 : ∑ c ∈ T, m c = (∑ c ∈ T, (m c - 1)) + T.card := by
      conv_rhs => rw [Finset.card_eq_sum_ones T, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      exact (Nat.sub_add_cancel (hm1 c hc)).symm
    omega
  set A := T.filter (fun c => 2 ≤ m c) with hA
  have hsubKey : ∑ c ∈ A, (m c - 1) = ∑ c ∈ T, (m c - 1) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro c hcT hcA
    have h2 : ¬ (2 ≤ m c) := fun h => hcA (Finset.mem_filter.mpr ⟨hcT, h⟩)
    have h3 : 1 ≤ m c := hm1 c hcT
    omega
  have hA1 : ∑ c ∈ A, (m c - 1) = 1 := hsubKey.trans hsum_sub
  have hAle : A.card ≤ 1 := by
    have h := Finset.card_nsmul_le_sum A (fun c => m c - 1) 1 (fun c hc => by
      have : 2 ≤ m c := (Finset.mem_filter.mp hc).2
      omega)
    have h' : A.card ≤ ∑ c ∈ A, (m c - 1) := by
      simpa only [nsmul_one, Nat.cast_id] using h
    omega
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hA1
    simp at hA1
  have hAcard : A.card = 1 := by
    have := Finset.card_pos.mpr hAne
    omega
  obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp hAcard
  have hmc0 : m c0 = 2 := by
    have : ∑ c ∈ A, (m c - 1) = m c0 - 1 := by simp [hc0]
    omega
  have hfilter : s.filter (fun a => 2 ≤ m (f a)) = s.filter (fun a => f a ∈ A) := by
    apply Finset.filter_congr
    intro a ha
    rw [hA, Finset.mem_filter]
    constructor
    · intro h; exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, h⟩
    · intro h; exact h.2
  rw [hfilter]
  have hfib : (s.filter (fun a => f a ∈ A)).card = ∑ c ∈ A, m c := by
    rw [Finset.card_eq_sum_card_fiberwise (t := A) (f := f) (s := s.filter (fun a => f a ∈ A)) (by
      intro a ha
      exact (Finset.mem_filter.mp ha).2)]
    apply Finset.sum_congr rfl
    intro c hc
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, hfa⟩; exact ⟨ha, hfa⟩
    · rintro ⟨ha, hfa⟩; exact ⟨⟨ha, hfa ▸ hc⟩, hfa⟩
  rw [hfib]
  simp [hc0, hmc0]

/-- If `C.image col = univ` and `C.card = n` (so `col` is injective on `C`), then exactly one
vertex of `C` has colour `t`. -/
lemma sperner_card_filter_col_eq_one_of_image_eq_univ {V : Type*} [Fintype V] {n : ℕ}
    (col : V → Fin n) (t : Fin n) {C : Finset V} (hcard : C.card = n)
    (hU : C.image col = Finset.univ) :
    (C.filter (fun v => col v = t)).card = 1 := by
  classical
  have hinj : Set.InjOn col ↑C := by
    rw [← Finset.card_image_iff, hU, Finset.card_univ, Fintype.card_fin]
    exact hcard.symm
  obtain ⟨v0, hv0C, hv0t⟩ := Finset.mem_image.mp (by rw [hU]; exact Finset.mem_univ t)
  rw [Finset.card_eq_one]
  refine ⟨v0, ?_⟩
  ext v
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hvC, hvt⟩
    exact hinj hvC hv0C (hvt.trans hv0t.symm)
  · rintro rfl
    exact ⟨hv0C, hv0t⟩

/-- The image of `C.erase v` equals `univ \ {t}` iff it contains `univ \ {t}`. -/
lemma sperner_erase_image_eq_erase_univ_iff {V : Type*} [DecidableEq V] {d : ℕ}
    (col : V → Fin (d + 1)) (t : Fin (d + 1))
    {C : Finset V} (hC : C.card = d + 1) {v : V} (hv : v ∈ C) :
    (C.erase v).image col = Finset.univ.erase t ↔
      (Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ (C.erase v).image col := by
  constructor
  · intro h; rw [h]
  · intro h
    have hcard : (C.erase v).card = d := by
      rw [Finset.card_erase_of_mem hv, hC]; omega
    have hle : ((C.erase v).image col).card ≤ d := by
      calc ((C.erase v).image col).card ≤ (C.erase v).card := Finset.card_image_le
        _ = d := hcard
    have h3 : ((C.erase v).image col).card ≤
        (Finset.univ.erase t : Finset (Fin (d + 1))).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
      exact hle
    exact (Finset.eq_of_subset_of_card_le h h3).symm

/-- A vertex `v ∈ C` loses no colour other than possibly `t` when removed iff all colours other
than `t` occur in `C` and either `v` is the unique vertex of colour `t` or its colour is
repeated. -/
lemma sperner_erase_univ_subset_iff {V : Type*} [DecidableEq V] {d : ℕ}
    (col : V → Fin (d + 1)) (t : Fin (d + 1)) {C : Finset V} {v : V} (hv : v ∈ C) :
    (Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ (C.erase v).image col ↔
      (Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ C.image col ∧
        (col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card) := by
  classical
  constructor
  · intro h
    constructor
    · exact h.trans (Finset.image_subset_image (Finset.erase_subset v C))
    · by_cases hvt : col v = t
      · exact Or.inl hvt
      · refine Or.inr ?_
        have hmem : col v ∈ (Finset.univ.erase t : Finset (Fin (d + 1))) := by
          rw [Finset.mem_erase]
          exact ⟨hvt, Finset.mem_univ _⟩
        obtain ⟨w, hw, hwcol⟩ := Finset.mem_image.mp (h hmem)
        obtain ⟨hwv, hwC⟩ := Finset.mem_erase.mp hw
        have hsub : ({v, w} : Finset V) ⊆ C.filter (fun w => col w = col v) := by
          intro x hx
          rw [Finset.mem_filter]
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact ⟨hv, rfl⟩
          · rw [Finset.mem_singleton] at hx'
            exact ⟨hx' ▸ hwC, hx' ▸ hwcol⟩
        have hc := Finset.card_le_card hsub
        rwa [Finset.card_pair hwv.symm] at hc
  · rintro ⟨h1, h2⟩ c hc
    have hct : c ≠ t := (Finset.mem_erase.mp hc).1
    obtain ⟨w, hwC, hwcol⟩ := Finset.mem_image.mp (h1 hc)
    by_cases hwv : w = v
    · rw [hwv] at hwcol
      have hcvt : col v ≠ t := fun h' => hct (hwcol ▸ h')
      rcases h2 with h | h
      · exact absurd h hcvt
      · obtain ⟨u, hu, u', hu', huu'⟩ := Finset.one_lt_card.mp (by omega :
           1 < (C.filter (fun w => col w = col v)).card)
        have hex : ∃ x ∈ C.filter (fun w => col w = col v), x ≠ v := by
          by_cases hun : u = v
          · exact ⟨u', hu', fun hh => huu' (hun.trans hh.symm)⟩
          · exact ⟨u, hu, hun⟩
        obtain ⟨x, hx, hxv⟩ := hex
        rw [Finset.mem_filter] at hx
        exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxv, hx.1⟩, hx.2.trans hwcol⟩
    · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, hwC⟩, hwcol⟩

/-- Per-cell parity: the number of facets of a `(d+1)`-cell whose colours are all colours but `t`
is odd exactly when the cell is complete. -/
lemma sperner_percell {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (col : V → Fin (d + 1)) (t : Fin (d + 1)) (C : Finset V) (hC : C.card = d + 1) :
    ((C.filter (fun v => (C.erase v).image col = Finset.univ.erase t)).card : ZMod 2)
      = if C.image col = Finset.univ then 1 else 0 := by
  classical
  have hfil : C.filter (fun v => (C.erase v).image col = Finset.univ.erase t)
      = C.filter (fun v => ((Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ C.image col) ∧
          (col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card)) := by
    apply Finset.filter_congr
    intro v hv
    rw [sperner_erase_image_eq_erase_univ_iff col t hC hv, sperner_erase_univ_subset_iff col t hv]
  rw [hfil]
  by_cases hsub : (Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ C.image col
  · have hfil2 : C.filter (fun v => ((Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ C.image col) ∧
        (col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card))
        = C.filter (fun v => col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card) := by
      apply Finset.filter_congr
      intro v hv
      exact ⟨fun h => h.2, fun h => ⟨hsub, h⟩⟩
    rw [hfil2]
    by_cases hU : C.image col = Finset.univ
    · rw [if_pos hU]
      have hfil3 : C.filter (fun v => col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card)
          = C.filter (fun v => col v = t) := by
        apply Finset.filter_congr
        intro v hv
        have hinj : Set.InjOn col ↑C := by
          rw [← Finset.card_image_iff, hU, Finset.card_univ, Fintype.card_fin]
          exact hC.symm
        have hm1 : (C.filter (fun w => col w = col v)).card = 1 := by
          have hone : C.filter (fun w => col w = col v) = {v} := by
            ext w
            rw [Finset.mem_filter, Finset.mem_singleton]
            exact ⟨fun h => hinj h.1 hv h.2, fun h => ⟨h ▸ hv, h ▸ rfl⟩⟩
          rw [hone, Finset.card_singleton]
        rw [hm1]
        constructor
        · rintro (h | h)
          · exact h
          · omega
        · exact Or.inl
      rw [hfil3, sperner_card_filter_col_eq_one_of_image_eq_univ col t hC hU]
      simp
    · rw [if_neg hU]
      have himg : C.image col = Finset.univ.erase t := by
        have hsubU : C.image col ⊆ (Finset.univ : Finset (Fin (d + 1))) :=
          fun x _ => Finset.mem_univ x
        have h1 : (C.image col).card ≤ d + 1 := by
          calc (C.image col).card ≤ (Finset.univ : Finset (Fin (d + 1))).card :=
                Finset.card_le_card hsubU
            _ = d + 1 := by rw [Finset.card_univ, Fintype.card_fin]
        have h2 : (C.image col).card ≠ d + 1 := by
          intro h
          exact hU (Finset.eq_of_subset_of_card_le hsubU
            (by rw [h, Finset.card_univ, Fintype.card_fin]))
        have h3 : ((C.image col)).card ≤ (Finset.univ.erase t : Finset (Fin (d + 1))).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
          omega
        exact (Finset.eq_of_subset_of_card_le hsub h3).symm
      have hfil3 : C.filter (fun v => col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card)
          = C.filter (fun v => 2 ≤ (C.filter (fun w => col w = col v)).card) := by
        apply Finset.filter_congr
        intro v hv
        have hvt : col v ≠ t := by
          intro h
          have : t ∈ C.image col := Finset.mem_image.mpr ⟨v, hv, h⟩
          rw [himg] at this
          exact Finset.notMem_erase t Finset.univ this
        constructor
        · rintro (h | h)
          · exact absurd h hvt
          · exact h
        · exact Or.inr
      rw [hfil3]
      have hcard' : C.card = (C.image col).card + 1 := by
        rw [himg, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
        omega
      rw [sperner_card_filter_two_le_fiber_eq_two C col hcard']
      decide
  · rw [if_neg (fun h => hsub (by rw [h]; exact Finset.erase_subset t Finset.univ))]
    have hempty : C.filter (fun v => ((Finset.univ.erase t : Finset (Fin (d + 1))) ⊆ C.image col) ∧
        (col v = t ∨ 2 ≤ (C.filter (fun w => col w = col v)).card)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv
      exact fun h => hsub h.1
    rw [hempty]
    simp

/-! ## The two countings -/

/-- Counting the pairs `(C, v)` by cells: this is congruent mod 2 to the number of complete
cells. -/
lemma sperner_sigma_card_mod_two_left {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (col : V → Fin (d + 1)) (t : Fin (d + 1)) (Cells : Finset (Finset V))
    (hcard : ∀ C ∈ Cells, C.card = d + 1) :
    ((Cells.sigma (fun C => C.filter (fun v => (C.erase v).image col = Finset.univ.erase t))).card
        : ZMod 2)
      = ((Cells.filter (fun C => C.image col = Finset.univ)).card : ZMod 2) := by
  classical
  rw [Finset.card_sigma, Nat.cast_sum]
  trans ∑ C ∈ Cells,
      (if C.image col = Finset.univ then (1 : ZMod 2) else 0)
  · apply Finset.sum_congr rfl
    intro C hC
    exact sperner_percell col t C (hcard C hC)
  · rw [Finset.sum_boole]

/-- Counting the pairs `(C, v)` by facets: this is congruent mod 2 to the number of boundary
`t`-doors. -/
lemma sperner_sigma_card_mod_two_right {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (col : V → Fin (d + 1)) (t : Fin (d + 1)) (Cells : Finset (Finset V))
    (hinc : ∀ f : Finset V, f.card = d → (∃ C ∈ Cells, f ⊆ C) →
        (Cells.filter (fun C => f ⊆ C)).card = 1 ∨ (Cells.filter (fun C => f ⊆ C)).card = 2) :
    (((((Cells.biUnion id).powersetCard d).filter (fun f =>
        f.image col = Finset.univ.erase t)).sigma
        (fun f => Cells.filter (fun C => f ⊆ C))).card : ZMod 2)
      = ((((Cells.biUnion id).powersetCard d).filter (fun f =>
          f.image col = Finset.univ.erase t ∧
            (Cells.filter (fun C => f ⊆ C)).card = 1)).card : ZMod 2) := by
  classical
  rw [Finset.card_sigma, Nat.cast_sum, Finset.sum_filter]
  trans ∑ f ∈ ((Cells.biUnion id).powersetCard d),
      (if f.image col = Finset.univ.erase t ∧
        (Cells.filter (fun C => f ⊆ C)).card = 1 then (1 : ZMod 2) else 0)
  · apply Finset.sum_congr rfl
    intro f hf
    by_cases hcond : f.image col = Finset.univ.erase t
    · rw [if_pos hcond]
      rcases Nat.eq_zero_or_pos (Cells.filter (fun C => f ⊆ C)).card with hk | hk
      · rw [if_neg (by rintro ⟨-, h⟩; omega), hk]; simp
      · have hfcard : f.card = d :=
          (Finset.mem_powersetCard.mp hf).2
        have hex : ∃ C ∈ Cells, f ⊆ C := by
          obtain ⟨C, hC⟩ := Finset.card_pos.mp hk
          rw [Finset.mem_filter] at hC
          exact ⟨C, hC.1, hC.2⟩
        rcases hinc f hfcard hex with h1 | h2
        · rw [if_pos ⟨hcond, h1⟩, h1]; simp
        · rw [if_neg (by rintro ⟨-, h⟩; omega), h2]; decide
    · rw [if_neg hcond]
      have hne : ¬ (f.image col = Finset.univ.erase t ∧
          (Cells.filter (fun C => f ⊆ C)).card = 1) := by
        rintro ⟨h, -⟩; exact hcond h
      rw [if_neg hne]
  · rw [Finset.sum_boole]

/-- Counting the pairs `(C, v)` with `(C.erase v)` a facet of colour type `t` in two ways. -/
lemma sperner_sigma_card_eq {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (col : V → Fin (d + 1)) (t : Fin (d + 1)) (Cells : Finset (Finset V))
    (hcard : ∀ C ∈ Cells, C.card = d + 1) :
    (Cells.sigma (fun C => C.filter (fun v => (C.erase v).image col = Finset.univ.erase t))).card
      = ((((Cells.biUnion id).powersetCard d).filter (fun f =>
          f.image col = Finset.univ.erase t)).sigma
          (fun f => Cells.filter (fun C => f ⊆ C))).card := by
  classical
  refine Finset.card_bij (fun a _ => ⟨a.1.erase a.2, a.1⟩) ?_ ?_ ?_
  · rintro ⟨C, v⟩ ha
    obtain ⟨hC, hv⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hvC, hvimg⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, hvimg⟩,
        Finset.mem_filter.mpr ⟨hC, Finset.erase_subset v C⟩⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.erase_subset v C hx⟩
    · rw [Finset.card_erase_of_mem hvC, hcard C hC]; omega
  · rintro ⟨C, v⟩ ha ⟨C', v'⟩ ha' heq
    obtain ⟨hC, hv⟩ := Finset.mem_sigma.mp ha
    have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
    have hCC : C = C' := by simpa using congrArg Sigma.snd heq
    subst hCC
    have herase : C.erase v = C.erase v' := by simpa using congrArg Sigma.fst heq
    have hvv : v = v' := by
      by_contra hne
      have h1 : v ∈ C.erase v' := Finset.mem_erase.mpr ⟨hne, hvC⟩
      rw [← herase] at h1
      exact Finset.notMem_erase v C h1
    subst hvv
    rfl
  · rintro ⟨f, C⟩ hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_sigma.mp hb
    obtain ⟨hfpC, hfimg⟩ := Finset.mem_filter.mp hb1
    obtain ⟨hC, hfC⟩ := Finset.mem_filter.mp hb2
    obtain ⟨_, hfcard⟩ := Finset.mem_powersetCard.mp hfpC
    have hcard1 : (C \ f).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hfC, hcard C hC, hfcard]
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard1
    have hvC : v ∈ C := by
      have : v ∈ C \ f := by rw [hv]; exact Finset.mem_singleton_self v
      exact Finset.sdiff_subset this
    have herase : C.erase v = f := by
      rw [Finset.erase_eq, ← hv, Finset.sdiff_sdiff_eq_self hfC]
    refine ⟨⟨C, v⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨hC, Finset.mem_filter.mpr ⟨hvC, by rw [herase]; exact hfimg⟩⟩
    · show (⟨C.erase v, C⟩ : (_ : Finset V) × Finset V) = ⟨f, C⟩
      rw [herase]

/-! ## The abstract Sperner parity theorem -/

/-- Abstract Sperner parity: for a finite "cell complex" (a Finset `Cells` of
`(d+1)`-element vertex sets) in which every `d`-element facet is contained in
exactly `1` or `2` cells, the number of "complete" cells is congruent mod 2 to
the number of *boundary* `t`-doors (facets with colours = all but `t` and lying
in exactly one cell). -/
theorem sperner_parity_mod2 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (col : V → Fin (d + 1)) (Cells : Finset (Finset V))
    (hcard : ∀ C ∈ Cells, C.card = d + 1)
    (hinc : ∀ f : Finset V, f.card = d → (∃ C ∈ Cells, f ⊆ C) →
        (Cells.filter (fun C => f ⊆ C)).card = 1 ∨ (Cells.filter (fun C => f ⊆ C)).card = 2)
    (t : Fin (d + 1))
    (hB : Odd (((Cells.biUnion id).powersetCard d).filter (fun f =>
        f.image col = Finset.univ.erase t ∧ (Cells.filter (fun C => f ⊆ C)).card = 1)).card) :
    Odd ((Cells.filter (fun C => C.image col = Finset.univ)).card) := by
  have h3 := sperner_sigma_card_eq d col t Cells hcard
  have h1 := sperner_sigma_card_mod_two_left d col t Cells hcard
  have h2 := sperner_sigma_card_mod_two_right d col t Cells hinc
  have hmA : ((Cells.filter (fun C => C.image col = Finset.univ)).card : ZMod 2)
      = ((((Cells.biUnion id).powersetCard d).filter (fun f =>
          f.image col = Finset.univ.erase t ∧
            (Cells.filter (fun C => f ⊆ C)).card = 1)).card : ZMod 2) := by
    rw [← h1, h3, h2]
  exact ZMod.natCast_eq_one_iff_odd.mp (by rw [hmA]; exact ZMod.natCast_eq_one_iff_odd.mpr hB)

end Commons.Topology.Simplex
