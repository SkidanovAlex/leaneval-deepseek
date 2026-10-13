import Mathlib
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Choice.SelDefs

/-!
  WilG1/Choice — `selSet_fibre`: the selection set is the graph of a single point of the fibre.

  Given `K ⊆ ℝ^{p+1}`, `R ⊆ ℝ^p`, `l ∈ R` with nonempty fibre `{t | Fin.snoc l t ∈ K}` that is
  either a point or an open interval with `EReal` endpoints (the dichotomy produced by
  `WilG4a.isCell_fiber` for cells), the set of `s` with `Fin.snoc l s ∈ selSet K R` is a
  singleton `{t}` with `t` in the fibre.

  The proof reduces the four disjuncts of `selSet` — restricted to the fibre over `l` — to the
  abstract rule `selRule P` of `SelDefs.lean` (with `P = inFib K l`), and then decides the four
  possible shapes of the fibre (all of `ℝ`, `(-∞,β)`, `(α,∞)`, `(α,β)`) and the point case.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.Choice

/-- The fibre is a single point `x`: the rule selects exactly `x`. -/
lemma selRule_point {P : ℝ → Prop} {x : ℝ} (h : {s : ℝ | P s} = {x}) :
    P x ∧ {s : ℝ | selRule P s} = {x} := by
  have hP : ∀ y : ℝ, P y ↔ y = x := by
    intro y
    show y ∈ ({s : ℝ | P s} : Set ℝ) ↔ y = x
    rw [h]
    simp
  have hx : P x := (hP x).2 rfl
  have hcentre : ∀ c : ℝ, (∀ u : ℝ, P (c + u) ↔ P (c - u)) ↔ c = x := by
    intro c
    constructor
    · intro hc
      have h1 : P (c + (x - c)) := by
        have hcx : c + (x - c) = x := by ring
        rw [hcx]; exact hx
      have h2 : P (c - (x - c)) := (hc (x - c)).1 h1
      rw [hP] at h2
      linarith
    · intro hcx u
      rw [hcx, hP (x + u), hP (x - u)]
      constructor <;> intro hh <;> linarith
  have hnotall : ¬ (∀ u : ℝ, P u) := by
    intro hall
    have h1 := hall (x + 1)
    rw [hP] at h1
    linarith
  have hnotabove : ¬ (∀ M : ℝ, ∃ u : ℝ, P u ∧ M < u) := by
    intro hab
    obtain ⟨u, hu, hlt⟩ := hab x
    rw [hP] at hu
    linarith
  have hnotbelow : ¬ (∀ M : ℝ, ∃ u : ℝ, P u ∧ u < M) := by
    intro hab
    obtain ⟨u, hu, hlt⟩ := hab x
    rw [hP] at hu
    linarith
  refine ⟨hx, ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hs
    rcases hs with h1 | h2 | h3 | h4
    · exact absurd h1.1 hnotall
    · exact (hcentre s).1 h2.1
    · exact absurd h3.2.2.2 hnotabove
    · exact absurd h4.2.2.2 hnotbelow
  · intro hs
    rw [hs]
    exact Or.inr (Or.inl ⟨(hcentre x).2 rfl, x, (hcentre x).2 rfl,
      fun c' hc' => (hcentre c').1 hc'⟩)

/-- The fibre is all of `ℝ`: the rule selects exactly `0`. -/
lemma selRule_all_aux {P : ℝ → Prop} (h : {s : ℝ | P s} = IooE ⊥ ⊤) :
    P 0 ∧ {s : ℝ | selRule P s} = {0} := by
  have hP : ∀ s : ℝ, P s := by
    intro s
    have hs : s ∈ IooE (⊥ : EReal) ⊤ := ⟨EReal.bot_lt_coe s, EReal.coe_lt_top s⟩
    rwa [← h] at hs
  refine ⟨hP 0, ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hs
    rcases hs with h1 | h2 | h3 | h4
    · exact h1.2
    · exfalso
      obtain ⟨c, hc, huniq⟩ := h2.2
      exact absurd (huniq (c + 1) (fun u => ⟨fun _ => hP _, fun _ => hP _⟩)) (by linarith)
    · exact absurd (hP (s - 1)) h3.2.1
    · exact absurd (hP (s + 1)) h4.2.1
  · intro hs
    rw [hs]
    exact Or.inl ⟨hP, rfl⟩

/-- The fibre is the half-line `(-∞, β)`: the rule selects exactly `β - 1`. -/
lemma selRule_lower_aux {P : ℝ → Prop} {β : ℝ}
    (h : {s : ℝ | P s} = IooE ⊥ (β : EReal)) :
    P (β - 1) ∧ {s : ℝ | selRule P s} = {β - 1} := by
  have hP : ∀ s : ℝ, P s ↔ s < β := by
    intro s
    show s ∈ ({s : ℝ | P s} : Set ℝ) ↔ s < β
    rw [h, IooE_bot_coe]
    exact Set.mem_Iio
  refine ⟨(hP (β - 1)).2 (by linarith), ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hs
    rcases hs with h1 | h2 | h3 | h4
    · have := (hP β).1 (h1.1 β)
      linarith [this]
    · exfalso
      obtain ⟨c, hc, _⟩ := h2.2
      have hu : P (c + (max (β - c) (c - β) + 1)) ↔
          P (c - (max (β - c) (c - β) + 1)) := hc _
      have h1' : ¬ P (c + (max (β - c) (c - β) + 1)) := by
        rw [hP]; linarith [le_max_left (β - c) (c - β)]
      have h2' : P (c - (max (β - c) (c - β) + 1)) := by
        rw [hP]; linarith [le_max_right (β - c) (c - β)]
      exact h1' (hu.2 h2')
    · obtain ⟨u, hu, hlt⟩ := h3.2.2.2 β
      have := (hP u).1 hu
      linarith [this, hlt]
    · have hs1 : s < β := (hP s).1 h4.1
      have hs2 : β ≤ s + 1 := by
        have hh := h4.2.1
        rw [hP] at hh
        linarith
      have hs3 : s + 1 ≤ β := by
        by_contra hlt
        have hlt' : β < s + 1 := not_le.mp hlt
        have hd : 0 < s + 1 - β := by linarith
        have hd1 : s + 1 - β < 1 := by linarith
        have hu : 0 < (s + 1 - β) / 2 := by linarith
        have hu1 : (s + 1 - β) / 2 < 1 := by linarith
        have h5 := h4.2.2.1 ((s + 1 - β) / 2) hu hu1
        rw [hP] at h5
        linarith
      linarith
  · intro hs
    rw [hs]
    refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩))
    · rw [hP]; linarith
    · rw [hP]; linarith
    · intro u hu hu1; rw [hP]; linarith
    · intro M
      exact ⟨min M β - 1, by rw [hP]; linarith [min_le_right M β],
        by linarith [min_le_left M β]⟩

/-- The fibre is the half-line `(α, ∞)`: the rule selects exactly `α + 1`. -/
lemma selRule_upper_aux {P : ℝ → Prop} {α : ℝ}
    (h : {s : ℝ | P s} = IooE (α : EReal) ⊤) :
    P (α + 1) ∧ {s : ℝ | selRule P s} = {α + 1} := by
  have hP : ∀ s : ℝ, P s ↔ α < s := by
    intro s
    show s ∈ ({s : ℝ | P s} : Set ℝ) ↔ α < s
    rw [h, IooE_coe_top]
    exact Set.mem_Ioi
  refine ⟨(hP (α + 1)).2 (by linarith), ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hs
    rcases hs with h1 | h2 | h3 | h4
    · have := (hP α).1 (h1.1 α)
      linarith [this]
    · exfalso
      obtain ⟨c, hc, _⟩ := h2.2
      have hu : P (c + (max (c - α) (α - c) + 1)) ↔
          P (c - (max (c - α) (α - c) + 1)) := hc _
      have h1' : P (c + (max (c - α) (α - c) + 1)) := by
        rw [hP]; linarith [le_max_right (c - α) (α - c)]
      have h2' : ¬ P (c - (max (c - α) (α - c) + 1)) := by
        rw [hP]; linarith [le_max_left (c - α) (α - c)]
      exact h2' (hu.1 h1')
    · have hs1 : α < s := (hP s).1 h3.1
      have hs2 : s ≤ α + 1 := by
        have hh := h3.2.1
        rw [hP] at hh
        linarith
      have hs3 : α + 1 ≤ s := by
        by_contra hlt
        have hlt' : s < α + 1 := not_le.mp hlt
        have hd : 0 < α + 1 - s := by linarith
        have hd1 : α + 1 - s < 1 := by linarith
        have hu : 0 < (α + 1 - s) / 2 := by linarith
        have hu1 : (α + 1 - s) / 2 < 1 := by linarith
        have h5 := h3.2.2.1 ((α + 1 - s) / 2) hu hu1
        rw [hP] at h5
        linarith
      linarith
    · have hs1 : α < s := (hP s).1 h4.1
      have hh := h4.2.1
      rw [hP] at hh
      linarith
  · intro hs
    rw [hs]
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩))
    · rw [hP]; linarith
    · rw [hP]; linarith
    · intro u hu hu1; rw [hP]; linarith
    · intro M
      exact ⟨max M α + 1, by rw [hP]; linarith [le_max_right M α],
        by linarith [le_max_left M α]⟩

/-- The fibre is the bounded open interval `(α, β)`, `α < β`: the rule selects exactly
its centre `(α + β) / 2`. -/
lemma selRule_finite_aux {P : ℝ → Prop} {α β : ℝ} (hab : α < β)
    (h : {s : ℝ | P s} = IooE (α : EReal) (β : EReal)) :
    P ((α + β) / 2) ∧ {s : ℝ | selRule P s} = {(α + β) / 2} := by
  have hP : ∀ s : ℝ, P s ↔ α < s ∧ s < β := by
    intro s
    show s ∈ ({s : ℝ | P s} : Set ℝ) ↔ α < s ∧ s < β
    rw [h, IooE_coe_coe]
    exact Set.mem_Ioo
  set t : ℝ := (α + β) / 2 with ht
  have htP : P t := (hP t).2 ⟨by linarith, by linarith⟩
  have hcentre : ∀ c : ℝ, (∀ u : ℝ, P (c + u) ↔ P (c - u)) ↔ c = t := by
    intro c
    constructor
    · intro hc
      have hR : ∀ r : ℝ, P (2 * c - r) ↔ P r := by
        intro r
        have hh := hc (c - r)
        have e1 : c + (c - r) = 2 * c - r := by ring
        have e2 : c - (c - r) = r := by ring
        rwa [e1, e2] at hh
      have hcle : c ≤ β := by
        by_contra hlt
        have hlt' : β < c := not_le.mp hlt
        have h2 := (hP (2 * c - t)).1 ((hR t).2 htP)
        linarith [h2.2]
      have hcge : α ≤ c := by
        by_contra hlt
        have hlt' : c < α := not_le.mp hlt
        have h2 := (hP (2 * c - t)).1 ((hR t).2 htP)
        linarith [h2.1]
      have hct : c ≤ t := by
        by_contra hlt
        have hlt' : t < c := not_le.mp hlt
        set r : ℝ := (α + (2 * c - β)) / 2 with hr
        have hrP : P r := by
          rw [hP]
          constructor <;> linarith
        have h2 := (hP (2 * c - r)).1 ((hR r).2 hrP)
        linarith [h2.2]
      have htc : t ≤ c := by
        by_contra hlt
        have hlt' : c < t := not_le.mp hlt
        set r : ℝ := ((2 * c - α) + β) / 2 with hr
        have hrP : P r := by
          rw [hP]
          constructor <;> linarith
        have h2 := (hP (2 * c - r)).1 ((hR r).2 hrP)
        linarith [h2.1]
      linarith
    · intro hct u
      rw [hct, hP (t + u), hP (t - u)]
      constructor <;> intro hh <;> exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  refine ⟨htP, ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hs
    rcases hs with h1 | h2 | h3 | h4
    · have hb := (hP β).1 (h1.1 β)
      exact absurd hb.2 (lt_irrefl β)
    · exact (hcentre s).1 h2.1
    · obtain ⟨u, hu, hlt⟩ := h3.2.2.2 β
      have hb := (hP u).1 hu
      linarith [hb.2, hlt]
    · obtain ⟨u, hu, hlt⟩ := h4.2.2.2 α
      have hb := (hP u).1 hu
      linarith [hb.1, hlt]
  · intro hs
    rw [hs]
    exact Or.inr (Or.inl ⟨(hcentre t).2 rfl, t, (hcentre t).2 rfl,
      fun c' hc' => (hcentre c').1 hc'⟩)

/-- **Target lemma.** The fibre of `K` over `l` is a point or an `EReal` interval, so the
selection rule of `selSet` picks a unique point of that fibre. -/
theorem selSet_fibre {p : ℕ} {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    {l : Fin p → ℝ} (hl : l ∈ R) (hne : ∃ t : ℝ, Work.WilG1.inFib K l t)
    (htype : (∃ x : ℝ, {s : ℝ | Work.WilG1.inFib K l s} = {x}) ∨
      (∃ a b : EReal, {s : ℝ | Work.WilG1.inFib K l s} =
        {s : ℝ | a < (s : EReal) ∧ (s : EReal) < b})) :
    ∃ t : ℝ, Work.WilG1.inFib K l t ∧
      {s : ℝ | Fin.snoc l s ∈ Work.WilG1.selSet K R} = {t} := by
  have hset : {s : ℝ | Fin.snoc l s ∈ Work.WilG1.selSet K R} =
      {s : ℝ | selRule (Work.WilG1.inFib K l) s} := by
    ext s
    show (Fin.snoc l s ∈ Work.WilG1.selSet K R) ↔ selRule (Work.WilG1.inFib K l) s
    rw [mem_selSet_snoc_iff]
    exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
  rcases htype with ⟨x, hx⟩ | ⟨a, b, hab⟩
  · obtain ⟨hPx, hEq⟩ := selRule_point hx
    exact ⟨x, hPx, hset.trans hEq⟩
  · obtain ⟨t0, ht0⟩ := hne
    have ht0' : a < (t0 : EReal) ∧ (t0 : EReal) < b := by
      have h1 : t0 ∈ ({s : ℝ | a < (s : EReal) ∧ (s : EReal) < b} : Set ℝ) := by
        rw [← hab]; exact ht0
      exact h1
    rcases a with _ | a
    · rcases b with _ | b
      · exact absurd ht0'.2 (not_lt_of_ge bot_le)
      · rcases b with _ | b
        · obtain ⟨ht, hEq⟩ := selRule_all_aux hab
          exact ⟨0, ht, hset.trans hEq⟩
        · obtain ⟨ht, hEq⟩ := selRule_lower_aux (β := b) hab
          exact ⟨b - 1, ht, hset.trans hEq⟩
    · rcases a with _ | a
      · exact absurd ht0'.1 (not_lt_of_ge le_top)
      · rcases b with _ | b
        · exact absurd ht0'.2 (not_lt_of_ge bot_le)
        · rcases b with _ | b
          · obtain ⟨ht, hEq⟩ := selRule_upper_aux (α := a) hab
            exact ⟨a + 1, ht, hset.trans hEq⟩
          · have hlt : a < b := by
              have h1 : (a : EReal) < (t0 : EReal) := ht0'.1
              have h2 : (t0 : EReal) < (b : EReal) := ht0'.2
              exact EReal.coe_lt_coe_iff.mp (h1.trans h2)
            obtain ⟨ht, hEq⟩ := selRule_finite_aux hlt hab
            exact ⟨(a + b) / 2, ht, hset.trans hEq⟩

end Work.WilG1.Choice
