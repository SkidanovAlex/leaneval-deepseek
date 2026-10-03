import Mathlib
import Submission.Work.Peluse.SwapC.concatState

set_option autoImplicit false

namespace Work.Peluse.SwapC

open CC

variable {s : ℕ}

/-! ## 0. The slot condition -/

/-- The pointwise condition under which the pair of strings `(a, b)` contributes the slot `j` in
`genuineDiffs` (a copy of the conjunction occurring in the body of `genuineDiffs`). -/
private abbrev sCond (j : Fin s) (a b : Fin s → Bool) : Prop :=
  (∀ i : Fin s, i.val < s - 1 - j.val → a i = b i) ∧
    a ⟨s - 1 - j.val, by omega⟩ = true ∧ b ⟨s - 1 - j.val, by omega⟩ = false

/-- At most one `j` is compatible with a pair of strings.  (The pivot `s - 1 - j` is the first
coordinate at which `a` and `b` differ.) -/
private lemma sCond_unique {j j' : Fin s} {a b : Fin s → Bool}
    (h : sCond j a b) (h' : sCond j' a b) : j = j' := by
  have hp : s - 1 - j.val < s := by omega
  have hp' : s - 1 - j'.val < s := by omega
  have hkey : s - 1 - j.val = s - 1 - j'.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : a ⟨s - 1 - j.val, hp⟩ = b ⟨s - 1 - j.val, hp⟩ :=
        h'.1 ⟨s - 1 - j.val, hp⟩ (by omega)
      rw [h.2.1, h.2.2] at h1
      exact Bool.noConfusion h1
    · have h1 : a ⟨s - 1 - j'.val, hp'⟩ = b ⟨s - 1 - j'.val, hp'⟩ :=
        h.1 ⟨s - 1 - j'.val, hp'⟩ (by omega)
      rw [h'.2.1, h'.2.2] at h1
      exact Bool.noConfusion h1
  exact Fin.ext (by omega)

/-- Some leaf of `Λ` has the string `b`. -/
private abbrev strOf (Λ : List (CLeaf s)) (b : Fin s → Bool) : Prop := ∃ m ∈ Λ, m.str = b

/-- The leaf of `Λ` with string `b` is shallow enough for the raw slot `j`. -/
private abbrev slotOf (Λ : List (CLeaf s)) (j : Fin s) (b : Fin s → Bool) : Prop :=
  ∃ m ∈ Λ, m.str = b ∧ m.dep ≤ s - 1 - j.val

/-! ## 1. Membership in the slot lists -/

private lemma mem_raws {l : CLeaf s} {sl : CC s} :
    sl ∈ l.raws ↔ ∃ j : Fin s, l.dep ≤ s - 1 - j.val ∧ sl = CC.raw j l.str := by
  rw [CLeaf.raws]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨j, h, rfl⟩; exact ⟨j, h, rfl⟩
  · rintro ⟨j, h, rfl⟩; exact ⟨j, h, rfl⟩

private lemma mem_diffs {Λ : List (CLeaf s)} {sl : CC s} :
    sl ∈ genuineDiffs Λ ↔
      ∃ j : Fin s, ∃ m₁ ∈ Λ, ∃ m₂ ∈ Λ, sCond j m₁.str m₂.str ∧ sl = CC.dff j m₁.str m₂.str := by
  rw [genuineDiffs, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hsl⟩
    have hp' : p.1 ∈ Λ ∧ p.2 ∈ Λ :=
      List.mem_product.mp (show (p.1, p.2) ∈ Λ ×ˢ Λ from hp)
    rw [List.mem_filterMap] at hsl
    obtain ⟨j, -, hj⟩ := hsl
    by_cases hc : (∀ i : Fin s, i.val < s - 1 - j.val → p.1.str i = p.2.str i) ∧
        p.1.str ⟨s - 1 - j.val, by omega⟩ = true ∧ p.2.str ⟨s - 1 - j.val, by omega⟩ = false
    · rw [if_pos hc] at hj
      have hj' := Option.some.inj hj
      exact ⟨j, p.1, hp'.1, p.2, hp'.2, hc, hj'.symm⟩
    · rw [if_neg hc] at hj
      exact absurd hj (by simp)
  · rintro ⟨j, m₁, hm₁, m₂, hm₂, hc, rfl⟩
    refine ⟨(m₁, m₂), ?_, ?_⟩
    · exact List.mem_product.mpr ⟨hm₁, hm₂⟩
    · rw [List.mem_filterMap]
      exact ⟨j, List.mem_finRange j, if_pos hc⟩

private lemma mem_slots {Λ : List (CLeaf s)} {sl : CC s} :
    sl ∈ genuineSlots Λ ↔
      (∃ m ∈ Λ, ∃ j : Fin s, m.dep ≤ s - 1 - j.val ∧ sl = CC.raw j m.str) ∨
      (∃ j : Fin s, ∃ m₁ ∈ Λ, ∃ m₂ ∈ Λ, sCond j m₁.str m₂.str ∧ sl = CC.dff j m₁.str m₂.str) := by
  rw [genuineSlots, List.mem_append, List.mem_flatten]
  constructor
  · rintro (h | hd)
    · obtain ⟨L, hL, hsl⟩ := h
      rw [List.mem_map] at hL
      obtain ⟨m, hm, rfl⟩ := hL
      exact Or.inl ⟨m, hm, mem_raws.mp hsl⟩
    · exact Or.inr (mem_diffs.mp hd)
  · rintro (⟨m, hm, h⟩ | hd)
    · exact Or.inl ⟨m.raws, List.mem_map.mpr ⟨m, hm, rfl⟩, mem_raws.mpr h⟩
    · exact Or.inr (mem_diffs.mpr hd)

/-- The strings occurring in a slot. -/
private def strs : CC s → List (Fin s → Bool)
  | .raw _ b => [b]
  | .dff _ b c => [b, c]

@[simp] private lemma subst_self (a : Fin s → Bool) (sl : CC s) : CC.subst a a sl = sl := by
  cases sl with
  | raw j b =>
      rw [CC.subst]
      by_cases h : b = a
      · rw [if_pos h, h]
      · rw [if_neg h]
  | dff j b c =>
      rw [CC.subst]
      by_cases hb : b = a <;> by_cases hc : c = a <;> simp_all

private lemma map_subst_self (a : Fin s → Bool) (L : List (CC s)) :
    L.map (CC.subst a a) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, subst_self, ih]

private lemma touchesb_eq (a : Fin s → Bool) (sl : CC s) :
    (CC.touchesb a sl = true) ↔ CC.touches a sl := by
  cases sl <;> simp [CC.touchesb, CC.touches]

private lemma not_touchesb_eq (a : Fin s → Bool) (sl : CC s) :
    ((!CC.touchesb a sl) = true) ↔ ¬ CC.touches a sl := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, touchesb_eq]

private lemma strs_subst (z z' : Fin s → Bool) (sl : CC s) :
    strs (CC.subst z z' sl) = (strs sl).map (fun b => if b = z then z' else b) := by
  cases sl <;> simp [CC.subst, strs]

private lemma touches_iff_mem_strs (z : Fin s → Bool) (sl : CC s) :
    CC.touches z sl ↔ z ∈ strs sl := by
  cases sl with
  | raw j b => simp only [CC.touches_raw, strs, List.mem_cons, List.mem_nil_iff, or_false]
               exact eq_comm
  | dff j b c => simp only [CC.touches_dff, strs, List.mem_cons, List.mem_nil_iff,
      or_false]; tauto

/-- `CC.subst z z'` is injective on slots all of whose strings avoid `z'`. -/
private lemma subst_inj {z z' : Fin s → Bool} {s₁ s₂ : CC s}
    (h₁ : z' ∉ strs s₁) (h₂ : z' ∉ strs s₂)
    (h : CC.subst z z' s₁ = CC.subst z z' s₂) : s₁ = s₂ := by
  have key : ∀ {b₁ b₂ : Fin s → Bool}, b₁ ∈ strs s₁ → b₂ ∈ strs s₂ →
      (if b₁ = z then z' else b₁) = (if b₂ = z then z' else b₂) → b₁ = b₂ := by
    intro b₁ b₂ hb₁ hb₂ hb
    by_cases hz : b₁ = z
    · rw [if_pos hz] at hb
      have hb2 : b₂ = z := by
        by_cases hz2 : b₂ = z
        · exact hz2
        · rw [if_neg hz2] at hb
          exact absurd (hb ▸ hb₂) h₂
      rw [hz, hb2]
    · rw [if_neg hz] at hb
      have hz2 : ¬ (b₂ = z) := by
        intro hz2
        rw [if_pos hz2] at hb
        exact h₁ (hb.symm ▸ hb₁)
      rw [if_neg hz2] at hb
      exact hb
  cases s₁ with
  | raw j b =>
      cases s₂ with
      | raw j' b' =>
          rw [CC.subst, CC.subst, CC.raw.injEq] at h
          rw [CC.raw.injEq]
          exact ⟨h.1, key (by simp [strs]) (by simp [strs]) h.2⟩
      | dff j' b' c' =>
          rw [CC.subst, CC.subst] at h
          exact absurd h (by simp)
  | dff j b c =>
      cases s₂ with
      | raw j' b' =>
          rw [CC.subst, CC.subst] at h
          exact absurd h (by simp)
      | dff j' b' c' =>
          rw [CC.subst, CC.subst, CC.dff.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          rw [CC.dff.injEq]
          exact ⟨h1, key (by simp [strs]) (by simp [strs]) h2,
            key (by simp [strs]) (by simp [strs]) h3⟩

/-- Substituting `z ↦ z'` (with `z' ≠ z`) produces a slot that never touches `z`. -/
private lemma subst_not_touches {z z' : Fin s → Bool} (hzz' : z' ≠ z) (sl : CC s) :
    ¬ CC.touches z (CC.subst z z' sl) := by
  rw [touches_iff_mem_strs, strs_subst, List.mem_map]
  rintro ⟨c, hc, hcz⟩
  by_cases hcz2 : c = z
  · rw [if_pos hcz2] at hcz
    exact hzz' hcz
  · rw [if_neg hcz2] at hcz
    exact hcz2 hcz

/-! ## 2. `CLeaf` and `IsSubdiv` facts -/

private lemma cleaf_eq_of {l₁ l₂ : CLeaf s} (h₁ : l₁.str = l₂.str) (h₂ : l₁.dep = l₂.dep) :
    l₁ = l₂ := by
  cases l₁; cases l₂; simp_all

private lemma children_mem_iff {m : CLeaf s} {h : m.dep < s} {x : CLeaf s} :
    x ∈ m.children h ↔
      (x.str = m.str ∨ x.str = Function.update m.str ⟨m.dep, h⟩ true) ∧ x.dep = m.dep + 1 := by
  rw [CLeaf.children]
  constructor
  · intro hx
    rw [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩
  · rintro ⟨hstr | hstr, hdep⟩
    · exact List.mem_cons.mpr (Or.inl (cleaf_eq_of hstr hdep))
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (cleaf_eq_of hstr hdep)))

private lemma mem_children_first (m : CLeaf s) (h : m.dep < s) :
    ∃ x ∈ m.children h, x.str = m.str := by
  refine ⟨⟨m.str, m.dep + 1, by omega, fun i hi => m.pad i (by omega)⟩, ?_, rfl⟩
  rw [children_mem_iff]
  exact ⟨Or.inl rfl, rfl⟩

private lemma mem_children_second (m : CLeaf s) (h : m.dep < s) :
    ∃ x ∈ m.children h, x.str = Function.update m.str ⟨m.dep, h⟩ true := by
  refine ⟨⟨Function.update m.str ⟨m.dep, h⟩ true, m.dep + 1, by omega, fun i hi => ?_⟩, ?_, rfl⟩
  · have hne : i ≠ ⟨m.dep, h⟩ := by
      intro he
      have : i.val = m.dep := by simpa using congrArg Fin.val he
      omega
    rw [Function.update_of_ne hne]
    exact m.pad i (by omega)
  · rw [children_mem_iff]
    exact ⟨Or.inr rfl, rfl⟩

private lemma children_str_agree {m : CLeaf s} {h : m.dep < s} {x : CLeaf s}
    (hx : x ∈ m.children h) : ∀ i : Fin s, i.val < m.dep → x.str i = m.str i := by
  obtain ⟨hstr, -⟩ := children_mem_iff.mp hx
  rcases hstr with h1 | h1
  · intro i _; rw [h1]
  · intro i hi
    have hne : i ≠ ⟨m.dep, h⟩ := by
      intro he
      have : i.val = m.dep := by simpa using congrArg Fin.val he
      omega
    rw [h1, Function.update_of_ne hne]

private lemma children_nodup (m : CLeaf s) (h : m.dep < s) : (m.children h).Nodup := by
  rw [CLeaf.children]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
  rw [List.mem_singleton]
  intro heq
  have hstr : m.str ⟨m.dep, h⟩ = true := by
    have := congrFun (congrArg CLeaf.str heq) ⟨m.dep, h⟩
    simpa [Function.update_self] using this
  have hfalse : m.str ⟨m.dep, h⟩ = false := m.pad ⟨m.dep, h⟩ (le_refl _)
  rw [hfalse] at hstr
  exact Bool.noConfusion hstr

/-- Two leaves of a subdivision with the same string are equal. -/
private lemma subdiv_str_inj {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ) {m₁ m₂ : CLeaf s}
    (h₁ : m₁ ∈ Λ) (h₂ : m₂ ∈ Λ) (h : m₁.str = m₂.str) : m₁ = m₂ := by
  refine ExistsUnique.unique (hsub m₁.str) ⟨h₁, fun i _ => rfl⟩ ⟨h₂, fun i _ => ?_⟩
  rw [h]

/-- Two leaves of a subdivision whose cells meet are equal. -/
private lemma subdiv_eq_of_cell {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ) {m₁ m₂ : CLeaf s}
    (h₁ : m₁ ∈ Λ) (h₂ : m₂ ∈ Λ) (x : Fin s → Bool)
    (hx₁ : ∀ i : Fin s, i.val < m₁.dep → m₁.str i = x i)
    (hx₂ : ∀ i : Fin s, i.val < m₂.dep → m₂.str i = x i) : m₁ = m₂ :=
  ExistsUnique.unique (hsub x) ⟨h₁, hx₁⟩ ⟨h₂, hx₂⟩

/-- A leaf of a subdivision agreeing with `l.str` below `l.dep` is `l`. -/
private lemma subdiv_eq_of_agree {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ) {l : CLeaf s}
    (hl : l ∈ Λ) {m : CLeaf s} (hm : m ∈ Λ)
    (h : ∀ i : Fin s, i.val < l.dep → m.str i = l.str i) : m = l := by
  refine subdiv_eq_of_cell hsub hm hl
    (fun i => if i.val < l.dep then l.str i else m.str i) ?_ ?_
  · intro i hi
    by_cases hil : i.val < l.dep
    · rw [if_pos hil]; exact h i hil
    · rw [if_neg hil]
  · intro i hi
    rw [if_pos hi]

/-- No leaf of a subdivision has the string of the second child of `l`. -/
private lemma subdiv_ne_second_child {Λ : List (CLeaf s)} (hsub : IsSubdiv Λ) {l : CLeaf s}
    (hl : l ∈ Λ) (hd : l.dep < s) {m : CLeaf s} (hm : m ∈ Λ) :
    m.str ≠ Function.update l.str ⟨l.dep, hd⟩ true := by
  intro h
  have hagree : ∀ i : Fin s, i.val < l.dep → m.str i = l.str i := by
    intro i hi
    have hne : i ≠ ⟨l.dep, hd⟩ := by
      intro he
      have : i.val = l.dep := by simpa using congrArg Fin.val he
      omega
    rw [h, Function.update_of_ne hne]
  have hml : m = l := subdiv_eq_of_agree hsub hl hm hagree
  have hfun : Function.update l.str ⟨l.dep, hd⟩ true = l.str := by rw [← h, hml]
  have hcontra := congrFun hfun ⟨l.dep, hd⟩
  rw [Function.update_self, l.pad ⟨l.dep, hd⟩ (le_refl _)] at hcontra
  exact Bool.noConfusion hcontra

/-! ## 3. The refinement `refine Λ l` -/

private lemma refine_decomp {Λ : List (CLeaf s)} {l : CLeaf s} (hnod : Λ.Nodup) (hl : l ∈ Λ)
    (hd : l.dep < s) :
    ∃ Λ₁ Λ₂ : List (CLeaf s), Λ = Λ₁ ++ l :: Λ₂ ∧
      refine Λ l = Λ₁ ++ l.children hd ++ Λ₂ := by
  obtain ⟨Λ₁, Λ₂, rfl⟩ := List.mem_iff_append.mp hl
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hnod
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  have hl1 : l ∉ Λ₁ := fun h => hdisj l h l (by simp) rfl
  have hl2 : l ∉ Λ₂ := (List.nodup_cons.mp hnd2).1
  refine ⟨Λ₁, Λ₂, rfl, ?_⟩
  rw [refine, List.flatMap_append, List.flatMap_cons]
  have key : ∀ (L : List (CLeaf s)), l ∉ L →
      List.flatMap (fun l' => if he : l' = l then
        (if hh : l'.dep < s then l'.children hh else [l']) else [l']) L = L := by
    intro L hL
    conv_rhs => rw [← List.map_id L, List.map_eq_flatMap]
    apply List.flatMap_congr
    intro x hx
    have hne : ¬ (x = l) := by intro h; rw [h] at hx; exact hL hx
    rw [dif_neg hne]
    rfl
  have h3 : (if he : l = l then (if hh : l.dep < s then l.children hh else [l]) else [l])
      = l.children hd := by
    rw [dif_pos rfl, dif_pos hd]
  rw [key Λ₁ hl1, h3, key Λ₂ hl2, List.append_assoc]

/-- Membership in the refinement, in terms of the decomposition. -/
private lemma mem_refine_of_decomp {Λ Λ₁ Λ₂ : List (CLeaf s)} {l : CLeaf s}
    (hΛ : Λ = Λ₁ ++ l :: Λ₂) (hd : l.dep < s) (hl1 : l ∉ Λ₁) (hl2 : l ∉ Λ₂) {m : CLeaf s} :
    m ∈ (Λ₁ ++ l.children hd ++ Λ₂) ↔ (m ∈ Λ ∧ m ≠ l) ∨ m ∈ l.children hd := by
  rw [hΛ]
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro ((hm | hm) | hm)
    · exact Or.inl ⟨Or.inl hm, fun h => hl1 (by rw [← h]; exact hm)⟩
    · exact Or.inr hm
    · exact Or.inl ⟨Or.inr (Or.inr hm), fun h => hl2 (by rw [← h]; exact hm)⟩
  · rintro (⟨hm | hm | hm, hne⟩ | hm)
    · exact Or.inl (Or.inl hm)
    · exact (hne hm).elim
    · exact Or.inr hm
    · exact Or.inl (Or.inr hm)

private lemma str_mem_refine {Λ : List (CLeaf s)} {l : CLeaf s} (hnod : Λ.Nodup) (hl : l ∈ Λ)
    (hd : l.dep < s) (b : Fin s → Bool) :
    strOf (refine Λ l) b ↔ (strOf Λ b ∨ b = Function.update l.str ⟨l.dep, hd⟩ true) := by
  obtain ⟨Λ₁, Λ₂, hΛ, href⟩ := refine_decomp hnod hl hd
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hΛ ▸ hnod
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  have hl1 : l ∉ Λ₁ := fun h => hdisj l h l (by simp) rfl
  have hl2 : l ∉ Λ₂ := (List.nodup_cons.mp hnd2).1
  subst hΛ
  rw [href]
  constructor
  · rintro ⟨m, hm, hmb⟩
    rw [List.mem_append, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact Or.inl ⟨m, List.mem_append.mpr (Or.inl hm), hmb⟩
    · obtain ⟨hstr, -⟩ := children_mem_iff.mp hm
      rcases hstr with h | h
      · exact Or.inl ⟨l, List.mem_append.mpr (Or.inr List.mem_cons_self),
          h.symm.trans hmb⟩
      · exact Or.inr (hmb.symm.trans h)
    · exact Or.inl ⟨m, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem l hm)), hmb⟩
  · rintro (⟨m, hm, hmb⟩ | hmb)
    · rw [List.mem_append, List.mem_cons] at hm
      rcases hm with hm | hm | hm
      · exact ⟨m, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm))), hmb⟩
      · subst hm
        obtain ⟨c, hc, hcs⟩ := mem_children_first m hd
        exact ⟨c, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc))),
          hcs.trans hmb⟩
      · exact ⟨m, List.mem_append.mpr (Or.inr hm), hmb⟩
    · obtain ⟨c, hc, hcs⟩ := mem_children_second l hd
      exact ⟨c, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc))),
        hcs.trans hmb.symm⟩

/-! ## 4. Pairwise distinctness of the slot list -/

/-- The `raw` slots of one leaf are pairwise distinct. -/
private lemma raws_nodup (l : CLeaf s) : (CLeaf.raws l).Nodup := by
  rw [CLeaf.raws]
  refine List.Nodup.map (fun a b h => (CC.raw.inj h).1) ?_
  exact List.Nodup.sublist List.filter_sublist (List.nodup_finRange s)

private lemma flatten_map_raws (Λ : List (CLeaf s)) :
    (Λ.map CLeaf.raws).flatten = Λ.flatMap CLeaf.raws := by
  induction Λ with
  | nil => rfl
  | cons l t ih => rw [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

/-- The raw slots of the leaves of `Λ` are pairwise distinct. -/
private lemma raws_flatten_nodup {Λ : List (CLeaf s)} (hnod : Λ.Nodup)
    (hstr : ∀ m₁ ∈ Λ, ∀ m₂ ∈ Λ, m₁.str = m₂.str → m₁ = m₂) :
    ((Λ.map CLeaf.raws).flatten).Nodup := by
  rw [flatten_map_raws, List.nodup_flatMap]
  refine ⟨fun m _ => raws_nodup m, ?_⟩
  rw [List.pairwise_iff_forall_sublist]
  intro m₁ m₂ hsub
  have hm₁ : m₁ ∈ Λ := hsub.subset (by simp)
  have hm₂ : m₂ ∈ Λ := hsub.subset (by simp)
  have hne : m₁ ≠ m₂ := by
    have h2 := List.Sublist.nodup hsub hnod
    simpa using (List.nodup_cons.mp h2).1
  show List.Disjoint (CLeaf.raws m₁) (CLeaf.raws m₂)
  rw [List.disjoint_iff_ne]
  intro x hx y hy hxy
  obtain ⟨j, -, rfl⟩ := mem_raws.mp hx
  obtain ⟨j', -, h1⟩ := mem_raws.mp hy
  rw [h1] at hxy
  exact hne (hstr m₁ hm₁ m₂ hm₂ (CC.raw.inj hxy).2)

/-- The difference slots of `Λ` are pairwise distinct. -/
private lemma diffs_nodup {Λ : List (CLeaf s)} (hnod : Λ.Nodup)
    (hstr : ∀ m₁ ∈ Λ, ∀ m₂ ∈ Λ, m₁.str = m₂.str → m₁ = m₂) :
    (genuineDiffs Λ).Nodup := by
  rw [genuineDiffs, List.nodup_flatMap]
  constructor
  · intro p hp
    refine List.Nodup.filterMap (fun a a' b hb hb' => ?_) (List.nodup_finRange s)
    by_cases ha : sCond a p.1.str p.2.str
    · have hfa : (if sCond a p.1.str p.2.str then some (CC.dff a p.1.str p.2.str) else none)
          = some (CC.dff a p.1.str p.2.str) := if_pos ha
      rw [hfa] at hb
      have hb1 : CC.dff a p.1.str p.2.str = b := Option.mem_some.mp hb
      by_cases ha' : sCond a' p.1.str p.2.str
      · have hfa' : (if sCond a' p.1.str p.2.str then some (CC.dff a' p.1.str p.2.str) else none)
            = some (CC.dff a' p.1.str p.2.str) := if_pos ha'
        rw [hfa'] at hb'
        have hb2 : CC.dff a' p.1.str p.2.str = b := Option.mem_some.mp hb'
        exact (CC.dff.inj (hb1.trans hb2.symm)).1
      · have hfa' : (if sCond a' p.1.str p.2.str then some (CC.dff a' p.1.str p.2.str) else none)
            = none := if_neg ha'
        rw [hfa'] at hb'
        exact absurd hb' (by simp)
    · have hfa : (if sCond a p.1.str p.2.str then some (CC.dff a p.1.str p.2.str) else none)
          = none := if_neg ha
      rw [hfa] at hb
      exact absurd hb (by simp)
  · rw [List.pairwise_iff_forall_sublist]
    intro p₁ p₂ hsub
    have hprod : (Λ.product Λ).Nodup := List.Nodup.product hnod hnod
    have hne : p₁ ≠ p₂ := by
      have h2 := List.Sublist.nodup hsub hprod
      simpa using (List.nodup_cons.mp h2).1
    have hp₁ : p₁.1 ∈ Λ ∧ p₁.2 ∈ Λ :=
      List.mem_product.mp (show p₁ ∈ Λ ×ˢ Λ from hsub.subset (by simp))
    have hp₂ : p₂.1 ∈ Λ ∧ p₂.2 ∈ Λ :=
      List.mem_product.mp (show p₂ ∈ Λ ×ˢ Λ from hsub.subset (by simp))
    show List.Disjoint ((fun p => List.filterMap
        (fun j : Fin s => if sCond j p.1.str p.2.str
          then some (CC.dff j p.1.str p.2.str) else none) (List.finRange s)) p₁)
      ((fun p => List.filterMap
        (fun j : Fin s => if sCond j p.1.str p.2.str
          then some (CC.dff j p.1.str p.2.str) else none) (List.finRange s)) p₂)
    rw [List.disjoint_iff_ne]
    intro x hx y hy hxy
    obtain ⟨j₁, -, hj₁⟩ := List.mem_filterMap.mp hx
    obtain ⟨j₂, -, hj₂⟩ := List.mem_filterMap.mp hy
    by_cases hs₁ : sCond j₁ p₁.1.str p₁.2.str
    · have h1 : (if sCond j₁ p₁.1.str p₁.2.str then some (CC.dff j₁ p₁.1.str p₁.2.str)
            else none) = some (CC.dff j₁ p₁.1.str p₁.2.str) := if_pos hs₁
      rw [h1] at hj₁
      have hx' : x = CC.dff j₁ p₁.1.str p₁.2.str := (Option.mem_some.mp hj₁).symm
      by_cases hs₂ : sCond j₂ p₂.1.str p₂.2.str
      · have h2 : (if sCond j₂ p₂.1.str p₂.2.str then some (CC.dff j₂ p₂.1.str p₂.2.str)
              else none) = some (CC.dff j₂ p₂.1.str p₂.2.str) := if_pos hs₂
        rw [h2] at hj₂
        have hy' : y = CC.dff j₂ p₂.1.str p₂.2.str := (Option.mem_some.mp hj₂).symm
        have heq : CC.dff j₁ p₁.1.str p₁.2.str = CC.dff j₂ p₂.1.str p₂.2.str := by
          rw [← hx', ← hy']
          exact hxy
        obtain ⟨-, hb, hc⟩ := CC.dff.inj heq
        have hp1 : p₁.1 = p₂.1 := hstr p₁.1 hp₁.1 p₂.1 hp₂.1 hb
        have hp2 : p₁.2 = p₂.2 := hstr p₁.2 hp₁.2 p₂.2 hp₂.2 hc
        exact hne (Prod.ext hp1 hp2)
      · have h2 : (if sCond j₂ p₂.1.str p₂.2.str then some (CC.dff j₂ p₂.1.str p₂.2.str)
              else none) = none := if_neg hs₂
        rw [h2] at hj₂
        exact absurd hj₂ (by simp)
    · have h1 : (if sCond j₁ p₁.1.str p₁.2.str then some (CC.dff j₁ p₁.1.str p₁.2.str)
            else none) = none := if_neg hs₁
      rw [h1] at hj₁
      exact absurd hj₁ (by simp)

/-- The slot list of a subdivision is pairwise distinct. -/
private lemma genuineSlots_nodup {Λ : List (CLeaf s)} (hnod : Λ.Nodup)
    (hstr : ∀ m₁ ∈ Λ, ∀ m₂ ∈ Λ, m₁.str = m₂.str → m₁ = m₂) :
    (genuineSlots Λ).Nodup := by
  rw [genuineSlots, List.nodup_append]
  refine ⟨raws_flatten_nodup hnod hstr, diffs_nodup hnod hstr, ?_⟩
  intro a ha b hb hcontra
  obtain ⟨L, hL, haL⟩ := List.mem_flatten.mp ha
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hL
  obtain ⟨j, -, rfl⟩ := mem_raws.mp haL
  obtain ⟨j', m₁, -, m₂, -, -, hb'⟩ := mem_diffs.mp hb
  rw [hb'] at hcontra
  exact absurd hcontra (by intro hh; cases hh)

/-! ## 5. Slot predicates, and membership in the two slot lists -/

/-- The slots of `genuineSlots Λ` that do not touch `l.str`. -/
private def rF (Λ : List (CLeaf s)) (l : CLeaf s) : List (CC s) :=
  (genuineSlots Λ).filter (fun sl => !CC.touchesb l.str sl)

/-- The slots of `genuineSlots Λ` that touch `l.str`, minus the topmost raw slot of `l`. -/
private def rBc (Λ : List (CLeaf s)) (l : CLeaf s) (hd : l.dep < s) : List (CC s) :=
  ((genuineSlots Λ).filter (fun sl => CC.touchesb l.str sl)).erase
    (CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str)

/-- The right-hand side of the slot identity of `cgenSlotsRefine`. -/
private def rhs (Λ : List (CLeaf s)) (l : CLeaf s) (hd : l.dep < s) : List (CC s) :=
  ((rF Λ l ++ (rBc Λ l hd).map (CC.subst l.str l.str))
      ++ (rBc Λ l hd).map (CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true)))
    ++ [CC.dff ⟨s - 1 - l.dep, by omega⟩ (Function.update l.str ⟨l.dep, hd⟩ true) l.str]

private lemma mem_raw_genuineSlots {Λ : List (CLeaf s)} {j : Fin s} {b : Fin s → Bool} :
    CC.raw j b ∈ genuineSlots Λ ↔ slotOf Λ j b := by
  rw [mem_slots]
  constructor
  · rintro (⟨m, hm, j', hj, heq⟩ | ⟨j', m₁, -, m₂, -, -, heq⟩)
    · obtain ⟨hj', hb⟩ := CC.raw.inj heq.symm
      exact ⟨m, hm, hb, by rw [hj'] at hj; exact hj⟩
    · exact absurd heq (by intro hh; cases hh)
  · rintro ⟨m, hm, hb, hj⟩
    exact Or.inl ⟨m, hm, j, hj, by rw [hb]⟩

private lemma mem_dff_genuineSlots {Λ : List (CLeaf s)} {j : Fin s} {b c : Fin s → Bool} :
    CC.dff j b c ∈ genuineSlots Λ ↔ strOf Λ b ∧ strOf Λ c ∧ sCond j b c := by
  rw [mem_slots]
  constructor
  · rintro (⟨m, hm, j', hj', heq⟩ | ⟨j', m₁, hm₁, m₂, hm₂, hc, heq⟩)
    · exact absurd heq (by intro hh; cases hh)
    · rw [CC.dff.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨⟨m₁, hm₁, rfl⟩, ⟨m₂, hm₂, rfl⟩, hc⟩
  · rintro ⟨⟨m₁, hm₁, rfl⟩, ⟨m₂, hm₂, rfl⟩, hc⟩
    exact Or.inr ⟨j, m₁, hm₁, m₂, hm₂, hc, rfl⟩

private lemma mem_refine_of_children {Λ : List (CLeaf s)} {l : CLeaf s} (hnod : Λ.Nodup)
    (hl : l ∈ Λ) (hd : l.dep < s) {x : CLeaf s} (hx : x ∈ l.children hd) :
    x ∈ refine Λ l := by
  obtain ⟨Λ₁, Λ₂, hΛ, href⟩ := refine_decomp hnod hl hd
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hΛ ▸ hnod
  rw [List.nodup_append] at hnd
  rw [href]
  refine (mem_refine_of_decomp hΛ hd ?_ ?_).mpr (Or.inr hx)
  · exact fun h => hnd.2.2 l h l (by simp) rfl
  · exact (List.nodup_cons.mp hnd.2.1).1

private lemma mem_dff_refine {Λ : List (CLeaf s)} {l : CLeaf s} (hnod : Λ.Nodup)
    (hl : l ∈ Λ) (hd : l.dep < s) {j : Fin s} {b c : Fin s → Bool} :
    CC.dff j b c ∈ genuineSlots (refine Λ l) ↔
      sCond j b c ∧ (strOf Λ b ∨ b = Function.update l.str ⟨l.dep, hd⟩ true)
        ∧ (strOf Λ c ∨ c = Function.update l.str ⟨l.dep, hd⟩ true) := by
  rw [mem_dff_genuineSlots, str_mem_refine hnod hl hd b, str_mem_refine hnod hl hd c]
  exact ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩

private lemma slotOf_refine {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) {j : Fin s} {b : Fin s → Bool} :
    slotOf (refine Λ l) j b ↔
      ((slotOf Λ j b ∧ b ≠ l.str)
        ∨ (b = l.str ∧ l.dep + 1 ≤ s - 1 - j.val)
        ∨ (b = Function.update l.str ⟨l.dep, hd⟩ true ∧ l.dep + 1 ≤ s - 1 - j.val)) := by
  obtain ⟨Λ₁, Λ₂, hΛ, href⟩ := refine_decomp hnod hl hd
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hΛ ▸ hnod
  rw [List.nodup_append] at hnd
  have hl1 : l ∉ Λ₁ := fun h => hnd.2.2 l h l (by simp) rfl
  have hl2 : l ∉ Λ₂ := (List.nodup_cons.mp hnd.2.1).1
  constructor
  · rintro ⟨m, hm, hstr, hdep⟩
    rcases (mem_refine_of_decomp hΛ hd hl1 hl2).mp (href ▸ hm) with ⟨hmΛ, hne⟩ | hmc
    · exact Or.inl ⟨⟨m, hmΛ, hstr, hdep⟩,
        fun hb => hne (subdiv_str_inj hsub hmΛ hl (by rw [hstr, hb]))⟩
    · obtain ⟨hc, hcd⟩ := children_mem_iff.mp hmc
      rcases hc with hc | hc
      · exact Or.inr (Or.inl ⟨hstr.symm.trans hc, by omega⟩)
      · exact Or.inr (Or.inr ⟨hstr.symm.trans hc, by omega⟩)
  · rintro (⟨⟨m, hm, hstr, hdep⟩, hne⟩ | ⟨hb, hj⟩ | ⟨hb, hj⟩)
    · refine ⟨m, ?_, hstr, hdep⟩
      rw [href]
      exact (mem_refine_of_decomp hΛ hd hl1 hl2).mpr
        (Or.inl ⟨hm, fun hml => hne (by rw [← hstr, hml])⟩)
    · obtain ⟨c, hc, hcs⟩ := mem_children_first l hd
      have hcd : c.dep = l.dep + 1 := (children_mem_iff.mp hc).2
      refine ⟨c, ?_, by rw [hcs, hb], by omega⟩
      rw [href]
      exact (mem_refine_of_decomp hΛ hd hl1 hl2).mpr (Or.inr hc)
    · obtain ⟨c, hc, hcs⟩ := mem_children_second l hd
      have hcd : c.dep = l.dep + 1 := (children_mem_iff.mp hc).2
      refine ⟨c, ?_, by rw [hcs, hb], by omega⟩
      rw [href]
      exact (mem_refine_of_decomp hΛ hd hl1 hl2).mpr (Or.inr hc)

/-! ## 6. The transfer of the slot condition across the split -/

private lemma sCond_congr {j j' : Fin s} {b b' c c' : Fin s → Bool} (hj : j = j')
    (hb : b = b') (hc : c = c') (h : sCond j b c) : sCond j' b' c' := by
  subst hj
  subst hb
  subst hc
  exact h

private lemma sCond_self_false (j : Fin s) (b : Fin s → Bool) : ¬ sCond j b b := by
  intro h
  have h1 := h.2.1
  have h2 := h.2.2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- `i ≠ ⟨d, _⟩` when `i.val < d`. -/
private lemma ne_mk_of_lt {i : Fin s} {d : ℕ} (hd : d < s) (hi : i.val < d) : i ≠ ⟨d, hd⟩ := by
  intro he
  have h : i.val = d := by simpa using congrArg Fin.val he
  omega

private lemma ne_mk_of_gt {i : Fin s} {d : ℕ} (hd : d < s) (hi : d < i.val) : i ≠ ⟨d, hd⟩ := by
  intro he
  have h : i.val = d := by simpa using congrArg Fin.val he
  omega

/-- A difference slot whose first string is the second child is either the image of a difference
slot whose first string is `l.str` (same pivot, strictly below `l.dep`), or the new top slot. -/
private lemma sCond_first {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ) (hl : l ∈ Λ)
    (hd : l.dep < s) {j : Fin s} {c : Fin s → Bool}
    (h : sCond j (Function.update l.str ⟨l.dep, hd⟩ true) c) (hc : strOf Λ c) :
    (s - 1 - l.dep < j.val ∧ sCond j l.str c) ∨ (j.val = s - 1 - l.dep ∧ c = l.str) := by
  have h1 : ∀ i : Fin s, i.val < s - 1 - j.val →
      Function.update l.str ⟨l.dep, hd⟩ true i = c i := h.1
  have h2 : Function.update l.str ⟨l.dep, hd⟩ true ⟨s - 1 - j.val, by omega⟩ = true := h.2.1
  have h3 : c ⟨s - 1 - j.val, by omega⟩ = false := h.2.2
  by_cases hkd : s - 1 - j.val = l.dep
  · refine Or.inr (And.intro (by omega) ?_)
    obtain ⟨m, hm, rfl⟩ := hc
    have hagree : ∀ i : Fin s, i.val < l.dep → m.str i = l.str i := by
      intro i hi
      have h4 := h1 i (by omega)
      rw [Function.update_of_ne (ne_mk_of_lt hd hi) true l.str] at h4
      exact h4.symm
    rw [subdiv_eq_of_agree hsub hl hm hagree]
  · have hklt : s - 1 - j.val < l.dep := by
      by_contra hcon
      have hne : (⟨s - 1 - j.val, by omega⟩ : Fin s) ≠ ⟨l.dep, hd⟩ := by
        intro he
        have hh : s - 1 - j.val = l.dep := by
          have := congrArg Fin.val he
          rw [Fin.val_mk, Fin.val_mk] at this
          exact this
        omega
      have hle : l.dep ≤ (⟨s - 1 - j.val, by omega⟩ : Fin s).val := by
        rw [Fin.val_mk]; omega
      rw [Function.update_of_ne hne true l.str, l.pad _ hle] at h2
      exact Bool.noConfusion h2
    refine Or.inl (And.intro (by omega) ?_)
    refine And.intro (fun i hi => ?_) (And.intro ?_ h3)
    · have h4 := h1 i (by omega)
      rw [Function.update_of_ne (ne_mk_of_lt hd (by omega)) true l.str] at h4
      exact h4
    · rw [Function.update_of_ne (ne_mk_of_lt hd (by omega)) true l.str] at h2
      exact h2

/-- A difference slot whose second string is the second child comes from a difference slot whose
second string is `l.str`, with the same pivot, strictly below `l.dep`. -/
private lemma sCond_second {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ) (hl : l ∈ Λ)
    (hd : l.dep < s) {j : Fin s} {b : Fin s → Bool}
    (h : sCond j b (Function.update l.str ⟨l.dep, hd⟩ true)) (hb : strOf Λ b) :
    s - 1 - l.dep < j.val ∧ sCond j b l.str := by
  have h1 : ∀ i : Fin s, i.val < s - 1 - j.val →
      b i = Function.update l.str ⟨l.dep, hd⟩ true i := h.1
  have h2 : b ⟨s - 1 - j.val, by omega⟩ = true := h.2.1
  have h3 : Function.update l.str ⟨l.dep, hd⟩ true ⟨s - 1 - j.val, by omega⟩ = false := h.2.2
  have hklt : s - 1 - j.val < l.dep := by
    by_contra hcon
    have hle : l.dep ≤ (⟨s - 1 - j.val, by omega⟩ : Fin s).val := by
      rw [Fin.val_mk]; omega
    have hlek : l.dep ≤ s - 1 - j.val := by
      rw [Fin.val_mk] at hle
      exact hle
    rcases lt_or_eq_of_le hlek with hlt | heq
    · obtain ⟨m, hm, rfl⟩ := hb
      have hagree : ∀ i : Fin s, i.val < l.dep → m.str i = l.str i := by
        intro i hi
        have h4 := h1 i (by omega)
        rw [Function.update_of_ne (ne_mk_of_lt hd hi) true l.str] at h4
        exact h4
      have hml := subdiv_eq_of_agree hsub hl hm hagree
      have hkf : l.str ⟨s - 1 - j.val, by omega⟩ = false :=
        l.pad _ (by rw [Fin.val_mk]; omega)
      rw [hml, hkf] at h2
      exact Bool.noConfusion h2
    · have hne : (⟨s - 1 - j.val, by omega⟩ : Fin s) = ⟨l.dep, hd⟩ := Fin.ext heq.symm
      rw [hne, Function.update_self] at h3
      exact Bool.noConfusion h3
  have hkf : l.str ⟨s - 1 - j.val, by omega⟩ = false := by
    rw [← Function.update_of_ne (ne_mk_of_lt hd hklt) true l.str]
    exact h3
  refine And.intro (by omega) (And.intro (fun i hi => ?_) (And.intro h2 hkf))
  have h4 := h1 i (by omega)
  rw [Function.update_of_ne (ne_mk_of_lt hd (by omega)) true l.str] at h4
  exact h4

/-! ## 7. Membership in the pieces of the right-hand side -/

private lemma mem_rF {Λ : List (CLeaf s)} {l : CLeaf s} {sl : CC s} :
    sl ∈ rF Λ l ↔ sl ∈ genuineSlots Λ ∧ ¬ CC.touches l.str sl := by
  rw [rF, List.mem_filter, not_touchesb_eq]

private lemma mem_rBc {Λ : List (CLeaf s)} {l : CLeaf s} (hd : l.dep < s)
    (hG : (genuineSlots Λ).Nodup) {sl : CC s} :
    sl ∈ rBc Λ l hd ↔ sl ∈ genuineSlots Λ ∧ CC.touches l.str sl
      ∧ sl ≠ CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str := by
  have herase := List.Nodup.erase_eq_filter
    (List.Nodup.filter (fun sl => CC.touchesb l.str sl) hG)
    (CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str)
  rw [rBc, herase, List.mem_filter, List.mem_filter, touchesb_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun hcon => by rw [hcon] at h3; simpa using h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, by simpa using h3⟩

/-- The images under `l.str ↦ a1` of the raw slots of `rBc` are exactly the raw slots `j a1` with
`l.dep + 1 ≤ s - 1 - j`. -/
private lemma mem_bc_map_raw {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) (hG : (genuineSlots Λ).Nodup)
    {j : Fin s} {b : Fin s → Bool} :
    (∃ s ∈ rBc Λ l hd,
        CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true) s = CC.raw j b)
      ↔ (b = Function.update l.str ⟨l.dep, hd⟩ true ∧ l.dep + 1 ≤ s - 1 - j.val) := by
  constructor
  · rintro ⟨s, hs, hsubst⟩
    obtain ⟨hsG, hst, hse⟩ := (mem_rBc hd hG).mp hs
    cases s with
    | raw j' b' =>
        rw [CC.subst, CC.raw.injEq] at hsubst
        obtain ⟨hj', hb⟩ := hsubst
        rw [touches_iff_mem_strs, strs, List.mem_singleton] at hst
        have hst' : b' = l.str := hst.symm
        rw [if_pos hst'] at hb
        obtain ⟨m, hm, hms, hmd⟩ := mem_raw_genuineSlots.mp hsG
        have hml : m = l := subdiv_str_inj hsub hm hl (hms.trans hst.symm)
        rw [hml] at hmd
        have hmdj : l.dep ≤ s - 1 - j.val := by rw [← hj']; exact hmd
        have hjle : j.val ≤ s - 1 - l.dep := by omega
        have hjne : j.val ≠ s - 1 - l.dep := by
          intro hh
          refine hse ?_
          rw [CC.raw.injEq]
          exact ⟨hj'.trans (Fin.ext hh), hst'⟩
        exact ⟨hb.symm, by omega⟩
    | dff j' b' c' =>
        rw [CC.subst] at hsubst
        exact absurd hsubst (by intro hh; cases hh)
  · rintro ⟨hb, hj⟩
    refine ⟨CC.raw j l.str, ?_, ?_⟩
    · rw [mem_rBc hd hG, mem_raw_genuineSlots]
      refine And.intro ?_ (And.intro ?_ ?_)
      · exact ⟨l, hl, rfl, by omega⟩
      · rw [touches_iff_mem_strs, strs, List.mem_singleton]
      · intro hcon
        rw [CC.raw.injEq] at hcon
        have hh : j.val = s - 1 - l.dep := by
          have := congrArg Fin.val hcon.1
          simpa using this
        omega
    · rw [CC.subst, if_pos rfl]
      rw [hb]

/-- Only the leaf `l` itself has the string `l.str`. -/
private lemma slotOf_congr {Λ : List (CLeaf s)} {j : Fin s} {b b' : Fin s → Bool} (h : b = b')
    (hb : slotOf Λ j b) : slotOf Λ j b' := by
  obtain ⟨m, hm, hms, hmd⟩ := hb
  exact ⟨m, hm, by rw [hms, h], hmd⟩

private lemma slotOf_self {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ) (hl : l ∈ Λ)
    {j : Fin s} (h : slotOf Λ j l.str) : l.dep ≤ s - 1 - j.val := by
  obtain ⟨m, hm, hms, hmd⟩ := h
  rw [subdiv_str_inj hsub hm hl hms] at hmd
  exact hmd

/-- The slot condition with `l.str` as first string transfers to the second child. -/
private lemma sCond_first' {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ) (hl : l ∈ Λ)
    (hd : l.dep < s) {j : Fin s} {c : Fin s → Bool} (h : sCond j l.str c) (hc : strOf Λ c) :
    sCond j (Function.update l.str ⟨l.dep, hd⟩ true) c := by
  have hklt : s - 1 - j.val < l.dep := by
    by_contra hcon
    have hle : l.dep ≤ (⟨s - 1 - j.val, by omega⟩ : Fin s).val := by rw [Fin.val_mk]; omega
    have hp := h.2.1
    rw [l.pad _ hle] at hp
    exact Bool.noConfusion hp
  have h1 : ∀ i : Fin s, i.val < s - 1 - j.val →
      Function.update l.str ⟨l.dep, hd⟩ true i = c i := by
    intro i hi
    rw [Function.update_of_ne (ne_mk_of_lt hd (by omega))]
    exact h.1 i hi
  have h2 : Function.update l.str ⟨l.dep, hd⟩ true ⟨s - 1 - j.val, by omega⟩ = true := by
    rw [Function.update_of_ne (ne_mk_of_lt hd hklt)]
    exact h.2.1
  exact ⟨h1, h2, h.2.2⟩

/-- The slot condition with `l.str` as second string transfers to the second child. -/
private lemma sCond_second' {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ) (hl : l ∈ Λ)
    (hd : l.dep < s) {j : Fin s} {b : Fin s → Bool} (h : sCond j b l.str) (hb : strOf Λ b) :
    sCond j b (Function.update l.str ⟨l.dep, hd⟩ true) := by
  have hklt : s - 1 - j.val < l.dep := by
    by_contra hcon
    have hle : l.dep ≤ (⟨s - 1 - j.val, by omega⟩ : Fin s).val := by rw [Fin.val_mk]; omega
    have hkf : l.str ⟨s - 1 - j.val, by omega⟩ = false := l.pad _ hle
    obtain ⟨m, hm, rfl⟩ := hb
    have hagree : ∀ i : Fin s, i.val < l.dep → m.str i = l.str i := by
      intro i hi
      exact h.1 i (by omega)
    have hml := subdiv_eq_of_agree hsub hl hm hagree
    have hp := h.2.1
    rw [hml, hkf] at hp
    exact Bool.noConfusion hp
  have h1 : ∀ i : Fin s, i.val < s - 1 - j.val →
      b i = Function.update l.str ⟨l.dep, hd⟩ true i := by
    intro i hi
    rw [Function.update_of_ne (ne_mk_of_lt hd (by omega))]
    exact h.1 i hi
  have h2 : Function.update l.str ⟨l.dep, hd⟩ true ⟨s - 1 - j.val, by omega⟩ = false := by
    rw [Function.update_of_ne (ne_mk_of_lt hd hklt)]
    exact h.2.2
  exact ⟨h1, h.2.1, h2⟩

/-- The images under `l.str ↦ a1` of the difference slots of `rBc` are exactly the difference
slots of the refinement whose first or second string is `a1`. -/
private lemma mem_bc_map_dff {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) (hG : (genuineSlots Λ).Nodup)
    {j : Fin s} {b c : Fin s → Bool} :
    (∃ s ∈ rBc Λ l hd,
        CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true) s = CC.dff j b c)
      ↔ ((∃ c' : Fin s → Bool, strOf Λ c' ∧ sCond j l.str c'
            ∧ b = Function.update l.str ⟨l.dep, hd⟩ true ∧ c = c')
        ∨ (∃ b' : Fin s → Bool, strOf Λ b' ∧ sCond j b' l.str
            ∧ b = b' ∧ c = Function.update l.str ⟨l.dep, hd⟩ true)) := by
  constructor
  · rintro ⟨s, hs, hsubst⟩
    obtain ⟨hsG, hst, hse⟩ := (mem_rBc hd hG).mp hs
    cases s with
    | raw j' b' =>
        rw [CC.subst] at hsubst
        exact absurd hsubst (by intro hh; cases hh)
    | dff j' b' c' =>
        rw [CC.subst, CC.dff.injEq] at hsubst
        obtain ⟨hj', hb, hc⟩ := hsubst
        obtain ⟨hbG, hcG, hcond⟩ := mem_dff_genuineSlots.mp hsG
        rw [touches_iff_mem_strs, strs, List.mem_cons, List.mem_singleton] at hst
        rcases hst with hst | hst
        · -- `b' = l.str`
          have hc'ne : c' ≠ l.str := by
            intro hcon
            have hp := hcond.2.1
            have hq := hcond.2.2
            rw [← hst] at hp
            rw [hcon] at hq
            rw [hp] at hq
            exact Bool.noConfusion hq
          rw [if_pos hst.symm] at hb
          rw [if_neg hc'ne] at hc
          exact Or.inl ⟨c', hcG, sCond_congr hj' hst.symm rfl hcond, hb.symm, hc.symm⟩
        · -- `c' = l.str`
          have hb'ne : b' ≠ l.str := by
            intro hcon
            have hp := hcond.2.1
            have hq := hcond.2.2
            rw [hcon] at hp
            rw [← hst] at hq
            rw [hp] at hq
            exact Bool.noConfusion hq
          rw [if_neg hb'ne] at hb
          rw [if_pos hst.symm] at hc
          exact Or.inr ⟨b', hbG, sCond_congr hj' rfl hst.symm hcond, hb.symm, hc.symm⟩
  · rintro (⟨c', hc'G, hcond, hb, hc⟩ | ⟨b', hb'G, hcond, hb, hc⟩)
    · have hc'ne : c' ≠ l.str := by
        intro hcon
        have hp := hcond.2.1
        have hq := hcond.2.2
        rw [hcon] at hq
        rw [hp] at hq
        exact Bool.noConfusion hq
      refine ⟨CC.dff j l.str c', ?_, ?_⟩
      · rw [mem_rBc hd hG, mem_dff_genuineSlots]
        refine And.intro (And.intro ?_ (And.intro ?_ ?_)) (And.intro ?_ ?_)
        · exact ⟨l, hl, rfl⟩
        · exact hc'G
        · exact hcond
        · rw [touches_iff_mem_strs, strs, List.mem_cons, List.mem_singleton]; exact Or.inl rfl
        · intro hcon
          exact absurd hcon (by intro hh; cases hh)
      · rw [CC.subst, if_pos rfl, if_neg hc'ne, hb, hc]
    · have hb'ne : b' ≠ l.str := by
        intro hcon
        have hp := hcond.2.1
        have hq := hcond.2.2
        rw [hcon] at hp
        rw [hp] at hq
        exact Bool.noConfusion hq
      refine ⟨CC.dff j b' l.str, ?_, ?_⟩
      · rw [mem_rBc hd hG, mem_dff_genuineSlots]
        refine And.intro (And.intro ?_ (And.intro ?_ ?_)) (And.intro ?_ ?_)
        · exact hb'G
        · exact ⟨l, hl, rfl⟩
        · exact hcond
        · rw [touches_iff_mem_strs, strs, List.mem_cons, List.mem_singleton]; exact Or.inr rfl
        · intro hcon
          exact absurd hcon (by intro hh; cases hh)
      · rw [CC.subst, if_neg hb'ne, if_pos rfl, hb, hc]

/-- `refine Λ l` has no repeated leaves. -/
private lemma refine_nodup {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) : (refine Λ l).Nodup := by
  obtain ⟨Λ₁, Λ₂, hΛ, href⟩ := refine_decomp hnod hl hd
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hΛ ▸ hnod
  rw [List.nodup_append] at hnd
  obtain ⟨hnd1, hnd2, hdisj⟩ := hnd
  have hl1 : l ∉ Λ₁ := fun h => hdisj l h l (by simp) rfl
  have hl2 : l ∉ Λ₂ := (List.nodup_cons.mp hnd2).1
  rw [href, List.nodup_append, List.nodup_append]
  have hnd2' : Λ₂.Nodup := (List.nodup_cons.mp hnd2).2
  refine ⟨⟨hnd1, children_nodup l hd, ?_⟩, hnd2', ?_⟩
  · intro a ha b hb hcon
    have haΛ : a ∈ Λ := by rw [hΛ]; exact List.mem_append_left _ ha
    have hb_agree : ∀ i : Fin s, i.val < l.dep → b.str i = l.str i := children_str_agree hb
    have : a = l := subdiv_eq_of_agree hsub hl haΛ (fun i hi => by rw [hcon]; exact hb_agree i hi)
    exact hl1 (this ▸ ha)
  · intro a ha b hb hcon
    rcases List.mem_append.mp ha with ha | ha
    · exact hdisj a ha b (List.mem_cons_of_mem l hb) hcon
    · have hbΛ : b ∈ Λ := by rw [hΛ]; exact List.mem_append_right _ (List.mem_cons_of_mem l hb)
      obtain ⟨hastr, -⟩ := children_mem_iff.mp ha
      have haΛ : a ∈ Λ := by rw [hcon]; exact hbΛ
      have hab : a = l := subdiv_eq_of_agree hsub hl haΛ (fun i hi => by
        rcases hastr with hastr | hastr
        · rw [hastr]
        · rw [hastr, Function.update_of_ne (ne_mk_of_lt hd hi)])
      exact hl2 (by rw [← hab, hcon]; exact hb)

/-- Distinct leaves of `refine Λ l` have distinct strings. -/
private lemma str_inj_refine {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) {m₁ m₂ : CLeaf s}
    (h₁ : m₁ ∈ refine Λ l) (h₂ : m₂ ∈ refine Λ l) (h : m₁.str = m₂.str) : m₁ = m₂ := by
  obtain ⟨Λ₁, Λ₂, hΛ, href⟩ := refine_decomp hnod hl hd
  have hnd : (Λ₁ ++ l :: Λ₂).Nodup := hΛ ▸ hnod
  rw [List.nodup_append] at hnd
  have hl1 : l ∉ Λ₁ := fun h => hnd.2.2 l h l (by simp) rfl
  have hl2 : l ∉ Λ₂ := (List.nodup_cons.mp hnd.2.1).1
  have hm₁ := (mem_refine_of_decomp hΛ hd hl1 hl2).mp (href ▸ h₁)
  have hm₂ := (mem_refine_of_decomp hΛ hd hl1 hl2).mp (href ▸ h₂)
  rcases hm₁ with ⟨h₁Λ, h₁ne⟩ | h₁c <;> rcases hm₂ with ⟨h₂Λ, h₂ne⟩ | h₂c
  · exact subdiv_str_inj hsub h₁Λ h₂Λ h
  · obtain ⟨h₂str, -⟩ := children_mem_iff.mp h₂c
    rcases h₂str with h₂str | h₂str
    · exact absurd (subdiv_str_inj hsub h₁Λ hl (by rw [h, h₂str])) h₁ne
    · exact absurd (by rw [h, h₂str] :
        m₁.str = Function.update l.str ⟨l.dep, hd⟩ true) (subdiv_ne_second_child hsub hl hd h₁Λ)
  · obtain ⟨h₁str, -⟩ := children_mem_iff.mp h₁c
    rcases h₁str with h₁str | h₁str
    · exact absurd (subdiv_str_inj hsub h₂Λ hl (by rw [← h, h₁str])) h₂ne
    · exact absurd (by rw [h.symm, h₁str] :
        m₂.str = Function.update l.str ⟨l.dep, hd⟩ true) (subdiv_ne_second_child hsub hl hd h₂Λ)
  · obtain ⟨-, h₁dep⟩ := children_mem_iff.mp h₁c
    obtain ⟨-, h₂dep⟩ := children_mem_iff.mp h₂c
    exact cleaf_eq_of h (by rw [h₁dep, h₂dep])

/-- The top slot condition: `a1` as first string, `l.str` as second. -/
private lemma sCond_top (l : CLeaf s) (hd : l.dep < s) :
    sCond ⟨s - 1 - l.dep, by omega⟩ (Function.update l.str ⟨l.dep, hd⟩ true) l.str := by
  have hkey : (⟨s - 1 - (⟨s - 1 - l.dep, by omega⟩ : Fin s).val, by omega⟩ : Fin s)
      = ⟨l.dep, hd⟩ := by
    apply Fin.ext
    show s - 1 - (⟨s - 1 - l.dep, by omega⟩ : Fin s).val = (⟨l.dep, hd⟩ : Fin s).val
    have h1 : (⟨s - 1 - l.dep, by omega⟩ : Fin s).val = s - 1 - l.dep := rfl
    have h2 : (⟨l.dep, hd⟩ : Fin s).val = l.dep := rfl
    rw [h1, h2]
    omega
  refine And.intro (fun i hi => ?_) (And.intro ?_ ?_)
  · have hh1 : (⟨s - 1 - l.dep, by omega⟩ : Fin s).val = s - 1 - l.dep := rfl
    have hh2 : i.val < s - 1 - (s - 1 - l.dep) := by rwa [hh1] at hi
    have hi' : i.val < l.dep := by omega
    rw [Function.update_of_ne (ne_mk_of_lt hd hi')]
  · rw [hkey, Function.update_self]
  · rw [hkey]
    exact l.pad _ (le_refl _)

/-- The image slots of the raw slots of `rBc` are the raw slots of the refinement. -/
private lemma raw_ne_raw_iff {j j' : Fin s} {b b' : Fin s → Bool} :
    CC.raw j b ≠ CC.raw j' b' ↔ ¬(j = j' ∧ b = b') := by
  rw [ne_eq, CC.raw.injEq]

private lemma mem_rhs_raw {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) (hG : (genuineSlots Λ).Nodup)
    (j : Fin s) (b : Fin s → Bool) :
    CC.raw j b ∈ rhs Λ l hd ↔
      ((slotOf Λ j b ∧ b ≠ l.str)
        ∨ (b = l.str ∧ l.dep + 1 ≤ s - 1 - j.val)
        ∨ (b = Function.update l.str ⟨l.dep, hd⟩ true ∧ l.dep + 1 ≤ s - 1 - j.val)) := by
  rw [rhs, List.mem_append, List.mem_append, List.mem_append, List.mem_singleton,
    mem_rF, map_subst_self, mem_rBc hd hG, List.mem_map, mem_bc_map_raw hsub hnod hl hd hG,
    mem_raw_genuineSlots]
  simp only [CC.touches_raw]
  rw [raw_ne_raw_iff]
  constructor
  · rintro (((⟨h1, h2⟩ | ⟨h1, h2, h3⟩) | ⟨hb, hj⟩) | h4)
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr (Or.inl ⟨h2, ?_⟩)
      have hdep := slotOf_self hsub hl (slotOf_congr h2 h1)
      have hjne : j.val ≠ s - 1 - l.dep := by
        intro hh
        exact h3 ⟨Fin.ext hh, h2⟩
      omega
    · exact Or.inr (Or.inr ⟨hb, hj⟩)
    · exact absurd h4 (by intro hh; cases hh)
  · rintro (⟨h1, h2⟩ | ⟨hb, hj⟩ | ⟨hb, hj⟩)
    · left; left; left; exact And.intro h1 h2
    · left; left; right
      refine And.intro ?_ (And.intro hb ?_)
      · exact ⟨l, hl, hb.symm, by omega⟩
      · rintro ⟨hjeq, -⟩
        have hjv : j.val = s - 1 - l.dep := by
          have h := congrArg Fin.val hjeq
          have h' : (⟨s - 1 - l.dep, by omega⟩ : Fin s).val = s - 1 - l.dep := rfl
          rwa [h'] at h
        omega
    · left; right; exact And.intro hb hj

private lemma strOf_congr {Λ : List (CLeaf s)} {b b' : Fin s → Bool} (h : b = b')
    (hb : strOf Λ b) : strOf Λ b' := by
  obtain ⟨m, hm, hms⟩ := hb
  exact ⟨m, hm, by rw [hms, h]⟩

/-- Membership of a difference slot in the right-hand side, in the form matching the slots of the
refinement. -/
private lemma mem_rhs_dff {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) (hG : (genuineSlots Λ).Nodup)
    (j : Fin s) (b c : Fin s → Bool) :
    CC.dff j b c ∈ rhs Λ l hd ↔
      (sCond j b c ∧ (strOf Λ b ∨ b = Function.update l.str ⟨l.dep, hd⟩ true)
        ∧ (strOf Λ c ∨ c = Function.update l.str ⟨l.dep, hd⟩ true)) := by
  rw [rhs, List.mem_append, List.mem_append, List.mem_append, List.mem_singleton,
    mem_rF, map_subst_self, mem_rBc hd hG, List.mem_map, mem_bc_map_dff hsub hnod hl hd hG,
    mem_dff_genuineSlots]
  simp only [CC.touches_dff, CC.dff.injEq]
  constructor
  · rintro (((⟨⟨hbG, hcG, hcond⟩, -⟩ | ⟨⟨hbG, hcG, hcond⟩, -, -⟩) | hmap) | ⟨hj, hb, hc⟩)
    · exact And.intro hcond (And.intro (Or.inl hbG) (Or.inl hcG))
    · exact And.intro hcond (And.intro (Or.inl hbG) (Or.inl hcG))
    · rcases hmap with ⟨c', hc'G, hcond', hb, hc⟩ | ⟨b', hb'G, hcond', hb, hc⟩
      · exact And.intro
          (sCond_congr rfl hb.symm hc.symm (sCond_first' hsub hl hd hcond' hc'G))
          (And.intro (Or.inr hb) (Or.inl (strOf_congr hc.symm hc'G)))
      · exact And.intro
          (sCond_congr rfl hb.symm hc.symm (sCond_second' hsub hl hd hcond' hb'G))
          (And.intro (Or.inl (strOf_congr hb.symm hb'G)) (Or.inr hc))
    · exact And.intro (sCond_congr hj.symm hb.symm hc.symm (sCond_top l hd))
        (And.intro (Or.inr hb) (Or.inl (strOf_congr hc.symm ⟨l, hl, rfl⟩)))
  · rintro ⟨hcond, hb, hc⟩
    rcases hb with hbG | hb
    · rcases hc with hcG | hc
      · by_cases hbl : b = l.str
        · left; left; right
          refine And.intro (And.intro hbG (And.intro hcG ?_))
            (And.intro (Or.inl hbl) ?_)
          · exact hcond
          · intro hcon; exact absurd hcon (by intro hh; cases hh)
        · by_cases hcl : c = l.str
          · left; left; right
            refine And.intro (And.intro hbG (And.intro hcG hcond))
              (And.intro (Or.inr hcl) ?_)
            intro hcon; exact absurd hcon (by intro hh; cases hh)
          · left; left; left
            exact And.intro (And.intro hbG (And.intro hcG hcond))
              (fun hcon => hcon.elim hbl hcl)
      · rcases sCond_second hsub hl hd (sCond_congr rfl rfl hc hcond) hbG with ⟨hlt, hcond'⟩
        left; right; right
        exact ⟨b, hbG, hcond', rfl, hc⟩
    · rcases hc with hcG | hc
      · rcases sCond_first hsub hl hd (sCond_congr rfl hb rfl hcond) hcG with
          ⟨hlt, hcond'⟩ | ⟨hjeq, hceq⟩
        · left; right; left
          exact ⟨c, hcG, hcond', hb, rfl⟩
        · right
          exact ⟨Fin.ext hjeq, hb, hceq⟩
      · exact absurd (sCond_congr rfl hb hc hcond) (sCond_self_false j _)

private lemma a1_ne (l : CLeaf s) (hd : l.dep < s) :
    Function.update l.str ⟨l.dep, hd⟩ true ≠ l.str := by
  intro h
  have h1 : Function.update l.str ⟨l.dep, hd⟩ true ⟨l.dep, hd⟩ = l.str ⟨l.dep, hd⟩ := by rw [h]
  rw [Function.update_self, l.pad ⟨l.dep, hd⟩ (le_refl _)] at h1
  exact Bool.noConfusion h1

/-- Every string of a slot of `genuineSlots Λ` is the string of a leaf of `Λ`. -/
private lemma strs_mem_genuineSlots {Λ : List (CLeaf s)} {sl : CC s}
    (h : sl ∈ genuineSlots Λ) {b : Fin s → Bool} (hb : b ∈ strs sl) : strOf Λ b := by
  cases sl with
  | raw j b' =>
      rw [strs, List.mem_singleton] at hb
      obtain ⟨m, hm, hms, -⟩ := mem_raw_genuineSlots.mp h
      exact strOf_congr hb.symm ⟨m, hm, hms⟩
  | dff j b' c' =>
      rw [strs, List.mem_cons, List.mem_singleton] at hb
      obtain ⟨hbG, hcG, -⟩ := mem_dff_genuineSlots.mp h
      rcases hb with hb | hb
      · exact strOf_congr hb.symm hbG
      · exact strOf_congr hb.symm hcG

/-- No string of a slot of `genuineSlots Λ` is the second child of `l`. -/
private lemma a1_not_mem_strs {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hl : l ∈ Λ) (hd : l.dep < s) {sl : CC s} (h : sl ∈ genuineSlots Λ) {b : Fin s → Bool}
    (hb : b ∈ strs sl) : b ≠ Function.update l.str ⟨l.dep, hd⟩ true := by
  intro hcon
  obtain ⟨m, hm, hms⟩ := strs_mem_genuineSlots h (hcon ▸ hb)
  exact subdiv_ne_second_child hsub hl hd hm hms

private lemma not_touches_ne {z : Fin s → Bool} {x y : CC s} (hx : ¬ CC.touches z x)
    (hy : CC.touches z y) : x ≠ y := fun h => hx (h ▸ hy)

/-- The right-hand side is a list without repetitions. -/
private lemma rhs_nodup {Λ : List (CLeaf s)} {l : CLeaf s} (hsub : IsSubdiv Λ)
    (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) (hG : (genuineSlots Λ).Nodup) :
    (rhs Λ l hd).Nodup := by
  have ha1 : Function.update l.str ⟨l.dep, hd⟩ true ≠ l.str := a1_ne l hd
  have hF : (rF Λ l).Nodup := List.Nodup.filter _ hG
  have hBc : (rBc Λ l hd).Nodup := (List.Nodup.filter _ hG).erase _
  have htd : CC.touches l.str
      (CC.dff ⟨s - 1 - l.dep, by omega⟩ (Function.update l.str ⟨l.dep, hd⟩ true) l.str) :=
    Or.inr rfl
  have hmap : ((rBc Λ l hd).map (CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true))).Nodup := by
    show List.Pairwise (fun x y => x ≠ y)
      (List.map (CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true)) (rBc Λ l hd))
    rw [List.pairwise_map]
    refine hBc.imp_of_mem ?_
    intro a b ha hb hab hcon
    refine hab (subst_inj ?_ ?_ hcon)
    · intro hba
      exact a1_not_mem_strs hsub hl hd ((mem_rBc hd hG).mp ha).1 hba rfl
    · intro hbb
      exact a1_not_mem_strs hsub hl hd ((mem_rBc hd hG).mp hb).1 hbb rfl
  rw [rhs, map_subst_self]
  refine List.nodup_append.mpr ⟨?_, List.nodup_singleton _, ?_⟩
  · refine List.nodup_append.mpr ⟨?_, hmap, ?_⟩
    · refine List.nodup_append.mpr ⟨hF, hBc, ?_⟩
      intro a ha b hb
      exact not_touches_ne (mem_rF.mp ha).2 ((mem_rBc hd hG).mp hb).2.1
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        intro hcon
        have haG := (mem_rF.mp ha).1
        rw [hcon] at haG
        have hls : l.str ∈ strs s := by
          rw [← touches_iff_mem_strs]
          exact ((mem_rBc hd hG).mp hs).2.1
        have hmem : Function.update l.str ⟨l.dep, hd⟩ true ∈
            strs (CC.subst l.str (Function.update l.str ⟨l.dep, hd⟩ true) s) := by
          rw [strs_subst]
          exact List.mem_map.mpr ⟨l.str, hls, by rw [if_pos rfl]⟩
        exact a1_not_mem_strs hsub hl hd haG hmem rfl
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        intro hcon
        exact (subst_not_touches ha1 s)
          (hcon.symm ▸ ((mem_rBc hd hG).mp ha).2.1)
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · intro hcon
        exact (mem_rF.mp ha).2 (hcon.symm ▸ (hb.symm ▸ htd))
      · intro hcon
        refine a1_not_mem_strs hsub hl hd ((mem_rBc hd hG).mp ha).1 ?_ rfl
        rw [hcon, hb]
        exact List.mem_cons_self
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
      intro hcon
      exact (subst_not_touches ha1 s) (hcon.symm ▸ (hb.symm ▸ htd))

private lemma count_of_nodup {l : List (CC s)} (h : l.Nodup) (a : CC s) :
    l.count a = if a ∈ l then 1 else 0 := by
  by_cases ha : a ∈ l
  · rw [if_pos ha]; exact List.count_eq_one_of_mem h ha
  · rw [if_neg ha, List.count_eq_zero.mpr ha]

private lemma perm_of_mem_nodup {L L' : List (CC s)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hmem : ∀ sl : CC s, sl ∈ L ↔ sl ∈ L') : L.Perm L' := by
  rw [List.perm_iff_count]
  intro sl
  by_cases h : sl ∈ L'
  · have h2 : sl ∈ L := (hmem sl).mpr h
    rw [count_of_nodup hL sl, count_of_nodup hL' sl, if_pos h, if_pos h2]
  · have h2 : sl ∉ L := fun hh => h ((hmem sl).mp hh)
    rw [count_of_nodup hL sl, count_of_nodup hL' sl, if_neg h, if_neg h2]

/-- The topmost raw slot of `l` is a genuine slot. -/
private lemma top_raw_mem {Λ : List (CLeaf s)} {l : CLeaf s} (hl : l ∈ Λ) (hd : l.dep < s) :
    CC.raw ⟨s - 1 - l.dep, by omega⟩ l.str ∈ genuineSlots Λ := by
  refine mem_slots.mpr (Or.inl ⟨l, hl, ⟨s - 1 - l.dep, by omega⟩, ?_, rfl⟩)
  have h : (⟨s - 1 - l.dep, by omega⟩ : Fin s).val = s - 1 - l.dep := rfl
  rw [h]
  omega

/-- **The step-compatibility of the iteration of `Work.Peluse.SwapC.concatAll`** (the slot
bookkeeping of KKL Proposition 6.2's iteration).

Let `Λ` be a `Nodup` subdivision (`IsSubdiv`: the cells of the leaves partition `{0,1}^s` — this
rules out a touching difference whose first-difference coordinate exceeds `l.dep`, by disjointness
of cells), `l ∈ Λ` a leaf of depth `< s`, `jh = s - 1 - l.dep` (the topmost raw slot of `l`),
`a1 = Function.update l.str ⟨l.dep, _⟩ true` (the second child of `l`; the first child has
`str = l.str`, so `CC.subst l.str l.str` is the identity on the slots touching `l.str`).

Then the genuine slots of the refinement `refine Λ l` are, up to permutation, the union of

* the slots of `genuineSlots Λ` not touching `l.str` (kept unchanged),
* the two versions of every slot of `genuineSlots Λ` touching `l.str` other than the topmost raw
  slot `CC.raw jh l.str` (which disappears): one with `l.str` substituted by `l.str` and one with
  `l.str` substituted by `a1`,
* the new difference slot `CC.dff jh a1 l.str`.

Moreover `CC.raw jh l.str ∈ genuineSlots Λ`. -/
theorem cgenSlotsRefine {s : ℕ} {Λ : List (CLeaf s)} {l : CLeaf s}
    (hsub : IsSubdiv Λ) (hnod : Λ.Nodup) (hl : l ∈ Λ) (hd : l.dep < s) :
    letI jh : Fin s := ⟨s - 1 - l.dep, by omega⟩
    letI a1 : Fin s → Bool := Function.update l.str ⟨l.dep, hd⟩ true
    letI Bc : List (CC s) :=
      ((genuineSlots Λ).filter (fun sl => CC.touchesb l.str sl)).erase (CC.raw jh l.str)
    (CC.raw jh l.str ∈ genuineSlots Λ) ∧
    (genuineSlots (refine Λ l)).Perm
      (((genuineSlots Λ).filter (fun sl => !CC.touchesb l.str sl))
        ++ Bc.map (CC.subst l.str l.str) ++ Bc.map (CC.subst l.str a1)
        ++ [CC.dff jh a1 l.str]) := by
  have hstr : ∀ m₁ ∈ Λ, ∀ m₂ ∈ Λ, m₁.str = m₂.str → m₁ = m₂ :=
    fun m₁ hm₁ m₂ hm₂ h => subdiv_str_inj hsub hm₁ hm₂ h
  have hG : (genuineSlots Λ).Nodup := genuineSlots_nodup hnod hstr
  have hLnod : (genuineSlots (refine Λ l)).Nodup :=
    genuineSlots_nodup (refine_nodup hsub hnod hl hd)
      (fun m₁ hm₁ m₂ hm₂ h => str_inj_refine hsub hnod hl hd hm₁ hm₂ h)
  have hRnod : (rhs Λ l hd).Nodup := rhs_nodup hsub hnod hl hd hG
  have hmem : ∀ sl : CC s, sl ∈ genuineSlots (refine Λ l) ↔ sl ∈ rhs Λ l hd := by
    intro sl
    cases sl with
    | raw j b => rw [mem_raw_genuineSlots, slotOf_refine hsub hnod hl hd,
        mem_rhs_raw hsub hnod hl hd hG j b]
    | dff j b c => rw [mem_dff_refine hnod hl hd, mem_rhs_dff hsub hnod hl hd hG j b c]
  exact ⟨top_raw_mem hl hd, perm_of_mem_nodup hLnod hRnod hmem⟩

end Work.Peluse.SwapC
