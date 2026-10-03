import Mathlib
import Submission.Work.Peluse.SwapC.cprocDefs

namespace Work.Peluse.SwapC

set_option autoImplicit false

variable {s : ℕ}

/-! ## Elementary facts about `CLeaf`, `Agree` and `CLeaf.children` -/

/-- Equality of leaves is equality of string and depth. -/
theorem CLeaf.eq_iff {l₁ l₂ : CLeaf s} :
    l₁ = l₂ ↔ l₁.str = l₂.str ∧ l₁.dep = l₂.dep := by
  refine ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
  cases l₁
  cases l₂
  simp_all

/-- Every leaf's own string lies in its cell. -/
theorem Agree.str (l : CLeaf s) : Agree l.str l := fun _ _ => rfl

/-- A child of `m` has depth `m.dep + 1`. -/
theorem children_dep_eq {m : CLeaf s} {h : m.dep < s} {a : CLeaf s}
    (ha : a ∈ m.children h) : a.dep = m.dep + 1 := by
  rw [CLeaf.children] at ha
  rcases List.mem_cons.mp ha with h' | h'
  · rw [h']
  · rw [List.mem_singleton] at h'
    rw [h']

/-- A child of `m` agrees with `m` on the first `m.dep` coordinates. -/
theorem mem_children_str {m : CLeaf s} {h : m.dep < s} {a : CLeaf s}
    (ha : a ∈ m.children h) : ∀ i : Fin s, i.val < m.dep → a.str i = m.str i := by
  rw [CLeaf.children] at ha
  rcases List.mem_cons.mp ha with h' | h'
  · intro i _; rw [h']
  · rw [List.mem_singleton] at h'
    subst h'
    intro i hi
    have hne : i ≠ ⟨m.dep, h⟩ := by
      intro he
      have : i.val = m.dep := by simpa using congrArg Fin.val he
      omega
    change Function.update m.str ⟨m.dep, h⟩ true i = m.str i
    rw [Function.update_of_ne hne]

/-- The cell of a child of `m` is contained in the cell of `m`. -/
theorem Agree.of_children {m : CLeaf s} {h : m.dep < s} {a : CLeaf s}
    (ha : a ∈ m.children h) {x : Fin s → Bool} (hx : Agree x a) : Agree x m := by
  intro i hi
  rw [← mem_children_str ha i hi]
  exact hx i (by have := children_dep_eq ha; omega)

/-- The two children of a splittable leaf are distinct. -/
theorem children_list_nodup (m : CLeaf s) (h : m.dep < s) : (m.children h).Nodup := by
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

/-! ## `csplitFirst` preserves `Nodup` on subdivisions -/

/-- A subdivision is in particular pairwise disjoint: two leaves whose cells meet are equal. -/
theorem pairDisj_of_isSubdiv {Λ : List (CLeaf s)} (h : IsSubdiv Λ) : PairDisj Λ := by
  intro l₁ hl₁ l₂ hl₂ hx
  obtain ⟨x, hx₁, hx₂⟩ := hx
  exact ExistsUnique.unique (h x) ⟨hl₁, hx₁⟩ ⟨hl₂, hx₂⟩

/-- A child of a leaf `m` of a pairwise disjoint list cannot occur in that list: its cell lies
inside `m`'s cell and its depth is strictly larger. -/
theorem child_not_mem_of_pairDisj {Λ : List (CLeaf s)} (hpd : PairDisj Λ) {m : CLeaf s}
    (hm : m ∈ Λ) {h : m.dep < s} {a : CLeaf s} (ha : a ∈ m.children h) : a ∉ Λ := by
  intro haΛ
  have hdep : a.dep = m.dep + 1 := children_dep_eq ha
  have hxm : Agree a.str m := Agree.of_children ha (Agree.str a)
  have heq : m = a := hpd m hm a haΛ ⟨a.str, hxm, Agree.str a⟩
  rw [heq] at hdep
  omega

/-- Every leaf of `csplitFirst Λ` lies in the cell of some leaf of `Λ`. -/
theorem exists_agree_of_mem_csplitFirst {Λ : List (CLeaf s)} {l' : CLeaf s}
    (h : l' ∈ csplitFirst Λ) : ∃ l ∈ Λ, ∀ x, Agree x l' → Agree x l := by
  induction Λ with
  | nil => simp [csplitFirst] at h
  | cons m rest ih =>
    rw [csplitFirst.eq_2] at h
    by_cases hm : m.dep < s
    · rw [dif_pos hm] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨m, List.mem_cons_self .., fun x hx => Agree.of_children h hx⟩
      · exact ⟨l', List.mem_cons_of_mem m h, fun x hx => hx⟩
    · rw [dif_neg hm] at h
      rcases List.mem_cons.mp h with h | h
      · exact ⟨m, List.mem_cons_self .., fun x hx => by rw [h] at hx; exact hx⟩
      · obtain ⟨l, hl, hle⟩ := ih h
        exact ⟨l, List.mem_cons_of_mem m hl, hle⟩

/-- **`csplitFirst` preserves `Nodup`** on a pairwise disjoint list: it splits the first leaf of
depth `< s` into its two distinct children, which are absent from the tail. -/
theorem nodup_csplitFirst {Λ : List (CLeaf s)} (hnod : Λ.Nodup) (hpd : PairDisj Λ) :
    (csplitFirst Λ).Nodup := by
  induction Λ with
  | nil => simp [csplitFirst]
  | cons m rest ih =>
    obtain ⟨hmnot, hnod'⟩ := List.nodup_cons.mp hnod
    have hpd' : PairDisj rest := fun l₁ hl₁ l₂ hl₂ hx =>
      hpd l₁ (List.mem_cons_of_mem m hl₁) l₂ (List.mem_cons_of_mem m hl₂) hx
    rw [csplitFirst.eq_2]
    by_cases hm : m.dep < s
    · rw [dif_pos hm]
      rw [List.nodup_append]
      refine ⟨children_list_nodup m hm, hnod', ?_⟩
      intro a ha b hb hab
      have hmem : a ∈ m :: rest := by
        rw [hab]
        exact List.mem_cons_of_mem m hb
      exact child_not_mem_of_pairDisj (h := hm) hpd (List.mem_cons_self ..) ha hmem
    · rw [dif_neg hm, List.nodup_cons]
      refine ⟨?_, ih hnod' hpd'⟩
      intro hmem
      obtain ⟨l, hl, hle⟩ := exists_agree_of_mem_csplitFirst hmem
      have hx : Agree m.str l := hle m.str (Agree.str m)
      have heq : m = l := hpd m (List.mem_cons_self ..) l (List.mem_cons_of_mem m hl)
        ⟨m.str, Agree.str m, hx⟩
      have : m ∈ rest := by rw [heq]; exact hl
      exact hmnot this

/-- **The subdivision lists of the process are `Nodup`** (needed for the slot bookkeeping of
`Work.Peluse.SwapC.concatAll`, whose step lemmas assume `Λ.Nodup`).  Prove it by induction on `k`
maintaining `Nodup` along `csplitFirst`: the two children of a splittable leaf are distinct, are not
in the tail (their depths are one larger and the cell of each child is strictly inside the parent's
cell, so it cannot be the cell of another leaf of the subdivision `hsub`), and the tail is
unchanged.  Note that `IsSubdiv` alone does not give `Nodup` (it only forbids repeated *values*),
but `cproc s k` is `Nodup` for every `k`. -/
theorem cprocNodup (s : ℕ) (hsub : ∀ k : ℕ, IsSubdiv (cproc s k)) :
    ∀ k : ℕ, (cproc s k).Nodup := by
  intro k
  induction k with
  | zero => rw [cproc.eq_1]; simp
  | succ k ih =>
    rw [cproc.eq_2]
    exact nodup_csplitFirst ih (pairDisj_of_isSubdiv (hsub k))

end Work.Peluse.SwapC
