import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.exists_split_arrowList
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.Howie.Defs
import Submission.Work.Howie.decomp_of_tail
import Submission.Work.Howie.efree_isReduced_codes_nodup

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie.L5

open Quiver

/-! ## `edgeCount` against a list of pairwise distinct codes -/

/-- If a list whose entries are all mapped to the same value is `Nodup`, then exactly one entry is
mapped to a given value occurring in the list. -/
theorem filter_length_eq_one_of_map_nodup {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l : List α} {g : α}, (l.map f).Nodup → g ∈ l →
      (l.filter (fun x => decide (f x = f g))).length = 1
  | [], g, _, hg => absurd hg (by simp)
  | x :: xs, g, h, hg => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hxs⟩ := h
    by_cases hfx : f x = f g
    · rw [List.filter_cons_of_pos (p := fun y => decide (f y = f g)) (by simp [hfx])]
      have hempty : xs.filter (fun y => decide (f y = f g)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        rw [decide_eq_true_iff]
        intro hfy
        exact hx (List.mem_map.mpr ⟨y, hy, hfy.trans hfx.symm⟩)
      rw [hempty]
      rfl
    · rw [List.filter_cons_of_neg (p := fun y => decide (f y = f g)) (by simp [hfx])]
      have hgxs : g ∈ xs := by
        rcases List.mem_cons.mp hg with h' | h'
        · subst h'
          exact absurd rfl hfx
        · exact h'
      exact filter_length_eq_one_of_map_nodup f hxs hgxs

/-- **A `Nodup` list of codes gives `edgeCount` one.**  If the codes `ω` of the arrows of a path
`p` are pairwise distinct, then the arrows of `p` carrying the code of a given arrow `g ∈ p` are
exactly `g` itself; in particular `edgeCount ω p g = 1`. -/
theorem edgeCount_eq_one_of_codes_nodup {V : Type u} [Quiver V] {α : Type u} [LinearOrder α]
    (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b) {g : Quiver.Total V}
    (h : (p.arrowList.map ω).Nodup) (hg : g ∈ p.arrowList) :
    Work.ORLocInd.Howie.edgeCount ω p g = 1 := by
  unfold Work.ORLocInd.Howie.edgeCount
  exact filter_length_eq_one_of_map_nodup ω h hg

/-- If `(l₂ ++ l₁).Nodup` and `a` occurs in neither `l₁` nor `l₂`, then `l₁ ++ a :: l₂` is
`Nodup`.  (The list of codes of a closed path is a cyclic rotation of the list of codes of its
wrap-around.) -/
theorem nodup_append_cons_swap {α : Type*} {l₁ l₂ : List α} {a : α}
    (h : (l₂ ++ l₁).Nodup) (h₁ : a ∉ l₁) (h₂ : a ∉ l₂) : (l₁ ++ a :: l₂).Nodup := by
  rw [List.nodup_append] at h
  obtain ⟨h₂n, h₁n, hdisj⟩ := h
  rw [List.nodup_append]
  refine ⟨h₁n, ?_, ?_⟩
  · exact List.Nodup.cons h₂ h₂n
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fun hxy => h₁ (hxy ▸ hx)
    · exact fun hxy => hdisj y hy x hx hxy.symm

/-! ## The power identity for the wrap-around -/

/-- **The wrap-around power identity.**  Consecutive occurrences of the arrow `E` in a closed path,
separated by the reduced `e`-free path `R · A₀`, make the path a power: writing
`Q = R · A₀`, the path `A₀ · E · (Q · E)^j · R` is the `(j+1)`-st power of the closed path
`A₀ · E · R`. -/
theorem compPower_shift_eq {V : Type u} [Quiver V] {w u v : V} (A₀ : Quiver.Path w u)
    (E : u ⟶ v) (R : Quiver.Path v w) (j : ℕ) :
    A₀.comp (E.toPath.comp
        ((Quiver.Path.compPower ((R.comp A₀).comp E.toPath) j).comp R)) =
      Quiver.Path.compPower (A₀.comp (E.toPath.comp R)) (j + 1) := by
  induction j with
  | zero =>
    rw [Quiver.Path.compPower_zero, Quiver.Path.nil_comp, Quiver.Path.compPower_succ,
      Quiver.Path.compPower_zero, Quiver.Path.comp_nil]
  | succ j ih =>
    rw [Quiver.Path.compPower_succ, Quiver.Path.comp_assoc, Quiver.Path.compPower_succ, ← ih]
    simp only [Quiver.Path.comp_assoc]

/-! ## The forest relator lemma (L5c) -/

/-- **L5c of `N4_LOCIND_LEAD.md`.**  If `Γ ∖ e` (the arrows whose code is `P.edgeOf e`) is a
forest — hypothesis `hfor`, every reduced closed `dpath` there is empty — then every arrow of a
reduced, cyclically reduced closed path `r` that is not a proper power and contains the arrow `e`
occurs exactly once in `r` *up to code*, i.e. `edgeCount P.edgeOf r g = 1` for every arrow `g`
of `r`.

The proof splits `r = A₀ · E · p₁` at its first arrow `E` of code `c = P.edgeOf e` (`A₀` is
`e`-free) and analyses the tail `p₁` with `decomp_of_tail`: either

* `p₁` is `e`-free — then `E` is the only crossing of the edge `{e, e⁻¹}` and the codes of `r` are
  the codes of `A₀`, then `c`, then the codes of `p₁`; the wrap-around `p₁ · A₀` is `e`-free and
  reduced, so its codes are pairwise distinct (`efree_isReduced_codes_nodup`) and `c` is fresh,
  giving a `Nodup` list of codes; or
* `p₁ = (Q · E)^j · R` with `j ≥ 1` — then the wrap-around shows `R · A₀ = Q`, the two reduced
  `e`-free paths from `E.right` to `E.left` coincide by uniqueness, and the power identity
  `compPower_shift_eq` exhibits `r` as the `(j+1)`-st power of `A₀ · E · R`, contradicting `hpp`. -/
theorem edgeCount_eq_one_of_forest_del {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode (P.edgeOf e)) y y),
      q.IsReduced → q.length = 0)
    {w : V} (r : Quiver.Path w w) (hr : r.IsReduced)
    (hcr : Work.ORLocInd.Howie.IsCyclicallyReduced r)
    (hpp : ¬ Work.ORLocInd.Howie.IsProperPower r) (he : e ∈ r.arrowList) :
    ∀ g ∈ r.arrowList, Work.ORLocInd.Howie.edgeCount P.edgeOf r g = 1 := by
  set c : P.α := P.edgeOf e with hc
  have hfor' : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0 := hfor
  rcases Work.Howie.strip_efree_decomp P c r with
    hfree | ⟨d, d', A₀, E, p₁, hA₀free, hEcode, hr_eq⟩
  · -- `r` is a path of `Γ ∖ e`, but it contains the arrow `e`
    exact (hfree e he hc.symm).elim
  · -- `r = A₀ · E · p₁` with `A₀` free of the code `c`
    have hrE : (A₀.comp (E.toPath.comp p₁)).IsReduced := by rw [← hr_eq]; exact hr
    have hcrE : Work.ORLocInd.Howie.IsCyclicallyReduced (A₀.comp (E.toPath.comp p₁)) := by
      rw [← hr_eq]; exact hcr
    -- the wrap-around `p₁ · A₀` of the cyclically reduced path `r` is reduced
    have hwrap : (p₁.comp A₀).IsReduced :=
      Work.Howie.isReduced_wrap_of_isCyclicallyReduced A₀ E p₁ hrE hcrE
    rcases Work.Howie.decomp_of_tail P c hsep hfor' (Quiver.Total.mk d d' E) hEcode
        (X := A₀) (p := p₁) hrE with
      hp₁free | ⟨Q, j, R, hj, hQred, hQfree, hRred, hRfree, hp₁eq⟩
    · -- `p₁` is free of the code `c`: `E` is the only crossing of `r`
      have hwrapfree : Work.Howie.EFree P c (p₁.comp A₀) := Work.Howie.EFree.comp hp₁free hA₀free
      have hnodup_wrap :
          ((p₁.arrowList.map P.edgeOf) ++ (A₀.arrowList.map P.edgeOf)).Nodup := by
        rw [← Work.Howie.map_arrowList_comp P.edgeOf p₁ A₀]
        exact Work.Howie.efree_isReduced_codes_nodup P c hsep hfor' hwrap hwrapfree
      -- the codes of `r` are those of `A₀`, then `c`, then those of `p₁`
      have hcodes : r.arrowList.map P.edgeOf =
          (A₀.arrowList.map P.edgeOf) ++ ([c] ++ (p₁.arrowList.map P.edgeOf)) := by
        rw [hr_eq, Work.Howie.map_arrowList_comp, Work.Howie.map_arrowList_comp,
          Work.Howie.arrowList_toPath, List.map_cons, List.map_nil, hEcode]
      have hnodup_r : (r.arrowList.map P.edgeOf).Nodup := by
        rw [hcodes]
        exact nodup_append_cons_swap hnodup_wrap (Work.Howie.EFree.codes_ne hA₀free)
          (Work.Howie.EFree.codes_ne hp₁free)
      intro g hg
      exact edgeCount_eq_one_of_codes_nodup P.edgeOf r hnodup_r hg
    · -- `p₁` meets the arrow `E` again: `r` is a proper power
      have hRA : (R.comp A₀).IsReduced := by
        have h := hwrap
        rw [hp₁eq, Quiver.Path.comp_assoc] at h
        exact Work.Howie.isReduced_of_comp_right h
      -- the two reduced `e`-free paths `R · A₀` and `Q` from `E.right` to `E.left` coincide
      have hQA₀ : R.comp A₀ = Q :=
        Work.Howie.efree_isReduced_eq_of_same_ends P c hfor' hRA hQred
          (Work.Howie.EFree.comp hRfree hA₀free) hQfree
      have hpow : r = Quiver.Path.compPower (A₀.comp (E.toPath.comp R)) (j + 1) := by
        rw [hr_eq, hp₁eq, ← hQA₀]
        exact compPower_shift_eq A₀ E R j
      exact absurd ⟨A₀.comp (E.toPath.comp R), j + 1, by omega, hpow⟩ hpp

end Work.ORLocInd.Howie.L5
