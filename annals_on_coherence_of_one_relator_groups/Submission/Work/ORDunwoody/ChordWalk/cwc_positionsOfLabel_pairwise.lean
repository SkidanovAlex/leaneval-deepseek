import Mathlib
import Submission.Work.ORDunwoody.ChordWalk.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.ChordWalk

open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## Bookkeeping for `positionsOfLabelAux`

`positionsOfLabelAux l e k` lists, in increasing order, the positions `i ≥ k` such that the
`(i-k)`-th visit of `l` has label `e`.  In particular it is a strictly increasing list of naturals,
which is what the target lemma records. -/

@[simp] theorem cwc_aux_positionsOfLabelAux_nil (e : Sym2 V) (k : ℕ) :
    positionsOfLabelAux (D := D) ([] : List (MidV D)) e k = [] := rfl

theorem cwc_aux_positionsOfLabelAux_cons (a : MidV D) (rest : List (MidV D)) (e : Sym2 V)
    (k : ℕ) :
    positionsOfLabelAux (a :: rest) e k =
      (if a.label = e then [k] else []) ++ positionsOfLabelAux rest e (k + 1) := rfl

/-- Every element of `positionsOfLabelAux l e k` lies in the window `[k, k + l.length)`. -/
theorem cwc_aux_positionsOfLabelAux_bounds {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (h : j ∈ positionsOfLabelAux l e k) : k ≤ j ∧ j < k + l.length := by
  induction l generalizing k j with
  | nil =>
    rw [cwc_aux_positionsOfLabelAux_nil] at h
    exact absurd h (List.not_mem_nil)
  | cons a rest ih =>
    rw [cwc_aux_positionsOfLabelAux_cons] at h
    simp only [List.length_cons]
    by_cases he : a.label = e
    · rw [if_pos he, List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_singleton] at h
        subst h
        omega
      · obtain ⟨h1, h2⟩ := ih h
        omega
    · rw [if_neg he, List.nil_append] at h
      obtain ⟨h1, h2⟩ := ih h
      omega

/-- `positionsOfLabelAux l e k` is strictly increasing. -/
theorem cwc_aux_positionsOfLabelAux_pairwise {l : List (MidV D)} {e : Sym2 V} {k : ℕ} :
    (positionsOfLabelAux l e k).Pairwise (· < ·) := by
  induction l generalizing k with
  | nil =>
    rw [cwc_aux_positionsOfLabelAux_nil]
    exact List.Pairwise.nil
  | cons a rest ih =>
    rw [cwc_aux_positionsOfLabelAux_cons, List.pairwise_append]
    refine ⟨?_, ih (k := k + 1), ?_⟩
    · by_cases he : a.label = e
      · rw [if_pos he]
        exact List.pairwise_singleton _ k
      · rw [if_neg he]
        exact List.Pairwise.nil
    · intro x hx y hy
      by_cases he : a.label = e
      · rw [if_pos he, List.mem_singleton] at hx
        subst hx
        have := (cwc_aux_positionsOfLabelAux_bounds hy).1
        omega
      · rw [if_neg he] at hx
        exact absurd hx (List.not_mem_nil)

/-! ## The target -/

theorem cwc_positionsOfLabel_pairwise {G : Type _} {V : Type _} [Group G] [MulAction G V]
    [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V}
    {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    {l : List (Work.ORDunwoody.Dunwoody.MidV D)} {e : Sym2 V} :
    (Work.ORDunwoody.Dunwoody.positionsOfLabel l e).Pairwise (· < ·) :=
  cwc_aux_positionsOfLabelAux_pairwise (k := 0)

end Work.ORDunwoody.ChordWalk
