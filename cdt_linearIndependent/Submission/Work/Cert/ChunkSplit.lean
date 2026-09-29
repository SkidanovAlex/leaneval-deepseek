import Submission.Work.Cert.WindDefs

/-! # Splitting a certificate chunk into small kernel checks (nanoda memory)

`arcsOK2` / `warcsOK` of a concatenation follow from the checks of the pieces plus the (cheap) boundary
conditions, so a chunk can be verified as several small `decide +kernel` lemmas: nanoda keeps the whole
reduction DAG of one declaration in memory, and a 60-leaf chunk needs ~28 M expressions (≈ 1.5 GB per thread). -/

namespace Work.Cert

theorem csplit_arcs_core (Fx Fy : Int) (l1 l2 : List ArcD) (a b : ArcD)
    (h1 : arcsOK2 b.Ex b.Ey l1 = true) (h2 : arcsOK2 Fx Fy l2 = true)
    (ha : l1.getLast? = some a) (hb : l2.head? = some b)
    (hk : decide (a.k = b.k) = true) (hj : decide (a.j + 1 = b.j) = true) :
    arcsOK2 Fx Fy (l1 ++ l2) = true := by
  induction l1 with
  | nil => simp at ha
  | cons x t ih =>
    cases l2 with
    | nil => simp at hb
    | cons y l2' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      cases t with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        simp only [arcsOK2] at h1
        simp only [List.cons_append, List.nil_append, arcsOK2, h1, hk, hj, h2, Bool.and_self]
      | cons z t' =>
        simp only [arcsOK2, Bool.and_eq_true] at h1
        obtain ⟨⟨⟨h1a, h1b⟩, h1c⟩, h1d⟩ := h1
        have ha' : (z :: t').getLast? = some a := by
          simpa [List.getLast?_cons_cons] using ha
        have := ih h1d ha'
        simp only [List.cons_append] at this ⊢
        simp only [arcsOK2, h1a, h1b, h1c, this, Bool.and_self]

theorem csplit_warcs_core (Fx Fy : Int) (l1 l2 : List WArc) (a b : WArc)
    (h1 : warcsOK b.Ex b.Ey l1 = true) (h2 : warcsOK Fx Fy l2 = true)
    (ha : l1.getLast? = some a) (hb : l2.head? = some b)
    (hj : decide (a.j + 1 = b.j) = true) :
    warcsOK Fx Fy (l1 ++ l2) = true := by
  induction l1 with
  | nil => simp at ha
  | cons x t ih =>
    cases l2 with
    | nil => simp at hb
    | cons y l2' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      cases t with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at ha
        subst ha
        simp only [warcsOK] at h1
        simp only [List.cons_append, List.nil_append, warcsOK, h1, hj, h2, Bool.and_self]
      | cons z t' =>
        simp only [warcsOK, Bool.and_eq_true] at h1
        obtain ⟨⟨h1a, h1b⟩, h1c⟩ := h1
        have ha' : (z :: t').getLast? = some a := by
          simpa [List.getLast?_cons_cons] using ha
        have := ih h1c ha'
        simp only [List.cons_append] at this ⊢
        simp only [warcsOK, h1a, h1b, this, Bool.and_self]

/-- chunk splitting with literal boundary data (all side conditions are one small `decide`). -/
theorem csplit_arcs (Fx Fy bx bY : Int) (l1 l2 : List ArcD)
    (h1 : arcsOK2 bx bY l1 = true) (h2 : arcsOK2 Fx Fy l2 = true)
    (hc : (match l1.getLast?, l2.head? with
      | some a, some b => decide (b.Ex = bx) && decide (b.Ey = bY) && decide (a.k = b.k) && decide (a.j + 1 = b.j)
      | _, _ => false) = true) :
    arcsOK2 Fx Fy (l1 ++ l2) = true := by
  cases ha : l1.getLast? with
  | none => simp [ha] at hc
  | some a =>
    cases hb : l2.head? with
    | none => simp [ha, hb] at hc
    | some b =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hx, hy⟩, hk⟩, hj⟩ := hc
      subst hx hy
      exact csplit_arcs_core Fx Fy l1 l2 a b h1 h2 ha hb (by simp [hk]) (by simp [hj])

/-- winding-chunk splitting with literal boundary data. -/
theorem csplit_warcs (Fx Fy bx bY : Int) (l1 l2 : List WArc)
    (h1 : warcsOK bx bY l1 = true) (h2 : warcsOK Fx Fy l2 = true)
    (hc : (match l1.getLast?, l2.head? with
      | some a, some b => decide (b.Ex = bx) && decide (b.Ey = bY) && decide (a.j + 1 = b.j)
      | _, _ => false) = true) :
    warcsOK Fx Fy (l1 ++ l2) = true := by
  cases ha : l1.getLast? with
  | none => simp [ha] at hc
  | some a =>
    cases hb : l2.head? with
    | none => simp [ha, hb] at hc
    | some b =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hx, hy⟩, hj⟩ := hc
      subst hx hy
      exact csplit_warcs_core Fx Fy l1 l2 a b h1 h2 ha hb (by simp [hj])

end Work.Cert
