import Mathlib
import Submission.Work.MainP.crtDefs

namespace Work.MainP

/-- `i ↦ cons (int i) nil` is injective: it is (the `cons`/`int`/`nil` encoding of) the identity. -/
private theorem phi_inj {a i : ℕ}
    (h : HvdH.Val.cons (HvdH.Val.int (a : ℤ)) HvdH.Val.nil
          = HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil) :
    a = i := by
  have h1 : (HvdH.Val.int (a : ℤ) : HvdH.Val) = HvdH.Val.int (i : ℤ) :=
    ((HvdH.Val.cons.injEq _ _ _ _).mp h).1
  exact Int.ofNat.inj (HvdH.Val.int.inj h1)

/-- The relation `x = cons (int i) nil ∧ y = int i` is functional on the image of
`i ↦ cons (int i) nil`: a pointwise-related pair of lists whose first coordinate is that image
has second coordinate the image of `i ↦ int i`. -/
private theorem map_eq_of_forall2 {l : List ℕ} {E I : List HvdH.Val}
    (hE : E = l.map (fun i : ℕ => HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil))
    (h : List.Forall₂ (fun x y => ∃ i : ℕ, x = HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil
                                    ∧ y = HvdH.Val.int (i : ℤ)) E I) :
    I = l.map (fun i : ℕ => HvdH.Val.int (i : ℤ)) := by
  induction l generalizing E I with
  | nil =>
      rw [hE] at h
      simp only [List.map_nil] at h
      obtain rfl := List.forall₂_nil_left_iff.mp h
      simp
  | cons a l ih =>
      rw [hE] at h
      simp only [List.map_cons] at h
      cases h with
      | cons hhead htail =>
          obtain ⟨i, hx, hy⟩ := hhead
          have hai : a = i := phi_inj hx
          subst hai
          have hb : _ = HvdH.Val.int (a : ℤ) := hy
          subst hb
          have hI : _ = l.map (fun i : ℕ => HvdH.Val.int (i : ℤ)) := ih rfl htail
          rw [hI]
          rfl

theorem crtB1_forall2_eq {S : ℕ} {E I : List HvdH.Val}
    (hE : E = (List.range S).map (fun i : ℕ => HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil))
    (h : List.Forall₂ (fun x y => ∃ i : ℕ, x = HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil ∧ y = HvdH.Val.int (i : ℤ)) E I) :
    I = Work.MainP.labVals (List.range S) := by
  have := map_eq_of_forall2 (l := List.range S) hE h
  simpa [labVals] using this

end Work.MainP
