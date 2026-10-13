import Mathlib
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4c.erealIntervalToIoo
import Submission.Work.WilG4c.eqEndpointsOfIoo
import Submission.Work.WilG4c.eqEndpointsOfSingleton
import Submission.Work.WilG4c.fibreParamIoo

namespace Work.WilG4c

theorem cellFibre_param {n : ℕ} {Z : Set (Fin (n+1) → ℝ)} (hZ : WilkiesDesign.IsCell (n+1) Z)
    {lo hi : (Fin n → ℝ) → ℝ}
    (hlo : ∀ l : Fin n → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
        (∀ x : ℝ, Fin.snoc l x ∈ Z → lo l ≤ x ∧ x ≤ hi l) ∧
        (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u) ∧
        (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x)) :
    ∀ l : Fin n → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
      ((∃ c : ℝ, lo l = c ∧ hi l = c ∧ {x : ℝ | Fin.snoc l x ∈ Z} = {c}) ∨
       (∃ a b : ℝ, a < b ∧ lo l = a ∧ hi l = b ∧
          {x : ℝ | Fin.snoc l x ∈ Z} = Set.Ioo a b)) ∧
      (∀ t ∈ Set.Ioo (0:ℝ) 1, Fin.snoc l (lo l + t * (hi l - lo l)) ∈ Z) ∧
      (∀ x : ℝ, Fin.snoc l x ∈ Z → ∃ t ∈ Set.Ioo (0:ℝ) 1, x = lo l + t * (hi l - lo l)) := by
  intro l hl
  obtain ⟨hbd, h2, h3⟩ := hlo l hl
  have h1 : ∀ x ∈ ({x : ℝ | Fin.snoc l x ∈ Z}), lo l ≤ x ∧ x ≤ hi l :=
    fun x hx => hbd x hx
  have hl2 : ∀ u : ℝ, lo l < u → ∃ x ∈ ({x : ℝ | Fin.snoc l x ∈ Z}), x < u := fun u hu => by
    obtain ⟨x, hx, hxu⟩ := h2 u hu; exact ⟨x, hx, hxu⟩
  have hl3 : ∀ u : ℝ, u < hi l → ∃ x ∈ ({x : ℝ | Fin.snoc l x ∈ Z}), u < x := fun u hu => by
    obtain ⟨x, hx, hxu⟩ := h3 u hu; exact ⟨x, hx, hxu⟩
  have hne : ({x : ℝ | Fin.snoc l x ∈ Z}).Nonempty := hl
  rcases Work.WilG4a.isCell_fiber n hZ l with ⟨x0, hx0⟩ | ⟨a, b, hab⟩
  · -- the fibre is the singleton `{x0}`
    obtain ⟨hloeq, hhieq⟩ := eqEndpointsOfSingleton hx0 h1 hl2 hl3
    refine ⟨Or.inl ⟨x0, hloeq, hhieq, hx0⟩, ?_, ?_⟩
    · intro t ht
      change lo l + t * (hi l - lo l) ∈ ({x : ℝ | Fin.snoc l x ∈ Z})
      rw [hloeq, hhieq, hx0]
      simp
    · intro x hx
      refine ⟨(1:ℝ)/2, by norm_num, ?_⟩
      have hx' : x = x0 := by
        have : x ∈ ({x0} : Set ℝ) := hx0 ▸ hx
        exact Set.mem_singleton_iff.mp this
      rw [hloeq, hhieq, hx']
      ring
  · -- the fibre is the open interval `(a, b)` of `EReal`
    have hne' : ({y : ℝ | a < (y : EReal) ∧ (y : EReal) < b}).Nonempty := by
      rw [← hab]; exact hne
    have hbdd : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → lo l ≤ x ∧ x ≤ hi l := by
      intro x hxa hxb
      apply h1
      rw [hab]
      exact ⟨hxa, hxb⟩
    obtain ⟨_, _, hSeq⟩ := erealIntervalToIoo hne' hbdd
    have hSI : {y : ℝ | Fin.snoc l y ∈ Z} = Set.Ioo a.toReal b.toReal := by
      rw [hab, hSeq]
    obtain ⟨hloeq, hhieq⟩ := eqEndpointsOfIoo hSI hne h1 hl2 hl3
    have hra_lt_rb : a.toReal < b.toReal := by
      obtain ⟨x0, hx0⟩ := hne
      have hx0I : x0 ∈ Set.Ioo a.toReal b.toReal := hSI ▸ hx0
      exact lt_trans (Set.mem_Ioo.mp hx0I).1 (Set.mem_Ioo.mp hx0I).2
    have hSI' : {y : ℝ | Fin.snoc l y ∈ Z} = Set.Ioo (lo l) (hi l) := by
      rw [hSI, hloeq, hhieq]
    have hlt' : lo l < hi l := by rw [hloeq, hhieq]; exact hra_lt_rb
    obtain ⟨hpar1, hpar2⟩ := fibreParamIoo hSI' hlt'
    refine ⟨Or.inr ⟨a.toReal, b.toReal, hra_lt_rb, hloeq, hhieq, hSI⟩, ?_, ?_⟩
    · intro t ht
      change lo l + t * (hi l - lo l) ∈ ({x : ℝ | Fin.snoc l x ∈ Z})
      exact hpar1 t ht
    · intro x hx
      exact hpar2 x hx

end Work.WilG4c
