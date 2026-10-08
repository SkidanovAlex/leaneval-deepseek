import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- Elementary consequences of an alternating biadditive map `c : V → V → W` where `V` is
a module over `ZMod 2` (so `x + x = 0` for all `x`). Taking `a = b = 0` in the
biadditivity of the first slot shows `c 0 y = 0`, and symmetrically `c x 0 = 0`; from
`c (x + x) y = c x y + c x y` and `x + x = 0` one gets `c x y + c x y = 0` (so every value
of `c` is `2`-torsion), which in turn gives the skew-symmetry `c y x = - c x y` via
`halt`, and the expansion of `c (P1 + Q1) (P2 + Q2)` uses this torsion relation to cancel
the doubled terms. -/
theorem cob_facts {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    (c : V → V → W)
    (hc1 : ∀ a b d : V, c (a + b) d = c a d + c b d)
    (hc2 : ∀ a b d : V, c a (b + d) = c a b + c a d)
    (halt : ∀ a : V, c a a = 0) :
    (∀ y : V, c 0 y = 0) ∧ (∀ x : V, c x 0 = 0) ∧
    (∀ x y : V, c y x = - c x y) ∧
    (∀ x y : V, c x y + c x y = 0) ∧
    (∀ (r s : ZMod 2) (x : V), c (r • x) (s • x) = 0) ∧
    (∀ P1 Q1 P2 Q2 : V, c (P1 + Q1) (P2 + Q2) + c P1 P2 + c Q1 Q2 = c P1 Q2 + c Q1 P2) := by
  -- every element of `V` is `2`-torsion, because `V` is a module over `ZMod 2`
  have hz2 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  have hxx : ∀ x : V, x + x = 0 := by
    intro x
    have h2 : (2 : ZMod 2) = 0 := by decide
    have : x + x = (2 : ZMod 2) • x := by rw [two_smul]
    rw [this, h2, zero_smul]
  -- `c 0 y = 0`
  have h0 : ∀ y : V, c 0 y = 0 := by
    intro y
    have h := hc1 0 0 y
    rw [zero_add] at h
    have key : c 0 y + 0 = c 0 y + c 0 y := by rw [add_zero]; exact h
    exact (add_left_cancel key).symm
  -- `c x 0 = 0`
  have hz0 : ∀ x : V, c x 0 = 0 := by
    intro x
    have h := hc2 x 0 0
    rw [zero_add] at h
    have key : c x 0 + 0 = c x 0 + c x 0 := by rw [add_zero]; exact h
    exact (add_left_cancel key).symm
  -- all values of `c` are `2`-torsion
  have h2t : ∀ x y : V, c x y + c x y = 0 := by
    intro x y
    have h := hc1 x x y
    rw [hxx x, h0 y] at h
    exact h.symm
  -- skew-symmetry
  have hskew : ∀ x y : V, c y x = - c x y := by
    intro x y
    have h := halt (x + y)
    rw [hc2, hc1, hc1] at h
    rw [halt x, halt y] at h
    simp at h
    exact eq_neg_of_add_eq_zero_left h
  -- scalar multiples vanish in pairs
  have hscal : ∀ (r s : ZMod 2) (x : V), c (r • x) (s • x) = 0 := by
    intro r s x
    rcases hz2 r with h | h <;> rcases hz2 s with h' | h' <;>
      simp [h, h', h0, hz0, halt]
  -- expansion of the "quadratic" term
  have hquad : ∀ P1 Q1 P2 Q2 : V,
      c (P1 + Q1) (P2 + Q2) + c P1 P2 + c Q1 Q2 = c P1 Q2 + c Q1 P2 := by
    intro P1 Q1 P2 Q2
    have hexp : c (P1 + Q1) (P2 + Q2) = (c P1 P2 + c Q1 P2) + (c P1 Q2 + c Q1 Q2) := by
      rw [hc2, hc1, hc1]
    rw [hexp]
    have key : (c P1 P2 + c Q1 P2) + (c P1 Q2 + c Q1 Q2) + c P1 P2 + c Q1 Q2
        = (c P1 P2 + c P1 P2) + (c Q1 Q2 + c Q1 Q2) + (c Q1 P2 + c P1 Q2) := by abel
    rw [key, h2t P1 P2, h2t Q1 Q2]
    abel
  exact ⟨h0, hz0, hskew, h2t, hscal, hquad⟩

end Work.Higman
