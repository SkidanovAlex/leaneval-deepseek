import Mathlib
import Submission.Work.SSGRoute.gradedPiece_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The second graded piece of the `p = 2` correction

The descent along the refined filtration `F(n)^{(1,1)} ⊃ F(n)^{(2,1)} ⊃ F(n)^{(2,2)} ⊃ …` needs, at
each step `σ`, the statement

> `(E_σ)^δ ⊆ (1 - δ)·Q_{σ+1}`,

where `E_σ = F(n)^{(σ)}/F(n)^{(σ)+1}` is the graded piece and `Q_{σ+1} = F(n)/F(n)^{(σ)+1}`.
For the second step, `σ = (2,1)`, the graded piece is again the degree-1 piece
`E_{(2,1)} = F(n)^{(2,1)}/F(n)^{(2,2)} ≅ F(n)/F(n)^2[F(n),F(n)]` (the `2`-powers), while the
*ambient* quotient is `Q_{(2,2)} = F(n)/F(n)^{(2,2)}`, which for the free `G`-operator group is the
"`ℤ/4`-model": in the coordinates of the free basis it behaves like
`(Fin n × G → ℤ/4)` with the `δ`-action permuting the coordinates.

This file proves that model statement: every `δ`-fixed `2`-torsion vector of
`(Fin n × G → ℤ/4)` is a `δ`-difference.  This is `E_{(2,1)}^δ ⊆ (1-δ)Q_{(2,2)}` at the level of
coordinates; the passage to the honest quotient uses the identification
`F(n)/F(n)^{(2,2)} ≅ (Fin n × G → ℤ/4)` (equivalently `F(n)^{(2,2)} = [F(n),F(n)]·F(n)^{(3,1)}`
together with `F(n)/[F(n),F(n)]F(n)^4 ≅ (ℤ/4)^{Fin n × G}`).

The genuinely *quadratic* phenomenon first appears one step further, in the degree-2 piece
`E_{(2,2)} = F(n)^{(2,2)}/F(n)^{(3,1)}`: there the class of `A·(δA)` in the graded piece is
`Q(ā) = (1+δ)T(ā) + ā ∧ (δ•ā)` — a quadratic form in the exponent vector `ā` of `A` — and a
`δ`-fixed exponent vector satisfies `ā ∧ δ•ā = ā ∧ ā = 0` in characteristic `2`, which is why the
`(1+δ)`-part is all that survives.
-/

namespace Work.SSGRoute

/-- The `δ`-action on `Fin n × G → R` by permuting coordinates, `(δ • f) x = f (x.1, δ * x.2)`
(this is the regular action used for the free `G`-operator group; note `δ * δ = 1`). -/
def coordPerm (G : Type*) [Group G] (n : ℕ) (R : Type*) [AddCommGroup R] (δ : G) :
    (Fin n × G → R) →+ (Fin n × G → R) where
  toFun f := fun x => f (x.1, δ * x.2)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coordPerm_apply (G : Type*) [Group G] (n : ℕ) (R : Type*) [AddCommGroup R]
    (δ : G) (f : Fin n × G → R) (x : Fin n × G) :
    coordPerm G n R δ f x = f (x.1, δ * x.2) := rfl

/-- Twice the coordinate function: the image of the degree-1 piece (the `2`-powers) in the
`ℤ/4`-model. -/
def twoCoord {G : Type*} [Group G] {n : ℕ} (f : Fin n × G → ZMod 2) : Fin n × G → ZMod 4 :=
  fun x => 2 * (f x).val

/-- **Second graded piece.**  Every `δ`-fixed `2`-torsion vector of the `ℤ/4`-model is a
`δ`-difference: for `v : Fin n × G → ZMod 2` with `δ • v = v` there is
`a : Fin n × G → ZMod 4` with `δ • a - a = twoCoord v`.

This is the model-level form of `(E_{(2,1)})^δ ⊆ (1-δ)·Q_{(2,2)}`. -/
theorem zmod4_two_torsion_fixed_is_delta_difference (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (v : Fin n × G → ZMod 2)
    (hv : coordPerm G n (ZMod 2) δ v = v) :
    ∃ a : Fin n × G → ZMod 4,
      coordPerm G n (ZMod 4) δ a - a = twoCoord v := by
  classical
  -- transversal by a linear order on the finite type
  set e : Fin n × G ≃ Fin (Fintype.card (Fin n × G)) := Fintype.equivFin _ with he
  set a : Fin n × G → ZMod 4 :=
    fun x => if e x ≤ e (x.1, δ * x.2) then 0 else twoCoord v x with ha
  have hpair : ∀ x : Fin n × G, (x.1, δ * x.2) ≠ x := by
    intro x h
    have h2 : δ * x.2 = x.2 := congrArg Prod.snd h
    exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))
  have hdelta : ∀ x : Fin n × G, (x.1, δ * (δ * x.2)) = x := by
    intro x
    rw [← mul_assoc, hδ, one_mul]
  have hv' : ∀ x : Fin n × G, v (x.1, δ * x.2) = v x := by
    intro x
    have h2 := congrFun hv x
    simpa [coordPerm_apply] using h2
  refine ⟨a, ?_⟩
  funext x
  rw [Pi.sub_apply, coordPerm_apply]
  by_cases hc : e x ≤ e (x.1, δ * x.2)
  · have hcy : ¬ e (x.1, δ * x.2) ≤ e x := by
      intro hle
      exact hpair x (e.injective (le_antisymm hc hle).symm)
    have h3 : a x = 0 := by simp only [ha]; exact if_pos hc
    have h4 : a (x.1, δ * x.2) = twoCoord v (x.1, δ * x.2) := by
      simp only [ha, hdelta x]
      exact if_neg hcy
    rw [h3, h4, sub_zero]
    simp only [twoCoord]
    rw [hv' x]
  · have hcy : e (x.1, δ * x.2) ≤ e x := le_of_lt (lt_of_not_ge hc)
    have h3 : a x = twoCoord v x := by simp only [ha]; exact if_neg hc
    have h4 : a (x.1, δ * x.2) = 0 := by
      simp only [ha, hdelta x]
      exact if_pos hcy
    have hneg2 : ∀ m : ZMod 4, -(2 * m) = 2 * m := by decide
    rw [h3, h4]
    show (0 : ZMod 4) - twoCoord v x = twoCoord v x
    rw [zero_sub]
    exact hneg2 _

end Work.SSGRoute
