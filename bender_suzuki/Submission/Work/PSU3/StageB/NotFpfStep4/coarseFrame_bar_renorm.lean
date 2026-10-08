import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- Left multiplication by a unit `c` of `E n`, viewed as a monoid endomorphism of the
multiplicative group `Multiplicative (E n)`: `a ↦ c * Multiplicative.toAdd a`.
Composing `bar` with this endomorphism is the renormalisation of the coarse coordinate
`bar` performed in `coarseFrame_bar_renorm`. -/
noncomputable def barScale (n : ℕ) (c : (E n)ˣ) : Multiplicative (E n) →* Multiplicative (E n) where
  toFun a := Multiplicative.ofAdd ((c : E n) * Multiplicative.toAdd a)
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, mul_add, ofAdd_add]

/-- The defining formula of `barScale`, as a `simp` lemma. -/
@[simp] lemma barScale_apply (n : ℕ) (c : (E n)ˣ) (a : Multiplicative (E n)) :
    Multiplicative.toAdd (barScale n c a) = (c : E n) * Multiplicative.toAdd a := rfl

/-- The scalar `c` is nonzero, in the form needed for cancellation. -/
lemma barScale_ne_zero (n : ℕ) (c : (E n)ˣ) : (c : E n) ≠ 0 := Units.ne_zero c

/-- Cancellation of the scalar: `c * (c⁻¹ * t) = t`. -/
lemma barScale_cancel (n : ℕ) (c : (E n)ˣ) (t : E n) :
    (c : E n) * ((c : E n)⁻¹ * t) = t := by
  rw [← mul_assoc, mul_inv_cancel₀ (barScale_ne_zero n c), one_mul]

/-- `barScale c` is injective, because `c` is invertible. -/
lemma barScale_injective (n : ℕ) (c : (E n)ˣ) : Function.Injective (barScale n c) := by
  intro a a' ha
  apply Multiplicative.ext
  have h := congrArg Multiplicative.toAdd ha
  simp only [barScale_apply] at h
  exact mul_left_cancel₀ (barScale_ne_zero n c) h

theorem coarseFrame_bar_renorm {G : Type} [Group G] (H Q : Subgroup G) (t : G) {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) (c : (Work.PSU3.E n)ˣ) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n,
      (∀ x : ↥Q, Multiplicative.toAdd (fr'.bar x)
          = (c : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x)) ∧
      fr'.Q0 = fr.Q0 ∧ fr'.KW = fr.KW ∧ ((fr'.ζ : G) = (fr.ζ : G)) := by
  classical
  -- The renormalised coordinate: `bar' = c · bar`.
  let b : ↥Q →* Multiplicative (E n) := (barScale n c).comp fr.bar
  have hb : ∀ x : ↥Q, Multiplicative.toAdd (b x)
      = (c : E n) * Multiplicative.toAdd (fr.bar x) := by
    intro x
    simp [b]
  refine ⟨{ fr with
    bar := b
    bar_surjective := ?_
    bar_eq_one_iff := ?_
    act_bar := ?_ }, hb, rfl, rfl, rfl⟩
  · -- `bar'` is still surjective: `c` is invertible.
    intro y
    obtain ⟨x, hx⟩ := fr.bar_surjective
      (Multiplicative.ofAdd ((c : E n)⁻¹ * Multiplicative.toAdd y))
    refine ⟨x, ?_⟩
    apply Multiplicative.ext
    rw [hb x, hx, toAdd_ofAdd]
    exact barScale_cancel n c (Multiplicative.toAdd y)
  · -- the kernel of `bar'` is still `Q₀`.
    intro x
    rw [← toAdd_eq_zero, hb x]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 (barScale_ne_zero n c)
      · exact (fr.bar_eq_one_iff x).mp (toAdd_eq_zero.mp h0)
    · intro hx
      rw [(fr.bar_eq_one_iff x).mpr hx, toAdd_one, mul_zero]
  · -- equivariance of `bar'` under `KW`: the scalar commutes with `κ d`.
    intro d x y hy
    rw [hb y, hb x, fr.act_bar d x y hy]
    exact mul_left_comm ((c : E n)) ((fr.κ d : (E n)ˣ) : E n)
      (Multiplicative.toAdd (fr.bar x))

end Work.PSU3.StageB.NotFpfStep4
