import Mathlib
import Submission.Work.SSGRoute.gradedPiece_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quadratic form of the degree-2 graded piece (the `p = 2` correction)

At `τ = (2,2)` the graded piece `E_{(2,2)} = F(n)^{(2,2)}/F(n)^{(3,1)}` is the *commutator*
piece, and the class of `A · (δA)` there is a **quadratic form** in the exponent vector `ā` of the
word `A`, namely

  `Q(ā) = (1+δ)·T(ā) + ā ∧ (δ•ā)`,

where `T(ā) = Σ_{i<j} e_{a_i} ∧ e_{a_j}` is the "half-square" of the word (the class of the word
`A` in `γ₂/γ₃`), and `ā ∧ (δ•ā)` is the "cross term" between the word and its `δ`-image.  When the
exponent vector is `δ`-invariant — which is exactly the condition `a·(δ•a) = 1` read in the
abelianization `F(n)/F(n)^2` — the cross term vanishes in characteristic `2`, because

  `ā ∧ (δ•ā) = ā ∧ ā = 0`.

This file isolates that cancellation, which is the reason the "orbit-pair" coefficients of the
quadratic form vanish at `p = 2`.  The identification of the class of `A·(δA)` with
`(1+δ)T(ā) + ā∧δ•ā` itself is the Prop. 5 (graded-piece) input and is not needed here.
-/

namespace Work.SSGRoute

/-- The alternating pairing `v ∧ w` on coordinate vectors, evaluated on an ordered pair. -/
def wedgePair {G : Type*} [Group G] {n : ℕ} (v w : Fin n × G → ZMod 2) :
    (Fin n × G) × (Fin n × G) → ZMod 2 :=
  fun p => v p.1 * w p.2 + v p.2 * w p.1

/-- **The cross term of a `δ`-fixed exponent vector vanishes.** -/
theorem wedgePair_coordPerm_eq_zero (G : Type*) [Group G] (n : ℕ) (δ : G)
    (v : Fin n × G → ZMod 2) (hv : coordPerm G n (ZMod 2) δ v = v) :
    wedgePair v (coordPerm G n (ZMod 2) δ v) = 0 := by
  have hx : ∀ x : Fin n × G, v (x.1, δ * x.2) = v x := by
    intro x
    have h := congrFun hv x
    simpa [coordPerm_apply] using h
  funext p
  simp only [wedgePair, coordPerm_apply, Pi.zero_apply]
  rw [hx p.2, hx p.1]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hzero : v p.1 * v p.2 + v p.2 * v p.1 = 0 := by
    rw [mul_comm (v p.2) (v p.1), ← two_mul, h2, zero_mul]
  exact hzero

end Work.SSGRoute
