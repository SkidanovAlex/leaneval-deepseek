import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.InArcHard.ccBet_angDouble_dichotomy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.InArcHard

/-- `ccBet` is antisymmetric in its first two arguments: the two orientations of a non-degenerate
triple are mutually exclusive (so a triple cannot be both in counterclockwise order and in
clockwise order).  Pure `Int.fract` arithmetic. -/
private theorem ccBet_not_swap_aux {A B X : ℝ} (h : Work.LandLeaves.ccBet A B X) :
    ¬ Work.LandLeaves.ccBet B A X := by
  obtain ⟨h1, h2⟩ := h
  intro h'
  obtain ⟨-, h2'⟩ := h'
  have hp : Int.fract (B - A) ≠ 0 := ne_of_gt (lt_trans h1 h2)
  have hAB : Int.fract (A - B) = 1 - Int.fract (B - A) := by
    rw [show A - B = -(B - A) by ring, Work.LandLeaves.fract_neg_eq hp]
  have hXB : Int.fract (X - B) = Int.fract (X - A) - Int.fract (B - A) + 1 :=
    Work.LandLeaves.fract_sub_fract_of_lt h2
  rw [hXB, hAB] at h2'
  linarith

/-- **Cyclic-order preservation of the second-return angle map at a repelling periodic point**
(Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2, in the tricorn setting).

Let `T_c z = z̄² + c` be the tricorn, `φ` a Böttcher coordinate, and `y` a repelling periodic
point of period `k` (`Work.Landing.IsRepelling c k y`).  The `2k`-fold angle map
`σ = (angDouble)^[2k] = θ ↦ Int.fract (4^k θ)` — the angle map of the holomorphic second return
map `τ = (T_c)^{2k}` — **preserves the cyclic betweenness** `ccBet` on the *type* of `y`: if the
dynamic rays at three angles `a`, `b`, `x` all accumulate at the single point `y` and `x` lies
strictly counterclockwise between `a` and `b`, then the same holds for the images.

Structure of the proof (the classical argument of Goldberg–Milnor, transported to the tricorn):

* **The sign-free sector transfer** (`Submission.Work.LandLeaves.InArcHard.sectorTransfer`, via
  `ccBet_angDouble_of_sectorTransfer`): near `y`, `τ` carries the far side of a co-landing pair
  into the far side of the pair of the image angles.  This is the whole geometric content — it
  never asks *which* of the two sectors at `y` is the far one, only that the orientation-preserving
  local biholomorphism `τ` matches the far sectors;
* the angle–side dictionary turns the transfer into the cyclic-order preservation: if `R_x` is in
  the far side of `(a,b)` (`paramRay_subset_pairSide_of_ccBet`), then the tail of `R_x` is carried
  into the far side of `(σa, σb)`, hence the whole image ray `R_{σx} = τ (R_x)` lies there (it is
  preconnected and disjoint from the pair curve), and the converse dictionary
  (`ccBet_of_paramRay_subset_pairSide`) reads off `ccBet (σa) (σb) (σx)`.

The equivalent *dichotomy* form (one single orientation choice valid for every triple of the
type) is `ccBet_angDouble_dichotomy`; here we exhibit the target as its first branch and rule out
the second by antisymmetry. -/
theorem type_ccBet {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  have hfwd : Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) :=
    ccBet_angDouble_of_sectorTransfer hφ hrep ha hb hx hab
  rcases ccBet_angDouble_dichotomy hφ hrep with h | h
  · exact h a b x ha hb hx hab
  · exact absurd hfwd (ccBet_not_swap_aux (h a b x ha hb hx hab))

end Work.LandLeaves.InArcHard
