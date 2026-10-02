import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet_short
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.ccBet_angDouble_of_hard_case

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-!
## The long-arc case of cyclic-order preservation

`Work.LandLeaves.ccBet_angDouble_of_typeSet_short` is the *short-arc* half of the cyclic-order
preservation of the angles of the dynamic rays landing at a repelling periodic point `y` of odd
period `k` of the tricorn `T_c z = z̄² + c`:

> for `a, b, x` in the *type* of `y` (`rayAccum c φ θ = {y}`) with `x` strictly between `a` and `b`
> counterclockwise (`ccBet a b x`), the `2k`-fold angle map `σ = (angDouble)^[2k]`, i.e.
> `σ θ = Int.fract (4^k θ)`, preserves the cyclic order.

This file is the *long-arc* half (the case `1 < 4^k · fract (b - a)`, i.e. the arc `a → b`
wraps under the `4^k`-fold covering of the circle).  The two ingredients of the classical proof
(Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2) are:

* the second return map `τ = (T_c)^[2k]` is a local diffeomorphism at `y`
  (`exists_local_repelling_branch`), hence maps the local picture of the rays landing at `y` to
  itself, preserving their cyclic order;
* the cyclic order of the rays *around* `y` is the cyclic order of their angles, because the rays
  are pairwise disjoint properly embedded arcs from `y` to `∞`.

The second ingredient is the geometric core.  It is only needed when *all three* arcs of the
triple are long; if one of the arcs `fract (x - b)`, `fract (a - x)` is short the short-arc lemma
applies to a cyclic rotation of the triple (`ccBet_angDouble_of_short_gap` below), and if
`fract (b - a)` is short this is the short-arc lemma itself.  The remaining case — all three of
`fract (b - a)`, `fract (x - b)`, `fract (a - x)` exceeding `1/4^k` — is isolated in
`ccBet_angDouble_of_hard_case` (a separate module), where the plane topology of the rays enters.
-/

/-- **Cyclic rotation of `ccBet`.**  `x` lies strictly between `a` and `b` counterclockwise iff
the same holds for any cyclic rotation of the three angles.  (Pure `Int.fract` arithmetic.) -/
theorem ccBet_rot {A B X : ℝ} (h : ccBet A B X) : ccBet B X A := by
  obtain ⟨h1, h2⟩ := h
  have hA : Int.fract (B - A) ≠ 0 := ne_of_gt (lt_trans h1 h2)
  have hAB : Int.fract (A - B) = 1 - Int.fract (B - A) := by
    have h' : A - B = -(B - A) := by ring
    rw [h', Int.fract_neg hA]
  have hXB : Int.fract (X - B) = Int.fract (X - A) - Int.fract (B - A) + 1 := by
    have hsub : X - B = (X - A) - (B - A) := by ring
    rw [hsub]
    have step : Int.fract ((X - A) - (B - A))
        = Int.fract (Int.fract (X - A) - Int.fract (B - A)) := by
      rw [Int.fract_eq_fract]
      refine ⟨⌊X - A⌋ - ⌊B - A⌋, ?_⟩
      have e1 := Int.self_sub_fract (X - A)
      have e2 := Int.self_sub_fract (B - A)
      push_cast
      linarith
    rw [step]
    have hshift : Int.fract (Int.fract (X - A) - Int.fract (B - A) + 1)
        = Int.fract (Int.fract (X - A) - Int.fract (B - A)) := by
      rw [show Int.fract (X - A) - Int.fract (B - A) + 1
            = (Int.fract (X - A) - Int.fract (B - A)) + (1 : ℤ) by push_cast; ring]
      exact Int.fract_add_intCast _ 1
    rw [← hshift, Int.fract_eq_self]
    constructor <;> linarith [Int.fract_lt_one (B - A), Int.fract_nonneg (X - A)]
  rw [ccBet, hAB, hXB]
  constructor <;> linarith [Int.fract_lt_one (B - A)]

/-- **Cyclic rotation of `ccBet`, equivalence form.** -/
theorem ccBet_rot_iff {A B X : ℝ} : ccBet A B X ↔ ccBet B X A :=
  ⟨ccBet_rot, fun h => by
    have := ccBet_rot (ccBet_rot h)
    simpa using this⟩

/-- **The short-arc reductions of the long case.**  If `ccBet a b x` holds and one of the two arcs
`fract (x - b)`, `fract (a - x)` of the triple is short (`≤ 1/4^k`), then the conclusion holds:
the short-arc lemma `ccBet_angDouble_of_typeSet_short` applies to the cyclic rotation `(b, x, a)`
resp. `(x, a, b)` of the triple. -/
theorem ccBet_angDouble_of_short_gap {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x)
    (h : (4 : ℝ) ^ k * Int.fract (x - b) ≤ 1 ∨ (4 : ℝ) ^ k * Int.fract (a - x) ≤ 1) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  rcases h with h | h
  · -- apply the short lemma to the rotation `(b, x, a)`
    have hrot : ccBet b x a := ccBet_rot hab
    have hshort := Work.LandLeaves.ccBet_angDouble_of_typeSet_short hφ hrep
      (a := b) (b := x) (x := a) hb hx ha h hrot
    exact (ccBet_rot_iff).mp ((ccBet_rot_iff).mp hshort)
  · -- apply the short lemma to the rotation `(x, a, b)`
    have hrot : ccBet x a b := ccBet_rot (ccBet_rot hab)
    have hshort := Work.LandLeaves.ccBet_angDouble_of_typeSet_short hφ hrep
      (a := x) (b := a) (x := b) hx ha hb h hrot
    exact (ccBet_rot_iff).mp hshort

/-- **The long case reduces to the hard case.**  If the arc `a → b` is long (`hlong`) and `ccBet a b x`
holds, then the conclusion follows from the "hard case" — the case in which *all three* arcs of the
triple are long — by the short-arc reductions.  This isolates the geometric input: everything except
`ccBet_angDouble_of_hard_case` is pure `Int.fract` arithmetic. -/
theorem ccBet_angDouble_of_long_of_hard_case {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hlong : 1 < (4 : ℝ) ^ k * Int.fract (b - a)) (hab : Work.LandLeaves.ccBet a b x)
    (hhard : 1 < (4 : ℝ) ^ k * Int.fract (b - a) →
      1 < (4 : ℝ) ^ k * Int.fract (x - b) → 1 < (4 : ℝ) ^ k * Int.fract (a - x) →
      Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
        ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x)) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  by_cases hq : (4 : ℝ) ^ k * Int.fract (x - b) ≤ 1
  · exact ccBet_angDouble_of_short_gap hφ hrep ha hb hx hab (Or.inl hq)
  · by_cases hr : (4 : ℝ) ^ k * Int.fract (a - x) ≤ 1
    · exact ccBet_angDouble_of_short_gap hφ hrep ha hb hx hab (Or.inr hr)
    · exact hhard hlong (lt_of_not_ge hq) (lt_of_not_ge hr)

/-- **The requested lemma (long-arc case of cyclic-order preservation).**  If the dynamic rays at
the three angles `a, b, x` all accumulate at the repelling periodic point `y` of odd period `k`,
`x` lies strictly counterclockwise between `a` and `b`, and the arc `a → b` wraps under the
`4^k`-fold covering (`1 < 4^k · fract (b - a)`), then the `2k`-fold angle map preserves the cyclic
order of the triple.

The proof is the reduction `ccBet_angDouble_of_long_of_hard_case` together with the geometric core
`Work.LandLeaves.ccBet_angDouble_of_hard_case` (all three arcs long). -/
theorem ccBet_angDouble_of_typeSet_long {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hlong : 1 < (4 : ℝ) ^ k * Int.fract (b - a)) (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  exact ccBet_angDouble_of_long_of_hard_case hφ hrep ha hb hx hlong hab
    (fun hp hq hr => ccBet_angDouble_of_hard_case hφ hrep ha hb hx hp hq hr hab)

end Work.LandLeaves
