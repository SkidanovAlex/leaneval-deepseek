import Mathlib

namespace Work.WilE4.CAD

/-!
## Circle integral of a multiset of `(z - a)⁻¹`

The main result `circleIntegral_multiset_sum_inv` computes
`∮ z in C(c, R), ∑_{a ∈ m} (z - a)⁻¹` for a multiset `m` of complex numbers none of which lies on
the circle: it is `2πi` times the number of elements of `m` inside the circle.

The proof is the elementary residue computation together with the linearity of the circle integral
over (multi)sums.  The auxiliary lemmas below are kept in a private namespace so that they cannot
clash with other material in `Work.WilE4.CAD`.
-/

namespace CircleInvAux

/-- The single-pole integral when the pole lies inside the circle. -/
theorem circleIntegral_inv_sub_of_lt {a c : ℂ} {R : ℝ} (h : dist a c < R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 2 * Real.pi * Complex.I :=
  circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball.mpr h)

/-- The single-pole integral when the pole lies outside the circle: the integrand is holomorphic on
the closed disk, so the integral vanishes by Cauchy–Goursat. -/
theorem circleIntegral_inv_sub_of_gt {a c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : R < dist a c) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty ?_ ?_
  · refine (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_
    show z - a ≠ 0
    intro hza
    have hz' : dist z c ≤ R := Metric.mem_closedBall.mp hz
    have : z = a := sub_eq_zero.mp hza
    rw [this] at hz'
    linarith
  · intro z hz
    refine (differentiableAt_id.sub_const a).inv ?_
    show z - a ≠ 0
    intro hza
    have hz' : dist z c < R := Metric.mem_ball.mp hz.1
    have : z = a := sub_eq_zero.mp hza
    rw [this] at hz'
    linarith

/-- `(z - a)⁻¹` is circle integrable whenever `a` is not on the circle. -/
theorem circleIntegrable_inv_sub (a c : ℂ) {R : ℝ} (hR : 0 ≤ R) (ha : dist a c ≠ R) :
    CircleIntegrable (fun z => (z - a)⁻¹) c R :=
  ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => by
    show z - a ≠ 0
    intro hza
    have hz' : dist z c = R := Metric.mem_sphere.mp hz
    have : z = a := sub_eq_zero.mp hza
    rw [this] at hz'
    exact ha hz').circleIntegrable hR

/-- A multiset sum of functions `(z - a)⁻¹` is circle integrable as soon as none of the `a` lies on
the circle. -/
theorem circleIntegrable_multiset_sum_inv (m : Multiset ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ m, dist a c ≠ R) :
    CircleIntegrable (fun z => (m.map (fun a => (z - a)⁻¹)).sum) c R := by
  induction m using Multiset.induction_on with
  | empty =>
      have hz : (fun z : ℂ => ((0 : Multiset ℂ).map (fun a => (z - a)⁻¹)).sum)
          = fun _ => (0 : ℂ) := by funext z; simp
      rw [hz]
      exact (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ))
        (Metric.sphere c R)).circleIntegrable hR
  | cons a s ih =>
      have ha : dist a c ≠ R := h a (Multiset.mem_cons_self a s)
      have hs : ∀ b ∈ s, dist b c ≠ R := fun b hb => h b (Multiset.mem_cons_of_mem hb)
      have hfun : (fun z : ℂ => ((a ::ₘ s).map (fun a => (z - a)⁻¹)).sum)
          = (fun z => (z - a)⁻¹) + (fun z => (s.map (fun a => (z - a)⁻¹)).sum) := by
        funext z; simp [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]
      exact (circleIntegrable_inv_sub a c hR ha).add (ih hs)

/-- Linearity of the circle integral over a multiset sum. -/
theorem circleIntegral_multiset_sum_inv_eq (m : Multiset ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ m, dist a c ≠ R) :
    (∮ z in C(c, R), (m.map (fun a => (z - a)⁻¹)).sum)
      = (m.map (fun a => ∮ z in C(c, R), (z - a)⁻¹)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a s ih =>
      have ha : dist a c ≠ R := h a (Multiset.mem_cons_self a s)
      have hs : ∀ b ∈ s, dist b c ≠ R := fun b hb => h b (Multiset.mem_cons_of_mem hb)
      have hfun : (fun z : ℂ => ((a ::ₘ s).map (fun a => (z - a)⁻¹)).sum)
          = (fun z => (z - a)⁻¹) + (fun z => (s.map (fun a => (z - a)⁻¹)).sum) := by
        funext z; simp [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]
      change circleIntegral (fun z => (z - a)⁻¹ + (s.map (fun a => (z - a)⁻¹)).sum) c R
        = (Multiset.map (fun a => ∮ z in C(c, R), (z - a)⁻¹) (a ::ₘ s)).sum
      rw [circleIntegral.integral_add (circleIntegrable_inv_sub a c hR ha)
        (circleIntegrable_multiset_sum_inv s c hR hs), ih hs]
      simp [Multiset.map_cons, Multiset.sum_cons]

/-- The abstract counting identity: a multiset sum of `x` over the points satisfying `p` and `0`
elsewhere is `x` times the number of points satisfying `p`. -/
theorem multiset_sum_ite_dist (m : Multiset ℂ) (c : ℂ) (R : ℝ) (x : ℂ) :
    (m.map (fun a => if dist a c < R then x else 0)).sum
      = x * ((m.filter (fun a => dist a c < R)).card : ℂ) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.filter_cons, Multiset.card_add]
      split_ifs with hp
      · rw [Multiset.card_singleton, Nat.cast_add, Nat.cast_one]; ring
      · rw [Multiset.card_zero, Nat.cast_add, Nat.cast_zero]; ring

end CircleInvAux

theorem circleIntegral_multiset_sum_inv (m : Multiset ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (h : ∀ a ∈ m, dist a c ≠ R) :
    (∮ z in C(c, R), (m.map (fun a => (z - a)⁻¹)).sum)
      = 2 * Real.pi * Complex.I * ((m.filter (fun a => dist a c < R)).card : ℂ) := by
  rw [CircleInvAux.circleIntegral_multiset_sum_inv_eq m c hR.le h]
  have hsingle : ∀ a ∈ m, (∮ z in C(c, R), (z - a)⁻¹)
      = if dist a c < R then 2 * Real.pi * Complex.I else 0 := by
    intro a ha
    by_cases hlt : dist a c < R
    · rw [if_pos hlt, CircleInvAux.circleIntegral_inv_sub_of_lt hlt]
    · rw [if_neg hlt, CircleInvAux.circleIntegral_inv_sub_of_gt hR.le
        (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm (h a ha)))]
  rw [Multiset.map_congr rfl hsingle,
    CircleInvAux.multiset_sum_ite_dist m c R (2 * Real.pi * Complex.I)]

end Work.WilE4.CAD
