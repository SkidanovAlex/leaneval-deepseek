import Mathlib
import Submission.Work.Smooth.JordanSeparation.JumpOnRegular
import Submission.Work.Smooth.JordanSeparation.Separation
import Submission.Work.Smooth.JordanSeparation.frontier_eq_trace

/-!
# Simple (not necessarily immersed) `C¹` closed curves: at least two components, and the exact
reduction to the remaining half

Everything in this chapter up to now assumed that the curve is an **immersion**.  The index jump —
the engine of the *at least two components* half — only needs the curve to be regular at a single
point, and a simple closed curve always has one:

* `exists_deriv_ne_zero_of_isSimple` — a `C¹` simple closed curve has some regular parameter;
* `exists_two_components_of_isSimple` — hence its complement has **at least two** components;
* `jordanSeparation_of_atMostTwo` — consequently **the full Jordan separation theorem for a `C¹`
  simple closed curve follows from the single statement that its complement has at most two
  components** (`atMostTwo_connectedComponentIn_of_isSimple`), which is the one remaining half and
  is *not* proved here (nor in Mathlib);
* the values of the index on the two sides, also conditional only on that one statement.

The reason the *at most two* half cannot be obtained by the present method is recorded in
`Submission/Work/Smooth/JordanSeparation/README.md`: the regular-neighbourhood construction rests
on the injectivity of the offset map of a transverse unit field, and at a cusp (`deriv c.γ t = 0`,
e.g. `t ↦ (t², t³)`, which is `C¹` — indeed polynomial — and simple) that map provably folds onto
the trace, so no offset-map neighbourhood of the trace exists.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **A `C¹` simple closed curve has a regular parameter.**  Otherwise `deriv c.γ` would vanish
identically, `c` would be constant, and a constant curve is not injective on a period. -/
theorem exists_deriv_ne_zero_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple) :
    ∃ a : ℝ, deriv c.γ a ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hconst : ∀ x y : ℝ, c.γ x = c.γ y :=
    is_const_of_deriv_eq_zero c.differentiable (fun x => hcon x)
  have hmem0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl 0, by positivity⟩
  have hmemπ : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have := hs hmem0 hmemπ (hconst 0 Real.pi)
  linarith [Real.pi_pos]

/-- **At least two components, for any `C¹` simple closed curve.**  Shifting the parameter to a
regular point and applying `ind_jump_of_deriv_ne_zero` to the shifted curve (the index being
invariant under the shift, `ind_shiftCurve`) produces two points off the trace with different
indices; by `ind_const_on_preconnected` they lie in different components of the complement. -/
theorem exists_two_components_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple) :
    ∃ x y : ℂ, x ∉ c.trace ∧ y ∉ c.trace ∧
      connectedComponentIn c.traceᶜ x ≠ connectedComponentIn c.traceᶜ y := by
  obtain ⟨a, ha⟩ := exists_deriv_ne_zero_of_isSimple c hs
  set c' : SmoothPlaneCurve := shiftCurve c a with hc'
  have hreg : deriv c'.γ 0 ≠ 0 := by rw [hc', deriv_shiftCurve, zero_add]; exact ha
  have hsimple : c'.toPlaneCurve.IsSimple := by rw [hc']; exact shiftCurve_isSimple c a hs
  obtain ⟨δ, hδ, hjump⟩ := ind_jump_of_deriv_ne_zero c' hreg hsimple
  set s : ℝ := δ / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsd : s < δ := by rw [hsdef]; linarith
  obtain ⟨hpos, hneg, hsub⟩ := hjump s hs0 hsd
  rw [hc'] at hpos hneg hsub
  simp only [shiftCurve_apply, zero_add, normalField_shiftCurve, shiftCurve_trace] at hpos hneg hsub
  have htrace : c'.trace = c.trace := by rw [hc']; exact shiftCurve_trace c a
  have e1 : ind c' (c.γ a + (s : ℂ) * normalField c a) = ind c (c.γ a + (s : ℂ) * normalField c a) :=
    ind_shiftCurve c a (by rw [← htrace, hc'] at hpos ⊢; exact hpos)
  have e2 : ind c' (c.γ a - (s : ℂ) * normalField c a) = ind c (c.γ a - (s : ℂ) * normalField c a) :=
    ind_shiftCurve c a (by rw [← htrace, hc'] at hneg ⊢; exact hneg)
  rw [e1, e2] at hsub
  refine ⟨c.γ a + (s : ℂ) * normalField c a, c.γ a - (s : ℂ) * normalField c a,
    hpos, hneg, ?_⟩
  intro heq
  have hpre : IsPreconnected
      (connectedComponentIn c.traceᶜ (c.γ a + (s : ℂ) * normalField c a)) :=
    isPreconnected_connectedComponentIn
  have hsub' : connectedComponentIn c.traceᶜ (c.γ a + (s : ℂ) * normalField c a) ⊆ c.traceᶜ :=
    connectedComponentIn_subset _ _
  have hmem1 : c.γ a + (s : ℂ) * normalField c a ∈
      connectedComponentIn c.traceᶜ (c.γ a + (s : ℂ) * normalField c a) :=
    mem_connectedComponentIn hpos
  have hmem2 : c.γ a - (s : ℂ) * normalField c a ∈
      connectedComponentIn c.traceᶜ (c.γ a + (s : ℂ) * normalField c a) := by
    rw [heq]
    exact mem_connectedComponentIn hneg
  have hc := ind_const_on_preconnected c hpre hsub' hmem1 hmem2
  rw [hc] at hsub
  linarith

/-- **The exact reduction.**  *The Jordan separation theorem for a `C¹` simple closed plane curve
follows from the single statement that its complement has at most two components.*

Given `atMostTwo_connectedComponentIn_of_isSimple` (of any three points off the trace, two lie in
the same component of the complement — the statement reviewed as the remaining half), the
complement is the disjoint union of the two sides. -/
theorem jordanSeparation_of_atMostTwo (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (hatMost : ∀ x y z : ℂ, x ∉ c.trace → y ∉ c.trace → z ∉ c.trace →
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
        connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
        connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z) :
    Nonempty (PlaneSeparation c.toPlaneCurve) :=
  nonempty_planeSeparation c.toPlaneCurve hs hatMost (exists_two_components_of_isSimple c hs)

/-- **The index vanishes on the unbounded side**, for any Jordan separation of a `C¹` simple
closed curve (no immersion, indeed no *at most two components* needed: the unbounded side is
unbounded, and the index is constant on preconnected sets and vanishes at infinity). -/
theorem ind_eq_zero_of_mem_U_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∈ S.U) : ind c x = 0 := by
  refine ind_eq_zero_of_unbounded c S.preconn_U ?_ ?_ x hx
  · intro z hz
    rw [← S.union_eq]; exact Or.inl hz
  · intro R
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp S.bounded_V
    obtain ⟨z, hz, hzR⟩ := exists_norm_gt_of_notMem_trace c.toPlaneCurve (max R r)
    have hz' : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hz
    rcases hz' with h | h
    · exact absurd hzR (not_lt.mpr (le_trans (hcon z h) (le_max_left R r)))
    · have := hr h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd hzR (not_lt.mpr (le_trans this (le_max_right R r)))

/-- **The index has modulus `1` on the bounded side**, for any Jordan separation of a `C¹` simple
closed curve (the index jump is applied at a regular point, obtained by shifting the parameter; no
immersion and no *at most two components* needed). -/
theorem ind_abs_eq_one_of_mem_V_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {y : ℂ} (hy : y ∈ S.V) : |ind c y| = 1 := by
  obtain ⟨a, ha⟩ := exists_deriv_ne_zero_of_isSimple c hs
  set c' : SmoothPlaneCurve := shiftCurve c a with hc'
  have hreg : deriv c'.γ 0 ≠ 0 := by rw [hc', deriv_shiftCurve, zero_add]; exact ha
  have hsimple : c'.toPlaneCurve.IsSimple := by rw [hc']; exact shiftCurve_isSimple c a hs
  obtain ⟨δ, hδ, hjump⟩ := ind_jump_of_deriv_ne_zero c' hreg hsimple
  set s : ℝ := δ / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsd : s < δ := by rw [hsdef]; linarith
  obtain ⟨hpos, hneg, hsub⟩ := hjump s hs0 hsd
  rw [hc'] at hpos hneg hsub
  simp only [shiftCurve_apply, zero_add, normalField_shiftCurve, shiftCurve_trace] at hpos hneg hsub
  set xp : ℂ := c.γ a + (s : ℂ) * normalField c a with hxp
  set xm : ℂ := c.γ a - (s : ℂ) * normalField c a with hxm
  have hxp' : xp ∉ c.trace := by rw [hxp]; exact hpos
  have hxm' : xm ∉ c.trace := by rw [hxm]; exact hneg
  have ex1 : ind c' xp = ind c xp := ind_shiftCurve c a (x := xp) hxp'
  have ex2 : ind c' xm = ind c xm := ind_shiftCurve c a (x := xm) hxm'

  rw [ex1, ex2] at hsub
  have hne : ind c xp ≠ ind c xm := by
    intro h; rw [h] at hsub; omega
  have hmem : ∀ z : ℂ, z ∉ c.trace → z ∈ S.U ∪ S.V := fun z hz => by
    rw [S.union_eq]; exact hz
  have hzero : ∀ z ∈ S.U, ind c z = 0 := fun z hz => ind_eq_zero_of_mem_U_of_isSimple c hs (S := S) hz
  have hconstV : ∀ z₁ ∈ S.V, ∀ z₂ ∈ S.V, ind c z₁ = ind c z₂ :=
    fun z₁ h₁ z₂ h₂ => ind_const_on_preconnected c S.preconn_V (fun w hw => by
      rw [← S.union_eq]; exact Or.inr hw) h₁ h₂
  have key : ind c y = 1 ∨ ind c y = -1 := by
    have hnotbothV : ¬ (xp ∈ S.V ∧ xm ∈ S.V) := by
      rintro ⟨h1, h2⟩
      exact hne (hconstV _ h1 _ h2)
    have hnotbothU : ¬ (xp ∈ S.U ∧ xm ∈ S.U) := by
      rintro ⟨h1, h2⟩
      exact hne (by rw [hzero _ h1, hzero _ h2])
    have h1 := hmem _ hxp'
    have h2 := hmem _ hxm'
    rcases h1 with h1U | h1V
    · have h2V : xm ∈ S.V := by
        rcases h2 with h | h
        · exact absurd ⟨h1U, h⟩ hnotbothU
        · exact h
      have hxneg : ind c xm = -1 := by
        have hx0 : ind c xp = 0 := hzero _ h1U
        rw [hx0] at hsub; omega
      rw [hconstV y hy _ h2V, hxneg]; exact Or.inr rfl
    · have h2U : xm ∈ S.U := by
        rcases h2 with h | h
        · exact h
        · exact absurd ⟨h1V, h⟩ hnotbothV
      have hxpos : ind c xp = 1 := by
        have hx0 : ind c xm = 0 := hzero _ h2U
        rw [hx0] at hsub; omega
      rw [hconstV y hy _ h1V, hxpos]; exact Or.inl rfl
  rcases key with h | h <;> rw [h] <;> norm_num

/-- Two points of the same preconnected subset of the complement have the same component. -/
theorem connectedComponentIn_eq_of_same_preconnected {c : PlaneCurve} {P : Set ℂ}
    (hP : IsPreconnected P) (hPc : P ⊆ c.traceᶜ) {a b : ℂ} (ha : a ∈ P) (hb : b ∈ P) :
    connectedComponentIn c.traceᶜ a = connectedComponentIn c.traceᶜ b :=
  connectedComponentIn_eq (hP.subset_connectedComponentIn ha hPc hb)

/-- **At most two components from a two-element preconnected cover.**

It suffices, for the *at most two components* half, to exhibit **two preconnected sets covering the
complement of the trace**: each lies in a component of the complement, so every point off the trace
lies in one of (at most) two components.  This is the sharpest form of the remaining obligation: a
proof only has to produce the two "sides" as preconnected sets. -/
theorem atMostTwo_of_two_preconnected_cover (c : PlaneCurve) {P Q : Set ℂ}
    (hP : IsPreconnected P) (hQ : IsPreconnected Q) (hPc : P ⊆ c.traceᶜ) (hQc : Q ⊆ c.traceᶜ)
    (hcover : c.traceᶜ ⊆ P ∪ Q) {x y z : ℂ} (hx : x ∉ c.trace) (hy : y ∉ c.trace)
    (hz : z ∉ c.trace) :
    connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z := by
  have hxo : x ∈ P ∪ Q := hcover hx
  have hyo : y ∈ P ∪ Q := hcover hy
  have hzo : z ∈ P ∪ Q := hcover hz
  rcases hxo with hxP | hxQ
  · rcases hyo with hyP | hyQ
    · exact Or.inl (connectedComponentIn_eq_of_same_preconnected hP hPc hxP hyP)
    · rcases hzo with hzP | hzQ
      · exact Or.inr (Or.inl (connectedComponentIn_eq_of_same_preconnected hP hPc hxP hzP))
      · exact Or.inr (Or.inr (connectedComponentIn_eq_of_same_preconnected hQ hQc hyQ hzQ))
  · rcases hyo with hyP | hyQ
    · rcases hzo with hzP | hzQ
      · exact Or.inr (Or.inr (connectedComponentIn_eq_of_same_preconnected hP hPc hyP hzP))
      · exact Or.inr (Or.inl (connectedComponentIn_eq_of_same_preconnected hQ hQc hxQ hzQ))
    · exact Or.inl (connectedComponentIn_eq_of_same_preconnected hQ hQc hxQ hyQ)

end

end Work.Smooth.JordanSeparation
