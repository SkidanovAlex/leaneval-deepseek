import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

noncomputable section

open Classical Polynomial Metric

/-- A multiset-indexed sum of circle integrable functions is circle integrable. -/
lemma circleIntegrable_multiset_apply {ι : Type*} {c : ℂ} {r : ℝ} (S : Multiset ι)
    (h : ι → ℂ → ℂ) (hint : ∀ a ∈ S, CircleIntegrable (h a) c r) :
    CircleIntegrable (fun z => (S.map (fun a => h a z)).sum) c r := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x T ih =>
      have hx : CircleIntegrable (h x) c r := hint x (Multiset.mem_cons_self x T)
      have hT : ∀ b ∈ T, CircleIntegrable (h b) c r := fun b hb =>
        hint b (Multiset.mem_cons_of_mem hb)
      have hsum : CircleIntegrable (h x + fun z => (Multiset.map (fun a => h a z) T).sum) c r :=
        hx.add (ih hT)
      have hfun : (fun z => (Multiset.map (fun a => h a z) (x ::ₘ T)).sum)
          = h x + fun z => (Multiset.map (fun a => h a z) T).sum := by
        funext z; simp [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun]; exact hsum

/-- Linearity of the circle integral over a multiset-indexed sum. -/
lemma circleIntegral_multiset_sum {ι : Type*} {c : ℂ} {r : ℝ} (S : Multiset ι)
    (h : ι → ℂ → ℂ) (hint : ∀ a ∈ S, CircleIntegrable (h a) c r) :
    (∮ z in C(c, r), (S.map (fun a => h a z)).sum)
      = (S.map (fun a => ∮ z in C(c, r), h a z)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons x T ih =>
      have hx : CircleIntegrable (h x) c r := hint x (Multiset.mem_cons_self x T)
      have hT : ∀ b ∈ T, CircleIntegrable (h b) c r := fun b hb =>
        hint b (Multiset.mem_cons_of_mem hb)
      have hsumT : CircleIntegrable (fun z => (T.map (fun b => h b z)).sum) c r :=
        circleIntegrable_multiset_apply T h hT
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [circleIntegral.integral_add (f := fun z => h x z)
            (g := fun z => (T.map (fun b => h b z)).sum) hx hsumT, ih hT]

/-- Pulling a constant out of a multiset sum with an indicator. -/
lemma multiset_sum_ite {ι : Type*} (p : ι → Prop) [DecidablePred p] (S : Multiset ι)
    (k : ℂ) (f : ι → ℂ) :
    (S.map (fun a => if p a then k * f a else 0)).sum = k * ((S.filter p).map f).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x T ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      by_cases hp : p x
      · rw [ite_eq_left hp, Multiset.filter_cons_of_pos T hp, Multiset.map_cons, Multiset.sum_cons]
        ring
      · rw [ite_eq_right hp, Multiset.filter_cons_of_neg T hp]
        simp

open Classical Polynomial in
theorem polyArgPrinciple {P : ℂ[X]} (hP : P ≠ 0) {c : ℂ} {r : ℝ} (hr : 0 < r) {g : ℂ[X]}
    (h0 : ∀ z ∈ Metric.sphere c r, P.eval z ≠ 0) :
    (∮ z in C(c, r), (P.derivative.eval z / P.eval z) * g.eval z)
      = 2 * ↑Real.pi * Complex.I *
        ((P.roots.filter (fun a => a ∈ Metric.ball c r)).map (fun a => g.eval a)).sum := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  set S : Multiset ℂ := P.roots with hS
  -- No root of `P` lies on the sphere.
  have hroot_not_sphere : ∀ a ∈ S, a ∉ Metric.sphere c r := by
    intro a ha hmem
    have haP : P.eval a = 0 :=
      Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hP).mp (hS ▸ ha))
    exact h0 a hmem haP
  -- Step 1: rewrite the integrand on the sphere via the logarithmic derivative formula.
  have step1 : (∮ z in C(c, r), (P.derivative.eval z / P.eval z) * g.eval z)
      = ∮ z in C(c, r), (S.map (fun a => 1 / (z - a) * g.eval z)).sum := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    show P.derivative.eval z / P.eval z * g.eval z = (S.map (fun a => 1 / (z - a) * g.eval z)).sum
    have hzP : P.eval z ≠ 0 := h0 z hz
    have hlog : P.derivative.eval z / P.eval z = (S.map (fun a => 1 / (z - a))).sum := by
      simpa only [hS] using hsplit.eval_derivative_div_eval_of_ne_zero hzP
    rw [hlog, Multiset.sum_map_mul_right]
  -- Integrability of each summand.
  have hint : ∀ a ∈ S, CircleIntegrable (fun z => 1 / (z - a) * g.eval z) c r := by
    intro a ha
    have hna := hroot_not_sphere a ha
    have hne : ∀ z ∈ Metric.sphere c r, z ≠ a := fun z hz hza => hna (hza ▸ hz)
    have hcont : ContinuousOn (fun z => 1 / (z - a) * g.eval z) (Metric.sphere c r) := by
      refine ContinuousOn.mul ?_ (Polynomial.continuous g).continuousOn
      exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        (fun z hz => sub_ne_zero.mpr (hne z hz))
    exact hcont.circleIntegrable hr.le
  -- Step 2: push the integral through the multiset sum.
  have step2 : (∮ z in C(c, r), (S.map (fun a => 1 / (z - a) * g.eval z)).sum)
      = (S.map (fun a => ∮ z in C(c, r), 1 / (z - a) * g.eval z)).sum :=
    circleIntegral_multiset_sum S (fun a z => 1 / (z - a) * g.eval z) hint
  -- Step 3: evaluate each Cauchy-type integral.
  have hterm : ∀ a ∈ S, (∮ z in C(c, r), 1 / (z - a) * g.eval z)
      = if a ∈ Metric.ball c r then 2 * ↑Real.pi * Complex.I * g.eval a else 0 := by
    intro a ha
    have hna := hroot_not_sphere a ha
    have hswap : (∮ z in C(c, r), 1 / (z - a) * g.eval z)
        = ∮ z in C(c, r), g.eval z / (z - a) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      show 1 / (z - a) * g.eval z = g.eval z / (z - a)
      ring
    by_cases hab : a ∈ Metric.ball c r
    · rw [ite_eq_left hab, hswap]
      exact Complex.circleIntegral_div_sub_of_differentiable_on_off_countable (s := (∅ : Set ℂ))
        Set.countable_empty hab (Polynomial.continuous g).continuousOn
        (fun z _ => Polynomial.differentiableAt g)
    · rw [ite_eq_right hab, hswap]
      have hna_closed : a ∉ Metric.closedBall c r := by
        have h1 : ¬ dist a c < r := fun hh => hab (by rw [Metric.mem_ball]; exact hh)
        have h2 : dist a c ≠ r := fun hh => hna (by rw [Metric.mem_sphere]; exact hh)
        have h3 : ¬ dist a c ≤ r := fun h => (lt_or_eq_of_le h).elim h1 h2
        simpa [Metric.mem_closedBall] using h3
      refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
        (s := (∅ : Set ℂ)) Set.countable_empty (f := fun z => g.eval z / (z - a)) ?_ ?_
      · refine ContinuousOn.div (Polynomial.continuous g).continuousOn
          (continuousOn_id.sub continuousOn_const) (fun z hz => sub_ne_zero.mpr ?_)
        intro hza
        exact hna_closed (hza ▸ hz)
      · intro z hz
        refine DifferentiableAt.div (Polynomial.differentiableAt g)
          (differentiableAt_id.sub_const a) (sub_ne_zero.mpr ?_)
        intro hza
        exact hab (hza ▸ hz.1)
  have step3 : (S.map (fun a => ∮ z in C(c, r), 1 / (z - a) * g.eval z)).sum
      = (S.map (fun a => if a ∈ Metric.ball c r then
          2 * ↑Real.pi * Complex.I * g.eval a else 0)).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl hterm)
  have step4 : (S.map (fun a => if a ∈ Metric.ball c r then
        2 * ↑Real.pi * Complex.I * g.eval a else 0)).sum
      = 2 * ↑Real.pi * Complex.I *
        ((S.filter (fun a => a ∈ Metric.ball c r)).map (fun a => g.eval a)).sum := by
    rw [multiset_sum_ite (p := fun a => a ∈ Metric.ball c r) (S := S)
      (k := 2 * ↑Real.pi * Complex.I) (f := fun a => g.eval a)]
  exact step1.trans (step2.trans (step3.trans step4))

end

end Work.PARIMPL.ParSplit
