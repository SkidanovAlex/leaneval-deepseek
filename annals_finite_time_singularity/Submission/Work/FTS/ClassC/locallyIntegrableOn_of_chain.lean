/-
Copyright: work module for the Elgindi finite-time singularity project.

# Local integrability of the Euler-type chain integrand

Let `v : ℝ → ℝ` satisfy the integral relation

`v z - v s = ∫ r in s..z, (-(5 + α) / (α * r)) * v r`   for all `0 < s ≤ z`     (E)

i.e. `v` is a weak solution of the Euler-type ODE `v' = -β v / r` on `(0, ∞)`,
`β = (5 + α)/α > 0`.  The statement proved here is that the integrand
`F r = (-(5 + α) / (α r)) * v r` is locally integrable on `(0, ∞)`.

The argument is a rigidity observation: if `F` failed to be integrable on some `Ioc s z`
(`0 < s ≤ z`), then in Lean the interval integral is `0` (`integral_undef`), so (E) forces
`v z = v s`; splitting `Ioc s z = Ioc s x ∪ Ioc x z` and applying the same reasoning to each
half shows `v x = v s` for *every* `x ∈ Ioc s z`.  Hence `F` coincides on `Ioc s z` with the
continuous function `fun r => (-(5 + α) / (α r)) * v s`, which is integrable there — a
contradiction.  So `F` is integrable on every `Ioc s z` with `0 < s ≤ z`, and since a compact
subset of `(0, ∞)` sits inside such an interval, `F` is locally integrable on `(0, ∞)` by
`MeasureTheory.locallyIntegrableOn_iff`.

Note that no regularity of `v` is assumed and that the hypothesis `0 < α` is used only to
know `α ≠ 0` (so that `r ↦ -(5 + α)/(α r) * v s` is continuous on `(0, ∞)`).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.ClassC

theorem locallyIntegrableOn_of_chain {α : ℝ} {v : ℝ → ℝ} (hα : 0 < α)
    (hchain1 : ∀ s z : ℝ, 0 < s → s ≤ z →
      v z - v s = ∫ r in s..z, (-(5 + α) / (α * r)) * v r) :
    MeasureTheory.LocallyIntegrableOn (fun r : ℝ => (-(5 + α) / (α * r)) * v r) (Set.Ioi 0) := by
  set F : ℝ → ℝ := fun r => (-(5 + α) / (α * r)) * v r with hF
  have hch : ∀ s z : ℝ, 0 < s → s ≤ z → v z - v s = ∫ r in s..z, F r := by
    intro s z hs hsz
    simpa only [hF] using hchain1 s z hs hsz
  have hαne : α ≠ 0 := ne_of_gt hα
  -- Step 1: `F` is integrable on every `Ioc s z` with `0 < s ≤ z`.
  have key : ∀ s z : ℝ, 0 < s → s ≤ z → IntegrableOn F (Ioc s z) := by
    intro s z hs hsz
    by_contra hni
    -- If `F` is not integrable on `Ioc s z` the interval integral vanishes, so `v z = v s`.
    have hzero : ∫ r in s..z, F r = 0 := by
      rw [intervalIntegral.integral_of_le hsz]
      exact integral_undef hni
    have hzv : v z = v s := by
      have h := hch s z hs hsz
      rw [hzero] at h
      linarith
    -- ... and then `v` is constant on the whole of `Ioc s z`.
    have hconst : ∀ x ∈ Ioc s z, v x = v s := by
      intro x hx
      obtain ⟨hsx, hxz⟩ := hx
      by_cases h1 : IntegrableOn F (Ioc s x)
      · by_cases h2 : IntegrableOn F (Ioc x z)
        · have hunion := h1.union h2
          rw [Ioc_union_Ioc_eq_Ioc hsx.le hxz] at hunion
          exact absurd hunion hni
        · have h2zero : ∫ r in x..z, F r = 0 := by
            rw [intervalIntegral.integral_of_le hxz]
            exact integral_undef h2
          have h := hch x z (lt_trans hs hsx) hxz
          rw [h2zero] at h
          linarith
      · have h1zero : ∫ r in s..x, F r = 0 := by
          rw [intervalIntegral.integral_of_le hsx.le]
          exact integral_undef h1
        have h := hch s x hs hsx.le
        rw [h1zero] at h
        linarith
    -- Hence on `Ioc s z` the integrand agrees with a continuous function, contradiction.
    have hcont : ContinuousOn (fun r : ℝ => (-(5 + α) / (α * r)) * v s) (Icc s z) := by
      have h1 : ContinuousOn (fun r : ℝ => -(5 + α) / (α * r)) (Icc s z) := by
        apply ContinuousOn.div continuousOn_const
        · exact continuousOn_const.mul continuousOn_id
        · intro r hr
          exact mul_ne_zero hαne (ne_of_gt (lt_of_lt_of_le hs hr.1))
      exact h1.mul continuousOn_const
    have hint : IntegrableOn (fun r : ℝ => (-(5 + α) / (α * r)) * v s) (Icc s z) :=
      hcont.integrableOn_compact isCompact_Icc
    have hint' : IntegrableOn (fun r : ℝ => (-(5 + α) / (α * r)) * v s) (Ioc s z) :=
      hint.mono_set Ioc_subset_Icc_self
    refine hni ?_
    refine hint'.congr_fun ?_ measurableSet_Ioc
    intro r hr
    simp only [hF]
    rw [hconst r hr]
  -- Step 2: a compact subset of `(0, ∞)` lies in some `Ioc s z` with `0 < s ≤ z`.
  have hmain : MeasureTheory.LocallyIntegrableOn F (Set.Ioi 0) := by
    rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k hk hkc
    by_cases hne : k.Nonempty
    · obtain ⟨m, hmk, hmmin⟩ := hkc.exists_isMinOn hne continuousOn_id
      obtain ⟨M, hMk, hMmax⟩ := hkc.exists_isMaxOn hne continuousOn_id
      have hmpos : 0 < m := hk hmk
      have hle : m ≤ M := by simpa using hmmin hMk
      refine (key (m / 2) M (by linarith) (by linarith)).mono_set ?_
      intro y hy
      refine ⟨?_, ?_⟩
      · have h : m ≤ y := by simpa using hmmin hy
        linarith
      · simpa using hMmax hy
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact integrableOn_empty
  exact hmain

end Work.FTS.ClassC
