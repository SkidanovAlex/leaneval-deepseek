import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

/-- If `X` is continuous at `q` and vanishes there, then multiplying `X` by an arbitrary
`{0,1}`-valued factor (i.e. replacing `X y` by `0` on the complement of a set through `q`)
does not destroy continuity at `q`: the value is squeezed between `0` and `‖X y‖`. -/
theorem continuousAt_ite_zero {X : P3 → (P3 →L[ℝ] ℝ)} {p : P3 → Prop} [DecidablePred p] {q : P3}
    (hX : ContinuousAt X q) (hXq : X q = 0) :
    ContinuousAt (fun y => if p y then X y else 0) q := by
  have hq0 : (if p q then X q else 0 : P3 →L[ℝ] ℝ) = 0 := by
    by_cases hp : p q <;> simp [hp, hXq]
  rw [ContinuousAt, hq0]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm (a := fun y => ‖X y‖) (fun y => ?_) ?_
  · by_cases hp : p y <;> simp [hp]
  · simpa [ContinuousAt, hXq] using hX.norm

/-- Continuity at a point of a function obtained by gluing two continuous functions along the
half-space `{y | y.2.2 ≤ τ₀}`: at the interface `y.2.2 = τ₀` the two branches agree in the limit
because they agree *at* `q`. -/
theorem continuousAt_ite_le {g h : Work.FTS.StrongGlobal.P3 → (Work.FTS.StrongGlobal.P3 →L[ℝ] ℝ)}
    {τ₀ : ℝ} {q : Work.FTS.StrongGlobal.P3}
    (hg : ContinuousAt g q) (hh : ContinuousAt h q) (heq : g q = h q) :
    ContinuousAt (fun y : Work.FTS.StrongGlobal.P3 => if y.2.2 ≤ τ₀ then g y else h y) q := by
  have hite : ContinuousAt (fun y : P3 => if y.2.2 ≤ τ₀ then (g y - h y) else 0) q :=
    continuousAt_ite_zero (hg.sub hh) (sub_eq_zero.mpr heq)
  have hfun : (fun y : P3 => if y.2.2 ≤ τ₀ then g y else h y)
      = fun y : P3 => (if y.2.2 ≤ τ₀ then (g y - h y) else 0) + h y := by
    funext y
    by_cases hp : y.2.2 ≤ τ₀
    · simp only [hp, ↓reduceIte, sub_add_cancel]
    · simp only [hp, ↓reduceIte, zero_add]
  rw [hfun]
  exact hite.add hh

end Work.FTS.StrongGlobal
