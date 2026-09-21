import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The uniform region of the anchor's kernel estimates

`Reg a σ t` is the compact region on which all the state estimates of the anchor engine are
uniform in the perturbation `h`:

* the first slope `a` runs over `[49/100, 1]` — this is the anchor window `[1/2, 19/20]`
  thickened by `1/100`, which is what the Abel average of the `Θ`-datum needs;
* the second slope `σ` runs over the anchor window `[1/2, 19/20]`;
* the chord parameter `t` runs over `[-2, 2]`.

On the state ball `closedBall (baseState σ) (1/2)` the two chord parameters
`t = -(z 0)` and `t = z 1` lie in `[1/5, 2]`, which is the "far from the axis" range in which
the Abel radicands are bounded away from `0`.
-/

open Set

namespace Work.Anchor

/-- The compact region of the anchor's state estimates. -/
def Reg (a σ t : ℝ) : Prop :=
  a ∈ Set.Icc (49 / 100 : ℝ) 1 ∧ σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) ∧ t ∈ Set.Icc (-2 : ℝ) 2

lemma reg_of_mem {a σ t : ℝ} (ha : a ∈ Set.Icc (49 / 100 : ℝ) 1)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) (ht : t ∈ Set.Icc (-2 : ℝ) 2) : Reg a σ t :=
  ⟨ha, hσ, ht⟩

lemma Reg.a_mem {a σ t : ℝ} (h : Reg a σ t) : a ∈ Set.Icc (49 / 100 : ℝ) 1 := h.1
lemma Reg.sigma_mem {a σ t : ℝ} (h : Reg a σ t) : σ ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) := h.2.1
lemma Reg.t_mem {a σ t : ℝ} (h : Reg a σ t) : t ∈ Set.Icc (-2 : ℝ) 2 := h.2.2

end Work.Anchor
