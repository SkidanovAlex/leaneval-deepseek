import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs
import Submission.Work.RPB.B1a.Maehara.exists_first_exit
import Submission.Work.RPB.B1a.Maehara.exists_path_to_outside_of_unbounded_component

set_option autoImplicit false

namespace Work.RPB.B1a.Maehara

open Set Metric

/-- **Reaching the boundary of the rectangle from an unbounded complementary component.**

Let `K ⊆ ℂ` be closed, `x ∉ K` a point of the rectangle `RectC = [-1,1] × [-2,2]` whose connected
component in `Kᶜ` is unbounded.  Then one can walk from `x` inside the rectangle and outside `K`
to a point `w` of the boundary `BdC` which is itself outside `K`.

The proof is a two-step reduction:

* since `Kᶜ` is open in the locally path-connected space `ℂ`, the unbounded component of `x` is
  path-connected; as it is unbounded while `RectC` is bounded it contains a point `y ∉ RectC`, and
  a path in it runs from `x` to `y` without meeting `K`
  (`exists_path_to_outside_of_unbounded_component`);
* such a path leaves the rectangle for the first time at a parameter `t₀`, whose image is a point of
  `BdC` (`exists_first_exit`).

Re-parametrising this initial piece of the path gives the required `q`. -/
theorem exists_boundary_path_of_unbounded_component (K : Set ℂ) (hK : IsClosed K) (x : ℂ)
    (hxK : x ∉ K) (hxR : x ∈ RectC)
    (hnotbdd : ¬ Bornology.IsBounded (connectedComponentIn (Kᶜ) x)) :
    ∃ w ∈ BdC, w ∉ K ∧ ∃ q : ℝ → ℂ, Continuous q ∧ q 0 = x ∧ q 1 = w ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, q t ∈ RectC) ∧ (∀ t, q t ∉ K) := by
  -- A path outside `K` from `x` to a point `y` outside the rectangle.
  obtain ⟨y, hyR, p, hp, hp0, hp1, hpK⟩ :=
    exists_path_to_outside_of_unbounded_component K hK x hxK hnotbdd
  -- The first exit point of that path from the rectangle is a point of `BdC`.
  obtain ⟨t₀, ht₀, ht₀Bd, ht₀rect⟩ :=
    exists_first_exit p hp (by rw [hp0]; exact hxR) (by rw [hp1]; exact hyR)
  -- Re-parametrise the initial piece `p '' [0, t₀]` on `[0,1]`, and keep it constant for `t ≤ 0`.
  refine ⟨p t₀, ht₀Bd, hpK t₀, fun t => p (max t 0 * t₀), ?_, ?_, ?_, ?_, ?_⟩
  · exact hp.comp ((continuous_id.max continuous_const).mul continuous_const)
  · simp [hp0]
  · simp
  · intro t ht
    apply ht₀rect
    refine ⟨by nlinarith [le_max_right t 0, ht₀.1],
      by nlinarith [max_le ht.2 (by norm_num : (0 : ℝ) ≤ 1), ht₀.1]⟩
  · intro t
    exact hpK (max t 0 * t₀)

end Work.RPB.B1a.Maehara
