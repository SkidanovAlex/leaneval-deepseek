import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.doubleInterval_block_bound
import Submission.Work.CNum.integrableOn_max_prod

/-!
# `rearrInt_bridge`

The rearrangement integral `rearrInt 1 phiC = ∫₀¹∫₀¹ max (log‖phiC s‖) (log‖phiC t‖)`
is bounded by the block-averaged upper bound obtained from any `N`-fold uniform
subdivision of `[0,1]`: if `G k` bounds `circleLog phiC` on the `k`-th interval
`[k/N, (k+1)/N]`, then

`rearrInt 1 phiC ≤ ∑ k ∑ k' (1/N²) * max (G k) (G k')`.

This is the "seeding" step of the certified numerics for Theorem C: the right-hand
side is a finite sum of explicit numbers, so the bound on `rearrInt` reduces to
evaluating `G` on a finite grid.

Delegated pieces (proved in the sibling modules):
* `Work.CNum.doubleInterval_block_bound` — the general measure-theoretic block bound
  for a double interval integral;
* `Work.CNum.integrableOn_max_prod` — integrability of `(s,t) ↦ max (g s) (g t)`
  on the square `(0,1]²` for `g` continuous on `[0,1]`.
-/

open MeasureTheory Set

namespace Work.CNum

theorem rearrInt_bridge {N : ℕ} (hN : 0 < N) (G : Fin N → ℝ)
    (hcont : ContinuousOn (fun t : ℝ => Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t) (Set.Icc 0 1))
    (h : ∀ k : Fin N, ∀ t ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N),
      Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ G k) :
    Submission.CDTPlan.rearrInt (fun _ : Fin 1 => (1 : ℝ)) (fun _ => Submission.CDTPlan.phiC) ≤
      ∑ k : Fin N, ∑ k' : Fin N, (1 / (N : ℝ) ^ 2) * max (G k) (G k') := by
  have hrearr :
      Submission.CDTPlan.rearrInt (fun _ : Fin 1 => (1 : ℝ)) (fun _ => Submission.CDTPlan.phiC)
        = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
            max (Submission.CDTPlan.circleLog Submission.CDTPlan.phiC s)
                (Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t) := by
    simp only [Submission.CDTPlan.rearrInt]
    norm_num
  rw [hrearr]
  refine Work.CNum.doubleInterval_block_bound hN
    (fun s t => max (Submission.CDTPlan.circleLog Submission.CDTPlan.phiC s)
                      (Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t))
    (fun k k' => max (G k) (G k')) ?_ ?_
  · exact Work.CNum.integrableOn_max_prod hcont
  · intro k k' s hs t ht
    exact max_le_max (h k s ⟨le_of_lt hs.1, hs.2⟩) (h k' t ⟨le_of_lt ht.1, ht.2⟩)

end Work.CNum
