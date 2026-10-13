import Mathlib
import Submission.Work.WilG2.Tnorm

namespace Work.WilG4c

/-- Finite-sum subadditivity of the jet norm `tnorm` (BNZ's `‖·‖_{T,r}`, defined in namespace
`WilkiesDesign.CG` in `Submission/Work/Wilkies/CG/Spec.lean`, API in
`Submission/Work/WilG2/Tnorm.lean`): `‖Σᵢ fᵢ‖_{T,r} ≤ Σᵢ ‖fᵢ‖_{T,r}` at a point.  Immediate from
`WilkiesDesign.CG.tnorm_add_le` by induction over the finite index set (the empty sum is the zero
function; `ContDiffAt.sum` gives smoothness of the partial sums). -/
theorem tnorm_finset_sum_le {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (f : ι → E → ℝ) (x : E) (hf : ∀ i, ContDiffAt ℝ r (f i) x) :
    WilkiesDesign.CG.tnorm r (fun y => ∑ i, f i y) x ≤ ∑ i, WilkiesDesign.CG.tnorm r (f i) x := by
  classical
  -- Prove the statement for an arbitrary finite index set `s`, then specialise to `univ`.
  have key : ∀ s : Finset ι,
      WilkiesDesign.CG.tnorm r (fun y => ∑ i ∈ s, f i y) x
        ≤ ∑ i ∈ s, WilkiesDesign.CG.tnorm r (f i) x := by
    intro s
    induction s using Finset.induction with
    | empty =>
      -- The empty sum is the zero function; `tnorm` of `0` is `‖0‖ = 0 ≤ 0`.
      simp [WilkiesDesign.CG.tnorm_const]
    | insert a s ha ih =>
      -- Split off the new index `a`; the partial sum is smooth by `ContDiffAt.sum`.
      have hfun : (fun y => ∑ i ∈ insert a s, f i y) = f a + (fun y => ∑ i ∈ s, f i y) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      have hsum : ContDiffAt ℝ r (fun y => ∑ i ∈ s, f i y) x :=
        ContDiffAt.sum (fun i _ => hf i)
      rw [hfun, Finset.sum_insert ha]
      calc WilkiesDesign.CG.tnorm r (f a + fun y => ∑ i ∈ s, f i y) x
          ≤ WilkiesDesign.CG.tnorm r (f a) x
              + WilkiesDesign.CG.tnorm r (fun y => ∑ i ∈ s, f i y) x :=
            WilkiesDesign.CG.tnorm_add_le r (f a) (fun y => ∑ i ∈ s, f i y) x (hf a) hsum
        _ ≤ WilkiesDesign.CG.tnorm r (f a) x + ∑ i ∈ s, WilkiesDesign.CG.tnorm r (f i) x :=
            add_le_add le_rfl ih
  simpa using key Finset.univ

end Work.WilG4c
