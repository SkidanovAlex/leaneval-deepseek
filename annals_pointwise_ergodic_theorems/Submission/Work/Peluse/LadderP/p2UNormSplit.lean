import Mathlib
import Submission.Work.Peluse.LadderP.p2Defs
import Submission.Work.Peluse.LadderP.p2dilateSplit

namespace Work.Peluse.LadderP

theorem p2UNormSplit {c : ℤ} (hc : 0 < c) {s' D N : ℕ} (hs' : 1 ≤ s') (hD : 1 ≤ D)
    (hcN : c ≤ 2 * (N : ℤ) + 1) {f : ℤ → ℂ} (hfs : Work.Peluse.FinSuppZ f) :
    Work.Peluse.uNormPow s' (Work.Peluse.arithIcc c D) (Work.Peluse.symIcc N) f
      = ∑ r ∈ Finset.range c.natAbs, p2Wt c N r *
          Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 1 D) (p2Cls c N r) (p2ClsFn c r f) := by
  -- This is `p2dilateSplit` with all direction vectors equal to `1`.
  have h := p2dilateSplit (t := s') (q := fun _ : Fin s' => (1 : ℤ))
    (L := D) (N := N) hs' hc hD hcN hfs
  simp only [Work.Peluse.uNormPow, mul_one] at h ⊢
  rw [h]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [p2Wt, p2Cls]
  congr 1

end Work.Peluse.LadderP
