import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

/-- The momentum region `P_H` is invariant under negation of the mode: it is
defined through `‖F.kmom k‖` and `kmom` is odd (`F.kmom_neg`), while `‖·‖` is
even.  This is the substantive input to `sum_PHset_neg`. -/
theorem mem_PHset_neg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (k : Mode) :
    k ∈ F.PHset E ↔ -k ∈ F.PHset E := by
  simp only [FockData.PHset, Finset.mem_filter]
  unfold FockData.PH
  constructor
  · rintro ⟨hk, hPH⟩
    exact ⟨by simpa [excited] using hk, by simpa only [F.kmom_neg k, norm_neg] using hPH⟩
  · rintro ⟨hk, hPH⟩
    exact ⟨by simpa [excited] using hk, by simpa only [F.kmom_neg k, norm_neg] using hPH⟩

/-- Summing a function of the mode over `P_H` is invariant under replacing the
argument by its negative: `∑_{k∈P_H} f(-k) = ∑_{k∈P_H} f(k)`.  Immediate from
`mem_PHset_neg` by the substitution `k ↦ -k` (`Finset.sum_equiv` with the
negation equivalence of `Mode`). -/
theorem sum_PHset_neg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) {M : Type*}
    [AddCommMonoid M] (f : Mode → M) :
    ∑ k ∈ F.PHset E, f (-k) = ∑ k ∈ F.PHset E, f k := by
  exact Finset.sum_equiv (Equiv.neg Mode) (fun i => mem_PHset_neg F E i) (fun i _ => rfl)

end Work.BoseB7
