import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

namespace Work.ORVonNeumann.Rep

theorem vnInnerHdelta {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (A : Matrix (Fin n) (Fin n) (↥(Work.ORVonNeumann.groupVonNeumann G))) (i : Fin n) : inner ℂ (Work.ORVonNeumann.Rep.hdelta (G := G) n i) (Work.ORVonNeumann.Rep.matOp (G := G) A (Work.ORVonNeumann.Rep.hdelta (G := G) n i)) = Work.ORVonNeumann.Rep.tau (A i i) := by
  classical
  have hmat : ∀ k : Fin n,
      (matOp (G := G) A (hdelta (G := G) n i)).ofLp k
        = ((A k i : ↥(groupVonNeumann G)) : boundedEnd G) (delta1 G) := by
    intro k
    rw [← hcoord_apply (G := G) n k,
      hcoord_matOp_apply (G := G) A (hdelta (G := G) n i) k]
    rw [Finset.sum_eq_single i]
    · rw [hcoord_hdelta, if_pos rfl]
    · intro j _ hj
      rw [hcoord_hdelta, if_neg hj, map_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · rw [hmat i, ← hcoord_apply (G := G) n i, hcoord_hdelta, if_pos rfl, tau_apply]
  · intro k _ hk
    rw [← hcoord_apply (G := G) n k, hcoord_hdelta, if_neg hk, inner_zero_left]
  · intro h; exact absurd (Finset.mem_univ i) h

end Work.ORVonNeumann.Rep
