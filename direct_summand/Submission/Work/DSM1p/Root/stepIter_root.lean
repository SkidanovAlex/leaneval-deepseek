import Mathlib
import Submission.Work.DSM1p.Basic

namespace Work.DSM1p.Root

theorem stepIter_root (R : Type*) [CommRing R] (p : ℕ) (a : R) (m k : ℕ) :
    Work.DSM1p.RootTower.stepIter R p a m k (Work.DSM1p.RootTower.root R p a m) =
      Work.DSM1p.RootTower.root R p a (m + k) ^ p ^ k := by
  induction k with
  | zero => simp [Work.DSM1p.RootTower.stepIter]
  | succ k ih =>
    rw [Work.DSM1p.RootTower.stepIter, RingHom.comp_apply, ih, map_pow,
      Work.DSM1p.RootTower.step_root, ← pow_mul, ← pow_succ']
    rfl

end Work.DSM1p.Root
