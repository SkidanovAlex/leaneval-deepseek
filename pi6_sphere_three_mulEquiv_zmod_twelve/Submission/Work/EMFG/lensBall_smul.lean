import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Basic

/-!
# The `μₙ`-action on the lens total space maps open balls to open balls

The action of `ZMod n` on `S^{2N+3}` (the total space of the lens space) is by scalar
multiplication with a unit complex number of norm one, transported through a real linear
isometry `ℂ^{N+2} ≅ ℝ^{2N+4}`.  It therefore preserves distances, and consequently carries the
open ball of radius `ε` around `x` onto the open ball of radius `ε` around `g • x`.  This is the
geometric input for the contractibility of small pieces of the lens space.
-/

namespace Work.EMFG

open Work.RatHurewicz

/-- The transported scalar action preserves distances on the ambient Euclidean space: it is the
conjugate, by the real linear isometry `cIso`, of multiplication by a complex number of norm one. -/
private theorem lensBall_dist_ambient (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n))
    (x y : lensAmb N) : dist (lensAct n N g x) (lensAct n N g y) = dist x y := by
  have hsub : lensAct n N g x - lensAct n N g y
      = (cIso N) ((phi n (NeZero.ne n) g : ℂ) • ((cIso N).symm x - (cIso N).symm y)) := by
    rw [lensAct, lensAct, ← map_sub, ← smul_sub]
  rw [dist_eq_norm, dist_eq_norm, hsub, (cIso N).norm_map, norm_smul, phi_norm, one_mul]
  rw [← map_sub]
  exact (cIso N).symm.norm_map (x - y)

/-- The `μₙ`-action on the sphere `S^{2N+3}` preserves distances. -/
private theorem lensBall_dist (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n))
    (x y : lensTotal N) : dist (g • y) (g • x) = dist y x := by
  rw [Subtype.dist_eq, Subtype.dist_eq]
  rw [show ((g • y : lensTotal N) : lensAmb N) = lensAct n N g y.1 from rfl,
      show ((g • x : lensTotal N) : lensAmb N) = lensAct n N g x.1 from rfl]
  exact lensBall_dist_ambient n N g y.1 x.1

theorem lensBall_smul (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n))
    (x : Work.RatHurewicz.lensTotal N) (ε : ℝ) :
    (fun y => g • y) '' Metric.ball x ε = Metric.ball (g • x) ε := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_ball] at hy ⊢
    rwa [lensBall_dist n N g x y]
  · intro hz
    rw [Metric.mem_ball] at hz
    refine ⟨g⁻¹ • z, ?_, ?_⟩
    · rw [Metric.mem_ball, ← lensBall_dist n N g x (g⁻¹ • z), smul_inv_smul]
      exact hz
    · exact smul_inv_smul g z

end Work.EMFG
