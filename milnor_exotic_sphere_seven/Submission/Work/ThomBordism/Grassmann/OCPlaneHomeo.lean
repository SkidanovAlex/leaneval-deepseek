import Mathlib
import Submission.Work.ThomBordism.Grassmann.fibreBaseHomeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of the tautological bundle over `baseVec` is the oriented Grassmannian one rank down

The oriented `k`-planes of `ℝ^{k+m}` containing the fixed unit vector `baseVec k m` are exactly the
oriented `(k-1)`-planes of `(baseVec k m)^⊥ ≅ ℝ^{(k-1)+m}`, by appending `baseVec k m` as the last
vector of a frame.  This is the map `omega`, a continuous bijection from the compact space
`G̃r_{k-1}(ℝ^{(k-1)+m})` onto a subspace of the Hausdorff space `G̃r_k(ℝ^{k+m})`; hence a
homeomorphism, whose inverse is the homeomorphism `OCPlaneHomeo` of this file.
-/

namespace Work.ThomBordism.Grassmann

theorem OCPlaneHomeo (k m : ℕ) (hk : 2 ≤ k) :
    Nonempty ({P : Work.ThomBordism.Grassmann.OG k m //
      Work.ThomBordism.Grassmann.memPlane P (Work.ThomBordism.Grassmann.baseVec k m)} ≃ₜ
      Work.ThomBordism.Grassmann.OG (k - 1) m) := by
  -- `omega : G̃r_{k-1}(ℝ^{(k-1)+m}) → {P // memPlane P (baseVec k m)}` is a continuous bijection
  -- from a compact space to a Hausdorff space, hence a homeomorphism.
  have h : IsHomeomorph (omega k m hk) := by
    rw [isHomeomorph_iff_continuous_bijective]
    exact ⟨continuous_omega hk, omega_bijective hk⟩
  exact ⟨((h.homeomorph (omega k m hk))).symm⟩

end Work.ThomBordism.Grassmann
