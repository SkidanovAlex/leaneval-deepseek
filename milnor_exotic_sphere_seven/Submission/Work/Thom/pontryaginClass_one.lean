import Mathlib
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open Work.TangentClasses

/-- **`cohTransport` along a proof of an identity of degrees is the identity on classes.**
The canonical identification of the cohomology in two *equal* degrees does nothing: since the two
sides of the equality `h : n = n` are the same degree, `cohTransport h` acts as the identity.  (In
the application below `h` is a proof of `2 * (2 * 1) = 4 * 1`, two *definitionally equal* naturals,
so the transport is invisible.) -/
theorem cohTransport_self {B : Type} [TopologicalSpace B] {n : ℕ} (h : n = n)
    (x : Coh ℤ n B) : cohTransport h x = x := by
  rw [Subsingleton.elim h rfl, cohTransport_rfl]

theorem pontryaginClass_one {k : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι) :
    Work.Thom.pontryaginClass 1 Z = Work.Thom.pontryagin1 Z := by
  -- Both sides are `- c₂(E ⊗_ℝ ℂ)`; the definitions differ only in that `pontryaginClass`
  -- carries the universal sign `(-1)^i` (with `i = 1`, so `-1`) and a degree transport
  -- `2 * (2 * i) = 4 * i` (with `i = 1`, a proof between the definitionally equal naturals
  -- `2 * (2 * 1) = 4` and `4 * 1 = 4`).
  unfold Work.Thom.pontryaginClass Work.Thom.pontryagin1
  rw [pow_one, neg_one_zsmul]
  change Work.Thom.cohTransport (show (4 : ℕ) = 4 from (by ring : 2 * (2 * 1) = 4 * 1))
    (- chernClass k 2 (complexificationCore Z)) = - chernClass k 2 (complexificationCore Z)
  rw [cohTransport_self]

end Work.Thom
