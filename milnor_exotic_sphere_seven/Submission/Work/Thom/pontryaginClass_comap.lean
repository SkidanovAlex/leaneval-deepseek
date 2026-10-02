import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the Pontryagin classes under pullback

For a real vector bundle `Z` of rank `k` over `B` presented by gluing data over a finite index type
and a continuous map `f : B' → B`,

  `p_i(f^*Z) = f^*(p_i(Z))`   in `H^{4i}(B';ℤ)`,

where `p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)` (`Work.Thom.pontryaginClass`).

The proof is two lines of mathematics: the complexification commutes with the pullback
(`Work.Thom.complexificationCore_bundleComap`), the Chern classes are natural
(`Work.Thom.chernClass_comap`), and both the pullback and the canonical identification of two equal
degrees are `ℤ`-linear.  The formal content is the bookkeeping of the degree transport
`2 * (2 * i) = 4 * i` against the pullback: this is `Work.Thom.cohTransport_CohMap`, proved by
`subst` on the (subsingleton) proof of the equality of naturals.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **The pullback commutes with the canonical identification of two equal degrees.**  For
`h : n = n'`, pulling back along `f : B' → B` after the degree transport `n → n'` equals the degree
transport of the pullback.  This is the naturality of `CohMap` with respect to the (subsingleton)
equality of the degrees; it is proved by `subst` on `h`, reducing to the case `n = n` where the
transport is the identity (`cohTransport_rfl`). -/
theorem cohTransport_CohMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (f : C(B', B)) {n n' : ℕ} (h : n = n') (x : Coh ℤ n B) :
    (CohMap f ℤ n').hom (cohTransport h x) = cohTransport h ((CohMap f ℤ n).hom x) := by
  subst h
  simp

/-- **The canonical identification of two equal degrees is `ℤ`-linear** (compatibility with integer
multiples): `cohTransport h (a • x) = a • cohTransport h x`. -/
theorem cohTransport_zsmul {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n') (a : ℤ)
    (x : Coh ℤ n B) : cohTransport h (a • x) = a • cohTransport h x := by
  rw [← cohTransportLM_apply h (a • x), ← cohTransportLM_apply h x]
  exact map_zsmul (cohTransportLM h) a x

/-- **Naturality of the Pontryagin classes under pullback**: `p_i(f^*E) = f^*(p_i(E))`. -/
theorem pontryaginClass_comap {k i : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (f : C(B', B)) :
    Work.Thom.pontryaginClass i (Work.Thom.bundleComap Z f)
      = (Work.Thom.CohMap f ℤ (4 * i)).hom (Work.Thom.pontryaginClass i Z) := by
  unfold Work.Thom.pontryaginClass
  rw [Work.Thom.complexificationCore_bundleComap]
  rw [Work.Thom.chernClass_comap]
  simp only [cohTransport_zsmul, CohMap_zsmul, cohTransport_CohMap]

end

end Work.Thom
