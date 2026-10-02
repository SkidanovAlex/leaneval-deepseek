import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.inclusionBundleIso
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Agree.complexificationIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The ambient inclusion pulls `p₂(γ)` back to `p₂(γ)`

Appending a last zero coordinate gives the continuous map `ogInclCM k m : OG k m → OG k (m+1)` of
oriented Grassmannians, and `Work.ThomBordism.Grassmann.inclusionBundleIso` shows that the
pulled-back tautological bundle `ogInclCM k m ^* γ_{k,m+1}` is isomorphic to `γ_{k,m}`.

Since the Pontryagin classes are natural under pullback (`Work.Thom.pontryaginClass_comap`) and
depend only on the isomorphism class of the bundle (`incl_pontryaginClass_eq_of_bundleIso` below,
from the isomorphism-invariance of the Chern classes of the complexification), the induced map in
degree-`8` cohomology sends `p₂(γ_{k,m+1})` to `p₂(γ_{k,m})`.

This is the `m`-direction stabilisation step for the second Pontryagin class; it is used to move
degree-eight cohomology statements (for instance the non-vanishing of `p₂`) from a small
Grassmannian to a large one.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- **`p_i` depends only on the isomorphism class of a real bundle** with a fixed model fibre
`ℝ^k`: two isomorphic real bundles over the same base have the same Pontryagin classes.  Immediate
from `Work.Agree.chernClass_complexificationCore_eq` (isomorphism-invariance of the Chern classes of
the complexifications) and `p_i = (-1)^i c_{2i}(· ⊗_ℝ ℂ)`. -/
theorem incl_pontryaginClass_eq_of_bundleIso (i : ℕ) {k : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    {Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι}
    {Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι'}
    (e : Work.Thom.BundleIso Z Z') :
    Work.Thom.pontryaginClass i Z = Work.Thom.pontryaginClass i Z' := by
  have h : Work.Thom.chernClass k (2 * i) (Work.Thom.complexificationCore Z)
      = Work.Thom.chernClass k (2 * i) (Work.Thom.complexificationCore Z') :=
    Work.Agree.chernClass_complexificationCore_eq rfl Z Z' e (2 * i)
  unfold Work.Thom.pontryaginClass
  exact congrArg (fun c => Work.Thom.cohTransport (show 2 * (2 * i) = 4 * i from by ring)
    (((-1 : ℤ) ^ i) • c)) h

/-- **The `m`-step for `p₂`**: there is a continuous map `OG k m → OG k (m+1)` (the ambient
inclusion) whose pullback in degree-`8` cohomology sends `p₂(γ_{k,m+1})` to `p₂(γ_{k,m})`. -/
theorem CohMap_p2_incl (k m : ℕ) :
    ∃ φ : C(Work.ThomBordism.Grassmann.OG k m, Work.ThomBordism.Grassmann.OG k (m + 1)),
      (Work.Thom.CohMap φ ℤ 8).hom (Work.ThomBordism.Grassmann.p2 k (m + 1))
        = Work.ThomBordism.Grassmann.p2 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := inclusionBundleIso k m
  refine ⟨φ, ?_⟩
  have hnat := (Work.Thom.pontryaginClass_comap (i := 2)
    (tautologicalBundle k (m + 1)) φ).symm
  have hiso : Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) :=
    incl_pontryaginClass_eq_of_bundleIso 2 e
  rw [show p2 k (m + 1) = Work.Thom.pontryaginClass 2 (tautologicalBundle k (m + 1))
        from rfl,
    show p2 k m = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) from rfl]
  rw [hnat, hiso]

end

end Work.ThomBordism.Grassmann
