import Mathlib
import Submission.Work.Drive.classTripleSystem
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.diffMap_generalPosition
import Submission.Work.Drive.sameKernel_transfer
import Submission.Work.Drive.exists_iso_of_ker_eq
import Submission.Work.Drive.fderiv_classSystem_y

/-!
# The conversion: regularity of the class system ⟹ `hci` and `hV`

The class system `Work.Drive.classSystem` (see `Submission/Work/Drive/classTripleSystem.lean`) has, in
the quaternionic model `qform` of the class equality on `ℝP³`, exactly the triples of *perturbed*
common class as zeros.  This file converts the *regularity* of a zero (surjectivity of the
`y`-derivative of the system) into the two intrinsic conditions of `Work.Drive.ClassTripleRegular`:

* the class map of each perturbed plane is an immersion (`hci`), and
* the three class-derivative `2`-planes are in general position (`hV`).

## The route

Write `v k := A k (V k (parOf y k))` (non-zero), `d k := ∂_y (A k (V k (parOf · k)))` and
`π := qformRight (v 0)` — so `ker π = span{v 0}`.  `Work.Drive.fderiv_classSystem_y` writes the
`y`-derivative of the system as `pair33 ∘ G` with
`G z = (qform (d 0 z) (v 1) + qform (v 0) (d 1 z), qform (d 0 z) (v 2) + qform (v 0) (d 2 z))`;
using anti-symmetry and `v k = μ k • v 0`, `G` is a *reparametrisation* of the standard difference map
of the three linear maps `π ∘ d k`, so `Work.Drive.diffMap_generalPosition` yields

> `(∀ k, Injective (π ∘ d k)) ∧ (⨅ k, range (π ∘ d k) = ⊥)`.

Then, for the perturbed plane presented by `W k := A k ∘ V k` (so that `cls ∘ (linCapping A k ∘ P k)
= projMk ∘ W k`), `Work.Drive.injective_mfderiv_projMk_iff'` identifies `hci` with
`Injective (fderiv W k y) ∧ range (fderiv W k y) ⊓ span{v 0} = ⊥`, which is `Injective (π ∘ d k)`;
and `Work.Drive.range_mfderiv_projMk` writes each intrinsic range as
`map (projCoordFunDerivE i (v k)) (range (fderiv W k y))` with the *same* chart index `i`; since
`projCoordFunDerivE i` is invariant under rescaling its base point (up to a scalar, §1), all three of
those maps have kernel `span{v 0} = ker π` and differ from `π` by a linear isomorphism — so
`Work.Drive.sameKernel_transfer` transfers the vanishing of the triple intersection.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

noncomputable section

/-! ## 1. `projCoordFunDerivE` is invariant under rescaling the base point -/

/-! ## 1b. The tangent models, named (so that statements can be written without the `𝓡` notation) -/

/-- The model with corners of the plane parameter space, `𝓡 2`. -/
abbrev Tm2 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))

/-- The model with corners of the projective class space, `𝓡 3`. -/
abbrev Tm3 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))

/-! ## 2. The block projection and `parOf` -/

/-- The `k`-th block of the plane parameter space, as a continuous linear map. -/
noncomputable def parCProj (k : Fin 3) : Tgt 6 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      PiLp.proj 2 (fun _ : Fin 6 => ℝ) (parC k i)))

@[simp] lemma parCProj_apply (k : Fin 3) (y : Tgt 6) (i : Fin 2) :
    parCProj k y i = y (parC k i) := by
  simp only [parCProj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    PiLp.proj_apply, ContinuousLinearEquiv.coe_coe]
  rfl

lemma parCProj_apply_eq_parOf (k : Fin 3) (y : Tgt 6) : parCProj k y = parOf y k := by
  ext i
  rw [parCProj_apply, parOf_apply]

lemma parCProj_surjective (k : Fin 3) : Function.Surjective (parCProj k) := by
  intro w
  classical
  refine ⟨WithLp.toLp 2 (fun j : Fin 6 =>
      if h : ∃ i : Fin 2, parC k i = j then w (Classical.choose h) else 0), ?_⟩
  ext i
  rw [parCProj_apply]
  show (WithLp.toLp 2 (fun j : Fin 6 =>
      if h : ∃ i : Fin 2, parC k i = j then w (Classical.choose h) else 0)).ofLp (parC k i) = w i
  rw [WithLp.ofLp_toLp, dif_pos ⟨i, rfl⟩]
  exact congrArg w (parC_injective (Classical.choose_spec
    (⟨i, rfl⟩ : ∃ i' : Fin 2, parC k i' = parC k i))).2

/-- The `common class` hypothesis of the *perturbed* planes makes the class system vanish: equal
classes are proportional vectors. -/
theorem classSystem_eq_zero_of_proportional {m : ℕ}
    (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (p : EuclideanSpace ℝ (Fin m)) (y : Tgt 6)
    (hprop : ∀ k : Fin 3, ∃ a : ℝ, a • A p 0 (V 0 (parOf y 0)) = A p k (V k (parOf y k))) :
    classSystem V A p y = 0 := by
  rw [classSystem, pair33_eq_zero_iff]
  constructor
  · obtain ⟨a, ha⟩ := hprop 1
    rw [← ha, qform_smul_right, qform_self, smul_zero]
  · obtain ⟨a, ha⟩ := hprop 2
    rw [← ha, qform_smul_right, qform_self, smul_zero]

end

end Work.Drive
