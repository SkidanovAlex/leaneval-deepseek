import Mathlib
import Submission.Work.Sphere.Basic
import Submission.Work.Sphere.contractibleSpace_sph_compl

set_option linter.style.haveILetI false

namespace Work.Cofibre

open ContinuousMap

/-- A continuous map from any space into a contractible space is nullhomotopic: the identity of
the contractible target is nullhomotopic, and `f` is a reparametrisation of it. -/
theorem nullhomotopic_of_contractible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : ContractibleSpace Y) (f : C(X, Y)) : f.Nullhomotopic := by
  haveI := hY
  have h := (id_nullhomotopic Y).comp_left f
  rwa [ContinuousMap.id_comp] at h

/-- A continuous map from any space into the sphere `Sᵈ` whose image avoids a point `q` is
nullhomotopic: the complement of a point in `Sᵈ` is contractible, so `f` factors through a
contractible space. -/
theorem nullhomotopic_of_misses_point (d : ℕ) (X : TopCat.{0})
    (f : ContinuousMap ↥X ↥(Submission.Sphere.Sph d)) (q : ↥(Submission.Sphere.Sph d))
    (h : ∀ x, f x ≠ q) : f.Nullhomotopic := by
  -- The complement of `q` in `Sᵈ`, a contractible space.
  let Y := {x : ↥(Submission.Sphere.Sph d) // x ≠ q}
  have hc : ContractibleSpace Y := Classical.choice (Work.Sphere.contractibleSpace_sph_compl q)
  -- The lift of `f` through the inclusion `Y ↪ Sᵈ`.
  let g : C(↥X, Y) := ⟨fun x => ⟨f x, h x⟩, f.continuous.subtype_mk _⟩
  have hg : g.Nullhomotopic := nullhomotopic_of_contractible hc g
  -- Composing the nullhomotopy of `g` with the inclusion `Y ↪ Sᵈ` recovers `f`.
  let inc : C(Y, ↥(Submission.Sphere.Sph d)) := ⟨Subtype.val, continuous_subtype_val⟩
  have h2 : (inc.comp g).Nullhomotopic := hg.comp_right inc
  have heq : inc.comp g = f := by
    ext x; rfl
  rwa [heq] at h2

end Work.Cofibre
