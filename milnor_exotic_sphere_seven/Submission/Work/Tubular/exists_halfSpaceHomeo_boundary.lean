import Mathlib
import Submission.Work.Tubular.exists_chartedSpace_normalDisc_add

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relabelling the half-space model, preserving the boundary hyperplane

`EuclideanHalfSpace n` is, by definition, the subtype `{x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0}`
of the Euclidean space; its *boundary* hyperplane is the locus `x 0 = 0` of the first coordinate.
The index `n` is however not preserved by the numerical identities one meets in applications: the
same geometric object is referred to at the index `8 + k` and at the numerically equal index
`7 + k + 1`.  The canonical identification is the relabelling of the coordinates by
`finCongr h : Fin m ≃ Fin n` for `h : m = n`, which **fixes the coordinate `0`** (it is
`Fin.cast h`, and `Fin.cast_zero` says that it sends `0` to `0`).

`Work.Tubular.exists_chartedSpace_normalDisc_add` already proves that this gives a homeomorphism
between the two half-space models (`nonempty_halfSpaceHomeomorph_of_eq`), but only as a `Nonempty`
statement, which forgets *which* homeomorphism was produced.  Here we record the stronger,
usable form: the relabelling homeomorphism itself, *together with* the fact that it preserves the
`0`-th coordinate, hence maps the boundary hyperplane onto the boundary hyperplane (and the open
half-space onto the open half-space).  The target `exists_halfSpaceHomeo_boundary` is the case
`m = 7 + k + 1`, `n = 8 + k`.

The homeomorphism is `Homeomorph.subtype` applied to
`LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h).toHomeomorph` (the linearly isometric
relabelling of the ambient Euclidean spaces), the hypothesis on the half-space conditions being
the coordinate computation `coord_relabel`.
-/

open scoped Manifold Topology

namespace Work.Tubular

noncomputable section

/-- The relabelling of the coordinates `v ↦ v ∘ (finCongr h).symm` preserves the `0`-th
coordinate, because `(finCongr h).symm 0 = 0`. -/
theorem coord_relabel {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (v : EuclideanSpace ℝ (Fin m)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v) 0 = v 0 := by
  have h0 : (finCongr h).symm 0 = (0 : Fin m) := by
    rw [finCongr_symm_apply]
    exact Fin.cast_zero h.symm
  have hall : ∀ i : Fin n,
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v) i
        = v ((finCongr h).symm i) := by
    intro i
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  rw [show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v) 0
        = (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v).ofLp 0 from rfl,
      hall 0, h0]

/-- **The half-space model depends on its index only by relabelling, preserving the boundary.**

For any equality of indices `h : m = n` (with `m, n ≥ 1`) there is a homeomorphism
`EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace n` — the coordinate relabelling `finCongr h` — which
preserves the `0`-th coordinate, hence maps the boundary hyperplane `{x | x 0 = 0}` to the boundary
hyperplane in both directions. -/
theorem exists_halfSpaceHomeo_boundary_of_eq {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    ∃ Φ : EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace n,
      ∀ x : EuclideanHalfSpace m, (Φ x).val 0 = 0 ↔ x.val 0 = 0 := by
  have hcoord : ∀ v : EuclideanSpace ℝ (Fin m),
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)).toHomeomorph v) 0 = v 0 := by
    intro v
    show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) v) 0 = v 0
    exact coord_relabel h v
  refine ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)).toHomeomorph.subtype ?_, ?_⟩
  · intro v
    rw [hcoord v]
  · intro x
    show ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)).toHomeomorph x.val) 0 = 0
        ↔ x.val 0 = 0
    rw [hcoord x.val]

/-- There is a homeomorphism `EuclideanHalfSpace (7 + k + 1) ≃ₜ EuclideanHalfSpace (8 + k)` of the
two numerically equal half-space models which preserves the boundary hyperplane (the `0`-th
coordinate). -/
theorem exists_halfSpaceHomeo_boundary (k : ℕ) :
    ∃ Φ : EuclideanHalfSpace (7 + k + 1) ≃ₜ EuclideanHalfSpace (8 + k),
      ∀ x : EuclideanHalfSpace (7 + k + 1), (Φ x).val 0 = 0 ↔ x.val 0 = 0 := by
  exact exists_halfSpaceHomeo_boundary_of_eq (by omega : (7 + k + 1 : ℕ) = 8 + k)

end

end Work.Tubular
