import Mathlib
import Submission.Work.Whitney.CutPush.base_shear

/-!
# The SLICE brick: the *oblique* base shear, and the chord criterion

`CutPush/base_shear.lean` proves the base-cutoff shear for the **orthogonal** projection onto the
base plane: for a smooth `g` with values in `Pᗮ`, the map `y ↦ y - g (pr_P y)` is a global
`C^∞` diffeomorphism and carries the graph of `g` over `P` into `P`.  The SLICE step of the
linear-fibered route (`CutPush/NOTES_linear_fibered_route.md` §2 Step 5) needs exactly this, but the
hypothesis "`pr_P` is injective on the slice" that it comes with is *not* the weakest possible one:
the projection used to read off the graph may be **oblique**.

Here we prove the shear for an *arbitrary* linear projection `π` (an idempotent continuous linear
map) with the correction taking values in `ker π`:

    Φ y = y - g (π y),      Φ⁻¹ y = y + g (π y).

Both maps are `C^∞`, they are mutually inverse, and `Φ` carries the graph of `g` over `π` into
`range π`.  The proof is the same three lines as in the orthogonal case; the only point to notice is
that nothing about `π` is used except `π ∘ π = π`, `π` linear and `g`'s values lying in `ker π`
(after which `π` fixes the "base" coordinate and the fiberwise shift is a translation).

## Why the oblique form matters (the criterion)

Let `D` be a compact slice, `Π` the plane one wants to flatten it into, and `Q` a complement of `Π`
(`Π ⊕ Q = ℝ^N`, `dim Q = codim`-sized).  The **projection onto `Π` along `Q`** is injective on `D`
exactly when

    (D - D) ∩ Q = {0}      ("no chord of `D` lies in `Q`"),

which is *strictly weaker* than the injectivity of the orthogonal projection onto `Π`: the latter
forbids chords in the single plane `Πᗮ`, the former only forbids the chords lying in the chosen `Q`.
The classical obstruction behind the SLICE step -- a helical ribbon of small tilt and small diameter
whose projection to its plane is 2-to-1 (`CutPush/NOTES_STATE_S51.md` §3) -- is exactly a slice whose
"far" chords (the differences between the turns) point out of `Π`; choosing `Q` to avoid those
finitely many directions makes the projection injective, while no choice can make the *orthogonal*
projection injective.  `injOn_of_no_chord` below is the formal content of the criterion, and
`exists_global_diffeo_of_oblique_graph_slice` turns it into the flattening once the graph function is
known (the local-to-global graph-function construction is the other half; see
`CutPush/NOTES_STATE_S51.md` §S51c).
-/

namespace Work.Whitney.CutPush

open scoped ContDiff BigOperators

set_option linter.unusedVariables false

/-- **The oblique base shear is a global diffeomorphism.**  For an idempotent continuous linear map
`π` and a smooth `g` with values in `ker π`, the map `Φ y = y - g (π y)` is a global `C^∞`
diffeomorphism of `ℝ^N` with the explicitly displayed inverse `Φ⁻¹ y = y + g (π y)`. -/
theorem exists_global_diffeo_of_oblique_shear {N : ℕ}
    (π : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hidem : ∀ y, π (π y) = π y)
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hmem : ∀ y, g y ∈ LinearMap.ker π.toLinearMap) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y, Φ y = y - g (π y)) ∧
      (∀ y, Φinv y = y + g (π y)) := by
  have hcorr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => g (π y)) := hg.comp π.contDiff
  have hfix : ∀ y : EuclideanSpace ℝ (Fin N), π (g (π y)) = 0 :=
    fun y => LinearMap.mem_ker.mp (hmem (π y))
  refine ⟨fun y => y - g (π y), fun y => y + g (π y),
    contDiff_id.sub hcorr, contDiff_id.add hcorr, fun y => ?_, fun y => ?_,
    fun y => rfl, fun y => rfl⟩
  · have hbase : π (y - g (π y)) = π y := by
      rw [map_sub, hfix, sub_zero]
    show (y - g (π y)) + g (π (y - g (π y))) = y
    rw [hbase]
    abel
  · have hbase : π (y + g (π y)) = π y := by
      rw [map_add, hfix, add_zero]
    show (y + g (π y)) - g (π (y + g (π y))) = y
    rw [hbase]
    abel

/-- **Oblique graph slices are flattened into the base plane.**  If `D` lies in the graph of `g` over
`π` (i.e. `y - g (π y) ∈ range π` for `y ∈ D`), then some global `C^∞` diffeomorphism of the ambient
space carries `D` into `range π`. -/
theorem exists_global_diffeo_of_oblique_graph_slice {N : ℕ}
    (π : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hidem : ∀ y, π (π y) = π y)
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hmem : ∀ y, g y ∈ LinearMap.ker π.toLinearMap)
    (D : Set (EuclideanSpace ℝ (Fin N)))
    (hD : ∀ y ∈ D, y - g (π y) ∈ LinearMap.range π.toLinearMap) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y ∈ D, Φ y ∈ LinearMap.range π.toLinearMap) := by
  obtain ⟨Φ, Φinv, h1, h2, h3, h4, h5, _⟩ := exists_global_diffeo_of_oblique_shear π hidem g hg hmem
  exact ⟨Φ, Φinv, h1, h2, h3, h4, fun y hy => by rw [h5 y]; exact hD y hy⟩

/-- **The chord criterion.**  If no chord `y - z` (`y, z ∈ D`) of the slice lies in `ker π`, then the
projection `π` is injective on `D`.  This is the hypothesis under which the graph function of the
slice over `range π` is well defined; it is implied by the injectivity of the orthogonal projection
onto `range π`, but is strictly weaker (the chords only have to avoid the one plane `ker π`). -/
theorem injOn_of_no_chord {N : ℕ}
    (π : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (D : Set (EuclideanSpace ℝ (Fin N)))
    (hQ : ∀ y ∈ D, ∀ z ∈ D, y - z ∈ LinearMap.ker π.toLinearMap → y = z) :
    Set.InjOn π D := by
  intro y hy z hz hyz
  refine hQ y hy z hz ?_
  show π.toLinearMap (y - z) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hyz

end Work.Whitney.CutPush
