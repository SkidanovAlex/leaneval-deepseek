import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flow equation at a fixed pair of vectors

`Submission.Diff.dtMet G t x u v` is `deriv (fun s ↦ (G s).inner x u v) t`.  Along a Ricci flow the
metric pairing satisfies `∂_t g = −2 Ric`; since `IsRicciFlow` only gives this as a
`HasDerivWithinAt` on the half-open slab `Ico 0 T`, and an *interior* time `t ∈ Ioo 0 T` makes
`Ico 0 T` a neighbourhood of `t`, it upgrades to a genuine `HasDerivAt`, hence to an identity of
`deriv`s.  This is the bridge between the two equivalent descriptions of `∂_t aOf`:
the `LCVariation` form (`−2 Ric(Δ,·) + ½ Koszul(∇^{G t}Ric)`) and the `Koszul` form (the Koszul
combination of `dtMet`), whose values agree because `dtMet = −2 Ric`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The half-open slab `Ico 0 T` is a neighbourhood of an interior point `t`. -/
theorem Ico_mem_nhds_of_mem_Ioo {T t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    Set.Ico 0 T ∈ 𝓝 t :=
  Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) (fun s hs => ⟨le_of_lt hs.1, hs.2⟩)

/-- **The flow equation at a fixed pair of vectors.** -/
theorem dtMet_eq_of_flow
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (x : M) (u v : TangentSpace I x) :
    dtMet G t x u v = -2 * ricAt (lcOf (G t)) x u v := by
  have h := (hflow.2 t ⟨le_of_lt ht.1, ht.2⟩ x u v).hasDerivAt
    (Ico_mem_nhds_of_mem_Ioo ht)
  simpa only [Submission.Diff.dtMet] using h.deriv

end Work.Diff.EXT.ConnCov
