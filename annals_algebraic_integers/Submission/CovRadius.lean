import Submission.LatticeDefs
import Submission.CovDual
import Submission.CovShort
import Submission.CovExt
import Submission.CovRec

noncomputable section

open scoped BigOperators RealInnerProductSpace NNReal ENNReal
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter

/-!
# Covering-radius bound for a lattice whose dual has first minimum ≥ 1

Task for the sub-agent.  Prove `Submission.CovRadius.coverRadius_bound` stated below.
Do NOT change the statement or name.

Mathematical content (classical geometry of numbers; see the module header comment of
`Submission/GeoCore.lean` for the overall context): for a full-rank `ℤ`-lattice
`L : Submodule ℤ E` in a finite-dimensional real inner product space `E`
(`[DiscreteTopology L] [IsZLattice ℝ L]`), assume the *dual lattice*
`Submission.LatticeDefs.ldual E L := {y | ∀ x ∈ L, ∃ z : ℤ, ⟪x,y⟫ = (z:ℝ)}` (defined in
`Submission.LatticeDefs`) has Euclidean first minimum ≥ 1:
  `hmin : ∀ ⦃y : E⦄, y ∈ Submission.LatticeDefs.ldual E L → y ≠ 0 → 1 ≤ ‖y‖`.
Then the Euclidean covering radius of `L` is `≤ (finrank ℝ E) ^ 5 + 1`, i.e. every point
is within that distance of a lattice point.

## Proof route (all constants LARGE allowed; only polynomial in the dimension is needed)

1. **λ₁λ₁-duality bound (covolume products).** For any lattice `Λ` with dual `Λ* = ldual E Λ`
   in dimension `d ≥ 1`:  `λ₁(Λ) · λ₁(Λ*) ≤ c·d` with `c` absolute.  Standard proof:
   * `ZLattice.covolume Λ · ZLattice.covolume (ldual E Λ) = 1`.  Prove it via a `ℤ`-basis
     `b : Basis ι ℤ L` of `L`; the real extension `b.ofZLatticeBasis ℝ : Basis ι ℝ E`;
     the dual real basis `d := (euclForm E).dualBasis (euclForm_nondegenerate E) bℝ`
     (the inner product viewed as a bilinear form, `Submission.LatticeDefs.euclForm`), and
     `Submission.LatticeDefs.ldual_span_basis` which says the dual of `span ℤ (range b)`
     equals `span ℤ (range d)`; then compare the two covolumes via
     `ZLattice.covolume_eq_measure_fundamentalDomain` (or `_eq_det_mul_measureReal`)
     and the identity  `volume(fundamentalDomain b) · volume(fundamentalDomain d) = 1`
     (true in the canonical volume where orthonormal parallelepipeds have volume 1; prove
     it in coordinates relative to an orthonormal basis `stdOrthonormalBasis ℝ E`, using
     that the coordinate matrices of `b` and `d` satisfy `Uᵀ D = I` — see
     `LinearMap.BilinForm.apply_dualBasis_left` / `dualBasis_repr_apply`).
   * **Minkowski with a cube**: use
     `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
     (or the `≤` compact version) with the symmetric convex compact cube
     `{x | ∀ i, |(o.repr x) i| ≤ r}` (o = orthonormal basis), whose volume is `(2r)^d`,
     to show `λ₁(Λ) ≤ √d · covol(Λ)^{1/d}` up to a harmless absolute constant.
     (Haar measure on `E` is normalized so orthonormal cubes have volume `1`:
     `MeasureTheory.measureSpaceOfInnerProductSpace`, `volume_parallelepiped` etc.
     The measure-space/volume instances need `[MeasurableSpace E] [BorelSpace E]`.)
   * Combine to get `λ₁(L) ≤ c·d` from `hmin` (for an absolute constant `c`, e.g. `c=64`,
     any absolute `c` ≤ 10^9 fine).

2. **Covering-radius recursion (induction on `d = finrank ℝ E`).**  Claim
   `μ₂(L) ≤ (finrank)^5 + 1`.  Inductive step, `d ≥ 1`:
   * Choose `v : E`, `v ∈ L`, `v ≠ 0` with `‖v‖ ≤ c·d` (exists by step 1; `v` can be taken
     a *shortest* nonzero vector of `L`, which then satisfies `L ∩ (ℝ • v) = ℤ • v`).
   * `W := (span ℝ {v})ᗮ` (`Submodule.orthogonal`), `π : E →ₗ[ℝ] W` the orthogonal
     projection (`Submodule.orthogonalProjection`, available when
     `W.HasOrthogonalProjection`, automatic in finite dimension / complete space).
   * The projected lattice `π(L) := Submodule.map (π.restrictScalars ℤ) L : Submodule ℤ W`
     is again a `ℤ`-lattice of `W` (`[DiscreteTopology]`, `[IsZLattice ℝ]`): it is
     discrete (projection along a shortest vector separates points by ≥ ‖v‖/2, or argue
     `π(L) ≅ L / (ℤ • v)`) and spans `W`.  Its dual (in `W`) equals `Submission.LatticeDefs.ldual E L ∩ W`.
   * For every `x : E` decompose `x = x_W + x_v` with `x_W ∈ W`, `x_v ∈ span ℝ {v}`;
     inductively find `m₀ ∈ π(L)` (as an element of `W`, lift to `E`) within
     `(d-1)^5 + 1` of `x_W`; then round the `v`-component: choose `k : ℤ` such that
     `‖x_v - k • v‖ ≤ ‖v‖/2`; conclude `x` is within `(d-1)^5 + 1 + ‖v‖/2 ≤ d^5 + 1`
     of a point of `L`.
   * Base cases `d = 0, 1` trivial/direct.

3. All needed "instances" for submodules/subspaces (e.g. that `W` is an inner product
   space with `MeasurableSpace`/`BorelSpace`, and `[DiscreteTopology (image)]`,
   `[IsZLattice ℝ (image)]` for the projected lattice) must be constructed/proved in this
   file as helper lemmas.  You may write any number of helper definitions/lemmas above
   the theorem.

Useful Mathlib facts (all exist in this Mathlib revision):
  - `Submission.LatticeDefs.ldual`, `.euclForm`, `.euclForm_nondegenerate`,
    `.mem_ldual`, `.ldual_span_basis` (already proved in `Submission/LatticeDefs.lean`).
  - `LinearMap.BilinForm.dualSubmodule`, `.dualSubmodule_span_of_basis`,
    `.dualBasis`, `.dualBasis_repr_apply`, `.apply_dualBasis_left`
    (file `Mathlib.LinearAlgebra.BilinearForm.DualLattice` and `Properties`).
  - `Module.Basis.restrictScalars` : `Basis ι R (span R (range b))`,
    `Module.Basis.ofZLatticeBasis`, `.ofZLatticeBasis_span`.
  - `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_(lt|le)_measure`
    (Minkowski; needs `IsAddFundamentalDomain` which comes from
    `ZSpan.isAddFundamentalDomain b μ` / `ZLattice.isAddFundamentalDomain`),
  - covolumes: `ZLattice.covolume`, `.covolume_eq_measure_fundamentalDomain`,
    `.covolume_pos`; `ZSpan.fundamentalDomain`, `ZSpan.measureReal_fundamentalDomain`,
    `ZSpan.volume_real_fundamentalDomain` (pi-space); `Module.Basis.ofZLatticeBasis`.
  - measure on finite-dim real inner product spaces:
    `MeasureTheory.measureSpaceOfInnerProductSpace` instance,
    `OrthonormalBasis.volume_parallelepiped`, `stdOrthonormalBasis`,
    `(stdOrthonormalBasis ℝ E).measurePreserving_repr(_symm)`,
    `InnerProductSpace.volume_ball`, `EuclideanSpace.volume_ball`.
  - submodule/subspace structure: `Submodule.orthogonal`, `Submodule.orthogonalProjection`,
    `Submodule.orthogonal_eq_bot_iff` etc., `finrank_submodule`/`Submodule.finrank_lt` style
    results for the dimension of `vᗮ` being `d-1` when `v ≠ 0`.

Keep the bound `(finrank ℝ E) ^ 5 + 1` EXACTLY as stated (it is consumed by
`Submission.GeoCore.geo_core`).  You may use any absolute constant ≤ 10^30 inside proofs
as long as the final bound matches.
-/

namespace Submission.CovRadius

open Submission.LatticeDefs
open Submission.CovShort
open Submission.CovExt
open Submission.CovRec






/-- Strong version of the covering bound, for every dimension. -/
lemma coverProp_all (d : ℕ) : coverProp d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases h0 : d = 0
      · subst d
        exact coverProp_zero
      · by_cases h1 : d = 1
        · subst d
          exact coverProp_one
        · have hd : 2 ≤ d := by omega
          have ih' : coverProp (d - 1) := ih (d - 1) (by omega)
          exact coverProp_step d hd ih'

theorem coverRadius_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hmin : ∀ ⦃y : E⦄, y ∈ Submission.LatticeDefs.ldual E L → y ≠ 0 → 1 ≤ ‖y‖) :
    ∀ x : E, ∃ m : E, m ∈ L ∧ ‖x - m‖ ≤ (finrank ℝ E) ^ 5 + 1 := by
  intro x
  let d : ℕ := finrank ℝ E
  have hc : coverProp d := coverProp_all d
  rcases hc L (by dsimp [d]) hmin x with ⟨m, hmL, hb⟩
  refine ⟨m, hmL, ?_⟩
  dsimp [d] at hb
  simpa [Nat.cast_pow, Nat.cast_add] using hb

end Submission.CovRadius
