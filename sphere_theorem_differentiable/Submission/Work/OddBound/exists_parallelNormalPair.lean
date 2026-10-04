import Mathlib
import Submission.Work.OddBound.IndexBound
import Submission.Work.OddBound.ParallelKit

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two parallel normal fields along a geodesic (the odd-dimensional Klingenberg input)

`Work.OddBound.IndexBound` records the *index computation* of the odd-dimensional Klingenberg
length bound: two independent *parallel* unit normal fields along a closed geodesic give two
Dirichlet fields with negative index integral, hence index at least two.  That reduction needs the
fields to exist, and this module supplies them.

`Work.OddBound.exists_parallelNormalPair`: along **any** `C^∞` geodesic `γ` with non-vanishing
velocity in a manifold of dimension `≥ 3`, and for any window `[-1, L+1]` (`-1 < L`), there are two
smooth fields `X₁, X₂` along `γ`, parallel on `[0,L]`, unit and normal to `γ'` on `[0,L]`, and pointwise
independent.  Unlike Synge's fixed vector of the even-dimensional argument, no periodicity
(`X_j L = X_j 0`) is required — the Dirichlet fields `sin (π s / L) • X_j` are periodic for free.

## The construction

At the time `C.c 0` of a chart cover of `γ` over `[-1, L+1]` (note `C.c 0 = -1 < L`), the normal
space of the velocity is a subspace of codimension one of a space of dimension `≥ 3`, so it contains
an orthonormal pair `e₁ ⊥ e₂ ⊥ γ'` (`exists_orthonormal_pair_orthogonal`, a two-line application of
`stdOrthonormalBasis` to the orthogonal complement of `ℝ ∙ γ'`).  Their chart coordinates
`v_j = (trivializationAt ...).continuousLinearMapAt ℝ (γ (C.c 0)) e_j` are the data of the global
parallel fields `parallelFieldR htor C hN v_j`, which are

* smooth on `[-1, L+1]` (`parallelFieldR_spec`),
* parallel on `[-1, L+1]` (idem),
* of *constant* norm `1` and *constant* pairing with the velocity `0`, by the isometry
  (`norm_parallelField`) and bilinear Gram constancy (`inner_parallelField_eq`) of the parallel
  transport, together with the identification of the velocity with the parallel extension of
  `deriv (coordCurve C 0) (C.c 0)` (`velocity_eq_parallelField`,
  `frameVector_deriv_coordCurve_eq_curveVelocity`),
* pointwise independent, since otherwise the bilinear Gram constancy would force
  `inner ℝ e₁ e₂ = 0` and `= c` simultaneously (and `|c| = ‖e₂‖/‖e₁‖ = 1` while `c = 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

/-- **An orthonormal pair orthogonal to a nonzero vector.**  In a real inner product space of
dimension `≥ 3`, every nonzero vector `u` admits two orthonormal vectors orthogonal to it: the
orthogonal complement `(ℝ ∙ u)ᗮ` has dimension `finrank - 1 ≥ 2`, and the first two vectors of an
orthonormal basis of it are the required pair. -/
lemma exists_orthonormal_pair_orthogonal {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {u : F} (hu : u ≠ 0) (h3 : 3 ≤ Module.finrank ℝ F) :
    ∃ e1 e2 : F, ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ inner ℝ e1 e2 = 0 ∧
      inner ℝ e1 u = 0 ∧ inner ℝ e2 u = 0 := by
  have hdim : Module.finrank ℝ ↥((ℝ ∙ u)ᗮ) = Module.finrank ℝ F - 1 := by
    have h1 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := F) (ℝ ∙ u)
    omega
  have h2le : 2 ≤ Module.finrank ℝ ↥((ℝ ∙ u)ᗮ) := by omega
  have hne0 : NeZero (Module.finrank ℝ ↥((ℝ ∙ u)ᗮ)) := ⟨by omega⟩
  let b := stdOrthonormalBasis ℝ ↥((ℝ ∙ u)ᗮ)
  have hmem : ∀ i : Fin (Module.finrank ℝ ↥((ℝ ∙ u)ᗮ)),
      inner ℝ ((b i : ↥((ℝ ∙ u)ᗮ)) : F) u = 0 := by
    intro i
    have hi : ((b i : ↥((ℝ ∙ u)ᗮ)) : F) ∈ (ℝ ∙ u)ᗮ := (b i).2
    rw [Submodule.mem_orthogonal'] at hi
    exact hi u (Submodule.mem_span_singleton_self u)
  exact ⟨_, _, b.orthonormal.1 ⟨0, by omega⟩, b.orthonormal.1 ⟨1, by omega⟩,
    b.orthonormal.2 (by simp [Fin.ext_iff]), hmem ⟨0, by omega⟩, hmem ⟨1, by omega⟩⟩

/-- **Two independent parallel unit normal fields along a geodesic.**  Along a `C^∞` geodesic with
non-vanishing velocity in a manifold of dimension `≥ 3`, for every window `[-1, L+1]` with `-1 < L`
there is a parallel normal pair, smooth on `[-1, L+1]` and with the pair of fields isometric,
bilinear-constant, unit, normal and independent on `[0,L]`.

The construction transports the orthonormal normal pair of `γ` at the base time `C.c 0` of a chart
cover of `[-1, L+1]` (see the module docstring). -/
theorem exists_parallelNormalPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ∞ γ Set.univ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {L : ℝ} (hL : -1 < L) (h3 : 3 ≤ Module.finrank ℝ E) :
    Work.OddBound.ExistsParallelNormalPair (I := I) (cov := cov) γ L := by
  -- a chart cover of the geodesic on the enlarged window `[-1, L+1]`
  have hab : (-1 : ℝ) < L + 1 := by linarith
  obtain ⟨C⟩ : Nonempty (Submission.ParallelGlobal.GeodesicCover cov γ (-1) (L + 1)) :=
    Submission.ParallelGlobal.exists_geodesicCover (cov := cov) (a := -1) (b := L + 1)
      isOpen_univ (le_of_lt hab) (fun _ _ => mem_univ _) hγsm
      (fun t _ => hgeo t) (fun t _ => hne t)
  have hN : 0 < C.N := by
    by_contra h
    have h0 : C.N = 0 := by omega
    have hcc : C.c 0 = C.c C.N := by rw [h0]
    rw [C.c_zero, C.c_last] at hcc
    linarith
  have hγ1 : ∀ k < C.N, ∀ t ∈ Set.Ioo (Submission.ParallelRoom.roomA C k)
      (Submission.ParallelRoom.roomB C k),
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I ∞ γ (Set.Ioo (t - 1) (t + 1)) :=
    fun k hk t ht => hγsm.mono (Set.subset_univ _)
  have hne1 : ∀ k < C.N, ∀ t ∈ Set.Ioo (Submission.ParallelRoom.roomA C k)
      (Submission.ParallelRoom.roomB C k), Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0 :=
    fun k hk t ht => hne t
  -- the base point of the cover lies in the chart at `C.x 0`
  have hsrc : γ (C.c 0) ∈ (chartAt H (C.x 0)).source :=
    C.src 0 hN (C.c 0) (Submission.ParallelGlobal.piece_subset_room (cov := cov) C hN
      ⟨le_rfl, (C.mono 0 hN).le⟩)
  have hsrcE : γ (C.c 0) ∈ (extChartAt I (C.x 0)).source := by rwa [extChartAt_source]
  -- the velocity at the base point, in the chart at `C.x 0`
  have hV : Submission.Geodesic.frameVector (I := I) (C.x 0) (γ (C.c 0))
      (deriv (Submission.ParallelGlobal.coordCurve (I := I) C 0) (C.c 0))
      = Submission.Geodesic.curveVelocity (I := I) γ (C.c 0) :=
    Submission.ParallelGlobal.frameVector_deriv_coordCurve_eq_curveVelocity (cov := cov) C hN
      (Submission.ParallelGlobal.piece_subset_room (cov := cov) C hN ⟨le_rfl, (C.mono 0 hN).le⟩)
  -- an orthonormal pair in the normal space of the velocity at the base point
  have hfin : FiniteDimensional ℝ (TangentSpace I (γ (C.c 0))) := ‹FiniteDimensional ℝ E›
  obtain ⟨e₁, e₂, he1, he2, he12, he1u, he2u⟩ :=
    exists_orthonormal_pair_orthogonal (u := Submission.Geodesic.curveVelocity (I := I) γ (C.c 0))
      (hne (C.c 0)) h3
  -- their chart coordinates, and their images under the frame
  set v₁ : E := (trivializationAt E (TangentSpace I) (C.x 0)).continuousLinearMapAt ℝ
      (γ (C.c 0)) e₁ with hv₁
  set v₂ : E := (trivializationAt E (TangentSpace I) (C.x 0)).continuousLinearMapAt ℝ
      (γ (C.c 0)) e₂ with hv₂
  have hfv₁ : Submission.Geodesic.frameVector (I := I) (C.x 0) (γ (C.c 0)) v₁ = e₁ := by
    rw [hv₁]; exact Submission.GExpFlow.frameVector_clm (I := I) hsrcE e₁
  have hfv₂ : Submission.Geodesic.frameVector (I := I) (C.x 0) (γ (C.c 0)) v₂ = e₂ := by
    rw [hv₂]; exact Submission.GExpFlow.frameVector_clm (I := I) hsrcE e₂
  -- the two global parallel fields: smooth and parallel on `[-1, L+1]`
  have hspec₁ := Submission.ParallelRoom.parallelFieldR_spec (cov := cov) hmet htor C hN v₁ hγ1 hne1
  have hspec₂ := Submission.ParallelRoom.parallelFieldR_spec (cov := cov) hmet htor C hN v₂ hγ1 hne1
  have hmem : ∀ t ∈ Icc (0:ℝ) L, t ∈ Icc (C.c 0) (C.c C.N) := fun t ht =>
    ⟨by rw [C.c_zero]; linarith [ht.1], by rw [C.c_last]; linarith [ht.2]⟩
  have hmemL : ∀ t ∈ Icc (0:ℝ) L, t ∈ Icc (-1) (L + 1) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpar₁ : ∀ t ∈ Icc (0:ℝ) L,
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁ t
        = Submission.ParallelGlobal.parallelField htor C hN v₁ t :=
    fun t ht => Submission.ParallelRoom.parallelFieldR_eq_parallelField (cov := cov) htor C hN v₁ (hmem t ht)
  have hpar₂ : ∀ t ∈ Icc (0:ℝ) L,
      Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂ t
        = Submission.ParallelGlobal.parallelField htor C hN v₂ t :=
    fun t ht => Submission.ParallelRoom.parallelFieldR_eq_parallelField (cov := cov) htor C hN v₂ (hmem t ht)
  -- unit and normal on `[0,L]`, by the isometry and the bilinear Gram constancy of the transport
  have hunit₁ : IsUnitNormalField (I := I) γ L
      (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hpar₁ t ht, Submission.ParallelGlobal.norm_parallelField (cov := cov) hmet C htor hN v₁ (hmem t ht),
        hfv₁, he1]
    · rw [hpar₁ t ht, Submission.HolDet.velocity_eq_parallelField (cov := cov) htor C hN (hmem t ht),
        Submission.HolDet.inner_parallelField_eq (cov := cov) hmet htor C hN v₁
          (deriv (Submission.ParallelGlobal.coordCurve (I := I) C 0) (C.c 0)) (hmem t ht),
        hfv₁, hV, he1u]
  have hunit₂ : IsUnitNormalField (I := I) γ L
      (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hpar₂ t ht, Submission.ParallelGlobal.norm_parallelField (cov := cov) hmet C htor hN v₂ (hmem t ht),
        hfv₂, he2]
    · rw [hpar₂ t ht, Submission.HolDet.velocity_eq_parallelField (cov := cov) htor C hN (hmem t ht),
        Submission.HolDet.inner_parallelField_eq (cov := cov) hmet htor C hN v₂
          (deriv (Submission.ParallelGlobal.coordCurve (I := I) C 0) (C.c 0)) (hmem t ht),
        hfv₂, hV, he2u]
  -- pointwise independence
  have hindep : ∀ t ∈ Icc (0:ℝ) L,
      ¬ ∃ c : ℝ, Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂ t
        = c • Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁ t := by
    intro t ht hcon
    obtain ⟨c, hc⟩ := hcon
    have hn₁ : ‖Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁ t‖ = 1 :=
      (hunit₁ t ht).1
    have hn₂ : ‖Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂ t‖ = 1 :=
      (hunit₂ t ht).1
    have habs : |c| = 1 := by
      have h := congrArg Norm.norm hc
      rw [hn₂, norm_smul, Real.norm_eq_abs, hn₁, mul_one] at h
      exact h.symm
    have hi0 : inner ℝ (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁ t)
        (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂ t) = 0 := by
      rw [hpar₁ t ht, hpar₂ t ht,
        Submission.HolDet.inner_parallelField_eq (cov := cov) hmet htor C hN v₁ v₂ (hmem t ht),
        hfv₁, hfv₂, he12]
    have hi1 : inner ℝ (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁ t)
        (Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂ t) = c := by
      rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hn₁]
      ring
    have hc0 : c = 0 := by linarith [hi0, hi1]
    rw [hc0] at habs
    norm_num at habs
  exact ⟨{ X₁ := Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₁
           X₂ := Submission.ParallelRoom.parallelFieldR (cov := cov) htor C hN v₂
           smooth₁ := hspec₁.1
           smooth₂ := hspec₂.1
           parallel₁ := fun t ht => hspec₁.2 t (hmemL t ht)
           parallel₂ := fun t ht => hspec₂.2 t (hmemL t ht)
           unitNormal₁ := hunit₁
           unitNormal₂ := hunit₂
           independent := hindep }⟩

end

end Work.OddBound
