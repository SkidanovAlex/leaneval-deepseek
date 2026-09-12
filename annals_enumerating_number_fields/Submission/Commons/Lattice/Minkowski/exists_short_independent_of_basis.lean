import Mathlib
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.Minkowski.covol_span_wedge
import Submission.Commons.Lattice.Minkowski.exists_short_independent
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.Discrete.discreteTopology_span_linIndep
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul

open Module MeasureTheory Metric Submodule
open scoped BigOperators

set_option linter.style.haveILetI false

namespace Commons.Lattice.Minkowski

noncomputable section

/-- An `ℝ`-linearly independent family is `ℤ`-linearly independent (integer relations are
real relations). -/
lemma linearIndependent_int_of_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : ι → E) (h : LinearIndependent ℝ f) :
    LinearIndependent ℤ f := by
  exact LinearIndependent.restrict_scalars (R := ℤ) (K := ℝ) (M := E) (v := f)
    (by
      intro a b hab
      have hab' : (a : ℝ) = (b : ℝ) := by simpa [zsmul_eq_mul] using hab
      exact_mod_cast hab') h

/-- **Top wedge norm via orthonormal coordinates.** If `u : Fin d → E` is an orthonormal
family (`0 < d`) and `w j = ∑ i, A i j • u i`, then `‖ιMulti ℝ d w‖ = |A.det|`. -/
lemma norm_iMulti_eq_abs_det_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {d : ℕ} (hd : 0 < d)
    (u : Fin d → E) (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → E)
    (hu : Orthonormal ℝ u) (hw : ∀ j, w j = ∑ i, A i j • u i) :
    ‖exteriorPower.ιMulti ℝ d w‖ = |A.det| := by
  have hwedge := Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul (K := ℝ) (u := u)
    (A := A) (w := w) hw
  have hn : ‖exteriorPower.ιMulti ℝ d u‖ = 1 :=
    Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal u hu hd
  rw [hwedge, norm_smul, Real.norm_eq_abs, hn, mul_one]

/-- **Covolume of the `ℤ`-span of an `ℝ`-independent family inside its own `ℝ`-span.**
For `w : Fin D → EuclideanSpace ℝ (Fin M)` `ℝ`-linearly independent, with `W := span ℝ (range w)`,
the `ℤ`-span of `w` viewed inside `W` has covolume (for the canonical volume of the inner product
space `W`) equal to the norm of the top exterior power of `w`:
`ZLattice.covolume (span ℤ (range (fun i => ⟨w i, _⟩))) = ‖ιMulti ℝ D w‖`.

Proof: take an orthonormal basis `b₀` of `W` indexed by `Fin D`; its fundamental domain has
volume `1`. The `ℤ`-basis of the `ℤ`-span given by `w` (via `Module.Basis.span`) has coordinate
matrix `A i j = (b₀.repr ⟨w j,_⟩) i` in `b₀`, whence
`ZLattice.covolume_eq_measure_fundamentalDomain` together with
`ZSpan.measureReal_fundamentalDomain` gives `covolume = |A.det|`, while
`norm_iMulti_eq_abs_det_of_orthonormal` (applied to the orthonormal image of `b₀` in the ambient
Euclidean space) gives `‖ιMulti ℝ D w‖ = |A.det|`.  Discreteness of the lattice is transported
from the ambient `ℤ`-span of `w` through the closed embedding `W ↪ EuclideanSpace ℝ (Fin M)`. -/
theorem covolume_zspan_eq_wedge_norm {M D : ℕ} (hD : 0 < D)
    (w : Fin D → EuclideanSpace ℝ (Fin M)) (hv : LinearIndependent ℝ w) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (fun i =>
        (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℝ (Set.range w)))))
      = ‖exteriorPower.ιMulti ℝ D w‖ := by
  classical
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin M)) := Submodule.span ℝ (Set.range w)
  let wW : Fin D → W := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  let L : Submodule ℤ W := Submodule.span ℤ (Set.range wW)
  change ZLattice.covolume L = ‖exteriorPower.ιMulti ℝ D w‖
  have hWfin : Module.finrank ℝ W = D := by
    show Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = D
    rw [finrank_span_eq_card hv]
    simp
  have hwW_real : LinearIndependent ℝ wW := by
    apply LinearIndependent.of_comp W.subtype
    have hcoe : (W.subtype ∘ wW) = w := by funext i; rfl
    rw [hcoe]; exact hv
  have hspan_top : Submodule.span ℝ (Set.range wW) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hwW_real]
    simp [hWfin]
  have hDiscrete : DiscreteTopology L := by
    have hmap : Submodule.map (W.subtype.restrictScalars ℤ) L =
        Submodule.span ℤ (Set.range w) := by
      rw [show L = Submodule.span ℤ (Set.range wW) from rfl, Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨wW i, ⟨i, rfl⟩, rfl⟩
    have hmemLE : ∀ x : L, ((x : W) : EuclideanSpace ℝ (Fin M)) ∈
        Submodule.span ℤ (Set.range w) := by
      intro x
      rw [← hmap]
      exact ⟨x, x.2, rfl⟩
    let f : L → (Submodule.span ℤ (Set.range w)) := fun x => ⟨(x : W), hmemLE x⟩
    have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥(Submodule.span ℤ (Set.range w)) =>
        (y : EuclideanSpace ℝ (Fin M))) hab
    haveI : DiscreteTopology (Submodule.span ℤ (Set.range w)) :=
      Commons.Lattice.Discrete.discreteTopology_span_linIndep w hv
    exact DiscreteTopology.of_continuous_injective hcont hinj
  haveI : DiscreteTopology L := hDiscrete
  haveI : IsZLattice ℝ L := ⟨by
    refine le_antisymm le_top ?_
    rw [← hspan_top]
    refine Submodule.span_mono ?_
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩⟩
  have hfinL : Module.finrank ℤ L = D := by
    rw [ZLattice.rank ℝ L, hWfin]
  let uo : OrthonormalBasis (Fin D) ℝ W :=
    (stdOrthonormalBasis ℝ W).reindex (Fintype.equivFinOfCardEq (by simp [hWfin]))
  let b₀ : Module.Basis (Fin D) ℝ W := uo.toBasis
  have hvol₀ : volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    have hpar : volume (parallelepiped (⇑b₀)) = 1 := by
      have h := uo.volume_parallelepiped
      simpa [b₀, OrthonormalBasis.coe_toBasis] using h
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ volume)]
    rw [measureReal_def, hpar]
    simp
  have huorth : Orthonormal ℝ (fun i => (uo i : EuclideanSpace ℝ (Fin M))) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← Submodule.coe_inner W (uo i) (uo j), orthonormal_iff_ite.mp uo.orthonormal i j]
  have hwW_int : LinearIndependent ℤ wW := linearIndependent_int_of_real wW hwW_real
  let bZ : Module.Basis (Fin D) ℤ L := Module.Basis.span (R := ℤ) (v := wW) hwW_int
  have hbZ : ∀ j, (bZ j : W) = wW j := by
    intro j
    change ((Module.Basis.span hwW_int j : Submodule.span ℤ (Set.range wW)) : W) = wW j
    simp
  let A : Matrix (Fin D) (Fin D) ℝ := fun i j => (b₀.repr (wW j)) i
  have hM : b₀.toMatrix (⇑(Module.Basis.ofZLatticeBasis ℝ L bZ)) = A := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Module.Basis.ofZLatticeBasis_apply, hbZ j]
  have hAw : ∀ j, w j = ∑ i, A i j • (uo i : EuclideanSpace ℝ (Fin M)) := by
    intro j
    have hrepr : wW j = ∑ i, (b₀.repr (wW j)) i • b₀ i :=
      (Module.Basis.sum_repr b₀ (wW j)).symm
    have hcoe := congrArg (fun x : W => (x : EuclideanSpace ℝ (Fin M))) hrepr
    simpa [A, b₀, OrthonormalBasis.coe_toBasis] using hcoe
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L volume
    (ZLattice.isAddFundamentalDomain bZ volume)
  have hdet := ZSpan.measureReal_fundamentalDomain (b := Module.Basis.ofZLatticeBasis ℝ L bZ)
    volume b₀
  rw [hcov, hdet, hvol₀, mul_one, Module.Basis.det_apply, hM]
  exact (norm_iMulti_eq_abs_det_of_orthonormal hD _ A w huorth hAw).symm

-- Minkowski 2nd for the Z-span of an independent integer family: if v : Fin D -> (Fin M -> Z)
-- is R-independent, B bounds the wedge norm of v (equivalently the covolume of the Z-span of v
-- inside its own R-span), and every nonzero element of the Z-span has norm >= 1, then the
-- Z-span contains j R-independent elements (given as integer combinations of the v k) of norm
-- at most (4^D * B / (volume of the D-dimensional unit ball))^(1/(D+1-j)) + 1.
theorem exists_short_independent_of_basis {M D : ℕ} (hD : 0 < D)
    (v : Fin D → (Fin M → ℤ))
    (hv : LinearIndependent ℝ (fun i => (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k => (v i k : ℝ))))
    {B : ℝ}
    (hB : ‖exteriorPower.ιMulti ℝ D (fun i => (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k => (v i k : ℝ)))‖ ≤ B)
    (hB0 : 0 ≤ B)
    (hmin : ∀ a : Fin D → ℤ, a ≠ 0 →
      1 ≤ ‖∑ i, (a i : ℝ) • (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k => (v i k : ℝ))‖)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ D) :
    ∃ b : Fin j → (Fin D → ℤ),
      LinearIndependent ℝ (fun i => ∑ k, (b i k : ℝ) •
        (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k' => (v k k' : ℝ))) ∧
      ∀ i : Fin j, ‖∑ k, (b i k : ℝ) • (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k' => (v k k' : ℝ))‖ ≤
        ((4:ℝ)^D * B / ENNReal.toReal (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin D)) 1)))
          ^ ((1:ℝ) / ((D + 1 - j : ℕ) : ℝ)) + 1 := by
  classical
  set w : Fin D → EuclideanSpace ℝ (Fin M) :=
    fun i => (WithLp.equiv 2 (Fin M → ℝ)).symm (fun k => (v i k : ℝ)) with hw
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin M)) := Submodule.span ℝ (Set.range w)
  let wW : Fin D → W := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  let L : Submodule ℤ W := Submodule.span ℤ (Set.range wW)
  have hWfin : Module.finrank ℝ W = D := by
    show Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = D
    rw [finrank_span_eq_card hv]
    simp
  have hwW_real : LinearIndependent ℝ wW := by
    apply LinearIndependent.of_comp W.subtype
    have hcoe : (W.subtype ∘ wW) = w := by funext i; rfl
    rw [hcoe]; exact hv
  have hspan_top : Submodule.span ℝ (Set.range wW) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hwW_real]
    simp [hWfin]
  have hDiscrete : DiscreteTopology L := by
    have hmap : Submodule.map (W.subtype.restrictScalars ℤ) L =
        Submodule.span ℤ (Set.range w) := by
      rw [show L = Submodule.span ℤ (Set.range wW) from rfl, Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨wW i, ⟨i, rfl⟩, rfl⟩
    have hmemLE : ∀ x : L, ((x : W) : EuclideanSpace ℝ (Fin M)) ∈
        Submodule.span ℤ (Set.range w) := by
      intro x
      rw [← hmap]
      exact ⟨x, x.2, rfl⟩
    let f : L → (Submodule.span ℤ (Set.range w)) := fun x => ⟨(x : W), hmemLE x⟩
    have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥(Submodule.span ℤ (Set.range w)) =>
        (y : EuclideanSpace ℝ (Fin M))) hab
    haveI : DiscreteTopology (Submodule.span ℤ (Set.range w)) :=
      Commons.Lattice.Discrete.discreteTopology_span_linIndep w hv
    exact DiscreteTopology.of_continuous_injective hcont hinj
  haveI : DiscreteTopology L := hDiscrete
  haveI : IsZLattice ℝ L := ⟨by
    refine le_antisymm le_top ?_
    rw [← hspan_top]
    refine Submodule.span_mono ?_
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩⟩
  have hfinL : Module.finrank ℤ L = D := by
    rw [ZLattice.rank ℝ L, hWfin]
  have hcov : ZLattice.covolume L ≤ B := by
    have h1 : ZLattice.covolume L = ‖exteriorPower.ιMulti ℝ D w‖ := by
      simpa [L, wW] using covolume_zspan_eq_wedge_norm (M := M) (D := D) hD w hv
    rw [h1]; exact hB
  have hminL : ∀ y : L, y ≠ 0 → (1 : ℝ) ≤ ‖(y : W)‖ := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ (v := wW) (x := (y : W))).mp y.2
    have hcne : c ≠ 0 := by
      intro hc0
      apply hy
      apply Subtype.ext
      rw [← hc, hc0]
      simp
    have hcoe : ((y : W) : EuclideanSpace ℝ (Fin M)) = ∑ i, (c i : ℝ) • w i := by
      rw [← hc]
      show W.subtype (∑ i, c i • wW i) = ∑ i, (c i : ℝ) • w i
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul]
      exact (Int.cast_smul_eq_zsmul ℝ (c i) (w i)).symm
    calc (1 : ℝ) ≤ ‖∑ i, (c i : ℝ) • w i‖ := hmin c hcne
      _ = ‖(y : W)‖ := by rw [← hcoe]; exact Submodule.norm_coe (y : W)
  have hmin1 : (1 : ℝ) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L 1 :=
    Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge L 1
      le_rfl
      (Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet L 1
        (by rw [hfinL]; exact hD))
      hminL
  haveI : Nontrivial W :=
    ⟨wW ⟨0, hD⟩, 0, hwW_real.ne_zero ⟨0, hD⟩⟩
  obtain ⟨bv, hbvLI, hbvbd⟩ :=
    Commons.Lattice.Minkowski.exists_short_independent (E := W) (d := D) hD L hfinL hcov hB0
      hmin1 j hj hjd
  have hb : ∀ i : Fin j, ∃ c : Fin D → ℤ, ∑ k, c k • wW k = (bv i : W) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ (v := wW) (x := (bv i : W))).mp (bv i).2
  choose b hb using hb
  have hcoe : ∀ i : Fin j, ((bv i : W) : EuclideanSpace ℝ (Fin M)) =
      ∑ k, (b i k : ℝ) • w k := by
    intro i
    rw [← hb i]
    show W.subtype (∑ k, b i k • wW k) = ∑ k, (b i k : ℝ) • w k
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℝ (b i k) (w k)).symm
  refine ⟨b, ?_, ?_⟩
  · have h1 : LinearIndependent ℝ (fun i => ((bv i : W) : EuclideanSpace ℝ (Fin M))) :=
      hbvLI.map' W.subtype (Submodule.ker_subtype W)
    rwa [funext hcoe] at h1
  · intro i
    have hb_i := hbvbd i
    rw [show ‖(bv i : W)‖ = ‖∑ k, (b i k : ℝ) • w k‖ by
      rw [← hcoe i]
      rfl] at hb_i
    rw [show ENNReal.toReal (MeasureTheory.volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin D)) 1))
        = ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : W) 1)) from
      (Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := W) hWfin).symm]
    exact hb_i

end

end Commons.Lattice.Minkowski
