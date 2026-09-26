import Mathlib
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.Poisson.Std
import Submission.Work.Modular.Poisson.TorusInversion
import Submission.Work.Modular.Poisson.Periodize
import Submission.Work.Modular.Poisson.Fund
import Submission.Work.Poisson.covolume_intLatticeE
import Submission.Work.Poisson.dualLattice_eq_T
import Submission.Work.Poisson.covolume_eq_det_inv
import Submission.Work.Poisson.fourier_eq_integral_periodize
import Submission.Work.Poisson.integral_mFourier_periodize
import Submission.Work.Poisson.summable_fourier_adjoint

/-!
# Poisson summation for a lattice in `EuclideanSpace ℝ (Fin n)`

We prove `∑_{x ∈ L} f x = (covolume L)⁻¹ ∑_{y ∈ L*} f̂ y`.
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Work.Modular

/-- Every lattice in `EuclideanSpace ℝ (Fin n)` is the preimage of `ℤⁿ` under a linear
equivalence. -/
theorem exists_endomorphism {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤) :
    ∃ d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ intLatticeE (Fin n) := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L,
      finrank_euclideanSpace_fin]
  let b : Module.Basis (Fin n) ℤ L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq (by simpa using hcard))
  let b₀ : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := b.ofZLatticeBasis ℝ L
  let c : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := b₀.equivFun
  have hbmap : b₀.map c = Pi.basisFun ℝ (Fin n) := by
    ext i
    simp only [c, Module.Basis.map_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.basisFun_apply, Finsupp.single_eq_pi_single]
  have hspanb : Submodule.span ℤ (Set.range b₀) = L :=
    Module.Basis.ofZLatticeBasis_span ℝ L b
  have hmap : Submodule.map ((c.restrictScalars ℤ :
      EuclideanSpace ℝ (Fin n) →ₗ[ℤ] (Fin n → ℝ)))
      (Submodule.span ℤ (Set.range b₀)) = stdLattice (Fin n) := by
    rw [ZSpan.map b₀ c, hbmap]
    rfl
  refine ⟨c.trans (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.symm, fun x => ?_⟩
  have h1 : EuclideanSpace.equiv (Fin n) ℝ
      ((c.trans (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.symm) x) = c x := by
    rw [LinearEquiv.trans_apply]
    exact LinearEquiv.apply_symm_apply _ _
  rw [mem_intLatticeE_iff, h1]
  constructor
  · intro hx
    have hx1 : c x ∈ Submodule.map ((c.restrictScalars ℤ :
        EuclideanSpace ℝ (Fin n) →ₗ[ℤ] (Fin n → ℝ))) (Submodule.span ℤ (Set.range b₀)) :=
      ⟨x, by rwa [hspanb], rfl⟩
    rwa [hmap] at hx1
  · intro hx
    have hx1 : c x ∈ Submodule.map ((c.restrictScalars ℤ :
        EuclideanSpace ℝ (Fin n) →ₗ[ℤ] (Fin n → ℝ))) (Submodule.span ℤ (Set.range b₀)) := by
      rwa [hmap]
    obtain ⟨y, hy, hyx⟩ := hx1
    rw [hspanb] at hy
    have hyx' : y = x := by
      have h2 : c y = c x := by simpa using hyx
      calc y = c.symm (c y) := (c.symm_apply_apply y).symm
        _ = c.symm (c x) := by rw [h2]
        _ = x := c.symm_apply_apply x
    rwa [hyx'] at hy

/-- **Poisson summation for a lattice**, reduced to the case where the lattice is the image of
`ℤⁿ` under a linear equivalence. -/
theorem poissonSummation_of_endomorphism {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ intLatticeE (Fin n))
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∑' x : L, f x = (covolume L)⁻¹ *
      ∑' y : dualLattice L, 𝓕 f y := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  set G : (Fin n → ℝ) → ℂ := fun y => periodize L f ((coordMap d).symm y) with hG
  have hdual : ∀ y : EuclideanSpace ℝ (Fin n),
      y ∈ dualLattice L ↔ ∃ k : Fin n → ℤ, y = LinearMap.adjoint d.toLinearMap (intVecE k) :=
    Work.Poisson.dualLattice_eq_T L hspan d hd
  have hTfun : ∀ k : Fin n → ℤ,
      LinearMap.adjoint d.toLinearMap (intVecE k) ∈ dualLattice L := fun k =>
    (hdual _).mpr ⟨k, rfl⟩
  have hcomp : ∀ k : Fin n → ℤ,
      LinearMap.adjoint d.symm.toLinearMap
        (LinearMap.adjoint d.toLinearMap (intVecE k)) = intVecE k := by
    intro k
    refine ext_inner_right ℝ fun u => ?_
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
    simp
  have hinjT : Function.Injective fun k : Fin n → ℤ =>
      LinearMap.adjoint d.toLinearMap (intVecE k) := by
    intro k₁ k₂ h
    have h3 : intVecE k₁ = intVecE k₂ := by
      rw [← hcomp k₁, ← hcomp k₂]
      exact congrArg (fun x => LinearMap.adjoint d.symm.toLinearMap x) h
    funext i
    have h4 : ((k₁ i : ℝ)) = ((k₂ i : ℝ)) := by
      have := congrFun (congrArg WithLp.ofLp h3) i
      simpa [intVec] using this
    exact_mod_cast h4
  let e : (Fin n → ℤ) ≃ ↥(dualLattice L) :=
    Equiv.ofBijective
      (fun k => (⟨LinearMap.adjoint d.toLinearMap (intVecE k), hTfun k⟩ : ↥(dualLattice L)))
      ⟨fun k₁ k₂ h => hinjT (Subtype.ext_iff.mp h),
        fun y => by
          obtain ⟨k, hk⟩ := (hdual (y : EuclideanSpace ℝ (Fin n))).mp y.2
          exact ⟨k, Subtype.ext hk.symm⟩⟩
  have hcoeff : ∀ k : Fin n → ℤ,
      (∫ y in unitCube (ι := Fin n),
        UnitAddTorus.mFourier (-k) (projTorus y) • G y)
      = ((|LinearMap.det d.toLinearMap| : ℝ) : ℂ) *
        𝓕 f (LinearMap.adjoint d.toLinearMap (intVecE k)) := by
    intro k
    rw [hG]
    rw [Work.Poisson.integral_mFourier_periodize L hspan d hd f k]
    have hA := Work.Poisson.fourier_eq_integral_periodize L hspan d hd f
      (LinearMap.adjoint d.toLinearMap (intVecE k)) (hTfun k)
    simp only [FourierTransform.fourierCLM_apply] at hA
    rw [← hA]
  have hsum_int : Summable fun k : Fin n → ℤ =>
      ∫ y in unitCube (ι := Fin n), UnitAddTorus.mFourier (-k) (projTorus y) • G y := by
    have h1 : Summable fun k : Fin n → ℤ =>
        ((|LinearMap.det d.toLinearMap| : ℝ) : ℂ) *
          𝓕 f (LinearMap.adjoint d.toLinearMap (intVecE k)) := by
      simpa only [FourierTransform.fourierCLM_apply] using
        (Work.Poisson.summable_fourier_adjoint d f).mul_left
          ((|LinearMap.det d.toLinearMap| : ℝ) : ℂ)
    exact h1.congr fun k => (hcoeff k).symm
  have hGcont : Continuous G := by
    rw [hG]
    exact (periodize L f).continuous.comp (LinearMap.continuous_of_finiteDimensional
      ((coordMap d).symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  have hGper : ∀ (y : Fin n → ℝ) (m : Fin n → ℤ), G (y + intVec m) = G y := by
    intro y m
    simp only [hG]
    rw [map_add]
    refine periodize_periodic L f ((coordMap d).symm y)
      ⟨(coordMap d).symm (intVec m), ?_⟩
    refine (hd _).mpr ?_
    rw [coordMap_symm_apply, LinearEquiv.apply_symm_apply, mem_intLatticeE]
    exact fun i => ⟨m i, rfl⟩
  have hInv := hasSum_mFourier_series_of_periodic hGcont hGper hsum_int
  have hG0 : G 0 = ∑' x : L, f x := by
    simp only [hG]
    rw [show (coordMap d).symm 0 = 0 from map_zero _]
    rw [periodize_apply L f]
    simp
  have hcov : covolume L = |LinearMap.det d.toLinearMap|⁻¹ :=
    Work.Poisson.covolume_eq_det_inv L hspan d hd
  have hbij : (∑' k : Fin n → ℤ,
        𝓕 f (LinearMap.adjoint d.toLinearMap (intVecE k)))
      = ∑' y : ↥(dualLattice L), 𝓕 f (y : EuclideanSpace ℝ (Fin n)) := by
    have h := Equiv.tsum_eq e (fun y : ↥(dualLattice L) =>
      𝓕 f (y : EuclideanSpace ℝ (Fin n)))
    rw [show (∑' c : Fin n → ℤ, (fun y : ↥(dualLattice L) =>
          𝓕 f (y : EuclideanSpace ℝ (Fin n))) (e c))
        = ∑' c : Fin n → ℤ, 𝓕 f (LinearMap.adjoint d.toLinearMap (intVecE c))
        from tsum_congr fun c => rfl] at h
    exact h
  rw [← hG0, hInv,
    show (∑' k : Fin n → ℤ, ∫ y in unitCube (ι := Fin n),
          UnitAddTorus.mFourier (-k) (projTorus y) • G y)
        = ∑' k : Fin n → ℤ, ((|LinearMap.det d.toLinearMap| : ℝ) : ℂ) *
            𝓕 f (LinearMap.adjoint d.toLinearMap (intVecE k))
        from tsum_congr fun k => hcoeff k,
    tsum_mul_left, hbij, hcov, inv_inv]

/-- **Poisson summation for a lattice** in `EuclideanSpace ℝ (Fin n)`. -/
theorem poissonSummation_lattice_gen {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∑' x : L, f x = (covolume L)⁻¹ * ∑' y : dualLattice L, 𝓕 f y := by
  obtain ⟨d, hd⟩ := exists_endomorphism L hspan
  exact poissonSummation_of_endomorphism L hspan d hd f

end Work.Modular
