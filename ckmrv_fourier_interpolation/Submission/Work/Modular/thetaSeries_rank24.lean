import Mathlib
import Submission.Work.Core.Gaussian
import Submission.Work.Lattice.gaussTransformLinearEquiv
import Submission.Work.Lattice.poissonZMod
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.EisensteinDelta
import Submission.Work.Modular.thetaSeries_summable
import Submission.Work.Modular.thetaSeries_mdifferentiable
import Submission.Work.Modular.thetaSeries_T_smul
import Submission.Work.Modular.thetaSeries_atImInfty
import Submission.Work.Modular.thetaSeries_qExpansion_coeff_one
import Submission.Work.Modular.weight12_eq_E12_sub_discriminant
import Submission.Work.Modular.thetaSeries_S_smul_of_gaussian
import Submission.Work.Modular.modularForm_of_slash_invariant

/-!
# The magic of dimension twenty-four

The theta series `Θ_L τ = ∑_{x ∈ L} exp (π i τ ‖x‖²)` of an even unimodular lattice `L ⊆ ℝ²⁴`
without vectors of squared length `2` equals `E₁₂ - (65520/691) Δ`.

The proof has three ingredients.

* **Poisson summation** for `L`: the Gaussian theta sum satisfies `F t = t^{-12} F (1/t)`, where
  `F t = ∑_{x ∈ L} exp (-π t ‖x‖²)`.  This is the classical theta functional equation, obtained
  from Poisson summation on `ℝ²⁴` (reducing via a `ℤ`-basis of `L` to the standard lattice `ℤ²⁴`)
  together with the Gauss sum `∫ exp (-π t ‖v‖²) exp (-2 π i ⟪w, v⟫) = t^{-12} exp (-π ‖w‖² / t)`.
  The prefactor `covolume L` that appears is forced to be `1` by evaluating at `t = 1`.
* **Analytic continuation**: since both sides are holomorphic in `τ` and agree on the imaginary
  axis, `Θ_L (-1/τ) = τ¹² Θ_L τ` on all of `ℍ`.
* **Modular forms**: `Θ_L` is then a level-one modular form of weight `12`, and it has
  `q`-expansion `1 + 0·q + …` (the `q`-coefficient is the number of vectors of squared length `2`),
  which determines it as `E₁₂ - (65520/691) Δ`.

This file collects the elementary algebra of a lattice with a `ℤ`-basis (the standard lattice
`ℤⁿ ⊆ ℝⁿ`, its self-duality, and the dual lattice as the image of `ℤⁿ` under the inverse transpose
of the basis) and the final assembly.
-/

namespace Work.Modular

open Work.Modular
open scoped FourierTransform SchwartzMap RealInnerProductSpace Manifold MatrixGroups ModularForm
open UpperHalfPlane Filter Topology

/-! ## The standard lattice `ℤⁿ ⊆ ℝⁿ` -/

/-- The point of `ℝⁿ` with integer coordinates `v`. -/
noncomputable def znPoint {n : ℕ} (v : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp] theorem znPoint_ofLp {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    (znPoint v).ofLp i = (v i : ℝ) := rfl

theorem inner_znPoint {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℤ) :
    inner ℝ z (znPoint v) = ∑ i, (z.ofLp i * (v i : ℝ)) := by
  rw [show inner ℝ z (znPoint v) = ∑ x, ↑(v x) * z.ofLp x by simp [znPoint, PiLp.inner_apply]]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem inner_znPoint_znPoint {n : ℕ} (w v : Fin n → ℤ) :
    inner ℝ (znPoint w) (znPoint v) = ∑ i, ((w i : ℝ) * (v i : ℝ)) := by
  rw [show inner ℝ (znPoint w) (znPoint v) = ∑ x, ↑(v x) * ↑(w x) by
    simp [znPoint, PiLp.inner_apply]]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem inner_znPoint_single {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    inner ℝ z (znPoint (Pi.single i 1)) = z.ofLp i := by
  rw [inner_znPoint, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem znPoint_injective {n : ℕ} :
    Function.Injective (znPoint : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n)) := by
  intro v w h
  funext i
  have h' := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) h
  simp only [znPoint_ofLp] at h'
  exact_mod_cast h'

/-- The standard lattice `ℤⁿ ⊆ ℝⁿ` is self-dual. -/
theorem dual_znPoint {n : ℕ} {z : EuclideanSpace ℝ (Fin n)} :
    (∀ v : Fin n → ℤ, ∃ m : ℤ, inner ℝ z (znPoint v) = (m : ℝ)) ↔
      ∃ w : Fin n → ℤ, z = znPoint w := by
  constructor
  · intro h
    choose k hk using h
    refine ⟨fun i => k (Pi.single i 1), ?_⟩
    ext i
    have h1 := hk (Pi.single i 1)
    rw [inner_znPoint_single] at h1
    simp only [znPoint_ofLp]
    exact_mod_cast h1
  · rintro ⟨w, rfl⟩ v
    refine ⟨∑ i, w i * v i, ?_⟩
    rw [inner_znPoint_znPoint]
    push_cast
    ring

/-! ## A lattice with a `ℤ`-basis -/

section Basis

variable {n : ℕ} {L : Submodule ℤ (EuclideanSpace ℝ (Fin n))} [DiscreteTopology L]
  [IsZLattice ℝ L] (b : Module.Basis (Fin n) ℤ L)

/-- The `ℝ`-linear equivalence `ℝⁿ → ℝⁿ` sending the standard basis to the given `ℤ`-basis of `L`
(extended to an `ℝ`-basis of `ℝⁿ`). -/
noncomputable def basisEquiv :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans (Module.Basis.ofZLatticeBasis ℝ L b).equivFun.symm

theorem linearEquiv_toLp_apply (f : Fin n → ℝ) :
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) : WithLp 2 (Fin n → ℝ) → (Fin n → ℝ))
      (WithLp.toLp 2 f) = f := by
  rw [WithLp.linearEquiv_apply]
  simp

theorem basisEquiv_znPoint (v : Fin n → ℤ) :
    basisEquiv b (znPoint v) =
      ∑ i, (v i : ℝ) • (Module.Basis.ofZLatticeBasis ℝ L b) i := by
  simp only [basisEquiv, LinearEquiv.trans_apply, znPoint, linearEquiv_toLp_apply,
    Module.Basis.equivFun_symm_apply]

theorem basisEquiv_mem (v : Fin n → ℤ) : basisEquiv b (znPoint v) ∈ L := by
  rw [basisEquiv_znPoint]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Int.cast_smul_eq_zsmul]
  refine Submodule.smul_mem _ _ ?_
  have h1 : (Module.Basis.ofZLatticeBasis ℝ L b) i ∈
      Submodule.span ℤ (Set.range (Module.Basis.ofZLatticeBasis ℝ L b)) :=
    Submodule.subset_span (Set.mem_range_self i)
  rwa [Module.Basis.ofZLatticeBasis_span ℝ L b] at h1

theorem basisEquiv_symm_apply_apply (x : EuclideanSpace ℝ (Fin n)) :
    ((basisEquiv b).symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      (basisEquiv b x) = x :=
  LinearEquiv.symm_apply_apply _ x

theorem basisEquiv_apply_symm_apply (x : EuclideanSpace ℝ (Fin n)) :
    (basisEquiv b : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      ((basisEquiv b).symm x) = x :=
  LinearEquiv.apply_symm_apply _ x

theorem basisEquiv_injective :
    Function.Injective (fun v : Fin n → ℤ => basisEquiv b (znPoint v)) :=
  fun v w h => znPoint_injective ((basisEquiv b).injective h)

theorem basisEquiv_range :
    Set.range (fun v : Fin n → ℤ => basisEquiv b (znPoint v)) = (L : Set _) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact basisEquiv_mem b v
  · intro hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have hA : (Module.Basis.ofZLatticeBasis ℝ L b).equivFun x
        = fun i => ((b.repr ⟨x, hx⟩ i : ℤ) : ℝ) := by
      funext i
      rw [Module.Basis.equivFun_apply]
      simpa using Module.Basis.ofZLatticeBasis_repr_apply ℝ L b ⟨x, hx⟩ i
    show basisEquiv b (znPoint (fun i => b.repr ⟨x, hx⟩ i)) = x
    rw [basisEquiv_znPoint]
    calc ∑ i, ((b.repr ⟨x, hx⟩ i : ℤ) : ℝ) •
            (Module.Basis.ofZLatticeBasis ℝ L b) i
        = ∑ i, (Module.Basis.ofZLatticeBasis ℝ L b).equivFun x i •
            (Module.Basis.ofZLatticeBasis ℝ L b) i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← congrFun hA i]
      _ = x := Module.Basis.sum_equivFun _ x

/-- The bijection `ℤⁿ → L` given by a `ℤ`-basis of `L`. -/
noncomputable def znEquiv : (Fin n → ℤ) ≃ L :=
  Equiv.ofBijective (fun v => ⟨basisEquiv b (znPoint v), basisEquiv_mem b v⟩)
    ⟨fun v w h => basisEquiv_injective b (Subtype.ext_iff.mp h),
      fun x => by
        obtain ⟨v, hv⟩ := Set.mem_range.mp (by rw [basisEquiv_range b]; exact x.2)
        exact ⟨v, Subtype.ext hv⟩⟩

@[simp] theorem znEquiv_apply (v : Fin n → ℤ) :
    ((znEquiv b v : L) : EuclideanSpace ℝ (Fin n)) = basisEquiv b (znPoint v) := rfl

/-- The transpose of the inverse basis: this is the linear map whose image of `ℤⁿ` is the dual
lattice. -/
noncomputable def dualMap : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.adjoint ((basisEquiv b).symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n))

theorem adjoint_comp_dualMap (y : EuclideanSpace ℝ (Fin n)) :
    LinearMap.adjoint ((basisEquiv b : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n))) (dualMap b y) = y := by
  refine ext_inner_left ℝ (fun v => ?_)
  rw [dualMap, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
  congr 1
  exact basisEquiv_symm_apply_apply b v

theorem dualMap_comp_adjoint (y : EuclideanSpace ℝ (Fin n)) :
    dualMap b (LinearMap.adjoint ((basisEquiv b : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n))) y) = y := by
  refine ext_inner_left ℝ (fun v => ?_)
  rw [dualMap, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
  congr 1
  exact basisEquiv_apply_symm_apply b v

/-- The dual lattice of `L` is the image of `ℤⁿ` under the inverse transpose of the basis. -/
theorem dualLattice_eq_range_dualMap :
    (dualLattice L : Set _) = Set.range (fun w : Fin n → ℤ => dualMap b (znPoint w)) := by
  ext y
  constructor
  · intro hy
    have hz : ∃ w : Fin n → ℤ,
        LinearMap.adjoint ((basisEquiv b : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n))) y = znPoint w := by
      rw [← dual_znPoint]
      intro v
      obtain ⟨m, hm⟩ := hy (basisEquiv b (znPoint v)) (basisEquiv_mem b v)
      exact ⟨m, by rw [LinearMap.adjoint_inner_left]; exact hm⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, ?_⟩
    rw [← dualMap_comp_adjoint b y, hw]
  · rintro ⟨w, rfl⟩ x hx
    obtain ⟨u, rfl⟩ := Set.mem_range.mp (by rw [basisEquiv_range b]; exact hx)
    refine ⟨∑ i, w i * u i, ?_⟩
    rw [dualMap, LinearMap.adjoint_inner_left, basisEquiv_symm_apply_apply b (znPoint u),
      inner_znPoint_znPoint]
    push_cast
    ring

/-- The inverse transpose of a basis of `L` maps `ℤⁿ` into the dual lattice. -/
theorem dualMap_mem_dualLattice (w : Fin n → ℤ) : dualMap b (znPoint w) ∈ dualLattice L := by
  intro x hx
  obtain ⟨u, rfl⟩ := Set.mem_range.mp (by rw [basisEquiv_range b]; exact hx)
  refine ⟨∑ i, w i * u i, ?_⟩
  rw [dualMap, LinearMap.adjoint_inner_left, basisEquiv_symm_apply_apply b (znPoint u),
    inner_znPoint_znPoint]
  push_cast
  ring

/-- The bijection `ℤⁿ → L*` given by the inverse transpose of a basis of `L`. -/
noncomputable def dualEquiv : (Fin n → ℤ) ≃ dualLattice L :=
  Equiv.ofBijective
    (fun w => ⟨dualMap b (znPoint w), dualMap_mem_dualLattice b w⟩)
    ⟨fun v w h => znPoint_injective (by
        have h' := congrArg (fun y : EuclideanSpace ℝ (Fin n) =>
          LinearMap.adjoint ((basisEquiv b : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin n))) y) (Subtype.ext_iff.mp h)
        simpa only [adjoint_comp_dualMap] using h'),
      fun y => by
        have hy : (y : EuclideanSpace ℝ (Fin n)) ∈
            Set.range (fun w : Fin n → ℤ => dualMap b (znPoint w)) := by
          rw [← dualLattice_eq_range_dualMap b]
          exact y.2
        obtain ⟨w, hw⟩ := hy
        exact ⟨w, Subtype.ext hw⟩⟩

@[simp] theorem dualEquiv_apply (w : Fin n → ℤ) :
    ((dualEquiv b w : dualLattice L) : EuclideanSpace ℝ (Fin n)) = dualMap b (znPoint w) := rfl

end Basis




/-! ## Poisson summation for the Gaussian -/

section GaussPoisson

variable {L : Submodule ℤ (EuclideanSpace ℝ (Fin 24))} [DiscreteTopology L] [IsZLattice ℝ L]
  (b : Module.Basis (Fin 24) ℤ L)

/-- `exp (-π t ‖x‖²)` is the value at `τ = i t` of the Gaussian Schwartz function. -/
theorem gaussianSchwartz_apply_it (t : ℝ) (ht : 0 < t)
    (hτ : 0 < (↑t * Complex.I : ℂ).im) (x : EuclideanSpace ℝ (Fin 24)) :
    Work.Core.gaussianSchwartz 24 (↑t * Complex.I) hτ x
      = Complex.exp (-(↑(Real.pi * t * ‖x‖ ^ 2) : ℂ)) := by
  rw [Work.Core.gaussianSchwartz_apply, Work.Core.gaussianFun]
  congr 1
  calc ↑Real.pi * Complex.I * (↑t * Complex.I) * ↑(‖x‖ ^ 2)
      = ↑Real.pi * ↑t * (Complex.I * Complex.I) * ↑(‖x‖ ^ 2) := by ring
    _ = -(↑Real.pi * ↑t * ↑(‖x‖ ^ 2)) := by rw [Complex.I_mul_I]; ring
    _ = -(↑(Real.pi * t * ‖x‖ ^ 2) : ℂ) := by push_cast; ring

/-- **Poisson summation for the Gaussian on `L`**, in terms of a `ℤ`-basis `b` of `L`: the theta
sum of `L` is `|det Φ|⁻¹ t^{-12}` times the theta sum of the dual lattice, where `Φ` is the
linear equivalence sending the standard basis of `ℤ²⁴` to `b`. -/
theorem thetaSeries_gauss_poisson {t : ℝ} (ht : 0 < t) :
    (∑' x : L, Complex.exp (-(↑(Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))
      = (((|((LinearEquiv.det (basisEquiv b) : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) *
        ((t ^ (-(12 : ℝ)) : ℝ) : ℂ) *
        (∑' y : dualLattice L,
          Complex.exp (-(↑(Real.pi / t * ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) := by
  classical
  have hτ : 0 < (↑t * Complex.I : ℂ).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero]
    exact ht
  set Φ : EuclideanSpace ℝ (Fin 24) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 24) := basisEquiv b with hΦ
  set hS : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Φ.toContinuousLinearEquiv
      (Work.Core.gaussianSchwartz 24 (↑t * Complex.I) hτ) with hSdef
  have hSapply : ∀ v : EuclideanSpace ℝ (Fin 24),
      hS v = Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖Φ v‖ ^ 2) : ℂ)) := by
    intro v
    rw [hSdef, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    simp only [Function.comp_apply]
    show Work.Core.gaussianSchwartz 24 (↑t * Complex.I) hτ (Φ v) = _
    rw [gaussianSchwartz_apply_it t ht hτ (Φ v)]
    congr 1
    push_cast
    ring
  -- Poisson summation over the standard lattice `ℤ²⁴`
  have hP : (∑' v : Fin 24 → ℤ, hS (znPoint v))
      = ∑' w : Fin 24 → ℤ,
          (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) hS)
            (znPoint w) :=
  Work.Lattice.poissonZMod hS
  have hleft : (∑' v : Fin 24 → ℤ, hS (znPoint v))
      = (∑' x : L,
          Complex.exp (-(↑(Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) := by
    rw [← Equiv.tsum_eq (znEquiv b)
      (fun x : L => Complex.exp (-(↑(Real.pi * t * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))]
    exact tsum_congr (fun v => by
      rw [znEquiv_apply, hSapply]
      congr 1
      push_cast
      ring)
  -- the Fourier transform of the composed Gaussian
  have hfourier : ∀ w : EuclideanSpace ℝ (Fin 24),
      (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) hS) w
        = ∫ v : EuclideanSpace ℝ (Fin 24),
            Complex.exp (-(↑(Real.pi * t) : ℂ) * (↑(‖Φ v‖ ^ 2) : ℂ)) *
              Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I *
                (↑(inner ℝ w v) : ℂ)) := by
    intro w
    rw [show (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) hS) w
        = 𝓕 (hS : EuclideanSpace ℝ (Fin 24) → ℂ) w from rfl, Real.fourier_eq']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [hSapply v]
    have h1 : Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) =
        Complex.exp (-(↑(2 * Real.pi) : ℂ) * Complex.I * (↑(inner ℝ w v) : ℂ)) := by
      congr 1
      rw [real_inner_comm]
      push_cast
      ring
    rw [h1, mul_comm]
  have hright : (∑' w : Fin 24 → ℤ,
        (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) hS) (znPoint w))
      = (((|((LinearEquiv.det (basisEquiv b) : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) *
        ((t ^ (-(12 : ℝ)) : ℝ) : ℂ) *
        (∑' y : dualLattice L,
          Complex.exp (-(↑(Real.pi / t * ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) := by
    have hfr : (-(Module.finrank ℝ (EuclideanSpace ℝ (Fin 24)) : ℝ) / 2) = -12 := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hterm : ∀ w : Fin 24 → ℤ,
        (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) hS) (znPoint w)
          = (((|((LinearEquiv.det (basisEquiv b) : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) *
            ((t ^ (-(12 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(↑(Real.pi / t * ‖dualMap b (znPoint w)‖ ^ 2) : ℂ)) := by
      intro w
      have hgen := Work.Lattice.gaussTransformLinearEquiv_general Φ ht (znPoint w)
      rw [hfourier (znPoint w), hgen, hfr, hΦ]
      have hexp : (-(↑(Real.pi / t) : ℂ) *
            (↑(‖(LinearMap.adjoint ((basisEquiv b).symm :
              EuclideanSpace ℝ (Fin 24) →ₗ[ℝ] EuclideanSpace ℝ (Fin 24))) (znPoint w)‖ ^ 2) : ℂ))
          = -(↑(Real.pi / t * ‖dualMap b (znPoint w)‖ ^ 2) : ℂ) := by
        rw [dualMap]
        push_cast
        ring
      rw [hexp]
    have hsum : (∑' w : Fin 24 → ℤ,
          Complex.exp (-(↑(Real.pi / t * ‖dualMap b (znPoint w)‖ ^ 2) : ℂ)))
        = ∑' y : dualLattice L,
          Complex.exp (-(↑(Real.pi / t * ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)) := by
      rw [← Equiv.tsum_eq (dualEquiv b)
        (fun y : dualLattice L =>
          Complex.exp (-(↑(Real.pi / t * ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))]
      exact tsum_congr (fun w => by rw [dualEquiv_apply])
    rw [tsum_congr hterm, tsum_mul_left, hsum]
  rw [← hleft, hP, hright]

end GaussPoisson


/-! ## The functional equation from Poisson summation -/

section FunctionalEquation

variable {L : Submodule ℤ (EuclideanSpace ℝ (Fin 24))} [DiscreteTopology L]

/-- The theta sum over `L` equals the theta sum over the dual lattice when `L` is self-dual. -/
theorem tsum_dualLattice_eq (hdual : dualLattice L = L)
    (f : EuclideanSpace ℝ (Fin 24) → ℂ) :
    (∑' y : dualLattice L, f y) = ∑' x : L, f x := by
  let e : dualLattice L ≃ L := Equiv.subtypeEquivRight (fun y => by rw [hdual])
  rw [← Equiv.tsum_eq e (fun y : L => f ↑y)]
  exact tsum_congr (fun y => rfl)

variable [IsZLattice ℝ L]

/-- The Gaussian theta sum of a self-dual lattice satisfies the functional equation
`F t = t⁻¹² F (1/t)`.  The Poisson identity `thetaSeries_gauss_poisson` gives it up to an
unknown constant, which is forced to be `1` by evaluating at `t = 1`, where `F 1 ≠ 0` because
`F 1` is the sum of the positive terms `exp (-π ‖x‖²)`. -/
theorem gauss_functional_of_poisson (hdual : dualLattice L = L)
    (b : Module.Basis (Fin 24) ℤ L) :
    ∀ t : ℝ, 0 < t →
      (∑' x : L, Complex.exp (-(↑(Real.pi * t *
          ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))
        = ((t ^ (-(12 : ℝ)) : ℝ) : ℂ) *
          (∑' x : L, Complex.exp (-(↑(Real.pi / t *
            ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) := by
  classical
  -- summability of the real Gaussian, hence positivity of the value at `t = 1`
  have hsumm : Summable (fun x : L =>
      Real.exp (-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2))) := by
    refine (Complex.summable_ofReal).mp ?_
    refine (thetaSeries_summable L
      ⟨Complex.I, by rw [Complex.I_im]; norm_num⟩).congr (fun x => ?_)
    show Complex.exp ((↑Real.pi : ℂ) * Complex.I * Complex.I *
        ↑(‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2))
      = ↑(Real.exp (-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)))
    rw [show (↑Real.pi : ℂ) * Complex.I * Complex.I *
          ↑(‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)
        = ↑(-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)) by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc (↑Real.pi : ℂ) * Complex.I * Complex.I *
              ↑(‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)
          = ↑Real.pi * (Complex.I * Complex.I) *
              ↑(‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) := by ring
        _ = ↑Real.pi * (-1) * ↑(‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) := by rw [hI]
        _ = ↑(-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)) := by push_cast; ring]
    exact (Complex.ofReal_exp _).symm
  have hpos : 0 < ∑' x : L,
      Real.exp (-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)) := by
    have h := hsumm.sum_le_tsum ({0} : Finset L) (fun i _ => Real.exp_nonneg _)
    have h1 : (1 : ℝ) ≤
        ∑' x : L, Real.exp (-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)) := by
      simpa using h
    exact lt_of_lt_of_le zero_lt_one h1
  have hF1 : (∑' x : L, Complex.exp (-(↑(Real.pi *
        ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) ≠ 0 := by
    have hterm : ∀ x : L,
        Complex.exp (-(↑(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)) =
          ↑(Real.exp (-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2))) := by
      intro x
      rw [show (-(↑(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))
          = ↑(-(Real.pi * ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2)) by push_cast; ring]
      exact (Complex.ofReal_exp _).symm
    have hreal : (∑' x : L, Complex.exp (-(↑(Real.pi *
          ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))
        = ↑(∑' x : L, Real.exp (-(Real.pi *
            ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2))) := by
      rw [tsum_congr hterm, Complex.ofReal_tsum]
    rw [hreal]
    exact fun h => (ne_of_gt hpos) (Complex.ofReal_injective (by rw [h, Complex.ofReal_zero]))
  -- evaluate the Poisson identity at `t = 1`
  have h1 := thetaSeries_gauss_poisson b (t := 1) one_pos
  simp only [Real.one_rpow, Complex.ofReal_one, mul_one, div_one] at h1
  rw [tsum_dualLattice_eq hdual (fun y => Complex.exp (-(↑(Real.pi *
    ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ)))] at h1
  have hc : (((|((LinearEquiv.det (basisEquiv b) : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    have hcs : (((|((LinearEquiv.det (basisEquiv b) : ℝˣ) : ℝ)| : ℝ)⁻¹ : ℝ) : ℂ) *
        (∑' x : L, Complex.exp (-(↑(Real.pi *
          ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) =
        (∑' x : L, Complex.exp (-(↑(Real.pi *
          ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))) := h1.symm
    exact mul_right_cancel₀ hF1 (by rw [hcs, one_mul])
  intro t ht
  have h := thetaSeries_gauss_poisson b ht
  rw [tsum_dualLattice_eq hdual (fun y => Complex.exp (-(↑(Real.pi / t *
    ‖(y : EuclideanSpace ℝ (Fin 24))‖ ^ 2) : ℂ))), hc, one_mul] at h
  exact h

end FunctionalEquation

/-! ## The span of a dual lattice -/

section Final

variable {L : Submodule ℤ (EuclideanSpace ℝ (Fin 24))} [DiscreteTopology L]

/-- A lattice whose dual lattice is itself spans `ℝ²⁴` over `ℝ`. -/
theorem span_top_of_dualLattice_eq (hdual : dualLattice L = L) :
    Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin 24))) = ⊤ := by
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin 24)) :=
    Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin 24)))
  have hVL : (L : Set (EuclideanSpace ℝ (Fin 24))) ⊆ V := Submodule.subset_span
  have hsub : Vᗮ ≤ V := by
    intro y hy
    exact hVL (by
      rw [← hdual]
      intro x hx
      refine ⟨0, ?_⟩
      have h0 : inner ℝ x y = 0 := (Submodule.mem_orthogonal _ y).mp hy x (hVL hx)
      rw [real_inner_comm]
      simpa using h0)
  have hbot : Vᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hyV : y ∈ V := hsub hy
    have h0 : inner ℝ y y = 0 := (Submodule.mem_orthogonal _ y).mp hy y hyV
    exact inner_self_eq_zero.mp h0
  exact Submodule.orthogonal_eq_bot_iff.mp hbot

end Final


/-! ## The final assembly -/

section Final

variable {L : Submodule ℤ (EuclideanSpace ℝ (Fin 24))} [DiscreteTopology L]

/-- The `S`-transformation law of the theta series of a self-dual lattice of rank `24`. -/
theorem thetaSeries_S_smul_of_selfdual (hdual : dualLattice L = L)
    [IsZLattice ℝ L] (b : Module.Basis (Fin 24) ℤ L) :
    ∀ τ : ℍ, thetaSeries L (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * thetaSeries L τ := by
  have hfe := gauss_functional_of_poisson hdual b
  have h24 : (-((24 : ℕ) : ℝ) / 2) = -12 := by norm_num
  have h := thetaSeries_S_smul_of_gaussian L (by norm_num : 8 ∣ 24) (fun t ht => by
    rw [h24]
    exact hfe t ht)
  intro τ
  simpa only [show (24 : ℕ) / 2 = 12 by norm_num] using h τ

/-- **The magic of dimension twenty-four**: the theta series of any even unimodular rank-`24`
lattice without vectors of squared length `2` is `E₁₂ - (65520/691) Δ`.  In particular this
applies to the Leech lattice. -/
theorem thetaSeries_rank24 {L : Submodule ℤ (EuclideanSpace ℝ (Fin 24))} [DiscreteTopology L]
    (hdual : dualLattice L = L) (heven : IsEvenSubmodule L)
    (hmin : ∀ x ∈ L, ‖(x : EuclideanSpace ℝ (Fin 24))‖ ^ 2 ≠ 2) :
    thetaSeries L = fun τ => E12 τ - (65520 / 691) * Delta τ := by
  classical
  haveI : IsZLattice ℝ L := ⟨span_top_of_dualLattice_eq hdual⟩
  let b : Module.Basis (Fin 24) ℤ L := (Module.Free.chooseBasis ℤ L).reindex
    (Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
      simpa using finrank_euclideanSpace_fin))
  have hS : ∀ τ : ℍ, thetaSeries L (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * thetaSeries L τ :=
    thetaSeries_S_smul_of_selfdual hdual b
  -- the two generators of `SL(2, ℤ)`
  have hSslash : thetaSeries L ∣[(12 : ℤ)] ModularGroup.S = thetaSeries L := by
    funext z
    rw [ModularForm.slash_action_eq'_iff, hS z]
    have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
    have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
    rw [h10, h11]
    simp
  have hTslash : thetaSeries L ∣[(12 : ℤ)] ModularGroup.T = thetaSeries L := by
    funext z
    rw [ModularForm.slash_action_eq'_iff, thetaSeries_T_smul L heven z]
    have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
    have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
    rw [h10, h11]
    simp
  have hper : ∀ γ : SL(2, ℤ), thetaSeries L ∣[(12 : ℤ)] γ = thetaSeries L :=
    SlashInvariantForm.slash_action_generators_SL2Z hSslash hTslash
  have hhol : MDiff (thetaSeries L) := thetaSeries_mdifferentiable L
  have htend := thetaSeries_atImInfty L
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty (thetaSeries L) := by
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    have hnorm : Tendsto (fun z : ℍ => ‖thetaSeries L z‖) UpperHalfPlane.atImInfty (𝓝 1) := by
      simpa using htend.norm
    have h1 : {z : ℍ | ‖thetaSeries L z‖ ≤ 2} ∈ UpperHalfPlane.atImInfty := by
      have hmem2 : Set.Iic (2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
        mem_of_superset (IsOpen.mem_nhds isOpen_Iio (by norm_num)) Set.Iio_subset_Iic_self
      filter_upwards [hnorm.eventually hmem2] with z hz
      exact hz
    rw [UpperHalfPlane.atImInfty_mem] at h1
    obtain ⟨A, hA⟩ := h1
    exact ⟨2, A, fun z hz => hA z hz⟩
  obtain ⟨g, hg⟩ := modularForm_of_slash_invariant (k := 12) hper hhol hbdd
  have hperg : Function.Periodic ((⇑g : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := g) one_mem_strictPeriods_SL
  have hholg : MDiff (⇑g : ℍ → ℂ) := by rw [hg]; exact hhol
  have hbddg : UpperHalfPlane.IsBoundedAtImInfty (⇑g : ℍ → ℂ) := by rw [hg]; exact hbdd
  have hanal : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑g : ℍ → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperg hholg hbddg
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 0 = 1 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hanal hperg]
    rw [show UpperHalfPlane.valueAtInfty (⇑g : ℍ → ℂ) = 1 from by
      rw [UpperHalfPlane.valueAtInfty, hg]
      exact htend.limUnder_eq]
  have hperg' : Function.Periodic ((thetaSeries L) ∘ UpperHalfPlane.ofComplex) 1 := by
    rw [← hg]
    exact hperg
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑g : ℍ → ℂ)).coeff 1 = 0 := by
    rw [hg]
    exact thetaSeries_qExpansion_coeff_one L hperg' hhol hbdd heven hmin
  have hE := weight12_eq_E12_sub_discriminant g h0 h1
  rw [hg] at hE
  exact hE

end Final

end Work.Modular
