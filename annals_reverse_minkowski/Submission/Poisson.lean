import Mathlib
import ChallengeDeps
import Submission.VoronoiMeasure
import Submission.Commons.Lattice.PoissonSummation.lattice_psf
import Submission.Commons.Lattice.PoissonSummation.lattice_shifted_mass_le
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Algebra.Module.ZLattice.Covolume

open Module MeasureTheory Metric
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false

/-!
# Poisson summation block (paper §2.3)

Target (to be proven in this module):

    ρ_s(ℒ) = sⁿ · ρ_{1/s}(ℒ*) / det ℒ

where `ℒ ≤ E = EuclideanSpace ℝ (Fin n)` is a full-rank `ℤ`-lattice,
`ℒ* := {x | ∀ y ∈ ℒ, ⟨x,y⟩ ∈ ℤ}` is its dual lattice, `ρ_s(ℒ) = Σ_{y∈ℒ} e^{-π‖y‖²/s²}`,
`det ℒ = √(det(BᵀB))`, and `E` is identified with its own dual through the inner product.

Consequences needed later:
* shifted mass (Banaszczyk / paper Claim): `∀ u ∈ E, ρ_s(ℒ − u) ≤ ρ_s(ℒ)`;
* `direct_sum_rho`: for primitive `ℒ′ ≤ ℒ`: `ρ_s(ℒ) ≤ ρ_s(ℒ′)·ρ_s(ℒ/ℒ′)`.

Mathlib provides the 1-dimensional Poisson summation / Jacobi theta
transformation (`Real.tsum_exp_neg_mul_int_sq`, `Complex.tsum_exp_neg_quadratic`);
the n-dimensional lattice version is built in this module.
-/

namespace Submission.Poisson

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The Gaussian mass `ρ_s(ℒ)` (ambient-norm form, equals `ReverseMinkowski.ρ` by `rfl`). -/
noncomputable def rhoVal (s : ℝ) (ℒ : Submodule ℤ E) : ℝ :=
  ∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)

/-- A real number is an integer. -/
def IsInt (z : ℝ) : Prop := ∃ k : ℤ, (k : ℝ) = z

/-- The dual lattice of a `ℤ`-submodule of `E` (with respect to the inner product). -/
def dual (ℒ : Submodule ℤ E) : Submodule ℤ E where
  carrier := {x : E | ∀ y : ℒ, IsInt ⟪x, (y : E)⟫_ℝ}
  zero_mem' := by
    intro y
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro x z hx hz y
    rcases hx y with ⟨kx, hkx⟩
    rcases hz y with ⟨kz, hkz⟩
    refine ⟨kx + kz, ?_⟩
    calc
      ((kx + kz : ℤ) : ℝ) = (kx : ℝ) + (kz : ℝ) := by norm_num
      _ = ⟪x, (y : E)⟫_ℝ + ⟪z, (y : E)⟫_ℝ := by rw [hkx, hkz]
      _ = ⟪x + z, (y : E)⟫_ℝ := by rw [inner_add_left]
  smul_mem' := by
    intro k x hx y
    rcases hx y with ⟨l, hl⟩
    refine ⟨k * l, ?_⟩
    have hinner : ⟪(k : ℤ) • x, (y : E)⟫_ℝ = (k : ℝ) * ⟪x, (y : E)⟫_ℝ := by
      have hz : (k : ℤ) • x = (k : ℝ) • x :=
        (Int.cast_smul_eq_zsmul (R := ℝ) (n := k) x).symm
      rw [hz]
      exact real_inner_smul_left x (y : E) (k : ℝ)
    calc
      ((k * l : ℤ) : ℝ) = (k : ℝ) * (l : ℝ) := by norm_num
      _ = (k : ℝ) * ⟪x, (y : E)⟫_ℝ := by rw [hl]
      _ = ⟪(k : ℤ) • x, (y : E)⟫_ℝ := hinner.symm

/-- Membership in the dual lattice. -/
lemma mem_dual {ℒ : Submodule ℤ E} {x : E} :
    x ∈ dual ℒ ↔ ∀ y : ℒ, IsInt ⟪x, (y : E)⟫_ℝ := by
  rfl

/-- The dual lattice contains 0. -/
lemma zero_mem_dual (ℒ : Submodule ℤ E) : (0 : E) ∈ dual ℒ := by
  intro y
  exact ⟨0, by simp⟩


section DualBasis

/-- The real inner product as a bilinear form. -/
noncomputable def innerLeft (x : E) : E →ₗ[ℝ] ℝ where
  toFun := fun y : E => ⟪x, y⟫_ℝ
  map_add' := by intro y z; rw [inner_add_right]
  map_smul' := by intro r y; rw [inner_smul_right]; simp

/-- The real inner product, seen as a bilinear form on `E`. -/
noncomputable def innerBilin : E →ₗ[ℝ] (E →ₗ[ℝ] ℝ) where
  toFun := fun x : E => innerLeft x
  map_add' := by
    intro x1 x2
    ext y
    change ⟪x1 + x2, y⟫_ℝ = ⟪x1, y⟫_ℝ + ⟪x2, y⟫_ℝ
    rw [inner_add_left]
  map_smul' := by
    intro r x
    ext y
    change ⟪r • x, y⟫_ℝ = r • ⟪x, y⟫_ℝ
    rw [real_inner_smul_left]
    simp

@[simp] lemma innerBilin_apply (x y : E) : innerBilin x y = ⟪x, y⟫_ℝ := rfl

lemma innerBilin_separating (x : E) : (∀ y : E, innerBilin x y = 0) → x = 0 := by
  intro hx
  have hxx : ⟪x, x⟫_ℝ = 0 := by simpa using (hx x)
  have hsq : ‖x‖ ^ 2 = 0 := by
    rw [real_inner_self_eq_norm_sq] at hxx
    exact hxx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

lemma innerBilin_nondegenerate :
    LinearMap.Nondegenerate (innerBilin : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) := by
  constructor
  · intro x hx
    exact innerBilin_separating x (fun y => by simpa using hx y)
  · intro y hy
    exact innerBilin_separating y (fun x => by
      simpa [real_inner_comm] using hy x)

/-- The `B`-dual basis of an `ℝ`-basis of `E` for the inner-product bilinear form. -/
noncomputable def innerDualBasis {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Basis ι ℝ E) : Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis innerBilin innerBilin_nondegenerate b

/-- Membership in the dual via the inner bilinear form. -/
lemma mem_dual_iff_bilin {ℒ : Submodule ℤ E} {x : E} :
    x ∈ dual ℒ ↔ x ∈ (LinearMap.BilinForm.dualSubmodule innerBilin ℒ) := by
  simp [dual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one, IsInt,
    innerBilin_apply]

/-- DUAL-BASIS THEOREM: for an `ℝ`-basis `b` of `E` whose `ℤ`-span is `ℒ`,
`dual ℒ` is the `ℤ`-span of the (inner-product) dual basis. -/
lemma dual_eq_span_dualBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (ℒ : Submodule ℤ E) (b : Basis ι ℝ E)
    (hspan : Submodule.span ℤ (Set.range b) = ℒ) :
    dual ℒ = Submodule.span ℤ (Set.range (innerDualBasis b)) := by
  have hlib := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (S := ℝ)
    (M := E) (B := innerBilin) innerBilin_nondegenerate (b := b)
  calc
    dual ℒ = LinearMap.BilinForm.dualSubmodule innerBilin ℒ := by
      ext x
      exact mem_dual_iff_bilin (ℒ := ℒ) (x := x)
    _ = LinearMap.BilinForm.dualSubmodule innerBilin (Submodule.span ℤ (Set.range b)) := by
      rw [hspan]
    _ = Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis innerBilin
        innerBilin_nondegenerate b)) := hlib
    _ = Submodule.span ℤ (Set.range (innerDualBasis b)) := by
      rfl

/-- In a full-rank lattice, the dual lattice is the `ℤ`-span of the real-dual basis. -/
theorem dual_eq_span_dualBasis_of_zlattice {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (b₀ : Basis (Fin (finrank ℤ ℒ)) ℤ ℒ) :
    dual ℒ = Submodule.span ℤ (Set.range (innerDualBasis (b₀.ofZLatticeBasis ℝ))) := by
  have hspan : Submodule.span ℤ (Set.range (b₀.ofZLatticeBasis ℝ)) = ℒ := by
    exact (b₀.ofZLatticeBasis_span ℝ)
  exact dual_eq_span_dualBasis ℒ (b₀.ofZLatticeBasis ℝ) hspan

/-- The dual of a full-rank lattice is discrete (it is the `ℤ`-span of a basis). -/
lemma dual_discreteTopology_of_zlattice {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) : DiscreteTopology (dual ℒ) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  have hEq : dual ℒ = Submodule.span ℤ (Set.range (innerDualBasis (b₀.ofZLatticeBasis ℝ))) := by
    exact dual_eq_span_dualBasis_of_zlattice (ℒ := ℒ) hℒ b₀
  rw [hEq]
  infer_instance

/-- The dual of a full-rank lattice spans the whole space. -/
theorem dual_span_eq_top {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    Submodule.span ℝ ((dual ℒ : Submodule ℤ E) : Set E) = ⊤ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  have hEq : dual ℒ = Submodule.span ℤ (Set.range (innerDualBasis (b₀.ofZLatticeBasis ℝ))) := by
    exact dual_eq_span_dualBasis_of_zlattice (ℒ := ℒ) hℒ b₀
  rw [hEq]
  exact (instIsZLatticeRealSpan (innerDualBasis (b₀.ofZLatticeBasis ℝ))).span_top

/-- The dual of a full-rank lattice is itself a full-rank lattice. -/
theorem dual_isZLattice_of_zlattice {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) [DiscreteTopology (dual ℒ)] : IsZLattice ℝ (dual ℒ) := by
  refine IsZLattice.mk (span_top := ?_)
  exact dual_span_eq_top hℒ

/-- The inner product is a symmetric bilinear form. -/
lemma innerBilin_symm :
    LinearMap.BilinForm.IsSymm (innerBilin : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) := by
  constructor
  intro x y
  simp [real_inner_comm]

/-- The dual as a bilinear-form dual submodule. -/
lemma dual_eq_dualSubmodule (ℒ : Submodule ℤ E) :
    dual ℒ = LinearMap.BilinForm.dualSubmodule innerBilin ℒ := by
  ext x
  exact mem_dual_iff_bilin (ℒ := ℒ) (x := x)

/-- BIDUAL: the double dual of a full-rank lattice is itself. -/
theorem dual_dual_eq_self {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) : dual (dual ℒ) = ℒ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  let β := b₀.ofZLatticeBasis ℝ
  have hspan : Submodule.span ℤ (Set.range β) = ℒ := by
    dsimp [β]
    exact (b₀.ofZLatticeBasis_span ℝ)
  have hlib := LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (R := ℤ) (S := ℝ)
    (M := E) (B := innerBilin) innerBilin_nondegenerate innerBilin_symm (b := β)
  calc
    dual (dual ℒ) = LinearMap.BilinForm.dualSubmodule innerBilin (dual ℒ) := by
      rw [dual_eq_dualSubmodule (dual ℒ)]
    _ = LinearMap.BilinForm.dualSubmodule innerBilin
        (LinearMap.BilinForm.dualSubmodule innerBilin ℒ) := by
      rw [dual_eq_dualSubmodule ℒ]
    _ = LinearMap.BilinForm.dualSubmodule innerBilin
        (LinearMap.BilinForm.dualSubmodule innerBilin (Submodule.span ℤ (Set.range β))) := by
      rw [hspan]
    _ = Submodule.span ℤ (Set.range β) := hlib
    _ = ℒ := by rw [hspan]

end DualBasis

/-- For a square real matrix, `√(det(Bᵀ·B)) = |det B|`. -/
lemma sqrt_det_transpose_mul_eq_abs_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : Real.sqrt ((B.transpose * B).det) = |B.det| := by
  rw [Matrix.det_mul]
  rw [Matrix.det_transpose]
  rw [← pow_two]
  exact Real.sqrt_sq_eq_abs B.det

/-- Step (1) of the covolume/determinant chain: the covolume of a full-rank lattice equals
the real volume of the fundamental domain of its real basis. -/
lemma covolume_eq_measure_fd {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (b₀ : Basis (Fin (finrank ℤ ℒ)) ℤ ℒ) :
    ZLattice.covolume ℒ = volume.real (ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ)) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  have hfund : IsAddFundamentalDomain ℒ
      (ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ)) (volume : Measure E) := by
    exact ZLattice.isAddFundamentalDomain (L := ℒ) b₀ (volume : Measure E)
  exact ZLattice.covolume_eq_measure_fundamentalDomain (L := ℒ) (μ := (volume : Measure E)) hfund

section UnitCube

/-- The unit half-open cube in a finite function space has volume `1`. -/
lemma volume_unitCube_pi (ι : Type*) [Fintype ι] :
    volume {f : ι → ℝ | ∀ i, f i ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  rw [show {f : ι → ℝ | ∀ i, f i ∈ Set.Ico (0 : ℝ) 1} =
      Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) by ext f; simp]
  rw [MeasureTheory.volume_pi_pi]
  simp [Real.volume_Ico]

/-- The unit half-open cube in a finite-dimensional `EuclideanSpace` has volume `1`
(measure-transport of `volume_unitCube_pi` along the volume-preserving
`EuclideanSpace` ↔ `ι → ℝ` unwrap map). -/
lemma volume_unitCube_EuclideanSpace (ι : Type*) [Fintype ι] :
    volume {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  let f : EuclideanSpace ℝ ι → ι → ℝ := fun x => @WithLp.ofLp 2 (ι → ℝ) x
  have hp : MeasurePreserving f volume volume := by
    dsimp [f]
    exact (PiLp.volume_preserving_ofLp ι)
  let P : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hpre : {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1} = f ⁻¹' P := by
    ext x
    simp [f, P]
  have hPnull : NullMeasurableSet P (volume : Measure (ι → ℝ)) := by
    have hmeas : MeasurableSet P := by
      dsimp [P]
      exact MeasurableSet.pi (Set.countable_univ)
        (fun i _ => (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)))
    exact hmeas.nullMeasurableSet
  calc
    volume {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1} = volume (f ⁻¹' P) := by rw [hpre]
    _ = volume P := hp.measure_preimage hPnull
    _ = 1 := by
      rw [show P = {g : ι → ℝ | ∀ i, g i ∈ Set.Ico (0 : ℝ) 1} by
        ext g
        simp [P, Set.mem_pi]]
      exact volume_unitCube_pi ι

/-- The fundamental domain of an orthonormal basis of a Euclidean space has volume `1`
(= the unit cube transported back by the measure-preserving `b.repr`). -/
lemma volume_fundamentalDomain_orthonormal (ι : Type*) [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    volume (ZSpan.fundamentalDomain b.toBasis) = 1 := by
  have hp : MeasurePreserving b.repr volume volume := by
    exact OrthonormalBasis.measurePreserving_repr b
  let cube : Set (EuclideanSpace ℝ ι) :=
    {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}
  have hpre : ZSpan.fundamentalDomain b.toBasis =
      (b.repr : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ⁻¹' cube := by
    ext x
    constructor
    · intro hx
      have h' := (ZSpan.mem_fundamentalDomain (b := b.toBasis)).mp hx
      dsimp [cube]
      intro i
      simpa using (h' i)
    · intro hx
      intro i
      have h' : (b.repr x : EuclideanSpace ℝ ι) i ∈ Set.Ico (0 : ℝ) 1 := hx i
      simpa using h'
  have hcube : volume cube = 1 := by
    dsimp [cube]
    exact volume_unitCube_EuclideanSpace ι
  have hnull : NullMeasurableSet cube (volume : Measure (EuclideanSpace ℝ ι)) := by
    have hmeas : MeasurableSet cube := by
      dsimp [cube]
      have hpi : {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1} =
          (@WithLp.ofLp 2 (ι → ℝ) ⁻¹'
            (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1))) := by
        ext x
        simp
      rw [hpi]
      exact (MeasurableSet.pi (Set.countable_univ)
        (fun i _ => (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)))).preimage
        (PiLp.volume_preserving_ofLp ι).measurable
    exact hmeas.nullMeasurableSet
  calc
    volume (ZSpan.fundamentalDomain b.toBasis) = volume
        ((b.repr : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ⁻¹' cube) := by rw [hpre]
    _ = volume cube := hp.measure_preimage hnull
    _ = 1 := hcube

/-- The fundamental domain of an orthonormal basis of ANY finite-dimensional real inner
product space `F` has volume `1` (its `repr`-image is the unit cube of
`EuclideanSpace ℝ ι`, measure-preserving). -/
lemma volume_fundamentalDomain_orthonormal' {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (b : OrthonormalBasis ι ℝ F) :
    volume (ZSpan.fundamentalDomain b.toBasis) = 1 := by
  have hp : MeasurePreserving b.repr volume volume := by
    exact OrthonormalBasis.measurePreserving_repr b
  let cube : Set (EuclideanSpace ℝ ι) :=
    {y : EuclideanSpace ℝ ι | ∀ i, y i ∈ Set.Ico (0 : ℝ) 1}
  have hpre : ZSpan.fundamentalDomain b.toBasis = (b.repr : F → EuclideanSpace ℝ ι) ⁻¹' cube := by
    ext x
    constructor
    · intro hx
      have h' := (ZSpan.mem_fundamentalDomain (b := b.toBasis)).mp hx
      dsimp [cube]
      intro i
      simpa using (h' i)
    · intro hx
      intro i
      have h' : (b.repr x : EuclideanSpace ℝ ι) i ∈ Set.Ico (0 : ℝ) 1 := hx i
      simpa using h'
  have hcube : volume cube = 1 := by
    dsimp [cube]
    exact volume_unitCube_EuclideanSpace ι
  have hnull : NullMeasurableSet cube (volume : Measure (EuclideanSpace ℝ ι)) := by
    have hmeas : MeasurableSet cube := by
      dsimp [cube]
      have hpi : {y : EuclideanSpace ℝ ι | ∀ i, y i ∈ Set.Ico (0 : ℝ) 1} =
          (@WithLp.ofLp 2 (ι → ℝ) ⁻¹'
            (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1))) := by
        ext y
        simp
      rw [hpi]
      exact (MeasurableSet.pi (Set.countable_univ)
        (fun i _ => (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 1)))).preimage
        (PiLp.volume_preserving_ofLp ι).measurable
    exact hmeas.nullMeasurableSet
  calc
    volume (ZSpan.fundamentalDomain b.toBasis) = volume
        ((b.repr : F → EuclideanSpace ℝ ι) ⁻¹' cube) := by rw [hpre]
    _ = volume cube := hp.measure_preimage hnull
    _ = 1 := hcube

end UnitCube


section CovolumeDet

/-- Step (2) of the covolume/determinant chain: the real volume of the real-basis
fundamental domain equals `|det|` of the basis change to the standard orthonormal basis
(whose fundamental domain has volume 1). -/
lemma covolume_eq_abs_det_change {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (b₀ : Basis (Fin (finrank ℤ ℒ)) ℤ ℒ) :
    volume.real (ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ)) =
      |(((stdOrthonormalBasis ℝ E).toBasis.reindex
          (Equiv.cast (congrArg Fin (ZLattice.rank ℝ ℒ).symm))).det
        (b₀.ofZLatticeBasis ℝ))| := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  let β : Basis (Fin (finrank ℤ ℒ)) ℝ E := b₀.ofZLatticeBasis ℝ
  let e : Fin (finrank ℝ E) ≃ Fin (finrank ℤ ℒ) :=
    Equiv.cast (congrArg Fin (ZLattice.rank ℝ ℒ).symm)
  let s' : Basis (Fin (finrank ℤ ℒ)) ℝ E := (stdOrthonormalBasis ℝ E).toBasis.reindex e
  have hmr : volume.real (ZSpan.fundamentalDomain β) =
      |s'.det β| * volume.real (ZSpan.fundamentalDomain s') := by
    exact ZSpan.measureReal_fundamentalDomain (b := β) (μ := (volume : Measure E)) (b₀ := s')
  have hvol : volume (ZSpan.fundamentalDomain s') = 1 := by
    dsimp [s']
    rw [ZSpan.fundamentalDomain_reindex]
    exact volume_fundamentalDomain_orthonormal' (b := stdOrthonormalBasis ℝ E)
  have hreal : volume.real (ZSpan.fundamentalDomain s') = 1 := by
    change (volume (ZSpan.fundamentalDomain s')).toReal = 1
    rw [hvol]
    simp
  calc
    volume.real (ZSpan.fundamentalDomain (b₀.ofZLatticeBasis ℝ))
        = volume.real (ZSpan.fundamentalDomain β) := by rfl
    _ = |s'.det β| * volume.real (ZSpan.fundamentalDomain s') := hmr
    _ = |s'.det β| * 1 := by rw [hreal]
    _ = |s'.det β| := by simp
    _ = |(((stdOrthonormalBasis ℝ E).toBasis.reindex
          (Equiv.cast (congrArg Fin (ZLattice.rank ℝ ℒ).symm))).det
        (b₀.ofZLatticeBasis ℝ))| := by
          rfl

/-- The coordinate matrix of the reindexed real basis in the canonical orthonormal basis of
`E = EuclideanSpace ℝ (Fin n)` equals `ReverseMinkowski.B ℒ` (columns relabelled by ρ). -/
lemma toMatrix_reindexed_eq_B {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
      Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix
        (fun j : Fin n => ((Module.finBasis ℤ ℒ).ofZLatticeBasis ℝ).reindex ρ j) =
      Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  dsimp
  ext i j
  simp [Basis.toMatrix_apply, Basis.reindex_apply, Matrix.reindex_apply, ReverseMinkowski.B]

/-- The square reindexed canonical-coordinate matrix `Be := reindex refl ρ (B ℒ)` (where
`ρ : Fin (finrank ℤ ℒ) ≃ Fin n` is the rank identification) has `|det Be| = det ℒ`. -/
theorem abs_det_reindexed_eq_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) :
    let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
      Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
    |(Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ)).det| =
      ReverseMinkowski.determinant ℒ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  let β : Basis (Fin (finrank ℤ ℒ)) ℝ E := b₀.ofZLatticeBasis ℝ
  let c : OrthonormalBasis (Fin n) ℝ E := EuclideanSpace.basisFun (Fin n) ℝ
  let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
    Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
  let v : Fin n → E := fun j => β (ρ.symm j)
  let Be : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ)
  have hreidx : (fun j : Fin n => (β.reindex ρ) j) = v := by
    funext j
    dsimp [v]
    simp
  have htmv : c.toBasis.toMatrix v = Be := by
    dsimp [Be]
    have htm := toMatrix_reindexed_eq_B (ℒ := ℒ) hℒ
    dsimp at htm
    rw [← htm]
    congr 1
    exact hreidx.symm
  have hdetM : |c.toBasis.det v| = |Be.det| := by
    rw [Basis.det_apply]
    rw [htmv]
  have hBB : (Be.transpose * Be) = Matrix.reindex ρ ρ
      ((ReverseMinkowski.B ℒ).transpose * ReverseMinkowski.B ℒ) := by
    ext i j
    simp [Be, Matrix.mul_apply, Matrix.reindex_apply]
  have hdetBB : (Be.transpose * Be).det = ((ReverseMinkowski.B ℒ).transpose * ReverseMinkowski.B ℒ).det := by
    rw [hBB, Matrix.det_reindex_self]
  have hsq : ReverseMinkowski.determinant ℒ = |Be.det| := by
    dsimp [ReverseMinkowski.determinant, Be]
    rw [← hdetBB]
    exact sqrt_det_transpose_mul_eq_abs_det Be
  exact hsq.symm

theorem covolume_eq_determinant {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    ZLattice.covolume ℒ = ReverseMinkowski.determinant ℒ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  let β : Basis (Fin (finrank ℤ ℒ)) ℝ E := b₀.ofZLatticeBasis ℝ
  let c : OrthonormalBasis (Fin n) ℝ E := EuclideanSpace.basisFun (Fin n) ℝ
  let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
    Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
  let v : Fin n → E := fun j => β (ρ.symm j)
  let Be : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ)
  -- covolume = volume.real (fd β)
  have hA : ZLattice.covolume ℒ = volume.real (ZSpan.fundamentalDomain β) := by
    dsimp [β]
    exact covolume_eq_measure_fd (ℒ := ℒ) hℒ b₀
  -- fd β =ᵐ parallelepiped β
  have hfd_ae : ZSpan.fundamentalDomain β =ᵐ[(volume : Measure E)] (parallelepiped β : Set E) := by
    simpa using (ZSpan.fundamentalDomain_ae_parallelepiped (b := β) (μ := (volume : Measure E)))
  have hB : volume.real (ZSpan.fundamentalDomain β) = volume.real (parallelepiped β : Set E) :=
    MeasureTheory.measureReal_congr hfd_ae
  -- parallelepiped β = parallelepiped v
  have hreidx : (fun j : Fin n => (β.reindex ρ) j) = v := by
    funext j
    dsimp [v]
    simp
  have hp_eq : (parallelepiped β : Set E) = (parallelepiped v : Set E) := by
    rw [show (parallelepiped β : Set E) = parallelepiped (fun j : Fin n => β (ρ.symm j)) by
      exact (parallelepiped_comp_equiv β ρ.symm).symm]
  -- volume (parallelepiped v) = ofReal |c.det v|, via addHaar
  have hvolEN : volume (parallelepiped v : Set E) = ENNReal.ofReal |c.toBasis.det v| := by
    have hadd := MeasureTheory.Measure.addHaar_parallelepiped (b := c.toBasis) (v := v)
    rw [OrthonormalBasis.addHaar_eq_volume c] at hadd
    exact hadd
  have hvolR : volume.real (parallelepiped v : Set E) = |c.toBasis.det v| := by
    rw [MeasureTheory.Measure.real, hvolEN]
    exact ENNReal.toReal_ofReal (abs_nonneg _)
  -- c.toMatrix v = Be
  have htmv : c.toBasis.toMatrix v = Be := by
    dsimp [Be]
    have htm := toMatrix_reindexed_eq_B (ℒ := ℒ) hℒ
    dsimp at htm
    rw [← htm]
    congr 1
    exact hreidx.symm
  -- |c.toBasis.det v| = |Be.det|
  have hdetM : |c.toBasis.det v| = |Be.det| := by
    rw [Basis.det_apply]
    rw [htmv]
  -- √det(BᵀB) = |Be.det|
  have hBB : (Be.transpose * Be) = Matrix.reindex ρ ρ
      ((ReverseMinkowski.B ℒ).transpose * ReverseMinkowski.B ℒ) := by
    ext i j
    simp [Be, Matrix.mul_apply, Matrix.reindex_apply]
  have hdetBB : (Be.transpose * Be).det = ((ReverseMinkowski.B ℒ).transpose * ReverseMinkowski.B ℒ).det := by
    rw [hBB, Matrix.det_reindex_self]
  have hsq : ReverseMinkowski.determinant ℒ = |Be.det| := by
    dsimp [ReverseMinkowski.determinant, Be]
    rw [← hdetBB]
    exact sqrt_det_transpose_mul_eq_abs_det Be
  calc
    ZLattice.covolume ℒ = volume.real (ZSpan.fundamentalDomain β) := hA
    _ = volume.real (parallelepiped β : Set E) := hB
    _ = volume.real (parallelepiped v : Set E) := by rw [hp_eq]
    _ = |c.toBasis.det v| := hvolR
    _ = |Be.det| := hdetM
    _ = ReverseMinkowski.determinant ℒ := hsq.symm


/-- The real volume of the Voronoi cell equals the lattice determinant
(composition: Voronoi tiling ⇒ covolume = volume of the cell, and covolume = determinant). -/
lemma voronoi_volume_eq_det {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    volume.real (Submission.Voronoi.voronoi ℒ) = ReverseMinkowski.determinant ℒ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  have hfund : IsAddFundamentalDomain ℒ (Submission.Voronoi.voronoi ℒ) := by
    simpa using (Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ)
  have hvol : volume.real (Submission.Voronoi.voronoi ℒ) = ZLattice.covolume ℒ := by
    exact (ZLattice.covolume_eq_measure_fundamentalDomain (L := ℒ) (μ := (volume : Measure E)) hfund).symm
  rw [hvol]
  exact covolume_eq_determinant (ℒ := ℒ) hℒ


end CovolumeDet

/-- Membership in the dual lattice, in the "∃ integer" form used by the Poisson-summation
statements in the shared commons. -/
lemma mem_dual_iff_int {ℒ : Submodule ℤ E} {w : E} :
    w ∈ dual ℒ ↔ ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = ⟪w, (y : E)⟫_ℝ := by
  rw [mem_dual]
  refine forall_congr' (fun y => ?_)
  rfl


/-- **Poisson summation for full-rank lattices** (paper eq. (2.3)):
`ρ_s(ℒ) · det ℒ = sⁿ · ρ_{1/s}(ℒ*)`, with `ℒ* = dual ℒ`.  Derived from the commons
`Commons.Lattice.PoissonSummation.lattice_psf` (itself derived from the n-dimensional
Gaussian Poisson summation `gaussian_psf_matrix`), instantiated on the reindexed
canonical-coordinate matrix `Be` of `finBasis ℤ ℒ` (`|det Be| = determinant ℒ`), with the
dual lattice identified with the dual-basis span. -/
theorem rho_gamma_psf {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (s : ℝ) (hs : 0 < s) :
    rhoVal s ℒ * ReverseMinkowski.determinant ℒ =
      s ^ n * rhoVal (1 / s) (dual ℒ) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : DiscreteTopology (dual ℒ) := dual_discreteTopology_of_zlattice (ℒ := ℒ) hℒ
  let b₀ := Module.finBasis ℤ ℒ
  let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
    Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
  let b' : Basis (Fin n) ℤ ℒ := b₀.reindex ρ
  let Be : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ)
  have hcoords : ∀ i j : Fin n, (((b' j : ℒ) : E) i) = Be i j := by
    intro i j
    dsimp [b', Be]
    rw [Basis.reindex_apply]
    rfl
  have hdet : |Be.det| = ReverseMinkowski.determinant ℒ := by
    dsimp [Be]
    exact abs_det_reindexed_eq_det (ℒ := ℒ) hℒ
  have hBene0 : Be.det ≠ 0 := by
    intro hz
    have hdetpos : 0 < ReverseMinkowski.determinant ℒ := by
      rw [← covolume_eq_determinant (ℒ := ℒ) hℒ]
      exact ZLattice.covolume_pos ℒ
    have : |Be.det| = 0 := by simp [hz]
    rw [hdet] at this
    linarith
  have hmem : ∀ w : E, w ∈ dual ℒ ↔ ∀ y : ℒ, ∃ z : ℤ, (z : ℝ) = ⟪w, (y : E)⟫_ℝ := by
    intro w
    exact mem_dual_iff_int (ℒ := ℒ)
  have hpsf := Commons.Lattice.PoissonSummation.lattice_psf (n := n) (ℒ := ℒ) (Ld := dual ℒ)
    hmem (b := b') (A := Be) hBene0 hcoords s hs
  have hdual : (∑' w : dual ℒ, Real.exp (-Real.pi * s ^ 2 * ‖(w : E)‖ ^ 2)) =
      rhoVal (1 / s) (dual ℒ) := by
    unfold rhoVal
    apply tsum_congr
    intro w
    congr 1
    field_simp [ne_of_gt hs]
  calc
    rhoVal s ℒ * ReverseMinkowski.determinant ℒ
        = rhoVal s ℒ * |Be.det| := by rw [hdet]
    _ = (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * |Be.det| := by
        rfl
    _ = s ^ n * (∑' w : dual ℒ, Real.exp (-Real.pi * s ^ 2 * ‖(w : E)‖ ^ 2)) := hpsf
    _ = s ^ n * rhoVal (1 / s) (dual ℒ) := by rw [hdual]


/-- **Shifted Gaussian mass** (Banaszczyk / paper Claim 2.7): for a full-rank lattice `ℒ`,
`ρ_s(ℒ − u) ≤ ρ_s(ℒ)` for every shift `u ∈ E`.  Poisson-summation based (via the commons
`lattice_shifted_mass_le`, derived from the n-dimensional shifted Gaussian PSF); the proof
uses `covolume_eq_determinant` and `abs_det_reindexed_eq_det` to instantiate the
canonical-coordinate matrix of `finBasis ℤ ℒ`. -/
theorem shifted_mass_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (s : ℝ) (hs : 0 < s) (u : E) :
    (∑' y : ℒ, rexp (-Real.pi * ‖((y : E) - u)‖ ^ 2 / s ^ 2)) ≤ rhoVal s ℒ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  let b₀ := Module.finBasis ℤ ℒ
  let ρ : Fin (finrank ℤ ℒ) ≃ Fin n :=
    Equiv.cast (congrArg Fin (by rw [ZLattice.rank ℝ ℒ]; simp))
  let b' : Basis (Fin n) ℤ ℒ := b₀.reindex ρ
  let Be : Matrix (Fin n) (Fin n) ℝ := Matrix.reindex (Equiv.refl (Fin n)) ρ (ReverseMinkowski.B ℒ)
  have hcoords : ∀ i j : Fin n, (((b' j : ℒ) : E) i) = Be i j := by
    intro i j
    dsimp [b', Be]
    rw [Basis.reindex_apply]
    rfl
  have hBene0 : Be.det ≠ 0 := by
    intro hz
    have hdetpos : 0 < ReverseMinkowski.determinant ℒ := by
      rw [← covolume_eq_determinant (ℒ := ℒ) hℒ]
      exact ZLattice.covolume_pos ℒ
    have hdet : |Be.det| = ReverseMinkowski.determinant ℒ := by
      dsimp [Be]
      exact abs_det_reindexed_eq_det (ℒ := ℒ) hℒ
    have : |Be.det| = 0 := by simp [hz]
    rw [hdet] at this
    linarith
  have hle := Commons.Lattice.PoissonSummation.lattice_shifted_mass_le (n := n) (ℒ := ℒ)
    (b := b') (A := Be) hBene0 hcoords s hs u
  simpa [rhoVal] using hle


end Submission.Poisson
