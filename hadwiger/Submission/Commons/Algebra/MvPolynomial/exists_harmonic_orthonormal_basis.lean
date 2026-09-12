import Mathlib
import Submission.Commons.Analysis.MeasureTheory.continuous_integrable_sphere
import Submission.Commons.Analysis.MeasureTheory.sphere_polynomial_uniform_dense
import Submission.Commons.Analysis.MeasureTheory.sphere_restriction_pairing_pos
import Submission.Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional

noncomputable section
open scoped BigOperators
open MeasureTheory Metric LinearMap

namespace Commons.Algebra.MvPolynomial

abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1

/-! ### The harmonic homogeneous summand -/

/-- The Laplace operator `Δ = ∑ᵢ ∂ᵢ²` on multivariate real polynomials, as a linear map. -/
def lapLM (n : ℕ) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun P := ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)
  map_add' P Q := by
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c P := by
    show (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (c • P))) =
      c • (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P))
    simp only [Derivation.map_smul, Finset.smul_sum]

lemma lapLM_apply (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    lapLM n P = ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P) := rfl

/-- The space of polynomials that are harmonic (annihilated by the Laplacian) and
homogeneous of degree `k`. -/
def harmHom (n k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ⊓ LinearMap.ker (lapLM n)

lemma mem_harmHom {n k : ℕ} {P : MvPolynomial (Fin n) ℝ} :
    P ∈ harmHom n k ↔
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧ lapLM n P = 0 := by
  simp [harmHom, LinearMap.mem_ker]

/-! ### Continuity and integrability on the sphere -/

lemma continuous_eval_sphere (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    Continuous fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P := by
  have h : (fun θ : Sph n => MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P) =
      (fun θ : Sph n => Commons.Analysis.MeasureTheory.spherePolyToCont n P θ) := by
    funext θ
    exact (Commons.Analysis.MeasureTheory.spherePoly_apply_eval P θ).symm
  rw [h]
  exact (Commons.Analysis.MeasureTheory.spherePolyToCont n P).continuous

lemma integrable_eval_mul {n : ℕ} [Nonempty (Fin n)] (P Q : MvPolynomial (Fin n) ℝ) :
    Integrable (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) Q)
      MeasureTheory.volume.toSphere :=
  Commons.Analysis.MeasureTheory.continuous_integrable_sphere _
    ((continuous_eval_sphere n P).mul (continuous_eval_sphere n Q))

lemma eval_smul_sphere (n : ℕ) (c : ℝ) (P : MvPolynomial (Fin n) ℝ) (θ : Sph n) :
    MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (c • P) =
      c * MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.eval_mul, MvPolynomial.eval_C]

/-! ### The sphere pairing on the harmonic homogeneous summand -/

/-- The `L²`-pairing of two harmonic homogeneous polynomials on the unit sphere. -/
def harmPair (n k : ℕ) (x y : harmHom n k) : ℝ :=
  ∫ θ : Sph n,
    MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
    MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ)
  ∂MeasureTheory.volume.toSphere

lemma harmPair_add_left {n k : ℕ} [Nonempty (Fin n)] (x y z : harmHom n k) :
    harmPair n k (x + y) z = harmPair n k x z + harmPair n k y z := by
  have h1 : Integrable (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ))
      MeasureTheory.volume.toSphere := integrable_eval_mul _ _
  have h2 : Integrable (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ))
      MeasureTheory.volume.toSphere := integrable_eval_mul _ _
  have hcongr : (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) ((x + y : harmHom n k) : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ)) =
      fun θ : Sph n =>
        MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ) +
        MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ) := by
    funext θ
    rw [Submodule.coe_add, MvPolynomial.eval_add]
    ring
  unfold harmPair
  rw [hcongr, integral_add h1 h2]

lemma harmPair_smul_left {n k : ℕ} [Nonempty (Fin n)] (c : ℝ) (x y : harmHom n k) :
    harmPair n k (c • x) y = c • harmPair n k x y := by
  have hcongr : (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) ((c • x : harmHom n k) : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ)) =
      fun θ : Sph n =>
        c * (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ)) := by
    funext θ
    rw [Submodule.coe_smul, eval_smul_sphere]
    ring
  unfold harmPair
  rw [hcongr, integral_const_mul, smul_eq_mul]

lemma harmPair_add_right {n k : ℕ} [Nonempty (Fin n)] (x y z : harmHom n k) :
    harmPair n k x (y + z) = harmPair n k x y + harmPair n k x z := by
  have h1 : Integrable (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ))
      MeasureTheory.volume.toSphere := integrable_eval_mul _ _
  have h2 : Integrable (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ))
      MeasureTheory.volume.toSphere := integrable_eval_mul _ _
  have hcongr : (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) ((y + z : harmHom n k) : MvPolynomial (Fin n) ℝ)) =
      fun θ : Sph n =>
        MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ) +
        MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (z : MvPolynomial (Fin n) ℝ) := by
    funext θ
    rw [Submodule.coe_add, MvPolynomial.eval_add]
    ring
  unfold harmPair
  rw [hcongr, integral_add h1 h2]

lemma harmPair_smul_right {n k : ℕ} [Nonempty (Fin n)] (c : ℝ) (x y : harmHom n k) :
    harmPair n k x (c • y) = c • harmPair n k x y := by
  have hcongr : (fun θ : Sph n =>
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) ((c • y : harmHom n k) : MvPolynomial (Fin n) ℝ)) =
      fun θ : Sph n =>
        c * (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (x : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) (y : MvPolynomial (Fin n) ℝ)) := by
    funext θ
    rw [Submodule.coe_smul, eval_smul_sphere]
    ring
  unfold harmPair
  rw [hcongr, integral_const_mul, smul_eq_mul]

/-- The `L²`-pairing on the harmonic homogeneous summand, as a bilinear form. -/
def harmBilin (n k : ℕ) [Nonempty (Fin n)] : LinearMap.BilinForm ℝ (harmHom n k) :=
  LinearMap.mk₂ ℝ (harmPair n k)
    (fun x y z => harmPair_add_left x y z)
    (fun c x y => harmPair_smul_left c x y)
    (fun x y z => harmPair_add_right x y z)
    (fun c x y => harmPair_smul_right c x y)

lemma harmBilin_apply {n k : ℕ} [Nonempty (Fin n)] (x y : harmHom n k) :
    harmBilin n k x y = harmPair n k x y := rfl

lemma harmBilin_isSymm {n k : ℕ} [Nonempty (Fin n)] : LinearMap.IsSymm (harmBilin n k) := by
  refine LinearMap.BilinForm.isSymm_iff.mp ?_
  refine ⟨fun x y => ?_⟩
  rw [harmBilin_apply, harmBilin_apply]
  unfold harmPair
  apply integral_congr_ae
  filter_upwards with θ
  ring

lemma harmBilin_pos {n k : ℕ} [Nonempty (Fin n)] (x : harmHom n k) (hx : x ≠ 0) :
    0 < harmBilin n k x x := by
  have hxmem : (x : MvPolynomial (Fin n) ℝ) ∈
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := (mem_harmHom.mp x.2).1
  have hxne : (x : MvPolynomial (Fin n) ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
  have hpos := Commons.Analysis.MeasureTheory.sphere_restriction_pairing_pos
    (n := n) (k := k) (x : MvPolynomial (Fin n) ℝ) hxmem hxne
  rw [harmBilin_apply]
  unfold harmPair
  simpa only [pow_two] using hpos

/-! ### Existence of an orthonormal basis of the harmonic homogeneous summand -/

set_option linter.style.haveILetI false in
/-- The harmonic homogeneous summand of degree `k` admits a `harmBilin`-orthonormal
basis: normalising an orthogonal basis (which exists for a symmetric bilinear form
over a field of characteristic `≠ 2`) by the square roots of the diagonal entries. -/
theorem exists_orthonormalBasis_harmHom {n k : ℕ} [Nonempty (Fin n)] :
    ∃ Y : Fin (Module.finrank ℝ (harmHom n k)) → harmHom n k,
      (∀ i j : Fin (Module.finrank ℝ (harmHom n k)),
        harmBilin n k (Y i) (Y j) = if i = j then (1 : ℝ) else 0) ∧
      Submodule.span ℝ (Set.range Y) = ⊤ := by
  classical
  haveI : FiniteDimensional ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :=
    Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
  haveI : FiniteDimensional ℝ (harmHom n k) :=
    Submodule.finiteDimensional_of_le
      (S₁ := harmHom n k) (S₂ := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) inf_le_left
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (V := harmHom n k) (K := ℝ) (B := harmBilin n k) (harmBilin_isSymm (n := n) (k := k))
  let c : Fin (Module.finrank ℝ (harmHom n k)) → ℝ :=
    fun i => (Real.sqrt (harmBilin n k (b i) (b i)))⁻¹
  have hcpos : ∀ i, 0 < harmBilin n k (b i) (b i) :=
    fun i => harmBilin_pos (b i) (b.ne_zero i)
  have hcne : ∀ i, c i ≠ 0 :=
    fun i => inv_ne_zero (Real.sqrt_pos_of_pos (hcpos i)).ne'
  have horth : ∀ i j : Fin (Module.finrank ℝ (harmHom n k)),
      harmBilin n k (c i • b i) (c j • b j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have hbij : harmBilin n k (c i • b i) (c j • b j)
        = c i * c j * harmBilin n k (b i) (b j) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hbij]
      have hB : 0 < harmBilin n k (b i) (b i) := hcpos i
      have hsq : Real.sqrt (harmBilin n k (b i) (b i)) * Real.sqrt (harmBilin n k (b i) (b i))
          = harmBilin n k (b i) (b i) := by
        rw [← sq, Real.sq_sqrt (le_of_lt hB)]
      rw [show c i = (Real.sqrt (harmBilin n k (b i) (b i)))⁻¹ from rfl, ← mul_inv, hsq,
        inv_mul_cancel₀ (ne_of_gt hB)]
    · rw [if_neg hij, hbij, isOrthoᵢ_def.mp hb i j hij, mul_zero]
  refine ⟨fun i => c i • b i, horth, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro i _
  have hmem : c i • b i ∈ Submodule.span ℝ (Set.range (fun i => c i • b i)) :=
    Submodule.subset_span ⟨i, rfl⟩
  have h2 : b i ∈ Submodule.span ℝ (Set.range (fun i => c i • b i)) := by
    have h3 := Submodule.smul_mem (Submodule.span ℝ (Set.range (fun i => c i • b i)))
      (c i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (hcne i), one_smul] at h3
  exact Submodule.smul_mem _ _ h2

/-! ### The requested lemma -/

theorem exists_harmonic_orthonormal_basis
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)] :
    ∃ (d : ℕ) (Y : Fin d → MvPolynomial (Fin n) ℝ),
      (∀ j : Fin d, Y j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (Y j))) = 0) ∧
      (∀ i j : Fin d,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y i) *
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j)
          ∂MeasureTheory.volume.toSphere) = if i = j then 1 else 0) := by
  classical
  obtain ⟨Y, horth, -⟩ := exists_orthonormalBasis_harmHom (n := n) (k := k)
  refine ⟨Module.finrank ℝ (harmHom n k),
    fun j => (Y j : MvPolynomial (Fin n) ℝ), ?_, ?_⟩
  · intro j
    refine ⟨(mem_harmHom.mp (Y j).2).1, ?_⟩
    simpa only [lapLM_apply] using (mem_harmHom.mp (Y j).2).2
  · intro i j
    show harmBilin n k (Y i) (Y j) = if i = j then (1 : ℝ) else 0
    exact horth i j

end Commons.Algebra.MvPolynomial
