import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.LatVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.LatFourierDefs` — vocabulary for the lattice Fourier series on the box

This module collects the definitions and elementary lemmas used by
`Work.BoseBoxFock.latFourier_tendsto_periodisation`, the `L²` convergence of the truncated lattice
Fourier series of a bounded, compactly supported weight to its periodisation.

The objects are:

* `latCell ℓ = [0,ℓ)³`, the half-open cube (`Ico` form) used as the fundamental domain of the
  action of `ℓℤ³` on `ℝ³`;
* `latBox ℓ = [0,ℓ]³`, the closed cube of the target statement (`Icc` form);
* `latFinSet ℓ R`, the (finite) set of lattice points `m` with `‖ℓ • latVec m‖ ≤ R + √3·ℓ`, i.e.
  the multi-indices whose translate of the cube can meet the support of a weight vanishing
  outside the ball of radius `R`;
* `latPer ℓ W z = ∑'_m W (z + ℓ • latVec m)`, the `ℓℤ³`-periodisation of `W`;
* `latFt ℓ W n = kinFT W (kmomInt ℓ n)`, the `n`-th lattice Fourier sample of `W`;
* `latPerCut ℓ W`, the periodisation cut off by the closed cube.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

/- Everything in this file lives in the `LatFourier` sub-namespace, so that the (common)
names `latCell`, `latBox`, `latVec_add`, `kmomInt_zero`, ... cannot collide with the corpus
declarations of the same name in `Work.BoseBoxFock`. -/
namespace LatFourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The closed cube and the half-open cell -/

/-- The **half-open cube** `[0,ℓ)³`, in the `Ico` form convenient for the fundamental-domain
statement. -/
def latCell (ℓ : ℝ) : Set E3 := {x : E3 | ∀ i, x i ∈ Set.Ico (0 : ℝ) ℓ}

/-- The **closed cube** `[0,ℓ]³`, the integration domain of the target statement. -/
def latBox (ℓ : ℝ) : Set E3 := {x : E3 | ∀ i, x i ∈ Set.Icc (0 : ℝ) ℓ}

@[simp] lemma mem_latCell {ℓ : ℝ} {x : E3} : x ∈ latCell ℓ ↔ ∀ i, x i ∈ Set.Ico (0 : ℝ) ℓ :=
  Iff.rfl

@[simp] lemma mem_latBox {ℓ : ℝ} {x : E3} : x ∈ latBox ℓ ↔ ∀ i, x i ∈ Set.Icc (0 : ℝ) ℓ :=
  Iff.rfl

lemma measurableSet_latCell (ℓ : ℝ) : MeasurableSet (latCell ℓ) := by
  have h : latCell ℓ = ⋂ i : Fin 3, {x : E3 | x i ∈ Set.Ico (0 : ℝ) ℓ} := by
    ext x; simp [latCell]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage (by fun_prop : Measurable fun x : E3 => x i)

lemma measurableSet_latBox (ℓ : ℝ) : MeasurableSet (latBox ℓ) := by
  have h : latBox ℓ = ⋂ i : Fin 3, {x : E3 | x i ∈ Set.Icc (0 : ℝ) ℓ} := by
    ext x; simp [latBox]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Icc.preimage (by fun_prop : Measurable fun x : E3 => x i)

lemma isClosed_latBox (ℓ : ℝ) : IsClosed (latBox ℓ) := by
  have h : latBox ℓ = ⋂ i : Fin 3, {x : E3 | x i ∈ Set.Icc (0 : ℝ) ℓ} := by
    ext x; simp [latBox]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (by fun_prop : Continuous fun x : E3 => x i)

lemma latCell_subset_latBox {ℓ : ℝ} : latCell ℓ ⊆ latBox ℓ := by
  intro x hx
  simp only [mem_latBox, mem_latCell] at hx ⊢
  exact fun i => ⟨(hx i).1, (hx i).2.le⟩

/-- Every point of the closed cube has norm at most `√3 ℓ`. -/
lemma latBox_subset_closedBall {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {x : E3} (hx : x ∈ latBox ℓ) :
    ‖x‖ ≤ Real.sqrt 3 * ℓ := by
  rw [EuclideanSpace.norm_eq]
  have h2 : ∑ i, ‖x.ofLp i‖ ^ 2 ≤ 3 * ℓ ^ 2 := by
    have h4 : ∀ i : Fin 3, ‖x.ofLp i‖ ^ 2 ≤ ℓ ^ 2 := by
      intro i
      have h : 0 ≤ x i ∧ x i ≤ ℓ := (mem_latBox.mp hx) i
      rw [Real.norm_of_nonneg h.1]
      nlinarith [h.1, h.2]
    calc ∑ i, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ℓ ^ 2 := Finset.sum_le_sum fun i _ => h4 i
      _ = 3 * ℓ ^ 2 := by simp [Finset.sum_const]
  calc Real.sqrt (∑ i, ‖x.ofLp i‖ ^ 2) ≤ Real.sqrt (3 * ℓ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt 3 * ℓ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq hℓ]

/-- The volume of the half-open cell. -/
lemma volume_latCell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : volume (latCell ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' (latCell ℓ)
      = Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0 : ℝ) ℓ) := by
    ext x; simp [latCell]
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  rw [← MeasureTheory.MeasurePreserving.measure_preimage hmp
      (measurableSet_latCell ℓ).nullMeasurableSet, hpre, Real.volume_pi_Ico]
  simp [Finset.prod_const, ENNReal.ofReal_pow hℓ]

/-! ## 2. Lattice vector algebra -/

lemma latVec_add (m m' : Fin 3 → ℤ) : latVec (m + m') = latVec m + latVec m' := by
  rw [latVec, latVec, latVec, ← WithLp.toLp_add]
  congr 1
  ext i
  simp [Int.cast_add]

lemma latVec_zero : latVec (0 : Fin 3 → ℤ) = 0 := by
  rw [latVec]; ext i; simp

/-- `kmomInt ℓ m = (2π/ℓ) • latVec m`. -/
lemma kmomInt_eq_smul_latVec (ℓ : ℝ) (m : Fin 3 → ℤ) :
    kmomInt ℓ m = (2 * Real.pi / ℓ) • latVec m := by
  rw [kmomInt, BoseB4.vec, latVec,
    ← WithLp.toLp_smul (p := 2) ℓ⁻¹ (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ)),
    ← WithLp.toLp_smul (p := 2) (2 * Real.pi / ℓ) (fun i : Fin 3 => (m i : ℝ))]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma kmomInt_add (ℓ : ℝ) (m m' : Fin 3 → ℤ) :
    kmomInt ℓ (m + m') = kmomInt ℓ m + kmomInt ℓ m' := by
  rw [kmomInt_eq_smul_latVec, kmomInt_eq_smul_latVec, kmomInt_eq_smul_latVec, latVec_add,
    smul_add]

lemma kmomInt_zero (ℓ : ℝ) : kmomInt ℓ (0 : Fin 3 → ℤ) = 0 := by
  rw [kmomInt_eq_smul_latVec, latVec_zero, smul_zero]

lemma latVec_norm_smul (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (m : Fin 3 → ℤ) :
    ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := by
  rw [norm_smul, Real.norm_of_nonneg hℓ]

/-- Every coordinate of `m` is dominated by the Euclidean norm of `latVec m`. -/
lemma abs_coord_le_norm_latVec (m : Fin 3 → ℤ) (i : Fin 3) :
    |(m i : ℝ)| ≤ ‖latVec m‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : (m i : ℝ) ^ 2 ≤ ∑ j, ‖(latVec m).ofLp j‖ ^ 2 := by
    have h := Finset.single_le_sum (f := fun j : Fin 3 => ‖(latVec m).ofLp j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [latVec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using h
  calc |(m i : ℝ)| = Real.sqrt ((m i : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ‖(latVec m).ofLp j‖ ^ 2) := Real.sqrt_le_sqrt h1

/-- The set of lattice vectors of norm at most `C` is finite. -/
lemma finite_latVec_norm_le (C : ℝ) : {m : Fin 3 → ℤ | ‖latVec m‖ ≤ C}.Finite := by
  refine Set.Finite.subset (s := Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(⌈C⌉)) ⌈C⌉))
    (Set.Finite.pi (fun _ : Fin 3 => Set.finite_Icc _ _)) ?_
  intro m hm
  simp only [Set.mem_univ_pi, Set.mem_Icc] at hm ⊢
  intro i
  have h1 := abs_coord_le_norm_latVec m i
  have h2 : |(m i : ℝ)| ≤ ((⌈C⌉ : ℤ) : ℝ) := le_trans h1 (le_trans hm (Int.le_ceil C))
  obtain ⟨hlo, hhi⟩ := abs_le.mp h2
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- The lattice points of Euclidean norm at most `ρ`, as a `Finset`. -/
noncomputable def latBall (ρ : ℝ) : Finset (Fin 3 → ℤ) := (finite_latVec_norm_le ρ).toFinset

lemma mem_latBall {ρ : ℝ} {m : Fin 3 → ℤ} : m ∈ latBall ρ ↔ ‖latVec m‖ ≤ ρ :=
  (finite_latVec_norm_le ρ).mem_toFinset

/-- The lattice points whose `ℓ`-translate of the cube can meet the support of a weight
vanishing outside the ball of radius `R`. -/
noncomputable def latFinSet (ℓ R : ℝ) : Finset (Fin 3 → ℤ) :=
  latBall ((R + Real.sqrt 3 * ℓ) / ℓ)

lemma mem_latFinSet {ℓ R : ℝ} {m : Fin 3 → ℤ} :
    m ∈ latFinSet ℓ R ↔ ‖latVec m‖ ≤ (R + Real.sqrt 3 * ℓ) / ℓ := mem_latBall

/-! ## 3. Phases: the lattice momenta annihilate the `ℓℤ³` translations -/

/-- `⟪kmomInt ℓ n, ℓ • latVec m⟫ = 2π (n · m)`, an integer multiple of `2π`. -/
lemma inner_kmomInt_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) :
    inner ℝ (kmomInt ℓ n) (ℓ • latVec m) = 2 * Real.pi * ((∑ i, n i * m i : ℤ) : ℝ) := by
  have h1 : inner ℝ (BoseB4.vec n) (latVec m)
      = ∑ i, (2 * Real.pi * (n i : ℝ)) * (m i : ℝ) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show inner ℝ ((BoseB4.vec n).ofLp i) ((latVec m).ofLp i) = _
    rw [Real.inner_apply, BoseB4.vec, latVec, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  have h2 : inner ℝ (kmomInt ℓ n) (ℓ • latVec m) = inner ℝ (BoseB4.vec n) (latVec m) := by
    rw [kmomInt, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]
  rw [h2, h1]
  have hcast : ((∑ i, n i * m i : ℤ) : ℝ) = ∑ i, (n i : ℝ) * (m i : ℝ) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => Int.cast_mul _ _
  have hstep : (∑ i : Fin 3, (2 * Real.pi * (n i : ℝ)) * (m i : ℝ))
      = ∑ i : Fin 3, (2 * Real.pi) * ((n i : ℝ) * (m i : ℝ)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hstep, ← Finset.mul_sum, ← hcast]

lemma exp_I_inner_smul_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) :
    Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ) : ℂ)) = 1 := by
  set k : ℤ := ∑ i, n i * m i with hk
  rw [inner_kmomInt_latVec hℓ n m, ← hk]
  have harg : Complex.I * (((2 * Real.pi * (k : ℝ)) : ℝ) : ℂ)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

lemma exp_neg_I_inner_smul_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) :
    Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ) : ℂ))) = 1 := by
  set k : ℤ := ∑ i, n i * m i with hk
  rw [inner_kmomInt_latVec hℓ n m, ← hk]
  have harg : -(Complex.I * (((2 * Real.pi * (k : ℝ)) : ℝ) : ℂ))
      = (-k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

/-- The character `z ↦ e^{i⟪k_n,z⟫}` is invariant under the lattice translations. -/
lemma exp_I_inner_add_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) (z : E3) :
    Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) := by
  rw [inner_add_right]
  push_cast
  rw [show Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) + (inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ))
      = Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)
        + Complex.I * ((inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.exp_add, exp_I_inner_smul_latVec hℓ n m, mul_one]

/-- The conjugate character is invariant under the lattice translations. -/
lemma exp_neg_I_inner_add_latVec {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n m : Fin 3 → ℤ) (z : E3) :
    Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (z + ℓ • latVec m) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))) := by
  rw [inner_add_right]
  push_cast
  rw [show -(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) + (inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ)))
      = (-(Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
        + (-(Complex.I * ((inner ℝ (kmomInt ℓ n) (ℓ • latVec m) : ℝ) : ℂ))) by
      push_cast; ring,
    Complex.exp_add, exp_neg_I_inner_smul_latVec hℓ n m, mul_one]

/-! ## 4. The periodisation -/

/-- The `ℓℤ³`-periodisation `∑'_m W (z + ℓ • latVec m)` of `W`, as a complex-valued function
(the target's right-hand side is `ℓ³` times this). -/
noncomputable def latPer (ℓ : ℝ) (W : E3 → ℝ) (z : E3) : ℂ :=
  ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ)

/-- The `n`-th lattice Fourier sample `kinFT W (kmomInt ℓ n)` of `W`. -/
noncomputable def latFt (ℓ : ℝ) (W : E3 → ℝ) (n : Fin 3 → ℤ) : ℂ :=
  Submission.BoseGases.kinFT (fun y : E3 => (W y : ℂ)) (kmomInt ℓ n)

/-- The periodisation, cut off by the closed cube. -/
noncomputable def latPerCut (ℓ : ℝ) (W : E3 → ℝ) : E3 → ℂ :=
  (latBox ℓ).indicator (latPer ℓ W)

/-- On the closed cube, the periodisation is the finite sum over `latFinSet ℓ R` when `W`
vanishes outside the ball of radius `R`. -/
lemma latPer_eq_sum_finset {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) {z : E3} (hz : z ∈ latBox ℓ) :
    latPer ℓ W z = ∑ m ∈ latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ) := by
  rw [latPer]
  refine tsum_eq_sum (s := latFinSet ℓ R) (fun m hm => ?_)
  have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((mem_latFinSet).mpr hc)
  have hzb := latBox_subset_closedBall hℓ.le hz
  have h5 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := latVec_norm_smul ℓ hℓ.le m
  have hgt : R < ‖z + ℓ • latVec m‖ := by
    have h2 : ‖ℓ • latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      calc ‖ℓ • latVec m‖ = ‖(z + ℓ • latVec m) - z‖ := by
            congr 1; abel
        _ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := norm_sub_le _ _
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot
      linarith [hnot]
    linarith
  simp [hWs _ hgt]

/-- The periodisation is bounded on the cube. -/
lemma latPer_bdd {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ latBox ℓ, ‖latPer ℓ W z‖ ≤ D := by
  obtain ⟨C, hC⟩ := hWb
  refine ⟨(latFinSet ℓ R).card * max C 0, by positivity, fun z hz => ?_⟩
  rw [latPer_eq_sum_finset hℓ hWs hz]
  calc ‖∑ m ∈ latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ)‖
      ≤ ∑ m ∈ latFinSet ℓ R, ‖(W (z + ℓ • latVec m) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ latFinSet ℓ R, max C 0 := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h := le_trans (hC (z + ℓ • latVec m)) (le_max_left C 0)
        simpa [RCLike.norm_ofReal, Real.norm_eq_abs] using h
    _ = (latFinSet ℓ R).card * max C 0 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The cut periodisation, as the finite sum of the cut summands. -/
lemma latPerCut_eq_sum {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    latPerCut ℓ W = ∑ m ∈ latFinSet ℓ R,
      (latBox ℓ).indicator (fun z : E3 => (W (z + ℓ • latVec m) : ℂ)) := by
  funext z
  by_cases hz : z ∈ latBox ℓ
  · rw [latPerCut, Set.indicator_of_mem hz, latPer_eq_sum_finset hℓ hWs hz, Finset.sum_apply]
    exact Finset.sum_congr rfl fun m _ =>
      (Set.indicator_of_mem hz (fun z : E3 => (W (z + ℓ • latVec m) : ℂ))).symm
  · rw [latPerCut, Set.indicator_of_notMem hz, Finset.sum_apply]
    exact (Finset.sum_eq_zero fun m _ =>
      Set.indicator_of_notMem hz (fun z : E3 => (W (z + ℓ • latVec m) : ℂ))).symm

/-- The cut periodisation is bounded. -/
lemma latPerCut_bdd {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖latPerCut ℓ W z‖ ≤ D := by
  obtain ⟨D, hD0, hD⟩ := latPer_bdd (R := R) hℓ hWb hWs
  refine ⟨D, hD0, fun z => ?_⟩
  by_cases hz : z ∈ latBox ℓ
  · rw [latPerCut, Set.indicator_of_mem hz]
    exact hD z hz
  · rw [latPerCut, Set.indicator_of_notMem hz, norm_zero]
    exact hD0

/-- The cut periodisation is a.e. strongly measurable. -/
lemma latPerCut_aestronglyMeasurable {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    AEStronglyMeasurable (latPerCut ℓ W) volume := by
  rw [latPerCut_eq_sum hℓ hWs]
  refine Finset.aestronglyMeasurable_sum _ fun m _ => ?_
  have haesm : AEStronglyMeasurable (fun z : E3 => (W (z + ℓ • latVec m) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hWm.comp_measurePreserving (by
        simpa [add_comm] using measurePreserving_add_left (volume : Measure E3) (ℓ • latVec m)))
  exact haesm.indicator (measurableSet_latBox ℓ)

/-- A bounded, a.e. strongly measurable complex function vanishing outside the closed cube is in
`L²`: such a function is compactly supported and bounded. -/
lemma memLp_of_bdd_of_latBox {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hmeas : AEStronglyMeasurable f volume) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hs : ∀ x, x ∉ latBox ℓ → f x = 0) : MemLp f 2 volume := by
  obtain ⟨C, hC⟩ := hb
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : E3) (Real.sqrt 3 * ℓ) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hx (hs x fun hmem => hc (latBox_subset_closedBall hℓ.le hmem))
  have hcomp : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) (Real.sqrt 3 * ℓ))
      (isClosed_tsupport f) (closure_minimal hsupp Metric.isClosed_closedBall)
  exact hcomp.memLp_of_bound hmeas (max C 0)
    (Eventually.of_forall fun x => le_trans (hC x) (le_max_left C 0))

/-- A bounded, a.e. strongly measurable complex function vanishing outside the closed ball of
radius `ρ` is in `L²`: such a function is compactly supported and bounded. -/
lemma memLp_of_bdd_of_supp {ρ : ℝ} (hρ : 0 ≤ ρ) {f : E3 → ℂ}
    (hmeas : AEStronglyMeasurable f volume) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hs : ∀ x, ρ < ‖x‖ → f x = 0) : MemLp f 2 volume := by
  obtain ⟨C, hC⟩ := hb
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : E3) ρ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hx (hs x (not_le.mp hc))
  have hcomp : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) ρ)
      (isClosed_tsupport f) (closure_minimal hsupp Metric.isClosed_closedBall)
  exact hcomp.memLp_of_bound hmeas (max C 0)
    (Eventually.of_forall fun x => le_trans (hC x) (le_max_left C 0))

/-- A bounded, a.e. strongly measurable complex function vanishing outside the closed ball of
radius `ρ` is integrable. -/
lemma integrable_of_bdd_of_supp {ρ : ℝ} (hρ : 0 ≤ ρ) {f : E3 → ℂ}
    (hmeas : AEStronglyMeasurable f volume) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hs : ∀ x, ρ < ‖x‖ → f x = 0) : Integrable f volume := by
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : E3) ρ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hx (hs x (not_le.mp hc))
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E3) ρ)) :=
    isFiniteMeasure_restrict.mpr (measure_closedBall_lt_top (x := (0 : E3)) (r := ρ)).ne
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  exact ((memLp_of_bdd_of_supp hρ hmeas hb hs).restrict _).integrable (q := 2) (by norm_num)

/-- The cut periodisation is in `L²` (it is bounded and compactly supported). -/
lemma latPerCut_memLp {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWm : AEStronglyMeasurable W volume) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    MemLp (latPerCut ℓ W) 2 volume := by
  obtain ⟨D, hD0, hD⟩ := latPerCut_bdd (R := R) hℓ hWb hWs
  refine memLp_of_bdd_of_latBox hℓ (latPerCut_aestronglyMeasurable hℓ hWm hWs) ⟨D, hD⟩ ?_
  intro z hz
  rw [latPerCut, Set.indicator_of_notMem hz]

end LatFourier

end Work.BoseBoxFock
