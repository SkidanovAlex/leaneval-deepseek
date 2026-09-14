import Mathlib
import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Module MeasureTheory
open scoped Real BigOperators Pointwise
set_option autoImplicit false

/-!
# Gaussian measure on a finite-dimensional Euclidean space

Following the paper (Section 2.2, 6.1), for `s > 0` and a measurable set `S ⊆ E`,

`γ_s(S) := ∫_{S/s} e^{-π‖x‖²} dx`,

with `γ := γ₁`.  (Here `S/s = {x | s·x ∈ S}`.)

This module records the basic facts needed for the analytic part of the proof:

* the total mass identity `∫_E e^{-π‖x‖²} dx = 1` (hence `γ_s(E) = 1`);
* the standard Gaussian integral `∫_E e^{-b‖x‖²} dx = (π/b)^{n/2}`
  (from mathlib's `GaussianFourier.integral_rexp_neg_mul_sq_norm`).

The Voronoi-cell module (`Submission/Voronoi.lean`) provides the cell; combining
them yields Lemma rho_gamma (`ρ_s(ℒ)·γ_s(V(ℒ)) ≤ 1`) once the tiling
`V(ℒ) + ℒ = E` (measure-zero overlaps) is formalized.
-/

namespace Submission.GaussianMeasure

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The standard Gaussian density mass of a (measurable) set at parameter `s`:  -/
noncomputable def gammaMass (s : ℝ) (S : Set E) : ℝ :=
  ∫ x in {y : E | s • y ∈ S}, rexp (-Real.pi * ‖x‖ ^ 2)

/-- Total Gaussian mass of the space is `1`. -/
lemma gammaMass_univ (s : ℝ) (_hs : 0 < s) : gammaMass s (Set.univ : Set E) = 1 := by
  dsimp [gammaMass]
  have hset : {y : E | s • y ∈ Set.univ} = Set.univ := by ext; simp
  rw [hset]
  rw [MeasureTheory.setIntegral_univ]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := Real.pi) Real.pi_pos
  rw [h]
  have hfin : Module.finrank ℝ E = n := by simp
  rw [hfin]
  rw [div_self Real.pi_ne_zero]
  rw [Real.one_rpow]

/-- `γ₁(S) = ∫_S e^{-π‖x‖²} dx` when `1 • y ∈ S ↔ y ∈ S`. -/
lemma gammaMass_one (S : Set E) : gammaMass 1 S = ∫ x in S, rexp (-Real.pi * ‖x‖ ^ 2) := by
  dsimp [gammaMass]
  congr 1
  ext x
  simp

/-- The standard Gaussian integral with parameter `b > 0`. -/
lemma integral_exp_neg_b_mul_sq_norm (b : ℝ) (hb : 0 < b) :
    (∫ x : E, rexp (-b * ‖x‖ ^ 2)) = (Real.pi / b) ^ (n / 2 : ℝ) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := b) hb
  rw [h]
  congr 1
  simp


/-- The standard Gaussian density is integrable on the whole space. -/
lemma gaussian_density_integrable :
    MeasureTheory.Integrable (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2)) := by
  refine MeasureTheory.Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_b_mul_sq_norm Real.pi Real.pi_pos]
  rw [div_self Real.pi_ne_zero]
  rw [Real.one_rpow]
  norm_num

/-- `γ_s` is monotone in the set (the density is nonnegative). -/
lemma gammaMass_mono_set (s : ℝ) {A B : Set E} (hAB : A ⊆ B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    gammaMass s A ≤ gammaMass s B := by
  dsimp [gammaMass]
  refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
  · exact gaussian_density_integrable.integrableOn
  · refine Filter.Eventually.of_forall ?_
    intro x
    exact (Real.exp_pos _).le
  · refine Filter.Eventually.of_forall ?_
    intro x hx
    exact hAB hx


/-- Scale identity: `γ_{1/t}(K) = ∫_{t•K} e^{-π‖x‖²}` for `t ≠ 0`. -/
lemma gammaMass_inv_smul_set (t : ℝ) (ht : t ≠ 0) (K : Set E) :
    gammaMass (1 / t) K = ∫ x in t • K, rexp (-Real.pi * ‖x‖ ^ 2) := by
  have hset : {y : E | (1 / t) • y ∈ K} = t • K := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_smul_set]
      refine ⟨(1 / t) • y, hy, ?_⟩
      rw [smul_smul]
      field_simp [ht]
      simp
    · intro hy
      rw [Set.mem_smul_set] at hy
      rcases hy with ⟨k, hk, hyk⟩
      rw [← hyk]
      rw [Set.mem_ofPred_eq]
      rw [smul_smul]
      field_simp [ht]
      simpa using hk
  dsimp [gammaMass]
  rw [hset]

end Submission.GaussianMeasure


/-! ## Rank-generic Gaussian mass and isometry invariance

The ambient-`EuclideanSpace`-specific `gammaMass` above suffices for full-rank lattices, but
the boundary case of `gamma_stable_of_two_le` must transport Gaussian masses through
isometries between a lattice's real span and the standard space (and later between direct-sum
factors).  The generic definitions below are the transport backbone: `gammaMassGen` agrees
with `gammaMass` on `EuclideanSpace`, and `gammaMassGen_transport` is the invariance of the
Gaussian mass under any (linear) isometry `e : X ≃ₗᵢ Y`:

`γ(s, A)` over `Y` = `γ(s, e⁻¹A)` over `X`

(proved via `MeasurePreserving.setIntegral_preimage_emb` for `e` — a linear isometry between
finite-dimensional spaces is measure-preserving — plus the norm identity `‖e x‖ = ‖x‖`).
-/

section Generic

variable {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [FiniteDimensional ℝ Y]

/-- Gaussian mass on an arbitrary finite-dimensional real inner product space. -/
noncomputable def gammaMassGen (s : ℝ) (K : Set X) : ℝ :=
  ∫ x in {y : X | s • y ∈ K}, rexp (-Real.pi * ‖x‖ ^ 2)

/-- The Gaussian mass is invariant under (linear) isometries:
`γ(s, A)` in `Y` equals `γ(s, e⁻¹A)` in `X` for `e : X ≃ₗᵢ Y`. -/
lemma gammaMassGen_transport (e : X ≃ₗᵢ[ℝ] Y) (s : ℝ) (A : Set Y) :
    gammaMassGen s A = gammaMassGen (X := X) s (e ⁻¹' A) := by
  have hmp : MeasurePreserving (e : X → Y) volume volume := e.measurePreserving
  have hemb : MeasurableEmbedding (e : X → Y) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  let h : Y → ℝ := fun y => rexp (-Real.pi * ‖y‖ ^ 2)
  have hpre : (e : X → Y) ⁻¹' {y : Y | s • y ∈ A} = {x : X | s • x ∈ e ⁻¹' A} := by
    ext x
    constructor
    · intro hx
      change s • (e x) ∈ A at hx
      change e (s • x) ∈ A
      have hlin : e (s • x) = s • e x := (e : X →ₗ[ℝ] Y).map_smul s x
      rw [← hlin] at hx
      exact hx
    · intro hx
      change e (s • x) ∈ A at hx
      change s • (e x) ∈ A
      have hlin : e (s • x) = s • e x := (e : X →ₗ[ℝ] Y).map_smul s x
      rw [hlin] at hx
      exact hx
  have hfun : (fun x : X => h (e x)) = fun x : X => rexp (-Real.pi * ‖x‖ ^ 2) := by
    funext x
    dsimp [h]
    congr 1
    rw [e.norm_map]
  have h1 := hmp.setIntegral_preimage_emb hemb h {y : Y | s • y ∈ A}
  calc
    gammaMassGen s A = ∫ y in {y : Y | s • y ∈ A}, h y := rfl
    _ = ∫ x in (e : X → Y) ⁻¹' {y : Y | s • y ∈ A}, h (e x) := h1.symm
    _ = ∫ x in {x : X | s • x ∈ e ⁻¹' A}, rexp (-Real.pi * ‖x‖ ^ 2) := by
        rw [hpre]
        rw [hfun]
    _ = gammaMassGen (X := X) s (e ⁻¹' A) := rfl

end Generic
