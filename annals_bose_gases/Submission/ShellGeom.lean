import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import ChallengeDeps
import Submission.RadialIntegral
import Submission.RadialRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coordinate and slicing infrastructure for the sphere-shell geometry

Everything is expressed in the coordinate spaces
`X3 := Fin 3 → ℝ` and `X2 := Fin 2 → ℝ` (carrying the product Lebesgue
measures).  `EuclideanSpace ℝ (Fin 3)` is the `ℓ²`-normed version of `X3`
(`WithLp 2 X3`), and its `volume` is measure-preservingly identified with the
product measure on `X3`.

The central geometric content is the **latitude cap measure** of the unit
sphere: for the first-coordinate unit vector `shellE0`,

    (volume.toSphere) {u ∈ S² | c ≤ u₀} = 2π (1 − c)   (0 ≤ c ≤ 1)

Equivalently the push-forward of `σ` under `u ↦ u₀` is `2π`-times Lebesgue
measure on `[−1,1]` (`shell_proj_measure`), and the integral of a function of
the first coordinate reduces to a one-dimensional integral
(`shell_coord0_integral`).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real ENNReal NNReal BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Coordinate space of three real numbers. -/
abbrev ShellX3 : Type := Fin 3 → ℝ

/-- Coordinate space of two real numbers. -/
abbrev ShellX2 : Type := Fin 2 → ℝ

/-- The unit sphere in `ℝ³`. -/
abbrev ShellS2 : Type := Metric.sphere (0 : ℝ³) 1

/-- Integral over `ℝ³` in terms of the coordinate space `X3`. -/
lemma shell_integral_coords3 (f : ShellX3 → ℝ) :
    (∫ x : ℝ³, f (WithLp.ofLp x)) = ∫ c : ShellX3, f c := by
  have h := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h' := MeasurePreserving.integral_comp' h f
  simpa [MeasurableEquiv.coe_toLp_symm] using h'

/-- Integral over `ℝ²` in terms of the coordinate space `X2`. -/
lemma shell_integral_coords2 (f : ShellX2 → ℝ) :
    (∫ x : ℝ², f (WithLp.ofLp x)) = ∫ c : ShellX2, f c := by
  have h := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have h' := MeasurePreserving.integral_comp' h f
  simpa [MeasurableEquiv.coe_toLp_symm] using h'

/-- Squared norm on `ℝ³` in coordinates: `‖x‖² = Σᵢ (x i)²`. -/
lemma shell_sq_norm3 (x : ℝ³) : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  calc
    ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x i‖ ^ 2 := by
      simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) x)
    _ = ∑ i : Fin 3, (x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.norm_eq_abs, sq_abs]

/-- Squared norm on `ℝ²` in coordinates: `‖w‖² = Σᵢ (w i)²`. -/
lemma shell_sq_norm2 (w : ℝ²) : ‖w‖ ^ 2 = ∑ i : Fin 2, (w i) ^ 2 := by
  calc
    ‖w‖ ^ 2 = ∑ i : Fin 2, ‖w i‖ ^ 2 := by
      simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 2 => ℝ) w)
    _ = ∑ i : Fin 2, (w i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.norm_eq_abs, sq_abs]

/-- The standard unit vector along coordinate `0` of `ℝ³`. -/
noncomputable def shellE0 : ℝ³ := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma shellE0_coord (i : Fin 3) : (shellE0 : ℝ³) i = if i = 0 then 1 else 0 := by
  simp [shellE0, EuclideanSpace.single_apply]

lemma shellE0_coord0 : (shellE0 : ℝ³) 0 = 1 := by simp [shellE0, EuclideanSpace.single_apply]

lemma shellE0_coord_of_ne {i : Fin 3} (hi : i ≠ 0) : (shellE0 : ℝ³) i = 0 := by
  simp [shellE0, EuclideanSpace.single_apply, hi]

lemma shellE0_norm : ‖(shellE0 : ℝ³)‖ = 1 := by
  have hs : ‖(shellE0 : ℝ³)‖ ^ 2 = 1 := by
    rw [shell_sq_norm3]
    simp [shellE0_coord]
  have hn : 0 ≤ ‖(shellE0 : ℝ³)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖(shellE0 : ℝ³)‖]

lemma shellE0_mem : shellE0 ∈ Metric.sphere (0 : ℝ³) 1 := by
  simp [Metric.mem_sphere, dist_zero_right, shellE0_norm]

/-- `EuclideanSpace.single 0 1` as an element of the unit sphere. -/
noncomputable def shellE0S2 : ShellS2 := ⟨shellE0, shellE0_mem⟩

/-- Insertion of coordinate `0`: `x` with `x 0 = t` and coordinates `1,2` equal to `w`. -/
noncomputable def shellInsert0 (t : ℝ) (w : ShellX2) : ShellX3 :=
  Fin.insertNth (α := fun _ : Fin 3 => ℝ) 0 t w

lemma shellInsert0_coord0 (t : ℝ) (w : ShellX2) : (shellInsert0 t w) 0 = t := by
  simp [shellInsert0]

/-- The coordinates `1,2` of a 3-vector. -/
noncomputable def shellTail (x : ShellX3) : ShellX2 := Fin.removeNth (0 : Fin 3) x

lemma shellInsert0_tail (t : ℝ) (w : ShellX2) : shellTail (shellInsert0 t w) = w := by
  funext j
  simp [shellTail, shellInsert0]

lemma shellTail_coord (x : ShellX3) (j : Fin 2) :
    x ((0 : Fin 3).succAbove j) = (shellTail x) j := rfl

lemma shellInsert0_inverse (x : ShellX3) : shellInsert0 (x 0) (shellTail x) = x := by
  simp [shellInsert0, shellTail]

/-- Fubini peeling of coordinate 0: `∫_x f = ∫_t ∫_w f (insert 0 t w)`, for
integrable `f`. -/
lemma shell_integral_peel0 (f : ShellX3 → ℝ) (hf : Integrable f) :
    (∫ x : ShellX3, f x) =
      (∫ t : ℝ, ∫ w : ShellX2, f (shellInsert0 t w)) := by
  let e : ShellX3 ≃ᵐ (ℝ × ShellX2) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have hmp : MeasurePreserving e volume volume := by
    exact MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have hemb : MeasurableEmbedding e := MeasurableEquiv.measurableEmbedding e
  have hint : Integrable (fun y : ℝ × ShellX2 => f (e.symm y)) := by
    have hback : Integrable (fun x : ShellX3 => (fun y : ℝ × ShellX2 => f (e.symm y)) (e x)) := by
      simpa using hf
    exact (hmp.integrable_comp_emb hemb).mp hback
  have h1 : (∫ x : ShellX3, f x) = ∫ y : ℝ × ShellX2, f (e.symm y) := by
    have h' := MeasurePreserving.integral_comp' hmp (fun y : ℝ × ShellX2 => f (e.symm y))
    have hfun : (fun x : ShellX3 => (f ∘ e.symm) (e x)) = f := by
      funext x
      simp
    rw [← hfun]
    exact h'
  have hprod : (∫ y : ℝ × ShellX2, f (e.symm y)) =
      (∫ t : ℝ, ∫ w : ShellX2, f (e.symm (t, w))) := by
    exact MeasureTheory.integral_prod (f := fun y : ℝ × ShellX2 => f (e.symm y)) hint
  have heq : (fun y : ℝ × ShellX2 => f (e.symm y)) =
      (fun y : ℝ × ShellX2 => f (shellInsert0 y.1 y.2)) := by
    funext y
    congr 1
  calc
    (∫ x : ShellX3, f x) = ∫ y : ℝ × ShellX2, f (e.symm y) := h1
    _ = (∫ t : ℝ, ∫ w : ShellX2, f (e.symm (t, w))) := hprod
    _ = (∫ t : ℝ, ∫ w : ShellX2, f (shellInsert0 t w)) := by
          apply congrArg (fun h : ℝ → ℝ => ∫ t : ℝ, h t)
          funext t
          apply congrArg (fun h : ShellX2 → ℝ => ∫ w : ShellX2, h w)
          funext w
          exact congrFun heq (t, w)

/-- The open half line `(0,∞)`. -/
abbrev ShellRpos : Type := Set.Ioi (0 : ℝ)

lemma shell_finrank : Module.finrank ℝ ℝ³ = 3 := by simp

lemma shell_toSphere_total :
    (volume.toSphere : Measure ShellS2).real Set.univ = 4 * π := by
  rw [MeasureTheory.Measure.toSphere_real_apply_univ]
  rw [shell_finrank]
  norm_num
  rw [measureReal_unitBall_r3]
  norm_num
  ring

lemma shell_toSphere_finite : IsFiniteMeasure (volume.toSphere : Measure ShellS2) := by
  infer_instance

instance shell_toSphere_sfinite : SFinite (volume.toSphere : Measure ShellS2) := by
  infer_instance

/-- The radius in polar decomposition reconstructs a non-zero vector: for
`x ≠ 0`, `‖x‖ • (‖x‖⁻¹ • x) = x`. -/
lemma shell_unitSphere_decompose_self (x : ({0}ᶜ : Set ℝ³)) :
    ((homeomorphUnitSphereProd ℝ³ x).2 : ℝ) • ((homeomorphUnitSphereProd ℝ³ x).1 : ℝ³) =
      (x : ℝ³) := by
  rw [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
  have hx0 : ‖(x : ℝ³)‖ ≠ 0 := by
    simpa using (norm_ne_zero_iff.mpr x.2)
  calc
    (‖(x : ℝ³)‖ : ℝ) • (‖(x : ℝ³)‖⁻¹ • (x : ℝ³)) =
        (‖(x : ℝ³)‖ * ‖(x : ℝ³)‖⁻¹) • (x : ℝ³) := by rw [smul_smul]
    _ = (1 : ℝ) • (x : ℝ³) := by rw [mul_inv_cancel₀ hx0]
    _ = (x : ℝ³) := by simp

/-- **Polar decomposition of the volume integral (unconditional)**:
`∫_y f y = ∫_{(u,ρ) ∈ S²×(0,∞)} f(ρ•u)` w.r.t. the product of the sphere
measure and `ρ² dρ`. -/
lemma shell_integral_polar (f : ℝ³ → ℝ) :
    (∫ x : ℝ³, f x) =
      (∫ z : ShellS2 × ShellRpos, f ((z.2 : ℝ) • (z.1 : ℝ³))
        ∂((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2))) := by
  have hmp : MeasurePreserving (homeomorphUnitSphereProd ℝ³)
      (volume.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³))
      ((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := by
    simpa using (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd (μ := (volume : Measure ℝ³)))
  have h1 : (∫ x : ({0}ᶜ : Set ℝ³), f x.1 ∂(volume.comap Subtype.val)) = ∫ x : ℝ³, f x := by
    rw [integral_subtype_comap (measurableSet_singleton (0 : ℝ³)).compl f]
    rw [restrict_compl_singleton]
  have hemb : MeasurableEmbedding (homeomorphUnitSphereProd ℝ³) :=
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd ℝ³))
  have h2 := MeasurePreserving.integral_comp (μ := volume.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³))
    (ν := (volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) hmp hemb
    (fun z : ShellS2 × ShellRpos => f ((z.2 : ℝ) • (z.1 : ℝ³)))
  have hinterm : (fun x : ({0}ᶜ : Set ℝ³) => f x.1) =
      (fun x : ({0}ᶜ : Set ℝ³) => (fun z : ShellS2 × ShellRpos => f ((z.2 : ℝ) • (z.1 : ℝ³)))
        (homeomorphUnitSphereProd ℝ³ x)) := by
    funext x
    congr 1
    exact (shell_unitSphere_decompose_self x).symm
  have hcong := congrArg (fun g : ({0}ᶜ : Set ℝ³) → ℝ =>
      ∫ x : ({0}ᶜ : Set ℝ³), g x ∂(volume.comap Subtype.val)) hinterm
  calc
    (∫ x : ℝ³, f x) = ∫ x : ({0}ᶜ : Set ℝ³), f x.1 ∂(volume.comap Subtype.val) := h1.symm
    _ = ∫ z : ShellS2 × ShellRpos, f ((z.2 : ℝ) • (z.1 : ℝ³))
        ∂((volume.toSphere : Measure ShellS2).prod (Measure.volumeIoiPow 2)) := hcong.trans h2



/-- The measure `volumeIoiPow 2` on `(0,∞)`: `∫ f dν = ∫₀^∞ s²·f(s) ds`. -/
lemma shell_volumeIoiPow_integral (f : ℝ → ℝ) :
    (∫ r : ShellRpos, f (r : ℝ) ∂(Measure.volumeIoiPow 2)) =
      ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * f s := by
  rw [Measure.volumeIoiPow]
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul₀]
  · have hsub : (∫ x : ShellRpos, (Real.toNNReal ((x : ℝ) ^ 2) : ℝ≥0) • f (x : ℝ)
          ∂(Measure.comap (Subtype.val : ShellRpos → ℝ) volume))
        = ∫ s in Set.Ioi (0 : ℝ), (Real.toNNReal (s ^ 2) : ℝ≥0) • f s :=
        integral_subtype_comap (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
          (fun s : ℝ => (Real.toNNReal (s ^ 2) : ℝ≥0) • f s)
    calc
      (∫ x : ShellRpos, (Real.toNNReal ((x : ℝ) ^ 2) : ℝ≥0) • f (x : ℝ)
          ∂(Measure.comap (Subtype.val : ShellRpos → ℝ) volume))
          = ∫ s in Set.Ioi (0 : ℝ), (Real.toNNReal (s ^ 2) : ℝ≥0) • f s := hsub
      _ = ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * f s := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          change (Real.toNNReal (s ^ 2) : ℝ≥0) • f s = s ^ 2 * f s
          rw [NNReal.smul_def]
          congr 1
          exact Real.coe_toNNReal (s ^ 2) (sq_nonneg s)
  · exact (measurable_subtype_coe.pow_const 2).real_toNNReal.aemeasurable


end Submission.BoseGases
