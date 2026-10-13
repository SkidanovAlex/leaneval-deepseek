import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.Cyl.fderiv_rho_theta_eR
import Submission.Work.Cyl.fderiv_rho_theta_eZ
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.FTS.FireFix.Clauses.opNorm_le_frame
import Submission.Work.FTS.FireFix.Clauses.eTheta_deriv_bound
import Submission.Work.FTS.FireFix.Clauses.Fstar_bounds
import Submission.Work.FTS.FireFix.Clauses.rho_theta_sect
import Submission.Work.FTS.FireFix.Clauses.fderiv_rho_theta_eTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-- `ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **If the Fréchet derivative of `F` is bounded almost everywhere by a locally integrable
function, then `x ↦ fderiv ℝ F x` is locally integrable.**  (Measurability of `fderiv` is free:
`measurable_fderiv`.) -/
theorem locallyIntegrable_fderiv_of_ae_bound {F : R3 → R3} {Ψ : R3 → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrable Ψ MeasureTheory.volume)
    (hbd : ∀ᵐ x ∂MeasureTheory.volume, ‖fderiv ℝ F x‖ ≤ Ψ x) :
    MeasureTheory.LocallyIntegrable (fun x : R3 => fderiv ℝ F x) MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  refine MeasureTheory.Integrable.mono' (hΨ.integrableOn_isCompact hK) ?_ ?_
  · exact (measurable_fderiv ℝ F).aestronglyMeasurable.restrict
  · filter_upwards [MeasureTheory.ae_restrict_of_ae hbd] with x hx using hx

/-- The coordinate hyperplane `{x | x i = 0}` in `ℝ³` is null. -/
theorem volume_coord_eq_zero (i : Fin 3) : MeasureTheory.volume {x : R3 | x i = 0} = 0 := by
  have hker : {x : R3 | x i = 0}
      = ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ).ker := by
    ext x
    simp [LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule MeasureTheory.volume _ (fun htop => ?_)
  have hzero : ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ) = 0 :=
    LinearMap.ker_eq_top.mp htop
  have h1 := congrArg (fun (L : R3 →ₗ[ℝ] ℝ) => L (FiniteTimeSingularity.e i)) hzero
  simp only [LinearMap.zero_apply] at h1
  have hproj :
      (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] ℝ)
        (FiniteTimeSingularity.e i)) = 1 := by
    simp [EuclideanSpace.proj, FiniteTimeSingularity.e]
  rw [hproj] at h1
  exact one_ne_zero h1

/-- The axis `{x : ℝ³ | r(x) = 0}` is null. -/
theorem volume_radial_eq_zero : MeasureTheory.volume {x : R3 | Work.Cyl.radial x = 0} = 0 := by
  have hsub : {x : R3 | Work.Cyl.radial x = 0} ⊆ {x : R3 | x 0 = 0} ∪ {x : R3 | x 1 = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Work.Cyl.radial_eq_zero_iff] at hx
    exact Or.inl hx.1
  exact measure_mono_null hsub
    (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))

/-- The equatorial plane `{x : ℝ³ | x₃ = 0}` is null. -/
theorem volume_axial_eq_zero : MeasureTheory.volume {x : R3 | Work.Cyl.axial x = 0} = 0 := by
  have hsub : {x : R3 | Work.Cyl.axial x = 0} ⊆ {x : R3 | x 2 = 0} := by
    intro x hx
    simpa [Work.Cyl.axial] using hx
  exact measure_mono_null hsub (volume_coord_eq_zero 2)

/-! ## 3. The local section of `x ↦ (ρ(x)^{3α}/B, θ(x))`

For `x` off the axis, the point

  `sect x (z,θ) = (Bz)^{1/(3α)} • (cos θ • e_R(x) + sin θ • e_z)`

lies in the meridian half-plane spanned by `e_R(x)` and `e_z` and has self-similar variable `z` and
angle `θ`; it provides the local right inverse needed to transfer the differentiability of a
composite `x ↦ P (ρ(x)^{3α}/B) (θ(x))` back to the two-variable function `P`. -/

/-- The local section of `(ρ,θ)` through `x` (in the meridian half-plane of `x`). -/
noncomputable def sect (α B : ℝ) (x : R3) (p : ℝ × ℝ) : R3 :=
  (B * p.1) ^ (1 / (3 * α)) • (Real.cos p.2 • Work.Cyl.eR x + Real.sin p.2 • Work.Cyl.eZ)

lemma sect_diff {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3) {z θ : ℝ}
    (hz : 0 < z) : DifferentiableAt ℝ (sect α B x) (z, θ) := by
  have hBz : B * z ≠ 0 := by positivity
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => (B * p.1) ^ (1 / (3 * α))) (z, θ) := by
    have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => B * p.1) (z, θ) := by fun_prop
    exact h2.rpow_const (Or.inl hBz)
  have h3 : DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      Real.cos p.2 • Work.Cyl.eR x + Real.sin p.2 • Work.Cyl.eZ) (z, θ) := by fun_prop
  exact h1.smul h3

lemma sect_rho {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) {z θ : ℝ} (hz : 0 < z) (hθ : |θ| < Real.pi / 2) :
    Work.Cyl.rho (sect α B x (z, θ)) = (B * z) ^ (1 / (3 * α)) :=
  (rho_theta_sect x hr (Real.rpow_pos_of_pos (by positivity) _) hθ).1

lemma sect_theta {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) {z θ : ℝ} (hz : 0 < z) (hθ : |θ| < Real.pi / 2) :
    Work.Cyl.theta (sect α B x (z, θ)) = θ :=
  (rho_theta_sect x hr (Real.rpow_pos_of_pos (by positivity) _) hθ).2

/-- `ρ(x) = ρP(r(x), x₃)`. -/
lemma rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho]
  congr 1
  rw [← Work.Cyl.radial_sq]

/-- `cos θ(x) = r(x)/ρ(x)` off the axis. -/
lemma cos_theta_eq (x : R3) (hr : 0 < Work.Cyl.radial x) :
    Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  have hθ : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [hθ, Work.Cyl.cos_thetaP hr (Work.Cyl.axial x), rho_eq_rhoP x]

/-- `sin θ(x) = x₃/ρ(x)` off the axis. -/
lemma sin_theta_eq (x : R3) (hr : 0 < Work.Cyl.radial x) :
    Real.sin (Work.Cyl.theta x) = Work.Cyl.axial x / Work.Cyl.rho x := by
  have hθ : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [hθ, Work.Cyl.sin_thetaP hr (Work.Cyl.axial x), rho_eq_rhoP x]

/-- The section through `x` is a right inverse at `x` itself. -/
lemma sect_self {α B : ℝ} (hα : 0 < α) (hB : 0 < B) (x : R3)
    (hr : 0 < Work.Cyl.radial x) :
    sect α B x (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x) = x := by
  have hr0 : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have h1 : (B * (Work.Cyl.rho x ^ (3 * α) / B)) ^ (1 / (3 * α)) = Work.Cyl.rho x := by
    rw [mul_div_cancel₀ _ (ne_of_gt hB), ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    have hexp : (3 * α) * (1 / (3 * α)) = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  have h2 : Work.Cyl.radial x • Work.Cyl.eR x = Work.Cyl.radialVec x := by
    rw [Work.Cyl.eR, smul_smul, mul_one_div, div_self hr0, one_smul]
  have h3 : Work.Cyl.radialVec x + Work.Cyl.axial x • Work.Cyl.eZ = x := by
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.radialVec, Work.Cyl.eZ, Work.Cyl.axial, FiniteTimeSingularity.e]
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hρne : Work.Cyl.rho x ≠ 0 := ne_of_gt hρpos
  have h4 : Work.Cyl.rho x * (Work.Cyl.radial x / Work.Cyl.rho x) = Work.Cyl.radial x := by
    rw [mul_comm, div_mul_cancel₀ _ hρne]
  have h5 : Work.Cyl.rho x * (Work.Cyl.axial x / Work.Cyl.rho x) = Work.Cyl.axial x := by
    rw [mul_comm, div_mul_cancel₀ _ hρne]
  rw [sect, h1, cos_theta_eq x hr, sin_theta_eq x hr, smul_add, smul_smul, smul_smul, h4, h5, h2]
  exact h3

/-- **Differentiability of a two-variable function from that of its composition with
`x ↦ (ρ(x)^{3α}/B, θ(x))`.**  Since the latter has the local section `sect x` (through `x`), the
composition is differentiable at `x` exactly when the two-variable function is differentiable at
the image point. -/
lemma diffAt2_of_comp_sect {α B : ℝ} {P : ℝ → ℝ → ℝ} (hα : 0 < α) (hB : 0 < B)
    (x : R3) (hr : 0 < Work.Cyl.radial x)
    (hG : DifferentiableAt ℝ (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y))
      x) :
    Work.Cyl.DiffAt2 P (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x) := by
  set z₀ : ℝ := Work.Cyl.rho x ^ (3 * α) / B with hz₀
  set θ₀ : ℝ := Work.Cyl.theta x with hθ₀
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  have hz0pos : 0 < z₀ := by
    rw [hz₀]
    exact div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hθ₀mem : |θ₀| < Real.pi / 2 := by
    rw [hθ₀, Work.Cyl.theta]
    exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hsect : DifferentiableAt ℝ (sect α B x) (z₀, θ₀) := sect_diff hα hB x hz0pos
  have hsectx : sect α B x (z₀, θ₀) = x := by rw [hz₀, hθ₀]; exact sect_self hα hB x hr
  have hGs : DifferentiableAt ℝ
      (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y)) (sect α B x (z₀, θ₀)) := by
    rw [hsectx]; exact hG
  have hcomp : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (fun y : R3 => P (Work.Cyl.rho y ^ (3 * α) / B) (Work.Cyl.theta y))
        (sect α B x p)) (z₀, θ₀) :=
    hGs.comp (z₀, θ₀) hsect
  refine hcomp.congr_of_eventuallyEq ?_
  have hnb : {p : ℝ × ℝ | 0 < p.1 ∧ |p.2| < Real.pi / 2} ∈ 𝓝 (z₀, θ₀) := by
    refine IsOpen.mem_nhds ?_ ⟨hz0pos, hθ₀mem⟩
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  filter_upwards [hnb] with p hp
  obtain ⟨hpz, hpθ⟩ := hp
  show P p.1 p.2 = P (Work.Cyl.rho (sect α B x p) ^ (3 * α) / B)
    (Work.Cyl.theta (sect α B x p))
  rw [sect_rho hα hB x hr hpz hpθ, sect_theta hα hB x hr hpz hpθ]
  congr 1
  rw [← Real.rpow_mul (show (0 : ℝ) ≤ B * p.1 by positivity)]
  have hexp : (1 / (3 * α)) * (3 * α) = 1 := by field_simp
  rw [hexp, Real.rpow_one]
  field_simp

/-! ## 4. The pointwise majorant of the vorticity's derivative

`psiBound α A B g τ N Npz L z θ` is the function of the self-similar variables `(z,θ)` that
dominates the Fréchet derivative of the vorticity slice `physVort α A B g · τ` at every point with
self-similar variable `z` and angle `θ`, for a profile whose perturbation is bounded by `N` with
`z`-derivative bounded by `Npz` and supported in `z ≤ L`.  It is a sum of the three elementary
pieces of the bound

  `‖∂_x ω‖ ≤ |A(τ)⁻¹| · ( M_F · 2/r + 2·(∂_ρ F̃ + ∂_θ F̃ / ρ) )`,

with `F̃(ρ,θ) = F(ρ^{3α}/B, θ)`, `M_F = 20·3α + N`, `ρ = (Bz)^{1/(3α)}` and `r = ρ cos θ`. -/
noncomputable def psiBound (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ N Npz L : ℝ) (z θ : ℝ) : ℝ :=
  if z ≤ L then
    |(A τ)⁻¹| * ((20 * (3 * α) + N) * (2 / ((B τ * z) ^ (1 / (3 * α)) * Real.cos θ))
      + 2 * (((3 * α) / (B τ)) * (B τ * z) ^ ((3 * α - 1) / (3 * α)) * (60 * α + Npz)
        + (200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ)|)
          / (B τ * z) ^ (1 / (3 * α))))
  else 0

lemma psiBound_nonneg (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ N Npz L z θ : ℝ)
    {Bpos : 0 < B τ} (hN : 0 ≤ N) (hNpz : 0 ≤ Npz) (hα : 0 < α) (hz : 0 ≤ z)
    (hθ : |θ| ≤ Real.pi / 2) :
    0 ≤ psiBound α A B g τ N Npz L z θ := by
  have hρ : 0 ≤ (B τ * z) ^ (1 / (3 * α)) := Real.rpow_nonneg (by positivity) _
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp hθ).1, (abs_le.mp hθ).2⟩
  have hsin : 0 ≤ Real.sin (abs θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [hθ, Real.pi_pos])
  have hAθ : 0 ≤ 200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α))
      (Real.rpow_nonneg hsin _)) (Real.rpow_nonneg hcos _)
  have hX : 0 ≤ (20 * (3 * α) + N) * (2 / ((B τ * z) ^ (1 / (3 * α)) * Real.cos θ)) :=
    mul_nonneg (by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 20) hα.le])
      (div_nonneg (by norm_num) (mul_nonneg hρ hcos))
  have hY : 0 ≤ ((3 * α) / (B τ)) * (B τ * z) ^ ((3 * α - 1) / (3 * α)) * (60 * α + Npz) :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith [hα.le]) Bpos.le)
      (Real.rpow_nonneg (by positivity) _)) (by linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 60) hα.le])
  have hZ : 0 ≤ (200 * α ^ 2 * (Real.sin (abs θ)) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
      + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ)|)
      / (B τ * z) ^ (1 / (3 * α)) :=
    div_nonneg (by linarith [hAθ, abs_nonneg (Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (abs θ))]) hρ
  unfold psiBound
  split_ifs with h
  · exact mul_nonneg (abs_nonneg _) (by linarith)
  · exact le_refl 0

/-- **The `z`-derivative of the profile is bounded** by `60α + Npz`. -/
lemma abs_pz_profile_le {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {Npz : ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => g q.1 θ q.2) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (fun z' => Work.ConstructionInstance.profile (3 * α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) z| ≤ 60 * α + Npz := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hfun : (fun z' => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z' θ)
      = fun z' => Work.Construction.Fstar (3 * α) z' θ + g z' θ τ := by
    funext z'
    exact Work.ConstructionInstance.profile_of_nonneg hθ0
  rw [hfun]
  have hdiffFM : DifferentiableAt ℝ (fun z' : ℝ => Work.FM.Fstar z') z := by
    have hnum : DifferentiableAt ℝ (fun z' : ℝ => 2 * z') z := by fun_prop
    have hden : DifferentiableAt ℝ (fun z' : ℝ => (1 + z') ^ 2) z := by fun_prop
    have hne : (1 + z) ^ 2 ≠ 0 := by
      have h1 : (1 : ℝ) + z ≠ 0 := by positivity
      exact pow_ne_zero 2 h1
    have h := hnum.div hden hne
    have hfun : (fun z' : ℝ => Work.FM.Fstar z')
        = (fun z' => 2 * z') * (fun z' => (1 + z') ^ 2)⁻¹ := by
      funext z'; simp [Work.FM.Fstar, div_eq_mul_inv]
    rwa [hfun]
  have hdiff1 : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (3 * α) z' θ) z := by
    have hconst : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
        = fun z' => (3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))
            * Work.FM.Fstar z' := rfl
    rw [hconst]
    exact hdiffFM.const_mul _
  have hdiff2 : DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
    have hmem : (z, τ) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) := by
      refine ⟨?_, ?_⟩
      · show (-1 : ℝ) < z; linarith
      · show τ ∈ Set.Ioo (-1 : ℝ) (S + 1)
        exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hopen : Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) ∈ 𝓝 (z, τ) :=
      (isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem
    have hd := (hcont θ hθ).differentiableOn (one_ne_zero)
    have hd' : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
      hd.differentiableAt hopen
    exact hd'.comp z (by fun_prop : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z)
  have hsum : (fun z' => Work.Construction.Fstar (3 * α) z' θ + g z' θ τ)
      = (fun z' => Work.Construction.Fstar (3 * α) z' θ) + (fun z' => g z' θ τ) := rfl
  rw [hsum, deriv_add hdiff1 hdiff2]
  have h1 := (Work.FTS.FireFix.Clauses.Fstar_bounds hα hα13).2.1 z θ hz hθ
  have h2 : |deriv (fun z' => g z' θ τ) z| ≤ Npz := by
    have heq : deriv (fun z' => g z' θ τ) z = Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ := rfl
    rw [heq]
    exact hNpz z θ τ hz hθ hτ
  calc |deriv (fun z' => Work.Construction.Fstar (3 * α) z' θ) z + deriv (fun z' => g z' θ τ) z|
      ≤ |deriv (fun z' => Work.Construction.Fstar (3 * α) z' θ) z|
        + |deriv (fun z' => g z' θ τ) z| := abs_add_le _ _
    _ ≤ 60 * α + Npz := by linarith


/-! ## 5. The positive branch of the profile and its angular derivative bound -/

/-- The positive branch `F_* + g` of the profile (which is the profile itself for `θ ≥ 0`). -/
noncomputable def Ppos (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ z θ : ℝ) : ℝ :=
  Work.Construction.Fstar (3 * α) z θ + g z θ τ

lemma profile_eq_Ppos {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hθ : 0 ≤ θ) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
      = Ppos α g τ z θ :=
  Work.ConstructionInstance.profile_of_nonneg hθ

lemma profile_eq_neg_Ppos {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hθ : ¬ 0 ≤ θ) :
    Work.ConstructionInstance.profile (3 * α) (Work.FTS.Regularity.gSlice g τ) z θ
      = - Ppos α g τ z (-θ) :=
  Work.ConstructionInstance.profile_of_neg hθ

/-- Differentiability of `θ' ↦ F_*(z,θ')` on the open angular interval. -/
lemma differentiableAt_fstar_slice {α : ℝ} (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ := by
  have hbase : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hGam : DifferentiableAt ℝ (fun θ' : ℝ => (Real.sin θ' * Real.cos θ' ^ 2) ^ α) θ := by
    have h1 : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2) θ := by fun_prop
    exact h1.rpow_const (Or.inl (ne_of_gt hbase))
  have hconst : (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ')
      = fun θ' => (Work.FM.Fstar z * ((3 * α) / Work.Spaces.c (3 * α)))
          * (Real.sin θ' * Real.cos θ' ^ 2) ^ α := by
    funext θ'
    rw [Work.Construction.Fstar, Work.Spaces.Gam, show 3 * α / 3 = α from by ring]
    ring
  rw [hconst]
  exact hGam.const_mul _

/-- **The angular derivative of the positive branch**, bounded by the singular weight
`200α² sin^{α-1}θ cos^{2α-1}θ` plus the (uncontrolled) angular derivative of `g`. -/
lemma abs_pdz_posbranch_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hd : DifferentiableAt ℝ (fun θ' => Ppos α g τ z θ') θ) :
    |deriv (fun θ' => Ppos α g τ z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := by
  have hFd := differentiableAt_fstar_slice (z := z) hα hθ
  have hgd : DifferentiableAt ℝ (fun θ' => g z θ' τ) θ := by
    have hsub : DifferentiableAt ℝ
        ((fun θ' => Ppos α g τ z θ') - (fun θ' => Work.Construction.Fstar (3 * α) z θ')) θ :=
      hd.sub hFd
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards with θ'
    simp [Ppos]
  have hFsum : (fun θ' => Ppos α g τ z θ')
      = (fun θ' => Work.Construction.Fstar (3 * α) z θ') + (fun θ' => g z θ' τ) := rfl
  rw [hFsum, deriv_add hFd hgd]
  have h1 : |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ|
      ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    (Work.FTS.FireFix.Clauses.Fstar_bounds hα hα13).2.2 z θ hz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h2 : deriv (fun θ' => g z θ' τ) θ
      = Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ := rfl
  rw [h2]
  calc |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ
        + Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ|
      ≤ |deriv (fun θ' => Work.Construction.Fstar (3 * α) z θ') θ|
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := abs_add_le _ _
    _ ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ| := by linarith [h1]

end Work.FTS.FireFix.Clauses
