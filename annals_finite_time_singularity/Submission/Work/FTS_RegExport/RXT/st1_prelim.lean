/-
# `Work.FTS_RegExport.RXT.st1_prelim` — helpers for RX-St1 (leaf S9)

Preliminaries for `Work.FTS_RegExport.RXT.st1_of_weighted`: the exported family
`GG α g = extG (gS α (tauExt g))`, its agreement with the slice of `g` on `z > 0, θ ∈ Iθ, τ ≥ 0`,
the elementary facts about the angular factor `Γ α θ = (sinθ cos²θ)^α` and the weight
`ω α z θ = z²Γ(θ)/(1+z)²`, and the two auxiliary identities `D_zD_θ = z sin(2θ) ∂_z∂_θ`,
`deriv F 0 = 0` when `F` vanishes on `(-∞,0]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.RegPkgGal.R4d.van_global
import Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan
import Submission.Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta
import Submission.Work.FTS_RegExport.RXT.omega_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-! ## §1 The exported family and its elementary properties -/

/-- The sanitised, right-Taylor-extended family `gS α (tauExt g)`, extended to `z ≤ 0` by `0`. -/
abbrev GG (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))

/-- `GG` agrees with the slice of `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`. -/
theorem GG_of_mem (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    GG α g z θ τ = Work.FTS.Galerkin.slice g τ z θ := by
  rw [GG, Work.FTS.FinalV2.extG_gS_of_mem α (Work.FTS.FinalV2.tauExt g) hθ.1 hθ.2,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ]
  exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ

/-- `GG` vanishes for `z ≤ 0`. -/
theorem GG_of_nonpos (α : ℝ) {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hz : z ≤ 0) :
    GG α g z θ τ = 0 := by
  simp only [GG, Work.FTS.RegPkgGal.extG_of_nonpos hz]

/-- `deriv F 0 = 0` if `F` vanishes on `(-∞,0]`. -/
theorem deriv_eq_zero_of_eq_zero_of_nonpos {F : ℝ → ℝ} (h : ∀ x : ℝ, x ≤ 0 → F x = 0) :
    deriv F 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ F 0
  · have h1 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[≠] (0:ℝ)) (𝓝 (deriv F 0)) := by
      simpa only [zero_add, smul_eq_mul] using hd.hasDerivAt.tendsto_slope_zero
    have h2 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[<] (0:ℝ)) (𝓝 (deriv F 0)) :=
      h1.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
    have h3 : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[<] (0:ℝ)]
        (fun t : ℝ => t⁻¹ * (F t - F 0)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [h t ht.le, h 0 le_rfl, sub_zero, mul_zero]
    have h5 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[<] (0:ℝ)) (𝓝 (0:ℝ)) :=
      Tendsto.congr' h3 tendsto_const_nhds
    exact tendsto_nhds_unique h2 h5
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## §2 The angular factor `Γ`, the weight `ω` -/

/-- `Γ(0) = 0` for `α > 0`. -/
theorem Gamma_zero_left {α : ℝ} (hα : 0 < α) : Work.FTS.Regularity.Gamma α 0 = 0 := by
  have h : Real.sin (0:ℝ) * Real.cos (0:ℝ) ^ 2 = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, h,
    Real.zero_rpow (ne_of_gt hα)]

/-- `Γ(π/2) = 0` for `α > 0`. -/
theorem Gamma_zero_right {α : ℝ} (hα : 0 < α) : Work.FTS.Regularity.Gamma α (π / 2) = 0 := by
  have h : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, h,
    Real.zero_rpow (ne_of_gt hα)]

/-- `ω ≥ 0` on the closed quadrant. -/
theorem omega_nonneg_of (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.RegExportIface.ω α z θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  rw [Work.FTS.RegExportIface.ω]
  exact div_nonneg (mul_nonneg (sq_nonneg z) hG) (by positivity)

/-- `ω ≤ z²Γ`. -/
theorem omega_le_zsq_mul_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ ≤ z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h1 : (1:ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  rw [Work.FTS.RegExportIface.ω, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  simpa using mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg z) hG)

/-- `ω ≤ Γ` (the `z²/(1+z)²` factor is `≤ 1`). -/
theorem omega_le_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ ≤ Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h1 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  rw [Work.FTS.RegExportIface.ω, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  calc z ^ 2 * Work.FTS.Regularity.Gamma α θ
      = Work.FTS.Regularity.Gamma α θ * z ^ 2 := by ring
    _ ≤ Work.FTS.Regularity.Gamma α θ * (1 + z) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hG

/-- `z/(1+z)² ≤ 1` for `z ≥ 0`. -/
theorem z_div_one_add_sq_le_one {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg z]

/-- `ω α z θ / z ≤ Γ(θ)`, for `z ≥ 0` (the `z/(1+z)²` factor is `≤ 1`). -/
theorem omega_div_z_le_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ / z ≤ Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · simp [Work.FTS.RegExportIface.ω, hG]
  · have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hd0 : (1 + z) ^ 2 ≠ 0 := by positivity
    have e : Work.FTS.RegExportIface.ω α z θ / z
        = Work.FTS.Regularity.Gamma α θ * (z / (1 + z) ^ 2) := by
      rw [Work.FTS.RegExportIface.ω]
      field_simp
    rw [e]
    calc Work.FTS.Regularity.Gamma α θ * (z / (1 + z) ^ 2)
        ≤ Work.FTS.Regularity.Gamma α θ * 1 :=
          mul_le_mul_of_nonneg_left (z_div_one_add_sq_le_one hz) hG
      _ = Work.FTS.Regularity.Gamma α θ := mul_one _

/-- `ω α z θ / z ≤ z·Γ(θ)`, for `z ≥ 0` (the `1/(1+z)²` factor is `≤ 1`). -/
theorem omega_div_z_le_z_mul_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ / z ≤ z * Work.FTS.Regularity.Gamma α θ := by
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · simp [Work.FTS.RegExportIface.ω]
  · have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
    have h1 : (1:ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    have hd0 : (1 + z) ^ 2 ≠ 0 := by positivity
    have e : Work.FTS.RegExportIface.ω α z θ / z
        = Work.FTS.Regularity.Gamma α θ * z * ((1 + z) ^ 2)⁻¹ := by
      rw [Work.FTS.RegExportIface.ω]
      field_simp
    rw [e]
    calc Work.FTS.Regularity.Gamma α θ * z * ((1 + z) ^ 2)⁻¹
        ≤ Work.FTS.Regularity.Gamma α θ * z * 1 :=
          mul_le_mul_of_nonneg_left
            (by rw [inv_le_one₀ (by positivity)]; exact h1) (mul_nonneg hG hz)
      _ = z * Work.FTS.Regularity.Gamma α θ := by ring

/-! ## §3 Congruences between `GG` and the slice of `g` -/

/-- `∂_z` of the `GG`-slice equals `∂_z` of the `g`-slice, for `z > 0`, `θ ∈ Iθ`. -/
theorem pz_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
      = Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
  show deriv (fun z' => GG α g z' θ τ) z
    = deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact GG_of_mem α hτ hz' hθ

/-- `∂_z²` of the `GG`-slice equals `∂_z²` of the `g`-slice, for `z > 0`, `θ ∈ Iθ`. -/
theorem pz_pz_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ := by
  show deriv (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' θ) z
    = deriv (fun z' => Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z' θ) z
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact pz_GG_eq α hτ hz' hθ

/-- `D_θ` of the `GG`-slice equals `D_θ` of the `g`-slice, at interior angles. -/
theorem Dth_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
      = Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' => GG α g z θ' τ) θ
    = Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ'
  exact GG_of_mem α hτ hz ⟨hθ'.1.le, hθ'.2.le⟩

section Vanish

variable {g : Work.FTS.Galerkin.Fam}

/-- `GG α g z 0 τ = 0` on the left angular boundary. -/
theorem GG_eq_zero_left (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    GG α g z 0 τ = 0 := by
  rw [GG_of_mem α hτ hz ⟨le_rfl, by linarith [Real.pi_pos]⟩]
  exact (hv τ hτ z hz.le).1

/-- `GG α g z (π/2) τ = 0` on the right angular boundary. -/
theorem GG_eq_zero_right (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    GG α g z (π / 2) τ = 0 := by
  rw [GG_of_mem α hτ hz ⟨by linarith [Real.pi_pos], le_rfl⟩]
  exact (hv τ hτ z hz.le).2

/-- `∂_z` of the `GG`-slice vanishes at `θ = 0` (for `z > 0`). -/
theorem pz_GG_eq_zero_left (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z 0 = 0 := by
  show deriv (fun z' => GG α g z' 0 τ) z = 0
  have hev : (fun z' : ℝ => GG α g z' 0 τ) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact GG_eq_zero_left α hτ hz' hv
  rw [hev.deriv_eq, deriv_const]

/-- `∂_z` of the `GG`-slice vanishes at `θ = π/2` (for `z > 0`). -/
theorem pz_GG_eq_zero_right (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z (π / 2) = 0 := by
  show deriv (fun z' => GG α g z' (π / 2) τ) z = 0
  have hev : (fun z' : ℝ => GG α g z' (π / 2) τ) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact GG_eq_zero_right α hτ hz' hv
  rw [hev.deriv_eq, deriv_const]

end Vanish

/-- `D_zD_θ = z·sin(2θ)·∂_z∂_θ`. -/
theorem mixed_one_one_eq (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 1 Φ z θ
      = z * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth Φ) z θ) := by
  show z * Work.Spaces.pz (Work.Spaces.Dth Φ) z θ = _
  congr 1
  show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth Φ z' θ) z = _
  rw [deriv_const_mul_field]
  rfl

/-! ## §4 `K ≥ 0` -/

/-- The weighted bound forces `0 ≤ K` (it is read at the interior point `(1, π/4)`, `τ = 0`). -/
theorem st1_K_nonneg {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    0 ≤ K := by
  have hωpos : 0 < Work.FTS.RegExportIface.ω α 1 (π / 4) := by
    have hΓ : 0 < Work.FTS.Regularity.Gamma α (π / 4) :=
      Gamma_pos α (π / 4) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [Work.FTS.RegExportIface.ω]
    positivity
  have hpt : |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g 0) 1 (π / 4)|
      ≤ K * Work.FTS.RegExportIface.ω α 1 (π / 4) := by
    have h := hw (0 : Fin 6) 0 ⟨le_rfl, hS.le⟩ 1 (π / 4) one_pos
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    norm_num [Work.FTS.RegExportIface.RXT.idx] at h
    exact h
  exact nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) hpt) hωpos

end Work.FTS_RegExport.RXT
