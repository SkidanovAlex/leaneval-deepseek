import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/Slots` — the slot functionals of the `N`-zero-mode estimate

The `L₁₂`-density functional `FaU` (without the angular weight `K`), its bound by the `ℋ⁴`-norm
of the datum for the three datum slots (`PsgAux.rl1_slot_le` applied with the coefficient
`(K θ)⁻¹`, whose `K θ`-weight is `1`), the six slots `slots α f`, the coefficient majorant
`Kcoef`, and the six-slot `Fa`-estimate `Fa_le_slots`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The *slot* functional of the zero-mode estimate: `FaU g = ∫⁻_r r⁻¹ ∫⁻_θ |g(r,θ)|`
(the `r⁻¹`-density of `L₁₂`, without the angular weight `K`). -/
def FaU (g : Fn) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)

/-- **A slot bounded by the `ℋ⁴`-integrand.**  If `w(r)·B(r,θ)² ≤ HkIntegrand α 4 f r θ` a.e. in
`θ` (the shape of `PsgAux.slot_g`/`slot_dth`/`slot_dz`), then the slot functional of `B` is at
most `√(π/2)·|f|_{ℋ⁴}`.

Proof: apply `PsgAux.rl1_slot_le` with the coefficient `A = (K θ)⁻¹`, whose `K θ`-weight is `1`
a.e. on `Iθ`; the conclusion is the slot functional. -/
theorem FaU_slot_le {α : ℝ} {B f : Fn} (hα : 0 < α)
    (hB : ContinuousOn (Function.uncurry B) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α 4 f)
    (hBw : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ) :
    FaU B ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  have hA : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ| ≤ 1 := by
    intro r hr
    refine Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hKpos : 0 < Work.Spaces.K θ := by
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simp only [Work.Spaces.K]
      positivity
    show |Work.Spaces.K θ * (Work.Spaces.K θ)⁻¹| ≤ 1
    rw [mul_inv_cancel₀ (ne_of_gt hKpos), abs_one]
  have hBmeas : ∀ r : ℝ, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hB hr
  have hΦmeas : AEMeasurable
      (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hB
  have hE := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
    (A := fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) (B := B) (g := f) (C := 1)
    (by norm_num) hmem hA hBmeas hΦmeas hBw
  have hcongr : (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ
          * B r θ|)
      = fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ| := by
    funext r
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => hθ)] with θ hθ
    have hKpos : 0 < Work.Spaces.K θ := by
      have h1 : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simp only [Work.Spaces.K]
      positivity
    have : Work.Spaces.K θ * (Work.Spaces.K θ)⁻¹ * B r θ = B r θ := by
      rw [mul_inv_cancel₀ (ne_of_gt hKpos), one_mul]
    rw [this]
  have hkey : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|))
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            |Work.Spaces.K θ * (fun _ θ' : ℝ => (Work.Spaces.K θ')⁻¹) r θ * B r θ|)) := by
    refine MeasureTheory.lintegral_congr (fun r => ?_)
    rw [congrFun hcongr r]
  show FaU B ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f)
  rw [show FaU B = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)) from rfl, hkey]
  exact hE.trans (le_of_eq (by rw [one_mul]))


/-! ## Small analytic helpers -/

/-- `(√(gam α - 1))⁻¹ = √10·α^{-1/2}` for `α > 0` (the conversion of the Agmon constant
`C/√(γ-1)` into the `α^{-1/2}` used throughout). -/
theorem inv_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have hsq : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) :=
    (congrArg (fun x : ℝ => x⁻¹) (Real.sqrt_eq_rpow α)).trans
      (Real.rpow_neg hα.le (1 / 2 : ℝ)).symm
  rw [Work.Spaces.gam_sub_one, Real.sqrt_div hα.le 10, inv_div, div_eq_mul_inv, hsq]

/-- `1 ≤ α^{-1/2}` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hα.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hα _)).mpr
    (Real.rpow_le_one hα.le hα1 (by norm_num))

/-- The angular slice of a function continuous on the open quadrant is a.e. strongly
measurable (in the form `θ ↦ ofReal |g r θ|` needed by the `θ`-Cauchy–Schwarz). -/
theorem aesm_slot_abs {g : Fn}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {r : ℝ}
    (hr : 0 < r) :
    AEMeasurable (fun θ => ENNReal.ofReal |g r θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hg hr
  have h2 : AEMeasurable (fun θ => g r θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg' : Measurable (fun x : ℝ => ENNReal.ofReal |x|) := by fun_prop
  simpa only [Function.comp_def] using hg'.comp_aemeasurable h2

/-- The parametrised `θ`-integral `r ↦ ∫⁻_θ ofReal |g r θ|` is a.e. measurable. -/
theorem meas_slot_int {g : Fn}
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry g) hg
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hmeas_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hz
  rw [hmeas_eq] at h1
  have h2 : AEMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg' : Measurable (fun x : ℝ => ENNReal.ofReal |x|) := by fun_prop
  have h3 : AEMeasurable (Function.uncurry (fun r θ => ENNReal.ofReal |g r θ|))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hg'.comp_aemeasurable h2
  exact h3.lintegral_prod_right

/-- **The three datum slots.**  For `0 < α` and an `ℋ⁴`-datum `f`, each of the three slots
`f`, `D_θ f`, `D_z f` has slot functional at most `√(π/2)·|f|_{ℋ⁴}`. -/
theorem FaU_data_slots {α : ℝ} {f : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    FaU f ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) ∧
    FaU (Work.Spaces.Dth f)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) ∧
    FaU (Work.Spaces.Dz f)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  refine ⟨?_, ?_, ?_⟩
  · refine FaU_slot_le hα hso.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ f)
  · refine FaU_slot_le hα hso.Dth.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ f)
  · refine FaU_slot_le hα hso.Dz.continuousOn hmem (fun r hr => ?_)
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dz hα hr hθ f)

/-- The six slots of the zero-mode estimate: the three datum slots and the three profile
slots. -/
def slots (α : ℝ) (f : Fn) : Fin 6 → Fn :=
  ![f, Work.Spaces.Dth f, Work.Spaces.Dz f,
    Work.Construction.Fstar α, Work.Spaces.Dth (Work.Construction.Fstar α),
    Work.Spaces.Dz (Work.Construction.Fstar α)]

/-- The coefficient majorant of the zero-mode estimate. -/
def Kcoef (α M Ce Cs Cp Cu Cag : ℝ) : ℝ :=
  1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)

theorem Kcoef_pos {α M Ce Cs Cp Cu Cag : ℝ} (hα : 0 < α) (hCp : 0 < Cp) (hCu : 0 < Cu)
    (hCag : 0 < Cag) (hM : 0 ≤ M) : 0 < Kcoef α M Ce Cs Cp Cu Cag := by
  rw [Kcoef]
  have h1 : 0 < Cp + Cu + Cag + 1 := by linarith
  have h2 : 0 < (1 : ℝ) + |Ce| + |Cs| := by positivity
  have h3 : 0 < α ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hα _
  have h4 : 0 < (1 : ℝ) + M := by linarith
  positivity

theorem mul_le_Kcoef {α M Ce Cs Cp Cu Cag c : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (hc0 : 0 ≤ c) (hc : c ≤ 1000 * (Cp + Cu + Cag + 1)) :
    c * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) ≤ Kcoef α M Ce Cs Cp Cu Cag := by
  have h1 : (0 : ℝ) ≤ 1 + |Ce| + |Cs| := by positivity
  have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ 1 + M := by linarith
  calc c * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)
      ≤ (1000 * (Cp + Cu + Cag + 1)) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ))
          * (1 + M) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc h1) h2) h3
    _ = Kcoef α M Ce Cs Cp Cu Cag := by rw [Kcoef]

/-- **The zero-mode `Fa`-estimate.**  If `|K θ·N|` is pointwise dominated by `Kc` times the sum
of the six slots `G`, then the `L₁₂`-density of `N` is at most `Kc` times the sum of the six
slot functionals. -/
theorem Fa_le_slots {Kc : ℝ} {N : Fn} {G : Fin 6 → Fn} (hK0 : 0 ≤ Kc)
    (hpt : ∀ r θ : ℝ, 0 < r → 0 < θ → θ < π / 2 →
      |Work.Spaces.K θ * N r θ| ≤ Kc * ∑ j : Fin 6, |G j r θ|)
    (hm : ∀ j : Fin 6, ContinuousOn (Function.uncurry (G j))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Fa N ≤ ENNReal.ofReal Kc * ∑ j : Fin 6, FaU (G j) := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal Kc
          * (∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Kc * ∑ j : Fin 6, |G j r θ|) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
        (fun θ hθ => hθ)] with θ hθ
      exact ENNReal.ofReal_le_ofReal (hpt r θ hr hθ.1 hθ.2)
    refine h1.trans ?_
    rw [show (fun θ => ENNReal.ofReal (Kc * ∑ j : Fin 6, |G j r θ|))
        = fun θ => ENNReal.ofReal Kc * ∑ j : Fin 6, ENNReal.ofReal |G j r θ| from by
      funext θ
      rw [ENNReal.ofReal_mul hK0,
        ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [MeasureTheory.lintegral_finsetSum' _ (fun j _ => aesm_slot_abs (hm j) hr)]
  have h2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (ENNReal.ofReal Kc
          * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_of_nonneg_left (hinner r hr) bot_le
  refine h2.trans ?_
  rw [show (fun r => ENNReal.ofReal r⁻¹ * (ENNReal.ofReal Kc
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|))
      = fun r => ENNReal.ofReal Kc * (ENNReal.ofReal r⁻¹
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|) from by
    funext r
    rw [← mul_assoc, mul_comm (ENNReal.ofReal r⁻¹) (ENNReal.ofReal Kc), mul_assoc]]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [show (fun r => ENNReal.ofReal r⁻¹
        * ∑ j : Fin 6, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|)
      = fun r => ∑ j : Fin 6, ENNReal.ofReal r⁻¹
        * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ| from
    funext fun r => Finset.mul_sum _ _ _]
  rw [MeasureTheory.lintegral_finsetSum' (Finset.univ : Finset (Fin 6))
    (f := fun j r => ENNReal.ofReal r⁻¹ * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |G j r θ|)
    (fun j _ => (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable.mul
      (meas_slot_int (hm j)))]
  simp only [FaU]
  rfl

theorem alpha_le_rpow {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ≤ α ^ (-(1 / 2 : ℝ)) := le_trans hα1 (one_le_rpow_neg_half hα0 hα1)

theorem le_scaled {α M Ce Cs c : ℝ} (hα0 : 0 < α) (hM0 : 0 ≤ M)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 + |Ce| + |Cs|) :
    c * α ^ (-(1 / 2 : ℝ)) * (1 + M) ≤ (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hα0.le _))
    (by linarith)

theorem le_scaled' {α M Ce Cs X c : ℝ} (hα0 : 0 < α) (hM0 : 0 ≤ M) (hc0 : 0 ≤ c)
    (hX0 : 0 ≤ X) (hc : c ≤ 1 + |Ce| + |Cs|) (hX : X ≤ 1 + M) :
    c * α ^ (-(1 / 2 : ℝ)) * X ≤ (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
  refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hα0.le _)) hX0) ?_
  exact mul_le_mul_of_nonneg_left hX (by positivity)

