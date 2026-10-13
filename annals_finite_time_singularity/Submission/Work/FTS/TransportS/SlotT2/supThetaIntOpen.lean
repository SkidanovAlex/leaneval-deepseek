import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.SlotT2

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the weights and the intervals -/

theorem supOpen_w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem supOpen_one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

theorem supOpen_w_sq_ne_zero {z : ℝ} (hz : 0 < z) : (Work.Spaces.w z) ^ 2 ≠ 0 := by
  have h : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      (pow_ne_zero 2 (ne_of_gt hz))
  exact pow_ne_zero 2 h

/-- `Iθ = [0,π/2]` differs from the open interval by the null set `{0, π/2}`. -/
theorem supOpen_Iθ_ae_eq :
    (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)).symm

theorem supOpen_restrict_Iθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
    = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  MeasureTheory.Measure.restrict_congr_set supOpen_Iθ_ae_eq

/-- `Iz = [0,∞)` differs from the open half-line by the null set `{0}`. -/
theorem supOpen_Iz_ae_eq : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

theorem supOpen_restrict_Iz : MeasureTheory.volume.restrict Work.Spaces.Iz
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.Measure.restrict_congr_set supOpen_Iz_ae_eq

/-! ## The open-quadrant commutation, and the weight identity of the `θ`-slot -/

/-- On the open quadrant, `D_z^bD_θf = sin(2θ)·∂_θ(D_z^b f)`: the `D_θ`-iterate of a
`D_z`-iterate commutes across, for `C^∞` data on the open quadrant. -/
theorem supOpen_mixed_eq_sin_pth {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Work.Spaces.mixed b 1 f z θ
      = Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ :=
    ((Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF) b 1) hy).symm
  rw [h1]
  rfl

/-- The weight identity behind the angular Hardy inequality, on the open quadrant:
`(∂_θD_z^b f)² w² sin(2θ)^{2-γ} = (D_z^bD_θf · W)²`. -/
theorem supOpen_pth_weight {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
  Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) (Work.Spaces.mixed b 1 f z θ)
    (supOpen_mixed_eq_sin_pth hF b hz hθ)

/-! ## Integrability of the angular slices -/

/-- The pointwise domination of `(D_z^b f)²` by the `ℋ⁴`-integrand on the open quadrant,
using that the light weight `w/σ^{η/2}` exceeds `1` there. -/
theorem supOpen_sq_le_Hk {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ} (hb4 : b ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw1 : 1 ≤ Work.Spaces.w z := supOpen_one_le_w hz
  have hL : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    linarith
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]
        exact le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4

/-- For `z > 0` the angular slice `θ ↦ (D_z^bf z θ)²` is integrable on `Iθ`, by domination
by the `ℋ⁴`-integrand. -/
theorem supOpen_integrableOn_sq {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hkey : MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
      ((((hF.DzIter b).curry_θ hz).continuousOn.aestronglyMeasurable
        measurableSet_Ioo).pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact supOpen_sq_le_Hk hb4 hz hθ
  show MeasureTheory.Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [supOpen_restrict_Iθ]
  exact hkey

/-- For `z > 0` the weighted angular slice `(∂_θD_z^bf z ·)² σ^{2-γ}` is integrable on
`Iθ`: after multiplying by `(w z)²` it is the mixed slot `(mixed b 1 f · W)²`, which is
dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_integrableOn_pth_weight {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := supOpen_w_sq_ne_zero hz
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hderiv_cont : ContinuousOn
      (fun θ => deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hF.DzIter b).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen
      isOpen_Ioo le_rfl
  have hsincont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hkey : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine MeasureTheory.Integrable.mono'
      (((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self).const_mul
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (hderiv_cont.pow 2).mul hsincont
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
      calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = ((Work.Spaces.w z) ^ 2)⁻¹
              * (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            rw [← supOpen_pth_weight hF hα hα1 b hz hθ]
            rw [show ((Work.Spaces.w z) ^ 2)⁻¹
                  * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                      * (Work.Spaces.w z) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2)
                    * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) from by ring]
            rw [inv_mul_cancel₀ hw2, one_mul]
        _ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 4 f z θ :=
            mul_le_mul_of_nonneg_left
              (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega))
              (inv_nonneg.mpr (sq_nonneg _))
  show MeasureTheory.Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [supOpen_restrict_Iθ]
  exact hkey

/-! ## The slicewise bound and the a.e. sup bound -/

/-- The two-term majorant of the angular slice estimate at the fixed radius `z`. -/
def supOpenBfun (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
    + (200 / (Work.Spaces.gam α - 1))
        * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The open-interval Agmon inequality `Work.H2.T1Q.SliceSupOpen` at the slice
`θ ↦ D_z^b f z θ`. -/
theorem supOpen_slice_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter b f z θ) ^ 2 ≤ supOpenBfun α f b z := by
  have hb4 : b ≤ 4 := by omega
  have hslice : ContDiffOn ℝ 1 (fun θ => Work.Spaces.DzIter b f z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter b).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 := supOpen_integrableOn_sq hF hmem hb4 hz
  have hintp := supOpen_integrableOn_pth_weight hF hmem hα hα1 hb3 hz
  intro θ hθ
  exact Work.H2.T1Q.SliceSupOpen α (fun θ' => Work.Spaces.DzIter b f z θ') hα hα1 hslice
    hint2 hintp θ hθ

/-- The angular slice of `D_z^bf` is bounded above, the input of the countability argument
for the measurability of the interior supremum. -/
theorem supOpen_slice_bddAbove {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), y = |Work.Spaces.DzIter b f z θ|} :=
  ⟨Real.sqrt (supOpenBfun α f b z), fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := hy
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (supOpen_slice_bound hF hmem hα hα1 hb3 hz θ hθ)⟩

/-- The `D_z`-slot: multiplying the angular slice integral of `(D_z^bf)²` by `w(z)²` costs
only the light weight, hence is dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_block_z {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hmem : Work.Spaces.HkMem α 4 f) (hb4 : b ≤ 4) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hwz_nn : 0 ≤ Work.Spaces.w z := supOpen_w_nonneg z
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  rw [e1]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hmem.1 z hzIz) ?_
  rw [supOpen_restrict_Iθ]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hsinθ : 0 < Real.sin (2 * θ) := hsinpos θ hθ
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinθ) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [hwz_nn, hsle]
  have hstep : (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_mul, abs_of_nonneg hwz_nn,
      abs_of_nonneg (div_nonneg hwz_nn (le_of_lt hspos))]
    exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  exact hstep.trans (Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4)

/-- The mixed block: `∫_θ (∂_θD_z^bf)² σ^{2-γ} · w(z)²` is exactly the angular integral of
the `(D_z^bD_θf · W)²` slot, dominated by the `ℋ⁴`-integrand. -/
theorem supOpen_block_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_comm, ← MeasureTheory.integral_const_mul]
    have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
      MeasureTheory.setIntegral_congr_set supOpen_Iθ_ae_eq
    have h2 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      MeasureTheory.setIntegral_congr_set supOpen_Iθ_ae_eq
    rw [h1, h2]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [← supOpen_pth_weight hF hα hα1 b hz hθ]
    ring
  rw [e2]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
    (hmem.1 z hzIz) (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl (by omega)))

/-- **The a.e. pointwise bound.**  For almost every `z ∈ (0,∞)` the squared weighted angular
supremum of `D_z^bf` is dominated by `(4/π + 200/(γ-1))·∫_θ HkIntegrand α 4 f z θ`. -/
theorem supOpen_ae_sup_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb3 : b ≤ 3) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hb4 : b ≤ 4 := by omega
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hzpos
  have hwz_nn : 0 ≤ Work.Spaces.w z := supOpen_w_nonneg z
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hsinθ_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.Spaces.bt_sin_nonneg hθ
  have hBnn : 0 ≤ supOpenBfun α f b z := by
    rw [supOpenBfun]
    refine add_nonneg (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _))) ?_
    refine mul_nonneg (div_nonneg (by norm_num) (le_of_lt hγpos))
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinθ_nn θ hθ) _)))
  have hsup_nn : 0 ≤ Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z :=
    le_trans (abs_nonneg _)
      (le_csSup (supOpen_slice_bddAbove hF hmem hα hα1 hb3 hzpos)
        ⟨π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩)
  have hsup_le : Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z
      ≤ Real.sqrt (supOpenBfun α f b z) :=
    Work.FTS.H2.supAbsThO_le (fun θ hθ => by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (supOpen_slice_bound hF hmem hα hα1 hb3 hzpos θ hθ))
  have hstep1 : (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := by
    have h1 : Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z
        ≤ Real.sqrt (supOpenBfun α f b z) * Work.Spaces.w z :=
      mul_le_mul_of_nonneg_right hsup_le hwz_nn
    have h0 : 0 ≤ Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z :=
      mul_nonneg hsup_nn hwz_nn
    calc (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (Real.sqrt (supOpenBfun α f b z) * Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hBnn]
  calc (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ supOpenBfun α f b z * (Work.Spaces.w z) ^ 2 := hstep1
    _ = (4 / Real.pi) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2)
          + (200 / (Work.Spaces.gam α - 1)) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2) := by
        rw [supOpenBfun]; ring
    _ ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (supOpen_block_z hmem hb4 hzpos) (by positivity))
          (mul_le_mul_of_nonneg_left
            (supOpen_block_mixed hF hmem hα hα1 hb3 hzpos) (by positivity))
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by ring

/-- A version of `Work.H2.T1Q.SupAbsThOAesm` whose continuity hypothesis is only required
almost everywhere in `z` (the argument is pointwise a.e. in any case). -/
theorem supOpen_supAbsThO_aemeasurable {u : ℝ → ℝ → ℝ}
    (hcont : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hmeas : ∀ q : ℚ, ((q : ℝ) ∈ Set.Ioo 0 (Real.pi / 2)) →
      AEMeasurable (fun z => u z (q : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (Real.pi / 2), y = |u z θ|}) :
    AEMeasurable (fun z => Work.FTS.H2.supAbsThO u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine (Work.H2.T1Q.supRatAbs_aemeasurable hmeas).congr ?_
  filter_upwards [hcont, hbdd] with z hz hbddz
  exact (Work.H2.T1Q.supAbsThO_eq_supRatAbs hz hbddz).symm

/-- **Angular sup bound of Elgindi's Lemma `infinity_separated`, integrated in the radial
variable, in the open class.**  For `f` of class `C^∞` on the *open* quadrant with
`HkMem α 4 f` and `b ≤ 3`,

  `∫_z (sup_{θ ∈ (0,π/2)} |D_z^b f(z,θ)| · w(z))² dz ≤ C/(γ-1) · HkSq α 4 f`,

with `C` a universal constant.  The sup is taken over the **open** angular interval (for
`SmoothOpen` data the values at `θ = 0, π/2` are not controlled), and it is this function
which has to be proved integrable.

Route (adapt the *proved* closed-quadrant `Work.FTS.H2.SupThetaInt`, and the proved
`Work.H2.T1Q.SupThetaIntQ` which does exactly this for the *stronger* class `SmoothQuad` with
`supAbsThO`, defined in `Transport1Aux`/`H2.Defs`):
* at each fixed `z`, the angular Agmon inequality with a mean-value base point — for the
  open class this is `Work.FTS.H2.slice_sup_sq_le` **generalised to `ContDiffOn ℝ 1 u
  (Ioo 0 (π/2))` with the base point chosen in `(0,π/2)`** (`exists_le_setAverage` over the
  open interval) — gives
  `sup_θ|D_z^b f(z,θ)|² ≤ (4/π)∫_{Ioo}(D_z^b f(z,·))² + (200/(γ-1))∫_θ(∂_θD_z^b f)²σ^{2-γ}`;
* uniformly in `z`, the two right-hand integrals are bounded by `C·HkSq α 4 f`
  (`D_z^b f = z^b ∂_z^b f + …` is a finite combination, and the summand
  `(D_z^j f · w/σ^{η/2})²` resp. `(mixed b 1 f · Wt)²` is a summand of `HkIntegrand α 4 f`
  for `j ≤ 4` resp. `b + 1 ≤ 4`: use `Work.Spaces.sq_le_HkIntegrand_z`,
  `Work.Spaces.sq_le_HkIntegrand_mixed`, `Work.Spaces.DzIter_eq_sum_scoef`-type expansions,
  and the angular slice integrability `Work.FTS.EllipticEst.integrableOn_zSummand`,
  `...SliceDecompDefs.integrableOn_mixedSummand`);
* measurability of `z ↦ supAbsThO (DzIter b f) z` (the sup over the open interval) and a.e.
  strong measurability of the slice integrals, exactly as in `SupThetaIntQ.lean`
  (`SupAbsThOAesm.lean`); then integrate the a.e. inequality in `z`.
The factor `1/(γ-1)` is essential and cannot be replaced by a universal constant (see
`SlotT2/NOTES_sliceSupEtaGam_FALSE.md`). -/
theorem supThetaIntOpen : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ),
    0 < α → α ≤ 1 → b ≤ 3 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    MeasureTheory.IntegrableOn
        (fun z => (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
            y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
  refine ⟨1000, by norm_num, ?_⟩
  intro α f b hα hα1 hb3 hF hmem
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- the a.e. pointwise bound, transported to `volume.restrict Iz`
  have hstep : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
    rw [supOpen_restrict_Iz]
    exact supOpen_ae_sup_bound hF hmem hα hα1 hb3
  -- a.e. strong measurability of the interior angular supremum
  have hmeas_sup : AEMeasurable (fun z => Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine supOpen_supAbsThO_aemeasurable ?_ ?_ ?_
    · rw [supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
      exact ((hF.DzIter b).curry_θ hzpos).continuousOn
    · intro q hq
      rw [supOpen_restrict_Iz]
      exact (((hF.DzIter b).curry_z hq).continuousOn).aemeasurable measurableSet_Ioi
    · rw [supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzpos
      exact supOpen_slice_bddAbove hF hmem hα hα1 hb3 hzpos
  have hw_meas : AEMeasurable (fun z : ℝ => Work.Spaces.w z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [supOpen_restrict_Iz]
    change AEMeasurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).aemeasurable
        measurableSet_Ioi
  have hf_aesm : AEStronglyMeasurable
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hmeas_sup.mul hw_meas).pow_const 2).aestronglyMeasurable
  -- domination and integrability
  have hdom_nn : ∀ z, 0 ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := fun z =>
    mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg hIθ_meas
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
  have hdom_int : MeasureTheory.Integrable (fun z =>
      (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2.const_mul _
  have hf_int : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hdom_int hf_aesm ?_
    filter_upwards [hstep] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  have hmain : ∫ z in Work.Spaces.Iz,
        (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
    calc ∫ z in Work.Spaces.Iz,
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ ∫ z in Work.Spaces.Iz, (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hdom_int hstep
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := rfl
  have hcoef : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      ≤ 1000 / (Work.Spaces.gam α - 1) := by
    have heq : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        = (4 / Real.pi * (Work.Spaces.gam α - 1) + 200) / (Work.Spaces.gam α - 1) := by
      field_simp
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hγpos)
    have h1 : (4 / Real.pi) * (Work.Spaces.gam α - 1) ≤ (4 / Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left (by rw [Work.Spaces.gam]; linarith) (by positivity)
    have h2 : (4 : ℝ) / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    linarith
  have hfun : (fun z : ℝ => (sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        y = |Work.Spaces.DzIter b f z θ|}) ^ 2 * (Work.Spaces.w z) ^ 2)
      = fun z : ℝ =>
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2 := by
    funext z
    rw [mul_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hf_int
  · rw [hfun]
    calc ∫ z in Work.Spaces.Iz,
          (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := hmain
      _ ≤ 1000 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f :=
          mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end

end Work.FTS.TransportS.SlotT2
