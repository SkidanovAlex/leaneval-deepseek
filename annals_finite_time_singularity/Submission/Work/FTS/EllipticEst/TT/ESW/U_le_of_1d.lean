import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.TT.ESW.slice_tendsto_pi_half
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TopSlotRhsDom
import Submission.Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Mine.SlicePoincare
import Submission.Work.FTS.EllipticEst.SrcBnd.SlotAESM
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `U_le_of_1d`: the two-dimensional assembly of the one-dimensional top-slot estimate

Target: `Work.FTS.EllipticEst.TT.ESW.U_le_of_1d`.  Given the one-dimensional estimate `OneD k`
(the paper's §"General `ℋ^k` case" reduced to a single angular slice), the two-dimensional
statement follows by applying `OneD k` to the slices `u = Ψ z ·` (with source
`g = Gsl α F Ψ z · = Lzero1 (Ψ z ·)`, `z > 0`) for almost every `z`, and integrating in `z`.

## The three ingredients

* `Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability` (proved) supplies, for a.e. `z ∈ Iz`,
  the continuity of the slice on the closed angular interval together with the angular
  integrability of the six slots occurring in the hypotheses of `OneD k`.
* the pointwise inequality for a.e. `z` is the conclusion of `OneD k` at `γ = gam α ∈ [1, 5/4]`,
  applied to the slices of `Ψ` with source `Gsl α F Ψ z ·`.
* the passage to the `z`-integral: every right-hand slot function is `z`-integrable — the plain
  angular slots are dominated, slot by slot, by the `ℋ^k`-integrand of the corresponding datum
  (`Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand` for the slots of `F`,
  `z²∂_z²Ψ` and `∂_θ²Ψ`, `Work.FTS.EllipticEst.Cores.Pieces.srcB_pointwise` for the slot of
  `D_zΨ`, and `Work.FTS.EllipticEst.Mine.SlicePoincare` for the two low-order slots).
  `MeasureTheory.integral_mono_of_nonneg` then gives the bound and the sum splits by
  `MeasureTheory.integral_add` and `Finset.integrable_sum`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_add_fts (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- `∂_θ^n f z θ` is the `n`-th iterated derivative of the slice `θ ↦ f z θ`. -/
theorem pthIter_eq_iterDeriv_point (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter n f z θ = iteratedDeriv n (fun t => f z t) θ := by
  rw [Work.FTS.EllipticEst.Mine.pthIter_eq_iteratedDeriv]

/-- A constant multiple commutes with the iterated `∂_θ`. -/
theorem pthIter_const_mul_fts (c : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter m (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter m f z θ := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth]
      exact deriv_const_mul_field c

/-- `Work.Stability.smoothOrder` is the genuine smooth order `∞`. -/
theorem smoothOrder_ne_zero_fts : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- On the open quadrant the iterated `∂_θ` is additive for `SmoothOpen` data. -/
theorem pthIter_add_on_Q0_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  have hsm : ∀ {h : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen h → ∀ k : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter k h) := by
    intro h hh k
    induction k with
    | zero => exact hh
    | succ k ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((hsm hf n).curry_θ hz).differentiableOn smoothOrder_ne_zero_fts
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((hsm hg n).curry_θ hz).differentiableOn smoothOrder_ne_zero_fts
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-- The bounds `1 ≤ γ` and `γ ≤ 5/4` for `γ = gam α`, `0 < α ≤ 1/4`. -/
theorem gam_bounds_fts {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    1 ≤ Work.Spaces.gam α ∧ Work.Spaces.gam α ≤ 5 / 4 := by
  constructor <;> simp only [Work.Spaces.gam] <;> linarith

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- On `Iθ` the weight `sin(2θ)^e` is nonnegative. -/
theorem sin_rpow_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (e : ℝ) :
    0 ≤ (Real.sin (2 * θ)) ^ e := Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _

/-- The angular weight `θ ↦ sin(2θ)^c` is continuous on the open quadrant. -/
theorem continuousOn_sin_rpow_Q0_fts (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hsin.rpow_const (fun p hp => Or.inl (ne_of_gt ?_))
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- On `(0, π/2)` the weight `sin(2θ)^e` is antitone in the exponent. -/
theorem sin_rpow_le_fts {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {a b : ℝ}
    (hab : a ≤ b) : (Real.sin (2 * θ)) ^ b ≤ (Real.sin (2 * θ)) ^ a := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsplit : (Real.sin (2 * θ)) ^ b
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a) := by
    rw [← Real.rpow_add hs, show a + (b - a) = b from by ring]
  have hle : (Real.sin (2 * θ)) ^ (b - a) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by linarith)
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ a := Real.rpow_nonneg hs.le a
  rw [hsplit]
  calc (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a)
      ≤ (Real.sin (2 * θ)) ^ a * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = (Real.sin (2 * θ)) ^ a := mul_one _

/-- The exponent arithmetic `2((j-2)) - γ = 2j - 4 - γ`. -/
theorem weight_sub_two (j : ℕ) (hj : 2 ≤ j) (γ θ : ℝ) :
    (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - γ)
      = (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - γ) := by
  have hcast : (((j - 2 : ℕ)) : ℝ) = (j : ℝ) - 2 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hcast]
  ring_nf

/-- Pulling the radial weight `(w z)²` inside the angular slot integral. -/
theorem wsq_mul_int_eq_fts (m : ℕ) (f : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (z : ℝ) :
    (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter m f z θ) ^ 2 * σ θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m f z θ) ^ 2 * σ θ) := by
  rw [← MeasureTheory.integral_const_mul]

/-- Nonnegativity of the slot integrand, a.e. on `Iθ`. -/
theorem ae_slot_nonneg_fts (m : ℕ) (f : ℝ → ℝ → ℝ) (α z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Spaces.pthIter m f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) :=
  Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))) _))

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_Iz_fts :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  have h1 : {x : ℝ | ¬ (x ∈ Set.Ici (0 : ℝ) → (0 : ℝ) < x)} = {0} := by
    ext x
    simp only [Set.mem_Ici, not_imp, not_lt, Set.mem_singleton_iff]
    constructor
    · intro h; linarith [h.1, h.2]
    · intro h; subst h; norm_num
  rw [h1]
  exact MeasureTheory.measure_singleton 0

/-- `θ ↦ ∂_θ^m g z θ` is measurable (no smoothness needed). -/
theorem measurable_pthIter_succ_fts (m : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ => Work.Spaces.pthIter (m + 1) g z θ) := by
  have h : (fun θ => Work.Spaces.pthIter (m + 1) g z θ)
      = deriv (fun θ' => Work.Spaces.pthIter m g z θ') := by
    funext θ; rw [Work.Spaces.pthIter_succ]; rfl
  rw [h]
  exact measurable_deriv _

/-- `θ ↦ sin(2θ)^c` is measurable. -/
theorem measurable_sin_rpow_fts (c : ℝ) : Measurable fun θ : ℝ => (Real.sin (2 * θ)) ^ c :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const c

/-- A slot whose weight exponent is increased is still integrable on the slice. -/
theorem slot_theta_mono_fts {m : ℕ} (hm : 1 ≤ m) {g : ℝ → ℝ → ℝ} {z : ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 * (Real.sin (2 * θ)) ^ a)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 * (Real.sin (2 * θ)) ^ b)
      Work.Spaces.Iθ := by
  have hmeas : Measurable (fun θ => Work.Spaces.pthIter m g z θ) := by
    have h := measurable_pthIter_succ_fts (m - 1) g z
    rwa [show m - 1 + 1 = m from by omega] at h
  refine MeasureTheory.Integrable.mono' h
    ((hmeas.pow_const 2).mul (measurable_sin_rpow_fts b)).aestronglyMeasurable ?_
  filter_upwards [Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ] with θ hθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))) _))]
  exact mul_le_mul_of_nonneg_left (sin_rpow_le_fts hθ hab) (sq_nonneg _)

theorem three_sq_le_fts (a A D α σ : ℝ) (hσ : 0 ≤ σ) :
    (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2 * σ
      ≤ 3 * (a ^ 2 * σ) + 3 * (α ^ 2) ^ 2 * (A ^ 2 * σ)
        + 3 * (α * (5 + α)) ^ 2 * (D ^ 2 * σ) := by
  have h1 : (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2
      ≤ 3 * (a ^ 2 + (α ^ 2 * A) ^ 2 + ((α * (5 + α)) * D) ^ 2) := by
    nlinarith [sq_nonneg (a - α ^ 2 * A), sq_nonneg (α ^ 2 * A - (α * (5 + α)) * D),
      sq_nonneg (a - (α * (5 + α)) * D)]
  calc (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2 * σ
      ≤ (3 * (a ^ 2 + (α ^ 2 * A) ^ 2 + ((α * (5 + α)) * D) ^ 2)) * σ :=
        mul_le_mul_of_nonneg_right h1 hσ
    _ = 3 * (a ^ 2 * σ) + 3 * (α ^ 2) ^ 2 * (A ^ 2 * σ)
        + 3 * (α * (5 + α)) ^ 2 * (D ^ 2 * σ) := by ring

/-- **A plain angular slot is `z`-integrable as soon as it is dominated by the `ℋ^K`-integrand.**
The differentiated function `g` and the function `g'` whose `ℋ^K`-integrand dominates are allowed
to differ (the case `g = D_zΨ`, `g' = ∂_θ²(D_zΨ)`).  The domination is assumed a.e. in `θ` for
every `z ∈ Iz`; the `θ`-integral of the majorant is `z`-integrable by `HkMem`, and the slot
function is a.e. strongly measurable by `Work.FTS.EllipticEst.SrcBnd.SlotAESM`. -/
theorem slot_zInt {α : ℝ} {K m : ℕ} {g g' : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α K g')
    (hbound : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkIntegrand α K g' z θ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) m hg
      (continuousOn_sin_rpow_Q0_fts (2 * (m : ℝ) - Work.Spaces.gam α))).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    exact (wsq_mul_int_eq_fts m g
      (fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) z).symm
  refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
  have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae (ae_slot_nonneg_fts m g α z))
  rw [Real.norm_of_nonneg hnn]
  have hinner : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter m g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α K g' z θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      ((ae_slot_nonneg_fts m g α z).mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
      ((hmem.1 z hz).const_mul C) ?_
    filter_upwards [hbound z hz] with θ hθ
    exact hθ
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter m g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) :=
        wsq_mul_int_eq_fts m g
          (fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) z
    _ ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α K g' z θ := hinner
    _ = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K g' z θ) :=
        MeasureTheory.integral_const_mul C _

/-- **The `u`-family slot**: for `j ∈ Icc 3 (k+1)` the `z`-integral of the plain angular slot of
`Ψ` at order `j` with weight `sin(2θ)^{2j-4-γ}` is honest. -/
theorem uSlot_zInt {α : ℝ} {k j : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hj : j ∈ Finset.Icc 3 (k + 1)) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand (j - 2) (by
      have := Finset.mem_Icc.mp hj; omega)
  have hbase := slot_zInt (α := α) (K := k) (m := j - 2) (g := Work.Spaces.pthIter 2 Ψ)
    (g' := Work.Spaces.pthIter 2 Ψ) (C := C0) hC0pos.le hBsm hwk.memB
    (fun z hz => hC0 α (Work.Spaces.pthIter 2 Ψ) k (by have := Finset.mem_Icc.mp hj; omega)
      hα (fun n => hBsm.forall n) z hz)
  have hfun : (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter (j - 2) (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - Work.Spaces.gam α)))
      = fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)) := by
    funext z
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    have hj2 : 2 ≤ j := by have := Finset.mem_Icc.mp hj; omega
    have hpt : Work.Spaces.pthIter (j - 2) (Work.Spaces.pthIter 2 Ψ) z θ ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - Work.Spaces.gam α)
        = Work.Spaces.pthIter j Ψ z θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α) := by
      rw [← pthIter_add_fts (j - 2) 2 Ψ, show j - 2 + 2 = j from by omega,
        weight_sub_two j hj2 (Work.Spaces.gam α) θ]
    exact hpt
  rwa [hfun] at hbase

/-- The `θ`-slot of `D_zΨ` at order `k` with the weight `sin(2θ)^{2k-γ}` is integrable on the
slice: it is the order-`(k-2)` slot of `∂_θ²(D_zΨ)` (a level-`(k-1)` datum), whose weight
`sin(2θ)^{2k-4-γ}` dominates `sin(2θ)^{2k-γ}`. -/
theorem dzSlot_theta_int {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hk1 : 1 ≤ k := by omega
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 1).2.1
  have hB2sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := hDzsm.pth.pth
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
  have hDzmem : Work.Spaces.HkMem α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
    have h0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hBsm hwk.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) h0 ?_
    intro z hz θ hθ
    exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨsm 1
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ⟩)).symm
  have hbase := Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k - 1)
    (g := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) (fun n => hB2sm.forall n) hDzmem
    hz (m := k - 2) (by omega) (by omega)
  have hrew : (fun θ =>
        (Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
      = fun θ => (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - 4 - Work.Spaces.gam α) := by
    funext θ
    have hpt := weight_sub_two k (by omega) (Work.Spaces.gam α) θ
    have hpt2 : Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ := by
      rw [← pthIter_add_fts (k - 2) 2 (Work.Spaces.DzIter 1 Ψ),
        show k - 2 + 2 = k from by omega]
    rw [hpt2, hpt]
  rw [hrew] at hbase
  refine slot_theta_mono_fts (m := k) hk1 (by linarith : (2 : ℝ) * (k : ℝ) - 4
    - Work.Spaces.gam α ≤ 2 * (k : ℝ) - Work.Spaces.gam α) ?_
  exact hbase

/-- The pointwise expansion of `∂_θ^k(Gsl α F Ψ)` on the open quadrant. -/
theorem pthIter_Gsl_decomp {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ)) (k : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ
        = Work.Spaces.pthIter k F z θ
          + α ^ 2 * Work.Spaces.pthIter k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.Dz Ψ) z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := pthIter_add_on_Q0_fts (f := F)
    (g := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    hFsm (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hAsm) k z θ hz hθ0 hθ1
  have h2 := pthIter_add_on_Q0_fts (f := fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (g := fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ)
    (Work.FTS.EllipticEst.smoothOpen_add hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hAsm))
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α)) hDzsm) k z θ hz hθ0 hθ1
  rw [pthIter_const_mul_fts] at h1
  rw [pthIter_const_mul_fts] at h2
  have hG : Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ
      = fun z θ => (F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ := by
    funext z θ
    simp only [Work.FTS.EllipticEst.TT.ESW.Gsl, Work.FTS.EllipticEst.TT.ESW.Asl,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [hG, h2, h1]

/-- **The source slot**: the `z`-integral of the plain angular slot of `Gsl α F Ψ` at order `k`
with weight `sin(2θ)^{2k-γ}` is honest. -/
theorem sourceSlot_zInt {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
        (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have hk1 : 1 ≤ k := by omega
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).1
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.1
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 1).2.1
  have hB2sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := hDzsm.pth.pth
  have hGsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc hwk
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand k hk1
  have hzF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hC0pos.le hFsm hwk.memF
      (fun z hz => hC0 α F k le_rfl hα (fun n => hFsm.forall n) z hz)
  have hzA : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hC0pos.le hAsm hwk.memA
      (fun z hz => hC0 α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k le_rfl hα
        (fun n => hAsm.forall n) z hz)
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.FTS.EllipticEst.Cores.Pieces.srcB_pointwise k hk
  have hDzmem : Work.Spaces.HkMem α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
    have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
    have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
      (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
    have h0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hBsm hwk.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) h0 ?_
    intro z hz θ hθ
    exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨsm 1
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ⟩)).symm
  have hzD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hCbpos.le hDzsm hDzmem
      (fun z hz => hCb α (Work.Spaces.DzIter 1 Ψ) hα (fun n => hB2sm.forall n) z hz)
  refine MeasureTheory.Integrable.mono'
    (((hzF.const_mul 3).add (hzA.const_mul (3 * (α ^ 2) ^ 2))).add
      (hzD.const_mul (3 * (α * (5 + α)) ^ 2))) ?_ ?_
  · -- a.e. strong measurability of the source slot
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) k hGsm
      (continuousOn_sin_rpow_Q0_fts (2 * (k : ℝ) - Work.Spaces.gam α))).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    exact (wsq_mul_int_eq_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
      (fun θ => (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) z).symm
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici), ae_pos_Iz_fts]
      with z hz hzpos
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae (ae_slot_nonneg_fts k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) α z))
    rw [Real.norm_of_nonneg hnn]
    -- the θ-slice comparison, `z > 0`
    have hFθ : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k) (g := F)
        (fun n => hFsm.forall n) hwk.memF hzpos (m := k) hk1 le_rfl
    have hAθ : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k)
        (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (fun n => hAsm.forall n) hwk.memA hzpos (m := k) hk1 le_rfl
    have hDθ : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      dzSlot_theta_int hk hα hwk hzpos
    have hdec : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          + 3 * (α ^ 2) ^ 2 * ((Work.Spaces.pthIter k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          + 3 * (α * (5 + α)) ^ 2 * ((Work.Spaces.pthIter k
              (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
      refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
      have h := pthIter_Gsl_decomp (α := α) hFsm hAsm hDzsm k z θ hzpos hθ.1 hθ.2
      have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
        Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _
      rw [h]
      exact three_sq_le_fts (Work.Spaces.pthIter k F z θ)
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) α
        ((Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) hs0
    -- the integrand functions of the three summands, and the majorant
    set W : ℝ := (Work.Spaces.w z) ^ 2 with hW
    have hWnn : 0 ≤ W := by rw [hW]; exact sq_nonneg _
    have hFθ' : MeasureTheory.IntegrableOn (fun θ => W * ((Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hFθ.const_mul W
    have hAθ' : MeasureTheory.IntegrableOn (fun θ => W *
        ((Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hAθ.const_mul W
    have hDθ' : MeasureTheory.IntegrableOn (fun θ => W *
        ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hDθ.const_mul W
    set XF : ℝ → ℝ := fun θ => 3 * (W * ((Work.Spaces.pthIter k F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXF
    set XA : ℝ → ℝ := fun θ => 3 * (α ^ 2) ^ 2 * (W *
      ((Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXA
    set XD : ℝ → ℝ := fun θ => 3 * (α * (5 + α)) ^ 2 * (W *
      ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXD
    have hXFint : MeasureTheory.IntegrableOn XF Work.Spaces.Iθ :=
      hXF ▸ (hFθ'.const_mul 3)
    have hXAint : MeasureTheory.IntegrableOn XA Work.Spaces.Iθ :=
      hXA ▸ (hAθ'.const_mul (3 * (α ^ 2) ^ 2))
    have hXDint : MeasureTheory.IntegrableOn XD Work.Spaces.Iθ :=
      hXD ▸ (hDθ'.const_mul (3 * (α * (5 + α)) ^ 2))
    have hpt' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        W * ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ XF θ + XA θ + XD θ := by
      filter_upwards [hdec] with θ hθ
      have h1 := mul_le_mul_of_nonneg_left hθ hWnn
      rw [hXF, hXA, hXD]
      nlinarith [h1]
    have hinner : (∫ θ in Work.Spaces.Iθ, W *
          ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ :=
      MeasureTheory.integral_mono_of_nonneg
        ((ae_slot_nonneg_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) α z).mono
          (fun θ hθ => mul_nonneg hWnn hθ))
        ((hXFint.add hXAint).add hXDint) hpt'
    have hsplit : (∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ)
        = 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by
      have e1 : (fun θ : ℝ => XF θ + XA θ + XD θ)
          = fun θ : ℝ => (fun θ' : ℝ => XF θ' + XA θ') θ + XD θ := rfl
      rw [e1, MeasureTheory.integral_add (f := fun θ' : ℝ => XF θ' + XA θ')
        (g := XD) (hXFint.add hXAint) hXDint]
      have e2 : (fun θ' : ℝ => XF θ' + XA θ')
          = fun θ' : ℝ => (fun θ'' : ℝ => XF θ'') θ' + (fun θ'' : ℝ => XA θ'') θ' := rfl
      rw [e2, MeasureTheory.integral_add (f := fun θ'' : ℝ => XF θ'')
        (g := fun θ'' : ℝ => XA θ'') hXFint hXAint]
      rw [hXF, hXA, hXD]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by
      calc W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
            (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          = ∫ θ in Work.Spaces.Iθ, W *
              ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
            rw [hW]
            exact wsq_mul_int_eq_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
              (fun θ => (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) z
        _ ≤ ∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ := hinner
        _ = 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := hsplit
    rw [hW] at h1
    exact h1

/-- **The two low-order slots** `z ↦ w z² ∫_θ (∂_θΨ)²` and `z ↦ w z² ∫_θ Ψ²` are `z`-integrable,
by the slice Poincaré inequality and the honesty of the `η`-slot. -/
theorem lowSlot_zInt {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)) Work.Spaces.Iz ∧
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Kp, hKp, hSP⟩ := Work.FTS.EllipticEst.Mine.SlicePoincare
  have hmem0 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  -- a.e. strong measurability of the two slot functions
  have haesm1 : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun _ : ℝ => (1 : ℝ)) 1 hΨsm
      continuousOn_const).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 1 Ψ z θ) ^ 2 * (1 : ℝ)))
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
    rw [← wsq_mul_int_eq_fts 1 Ψ (fun _ => (1 : ℝ)) z]
    simp only [mul_one]
  have haesm2 : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun _ : ℝ => (1 : ℝ)) 0 hΨsm
      continuousOn_const).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 0 Ψ z θ) ^ 2 * (1 : ℝ)))
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
    rw [← wsq_mul_int_eq_fts 0 Ψ (fun _ => (1 : ℝ)) z]
    simp only [Work.Spaces.pthIter_zero, mul_one]
  -- the `η`-slot Poincaré bound on the slices, a.e. in `z`
  have hbnd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(fun z => (Work.Spaces.w z) ^ 2 *
        ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) z‖
        ≤ (fun z => 2 * Kp * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ))) z := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici), ae_pos_Iz_fts]
      with z hz hzpos
    have hlow := Work.FTS.EllipticEst.remov.weakSliceRegular k hk1 α F Ψ hα hα4 hwk z hzpos
    have hcont : ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := hlow.1
    have h2e : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hlow.2.2.2.2.2.2
    have hC2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hwk.smooth hzpos 2
    obtain ⟨-, -, hb1, hb2⟩ := hSP (fun θ => Ψ z θ) hC2 hcont (hwk.zero z) (hwk.pi_half z) h2e
    have hA0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    have hB0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    have hR0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.integral_nonneg_of_ae
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
              (by linarith [hθ.2, Real.pi_pos])) _)))
    have hgoal : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ 2 * Kp * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        rfl
      have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          = ∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        rfl
      rw [e1, e2]
      linarith [hb1, hb2, hR0]
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
      mul_nonneg (sq_nonneg _) (add_nonneg hA0 hB0)
    rw [Real.norm_of_nonneg hnn]
    calc (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        ≤ (Work.Spaces.w z) ^ 2 * (2 * Kp * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hgoal (sq_nonneg _)
      _ = 2 * Kp * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring
  have haesm_sum : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcongr : (fun z => (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
          + (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        = fun z => (Work.Spaces.w z) ^ 2 *
            ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
      funext z; simp only [Pi.add_apply]; ring
    exact hcongr ▸ (haesm1.add haesm2)
  have hsum : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) Work.Spaces.Iz :=
    (hmem0.const_mul (2 * Kp)).mono' haesm_sum hbnd
  constructor
  · refine hsum.mono' haesm1 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    have hnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    have hbn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hbn) (sq_nonneg _)
  · refine hsum.mono' haesm2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    have hnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    have hbn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hbn) (sq_nonneg _)

/-! ## The slot functions of the target's right-hand side -/

/-- The left-hand (top) slot `z ↦ w z² ∫_θ (∂_θ^{k+2}Ψ)² sin^{2k-γ}`. -/
abbrev Ul1d_L (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))

/-- The source slot `z ↦ w z² ∫_θ (∂_θ^k G)² sin^{2k-γ}`. -/
abbrev Ul1d_E (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
      (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))

/-- The `u`-family slot at order `j`. -/
abbrev Ul1d_B (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))

/-- The sum of the `u`-family slots. -/
abbrev Ul1d_U (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∑ j ∈ Finset.Icc 3 (k + 1), Ul1d_B α k F Ψ j z

/-- The `η`-slot `z ↦ w z² ∫_θ (∂_θ²Ψ)² sEta`. -/
abbrev Ul1d_D (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ)

/-- The low slot `z ↦ w z² ∫_θ (∂_θΨ)²`. -/
abbrev Ul1d_T (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)

/-- The low slot `z ↦ w z² ∫_θ Ψ²`. -/
abbrev Ul1d_Z (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)

/-- The angular source of the bundle is the one used in the statement. -/
theorem Gsrc_eq_Gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.Mine.Gsrc α F Ψ = Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ := by
  funext z θ
  simp only [Work.FTS.EllipticEst.Mine.Gsrc, Work.FTS.EllipticEst.TT.ESW.Gsl,
    Work.FTS.EllipticEst.TT.ESW.Asl, Work.Spaces.Dz]

/-- A weighted angular slot is nonnegative. -/
theorem wsq_slot_nonneg_fts (m : ℕ) (f : ℝ → ℝ → ℝ) {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (z : ℝ) :
    0 ≤ (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m f z θ) ^ 2 * σ θ) :=
  mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
    (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))))

/-! ## The target -/

/-- **The two-dimensional assembly of the one-dimensional top-slot estimate.** -/
theorem U_le_of_1d (D : ℝ) (hD : 0 < D) :
    ∀ (k : ℕ), 3 ≤ k → Work.FTS.EllipticEst.TT.ESW.OneD k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl Ψ)
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl (Work.Spaces.DzIter 1 Ψ))
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C *
          ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  intro k hk hOneD
  obtain ⟨C1, hC1pos, h1d⟩ := hOneD
  refine ⟨max 1 C1, lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro α F Ψ hα hα4 hwk hH1 hH2
  obtain ⟨hγ1, hγ54⟩ := gam_bounds_fts hα hα4
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  -- ## the a.e. slicewise inequality, from `OneD k` applied to the slices
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Ul1d_L α k F Ψ z ≤ max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
        + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := by
    filter_upwards [Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability k hk D hD α F Ψ
      hα hα4 hwk hH1 hH2, ae_pos_Iz_fts] with z hz hzpos
    obtain ⟨hcont, hA, hB, hC, hD', hE, hF⟩ := hz
    have hsm : ContDiffOn ℝ (k + 2) (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hwk.smooth hzpos (k + 2)
    have heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ
          = Work.FTS.EllipticEst.Lzero1 (fun θ => Ψ z θ) θ :=
      fun θ hθ => (slice_source_eq hΨsm
        (fun z θ hz hθ0 hθ1 => hwk.eq z hz θ hθ0 hθ1) hzpos hθ).symm
    have hB0 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k
        (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      simpa only [Gsrc_eq_Gsl] using hB
    have hA' : MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv (k + 2) (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine hA.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hB' : MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv k (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine hB0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hC' : ∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv j (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      intro j hj
      refine (hC j hj).congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hD'' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2
          * (Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ := by
      refine hD'.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ => Ψ z θ)) θ from rfl]
    have hE' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => Ψ z θ) θ) ^ 2)
        Work.Spaces.Iθ := by
      refine hE.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 = (deriv (fun θ => Ψ z θ) θ) ^ 2
      rw [show Work.Spaces.pthIter 1 Ψ z θ = deriv (fun θ => Ψ z θ) θ from rfl]
    have hone := h1d (Work.Spaces.gam α) (fun θ => Ψ z θ)
      (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) hγ1 hγ54 hsm hcont
      (hwk.zero z) (hwk.pi_half z) heq hA' hB' hC' hD'' hE' hF
    -- the conversion of the six slots back to the `pthIter` language
    have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = ∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hBeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k
            (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hsum' : (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter j Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
        = ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun θ => Ψ z θ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hDeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ => Ψ z θ)) θ from rfl]
    have hEeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ => Ψ z θ) θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 = (deriv (fun θ => Ψ z θ) θ) ^ 2
      rw [show Work.Spaces.pthIter 1 Ψ z θ = deriv (fun θ => Ψ z θ) θ from rfl]
    have hone' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
      rw [hAeq, hBeq, hsum', hDeq, hEeq]
      exact hone
    have hdist : (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        = Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z := by
      simp only [Ul1d_E, Ul1d_U, Ul1d_B, Ul1d_D, Ul1d_T, Ul1d_Z, mul_add, Finset.mul_sum]
    have hnn : 0 ≤ Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
        + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z := by
      have h1 : 0 ≤ Ul1d_E α k F Ψ z :=
        wsq_slot_nonneg_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
          (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z
      have h2 : 0 ≤ Ul1d_U α k F Ψ z :=
        Finset.sum_nonneg (fun j _ => wsq_slot_nonneg_fts j Ψ
          (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z)
      have h3 : 0 ≤ Ul1d_D α k F Ψ z :=
        wsq_slot_nonneg_fts 2 Ψ (fun θ hθ => Work.FTS.EllipticEst.Mine.sp_sEta_nonneg hθ) z
      have h4 : 0 ≤ Ul1d_T α k F Ψ z := by
        simpa only [Ul1d_T, mul_one] using
          wsq_slot_nonneg_fts 1 Ψ (fun θ _ => zero_le_one) z
      have h5 : 0 ≤ Ul1d_Z α k F Ψ z := by
        simpa only [Ul1d_Z, Work.Spaces.pthIter_zero, mul_one] using
          wsq_slot_nonneg_fts 0 Ψ (fun θ _ => zero_le_one) z
      linarith
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ (Work.Spaces.w z) ^ 2 * (C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
              + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.pthIter j Ψ z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hone' (sq_nonneg (Work.Spaces.w z))
      _ = C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := by
          rw [show (Work.Spaces.w z) ^ 2 * (C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                  (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
                + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pthIter j Ψ z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
                + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ)
                + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
                + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
              = C1 * ((Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                    (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
                  + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pthIter j Ψ z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
                  + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                      * Work.FTS.EllipticEst.sEta θ)
                  + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
                  + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) from by ring]
          rw [hdist]
      _ ≤ max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 C1) hnn
  -- ## integrability of the five slot functions and of the majorant
  have hEint : MeasureTheory.IntegrableOn (Ul1d_E α k F Ψ) Work.Spaces.Iz :=
    sourceSlot_zInt hk hα hwk
  have hBint : ∀ j ∈ Finset.Icc 3 (k + 1),
      MeasureTheory.IntegrableOn (Ul1d_B α k F Ψ j) Work.Spaces.Iz :=
    fun j hj => uSlot_zInt hk hα hwk hj
  have hUint : MeasureTheory.IntegrableOn (Ul1d_U α k F Ψ) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 3 (k + 1)) hBint
  have hDint : MeasureTheory.IntegrableOn (Ul1d_D α k F Ψ) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk
  have hTint : MeasureTheory.IntegrableOn (Ul1d_T α k F Ψ) Work.Spaces.Iz :=
    (lowSlot_zInt hk hα hα4 hwk).1
  have hZint : MeasureTheory.IntegrableOn (Ul1d_Z α k F Ψ) Work.Spaces.Iz :=
    (lowSlot_zInt hk hα hα4 hwk).2
  have hGint : MeasureTheory.IntegrableOn
      (fun z => max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
        + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z)) Work.Spaces.Iz :=
    ((((hEint.add hUint).add hDint).add hTint).add hZint).const_mul (max 1 C1)
  -- ## the integral comparison
  have hLnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ Ul1d_L α k F Ψ z :=
    Filter.Eventually.of_forall (fun z => wsq_slot_nonneg_fts (k + 2) Ψ
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z)
  have hmono : (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z) ≤
      ∫ z in Work.Spaces.Iz, max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
        + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
    MeasureTheory.integral_mono_of_nonneg hLnn hGint hae
  have hsplit1 : (∫ z in Work.Spaces.Iz, max 1 C1 *
        (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
          + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
      = max 1 C1 * ∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
          + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
    MeasureTheory.integral_const_mul (max 1 C1) _
  have hsplit2 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
          + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
      = (∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z) := by
    have e1 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
          + Ul1d_T α k F Ψ z)
        (g := fun z => Ul1d_Z α k F Ψ z)
        (((hEint.add hUint).add hDint).add hTint) hZint
    have e2 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z)
        (g := fun z => Ul1d_T α k F Ψ z)
        ((hEint.add hUint).add hDint) hTint
    have e3 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z)
        (g := fun z => Ul1d_D α k F Ψ z) (hEint.add hUint) hDint
    have e4 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
          + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z) (g := fun z => Ul1d_U α k F Ψ z) hEint hUint
    rw [e1, e2, e3, e4]
  have hsplit3 : (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
      = ∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z :=
    MeasureTheory.integral_finsetSum (Finset.Icc 3 (k + 1)) hBint
  have hfin : (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z) ≤ max 1 C1 *
      ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
        + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z)
        + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by
    calc (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z)
        ≤ ∫ z in Work.Spaces.Iz, max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := hmono
      _ = max 1 C1 * ∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := hsplit1
      _ = max 1 C1 * ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by rw [hsplit2]
      _ = max 1 C1 * ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z)
            + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by rw [hsplit3]
  simpa only [Ul1d_L, Ul1d_E, Ul1d_U, Ul1d_B, Ul1d_D, Ul1d_T, Ul1d_Z] using hfin

end Work.FTS.EllipticEst.TT.ESW
