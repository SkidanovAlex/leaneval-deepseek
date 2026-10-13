import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EComparison.SZML2.Basic
import Submission.Work.FTS.StrongEps.EComparison.sin_two_rpow_integral_le
import Submission.Work.FTS.StrongEps.EComparison.slice_abs_le_sqrt_sliceEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

noncomputable section

set_option autoImplicit false

/-! ## Continuity on the open quadrant, and a.e. strong measurability of the slices -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma continuousOn_psi {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => psi Φ p.1 p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have hs2 : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2) Qd :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact ContinuousOn.div hΦ hs2 (fun p hp => ne_of_gt (sin_two_pos_of_mem hp.2))

lemma continuousOn_slot {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (psi Φ p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Qd := by
  have hpsi := continuousOn_psi (Φ := Φ) hsm
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd :=
    ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem hp.2)))
  exact (hpsi.mul (hw.div hs (fun p hp =>
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem hp.2) _)))).pow 2

lemma continuousOn_absPhi {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Qd :=
  (hsm 0).continuousOn.abs

lemma continuousOn_PhiSqRoot {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2 * rootWeight p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have hrw : ContinuousOn (fun p : ℝ × ℝ => rootWeight p.2) Qd := by
    show ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(2 + Work.Spaces.eta))) Qd
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem hp.2)))
  exact (hΦ.pow 2).mul hrw

lemma continuousOn_mode {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Φ p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have he : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Qd :=
    (((Real.continuous_cos.mul ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC
      (2 * m + 1)).continuous.comp Real.continuous_sin)).comp continuous_snd)).continuousOn
  have hc : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Qd :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  exact (hΦ.mul he).mul hc

/-- Marginal measurability: a function continuous on the open quadrant has `θ`-integrals
that are a.e. strongly measurable in `z` on `Iz = [0,∞)`. -/
lemma aesm_sliceIntegral {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, g (z, θ))
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd g hg).integral_prod_right'
    (ν := volume.restrict Work.Spaces.Iθ)

/-- The same, on a measurable subset of `Iz`. -/
lemma aesm_sliceIntegral_of_subset {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {s : Set ℝ}
    (hs : s ⊆ Work.Spaces.Iz) (hsm : MeasurableSet s) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, g (z, θ)) (volume.restrict s) := by
  have h := aesm_sliceIntegral hg
  have hEq : volume.restrict s = (volume.restrict Work.Spaces.Iz).restrict s := by
    rw [MeasureTheory.Measure.restrict_restrict hsm, Set.inter_eq_left.mpr hs]
  rw [hEq]
  exact h.restrict

/-! ## `θ`-integrability of the `(0,0)` slot of `Ψ` and of `|Φ|` -/

/-- `θ ∈ (0,π/2)` for a.e. `θ` of `Iθ` (the two endpoints are null). -/
lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hEq : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [hEq]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The `(0,0)` slot of `Ψ` is `θ`-integrable on `Iθ` for every `z > 0` (and the constant
`w(z)² ≠ 0` can be removed). -/
lemma integrableOn_psi_sq_rpow {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
  have hquad := continuousOn_slot (Φ := Φ) hsm
  have hslot : MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hHk.1 z (by show (0 : ℝ) ≤ z; exact le_of_lt hz))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hquad hz) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α 6 (psi Φ) z θ 0 (by norm_num)
  have h2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
      * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) Work.Spaces.Iθ :=
    hslot.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => slot0_integrand_eq Φ z hθ))
  have h3 : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
      * ((Work.Spaces.w z) ^ 2
        * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  refine h3.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
  exact inv_mul_cancel_left₀ (ne_of_gt (w_sq_pos hz)) _

/-- `|Φ z ·|` is `θ`-integrable on `Iθ` for `z > 0`: AM–GM with the pair
`|Ψ| sin(2θ)^{-η/2}` and `sin(2θ)^{1+η/2}`. -/
lemma integrableOn_abs_Phi {Φ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply_univ, show Work.Spaces.Iθ
      = Set.Icc (0 : ℝ) (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hsin : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ)) ?_ ?_
    · exact (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ _ => Or.inr (le_of_lt two_add_eta_pos))).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)]
      exact Real.rpow_le_one (sin_two_nonneg_of_mem_Iθ' hθ) (Real.sin_le_one (2 * θ))
        (le_of_lt two_add_eta_pos)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => |Φ z θ|)
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ) (hsm 0).continuousOn hz).norm
  have hsum : MeasureTheory.IntegrableOn (fun θ => ((psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) / 2) Work.Spaces.Iθ :=
    (hint.add hsin).div_const 2
  refine MeasureTheory.Integrable.mono' hsum haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  simp only [Real.norm_eq_abs, abs_abs]
  have hΦ : Φ z θ = psi Φ z θ * Real.sin (2 * θ) := by
    rw [psi_apply, Work.Construction.s2, div_mul_cancel₀ _ (ne_of_gt hs)]
  have hsqrt : Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      * Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) = Real.sin (2 * θ) := by
    rw [← Real.sqrt_mul (Real.rpow_nonneg (le_of_lt hs) _)]
    have h : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) = (Real.sin (2 * θ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hs (-Work.Spaces.eta) (2 + Work.Spaces.eta),
        show (-Work.Spaces.eta) + (2 + Work.Spaces.eta) = (2 : ℝ) by ring]
      exact Real.rpow_natCast _ 2
    rw [h, Real.sqrt_sq (le_of_lt hs)]
  have habs : |Φ z θ| = |psi Φ z θ| * Real.sin (2 * θ) := by
    rw [hΦ, abs_mul, abs_of_pos hs]
  have hamgm : |psi Φ z θ| * Real.sin (2 * θ)
      ≤ ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) / 2 := by
    have hsquare := sq_nonneg (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      - Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)))
    have h1 : (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) ^ 2
        = (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (Real.rpow_nonneg (le_of_lt hs) _)]
    have h2 : (Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))) ^ 2
        = (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) :=
      Real.sq_sqrt (Real.rpow_nonneg (le_of_lt hs) _)
    have h3 : |psi Φ z θ| * Real.sin (2 * θ)
        = (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
            * Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := by
      rw [mul_assoc, hsqrt]
    rw [h3]
    nlinarith [hsquare, h1, h2]
  rw [habs]
  exact hamgm

/-! ## The `θ`-integral bounds for `sin(2θ)^{2+η}` -/

/-- Constant bounding `∫_{Iθ} sin(2θ)^{2+η}`: `√(π/2)`. -/
def K3 : ℝ := Real.sqrt (Real.pi / 2)

/-- Constant bounding the boundary-layer factor `√(∫_E sin(2θ)^{2+η})` by
`C·δ^{(3+η)/2}`. -/
def K4 : ℝ := Real.sqrt ((2 : ℝ) ^ (2 + Work.Spaces.eta))

lemma K3_pos : 0 < K3 := Real.sqrt_pos_of_pos (by positivity)

lemma K4_pos : 0 < K4 := Real.sqrt_pos_of_pos (by positivity)

lemma sqrt_sin_int_Iθ_le : Real.sqrt (∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) ≤ K3 := by
  rw [K3]
  exact Real.sqrt_le_sqrt (sin_two_rpow_integral_le (1 / 2) (by norm_num) (by
    linarith [Real.pi_gt_three])).2.2

/-- `√(∫_E sin(2θ)^{2+η}) ≤ K4 δ^{(3+η)/2}` for the boundary layers `E`. -/
lemma sqrt_sin_int_layer_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4) :
    Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K4 * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      Real.sqrt (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K4 * δ ^ ((3 + Work.Spaces.eta) / 2) := by
  have hsq : Real.sqrt (δ ^ (3 + Work.Spaces.eta))
      = δ ^ ((3 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hδ) (3 + Work.Spaces.eta) (1 / 2 : ℝ)]
    congr 1
    ring
  have hreal : Real.sqrt ((2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta))
      = K4 * δ ^ ((3 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg (by norm_num) _), K4, hsq]
  obtain ⟨hb1, hb2, -⟩ := sin_two_rpow_integral_le δ hδ hδ4
  refine ⟨?_, ?_⟩
  · rw [← hreal]
    exact Real.sqrt_le_sqrt hb1
  · rw [← hreal]
    exact Real.sqrt_le_sqrt hb2

/-! ## The slice Cauchy–Schwarz bound (the interface of the target statement) -/

/-- The Cauchy–Schwarz slice bound, with the constant `√(sliceEnergy Φ z)` factored out. -/
lemma slice_abs_le_sqrt {Φ : ℝ → ℝ → ℝ} (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
    MeasureTheory.IntegrableOn
    (fun θ => (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) {E : Set ℝ} (hE : E ⊆ Work.Spaces.Iθ) :
    ∫ θ in E, |Φ z θ| ≤ Real.sqrt (sliceEnergy Φ z)
      * Real.sqrt (∫ θ in E, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) :=
  slice_abs_le_sqrt_sliceEnergy (Φ := Φ) (z := z) (E := E) hE
    (by simpa only [psi_apply, Work.Construction.s2] using hint z hz)

end

end Work.FTS.StrongEps.EComparison
