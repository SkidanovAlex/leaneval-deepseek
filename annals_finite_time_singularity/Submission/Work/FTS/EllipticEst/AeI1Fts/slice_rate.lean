import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/slice_rate` — the slicewise rate of `U = z∂_zu` at the two endpoints

For a datum `AeData α u G`, with the two `ℋ⁰`-honesties of the slots
`U u = z ∂_z u` and `V u = z ∂_z∂_θu = ∂_θ(U u)` (Clairaut), the angular slice of `U` obeys,
for almost every `z > 0`, the two endpoint rates

* `|U(z,θ)| ≤ C (∫_{0<θ'<θ} V(z,θ')² σ(θ'))^{1/2} θ^{(1+η)/2}`,
* `|U(z,θ)| ≤ C (∫_{θ<θ'<π/2} V(z,θ')² σ(θ'))^{1/2} (π/2-θ)^{(1+η)/2}`

with `σ = sigE = sin(2θ)^{-η}` and a universal constant `C` (`C = √2` outright).

## Proof

`Work.EllipticEst.Core.sliceBoundaryLimit` (the sharp boundary-rate lemma of the `TT`
workstream) gives, for a `C¹` slice `f` whose weighted derivative square `(f')²·thEta` is
integrable on `(0,π/2)`, two endpoint constants `c₀`, `c₁` with

`(f θ - c)² ≤ K θ^{1+η} ∫_{0<θ'<θ} (f')² thEta`,  resp. the `(π/2-θ)`-analogue, `K = 2`.

The two constants vanish because the trace lemma
`Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk` shows that `U u z ·` tends to `0` at both endpoints
for a.e. `z > 0` (the hypothesis on `z * ∂_θ∂_zu` is transported from `HkMem α 0 (V u)` by
Clairaut), so the two limits coincide with `0` by uniqueness.  Taking square roots
(`√f ≤ √(c^{1+η}A) = c^{(1+η)/2}√A` because `∫ (sin 2θ')^{η} ≤ (2θ)^{1+η}/(1+η)`) and
rewriting `∂_θ(U u z ·) = V u z ·` (Clairaut, on the open interval) and
`thEta = sigE` finishes.

-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## The two angular weights agree -/

private theorem sigE_eq_thEta (θ : ℝ) : sigE θ = Work.FTS.EllipticEst.thEta θ := by
  rw [sigE, Work.FTS.EllipticEst.thEta]

/-! ## Transport of `HkMem` along equality on the open quadrant -/

/-- On `Iθ` the level-`0` `ℋ`-integrand only sees the values of the function on the open
quadrant. -/
private theorem hkIntegrand_zero_congr' (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand α 0 g z θ := by
  rw [hk_zero_eq α f hθ, hk_zero_eq α g hθ]
  by_cases hw : Work.Spaces.w z = 0
  · rw [hw]; ring
  by_cases hs : sigE θ = 0
  · rw [hs]; ring
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · exact absurd (by rw [← h0, Work.FTS.EllipticEst.TT.AeI1.w_eq_zero_at_zero]) hw
    · exact h0
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    intro hsin0
    apply hs
    rw [sigE, hsin0,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
  have hθ0 : θ ≠ 0 := by
    intro h; exact hsin (by rw [h]; norm_num)
  have hθπ : θ ≠ Real.pi / 2 := by
    intro h
    exact hsin (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
  have hθIoo : 0 < θ ∧ θ < Real.pi / 2 :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθπ⟩
  rw [heq z θ hzpos hθIoo.1 hθIoo.2]

/-- **`HkMem` is invariant under equality on the open quadrant.** -/
private theorem hkMem_zero_congr' {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hf : Work.Spaces.HkMem α 0 f) : Work.Spaces.HkMem α 0 g := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact (hf.1 z hz).congr_fun (fun θ hθ => hkIntegrand_zero_congr' α heq hz hθ)
      measurableSet_Icc
  · exact (hf.2).congr_fun
      (fun z hz => MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ hθ => hkIntegrand_zero_congr' α heq hz hθ)) measurableSet_Ici

/-! ## Slice integrability of `V z θ' ² σ θ'` -/

private theorem slice_sigE_int {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Iθo := by
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz
  have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ) Work.Spaces.Iθ :=
    hf.1 z hzmem
  have h2 : IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ :=
    IntegrableOn.congr_fun h1 (fun θ hθ => hk_zero_eq α f hθ) measurableSet_Icc
  have h3 : IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
    have h4 : Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Integrable.const_mul h2 ((Work.Spaces.w z) ^ 2)⁻¹
    refine IntegrableOn.congr_fun h4 (fun θ _ => ?_) measurableSet_Icc
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul]
  exact IntegrableOn.congr_set_ae h3
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))

/-! ## Nonnegativity of the slice energy -/

private theorem integral_V_sigE_nonneg {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Iθo) :
    0 ≤ ∫ θ' in Set.Ioo 0 θ, (V u z θ') ^ 2 * sigE θ' :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun θ' hθ' =>
    mul_nonneg (sq_nonneg _)
      (sigE_nonneg ⟨le_of_lt hθ'.1, le_of_lt (lt_trans hθ'.2 hθ.2)⟩)

private theorem integral_V_sigE_nonneg_right {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Iθo) :
    0 ≤ ∫ θ' in Set.Ioo θ (Real.pi / 2), (V u z θ') ^ 2 * sigE θ' :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun θ' hθ' =>
    mul_nonneg (sq_nonneg _)
      (sigE_nonneg ⟨le_of_lt (lt_trans hθ.1 hθ'.1), le_of_lt hθ'.2⟩)

/-! ## From the squared rate to the square-root rate -/

private theorem abs_le_sqrt_mul {f A c K : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hA : 0 ≤ A)
    (h : f ^ 2 ≤ K * c ^ (1 + Work.Spaces.eta) * A) :
    |f| ≤ Real.sqrt K * Real.sqrt A * c ^ ((1 + Work.Spaces.eta) / 2) := by
  have hc0 : 0 ≤ c := hc.le
  have h1 : Real.sqrt (K * c ^ (1 + Work.Spaces.eta) * A)
      = Real.sqrt K * Real.sqrt (c ^ (1 + Work.Spaces.eta) * A) := by
    rw [show K * c ^ (1 + Work.Spaces.eta) * A
        = K * (c ^ (1 + Work.Spaces.eta) * A) from by ring,
      Real.sqrt_mul hK]
  have h2 : Real.sqrt (c ^ (1 + Work.Spaces.eta) * A)
      = Real.sqrt (c ^ (1 + Work.Spaces.eta)) * Real.sqrt A :=
    Real.sqrt_mul (Real.rpow_nonneg hc0 (1 + Work.Spaces.eta)) A
  have h3 : Real.sqrt (c ^ (1 + Work.Spaces.eta)) = c ^ ((1 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0]
    congr 1
    ring
  calc |f| = Real.sqrt (f ^ 2) := (Real.sqrt_sq_eq_abs f).symm
    _ ≤ Real.sqrt (K * c ^ (1 + Work.Spaces.eta) * A) := Real.sqrt_le_sqrt h
    _ = Real.sqrt K * Real.sqrt (c ^ (1 + Work.Spaces.eta) * A) := h1
    _ = Real.sqrt K * (Real.sqrt (c ^ (1 + Work.Spaces.eta)) * Real.sqrt A) := by rw [h2]
    _ = Real.sqrt K * (c ^ ((1 + Work.Spaces.eta) / 2) * Real.sqrt A) := by rw [h3]
    _ = Real.sqrt K * Real.sqrt A * c ^ ((1 + Work.Spaces.eta) / 2) := by ring

/-! ## The per-slice rate -/

private theorem slice_rate_at {α : ℝ} {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) {z : ℝ} (hz : 0 < z)
    (h0 : Tendsto (fun θ => U u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Tendsto (fun θ => U u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Iθo, |U u z θ| ≤ C * Real.sqrt (∫ θ' in Set.Ioo 0 θ,
          (V u z θ') ^ 2 * sigE θ') * θ ^ ((1 + Work.Spaces.eta) / 2)) ∧
      (∀ θ ∈ Iθo, |U u z θ| ≤ C * Real.sqrt (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (V u z θ') ^ 2 * sigE θ') * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) := by
  obtain ⟨K, hKpos, hSBL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hcd : ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo := contDiffOn_slice_U_one hS hz
  have hintV : IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Iθo := slice_sigE_int hV hz
  have hintD : IntegrableOn
      (fun θ => (deriv (fun θ' => U u z θ') θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Iθo :=
    IntegrableOn.congr_fun hintV (fun θ hθ => by
      simp only [slice_deriv_U hS hz hθ, sigE_eq_thEta θ]) measurableSet_Ioo
  obtain ⟨⟨cL, hlimL, hbdL⟩, ⟨cR, hlimR, hbdR⟩⟩ := hSBL (fun θ => U u z θ) hcd hintD
  have hcL : cL = 0 := tendsto_nhds_unique hlimL h0
  have hcR : cR = 0 := tendsto_nhds_unique hlimR h1
  have hintEqL : ∀ θ ∈ Iθo,
      (∫ θ' in Set.Ioo 0 θ,
          (deriv (fun θ'' => U u z θ'') θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo 0 θ, (V u z θ') ^ 2 * sigE θ' := by
    intro θ hθ
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => by
      simp only [slice_deriv_U hS hz ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩, sigE_eq_thEta θ'])
  have hintEqR : ∀ θ ∈ Iθo,
      (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ'' => U u z θ'') θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo θ (Real.pi / 2), (V u z θ') ^ 2 * sigE θ' := by
    intro θ hθ
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => by
      simp only [slice_deriv_U hS hz ⟨lt_trans hθ.1 hθ'.1, hθ'.2⟩, sigE_eq_thEta θ'])
  refine ⟨Real.sqrt K, Real.sqrt_nonneg K, ?_, ?_⟩
  · intro θ hθ
    have h := hbdL θ hθ
    rw [hcL, sub_zero, hintEqL θ hθ] at h
    exact abs_le_sqrt_mul hKpos.le hθ.1 (integral_V_sigE_nonneg hθ) h
  · intro θ hθ
    have h := hbdR θ hθ
    rw [hcR, sub_zero, hintEqR θ hθ] at h
    exact abs_le_sqrt_mul hKpos.le (by linarith [hθ.2]) (integral_V_sigE_nonneg_right hθ) h

/-! ## The target -/

theorem slice_rate {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeI1Fts.U u z θ|
        ≤ C * Real.sqrt (∫ θ' in Set.Ioo 0 θ,
              (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
                * Work.FTS.EllipticEst.AeI1Fts.sigE θ') * θ ^ ((1 + Work.Spaces.eta) / 2))
      ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeI1Fts.U u z θ|
        ≤ C * Real.sqrt (∫ θ' in Set.Ioo θ (Real.pi / 2),
              (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
                * Work.FTS.EllipticEst.AeI1Fts.sigE θ')
            * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) := by
  have hS : SmoothOpen u := smoothOpen_of_forall h.smooth
  have hMix : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) := by
    refine hkMem_zero_congr' (f := V u)
      (g := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ?_ hV
    intro z θ hz hθ0 hθπ
    show z * Work.Spaces.pz (Work.Spaces.pth u) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ
    exact congrArg (fun t => z * t) (Work.Spaces.pz_pth_comm (f := u)
      ((h.smooth 2).contDiffAt (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz, hθ0, hθπ⟩))))
  have htr := Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk α u G h
    (show Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) from hU) hMix
  filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hztr hz
  exact slice_rate_at hS hV (Set.mem_Ioi.mp hz) hztr.1 hztr.2

end

end Work.FTS.EllipticEst.AeI1Fts
