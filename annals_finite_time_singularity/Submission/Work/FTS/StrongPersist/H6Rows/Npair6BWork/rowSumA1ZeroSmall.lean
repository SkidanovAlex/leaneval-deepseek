import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## Integrability and bounds of the slots -/

/-- The bound and integrability of a slot with `(i,j) ≠ (0,0)`: the pointwise domination by the
level-six integrand integrates to `K·HkSq α 6 f`. -/
theorem rowA_slot_bound {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) (hia : i ≤ a) (hjb : j ≤ b) (hij : 1 ≤ i + j) :
    MeasureTheory.Integrable (rowA_piece f A ρ a b i j) pqm ∧
      |∫ p, rowA_piece f A ρ a b i j p ∂pqm| ≤ K * Work.Spaces.HkSq α 6 f := by
  obtain ⟨hHkInt, hHkEq⟩ := rowA_HkIntegrand_prodIntegrable (k := 6) hso hm6
  have hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ
  have hdom : ∀ᵐ p ∂pqm,
      |rowA_piece f A ρ a b i j p| ≤ K * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
    Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
      (fun θ hθ z hz => rowA_slot_dom hα hα1 hK hρ hAbd hab hia hjb hij hz hθ)
  have hInt : MeasureTheory.Integrable (rowA_piece f A ρ a b i j) pqm :=
    (hHkInt.const_mul K).mono'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (rowA_piece_continuousOn hso hAso hρc))
      (by simpa only [Real.norm_eq_abs] using hdom)
  refine ⟨hInt, ?_⟩
  calc |∫ p, rowA_piece f A ρ a b i j p ∂pqm|
      ≤ ∫ p, |rowA_piece f A ρ a b i j p| ∂pqm := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, K * Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂pqm :=
        MeasureTheory.integral_mono_ae hInt.abs (hHkInt.const_mul K) hdom
    _ = K * ∫ p, Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂pqm :=
        MeasureTheory.integral_const_mul K _
    _ = K * Work.Spaces.HkSq α 6 f := by rw [hHkEq]

/-- The bound and integrability of the leading `(0,0)`-slot: the exact radial self-pairing
(`dzSelfA2d`) gives `5K·HkSq α 6 f` without ever using the level-seven norm. -/
theorem rowA_slot00 {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (rowA_piece f A ρ a b 0 0) pqm ∧
      |∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm| ≤ 5 * K * Work.Spaces.HkSq α 6 f := by
  have hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ
  have hInt : MeasureTheory.Integrable (rowA_piece f A ρ a b 0 0) pqm := by
    obtain ⟨hHk7Int, -⟩ := rowA_HkIntegrand_prodIntegrable (k := 7) hso hm7
    refine (hHk7Int.const_mul K).mono'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (rowA_piece_continuousOn hso hAso hρc)) ?_
    filter_upwards [Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
      (fun θ hθ z hz => rowA_slot_dom_00 hα hK hρ hAbd hab hz hθ)] with p hp
    simpa only [Real.norm_eq_abs] using hp
  refine ⟨hInt, ?_⟩
  obtain ⟨σ, hσeq, hσpos, hσm, hσle⟩ := rowA_leaf_decomp hα hα1 hρ
  have hAb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K := by
    intro z θ hz h1 h2
    have h := hAbd z θ hz h1 h2 0 0 (by norm_num)
    simpa using h
  obtain ⟨hVae, hFρ, hD2ρ, hcrossρ⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.leadPiece α hα hα1 hso hAso hm6 hm7 hK hρ hab hAb
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) pqm :=
    hFρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
        = (Work.Spaces.w p.1) ^ 2 * σ p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
      rw [hσeq p.1 p.2])
  have hD2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2) pqm :=
    hD2ρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2
        = (Work.Spaces.w p.1) ^ 2 * σ p.2
          * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2
      rw [hσeq p.1 p.2])
  have hcross : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2))) pqm :=
    hcrossρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
          * Work.Spaces.mixed b a f p.1 p.2))
        = (Work.Spaces.w p.1) ^ 2 * σ p.2
          * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
            * Work.Spaces.mixed b a f p.1 p.2))
      rw [hσeq p.1 p.2])
  have hdz := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d (σ := σ) (A := A)
    (V := Work.Spaces.mixed b a f) (K := K) hK hσm hσpos
    (fun θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice hAso hθ 1)
    hAb
    (fun z θ hz h1 h2 => by
      have h := hAbd z θ hz h1 h2 1 0 (by norm_num)
      have hrz : Work.Spaces.mixed 1 0 A z θ = z * deriv (fun z' => A z' θ) z := rfl
      rw [hrz] at h
      simpa using h)
    (fun θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice (hso.mixed b a) hθ 1)
    hVae hF hD2 hcross
  have hS : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 6 f := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).1 b (by omega) σ
        (fun θ hθ => le_of_lt (hσpos θ hθ)) (fun θ hθ => by simpa using hσle θ hθ)
      simpa using h
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).2 b a ha1 (by omega) σ
        (fun θ hθ => le_of_lt (hσpos θ hθ)) (fun θ hθ => by simpa [if_neg ha0] using hσle θ hθ)
      simpa using h
  have hcongr : (∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ
            * (A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
              * Work.Spaces.mixed b a f z θ)) := by
    rw [MeasureTheory.integral_prod _ hInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [rowA_piece, Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Nat.sub_zero]
    rw [hσeq z θ]
    rw [show Work.Spaces.mixed (b + 1) a f z θ
        = z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ from rfl]
    ring
  calc |∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
            * Work.Spaces.mixed b a f z θ))| := by rw [hcongr]
    _ ≤ 5 * K * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (Work.Spaces.mixed b a f z θ) ^ 2) := hdz
    _ ≤ 5 * K * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hS (by linarith)

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## §1. Products of `SmoothOpen` fields -/

theorem smoothOpen_mul {A Q : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hQ : Work.FTS.EllipticEst.SmoothOpen Q) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * Q z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at hA hQ ⊢
  intro n
  exact (hA n).mul (hQ n)

/-! ## §2. The weight identity `(Wt α z θ)² = w z² sin(2θ)^{-γ}` -/

theorem Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The canonical slot weight is a product of a `z`-weight and a `θ`-weight. -/
theorem canonW_eq (q z θ : ℝ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := rfl

/-! ## §3. The radial integral `∫_{Iz} (1+z)^{-2} = 1` -/

/-- `z ↦ -(1+z)⁻¹` has derivative `((1+z)²)⁻¹` on `z ≥ 0`. -/
theorem hasDerivAt_neg_inv_one_add (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (((1 + x) ^ 2)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hx0 : (1 + x) ≠ 0 := by positivity
  have h2 := (h1.inv hx0).neg
  have hval : -(-1 / (1 + x) ^ 2) = ((1 + x) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, neg_mul, neg_neg, one_mul]
  rwa [hval] at h2

/-- `-(1+z)⁻¹ → 0` as `z → ∞`. -/
theorem tendsto_neg_inv_one_add :
    Tendsto (fun z : ℝ => -((1 + z)⁻¹)) atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_left atTop (1 : ℝ) Filter.tendsto_id)
  simpa using h.neg

/-- The radial integral `∫_{Iz} (1+z)⁻² dz = 1`. -/
theorem integral_inv_sq_Iz :
    ∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹ = 1 := by
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun z : ℝ => -((1 + z)⁻¹)) (g' := fun z : ℝ => ((1 + z) ^ 2)⁻¹)
    (fun x hx => hasDerivAt_neg_inv_one_add x hx) (fun x _ => by positivity)
    tendsto_neg_inv_one_add
  rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi, hmain]
  norm_num

/-- `z ↦ (1+z)⁻²` is integrable on `Iz`. -/
theorem integrableOn_inv_sq_Iz :
    IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) Work.Spaces.Iz := by
  have h' : IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (a := (0 : ℝ)) (l := (0 : ℝ))
      (g := fun z : ℝ => -((1 + z)⁻¹)) (g' := fun z : ℝ => ((1 + z) ^ 2)⁻¹)
      (fun x hx => hasDerivAt_neg_inv_one_add x hx) (fun x _ => by positivity)
      tendsto_neg_inv_one_add
  have h'' : IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) (Set.Ici (0 : ℝ)) := by
    rw [MeasureTheory.IntegrableOn,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]
    exact h'
  rwa [Work.Spaces.Iz]

/-! ## §4. The datum slot against `HkIntegrand` -/

/-- **The datum-slot domination.**  A leaf weight `ρ` of the slot `a` times the square of
the slot `D_z^b D_θ^a f` is pointwise dominated by `HkIntegrand α 6 f`, for `a + b ≤ 6`. -/
theorem fSlot_le_HkIntegrand {α : ℝ} (hα0 : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ}
    (hab : a + b ≤ 6) {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hσ : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hρ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_eta hleaf z θ hz hθ0 hθ1
    have hρ' : ρ z θ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      simpa only [Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafEta_eq_canonW, canonW_eq]
        using hρ
    have hstep : ρ z θ * (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed b 0 f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hρ' (sq_nonneg _)
    have hfinal : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      rw [Work.Spaces.mixed_zero_right]
      have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f z θ) ^ 2
          = (Work.Spaces.DzIter b f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.Spaces.sq_mul_div_rpow (Work.Spaces.DzIter b f z θ) (Work.Spaces.w z)
          (Real.sin (2 * θ)) Work.Spaces.eta hσ (by norm_num [Work.Spaces.eta])]
        ring
      rw [hid]
      exact Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ b (by omega)
    exact le_trans hstep hfinal
  · have hρ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_gam hα0 hleaf z θ hz hθ0 hθ1
    have hρ' : ρ z θ
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      simpa only [Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafGam_eq_canonW, canonW_eq]
        using hρ
    have hstep : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hρ' (sq_nonneg _)
    have hfinal : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2
          = (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_pow, Wt_sq_eq α z θ hσ]
        ring
      rw [hid]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b (by omega) (by omega)
    exact le_trans hstep hfinal

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.FlatW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `w²σ^{-q}·(α+σ)σ^{α/5} ≤ 2 w²σ^{-γ}` on the open quadrant, for `q ≤ γ` and `α ∈ (0,1]`:
the flat price of a coefficient slot against the canonical slot weights of the `γ`-leaf. -/
theorem canonWMulFlatAgm {α q z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hq : q ≤ Work.Spaces.gam α) (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      ≤ 2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hexp : (0 : ℝ) ≤ α / 5 + (Work.Spaces.gam α - q) := by
    have : 0 ≤ Work.Spaces.gam α - q := by rw [hgam]; linarith
    linarith
  have hrpow : (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 hexp
  have hkey : (α + Real.sin (2 * θ))
        * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) ≤ 2 := by
    have h2 : (α + Real.sin (2 * θ)) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
    calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q))
        ≤ (α + Real.sin (2 * θ)) * 1 := mul_le_mul_of_nonneg_left hrpow h0
      _ ≤ 2 := by linarith
  have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hmul : (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)) := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.SlotT2.canonW]
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
          * (Real.sin (2 * θ)) ^ (α / 5)) * (α + Real.sin (2 * θ)) := by ring
    _ = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q)))
          * (α + Real.sin (2 * θ)) := by rw [hmul]
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5 + (Work.Spaces.gam α - q))) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * 2 :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg hw (Real.rpow_nonneg hs.le _))
    _ = 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1ZeroSmall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- **Leibniz summand with a pure coefficient slot (`a₁ = 0`), radial order `b₁ ≤ 4`, mixed datum `1 ≤ a`,
`b₁ ≤ b`.**

`X := D_z^{b₁}A`, `Y := mixed (b+1-b₁) a f`, `Z := mixed b a f`, both `f`-slots mixed (`a ≥ 1`) and of order
`≤ 6` (`ord Z = a+b ≤ 6`, `ord Y = a+b+1-b₁ ≤ 6` by the non-flux hypothesis `¬(b₁ = 0 ∧ a+b = 6)` and
`b₁ ≤ b`).

* `b₁ ≤ 2`: `|D_z^{b₁}A| ≤ Cα^{-1/2}(K0+K4)` pointwise (`CoefData.val` at `b₁ = 0`, `TransportS.sup_dz_le_hk`
  at `b₁ = 1,2`, with `Xn α A = HkNorm α 4 A`), and `∫ρ|Y||Z| ≤ HkSq α 6 f` (Cauchy–Schwarz with the same
  weight `ρ ≤ canonW (gam α)`; each weighted square is a mixed slot of `HkIntegrand α 6 f`).
* `3 ≤ b₁ ≤ 4`: `|D_z^{b₁}A| ≤ C₃α^{-1/2}K6` (`T1SixAux.supSix` applied to `A` with `(b,a) = (b₁,0)`,
  `HkMem α 6 A`), and `∫ρ|Y||Z| ≤ M·HkNorm α 6 f` because `ord Y = a+b+1-b₁ ≤ 4` (using `b₁ ≤ b`) gives
  `∫ρY² ≤ HkSq α 4 f ≤ M²` (a mixed slot of `HkIntegrand α 4 f`), while `∫ρZ² ≤ HkSq α 6 f`.

Assemble with `Npair6BWork.rowSummand_core`/`val_le_HkSq`, `canonW_mul_z_le_of_le`,
`canonW_mul_mixed_le_of_le`, `leafW_le_canonW_gam`, `aesm_mixed`, `HkMem_mono_le`. -/
theorem rowSumA1ZeroSmall : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → 1 ≤ a → b₁ ≤ 4 → b₁ ≤ b →
      ¬ (b₁ = 0 ∧ a + b = 6) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter b₁ A p.1 p.2
          * Work.Spaces.mixed (b + 1 - b₁) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
               + M * K6 * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨Cdz, hCdz, hdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Csup, hCsup, hsup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  refine ⟨Cdz * Real.sqrt 10 + Csup + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b b₁ ρ hcoef hctmem hctle hdat hab hleaf ha hb1le4 hb1leb hflux
  obtain ⟨hα0, hα1⟩ := hα
  -- the inverse power of `α`
  have hαinv0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαinv1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  -- nonnegativity of every price
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg _) (hcoef.val 1 (Real.pi / 4) one_pos
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hQ4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hQ6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  -- the two `f`-slots and the common weight
  let cW : ℝ → ℝ → ℝ := Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α)
  have hcW : cW = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl
  set Xf : ℝ → ℝ → ℝ := Work.Spaces.mixed (b + 1 - b₁) a f with hXf
  set Zf : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hZf
  let Yf : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter b₁ A z θ
  have hYf : Yf = fun z θ => Work.Spaces.DzIter b₁ A z θ := rfl
  have hcWnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ cW z θ :=
    fun _ _ _ hθ hθ2 => Work.FTS.TransportS.SlotT2.canonW_nonneg ⟨hθ.le, hθ2.le⟩
  -- a.e. strong measurability of the five factors
  have haeX : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Xf p.1 p.2) PM := by
    rw [hXf]; exact aesm_mixed hdat.sm (b + 1 - b₁) a
  have haeZ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Zf p.1 p.2) PM := by
    rw [hZf]; exact aesm_mixed hdat.sm b a
  have haeW : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => cW p.1 p.2) PM :=
    aesm_canonW (Work.Spaces.gam α)
  have haeY : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Yf p.1 p.2) PM :=
    aesm_of_smoothOpen (hcoef.sm.DzIter b₁)
  have hmeasX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (Xf p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeX.mul haeX)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  have hmeasZ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeZ.mul haeZ)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  -- order bookkeeping
  have hordX6 : a + (b + 1 - b₁) ≤ 6 := by omega
  -- the `Z`-slot energy (independent of the case split)
  have hdomZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      cW z θ * (Zf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ _ hθ hθ2
    have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
      (q := Work.Spaces.gam α) (g := f) 6 le_rfl (z := z) (θ := θ) hθ hθ2
      (j := b) (i := a) ha hab
    simpa only [hcW, hZf] using h
  have hAZ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := cW) (X := Zf)
    hdat.sm hdat.h6 hcWnn hdomZ hmeasZ
  -- **the engine**: a sup bound on the coefficient slot and the two weighted `L²`-values
  have hmain : ∀ (KX AX AZ : ℝ), 0 ≤ KX → 0 ≤ AX → 0 ≤ AZ →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ| ≤ KX) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (Xf p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (Xf p.1 p.2) ^ 2 ∂PM) ≤ AX →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (Zf p.1 p.2) ^ 2 ∂PM) ≤ AZ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
          * Xf p.1 p.2 * Zf p.1 p.2) PM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2 * Zf p.1 p.2 ∂PM|
          ≤ KX * (Real.sqrt AX * Real.sqrt AZ) := by
    intro KX AX AZ hKX0 hAX0 hAZ0 hYsup hI1 hv1 hI2 hv2
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Xf z θ * Work.Spaces.DzIter b₁ A z θ * Zf z θ|
          ≤ KX * (Real.sqrt (cW z θ * (Xf z θ) ^ 2)
              * Real.sqrt (cW z θ * (Zf z θ) ^ 2)) := by
      intro z θ hz hθ hθ2
      have hρle : ρ z θ ≤ cW z θ := by
        rw [hcW]; exact leafW_le_canonW_gam hα0 hleaf z θ hz hθ hθ2
      have hρnn : 0 ≤ ρ z θ := leafW_nonneg hleaf z θ hz hθ hθ2
      have hcnn : 0 ≤ cW z θ := hcWnn z θ hz hθ hθ2
      have hY := hYsup z θ hz hθ hθ2
      have hroot : Real.sqrt (cW z θ) * Real.sqrt (cW z θ) = cW z θ := by
        have h := Real.sq_sqrt hcnn
        rwa [pow_two] at h
      have hkey : Real.sqrt (cW z θ * (Xf z θ) ^ 2) * Real.sqrt (cW z θ * (Zf z θ) ^ 2)
          = cW z θ * |Xf z θ| * |Zf z θ| := by
        rw [Real.sqrt_mul hcnn, Real.sqrt_mul hcnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
        conv_rhs => rw [← hroot]
        ring
      rw [hkey, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
      calc ρ z θ * |Xf z θ| * |Work.Spaces.DzIter b₁ A z θ| * |Zf z θ|
          ≤ cW z θ * |Xf z θ| * KX * |Zf z θ| := by gcongr
        _ = KX * (cW z θ * |Xf z θ| * |Zf z θ|) := by ring
    have hm1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (Xf p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasX
    have hm2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (Zf p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasZ
    obtain ⟨hInt, hbd⟩ := rowSummand_core (α := α) (KY := KX) (AX := AX) (AZ := AZ)
      (f := fun _ _ => (0 : ℝ)) (X := Xf) (Y := Yf) (Z := Zf)
      (ρv := ρ) (ρ₁ := cW) (ρ₂ := cW)
      hKX0 hAX0 hAZ0 (leafW_nonneg hleaf) hI1 hI2 hv1 hv2
      (ae_of_forall_Qd hcWnn) (ae_of_forall_Qd hcWnn) hm1 hm2
      (aesm_leafW hleaf) haeX haeY haeZ hpt
    have hswap : ∀ p : ℝ × ℝ, ρ p.1 p.2 * Xf p.1 p.2 * Yf p.1 p.2 * Zf p.1 p.2
        = ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2 * Zf p.1 p.2 := by
      intro p
      simp only [hYf]
      ring
    refine ⟨hInt.congr (Filter.Eventually.of_forall hswap), ?_⟩
    have heq : (∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2
          * Zf p.1 p.2 ∂PM)
        = ∫ p, ρ p.1 p.2 * Xf p.1 p.2 * Yf p.1 p.2 * Zf p.1 p.2 ∂PM :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => (hswap p).symm))
    rw [heq]
    exact hbd
  by_cases hb2 : b₁ ≤ 2
  · -- **Case `b₁ ≤ 2`**: the coefficient slot is bounded by `C α^{-1/2}(K0+K4)`
    have hsupA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ|
          ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      intro z θ hz hθ hθ2
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        have h1 : |A z θ| ≤ K0 := hcoef.val z θ hz hθ hθ2
        have h2 : (1 : ℝ) ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) := by
          have h3 : (1 : ℝ) ≤ Cdz * Real.sqrt 10 + 1 := by nlinarith [hCdz, hsq10]
          exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
            (mul_le_mul h3 hαinv1 (by norm_num) (by linarith))
        calc |Work.Spaces.DzIter 0 A z θ| = |A z θ| := by rw [Work.Spaces.DzIter_zero]
          _ ≤ K0 := h1
          _ ≤ 1 * (K0 + K4) := by rw [one_mul]; linarith
          _ ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_right h2 (by linarith)
      · have hdz1 := hdz α A hα0 hα1 hcoef.sm hcoef.h4 b₁ hb2 z θ hz hθ hθ2
        have hfac : Cdz / Real.sqrt (Work.Spaces.gam α - 1)
            = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
          have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα0.le]
          rw [Work.Spaces.gam_sub_one α, Real.sqrt_div hα0.le, div_div_eq_mul_div,
            div_eq_mul_inv, hinv]
        calc |Work.Spaces.DzIter b₁ A z θ|
            ≤ Cdz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := hdz1
          _ ≤ Cdz / Real.sqrt (Work.Spaces.gam α - 1) * K4 :=
              mul_le_mul_of_nonneg_left hcoef.n4 (div_nonneg hCdz.le (Real.sqrt_nonneg _))
          _ = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by rw [hfac]
          _ ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
              have hstep : Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
                  ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * K4 := by
                refine mul_le_mul_of_nonneg_right ?_ hK4
                exact mul_le_mul_of_nonneg_right (by linarith) hαinv0
              refine le_trans hstep ?_
              exact mul_le_mul_of_nonneg_left (by linarith)
                (mul_nonneg (by nlinarith [hCdz, hsq10]) hαinv0)
    have hdomX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (Xf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := f) 6 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b + 1 - b₁) (i := a) ha hordX6
      simpa only [hcW, hXf] using h
    have hAX := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := cW) (X := Xf)
      hdat.sm hdat.h6 hcWnn hdomX hmeasX
    obtain ⟨hIntA, hbdA⟩ := hmain ((Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
      (Work.Spaces.HkSq α 6 f) (Work.Spaces.HkSq α 6 f)
      (mul_nonneg (mul_nonneg (by nlinarith [hCdz, hsq10]) hαinv0)
        (by linarith : (0 : ℝ) ≤ K0 + K4)) hQ6 hQ6 hsupA hAX.1 hAX.2 hAZ.1 hAZ.2
    refine ⟨hIntA, ?_⟩
    have hsq : Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)
        = Work.Spaces.HkSq α 6 f := by
      rw [← pow_two]; exact Real.sq_sqrt hQ6
    rw [hsq] at hbdA
    refine le_trans hbdA ?_
    have hK04 : 0 ≤ K0 + K4 := by linarith
    have hmonoA : (K0 + K4) * Work.Spaces.HkSq α 6 f
        ≤ (K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f := by
      have h := mul_nonneg (mul_nonneg hM hK6) hN6
      linarith
    have hfac1 : (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
        ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      refine mul_le_mul_of_nonneg_right ?_ hK04
      exact mul_le_mul_of_nonneg_right (by linarith) hαinv0
    calc (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * Work.Spaces.HkSq α 6 f
        = ((Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := rfl
      _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_right hfac1 hQ6
      _ = ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hmonoA
            (mul_nonneg (by nlinarith [hCdz, hCsup, hsq10]) hαinv0)
      _ = (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by ring
  · -- **Case `3 ≤ b₁`**: the coefficient slot is bounded by `C α^{-1/2}K6`
    have h3 : 3 ≤ b₁ := by omega
    have hordX4 : a + (b + 1 - b₁) ≤ 4 := by omega
    have hsupB : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ| ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 := by
      intro z θ hz hθ hθ2
      have h1 := hsup α A hα0 hα1 hcoef.sm hcoef.h6 b₁ 0 (by omega) z θ hz hθ hθ2
      rw [Work.Spaces.mixed_zero_right] at h1
      calc |Work.Spaces.DzIter b₁ A z θ|
          ≤ Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A := h1
        _ ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 :=
            mul_le_mul_of_nonneg_left hcoef.n6 (mul_nonneg hCsup.le hαinv0)
    have hmem4 : Work.Spaces.HkMem α 4 f := HkMem_mono_le hdat.sm (by norm_num) hdat.h6
    have hdomX4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (Xf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := f) 4 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b + 1 - b₁) (i := a) ha hordX4
      simpa only [hcW, hXf] using h
    have hAX := val_le_HkSq (α := α) (k := 4) (f := f) (ρv := cW) (X := Xf)
      hdat.sm hmem4 hcWnn hdomX4 hmeasX
    obtain ⟨hIntB, hbdB⟩ := hmain (Csup * α ^ (-(1 / 2 : ℝ)) * K6) (Work.Spaces.HkSq α 4 f)
      (Work.Spaces.HkSq α 6 f) (mul_nonneg (mul_nonneg hCsup.le hαinv0) hK6) hQ4 hQ6
      hsupB hAX.1 hAX.2 hAZ.1 hAZ.2
    refine ⟨hIntB, ?_⟩
    have hstep : Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f)
        ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
          * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by
      have hC : Csup * α ^ (-(1 / 2 : ℝ))
          ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hCdz, hsq10]) hαinv0
      have hMKN : 0 ≤ M * K6 * Work.Spaces.HkNorm α 6 f := mul_nonneg (mul_nonneg hM hK6) hN6
      have hmonoB : M * K6 * Work.Spaces.HkNorm α 6 f
          ≤ (K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f := by
        have h := mul_nonneg (by linarith : (0 : ℝ) ≤ K0 + K4) hQ6
        linarith
      calc Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f)
          = (Csup * α ^ (-(1 / 2 : ℝ))) * (M * K6 * Work.Spaces.HkNorm α 6 f) := by ring
        _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
              * (M * K6 * Work.Spaces.HkNorm α 6 f) := mul_le_mul_of_nonneg_right hC hMKN
        _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left hmonoB
              (mul_nonneg (by nlinarith [hCdz, hCsup, hsq10]) hαinv0)
        _ = (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by
            ring
    refine le_trans hbdB ?_
    calc Csup * α ^ (-(1 / 2 : ℝ)) * K6
          * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        = Csup * α ^ (-(1 / 2 : ℝ)) * K6
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := rfl
      _ ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hCsup.le hαinv0) hK6)
          exact mul_le_mul hdat.bdd le_rfl hN6 hM
      _ ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := hstep

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
