import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_theta_uniform
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.mixed_T_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.SupPort

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The pointwise identity behind the mixed-slot energy: on `Iθ`, the square of the weighted
mixed slot is the angular weight `sin(2θ)^{-γ}` times the square of the unweighted mixed slot
against `w²`. -/
theorem mixed_Wt_sq_eq_fts (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) {s θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed j i f s θ * Work.Spaces.Wt α s θ) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_mul (sin_two_nonneg_Iθ_fts hθ) (-(Work.Spaces.gam α / 2)) 2]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsq]
  ring

theorem mixed_T_le_HkSq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) :
    MeasureTheory.IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ
    ∧ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hi : 1 ≤ a + 1 := by omega
  have hij : (a + 1) + (b + 1) ≤ 4 := by omega
  -- The weighted mixed slot, as a function of `(z,θ)`, is product-integrable.
  have hΦint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (b + 1) (a + 1) f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
      hF hmem (b + 1) (a + 1) hi hij
  -- Tonelli for the `ℋ⁴`-integrand of an open-class datum.
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- The angular partial integral of the slot is integrable.
  have hΦθ : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hΦint.integral_prod_right
  -- Pointwise domination and monotonicity of the inner integral.
  have hmono : (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2))
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => MeasureTheory.integral_nonneg fun z => sq_nonneg _)
      hGint ?_
    filter_upwards [hGslice] with θ hθint
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => sq_nonneg _) hθint
      (Filter.Eventually.of_forall fun z =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (a + 1) (b + 1) hi hij)
  -- The two descriptions of the angular integrand agree on `Iθ`.
  have hae : (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc) fun θ hθ => ?_
    show (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
    have hcast : (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((Work.Spaces.mixed (b + 1) (a + 1) f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun z => mixed_Wt_sq_eq_fts α f (b + 1) (a + 1) hθ)
    rw [hcast, MeasureTheory.integral_const_mul]
  refine ⟨hΦθ.congr hae.symm, ?_⟩
  calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2) :=
        MeasureTheory.integral_congr_ae hae
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := hmono
    _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS.StrongEps.SupPort
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.sliceBoundSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

/-- The mixed slot with a general angular weight and a general order `k`:
for `c ≤ γ`, `1 ≤ i` and `i + j ≤ k`,
`(D_z^jD_θ^i f z θ)² · w(z)² · sin(2θ)^{-c} ≤ HkIntegrand α k f z θ`.

This is the level-`k` generalisation of `Work.FTS.TransportS.mixed_sq_w_rpow_le_HkIntegrand`
(which is stated at `k = 4`); the proof is verbatim the same, since
`Work.Spaces.sq_le_HkIntegrand_mixed` is already available at an arbitrary order `k`. -/
theorem mixed_sq_w_rpow_le_HkIntegrand_gen (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ c : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (hc : c ≤ Work.Spaces.gam α) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c) ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have h1 : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α k f z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
    have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have hw : Work.Spaces.Wt α z θ
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
      have hs2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [sq, ← Real.rpow_add hsin,
          show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
            = -(Work.Spaces.gam α) by ring]
      rw [hw, mul_pow, mul_pow, hs2]
      ring
    rwa [h2] at h
  have h3 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have hs1 : Real.sin (2 * θ) ^ Work.Spaces.gam α ≤ Real.sin (2 * θ) ^ c :=
      Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ)) hc
    rw [Real.rpow_neg (le_of_lt hsin) c, Real.rpow_neg (le_of_lt hsin) (Work.Spaces.gam α),
      ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hsin (Work.Spaces.gam α)) hs1
  calc (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c)
      ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := h1


end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SupB2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. The angular shift identity for mixed slots -/

/-- `sin(2θ) · ∂_θ(D_z^jD_θ^i f) = D_z^jD_θ^{i+1} f` on the open quadrant, for a datum which is
`C^∞` there.  (The `D_θ`-iterate form of `Work.FTS.TransportS.mixed_one_eq_sin_mul_pth`.) -/
theorem sin_mul_pth_mixed {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DthIter i f)).mp
        (hF.DthIter i)) j hp
  have h3 : Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ
      = Work.Spaces.DzIter j
          (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter i f) z θ')
          z θ :=
    (Work.FTS.TransportS.DzIter_const_mul j (fun θ' => Real.sin (2 * θ'))
      (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ).symm
  calc Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) z θ := rfl
    _ = Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i f)) z θ := by rw [h2]
    _ = Work.Spaces.DzIter j
          (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter i f) z θ')
          z θ := h3
    _ = Work.Spaces.mixed j (i + 1) f z θ := rfl

/-! ## 2. Integrability of the two weighted angular slices -/

/-- For `z > 0`, the `(j,i)` mixed slot with its own weight `sin(2θ)^{-γ}` is `θ`-integrable
on `Iθ`, as soon as the slot belongs to `HkIntegrand α 4 f`.  (The transfer from
`Work.FTS.EllipticEst.integrableOn_mixedSummand`, whose integrand carries the weight `Wt`.) -/
theorem integrableOn_mixed_sq_rpow {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hbase := Work.FTS.EllipticEst.integrableOn_mixedSummand α 4 hF hmem i j hi hij
    (z := z) (Set.mem_Ici.mpr (le_of_lt hz))
  have hw : (Work.Spaces.w z) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.FTS.TransportS.one_le_w hz))
  have hae : (fun t => (Work.Spaces.mixed j i f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun t => (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
    show (Work.Spaces.mixed j i f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed j i f z t * Work.Spaces.Wt α z t) ^ 2
        * ((Work.Spaces.w z) ^ 2)⁻¹
    have hs : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 hw
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z t hs]
    field_simp
  exact (hbase.mul_const _).congr hae.symm

/-- For `z > 0`, the `∂_θ`-slice of a mixed slot with the weight `sin(2θ)^{2-γ}` is
`θ`-integrable: it equals the next slot `(j,i+1)` with the weight `sin(2θ)^{-γ}`. -/
theorem integrableOn_pth_sq_rpow {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hij : i + j ≤ 3) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t => (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  refine (integrableOn_mixed_sq_rpow hF hmem j (i + 1) (by omega) (by omega) hz).congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
  show (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
  have hs : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hsplit : (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * t)) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α
        = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hs, Real.rpow_two]
  rw [← sin_mul_pth_mixed hF j i hz ht, hsplit]
  ring

/-- The integral identity behind the previous lemma: the `∂_θ`-slot with the weight
`sin(2θ)^{2-γ}` integrates to the next mixed slot with the weight `sin(2θ)^{-γ}`. -/
theorem setIntegral_pth_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ t in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))
      = ∫ t in Work.Spaces.Iθ, (Work.Spaces.mixed j (i + 1) f z t) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
  refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun t ht => ?_)
  show (Work.Spaces.pth (Work.Spaces.mixed j i f) z t) ^ 2
        * (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
  have hs : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hsplit : (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * t)) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α
        = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hs, Real.rpow_two]
  rw [← sin_mul_pth_mixed hF j i hz ht, hsplit]
  ring

/-! ## 3. The pointwise bound -/

theorem mixed_pointwise_le_Xn :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed j i f z θ| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨Real.sqrt 15, Real.sqrt_pos_of_pos (by norm_num), ?_⟩
  intro α f hα hα1 hF hmem j i hi hij z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ, hθ2⟩
  set R : ℝ := max z 2 with hRdef
  have hzR : z ≤ R := le_max_left z 2
  have hR2 : (2 : ℝ) ≤ R := le_max_right z 2
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR2
  have hz2R : z ≤ 2 * R := by linarith
  have hR2R : R ≤ 2 * R := by linarith
  have hHknn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- hypotheses of the radial window bound
  have hderiv : ∀ x ∈ Set.Icc z (2 * R),
      HasDerivAt (fun x => Work.Spaces.mixed j i f x θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i f) x θ) x :=
    fun x hx => (hF.mixed j i).hasDerivAt_slice hθI (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x => Work.Spaces.mixed j i f x θ) (Set.Icc R (2 * R)) :=
    ((hF.mixed j i).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed j i).pz).curry_z hθI).continuousOn.mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : IntegrableOn (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      (Set.Icc R (2 * R)) := (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hzR hderiv hcont hcont' hint
  have hwin' : (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ 2 * (∫ x in z..(2 * R),
            (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ * Work.Spaces.w x) ^ 2)
        + (2 / R) * ∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2 := hwin
  -- the weighted-derivative term
  have hwcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc z (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc z (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hmcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed (j + 1) i f x θ)
      (Set.Icc z (2 * R)) :=
    (((hF.mixed (j + 1) i).curry_z hθI).continuousOn).mono
      (fun x hx => lt_of_lt_of_le hz hx.1)
  have hIntL1 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
      volume z (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
      (Set.uIcc z (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact (hmcont1.mul hwcont1).pow 2
  have hIntR1 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ')
      volume z (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f x θ') (Set.uIcc z (2 * R)) volume from by
      rw [Set.uIcc_of_le hz2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz hx.1))).const_mul
        5).intervalIntegrable
  have hpt1 : ∀ x ∈ Set.Icc z (2 * R),
      (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
    have h := slice_bound hα hα1 hF hmem (j := j + 1) (i := i) hi (by omega) hx0 hθI
    have h2 : (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2
        = (Work.Spaces.mixed (j + 1) i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by ring
    rw [h2]; exact h
  have hmono1 : (∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ
        * Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in z..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hpt1
  have hbig1 : (∫ x in z..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [intervalIntegral.integral_of_le hz2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 4 f x θ'
    · exact le_of_lt (lt_trans hz hx.1)
  have hcongr1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2)
      = ∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rfl
  have hstep1 : (∫ x in z..(2 * R), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        * Work.Spaces.w x) ^ 2) ≤ 5 * Work.Spaces.HkSq α 4 f := by
    rw [hcongr1]
    calc (∫ x in z..(2 * R), (Work.Spaces.mixed (j + 1) i f x θ * Work.Spaces.w x) ^ 2)
        ≤ 5 * ∫ x in z..(2 * R),
            (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := hmono1
      _ ≤ 5 * Work.Spaces.HkSq α 4 f := by linarith
  -- the window average term
  have hIntL2 : IntervalIntegrable (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn (fun x => (Work.Spaces.mixed j i f x θ) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcont.pow 2
  have hwcont2 : ContinuousOn (fun x : ℝ => Work.Spaces.w x) (Set.Icc R (2 * R)) := by
    change ContinuousOn (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) (Set.Icc R (2 * R))
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hRpos hx.1))
  have hIntM2 : IntervalIntegrable
      (fun x => (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      volume R (2 * R) := by
    refine (show ContinuousOn
      (fun x => (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      (Set.uIcc R (2 * R)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact (hcont.pow 2).mul (hwcont2.pow 2)
  have hIntR2 : IntervalIntegrable
      (fun x => 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ')
      volume R (2 * R) :=
    (show IntegrableOn (fun x => 5 * ∫ θ' in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f x θ') (Set.uIcc R (2 * R)) volume from by
      rw [Set.uIcc_of_le hR2R]
      exact (hmem.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hRpos hx.1))).const_mul
        5).intervalIntegrable
  have hpt2a : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed j i f x θ) ^ 2
        ≤ (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    have h1 : 1 ≤ (Work.Spaces.w x) ^ 2 :=
      one_le_pow₀ (Work.FTS.TransportS.one_le_w hx0)
    nlinarith [sq_nonneg (Work.Spaces.mixed j i f x θ)]
  have hpt2b : ∀ x ∈ Set.Icc R (2 * R),
      (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2
        ≤ 5 * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ' := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact slice_bound hα hα1 hF hmem (j := j) (i := i) hi (by omega) hx0 hθI
  have hmono2a : (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ ∫ x in R..(2 * R),
          (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 :=
    intervalIntegral.integral_mono_on hR2R hIntL2 hIntM2 hpt2a
  have hmono2b : (∫ x in R..(2 * R),
        (Work.Spaces.mixed j i f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)
      ≤ 5 * ∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hR2R hIntM2 hIntR2 hpt2b
  have hbig2 : (∫ x in R..(2 * R),
        (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [intervalIntegral.integral_of_le hR2R]
    refine setIntegral_mono_set hmem.2 (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x hx => ?_)
    · exact integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 4 f x θ'
    · exact le_of_lt (lt_trans hRpos hx.1)
  have hstep2 : (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ 5 * Work.Spaces.HkSq α 4 f := by
    have h1 : 5 * (∫ x in R..(2 * R),
          (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x θ'))
        ≤ 5 * Work.Spaces.HkSq α 4 f := by linarith
    linarith [hmono2a, hmono2b, h1]
  -- conclusion
  have hYnn : 0 ≤ ∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2 :=
    intervalIntegral.integral_nonneg hR2R fun x _ => sq_nonneg _
  have hcoef : 2 / R ≤ 1 := by
    rw [div_le_one hRpos]; linarith
  have hcoef2 : (2 / R) * (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2)
      ≤ (∫ x in R..(2 * R), (Work.Spaces.mixed j i f x θ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hcoef hYnn
    rwa [one_mul] at h
  have hfinal : (Work.Spaces.mixed j i f z θ) ^ 2 ≤ 15 * Work.Spaces.HkSq α 4 f := by
    linarith [hwin', hcoef2, hstep1, hstep2]
  calc |Work.Spaces.mixed j i f z θ| = Real.sqrt ((Work.Spaces.mixed j i f z θ) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (15 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt 15 * Real.sqrt (Work.Spaces.HkSq α 4 f) := Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 15 * Work.FTS.Nonlin.Xn α f := by
        rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]

end Work.FTS.TransportS.T2SupB2
end
end
