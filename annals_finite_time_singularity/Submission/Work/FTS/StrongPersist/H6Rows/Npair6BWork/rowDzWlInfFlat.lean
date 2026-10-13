import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzTerms
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzRem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `rowDzWlInfFlat`

The flat per-slot bound for the `A · D_z f` row of the level-six pairing, with the coefficient
priced by `𝒲^{6,∞}` and the three flat bounds on `∂_θA`.  The proof is the Leibniz expansion
(`RowDzRem.rowDz_leib`), the per-term bound (`RowDzTerms.rowDz_term_bound`), the radial transport
term (`T6Gen.fluxSix_noDecay`) and the angular Hardy inequality (`T6Gen.qDzLe`).
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

theorem rowDzWlInfFlat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K M Kf : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ C * α ^ (-(4 : ℝ)) * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Ch, hChpos, hhardy⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
  obtain ⟨Cfl, hCflpos, hflux⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay
  obtain ⟨Cr, hCrpos, hrem⟩ := rowDz_rem_pt
  refine ⟨(1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12, by positivity, ?_⟩
  intro α hα A f K M Kf a b ρ hAsm hAwl hAK hdat hKf0 hKf1 hKf2 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have hf6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have hf7 : Work.Spaces.HkMem α 7 f := hdat.h7
  have hKnn : 0 ≤ K :=
    le_trans (Work.Spaces.WlInf_nonneg α 6 A hAwl) hAK
  have hKfnn : 0 ≤ Kf := le_trans (abs_nonneg _)
    (hKf0 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨q, hρeq, hq0, hqγ, hqη0⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  have hqcases : q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α := by
    rcases hleaf with h | h | ⟨_, h⟩
    · refine Or.inl (rowDz_canonW_eq_of hρeq ?_)
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1
    · refine Or.inr (Or.inl (rowDz_canonW_eq_of hρeq ?_))
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1
    · refine Or.inr (Or.inr (rowDz_canonW_eq_of hρeq ?_))
      rw [h]
      exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α
  rw [hρeq]
  -- ## the angular Hardy slot
  set pm : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hpm
  set HH : ℝ → ℝ → ℝ := fun z θ => ∑ k ∈ Finset.range 6,
      canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 with hHH
  have hHHnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ := by
    intro z θ hz hθ hθ2
    rw [hHH]
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩) (sq_nonneg _)
  have hHHdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
      canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ := by
    intro z θ hz hθ hθ2 k hk
    rw [hHH]
    refine Finset.single_le_sum (f := fun k => canonW (1 - α / 10) z θ
      * (Work.Spaces.DzIter k f z θ) ^ 2) (fun k hk' =>
      mul_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩) (sq_nonneg _)) ?_
    exact Finset.mem_range.mpr (by omega)
  have hHHint : MeasureTheory.Integrable (fun p : ℝ × ℝ => HH p.1 p.2) pm := by
    rw [hHH]
    exact MeasureTheory.integrable_finsetSum (Finset.range 6)
      (f := fun k => fun p : ℝ × ℝ =>
        canonW (1 - α / 10) p.1 p.2 * (Work.Spaces.DzIter k f p.1 p.2) ^ 2)
      (fun k hk => (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).1)
  have hHHval : (∫ p, HH p.1 p.2 ∂pm)
      ≤ 6 * (Ch * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) := by
    rw [hHH]
    rw [MeasureTheory.integral_finsetSum (Finset.range 6)
      (f := fun k => fun p : ℝ × ℝ =>
        canonW (1 - α / 10) p.1 p.2 * (Work.Spaces.DzIter k f p.1 p.2) ^ 2)
      (fun k hk => (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).1)]
    refine le_trans (Finset.sum_le_sum fun k hk =>
      (hhardy α hα f k hfsm hf6 (by have := Finset.mem_range.mp hk; omega)).2) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hIH0 : 0 ≤ ∫ p, HH p.1 p.2 ∂pm := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
    exact hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
  -- ## the pieces of the pairing
  set Z : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hZ
  set Uf : ℝ → ℝ → ℝ :=
    fun z θ => Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ with hUf
  set F : ℝ × ℝ → ℝ := fun p => canonW q p.1 p.2 * Uf p.1 p.2 * Z p.1 p.2 with hF
  set F0 : ℝ × ℝ → ℝ := fun p =>
    canonW q p.1 p.2 * A p.1 p.2 * Work.Spaces.Dz Z p.1 p.2 * Z p.1 p.2 with hF0
  set Fr : ℝ × ℝ → ℝ := fun p =>
    canonW q p.1 p.2 * (Uf p.1 p.2 - A p.1 p.2 * Work.Spaces.Dz Z p.1 p.2) * Z p.1 p.2 with hFr
  have hDZpt : ∀ z θ : ℝ, Work.Spaces.Dz Z z θ = Work.Spaces.mixed (b + 1) a f z θ := by
    intro z θ; rw [hZ]; rfl
  have hHki : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2) pm :=
    (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf6).1
  have hHki7 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 7 f p.1 p.2) pm :=
    (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf7).1
  -- ## integrability of the remainder
  have hZaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Z p.1 p.2) pm := by
    rw [hZ]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfsm b a)
  have hDZaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dz Z p.1 p.2) pm := by
    simp only [hDZpt]
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfsm (b + 1) a)
  have hAaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hAsm.continuousOn
  have hcanonAesm : AEStronglyMeasurable (fun p : ℝ × ℝ => canonW q p.1 p.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.TransportS.SlotT2.continuousOn_canonW q)
  have hUfaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Uf p.1 p.2) pm :=
    rowDz_Uf_aesm hAsm hfsm a b
  have hmaj_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Cr * (1 + K + Kf) * (HH p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) pm :=
    ((hHHint.add hHki).const_mul (Cr * (1 + K + Kf)))
  have hFr_int : MeasureTheory.Integrable Fr pm := by
    refine MeasureTheory.Integrable.mono' hmaj_int ?_ ?_
    · exact (hcanonAesm.mul (hUfaesm.sub (hAaesm.mul hDZaesm))).mul hZaesm
    · filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs, hFr]
      have h := hrem α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0
        hqγ hqη0 hqcases hHHdom hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
      simp only [hUf, hZ]
      exact h
  -- ## integrability of the transport piece
  have hF0_pt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F0 (z, θ)| ≤ K * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    intro z θ hz hθ hθ2
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
    have hσ : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos hθI)
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩
    have hAg : canonW q z θ * |A z θ| ≤ K * canonW q z θ := by
      calc canonW q z θ * |A z θ| ≤ canonW q z θ * K :=
            mul_le_mul_of_nonneg_left (rowDz_A_le hAwl hAK z θ hz hθ hθ2) hcw
        _ = K * canonW q z θ := by ring
    have h2 : canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ| * |Z z θ|
        ≤ K * (canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2 + canonW q z θ * (Z z θ) ^ 2) := by
      have h1 : canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ|
          ≤ K * (canonW q z θ * |Work.Spaces.Dz Z z θ|) := by
        calc canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ|
            ≤ (K * canonW q z θ) * |Work.Spaces.Dz Z z θ| :=
              mul_le_mul_of_nonneg_right hAg (abs_nonneg _)
          _ = K * (canonW q z θ * |Work.Spaces.Dz Z z θ|) := by ring
      calc canonW q z θ * |A z θ| * |Work.Spaces.Dz Z z θ| * |Z z θ|
          ≤ (K * (canonW q z θ * |Work.Spaces.Dz Z z θ|)) * |Z z θ| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = K * (canonW q z θ * |Work.Spaces.Dz Z z θ| * |Z z θ|) := by ring
        _ ≤ K * (canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2 + canonW q z θ * (Z z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left (rowDz_canonW_abs_mul_le hσ _ _) hKnn
    rw [hF0, abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]
    refine le_trans h2 ?_
    have h3 : canonW q z θ * (Work.Spaces.Dz Z z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
      simp only [hDZpt]
      exact rowDz_DZ_maj hqγ hqη0 hab z θ hz hθ hθ2
    have h4 : canonW q z θ * (Z z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      rw [hZ]
      exact rowDz_Z_maj hqγ hqη0 hab z θ hz hθ hθ2
    exact mul_le_mul_of_nonneg_left (add_le_add h3 h4) hKnn
  have hF0_int : MeasureTheory.Integrable F0 pm := by
    have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        K * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
          + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) pm :=
      ((hHki7.add hHki).const_mul K)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine AEStronglyMeasurable.congr
        (((hcanonAesm.mul hAaesm).mul hDZaesm).mul hZaesm) ?_
      filter_upwards with p
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs]
      exact hF0_pt p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hF_int : MeasureTheory.Integrable F pm := by
    have hsplit : F =ᵐ[pm] fun p => F0 p + Fr p := by
      filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      show F p = F0 p + Fr p
      rw [hF, hF0, hFr]
      ring
    exact (hF0_int.add hFr_int).congr hsplit.symm
  -- ## Fubini
  have hFub : Work.FTS.TransportS.slotPairing (canonW q) a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f = ∫ p, F p ∂pm := by
    rw [Work.FTS.TransportS.slotPairing]
    exact MeasureTheory.integral_integral hF_int
  -- ## the two integral bounds
  have hflux0 : |∫ p, F0 p ∂pm| ≤ Cfl * K * Work.Spaces.HkSq α 6 f := by
    have hfab : (∫ p, F0 p ∂pm)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F0 (z, θ) := by
      have h := MeasureTheory.integral_integral
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun z θ => F0 (z, θ)) hF0_int
      rw [hpm]
      exact h.symm
    have hfab2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F0 (z, θ))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * A z θ * Work.Spaces.Dz (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hF0, hZ]
    rw [hfab, hfab2]
    exact hflux α A f a b q K hα0 hα1 hq0 hqγ hqη0 hab hAsm hfsm hf6 hf7
      (fun z θ hz hθ hθ2 => rowDz_A_le hAwl hAK z θ hz hθ hθ2)
      (fun z θ hz hθ hθ2 => rowDz_DzA_le hAwl hAK z θ hz hθ hθ2)
  have hFr_bd : |∫ p, Fr p ∂pm| ≤ Cr * (1 + K + Kf)
      * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)) := by
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    have hmono : (∫ p, ‖Fr p‖ ∂pm)
        ≤ ∫ p, Cr * (1 + K + Kf)
            * (HH p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2) ∂pm := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => norm_nonneg _) hmaj_int ?_
      filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
      rw [Real.norm_eq_abs, hFr]
      have h := hrem α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0
        hqγ hqη0 hqcases hHHdom hHHnn p.1 p.2 hp.1 hp.2.1 hp.2.2
      simp only [hUf, hZ]
      exact h
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hHHint hHki,
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hfsm hf6).2]
    ring_nf
    exact le_refl _
  -- ## the final estimate
  have hfinal : Cfl * K * Work.Spaces.HkSq α 6 f
      + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
      ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
        * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have hα4 : (1 : ℝ) ≤ α ^ (-(4 : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ 0 by norm_num)
    have hα24 : α ^ (-(2 : ℝ)) ≤ α ^ (-(4 : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ -(2 : ℝ) by norm_num)
    have hS : 0 ≤ Work.Spaces.HkSq α 6 f := hSq0
    have hA4 : 0 ≤ α ^ (-(4 : ℝ)) := Real.rpow_nonneg hα0.le _
    -- ### the Hardy slot: `S + ∫HH ≤ (1+6Ch) α^{-4} (1+S)`
    have h2 : Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)
        ≤ (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
      have h := hHHval
      have h6 : 6 * (Ch * α ^ (-(2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f))
          ≤ 6 * (Ch * α ^ (-(4 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hα24 hChpos.le) (by linarith)
      nlinarith [h, h6, hS, hIH0, hChpos.le, hα4]
    -- ### the coefficient comparison
    have hc : Cfl + Cr * (1 + 6 * Ch) ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 := by
      have h1 : Cr * (1 + 6 * Ch) ≤ 7 * (1 + Cr) * (1 + Ch) := by nlinarith
      have h2 : Cfl + 7 * (1 + Cr) * (1 + Ch) ≤ 8 * (1 + Cfl) * (1 + Ch) * (1 + Cr) := by
        have hCh0 : 0 ≤ Ch := hChpos.le
        have hCr0 : 0 ≤ Cr := hCrpos.le
        have hCC : 0 ≤ Ch * Cr := mul_nonneg hCh0 hCr0
        have h6 : 1 ≤ (1 + Ch) * (1 + Cr) := by nlinarith [hCh0, hCr0, hCC]
        have h60 : 0 ≤ (1 + Ch) * (1 + Cr) := mul_nonneg (by linarith) (by linarith)
        have hA : Cfl * 1 ≤ Cfl * ((1 + Ch) * (1 + Cr)) :=
          mul_le_mul_of_nonneg_left h6 hCflpos.le
        have hA' : Cfl ≤ Cfl * ((1 + Ch) * (1 + Cr)) := by simpa using hA
        have hB : Cfl + 7 ≤ 8 * (1 + Cfl) := by linarith [hCflpos.le]
        calc Cfl + 7 * (1 + Cr) * (1 + Ch)
            = Cfl + 7 * ((1 + Ch) * (1 + Cr)) := by ring
          _ ≤ Cfl * ((1 + Ch) * (1 + Cr)) + 7 * ((1 + Ch) * (1 + Cr)) := by linarith [hA']
          _ = (Cfl + 7) * ((1 + Ch) * (1 + Cr)) := by ring
          _ ≤ (8 * (1 + Cfl)) * ((1 + Ch) * (1 + Cr)) :=
              mul_le_mul_of_nonneg_right hB h60
          _ = 8 * (1 + Cfl) * (1 + Ch) * (1 + Cr) := by ring
      have h3 : (8 : ℝ) * (1 + Cfl) * (1 + Ch) * (1 + Cr)
          ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 := by
        have h4 : 0 ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) := by positivity
        nlinarith
      linarith [h1, h2, h3]
    have hcc : Cr * (1 + 6 * Ch) ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 :=
      le_trans (by nlinarith [hCflpos.le]) hc
    have hc0 : 0 ≤ Cfl + Cr * (1 + 6 * Ch) := by nlinarith [hCflpos.le, hCrpos.le, hChpos.le]
    have hk : K ≤ α ^ (-(4 : ℝ)) * (1 + K + Kf) := by nlinarith [hKnn, hKfnn, hα4]
    have hA : Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
        ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by
      have ha : Cfl * K ≤ Cfl * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) :=
        mul_le_mul_of_nonneg_left hk hCflpos.le
      have hb : Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
          = Cr * (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by ring
      calc Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
          ≤ Cfl * (α ^ (-(4 : ℝ)) * (1 + K + Kf))
              + Cr * (1 + 6 * Ch) * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by
            rw [hb]; exact add_le_add ha le_rfl
        _ = (Cfl + Cr * (1 + 6 * Ch)) * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) := by ring
        _ ≤ ((1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12) * (α ^ (-(4 : ℝ)) * (1 + K + Kf)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf) := by ring
    have hB : (1 + Work.Spaces.HkSq α 6 f)
        ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by nlinarith [hM0, hS]
    have hpart1 : Cfl * K * Work.Spaces.HkSq α 6 f
        ≤ Cfl * K * (1 + Work.Spaces.HkSq α 6 f) := by
      nlinarith [hS, mul_nonneg hCflpos.le hKnn]
    have hpart2 : Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
            * (1 + Work.Spaces.HkSq α 6 f) := by
      have hc' : 0 ≤ Cr * (1 + K + Kf) := by nlinarith [hCrpos.le, hKnn, hKfnn]
      have h := mul_le_mul_of_nonneg_left h2 hc'
      simpa only [mul_assoc] using h
    have hS1 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    have hK1 : 0 ≤ 1 + K + Kf := by linarith
    have hmid : Cfl * K * Work.Spaces.HkSq α 6 f
          + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f) := by
      have hrn : (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f)
          = Cfl * K * (1 + Work.Spaces.HkSq α 6 f)
            + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ)))
              * (1 + Work.Spaces.HkSq α 6 f) := by ring
      rw [hrn]
      exact add_le_add hpart1 hpart2
    calc Cfl * K * Work.Spaces.HkSq α 6 f
          + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm))
        ≤ (Cfl * K + Cr * (1 + K + Kf) * ((1 + 6 * Ch) * α ^ (-(4 : ℝ))))
            * (1 + Work.Spaces.HkSq α 6 f) := hmid
      _ ≤ ((1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ)) * (1 + K + Kf))
            * ((1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul hA hB hS1 (by positivity)
      _ = (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
            * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring

  calc |Work.FTS.TransportS.slotPairing (canonW q) a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
      = |∫ p, F p ∂pm| := by rw [hFub]
    _ = |∫ p, (F0 p + Fr p) ∂pm| := by
        rw [MeasureTheory.integral_congr_ae (by
          filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
          show F p = F0 p + Fr p
          rw [hF, hF0, hFr]; ring)]
    _ = |∫ p, F0 p ∂pm + ∫ p, Fr p ∂pm| := by
        rw [MeasureTheory.integral_add hF0_int hFr_int]
    _ ≤ |∫ p, F0 p ∂pm| + |∫ p, Fr p ∂pm| := abs_add_le _ _
    _ ≤ Cfl * K * Work.Spaces.HkSq α 6 f
        + Cr * (1 + K + Kf) * (Work.Spaces.HkSq α 6 f + (∫ p, HH p.1 p.2 ∂pm)) :=
        add_le_add hflux0 hFr_bd
    _ ≤ (1 + Cfl) * (1 + Ch) * (1 + Cr) * 10 ^ 12 * α ^ (-(4 : ℝ))
        * (1 + K + Kf) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := hfinal

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
