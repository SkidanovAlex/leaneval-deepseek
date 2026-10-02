import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.exists_Rch_prime
import Submission.Work.PARIMPL2.Lavaurs.orbit_chart
import Submission.Work.PARIMPL2.Lavaurs.L0_symmetry
import Submission.Work.PARIMPL2.Lavaurs.approxEcal_step_rot_unif
import Submission.Work.PARIMPL2.Lavaurs.approxEcal_transit_rot_unif
import Submission.Work.PARIMPL2.Lavaurs.exists_log_mul_le
import Submission.Work.PARIMPL2.Lavaurs.exists_rho_direct
import Submission.Work.PARIMPL2.Direct.sinh_chart_norm
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_le_max
import Submission.Work.PARIMPL2.Direct.ecalPt_re_pos
import Submission.Work.PARIMPL2.Direct.approxEcal_re_level
import Submission.Work.PARIMPL2.Direct.im_kappa_le_quarter
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.modelTransit
import Submission.Work.PARIMPL2.Direct.sin_two_mul_pos_of_ecalPt_re_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

variable {c₀ : ℂ}

/-! ## Transport between the parameter chart and the model coordinates -/

private lemma chartZeta_m_add_s {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ P.ρ₀) (v : ℂ) :
    Work.PARIMPL.chartZeta P c (P.m c + P.s c * v) = v := by
  have hs : P.s c ≠ 0 := P.s_ne c hc
  simp only [Work.PARIMPL.chartZeta]
  field_simp
  ring

private lemma m_add_s_chartZeta {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ P.ρ₀) (z : ℂ) :
    P.m c + P.s c * Work.PARIMPL.chartZeta P c z = z := by
  have hs : P.s c ≠ 0 := P.s_ne c hc
  simp only [Work.PARIMPL.chartZeta]
  field_simp
  ring

private lemma chartZeta_eq_ecalPt_ecalUin {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) {c : ℂ} (hlam : 0 < P.lam c)
    (ha : P.a c = (P.lam c : ℂ) * Complex.I) (z : ℂ)
    (h1 : Work.PARIMPL.chartZeta P c z ≠ P.a c) (h2 : Work.PARIMPL.chartZeta P c z ≠ -P.a c) :
    Work.PARIMPL.chartZeta P c z = Work.Implosion.ecalPt (P.a c) (Work.PARIMPL.ecalUin P c z) := by
  have hane : P.a c ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  rw [Work.PARIMPL.ecalUin, Work.PARIMPL.ecalU]
  rw [Work.Implosion.ecalPt_add_period (P.a c) _ hane]
  exact (Work.Implosion.ecalPt_ecalCoord (P.a c) (Work.PARIMPL.chartZeta P c z) hane h1 h2).symm

private lemma branch_aux (lam : ℝ) (hlam : 0 < lam) (w : ℂ) :
    lam * (((Complex.log w) / (2 * ((lam : ℂ) * Complex.I))).re + Real.pi / lam) - Real.pi
      = (Complex.log w).im / 2 := by
  have h2a : (2 * ((lam : ℂ) * Complex.I)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have h2b : (2 * ((lam : ℂ) * Complex.I)).im = 2 * lam := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  have h2n : Complex.normSq (2 * ((lam : ℂ) * Complex.I)) = 4 * lam ^ 2 := by
    rw [Complex.normSq_apply, h2a, h2b]; ring
  have hdiv : ((Complex.log w) / (2 * ((lam : ℂ) * Complex.I))).re
      = (Complex.log w).im / (2 * lam) := by
    rw [Complex.div_re, h2a, h2b, h2n]
    field_simp
    ring
  rw [hdiv]
  field_simp
  ring

private lemma ecalUin_branch {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {c : ℂ} (hlam : 0 < P.lam c) (ha : P.a c = (P.lam c : ℂ) * Complex.I) (z : ℂ) :
    -(Real.pi / 2) < P.lam c * (Work.PARIMPL.ecalUin P c z).re - Real.pi ∧
      P.lam c * (Work.PARIMPL.ecalUin P c z).re - Real.pi ≤ Real.pi / 2 := by
  have hdivre : (Real.pi * Complex.I / P.a c).re = Real.pi / P.lam c := by
    rw [ha, Complex.div_re]
    have h1 : (Real.pi * Complex.I : ℂ).re = 0 := by simp
    have h2 : (Real.pi * Complex.I : ℂ).im = Real.pi := by simp
    have h3 : (((P.lam c : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
    have h4 : (((P.lam c : ℂ) * Complex.I)).im = P.lam c := by simp [Complex.mul_im]
    have h5 : Complex.normSq (((P.lam c : ℂ) * Complex.I)) = P.lam c ^ 2 := by
      rw [Complex.normSq_apply, h3, h4]; ring
    rw [h1, h2, h3, h4, h5]
    field_simp
    ring
  have hmain : P.lam c * (Work.PARIMPL.ecalUin P c z).re - Real.pi
      = (Complex.log (Work.Implosion.mobius (P.a c) (Work.PARIMPL.chartZeta P c z))).im / 2 := by
    rw [Work.PARIMPL.ecalUin, Work.PARIMPL.ecalU, Work.Implosion.ecalCoord, Complex.add_re,
      hdivre, ha]
    exact branch_aux (P.lam c) hlam
      (Work.Implosion.mobius ((P.lam c : ℂ) * Complex.I) (Work.PARIMPL.chartZeta P c z))
  rw [hmain]
  have h1 := Complex.neg_pi_lt_log_im
    (Work.Implosion.mobius (P.a c) (Work.PARIMPL.chartZeta P c z))
  have h2 := Complex.log_im_le_pi
    (Work.Implosion.mobius (P.a c) (Work.PARIMPL.chartZeta P c z))
  constructor <;> linarith

private lemma ecalU_m_add_s_ecalPt {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ P.ρ₀) (hlam : 0 < P.lam c)
    (ha : P.a c = (P.lam c : ℂ) * Complex.I) (v : ℂ)
    (h1 : 0 < (2 * (P.a c) * v).im) (h2 : (2 * (P.a c) * v).im ≤ Real.pi) :
    Work.PARIMPL.ecalU P c (P.m c + P.s c * Work.Implosion.ecalPt (P.a c) v) = v := by
  have hane : P.a c ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hζ : Work.PARIMPL.chartZeta P c (P.m c + P.s c * Work.Implosion.ecalPt (P.a c) v)
      = Work.Implosion.ecalPt (P.a c) v := by
    have hs : P.s c ≠ 0 := P.s_ne c hc
    simp only [Work.PARIMPL.chartZeta]
    field_simp
    ring
  have hEne : Work.Implosion.ecalE (P.a c) v ≠ 1 := by
    intro hE
    have hmem : v ∈ Work.Implosion.periodLattice (P.a c) := hE
    rw [Work.Implosion.mem_periodLattice_iff _ _ hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hcom : 2 * (P.a c) * v = 2 * (n : ℂ) * Real.pi * Complex.I := by
      rw [hn]; field_simp
    have him : (2 * (P.a c) * v).im = 2 * (n : ℝ) * Real.pi := by
      rw [hcom]; simp
    rw [him] at h1 h2
    have hpi := Real.pi_pos
    have hnpos : (0:ℝ) < (n:ℝ) := by nlinarith [hpi, h1]
    have hz : (0:ℤ) < n := by exact_mod_cast hnpos
    have h2z : (1:ℤ) ≤ n := Int.lt_iff_add_one_le.mp hz
    have h2r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2z
    nlinarith [hpi, h2r]
  rw [Work.PARIMPL.ecalU, hζ]
  exact Work.Implosion.Ecalle.ecalCoord_ecalPt (P.a c) v hane hEne (by linarith) h2

/-! ## The transit -/

/-- **THE TRANSIT, direct form** (`NOTES_LEAD_mandelbar_implosion.md` §3.5, L3): the same
statement as `Work.PARIMPL2.Lavaurs.transit_exit`, but *without* the model-transit interface
`Work.PARIMPL2.Lavaurs.transit_model` in its imports, so that the whole analytic argument is
inlined in one file (the model transit's statement was refuted three times in its
"hypotheses from the outside" form; see `Lavaurs/NOTES_FALSE_transit_model*.md`, and the lead's
calibration decision that the germ constants are fixed while `R` is chosen with
`log(1/λ) ≪ R ≪ 1/λ`).

The proof is assembled from `Work.PARIMPL2.Direct.modelTransit` (the analytic core, in model
coordinates), `Work.PARIMPL2.Lavaurs.exists_rho_direct` (the choice of the parameter ball),
`Work.PARIMPL2.Lavaurs.orbit_chart` and the transport lemmas above. -/
theorem transit_exit_direct {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (H : ℝ) (Rch : ℝ) (hRch : 4 ≤ Rch) (hRchOK : ∀ R ≥ Rch, Work.PARIMPL2.RchOK' P R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R ≥ max Rch (8 * (H + 2)), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ,
        (Work.PARIMPL.approxUin P c z).re ∈
          Set.Icc (Real.pi / P.lam c - R - 2) (Real.pi / P.lam c - R) →
        |(Work.PARIMPL.approxUin P c z).im| ≤ H → (Work.PARIMPL.chartZeta P c z).re < 0 →
        ‖Work.PARIMPL.chartZeta P c z‖ ≤ 4 / R →
        ∃ k : ℕ, (Work.PARIMPL.approxU P c ((Work.PARIMPL.Ft c)^[k] z)).re ∈ Set.Icc R (R + 2) ∧
          0 < (Work.PARIMPL.chartZeta P c ((Work.PARIMPL.Ft c)^[k] z)).re ∧
          ‖Work.PARIMPL.chartZeta P c ((Work.PARIMPL.Ft c)^[k] z)‖ ≤ 4 / R ∧
          ‖Work.PARIMPL.approxU P c ((Work.PARIMPL.Ft c)^[k] z) -
            (Work.PARIMPL.approxUin P c z - (k : ℂ))‖ ≤ C / R := by
  obtain ⟨C, hC0, hMT⟩ :=
    Work.PARIMPL2.Direct.modelTransit P.A P.r (‖P.h1 c₀‖ + 1) P.hA (by positivity) P.hr
  refine ⟨C, hC0, ?_⟩
  intro R hR
  by_cases hH : 0 ≤ H
  · have hRRch : Rch ≤ R := le_trans (le_max_left _ _) hR
    have hRH : 8 * (H + 2) ≤ R := le_trans (le_max_right _ _) hR
    obtain ⟨hRchOK1, h16r, hA64all, hreach⟩ := hRchOK R hRRch
    have hR128 : 128 ≤ R := by
      have h1 : P.A + ‖P.h1 c₀‖ + 2 ≥ 2 := by
        have := norm_nonneg (P.h1 c₀); linarith [P.hA]
      nlinarith [hA64all]
    have hA64 : 64 * P.A ≤ R := by
      have := norm_nonneg (P.h1 c₀); linarith [hA64all]
    have hit : ‖P.h1 c₀‖ + 2 ≤ R / 64 := by
      have := P.hA; linarith [hA64all]
    obtain ⟨ρ, hρ, hρ'⟩ := Work.PARIMPL2.Lavaurs.exists_rho_direct P R hR128
    refine ⟨ρ, hρ, ?_⟩
    intro c hc z hlev him hζre hζn
    have hcNm : c ∈ P.Nm := hc.1
    have hc1 : c ∈ Metric.ball c₀ P.ρ₀ := hcNm.1
    obtain ⟨hlamR2, hh1c, hτc1, hτpi⟩ := hρ' c hc
    have hlam : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
    have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hcNm
    have hb : Work.PARIMPL.ParBounds (P.h c) (P.h c 0) (P.h1 c) P.A P.r := P.bounds c hc1
    have hτnc : ‖P.h c 0‖ = 1 := hb.2.1
    have hκeq : P.κ c = P.h c 0 - P.h1 c / (P.h c 0) := (P.κ_eq c hc1).2
    obtain ⟨_hsym, himL, _hτ0, _hlim⟩ := Work.PARIMPL2.Lavaurs.L0_symmetry d P
    have hlar : P.lam c < P.r := by
      have hRpos : 0 < R := by linarith
      have hle : P.lam c ≤ 1 / R ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hge : 16 / R ≤ P.r := by
        rw [div_le_iff₀ hRpos]; linarith
      have hlt : 1 / R ^ 2 < 16 / R := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    have himτ : |(P.h c 0).im| ≤ P.A * (P.lam c) ^ 2 := (himL c hcNm hlar).1
    have himh1 : |(P.h1 c).im| ≤ P.A * P.lam c := (himL c hcNm hlar).2
    have hh1R64 : ‖P.h1 c‖ ≤ R / 64 := by linarith
    have hκR : 64 * ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ R := by
      have h1 : ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ 1 + ‖P.h1 c‖ := by
        calc ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ ‖P.h c 0‖ + ‖P.h1 c / (P.h c 0)‖ :=
              norm_sub_le _ _
          _ = 1 + ‖P.h1 c‖ := by rw [norm_div, hτnc, div_one]
      linarith
    have hκI : |(P.h c 0 - P.h1 c / (P.h c 0)).im| ≤ 1 / 4 :=
      Work.PARIMPL2.Direct.im_kappa_le_quarter P.A R (P.lam c) P.hA hlam.le hR128 hA64
        hlamR2 (P.h c 0) (P.h1 c) hτnc hh1R64 himτ himh1
    have hκlog : ‖P.h c 0 - P.h1 c / (P.h c 0)‖ * (1 + Real.log R) ≤ 3 * R / 4 := by
      have h1 : ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ ‖P.h1 c₀‖ + 2 := by
        have h1' : ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ 1 + ‖P.h1 c‖ := by
          calc ‖P.h c 0 - P.h1 c / (P.h c 0)‖ ≤ ‖P.h c 0‖ + ‖P.h1 c / (P.h c 0)‖ :=
                norm_sub_le _ _
            _ = 1 + ‖P.h1 c‖ := by rw [norm_div, hτnc, div_one]
        linarith
      have h2 : 0 ≤ 1 + Real.log R := by
        have := Real.log_nonneg (by linarith : (1:ℝ) ≤ R)
        linarith
      calc ‖P.h c 0 - P.h1 c / (P.h c 0)‖ * (1 + Real.log R)
            ≤ (‖P.h1 c₀‖ + 2) * (1 + Real.log R) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ 3 * R / 4 := hreach
    have hAr : 4 * (‖P.h1 c₀‖ + 1) / R + 16 * P.A / R ^ 2 ≤ 3 / 8 := by
      have h1 : ‖P.h1 c₀‖ + 1 ≤ R / 64 - 1 := by linarith
      have h2 : P.A ≤ R / 64 := by
        have := norm_nonneg (P.h1 c₀); linarith [hA64all]
      have hRpos : 0 < R := by linarith
      have e1 : 4 * (‖P.h1 c₀‖ + 1) / R ≤ 4 * (R / 64 - 1) / R := by gcongr
      have e2 : 16 * P.A / R ^ 2 ≤ 16 * (R / 64) / R ^ 2 := by gcongr
      have e3 : 4 * (R / 64 - 1) / R = 1 / 16 - 4 / R := by field_simp; ring
      have e4 : 16 * (R / 64) / R ^ 2 = 1 / (4 * R) := by field_simp; ring
      rw [e3] at e1
      rw [e4] at e2
      have hle : 1 / (4 * R) ≤ 4 / R := by
        rw [div_le_div_iff₀ (by positivity) hRpos]; nlinarith
      linarith
    set u0 : ℂ := Work.PARIMPL.ecalUin P c z with hu0
    have hz1 : Work.PARIMPL.chartZeta P c z ≠ P.a c := by
      intro hcon
      have hre : (P.a c).re = 0 := by rw [ha]; simp
      rw [hcon, hre] at hζre
      exact lt_irrefl 0 hζre
    have hz2 : Work.PARIMPL.chartZeta P c z ≠ -P.a c := by
      intro hcon
      have hre : (-P.a c).re = 0 := by rw [ha]; simp
      rw [hcon, hre] at hζre
      exact lt_irrefl 0 hζre
    have hζeq : Work.PARIMPL.chartZeta P c z = Work.Implosion.ecalPt (P.a c) u0 :=
      chartZeta_eq_ecalPt_ecalUin P hlam ha z hz1 hz2
    have hbranch : -(Real.pi / 2) < P.lam c * u0.re - Real.pi ∧
        P.lam c * u0.re - Real.pi ≤ Real.pi / 2 := by
      have h := ecalUin_branch P hlam ha z
      rwa [hu0]
    have hlev' : (Work.Implosion.approxEcal ((P.lam c : ℂ) * Complex.I)
        (P.h c 0 - P.h1 c / (P.h c 0)) u0).re ∈
        Set.Icc (Real.pi / P.lam c - R - 2) (Real.pi / P.lam c - R) := by
      have h := hlev
      unfold Work.PARIMPL.approxUin at h
      rw [← hu0] at h
      rw [ha, hκeq] at h
      exact h
    have him' : |(Work.Implosion.approxEcal ((P.lam c : ℂ) * Complex.I)
        (P.h c 0 - P.h1 c / (P.h c 0)) u0).im| ≤ H := by
      have h := him
      unfold Work.PARIMPL.approxUin at h
      rw [← hu0] at h
      rw [ha, hκeq] at h
      exact h
    have hζre' : (Work.Implosion.ecalPt ((P.lam c : ℂ) * Complex.I) u0).re < 0 := by
      rw [← ha, ← hζeq]; exact hζre
    have hζn' : ‖Work.Implosion.ecalPt ((P.lam c : ℂ) * Complex.I) u0‖ ≤ 4 / R := by
      rw [← ha, ← hζeq]; exact hζn
    obtain ⟨k, hk1, hk2, hk3, hkGT, hkr, _hslit, hkerr⟩ :=
      hMT (P.lam c) R H hlam hR128 hlamR2 hH hRH (P.h c) (P.h c 0) (P.h1 c) hb hτc1 hh1c
        hAr h16r hκR hκI hκlog hτpi u0 hbranch hlev' him' hζre' hζn'
    rw [← ha] at hk1 hk2 hk3 hkGT hkr hkerr
    rw [← hκeq] at hk1 hkerr
    have hR4 : (4:ℝ) ≤ R / 4 := by linarith
    have hstrip : ∀ j : ℕ, j ≤ k → Work.Implosion.modelOrbit (P.a c) (P.h c) j u0 ∈
        Work.Implosion.transitStrip (P.lam c) (R / 4) :=
      fun j hj => (hkGT j hj).1
    have hsmall : ∀ j : ℕ, j ≤ k → 4 * (‖Work.Implosion.ecalPt (P.a c)
        (Work.Implosion.modelOrbit (P.a c) (P.h c) j u0)‖ + P.lam c) ≤ 1 :=
      fun j hj => (hkGT j hj).2.2.1
    have horbit := Work.PARIMPL2.Lavaurs.orbit_chart P hc1 u0 k hlam ha hR4 hstrip hsmall hkr
    have hz_eq : z = P.m c + P.s c * Work.Implosion.ecalPt (P.a c) u0 := by
      rw [← hζeq]; exact (m_add_s_chartZeta P hc1 z).symm
    have hFtz : (Work.PARIMPL.Ft c)^[k] z = P.m c + P.s c *
        Work.Implosion.ecalPt (P.a c) (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) := by
      rw [hz_eq]; exact horbit
    have hcz : Work.PARIMPL.chartZeta P c ((Work.PARIMPL.Ft c)^[k] z)
        = Work.Implosion.ecalPt (P.a c) (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) := by
      rw [hFtz]; exact chartZeta_m_add_s P hc1 _
    have hstripK := (hkGT k le_rfl).1
    rw [Work.Implosion.mem_transitStrip_iff] at hstripK
    have hbrK : 0 < (2 * (P.a c) * Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).im ∧
        (2 * (P.a c) * Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).im ≤ Real.pi := by
      have hre : (2 * (P.a c) * Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).im
          = 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re) := by
        have h1 : 2 * (P.a c) * Work.Implosion.modelOrbit (P.a c) (P.h c) k u0
            = ((2 * P.lam c : ℝ) : ℂ)
              * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0 * Complex.I) := by
          rw [ha]; push_cast; ring
        rw [h1, Complex.mul_im, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [hre]
      have hRpos : 0 < R := by linarith
      have hle : P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re
          ≤ Real.pi - P.lam c * (R / 4) := by
        have h1 := mul_le_mul_of_nonneg_left hstripK.2 hlam.le
        have h2 : P.lam c * (Real.pi / P.lam c - R / 4)
            = Real.pi - P.lam c * (R / 4) := by
          rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hlam)]
        rwa [h2] at h1
      have hge : P.lam c * (R / 4) ≤
          P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re :=
        mul_le_mul_of_nonneg_left hstripK.1 hlam.le
      have hsin := Work.PARIMPL2.Direct.sin_two_mul_pos_of_ecalPt_re_pos (P.lam c) hlam
        (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) (by rw [← ha]; exact hk2)
      have hhalf : P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re
          ≤ Real.pi / 2 := by
        by_contra hcon
        push_neg at hcon
        have hlt2 : 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
            < 2 * Real.pi := by nlinarith [hle, hlam, hRpos]
        have hkey : Real.sin (2 * (P.lam c *
              (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re))
            = -Real.sin (2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
                - Real.pi) := by
          have hπ : 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
              = (2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
                - Real.pi) + Real.pi := by ring
          conv_lhs => rw [hπ]
          rw [Real.sin_add_pi]
        have h1 : 0 < 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
            - Real.pi := by linarith
        have h2 : 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re)
            - Real.pi < Real.pi := by linarith
        have h3 : 0 < Real.sin (2 * (P.lam c *
            (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re) - Real.pi) :=
          Real.sin_pos_of_pos_of_lt_pi h1 h2
        rw [hkey] at hsin
        linarith
      have hpos : 0 < 2 * (P.lam c * (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0).re) := by
        nlinarith [hge, hlam, hRpos]
      exact ⟨hpos, by linarith⟩
    have hecalU : Work.PARIMPL.ecalU P c ((Work.PARIMPL.Ft c)^[k] z)
        = Work.Implosion.modelOrbit (P.a c) (P.h c) k u0 := by
      rw [hFtz]
      exact ecalU_m_add_s_ecalPt P hc1 hlam ha _ hbrK.1 hbrK.2
    have htag : Work.PARIMPL.approxU P c ((Work.PARIMPL.Ft c)^[k] z)
        = Work.Implosion.approxEcal (P.a c) (P.κ c)
            (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0) := by
      rw [Work.PARIMPL.approxU, hecalU]
    have htag0 : Work.PARIMPL.approxUin P c z
        = Work.Implosion.approxEcal (P.a c) (P.κ c) u0 := by
      rw [Work.PARIMPL.approxUin, hu0]
    refine ⟨k, ?_, ?_, ?_, ?_⟩
    · rw [htag]; exact hk1
    · rw [hcz]; exact hk2
    · rw [hcz]; exact hk3
    · rw [htag, htag0]
      have hthis : Work.Implosion.approxEcal (P.a c) (P.κ c)
              (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0)
            - (Work.Implosion.approxEcal (P.a c) (P.κ c) u0 - (k : ℂ))
          = Work.Implosion.approxEcal (P.a c) (P.κ c)
              (Work.Implosion.modelOrbit (P.a c) (P.h c) k u0)
            - Work.Implosion.approxEcal (P.a c) (P.κ c) u0 + (k : ℂ) := by ring
      rw [hthis]
      exact hkerr
  · have hHneg : H < 0 := lt_of_not_ge hH
    refine ⟨1, one_pos, ?_⟩
    intro c hc z hlev him hζre hζn
    exfalso
    have h0 : 0 ≤ |(Work.PARIMPL.approxUin P c z).im| := abs_nonneg _
    linarith

end Work.PARIMPL2.Lavaurs
