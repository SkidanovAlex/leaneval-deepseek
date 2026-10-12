import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! ## The threshold-pinned form of FS `lem:EstimateIntegral`

`Work.BoseB7A.estIntegralOneA` states the row with an *existential* threshold
`t₀` and an *existential* constant, because that is the shape the K15 bundle
consumes.  This file needs the row at the **pinned** diluteness threshold
`(1/2) ^ 323` (the value the caller's hypothesis uses), so the pinned form is
recorded here: it is the statement that `estIntegralOneA`'s own proof
establishes (its `refine` supplies exactly the witnesses
`2000 * (max K₀ 1) ^ 5 + 2000` and `(1/2) ^ 323`, and its five scalar
ingredients `arith_aKH_div_dsell_le`, `arith_aKH_log_div_dsell_le`, `int_A_ge`,
`int_term_lowKernel` and the three `estIntegralOneA_*` estimates all take the
pinned `hv.t ≤ (1/2) ^ 323`).  Nothing is assumed here: the proof below is that
proof. -/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

/-- **FS `lem:EstimateIntegral` (`eq:CompIntegrals-Final`), threshold-pinned.**
From an `IntKernel K₀ R F E ĝ`, the FS parameter view `hv` with diluteness at the
pinned threshold `hv.t ≤ (1/2)^323` and the `R`-row `(R/ℓ)² ≤ K_H⁻¹`, the
`P_H` lattice sum is within `(2000(max K₀ 1)^5 + 2000) ρ a K_H⁻¹` of
`ρ Ŵ₁ω(0)`.  (Same proof as `estIntegralOneA`, with its witnesses made
explicit.) -/
theorem estIntegralOneA_pinned (K₀ : ℝ) :
    ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
      (hv : Work.BoseB7.FSParamsView E) (R : ℝ) (gHat : Mode → ℝ),
      hv.t ≤ (1 / 2) ^ 323 → (R / E.ell) ^ 2 ≤ E.KH⁻¹ →
      Work.BoseB7A.IntKernel K₀ R F E gHat →
      |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
        ≤ (2000 * (max K₀ 1) ^ 5 + 2000) * E.rho * E.aScat * E.KH⁻¹ := by
  intro Mode hACG hFin hDec F E hv R gHat ht hR hK
  have ha : 0 < E.aScat := hv.a_pos
  have hρ : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKHinv : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKH.le
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hℓ3 : 0 < E.ell ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hd : 0 < E.d := by rw [d_val E hv]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hKc : (1 : ℝ) ≤ max K₀ 1 := estIntegralOneA_Kc_ge_one K₀
  -- `0 ≤ K₀`: otherwise `IntKernel.sum_W1sq` is contradictory
  have hK₀ : 0 ≤ K₀ := by
    by_contra hcon
    have hcon' : K₀ < 0 := not_le.mp hcon
    have hL : 0 ≤ E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
      mul_nonneg hℓ3.le (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (by positivity)))
    have hlt : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 < 0 :=
      lt_of_le_of_lt hK.sum_W1sq (by nlinarith)
    linarith
  -- the scalar facts at the parameter point
  have h8 : 8 * (E.KH * E.aScat) ≤ E.d * E.s * E.ell := by
    have h := arith_aKH_div_dsell_le E hv ht
    have hds : 0 < E.d * E.s * E.ell := by positivity
    rw [div_le_iff₀ hds] at h
    linarith
  have hsmall : E.aScat * E.KH / (E.d * E.s * E.ell) ≤ 1 :=
    le_trans (arith_aKH_div_dsell_le E hv ht) (by norm_num)
  have hlog : E.aScat * E.KH / (E.d * E.s * E.ell) * (1 + Real.log E.KH) ≤ 1 :=
    arith_aKH_log_div_dsell_le E hv ht
  have hAge : ∀ k ∈ F.PHset E, ‖F.kmom k‖ ^ 2 / 3 ≤ E.A k :=
    int_A_ge F E R gHat K₀ hK hv h8
  have hAKH : E.aScat * E.KH ≤ E.ell := arith_aKH_le_ell E hv
  -- the decomposition
  have hdec := estIntegralOneA_decomposition F E R gHat K₀ hK hv
  -- piece 1: the discretisation error of `ω(0)`
  have hT1 : E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
      ≤ (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹ := by
    have hom := hK.omega_lattice
    have h1 : E.rho * |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
        ≤ E.rho * (K₀ * E.aScat ^ 2 / E.ell) := mul_le_mul_of_nonneg_left hom hρ
    have hratio : E.aScat ^ 2 / E.ell ≤ E.aScat * E.KH⁻¹ := by
      have h2 : E.aScat / E.ell ≤ E.KH⁻¹ := by
        rw [div_le_iff₀ hℓ]
        rw [show E.KH⁻¹ * E.ell = E.ell / E.KH by ring, le_div_iff₀ hKH]
        linarith [hAKH]
      calc E.aScat ^ 2 / E.ell = E.aScat * (E.aScat / E.ell) := by ring
        _ ≤ E.aScat * E.KH⁻¹ := mul_le_mul_of_nonneg_left h2 ha.le
    have h3 : E.rho * (K₀ * E.aScat ^ 2 / E.ell) ≤ E.rho * ((max K₀ 1) * E.aScat * E.KH⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      calc K₀ * E.aScat ^ 2 / E.ell = K₀ * (E.aScat ^ 2 / E.ell) := by ring
        _ ≤ (max K₀ 1) * (E.aScat * E.KH⁻¹) :=
            mul_le_mul (le_max_left _ _) hratio (by positivity) (by positivity)
        _ = (max K₀ 1) * E.aScat * E.KH⁻¹ := by ring
    have h4 : E.rho * ((max K₀ 1) * E.aScat * E.KH⁻¹)
        = (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹ := by ring
    linarith [h1, h3, h4.le, h4.ge]
  -- piece 2: the low-momentum tail
  have hT2 : E.rho * (E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          |E.W1 k * gHat k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    int_term_lowKernel F E R gHat K₀ hK hv hK₀
  -- piece 3: the `ĝ − Ŵ₁` difference
  have hT3 : E.rho * (E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by
    have h := estIntegralOneA_gHat_term F E R gHat K₀ hK hv hK₀ hR
    calc E.rho * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, |E.W1 k| * |gHat k - E.W1 k| / (2 * ‖F.kmom k‖ ^ 2))
        ≤ E.rho * (200 * (max K₀ 1) ^ 5 * E.aScat * E.KH⁻¹) :=
          mul_le_mul_of_nonneg_left h hρ
      _ = 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ := by ring
  -- piece 4: the `𝒜 − k²` difference
  have hT4 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.rho * E.W1 k ^ 2 * |E.A k - ‖F.kmom k‖ ^ 2| /
          (2 * ‖F.kmom k‖ ^ 2 * E.A k)
      ≤ 400 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    estIntegralOneA_A_diff_term F E R gHat K₀ hK hv hK₀ hAge hsmall hlog
  -- piece 5: the second-order `α` correction
  have hT5 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, 2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3
      ≤ 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹ :=
    estIntegralOneA_cubic_term F E R gHat K₀ hK hv hK₀ hAge
  -- assemble
  have hX : 0 ≤ E.rho * E.aScat * E.KH⁻¹ := by positivity
  have htot : (max K₀ 1) * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 400 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
        + 200 * (max K₀ 1) ^ 5 * E.rho * E.aScat * E.KH⁻¹
      ≤ (2000 * (max K₀ 1) ^ 5 + 2000) * E.rho * E.aScat * E.KH⁻¹ := by
    have h1 : (max K₀ 1) ≤ (max K₀ 1) ^ 5 := by
      have h2 : (1 : ℝ) ≤ (max K₀ 1) ^ 4 := one_le_pow₀ hKc
      calc max K₀ 1 = max K₀ 1 * 1 := by ring
        _ ≤ max K₀ 1 * (max K₀ 1) ^ 4 :=
            mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hKc)
        _ = (max K₀ 1) ^ 5 := by ring
    nlinarith [hX, h1, hKc, pow_nonneg (le_trans zero_le_one hKc) 5]
  linarith [hdec, hT1, hT2, hT3, hT4, hT5, htot]


end Work.BoseB7A

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology

theorem RowIntOne_of_IntKernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R K₀ : ℝ)
    (hv : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ (1 / 2 : ℝ) ^ 323 →
      Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ))
    (hvK : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ (1 / 2 : ℝ) ^ 323 →
      Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
      Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
    (hR : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ (1 / 2 : ℝ) ^ 323 →
      (R / (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ 2
        ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).KH⁻¹)
    (hIK : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ (1 / 2 : ℝ) ^ 323 →
      ∀ ρ : ℝ, Work.BoseGateFS.AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
        Work.BoseB7A.IntKernel K₀ R (Work.BoseRowsFS.honF v h fc fu HM μ)
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
          (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k))) :
    ∃ Kint : ℝ, 0 ≤ Kint ∧
      Work.BoseRowsFS.RowIntOneRegime (h := h) (fc := fc) (fu := fu) R
        ((1 / 2 : ℝ) ^ 323) Kint := by
  refine ⟨2000 * (max K₀ 1) ^ 5 + 2000, by positivity, ?_⟩
  intro HM μ hμ hdil ρ hadm
  have hρ0 : 0 ≤ ρ := hadm.1
  have hℓ : 0 < (honE v h fc fu HM μ).ell :=
    Work.BoseB7.ell_pos (honE v h fc fu HM μ) (hv HM μ hμ hdil)
  have hρeq : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).rho = ρ := by
    rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
    show (Real.sqrt (ρ * (honE v h fc fu HM μ).ell ^ 3)) ^ 2
        / (honE v h fc fu HM μ).ell ^ 3 = ρ
    rw [Real.sq_sqrt (by positivity), mul_div_assoc,
      div_self (pow_ne_zero 3 (ne_of_gt hℓ)), mul_one]
  have ht : (hvK HM μ ρ hμ hdil hadm).t ≤ (1 / 2 : ℝ) ^ 323 := by
    rw [← (hvK HM μ ρ hμ hdil hadm).mu_eq]
    simpa [Work.BoseFixR.KzEnvAt, Work.BoseRowsFS.honE, Work.BoseBoxFock.HonestBoxFam,
      Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs] using hdil
  have hPH : (honF v h fc fu HM μ).PHset (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ)
      = (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ) := rfl
  have hmain := Work.BoseB7A.estIntegralOneA_pinned K₀
    (honF v h fc fu HM μ) (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ)
    (hvK HM μ ρ hμ hdil hadm) R
    (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
      ((honF v h fc fu HM μ).kmom k))
    ht (hR HM μ hμ hdil) (hIK HM μ hμ hdil ρ hadm)
  rw [hPH] at hmain
  rw [hρeq] at hmain
  simpa [Work.BoseFixR.KzEnvAt] using hmain

end Work.BoseRowsFS

end
