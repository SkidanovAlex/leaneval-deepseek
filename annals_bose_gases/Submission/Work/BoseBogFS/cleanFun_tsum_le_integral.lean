import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.abs_cAt_le
import Submission.Work.BoseBogFS.bogD_le_one_of_eT_le_one
import Submission.Work.BoseBogFS.bogErrAux
import Submission.Work.BoseBogFS.bogS1_sum_le
import Submission.Work.BoseBogFS.bogS2_sum_le
import Submission.Work.BoseBogFS.bogS3_sum_le
import Submission.Work.BoseBogFS.cleanBracketArith
import Submission.Work.BoseBogFS.cleanFun_cell_excess_scale
import Submission.Work.BoseBogFS.origin_cell_excess_le
import Submission.Work.BoseBogFS.psiSc_tail_integral_le
import Submission.Work.BoseBogFS.tauAt_bounds_row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

open _root_.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The honest lattice points are the lattice points of the mesh `h = 2π/ℓ`: `kAt v μ n = lpt h n`. -/
lemma kAt_eq_lpt (v : E3 → ℝ) (μ : ℝ) (n : Fin 3 → ℤ) :
    kAt v μ n = lpt (2 * Real.pi / ell v μ) n := by
  rw [kAt, Work.BoseB4.vec, lpt]
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
  ring

/-- The origin lattice point is the origin. -/
lemma kAt_zero (v : E3 → ℝ) (μ : ℝ) : kAt v μ (0 : Fin 3 → ℤ) = 0 := by
  rw [kAt_eq_lpt]
  ext i
  simp [lpt]

/-- **The assembly of the clean Riemann row.

If, for every cell of the honest lattice `kAt v μ ·`, the excess of `cleanFun` at the cell centre
over the cell average is dominated by a summable `b` with `∑' b ≤ C·errBracket`, then the clean
lattice sum is at most the scaled integral plus `C·errBracket` — which is the conclusion of
`Work.BoseBogFS.cleanFun_tsum_le_integral`.

The analytic content of the row is exactly the construction of `b` (and of its sum bound); this
lemma is the (exact) lattice-tiling bookkeeping. -/
theorem cleanFun_tsum_le_integral_of_cell
    {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R C μ ρ : ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hℓ : 0 < ell v μ)
    (hInt : Integrable (fun k : E3 => cleanFun v h ρ μ k))
    (hSum : Summable (fun n : Fin 3 → ℤ => cleanFun v h ρ μ (kAt v μ n)))
    {b : (Fin 3 → ℤ) → ℝ} (hb_sum : Summable b)
    (hb : ∀ n, cleanFun v h ρ μ (lpt (2 * Real.pi / ell v μ) n)
        - ((2 * Real.pi / ell v μ) ^ 3)⁻¹
          * (∫ x in cell (2 * Real.pi / ell v μ) n, cleanFun v h ρ μ x) ≤ b n)
    (hC : (∑' n, b n) ≤ C * errBracket v R μ) :
    (∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (kAt v μ n))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
          * (∫ k : E3, cleanFun v h ρ μ k)
        + C * errBracket v R μ := by
  set m : ℝ := 2 * Real.pi / ell v μ with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  have hsum' : Summable (fun n : Fin 3 → ℤ => cleanFun v h ρ μ (lpt m n)) := by
    refine hSum.congr ?_
    intro n
    rw [hm, ← kAt_eq_lpt]
  have hmain := tsum_lpt_sub_integral_le (f := fun k : E3 => cleanFun v h ρ μ k) hmpos hInt hsum'
    hb_sum hb
  have hkey : (m ^ 3)⁻¹ * (∫ k : E3, cleanFun v h ρ μ k)
      = ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3 * (∫ k : E3, cleanFun v h ρ μ k) := by
    rw [hm]
    field_simp
  rw [hkey] at hmain
  have htsum_eq : (∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (kAt v μ n))
      = ∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (lpt m n) := by
    refine tsum_congr fun n => ?_
    rw [hm, ← kAt_eq_lpt]
  rw [htsum_eq]
  linarith [hmain, hC]

/-! ## The per-cell bound, with the bulk side conditions only under the bulk gate

`Work.BoseBogFS.bogCellAll` consumes the four bulk side conditions
(`0 < bogULot`, `bogUHit ≤ bogRLot²`, `0 < bogULot + 2 bogVlot`, `2 bogBs ≤ bogULot`) for
*every* cell `n ≠ 0`, but only uses them in the bulk branch `bogBigThr < bogRHit`.  The
variant below takes them only under that gate, which is what `Work.BoseBogFS.bogSideConds`
supplies. -/
theorem bogCellAllGated {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hμ : 0 < μ)
    (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hdil : dil v μ ≤ 1) (hδ : 0 < bogMesh v ρ μ)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ)
    (hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ)
    (hInt : ∀ n : Fin 3 → ℤ, IntegrableOn (psiSc v h ρ μ) (cell (bogMesh v ρ μ) n))
    (hgate : ∀ n : Fin 3 → ℤ, n ≠ 0 → bogBigThr v R ρ μ < bogRHit v ρ μ n →
      (0 < bogULot v ρ μ n
        ∧ bogUHit v ρ μ n ≤ (bogRLot v ρ μ n) ^ 2
        ∧ 0 < bogULot v ρ μ n + 2 * bogVlot v h R ρ μ n
        ∧ 2 * bogBs v R ≤ bogULot v ρ μ n))
    {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    psiSc v h ρ μ (tSca v ρ μ n)
        - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x)
      ≤ bogMaj v h R ρ μ n := by
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hmono : Monotone (tauScRad v ρ μ) := tauScRad_mono hP heT0 heT1 hc1 hc2
  have hosc := bogOm_spec (h := h) hR hρ hav hv hvrad hv_supp hRℓ hδ hn
  have hΔ : 0 < bogHalf v ρ μ := bogHalf_pos hδ
  have hOsc0 : 0 ≤ bogOm v h R ρ μ n := bogOm_nonneg hρ hav hR.le hδ hn
  have hr0 : 0 < bogRLot v ρ μ n := bogRLo_pos hδ hn
  by_cases hA : bogRHit v ρ μ n ≤ bogC1 v ρ μ
  · rw [bogMaj, if_neg hn, if_pos hA]
    exact bogCellA (h := h) hR hρ hav hμ hv hvrad hv_supp hRℓ hδ hn heT0 heT1 hc12 hA (hInt n)
  · by_cases hB : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
    · rw [bogMaj, if_neg hn, if_neg hA, if_pos hB]
      refine bogCellB (h := h) hδ hn (hInt n) ?_
      intro x hx
      have hrxl : bogRLot v ρ μ n ≤ ‖x‖ := by
        have h1 : ‖tSca v ρ μ n‖ - ‖x‖ ≤ ‖x - tSca v ρ μ n‖ := by
          have h2 := norm_sub_norm_le (tSca v ρ μ n) x
          rwa [norm_sub_rev] at h2
        rw [bogRLot]; linarith
      have hrxh : ‖x‖ ≤ bogRHit v ρ μ n := by
        have h1 := norm_add_le (x - tSca v ρ μ n) (tSca v ρ μ n)
        rw [sub_add_cancel] at h1
        rw [bogRHit]; linarith
      have hbx := abs_le.mp (hosc x hx)
      exact psiSc_cell_sqrt_le (n := n) hΔ hOsc0 hx hosc
        (tauScRad_nonneg v hP heT0 heT1 _)
        (by rw [tauSc_eq_tauScRad]; exact hmono hrxl)
        (by rw [tauSc_eq_tauScRad]; exact hmono hrxh)
        (by rw [tauSc_eq_tauScRad]; exact hmono (by rw [bogRLot]; linarith))
        (by rw [tauSc_eq_tauScRad]; exact hmono (by rw [bogRHit]; linarith))
        (by rw [bogVlot, bogVNt]; linarith [hbx.1])
        (by rw [bogVhit, bogVNt]; linarith [hbx.2])
        (by rw [bogVlot, bogVNt]; linarith [hOsc0])
        (by rw [bogVhit, bogVNt]; linarith [hOsc0])
        hrxl hrxh
        (by rw [bogRLot]; linarith)
        (by rw [bogRHit]; linarith) hr0
    · rw [bogMaj, if_neg hn, if_neg hA, if_neg hB]
      obtain ⟨hulo, huhi, huvl, hubeta⟩ := hgate n hn (lt_of_not_ge hB)
      exact bogCellC (h := h) hR hρ hav hμ hv hvrad hv_supp hRℓ hdil hδ hn heT0 heT1 hc1 hc2
        hulo huhi huvl hubeta (hInt n)

/-- **The clean Riemann row from the three region sums.**  The three lattice-sum bounds
(`Σ'bogSj ≤ 2000·X^{-43/10}`, `X = fsX v μ`) supply the whole analytic content; everything below
is the physical assembly (`cleanFun_cell_excess_scale` + `bogCellAllGated` + the origin cell
+ the budget `errBracket ≥ μ·a·X^{-4.3}`). -/
theorem cleanFun_tsum_le_integral_of_sums
    {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃)
    (hS1 : ∀ {ρ μ : ℝ}, Core v R μ ρ → dil v μ ≤ ε₁ → R ≤ ell v μ * Submission.BoseGases.chiR0 →
      Summable (bogS1 v h R ρ μ) ∧
        (∑' n : Fin 3 → ℤ, bogS1 v h R ρ μ n) ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ))
    (hS2 : ∀ {ρ μ : ℝ}, Core v R μ ρ → dil v μ ≤ ε₂ → R ≤ ell v μ * Submission.BoseGases.chiR0 →
      Summable (bogS2 v h R ρ μ) ∧
        (∑' n : Fin 3 → ℤ, bogS2 v h R ρ μ n) ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ))
    (hS3 : ∀ {ρ μ : ℝ}, Core v R μ ρ → dil v μ ≤ ε₃ → R ≤ ell v μ * Submission.BoseGases.chiR0 →
      Summable (bogS3 v h R ρ μ) ∧
        (∑' n : Fin 3 → ℤ, bogS3 v h R ρ μ n) ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      Summable (fun n : Fin 3 → ℤ => cleanFun v h ρ μ (kAt v μ n)) →
      MeasureTheory.Integrable (fun k : E3 => cleanFun v h ρ μ k) →
        (∑' n : Fin 3 → ℤ, cleanFun v h ρ μ (kAt v μ n))
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
              * (∫ k : E3, cleanFun v h ρ μ k)
            + 100000 * errBracket v R μ := by
  obtain ⟨εAbs, hεAbs0, hεAbs⟩ := abs_cAt_le (h := h) hR hv hvrad hv_supp hav
  obtain ⟨εTau, hεTau0, hεTau⟩ := tauAt_bounds_row (h := h) hav
  obtain ⟨X₀, hX₀0, hX₀sc⟩ := bogSideConds (v := v) hR hav hv hvrad hv_supp
  set θ : ℝ := (a v * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact Real.rpow_pos_of_pos
      (div_pos (mul_pos hav Submission.BoseGases.chiR0_pos) hR) _
  set ε₀ : ℝ := min (min (min ε₁ ε₂) (min ε₃ (X₀ ^ (323 : ℝ))))
      (min (min εAbs εTau) (min (coreBound v R) θ)) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (lt_min (lt_min hε₁ hε₂) (lt_min hε₃ (Real.rpow_pos_of_pos hX₀0 _)))
      (lt_min (lt_min hεAbs0 hεTau0) (lt_min (coreBound_pos hR hav) hθpos))
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm ρ hClose hSum hInt
  -- the eight pieces of the minimum
  have hA : ε₀ ≤ min (min ε₁ ε₂) (min ε₃ (X₀ ^ (323 : ℝ))) := by
    rw [hε₀def]; exact min_le_left _ _
  have hB : ε₀ ≤ min (min εAbs εTau) (min (coreBound v R) θ) := by
    rw [hε₀def]; exact min_le_right _ _
  have hε₁' : ε₀ ≤ ε₁ := le_trans hA (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₂' : ε₀ ≤ ε₂ := le_trans hA (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₃' : ε₀ ≤ ε₃ := le_trans hA (le_trans (min_le_right _ _) (min_le_left _ _))
  have hX₀' : ε₀ ≤ X₀ ^ (323 : ℝ) := le_trans hA (le_trans (min_le_right _ _) (min_le_right _ _))
  have hAbs' : ε₀ ≤ εAbs := le_trans hB (le_trans (min_le_left _ _) (min_le_left _ _))
  have hTau' : ε₀ ≤ εTau := le_trans hB (le_trans (min_le_left _ _) (min_le_right _ _))
  have hCoreB : ε₀ ≤ coreBound v R := le_trans hB (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθ' : ε₀ ≤ θ := le_trans hB (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := hAdm.1
  have hdil₀ : dil v μ ≤ ε₀ := hAdm.2.1
  have hcore : Core v R μ ρ := core_bounds hR hav hCoreB μ ρ hμ hdil₀ hClose
  have hdil₁ : dil v μ ≤ ε₁ := le_trans hdil₀ hε₁'
  have hdil₂ : dil v μ ≤ ε₂ := le_trans hdil₀ hε₂'
  have hdil₃ : dil v μ ≤ ε₃ := le_trans hdil₀ hε₃'
  have hfsX : Work.BoseFixR.fsX v μ ≤ X₀ := by
    have h1 : (dil v μ) ^ ((1 : ℝ) / 323) ≤ ε₀ ^ ((1 : ℝ) / 323) :=
      Real.rpow_le_rpow hcore.hD0.le hdil₀ (by norm_num)
    have h2 : ε₀ ^ ((1 : ℝ) / 323) ≤ X₀ := by
      have h3 := Real.rpow_le_rpow hε₀pos.le hX₀' (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 323)
      rw [← Real.rpow_mul hX₀0.le] at h3
      rwa [show (323 : ℝ) * (1 / 323) = 1 by norm_num, Real.rpow_one] at h3
    have h4 : Work.BoseFixR.fsX v μ = (dil v μ) ^ ((1 : ℝ) / 323) := rfl
    rw [h4]; exact le_trans h1 h2
  have hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0 :=
    Work.BoseFixR.adm_R_le_ell_chiR0 (ε₀ := ε₀) hR hav hθ' hAdm
  -- `Core` rows feeding `bogCellA/B/C`
  have hell : 0 < ell v μ := ell_pos_of_core hav hcore
  have hc1 : 0 < bogC1 v ρ μ := bogC1_pos_of_core hav hcore
  have hc2 : 0 < bogC2 v ρ μ := bogC2_pos_of_core hav hcore
  have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).eT := Real.rpow_nonneg hcore.hD0.le _
  have heT1 : (Work.BoseBox.paramsAt μ (a v)).eT ≤ 1 := by
    rw [paramsAt_eT]
    exact Real.rpow_le_one hcore.hD0.le hcore.hD1 (by norm_num)
  have hdrow := bogD_le_one_of_eT_le_one (v := v) (ρ := ρ) (μ := μ) hc1 heT1
  have hc12 : bogC1 v ρ μ ≤ bogC2 v ρ μ := by
    rw [hdrow.2.2, le_div_iff₀ hdrow.1]
    nlinarith [hdrow.2.1, hc1.le]
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hcore.hρ0 hav hell
  -- integrability of `psiSc`
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hell hRℓ
  have hIntψ : MeasureTheory.Integrable (fun t : E3 => psiSc v h ρ μ t) :=
    integrable_psiSc_of_cleanFun (mul_pos hcore.hρ0 hav) hW hInt
  have hβlin : ∀ k : E3, |cAt v h ρ μ k| ≤ cleanCB v μ :=
    hεAbs μ (adm_mono hAbs' hAdm) ρ hClose
  have hTauRow := hεTau μ (adm_mono hTau' hAdm)
  -- the assembled majorant
  set c₀ : ℝ := 96 * Real.pi + 512 * Real.pi * Real.sqrt 3 with hc₀def
  have hS1' := hS1 hcore hdil₁ hRℓ
  have hS2' := hS2 hcore hdil₂ hRℓ
  have hS3' := hS3 hcore hdil₃ hRℓ
  have hsumS1 : Summable (fun n : Fin 3 → ℤ => bogS1 v h R ρ μ n) := hS1'.1
  have hsumS2 : Summable (fun n : Fin 3 → ℤ => bogS2 v h R ρ μ n) := hS2'.1
  have hsumS3 : Summable (fun n : Fin 3 → ℤ => bogS3 v h R ρ μ n) := hS3'.1
  set b : (Fin 3 → ℤ) → ℝ := fun n =>
      (ρ * a v) * (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n)
        + (if n = 0 then c₀ * errBracket v R μ else 0) with hbdef
  have hfin : Summable (fun n : Fin 3 → ℤ =>
      if n = 0 then c₀ * errBracket v R μ else 0) :=
    summable_of_ne_finset_zero (s := ({0} : Finset (Fin 3 → ℤ)))
      (fun n hn => if_neg (by simpa using hn))
  have hsumB : Summable (fun n : Fin 3 → ℤ =>
      (ρ * a v) * (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n)) :=
    Summable.mul_left _ ((hsumS1.add hsumS2).add hsumS3)
  have hb_sum : Summable b := by
    simp only [hbdef]
    exact hsumB.add hfin
  have hPnn : 0 ≤ ρ * a v := mul_nonneg hcore.hρ0.le hav.le
  have herrnn : 0 ≤ errBracket v R μ := (errBracket_pos v hμ hav).le
  have hX43pos : 0 < (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) :=
    Real.rpow_pos_of_pos (fsX_pos hμ hav) _
  -- the per-cell bound
  have hper : ∀ n : Fin 3 → ℤ,
      cleanFun v h ρ μ (lpt (2 * Real.pi / ell v μ) n)
        - ((2 * Real.pi / ell v μ) ^ 3)⁻¹
          * (∫ x in cell (2 * Real.pi / ell v μ) n, cleanFun v h ρ μ x) ≤ b n := by
    intro n
    simp only [hbdef, ← kAt_eq_lpt]
    by_cases hn : n = 0
    · subst hn
      simp only [kAt_zero, sub_zero]
      rw [if_pos trivial]
      -- the origin cell
      have hKl2 : (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ))
          = (dil v μ) ^ ((3 : ℝ) / 323) := paramsAt_Kl_inv_sq v μ hcore.hD0
      have hβ0 : 0 ≤ cleanCB v μ := by
        have hd0 : (0 : ℝ) ≤ dil v μ := hcore.hD0.le
        have h1 : (0 : ℝ) ≤ (dil v μ) ^ ((3 : ℝ) / 323) := Real.rpow_nonneg hd0 _
        have h2 : (0 : ℝ) ≤ μ * (dil v μ) ^ ((3 : ℝ) / 323) / ((2 : ℝ) ^ 14 * Real.pi) :=
          div_nonneg (mul_nonneg hμ.le h1) (by positivity)
        rw [cleanCB, cleanRhoB, hKl2]
        exact mul_nonneg (by linarith only [h2, hμ]) (by positivity)
      have hlo1 : 0 < cleanLo1 v μ := by
        rw [cleanLo1]
        refine inv_pos.mpr (mul_pos (mul_pos (by norm_num) ?_) hell)
        rw [paramsAt_s]; exact Real.rpow_pos_of_pos hcore.hD0 _
      have hlo2 : 0 < cleanLo2 v μ := by
        rw [cleanLo2]
        refine inv_pos.mpr (mul_pos (mul_pos (mul_pos (by norm_num) ?_) ?_) hell)
        · rw [paramsAt_d]; exact Real.rpow_pos_of_pos hcore.hD0 _
        · rw [paramsAt_s]; exact Real.rpow_pos_of_pos hcore.hD0 _
      have hloMin : 0 ≤ cleanLoMin v μ := (lt_min hlo1 hlo2).le
      have hτ0 : tauAt v μ (0 : E3) = 0 := by
        have h := (hTauRow (0 : E3)).2.2.1
        exact h (by simpa using hloMin)
      have hτnn : ∀ k : E3, 0 ≤ tauAt v μ k := fun k => (hTauRow k).1
      have horig := origin_cell_excess_le (h := h) (ρ := ρ) (μ := μ) (β₀ := cleanCB v μ)
        hβ0 hτ0 hτnn hβlin
      have hA1 := cleanCB_le_const_mul_errBracket (v := v) (R := R) (μ := μ) hav hμ hcore.hD1
      have hB1 := cleanCB_sq_mul_m_inv_sq_le_errBracket (v := v) (R := R) (μ := μ) hav hμ hcore.hD1
      have hkey : cleanCB v μ ^ 2 * (2 * Real.pi * Real.sqrt 3)
            / (2 * Real.pi / ell v μ) ^ 2
          = 2 * Real.pi * Real.sqrt 3
              * (cleanCB v μ ^ 2 * ((2 * Real.pi / ell v μ)⁻¹) ^ 2) := by
        rw [div_eq_mul_inv, inv_pow]
        ring
      have hzero : 3 * cleanCB v μ + cleanCB v μ ^ 2 * (2 * Real.pi * Real.sqrt 3)
            / (2 * Real.pi / ell v μ) ^ 2 ≤ c₀ * errBracket v R μ := by
        rw [hkey, hc₀def]
        have hA1' : 3 * cleanCB v μ ≤ 3 * (32 * Real.pi * errBracket v R μ) :=
          mul_le_mul_of_nonneg_left hA1 (by norm_num)
        have hB1' : 2 * Real.pi * Real.sqrt 3
              * (cleanCB v μ ^ 2 * ((2 * Real.pi / ell v μ)⁻¹) ^ 2)
            ≤ 2 * Real.pi * Real.sqrt 3 * (256 * errBracket v R μ) :=
          mul_le_mul_of_nonneg_left hB1 (by positivity)
        nlinarith [hA1', hB1', herrnn]
      have hnnP : 0 ≤ (ρ * a v) * (bogS1 v h R ρ μ 0 + bogS2 v h R ρ μ 0 + bogS3 v h R ρ μ 0) := by
        refine mul_nonneg hPnn ?_
        have h1 := bogS1_nonneg v h R ρ μ (0 : Fin 3 → ℤ)
        have h2 := bogS2_nonneg v h R ρ μ (0 : Fin 3 → ℤ)
        have h3 := bogS3_nonneg v h R ρ μ (0 : Fin 3 → ℤ)
        linarith
      linarith [horig, hzero, hnnP]
    · rw [if_neg hn, add_zero]
      have hscale := cleanFun_cell_excess_scale (h := h) (ρ := ρ) (μ := μ)
        (mul_pos hcore.hρ0 hav) n hInt.integrableOn hIntψ.integrableOn
      rw [hscale, Psc]
      have hgate : ∀ n' : Fin 3 → ℤ, n' ≠ 0 → bogBigThr v R ρ μ < bogRHit v ρ μ n' →
          (0 < bogULot v ρ μ n'
            ∧ bogUHit v ρ μ n' ≤ (bogRLot v ρ μ n') ^ 2
            ∧ 0 < bogULot v ρ μ n' + 2 * bogVlot v h R ρ μ n'
            ∧ 2 * bogBs v R ≤ bogULot v ρ μ n') :=
        fun n' hn' hgt => hX₀sc hcore hn' hfsX hRℓ hgt
      have hcell := bogCellAllGated (h := h) hR hcore.hρ0 hav hμ hv hvrad hv_supp hRℓ
        hcore.hD1 hδ heT0 heT1 hc1 hc2 hc12 (fun _ => hIntψ.integrableOn) hgate hn
      have hgated := bogMaj_le_gated v h R ρ μ n
      have h1 : ρ * a v * (psiSc v h ρ μ (tSca v ρ μ n)
            - ((bogMesh v ρ μ) ^ 3)⁻¹ * (∫ x in cell (bogMesh v ρ μ) n, psiSc v h ρ μ x))
          ≤ ρ * a v * bogMaj v h R ρ μ n :=
        mul_le_mul_of_nonneg_left hcell hPnn
      have h2 : ρ * a v * bogMaj v h R ρ μ n
          ≤ ρ * a v * (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n) :=
        mul_le_mul_of_nonneg_left hgated hPnn
      exact le_trans h1 h2
  -- the sum of `b`
  have hite : (∑' n : Fin 3 → ℤ, (if n = 0 then c₀ * errBracket v R μ else 0))
      = c₀ * errBracket v R μ :=
    tsum_ite_eq (0 : Fin 3 → ℤ) (fun _ => c₀ * errBracket v R μ)
  have hadd : (∑' n : Fin 3 → ℤ, (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n))
      = (∑' n : Fin 3 → ℤ, bogS1 v h R ρ μ n) + (∑' n : Fin 3 → ℤ, bogS2 v h R ρ μ n)
        + (∑' n : Fin 3 → ℤ, bogS3 v h R ρ μ n) := by
    rw [Summable.tsum_add (hsumS1.add hsumS2) hsumS3, Summable.tsum_add hsumS1 hsumS2]
  have htsum_b : (∑' n, b n)
      = ρ * a v * ((∑' n, bogS1 v h R ρ μ n) + (∑' n, bogS2 v h R ρ μ n)
          + (∑' n, bogS3 v h R ρ μ n))
        + c₀ * errBracket v R μ := by
    simp only [hbdef]
    rw [Summable.tsum_add hsumB hfin, tsum_mul_left, hadd, hite]
  have hsum_bound : (∑' n : Fin 3 → ℤ,
        (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n))
      ≤ 6000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := by
    rw [hadd]
    linarith [hS1'.2, hS2'.2, hS3'.2]
  have hC : (∑' n, b n) ≤ 100000 * errBracket v R μ := by
    rw [htsum_b]
    have h43 := errBracket_ge_mu_a_X43 (v := v) (R := R) (μ := μ) hμ hav
    have hstep1 : ρ * a v * (∑' n : Fin 3 → ℤ,
          (bogS1 v h R ρ μ n + bogS2 v h R ρ μ n + bogS3 v h R ρ μ n))
        ≤ ρ * a v * (6000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_bound hPnn
    have hstep2 : ρ * a v * (6000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ))
        ≤ 6600 * errBracket v R μ := by
      have h1 : ρ * a v ≤ (11 / 10 : ℝ) * (μ * a v) := by
        nlinarith only [hcore.hρhi, hav.le]
      have h2 : 0 ≤ (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := hX43pos.le
      have h3 : ρ * a v * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ)
          ≤ ((11 / 10 : ℝ) * (μ * a v)) * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) :=
        mul_le_mul_of_nonneg_right h1 h2
      have h4 := mul_le_mul_of_nonneg_left h43 (by norm_num : (0 : ℝ) ≤ 6600)
      nlinarith [h3, h4]
    have hc₀le : c₀ ≤ 3400 := by
      have h3 : Real.sqrt 3 < 7 / 4 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
      have hπ : Real.pi < 3.15 := Real.pi_lt_d2
      rw [hc₀def]
      nlinarith [h3, hπ, Real.pi_pos, Real.sqrt_nonneg 3]
    nlinarith [hstep1, hstep2, hc₀le, herrnn]
  exact cleanFun_tsum_le_integral_of_cell (C := 100000) (b := b) hav hμ hell hInt hSum
    hb_sum hper hC

theorem cleanFun_tsum_le_integral :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        Summable (fun n : Fin 3 → ℤ => Work.BoseBogFS.cleanFun v h ρ μ (Work.BoseBogFS.kAt v μ n)) →
        MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) =>
            Work.BoseBogFS.cleanFun v h ρ μ k) →
          (∑' n : Fin 3 → ℤ, Work.BoseBogFS.cleanFun v h ρ μ (Work.BoseBogFS.kAt v μ n))
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
                * (∫ k : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.cleanFun v h ρ μ k)
              + C * Work.BoseBogFS.errBracket v R μ := by
  refine ⟨100000, by norm_num, ?_⟩
  intro v h R hR hv hvrad hv_supp hav
  obtain ⟨ε₁, hε₁, hS1⟩ := bogS1_sum_le (h := h) hR hav hv hvrad hv_supp
  obtain ⟨ε₂, hε₂, hS2⟩ := bogS2_sum_le (h := h) hR hav hv hvrad hv_supp
  obtain ⟨ε₃, hε₃, hS3⟩ := bogS3_sum_le (h := h) hR hav hv hvrad hv_supp
  exact cleanFun_tsum_le_integral_of_sums (h := h) hR hav hv hvrad hv_supp
    hε₁ hε₂ hε₃ hS1 hS2 hS3

end Work.BoseBogFS
