import ChallengeDeps
import Submission.Work.BoseGateFS.GateHonest
import Submission.Work.BoseGateFS.arith_tauTilde_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.HonestInhab` — the honest rows that are theorems

Three of the rows of the honest bundle `HonestRows` are *derivable* rather than
inputs, and this module proves them:

* `hon_tau` — **the kinetic domination at the honest model**:
  `‖k_q‖²/2 + 3ρK₀a ≤ τ̃(k_q)` on `P_H^q`, for every admissible `ρ`.  It is
  `arith_tauTilde_ge` (the arithmetic at FS's parameters, the `τ̃`-analogue of
  `Work.BoseK15.arith_tau_ge`) composed with `tauTilde_ge_kink` (the kinked lower
  bound of the smoothed symbol).  The potential coefficient is handled by
  re-pointing the environment at `KzEnvAt E ρ`, whose `ρ_z` is `ρ`
  (`GateInput.rho_kz`) and whose view is `E`'s view (the scalars are unchanged).
* `adm_of_closeCond` — `CloseCond` gives `AdmRho`: `|ρ-μ| ≤ μ(μa³)^{3/323} ≤ μ/2`
  at small diluteness (`Arith.Kl_inv_sq`).
* `hb_honest` — the gap coefficient `b₀ = 1/32` is below the honest `b = 1/16`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- `E.mu > 0` at FS's parameters. -/
lemma mu_pos_of_view (hv : FSParamsView E) : 0 < E.mu := by
  have ht : 0 < E.aScat ^ 3 * E.mu := by rw [mul_comm, hv.mu_eq]; exact hv.t_pos
  exact pos_of_mul_pos_right ht (pow_pos hv.a_pos 3).le

/-- **The kinetic domination at the honest model**, with its threshold. -/
theorem exists_hon_tau (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ tGe : ℝ, 0 < tGe ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode},
        (∀ k : Mode, E.tau k = Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell (F.kmom k)) →
        (hv : FSParamsView E) → hv.t ≤ tGe →
        E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 32 →
        ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
          ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q := by
  obtain ⟨tGe, htGe0, htGe⟩ := arith_tauTilde_ge_rho K₀ hK₀
  refine ⟨tGe, htGe0, ?_⟩
  intro Mode _ _ _ F T E htau hv hthr hsmall ρ hρ q hq
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hφ : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
    fun r => Work.BoseBoxFock.tauProf_spec.2.2.1 r
  have hE0 : 0 ≤ E.eT := by
    rw [hv.eT_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have hE1 : E.eT ≤ 1 := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hd : 0 < E.d := by rw [hv.d_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have h1 := htGe E hv ρ hρ.1 hρ.2.2 hthr hsmall ‖F.kmom q‖ hq
  have h2 : (1 - E.eT) * max (‖F.kmom q‖ - (E.s * E.ell)⁻¹) 0 ^ 2
      + E.eT * max (‖F.kmom q‖ - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 ≤ E.tau q := by
    have h3 := tauTilde_ge_kink (φ := Work.BoseBoxFock.tauProf) hφ hE0 hE1 hs hd hell
      (F.kmom q)
    have h4 : tauTilde Work.BoseBoxFock.tauProf E.eT E.s E.d E.ell (F.kmom q) = E.tau q := by
      rw [← tauSm_eq_tauTilde]
      exact (htau q).symm
    rwa [h4] at h3
  exact le_trans h1 h2

/-! ## 2. `CloseCond` gives `AdmRho` -/

/-- **`CloseCond` is inside the admissible window.**  `closeThreshold v μ = μ(μa³)^{3/323}`
(`Arith.Kl_inv_sq`), so `|ρ - μ| ≤ μ/2` as soon as `(μa³)^{3/323} ≤ 1/2`. -/
theorem adm_of_closeCond {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hav : 0 < a v) (hμ : 0 < μ)
    (hε : (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2) (hclose : CloseCond v μ ρ) :
    0 ≤ ρ ∧ μ / 2 ≤ ρ ∧ ρ ≤ 3 * μ / 2 := by
  have hthr : closeThreshold v μ = μ * (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) := by
    rw [closeThreshold, Work.BoseFixR.Kl_inv_sq v hμ hav]
  rw [CloseCond, hthr, abs_le] at hclose
  have hdil : 0 < Work.BoseFixR.dil v μ := by unfold Work.BoseFixR.dil; positivity
  have hpos : 0 ≤ μ * (dil v μ) ^ (3 / 323 : ℝ) :=
    mul_nonneg hμ.le (Real.rpow_nonneg hdil.le _)
  have hmul : μ * (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ μ / 2 :=
    calc μ * (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ μ * (1 / 2) :=
          mul_le_mul_of_nonneg_left hε hμ.le
      _ = μ / 2 := by ring
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hclose.1, hclose.2, hμ, hmul]

/-- The same, at the honest environment: `AdmRho E ρ`. -/
theorem adm_of_closeCond' {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hav : 0 < a v) (hμ : 0 < μ) (hE : E.mu = μ)
    (hε : (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2) (hclose : CloseCond v μ ρ) :
    AdmRho E ρ := by
  obtain ⟨h1, h2, h3⟩ := adm_of_closeCond hav hμ hε hclose
  exact ⟨h1, by rw [hE]; exact h2, by rw [hE]; exact h3⟩

/-! ## 3. The gap coefficient -/

/-- The honest environment's gap coefficient is FS's `b = 1/16`. -/
theorem honE_b {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).E.b = 1 / 16 := by
  have h1 : (HonestBoxFam v h fc fu HM μ).E.b = (Work.BoseBox.paramsAt μ (a v)).b := by
    simp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs]
  rw [h1, Work.BoseFixB1.paramsAt_b_eq, Work.BoseBox.bValue]

end Work.BoseGateFS
