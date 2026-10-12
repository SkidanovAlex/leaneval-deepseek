import ChallengeDeps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseBoxFock.CloseCondFSCompat
import Submission.Work.BoseFixR.FarEnvPos
import Submission.Work.BoseFixR.FarResidAdm
import Submission.Work.BoseGateFS.GateHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.FarResidBaux.farEnvSideB`

The side conditions of FS `thm:BogHamDiag`'s pair form (`Work.BoseFixR.FarBogPair`'s
`qw_KzBogFS_lower`/`pairQuad_ground`) at the `ε`-split environment `farEnv E v μ ρ`:

* `𝒜_k > 0`, `|ℬ_k| ≤ 𝒜_k`, `𝒜_k + ℬ_k > 0` — the `τ̃ ≥ 0` and `|Ŵ₁| ≤ 16πa` arithmetic of
  FS `lem:Roughbounds` (the same argument as `Work.BoseFixR.FarEnvPos`, now for an
  arbitrary view-satisfying `KzDatum`);
* evenness of `𝒜`, `ℬ` and of the `c`-number coefficient `𝒞` (`cCoefFar`) — these come from
  the view's **pins** `E.tau = tauSm (paramsAt …) (F.kmom ·)`,
  `E.W1 = uvCut fu Λ (F.kmom ·) · chat (W1fun …) (F.kmom ·)`,
  `E.hatChi = chat (chiFun …) (F.kmom ·)/chat (chiFun …²) 0` together with the mode parity
  `F.kmom (-k) = -F.kmom k` (`FockData.kmom_neg`), `norm_neg` and the evenness of
  `chat` (`Work.BoseB7AK.W1rows.chat_neg`);
* the box commutator bound `[a_k,a_k†] + [a_{−k},a_{−k}†] ≤ 2`: from the view's §10 gate
  `Q3KernelFS` at a *close* density (`ρ = μ`, always `CloseCond`), whose
  `hasKernel_noWrap` at the diagonal pairs `(k,k)`, `(−k,−k)` (always `NoWrap`, since
  `kmom 0 = 0`) gives `[a_k,a_k†] = χ̂²(0) − χ̂(k)² ≤ 1`, and likewise for `−k`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.FarResidBaux

open Work.BoseFixR Work.BoseBoxFock Work.BoseB7 Work.BoseBox

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. Unfolding lemmas for the two environments -/

lemma tauSm_neg (eT s d ℓ : ℝ) (k : ℝ³) : tauSm eT s d ℓ (-k) = tauSm eT s d ℓ k := by
  simp only [tauSm, norm_neg]

lemma uvCut_neg (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (k : ℝ³) :
    uvCut fu Λ (-k) = uvCut fu Λ k := by
  simp only [uvCut, norm_neg]

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

lemma kzAtA (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).A k = E.tau k + ρ * E.W1 k := rfl

lemma kzAtB (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).B k = ρ * E.W1 k := rfl

lemma kzAttau (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).tau k = E.tau k := rfl

lemma kzAtchi (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).hatChi k = E.hatChi k := rfl

lemma kzAtchiSq (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).hatChiSq k = E.hatChiSq k := rfl

lemma farEnvTau (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).tau k
      = (1 - epsFar v μ ρ) * E.tau k
        + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := rfl

lemma farEnvW1 (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).W1 k = E.W1 k := rfl

lemma farEnvChi (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).hatChi k = E.hatChi k := rfl

lemma farEnvMu (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) :
    (farEnv E v μ ρ).mu = E.mu := rfl

/-- The label `0` has zero momentum (`kmom (-i) = -kmom i`). -/
lemma fockData_kmom_zero (F : FockData Mode) : F.kmom 0 = 0 := by
  have h := F.kmom_neg 0
  rw [neg_zero] at h
  have h2 : (2 : ℝ) • F.kmom 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ## 2. Parity of the view's kernels (`E.tau`, `E.W1`, `E.hatChi`) -/

/-- The view pins `E.tau` to `tauSm` of `F.kmom`, which depends on `‖·‖` only. -/
theorem viewFS_tau_even {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) (k : D.Mode) :
    D.E.tau (-k) = D.E.tau k := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htau, -⟩ := hview
  simp only [htau, D.F.kmom_neg, tauSm_neg]

/-- The view pins `E.W1` to `uvCut fu Λ (F.kmom ·) · chat (W1fun …) (F.kmom ·)`; the
cut-off depends on `‖·‖` only and `chat` of a real function is even. -/
theorem viewFS_W1_even {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) (k : D.Mode) :
    D.E.W1 (-k) = D.E.W1 k := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hW1pin, -⟩ := hview
  obtain ⟨fu, Λ, -, hW1eq⟩ := hW1pin
  simp only [hW1eq, D.F.kmom_neg, uvCut_neg, Work.BoseB7AK.W1rows.chat_neg]

/-- The view pins `E.hatChi` to `chat (chiFun …) (F.kmom ·)` (divided by a constant). -/
theorem viewFS_hatChi_even {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFS v h μ) (k : D.Mode) :
    D.E.hatChi (-k) = D.E.hatChi k := by
  unfold KzDatum.viewFS RViewFS at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hhChi, -⟩ := hview
  simp only [hhChi, D.F.kmom_neg, Work.BoseB7AK.W1rows.chat_neg]

/-! ## 3. The side conditions at `farEnv` -/

theorem farEnvSideB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ ρ : ℝ} (D : KzDatum)
    (hε : Work.BoseFixR.epsFar v μ ρ ≤ 1 / 10 ^ 8)
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hview : KzDatum.viewFS D v h μ)
    (hW1 : ∀ k : D.Mode, |D.E.W1 k| ≤ 16 * Real.pi * BoseGases.a v) :
    (∀ k : D.Mode, 0 < (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).A k)
      ∧ (∀ k : D.Mode, |(Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).B k|
          ≤ (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).A k)
      ∧ (∀ k : D.Mode, 0 < (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).A k
          + (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).B k)
      ∧ (∀ k : D.Mode, (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).A (-k)
          = (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).A k)
      ∧ (∀ k : D.Mode, (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).B (-k)
          = (Work.BoseFixR.KzEnvAt (Work.BoseFixR.farEnv D.E v μ ρ) ρ).B k)
      ∧ (∀ k : D.Mode, Work.BoseFixR.cCoefFar (Work.BoseFixR.farEnv D.E v μ ρ) ρ (-k)
          = Work.BoseFixR.cCoefFar (Work.BoseFixR.farEnv D.E v μ ρ) ρ k)
      ∧ (∀ k : D.Mode, D.F.ccrK k k + D.F.ccrK (-k) (-k) ≤ 2) := by
  have hτ : ∀ k : D.Mode, 0 ≤ D.E.tau k := fun k => farEnvPos_tau_nonneg D hview k
  have hε0 : 0 < epsFar v μ ρ := farEnvPos_eps_pos hμ hav hρ
  have hbig : (10 : ℝ) ^ 4 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := farEnvPos_rpow_ge hε0 hε
  have h1ε : 0 ≤ 1 - epsFar v μ ρ := by linarith
  -- the two `ε`-arithmetic facts of FS `lem:Roughbounds`
  have hpi16 : 16 * Real.pi < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
    have h64 : 16 * Real.pi < 64 := by linarith [Real.pi_lt_four]
    have h10000 : (64 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  have hpi32 : 32 * Real.pi < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
    have h128 : 32 * Real.pi < 128 := by linarith [Real.pi_lt_four]
    have h10000 : (128 : ℝ) < (10 : ℝ) ^ 4 := by norm_num
    linarith
  -- the lower bound `ρŴ₁(k) ≥ −16πρa` of `hW1`
  have hW1lo : ∀ k : D.Mode, -(ρ * (16 * Real.pi * BoseGases.a v)) ≤ ρ * D.E.W1 k := by
    intro k
    have h3 : ρ * (-(16 * Real.pi * BoseGases.a v)) ≤ ρ * D.E.W1 k :=
      mul_le_mul_of_nonneg_left (abs_le.mp (hW1 k)).1 hρ.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `𝒜_k > 0`
    intro k
    rw [kzAtA, farEnvTau, farEnvW1]
    have hpos : ρ * (16 * Real.pi * BoseGases.a v)
        < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
      have h2 : 16 * Real.pi * BoseGases.a v
          < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
        mul_lt_mul_of_pos_right hpi16 hav
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left h2 hρ
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * D.E.tau k := mul_nonneg h1ε (hτ k)
    linarith [hW1lo k, hpos, hnn]
  · -- `|ℬ_k| ≤ 𝒜_k`
    intro k
    rw [kzAtB, kzAtA, farEnvTau, farEnvW1, abs_mul, abs_of_pos hρ]
    have h1 : ρ * |D.E.W1 k| ≤ ρ * (16 * Real.pi * BoseGases.a v) :=
      mul_le_mul_of_nonneg_left (hW1 k) hρ.le
    have hneg : -(ρ * |D.E.W1 k|) ≤ ρ * D.E.W1 k := by
      have h3 : ρ * (-|D.E.W1 k|) ≤ ρ * D.E.W1 k :=
        mul_le_mul_of_nonneg_left (neg_abs_le _) hρ.le
      linarith
    have h2 : 2 * (ρ * (16 * Real.pi * BoseGases.a v))
        ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
      have h3 : 32 * Real.pi * BoseGases.a v
          ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
        mul_le_mul_of_nonneg_right hpi32.le hav.le
      have h4 : ρ * (32 * Real.pi * BoseGases.a v)
          ≤ ρ * ((epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) :=
        mul_le_mul_of_nonneg_left h3 hρ.le
      linarith
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * D.E.tau k := mul_nonneg h1ε (hτ k)
    linarith [h1, hneg, h2, hnn]
  · -- `𝒜_k + ℬ_k > 0`
    intro k
    rw [kzAtA, kzAtB, farEnvTau, farEnvW1]
    have h2 : ρ * (32 * Real.pi * BoseGases.a v)
        < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
      have h3 : 32 * Real.pi * BoseGases.a v
          < (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v :=
        mul_lt_mul_of_pos_right hpi32 hav
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left h3 hρ
    have hnn : 0 ≤ (1 - epsFar v μ ρ) * D.E.tau k := mul_nonneg h1ε (hτ k)
    linarith [hW1lo k, h2, hnn]
  · -- `𝒜` is even
    intro k
    rw [kzAtA, kzAtA, farEnvTau, farEnvTau, farEnvW1, farEnvW1,
      viewFS_tau_even D hview k, viewFS_W1_even D hview k]
  · -- `ℬ` is even
    intro k
    rw [kzAtB, kzAtB, farEnvW1, farEnvW1, viewFS_W1_even D hview k]
  · -- `𝒞 = cCoefFar` is even
    intro k
    simp only [cCoefFar, farEnvChi, farEnvMu, farEnvW1]
    rw [viewFS_hatChi_even D hview k]
  · -- `[a_k,a_k†] + [a_{−k},a_{−k}†] ≤ 2`, from the §10 gate at the close density `μ`
    intro k
    have hvw : KzDatum.viewFS D v h μ := hview
    unfold KzDatum.viewFS RViewFS at hvw
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hgate⟩ := hvw
    obtain ⟨K₀, b₀, hK0, hb0, hb0b, hgate⟩ := hgate
    have hKl : 0 < (paramsAt μ (BoseGases.a v)).Kl := by
      have hdil : 0 < dil v μ := by
        simp only [dil]
        positivity
      simp only [paramsAt, fsParams]
      exact fsXp_pos hdil
    have hcc : Work.BoseBoxFock.CloseCondFS v μ μ :=
      Work.BoseBoxFock.closeCondFS_self hμ hav
    have hz : D.F.kmom 0 = 0 := fockData_kmom_zero D.F
    have hnw : ∀ j : D.Mode, Work.BoseK15.NoWrap D.F.kmom j j := by
      intro j
      simp only [Work.BoseK15.NoWrap, sub_self, hz, sub_self]
    have hself : ∀ j : D.Mode, D.F.ccrK j j ≤ 1 := by
      intro j
      have hh := (hgate μ hcc).hasKernel_noWrap j j (hnw j)
      rw [sub_self] at hh
      have h1 : (KzEnvAt D.E μ).hatChiSq 0 ≤ 1 :=
        (abs_le.mp ((hgate μ hcc).hatChiSq_le 0)).2
      have h2 : 0 ≤ (KzEnvAt D.E μ).hatChi j * (KzEnvAt D.E μ).hatChi j :=
        mul_self_nonneg _
      linarith [hh, h1, h2]
    have hk1 : D.F.ccrK k k ≤ 1 := hself k
    have hk2 : D.F.ccrK (-k) (-k) ≤ 1 := hself (-k)
    linarith

end Work.BoseFixR.FarResidBaux
