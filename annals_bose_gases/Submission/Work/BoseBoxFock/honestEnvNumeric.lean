import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.EnvFacts
import Submission.Work.BoseBoxFock.honestEnvFacts2
import Submission.Work.BoseFixR.WindowRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/honestEnvNumeric.lean`

The **regime lemma** of the honest environment bundle `EnvFactsAt`
(`Submission/Work/BoseBoxFock/EnvFacts.lean`):

    ∃ ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → EnvFactsAt v h fc fu HM μ C.

Every conjunct of `EnvFactsAt` is a *monomial* statement about the box parameters
at the diluteness `t = μ(a v)³` — the box side is `ℓ = K_ℓ(μa)^{-1/2}` with
`μℓ³ = t^{-166/323}` (`Work.BoseFixB1.mu_ell_cube_eq`), and the §10 windows are
`𝓜 = K_M t^{-1/4}` (`Work.BoseBox.bigM`, `K_M = t^{-1/323}`).  So the whole lemma
is the following list of elementary comparisons, valid for all admissible `μ`
(`0 < μ`, `t ≤ ε₀ ≤ 1`, `R ≤ ℓ·χ_{R₀}`, `157 ≤ μℓ³`):

* `1 ≤ μℓ³` — the `157`-clause of `Work.BoseFixR.WindowRegime`;
* `ℓ^{-3} ≤ Cμ` — `ℓ^{-3} = μ t^{166/323} ≤ μ`;
* `𝓜 ≤ C μℓ³` — `𝓜 = t^{-327/(4·323)}`, `μℓ³ = t^{-166/323}` and
  `-327/1292 > -664/1292`, so `𝓜 ≤ μℓ³` for `t ≤ 1`;
* `|Ŵ₁(k)| ≤ C a` — FS `eq:WSestimate` at the corpus kernel
  (`Work.BoseB7AK.W1rows.W1hat_abs_le` gives `16π·a v`), times the UV cut-off
  `ζ_Λ ≤ 1` (`Work.BoseBoxFix.LowCut.le_one`);
* `|Ŵ₁ω(k)| ≤ Ca` and `0 ≤ Ŵ₁ω(0) ≤ Ca` — FS `0 ≤ ∫W₁ω ≤ Ca` at the corpus
  kernel (`Work.BoseB7AK.W1rows.W1omega0_rows`, `W1omega_abs_integral_le`),
  which need `0 ≤ v` radial of compact support (as in the paper);
* `0 ≤ 8πa + Ŵ₁ω(0)` ⟹ `0 ≤ cHCF E (8π·a v)` (`cHCF_nonneg`);
* the parity rows (`honestEnvFam_parity`), `E.mu = μ`, `E.ell = sideAt μ (a v)`.

The constant is `C = max 1 (16π)` throughout; it is independent of `μ` (the
`𝓜`-row uses `𝓜 ≤ μℓ³`, *not* a bound on `K_M` alone, which would not be uniform
in the dilute window).

The statement of `honestEnvNumeric` is unchanged; only helper lemmas are added
above it.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-! ## 1. The helper lemmas (one per row of `EnvFactsAt`) -/

/-- `ellH v μ = sideAt μ (a v)` in the regime where the box side is positive. -/
lemma ellH_eq_sideAt {v : ℝ³ → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  rw [ellH, if_pos h]

/-- **The `Ŵ₁`-row.**  `|Ŵ₁(k)| ≤ 16π·(a v)` for the honest `E.W1`
(`Ŵ₁` times the UV cut-off `ζ_Λ`, which is `≤ 1`). -/
lemma honestFam_W1_abs_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0)
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (k : Lab (HM μ).N) :
    |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v := by
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := ellH_eq_sideAt hℓ
  rw [show (HonestBoxFam v h fc fu HM μ).E.W1 k
      = uvCut fu (uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
          (kmomLab (ellH v μ) (HM μ).N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
            (kmomLab (ellH v μ) (HM μ).N k) from rfl,
    hell]
  rw [abs_mul]
  have huv : 0 ≤ uvCut fu (uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
      (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) :=
    Work.BoseBoxFix.LowCut.nonneg fu _
  rw [abs_of_nonneg huv]
  have h16 := Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ (fun x => hv x) hvrad hv_supp h hRℓ
    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k)
  calc uvCut fu (uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N)
        (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k)
      * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
            (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k)|
      ≤ 1 * (16 * Real.pi * BoseGases.a v) :=
        mul_le_mul (Work.BoseBoxFix.LowCut.le_one fu _) h16 (abs_nonneg _) (by norm_num)
    _ = 16 * Real.pi * BoseGases.a v := by ring

/-- **The `Ŵ₁ω`-row.**  `|Ŵ₁ω(k)| ≤ 16π·(a v)` (the Fourier transform is
dominated by the `L¹` mass of `W₁ω`, which is `≤ 16π·(a v)`). -/
lemma honestFam_W1omega_abs_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0)
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (k : Lab (HM μ).N) :
    |(HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ 16 * Real.pi * BoseGases.a v := by
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := ellH_eq_sideAt hℓ
  rw [show (HonestBoxFam v h fc fu HM μ).E.W1omega k
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
          (kmomLab (ellH v μ) (HM μ).N k) from rfl, hell]
  exact le_trans (Work.BoseB7AK.W1rows.abs_chat_le_integral_abs _)
    (Work.BoseB7AK.W1rows.W1omega_abs_integral_le hR hℓ (fun x => hv x) hvrad hv_supp h hRℓ)

/-- **The `Ŵ₁ω(0)`-mass row.**  `Ŵ₁ω(0) = ∫W₁ω ≤ 16π·(a v)`. -/
lemma honestFam_W1omega0_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0)
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    (HonestBoxFam v h fc fu HM μ).E.W1omega0 ≤ 16 * Real.pi * BoseGases.a v := by
  rw [show (HonestBoxFam v h fc fu HM μ).E.W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v)))
          0 from rfl]
  exact le_trans (le_trans (le_abs_self _) (Work.BoseB7AK.W1rows.abs_chat_le_integral_abs 0))
    (Work.BoseB7AK.W1rows.W1omega_abs_integral_le hR hℓ (fun x => hv x) hvrad hv_supp h hRℓ)

/-- **The `𝓜`-row.**  `𝓜 ≤ μℓ³`: `𝓜 = K_M t^{-1/4} = t^{-327/1292}` and
`μℓ³ = t^{-166/323} = t^{-664/1292}`, so the comparison is the exponent
inequality `-327/1292 ≥ -664/1292` at `t ≤ 1`. -/
lemma honestFam_bigM_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (ht1 : μ * BoseGases.a v ^ 3 ≤ 1) :
    (HonestBoxFam v h fc fu HM μ).E.bigM
      ≤ μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 := by
  have ht0 : (0 : ℝ) < μ * BoseGases.a v ^ 3 := by positivity
  have hker : Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
        * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ))
      ≤ Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-166) := by
    rw [Work.BoseBox.fsXp, Work.BoseBox.fsXp, ← Real.rpow_add ht0]
    apply Real.rpow_le_rpow_of_exponent_ge ht0 ht1
    norm_num
  have hM : Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
      = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
        * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ)) := rfl
  have hell : μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
      = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-166) :=
    Work.BoseFixB1.mu_ell_cube_eq hav hμ
  calc (HonestBoxFam v h fc fu HM μ).E.bigM
      = Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ := rfl
    _ = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
        * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ)) := hM
    _ ≤ Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-166) := hker
    _ = μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := hell.symm
    _ = μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 := rfl

/-- **The `ℓ^{-3}`-row.**  `ℓ^{-3} ≤ μ` from `1 ≤ μℓ³` (`ℓ > 0`). -/
lemma honestFam_ell_inv_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (h1 : 1 ≤ μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3) :
    (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) ≤ μ := by
  have hℓ : 0 < (HonestBoxFam v h fc fu HM μ).E.ell :=
    honestEnvFam_ell_pos v h fc fu HM hμ hav
  have hh : (1 : ℝ) ≤ μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 := by
    rw [show (HonestBoxFam v h fc fu HM μ).E.ell
        = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl]
    exact h1
  rw [Real.rpow_neg hℓ.le]
  refine (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hℓ 3)).mpr ?_
  simpa using hh

/-! ## 2. The regime lemma -/

theorem honestEnvNumeric (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → EnvFactsAt v h fc fu HM μ C := by
  obtain ⟨ε, hεpos, hε⟩ := Work.BoseFixR.WindowRegime h hv hv1 hvrad hR hv_supp hav
  refine ⟨min ε 1, max 1 (16 * Real.pi), lt_min hεpos one_pos,
    le_trans zero_le_one (le_max_left 1 (16 * Real.pi)), ?_⟩
  intro μ hAdm
  obtain ⟨hμ, htε, hOK⟩ := hAdm
  have hAdmε : Work.BoseBoxFix.Adm v ε μ := ⟨hμ, le_trans htε (min_le_left ε 1), hOK⟩
  obtain ⟨hRℓ, h157, -, -⟩ := hε μ hAdmε
  have ht1 : μ * BoseGases.a v ^ 3 ≤ 1 := le_trans htε (min_le_right ε 1)
  have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    have hh := honestEnvFam_ell_pos v h fc fu HM hμ hav
    rwa [show (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v)
      from rfl] at hh
  have hellpos : 0 < (HonestBoxFam v h fc fu HM μ).E.ell :=
    honestEnvFam_ell_pos v h fc fu HM hμ hav
  have h157' : (1 : ℝ) ≤ μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 := by linarith
  have hW0 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0 :=
    honestEnvFam_W1omega0_nonneg v h hR hv hvrad hv_supp fc fu HM μ
  obtain ⟨hτ, hχ, hW1p, hWωp⟩ := honestEnvFam_parity v h fc fu HM μ
  refine ⟨hellpos, rfl, rfl, ?_, ?_, ?_, ?_, ?_, hW0, ?_, ?_, ?_, hW1p, hWωp, hτ, hχ⟩
  · -- `1 ≤ μℓ³`
    rw [show (HonestBoxFam v h fc fu HM μ).E.ell = Work.BoseBox.sideAt μ (BoseGases.a v)
      from rfl]
    linarith
  · -- `ℓ^{-3} ≤ Cμ`
    exact le_trans (honestFam_ell_inv_le v h fc fu HM hμ hav h157')
      (le_mul_of_one_le_left hμ.le (le_max_left 1 (16 * Real.pi)))
  · -- `𝓜 ≤ Cμℓ³`
    refine le_trans (honestFam_bigM_le v h fc fu HM hμ hav ht1) ?_
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hμ.le (le_max_left 1 (16 * Real.pi))) (pow_nonneg hellpos.le 3)
  · -- `|Ŵ₁(k)| ≤ Ca`
    intro k
    exact le_trans (honestFam_W1_abs_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos k)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `|Ŵ₁ω(k)| ≤ Ca`
    intro k
    exact le_trans (honestFam_W1omega_abs_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos k)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `Ŵ₁ω(0) ≤ Ca`
    exact le_trans (honestFam_W1omega0_le v h hv hvrad hR hv_supp hav fc fu HM hRℓ hℓpos)
      (mul_le_mul_of_nonneg_right (le_max_right 1 (16 * Real.pi)) hav.le)
  · -- `Ŵ₁ω(0) = Ŵ₁ω(0)` (the two definitions of the zero mode)
    exact honestEnvFam_W1omega_zero_eq v h fc fu HM μ
  · -- `0 ≤ cHCF E (8π·(a v))`
    exact cHCF_nonneg (HonestBoxFam v h fc fu HM μ).E v hellpos hW0 hav

end Work.BoseBoxFock
