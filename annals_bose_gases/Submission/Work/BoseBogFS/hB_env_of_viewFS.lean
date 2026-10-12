import ChallengeDeps
import Submission.Work.BoseBogFS.FsMatchEnvDefs
import Submission.Work.BoseBogFS.View
import Submission.Work.BoseBogFS.chat_zero_eq_integral
import Submission.Work.BoseGateFS.chat_W1fun_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.hB_env_of_viewFS` — the environment's `Ŵ₁` row at the view

Under `RViewFS` the environment's kernel is pinned to `E.W1 = ζ_Λ·Ŵ₁ ∘ F.kmom`, where
`Ŵ₁ = chat (W1fun v h (ell v μ))` is FS's renormalised one-body kernel and `ζ_Λ` is a
`LowCut`-cutoff (`0 ≤ ζ_Λ ≤ 1`).  This module proves the row

    `E.W1 k ≤ a v · (8π + 16π R √(ρ_z a v) · ‖modePos n (e k)‖)`    for every mode `k`,

i.e. FS's `eq:WSestimate` **with its `k`-dependence made explicit through the gain row
`hgain`**: the kernel is `8π(a v)` at the origin, Lipsschitz with constant
`16π R (a v)` (`Work.BoseGateFS.chat_W1fun_lipschitz`), and the excess of the mass
`Ŵ₁(0) = ∫W₁ ≤ 8π(a v)(1 + 2C(R/ℓ)²)` (the hypothesis `hmass`) over `8π(a v)` is
absorbed by the surplus `πσ/ℓ` in `hgain` against `C(R/ℓ) ≤ πσ` (`hsmall`).

## The chain

Writing `c = ζ_Λ(F.kmom k) ∈ [0,1]`, `Wk = Ŵ₁(F.kmom k)`, `W0 = Ŵ₁(0)`, `s = √(ρ_z a v)`,
`Nk = ‖modePos n (e k)‖` and `p = F.kmom k`:

* `E.W1 k = c·Wk ≤ max Wk 0` (for `c ∈ [0,1]`);
* `Wk ≤ W0 + 16π R (a v)‖p‖` (Lipschitz) and `W0 ≤ 8π(a v)(1 + 2C(R/ℓ)²)` (the mass row
  `hmass` through `chat 0 = ∫`);
* `hgain` gives `s·Nk ≥ ‖p‖ + πσ/ℓ`, so `C(R/ℓ)² + R‖p‖ ≤ R·s·Nk` (using
  `hsmall : C(R/ℓ) ≤ πσ`), which is exactly what turns the previous two rows into
  `≤ a v·(8π + 16π R s Nk)`.

Positivity of `a v` is *not* a hypothesis: `hgain` at the mode `k` forces
`s·Nk ≥ πσ/ℓ > 0`, hence `s > 0`, hence `ρ_z (a v) > 0` and `0 < a v` (`ρ_z > 0`).
-/

open scoped Real

set_option linter.unusedVariables false

namespace Work.BoseBogFS

/-- The UV cut-off factor `ζ_Λ(k) = f_u(‖k‖/Λ)` of `RViewFS` is nonnegative. -/
lemma uvCut_nonneg (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ)
    (k : EuclideanSpace ℝ (Fin 3)) : 0 ≤ uvCut fu Λ k := by
  rw [uvCut]
  rcases lt_or_ge (‖k‖ / Λ) 2 with h | h
  · have := fu.anti h.le
    rwa [fu.zero 2 le_rfl] at this
  · rw [fu.zero _ h]

/-- The UV cut-off factor `ζ_Λ(k) = f_u(‖k‖/Λ)` of `RViewFS` is at most `1`. -/
lemma uvCut_le_one (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ)
    (k : EuclideanSpace ℝ (Fin 3)) : uvCut fu Λ k ≤ 1 := by
  rw [uvCut]
  rcases lt_or_ge (‖k‖ / Λ) 1 with h | h
  · rw [fu.one _ h.le]
  · have := fu.anti h
    rwa [fu.one 1 le_rfl] at this

theorem hB_env_of_viewFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {gHat0 : ℝ} (hview : Work.BoseBogFS.RViewFS v h μ F T E gHat0)
    (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    {R r₁ C σ ρz : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hσ0 : 0 < σ) (hρz : 0 < ρz)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hreg : R / Work.BoseFixR.ell v μ ≤ r₁)
    (hcond : C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1 / 2)
    (hmass : ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) y
      ≤ 8 * π * _root_.BoseGases.a v * (1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2))
    (hsmall : C * (R / Work.BoseFixR.ell v μ) ≤ π * σ)
    {n : ℕ} (e : Mode → Work.BoseB6Est.modeIdx n)
    (hgain : ∀ k : Mode, ‖F.kmom k‖ + π * σ / Work.BoseFixR.ell v μ
      ≤ Real.sqrt (ρz * _root_.BoseGases.a v)
          * Submission.BoseGases.eucNorm3 (Work.BoseB6Est.modePos n (e k))) :
    ∀ k : Mode, E.W1 k
      ≤ _root_.BoseGases.a v * (8 * π + 16 * π * R * Real.sqrt (ρz * _root_.BoseGases.a v)
          * Submission.BoseGases.eucNorm3 (Work.BoseB6Est.modePos n (e k))) := by
  classical
  -- the `Ŵ₁` pin of the view
  obtain ⟨fu, Λ, -, hW1eq⟩ := hview.W1_pin
  -- the healing length is positive: `0 < R ≤ ℓ·χR0` and `0 < χR0`
  have hχ0 : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ : 0 < Work.BoseFixR.ell v μ := by
    by_contra hcon
    push Not at hcon
    have hmul : Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon hχ0.le
    linarith
  -- `W₁` is integrable in the dilute regime, so `Ŵ₁(0) = ∫W₁`
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) := by
    exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  intro k
  set s : ℝ := Real.sqrt (ρz * _root_.BoseGases.a v) with hs
  set Nk : ℝ := Submission.BoseGases.eucNorm3 (Work.BoseB6Est.modePos n (e k)) with hNk
  set Wk : ℝ := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
    (F.kmom k) with hWk
  set W0 : ℝ := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) 0 with hW0
  -- the gain row at `k`
  have hgaink : ‖F.kmom k‖ + π * σ / Work.BoseFixR.ell v μ ≤ s * Nk := by
    have h := hgain k
    simpa only [← hs, ← hNk] using h
  -- positivity of `s`, hence of `a v`
  have hπσ : 0 < π * σ / Work.BoseFixR.ell v μ := div_pos (mul_pos Real.pi_pos hσ0) hℓ
  have hsN : 0 < s * Nk := by
    linarith [hgaink, norm_nonneg (F.kmom k)]
  have hNknn : 0 ≤ Nk := by
    rw [hNk]
    exact Submission.BoseGases.eucNorm3_nonneg _
  have hs_pos : 0 < s := by
    by_contra hcon
    push Not at hcon
    have : s * Nk ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hNknn
    linarith
  have hav : 0 < _root_.BoseGases.a v := by
    have hρza : 0 < ρz * _root_.BoseGases.a v := by
      rw [hs] at hs_pos
      exact Real.sqrt_pos.mp hs_pos
    exact pos_of_mul_pos_right hρza hρz.le
  -- the Lipschitz row `|Ŵ₁(k) − Ŵ₁(0)| ≤ 16π R (a v)‖k‖`
  have hLip := Work.BoseGateFS.chat_W1fun_lipschitz (v := v) (h := h) (R := R)
    (ℓ := Work.BoseFixR.ell v μ) hR hℓ hv hvrad hv_supp hRℓ (F.kmom k) 0
  have hWk_le : Wk ≤ W0 + 16 * π * R * _root_.BoseGases.a v * ‖F.kmom k‖ := by
    have h := (abs_le.mp hLip).2
    rw [← hWk, ← hW0] at h
    simp only [sub_zero] at h
    linarith
  -- the mass row at `W0`
  have hW0up : W0 ≤ 8 * π * _root_.BoseGases.a v
      * (1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2) := by
    rw [hW0, chat_zero_eq_integral _ hWint]
    exact hmass
  -- the arithmetic core: `C(R/ℓ)² + R‖p‖ ≤ R·s·Nk`
  have hd : 0 < R / Work.BoseFixR.ell v μ := div_pos hR hℓ
  have hCN : C * (R / Work.BoseFixR.ell v μ) ^ 2 + R * ‖F.kmom k‖ ≤ R * (s * Nk) := by
    have h1 : C * (R / Work.BoseFixR.ell v μ) ^ 2
        ≤ π * σ * (R / Work.BoseFixR.ell v μ) := by
      have h := mul_le_mul_of_nonneg_right hsmall hd.le
      nlinarith [h]
    have h2 : R * (‖F.kmom k‖ + π * σ / Work.BoseFixR.ell v μ) ≤ R * (s * Nk) :=
      mul_le_mul_of_nonneg_left hgaink hR.le
    have h3 : R * (π * σ / Work.BoseFixR.ell v μ)
        = π * σ * (R / Work.BoseFixR.ell v μ) := by ring
    nlinarith [h1, h2, h3]
  -- the right-hand side is nonnegative
  have hRHSnn : 0 ≤ _root_.BoseGases.a v * (8 * π + 16 * π * R * s * Nk) := by
    have h1 : 0 ≤ 16 * π := mul_nonneg (by norm_num) Real.pi_pos.le
    have h2 : 0 ≤ 16 * π * R := mul_nonneg h1 hR.le
    have h3 : 0 ≤ 16 * π * R * s := mul_nonneg h2 (le_of_lt hs_pos)
    have h16 : 0 ≤ 16 * π * R * s * Nk := mul_nonneg h3 hNknn
    have : 0 ≤ 8 * π + 16 * π * R * s * Nk := by linarith [Real.pi_pos]
    exact mul_nonneg hav.le this
  -- assemble
  have hstep : W0 + 16 * π * R * _root_.BoseGases.a v * ‖F.kmom k‖
      ≤ _root_.BoseGases.a v * (8 * π + 16 * π * R * s * Nk) := by
    have h16av : 0 ≤ 16 * π * _root_.BoseGases.a v :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav.le
    have hCN' := mul_le_mul_of_nonneg_left hCN h16av
    calc W0 + 16 * π * R * _root_.BoseGases.a v * ‖F.kmom k‖
        ≤ 8 * π * _root_.BoseGases.a v * (1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2)
            + 16 * π * R * _root_.BoseGases.a v * ‖F.kmom k‖ := by linarith [hW0up]
      _ = 8 * π * _root_.BoseGases.a v
            + 16 * π * _root_.BoseGases.a v
              * (C * (R / Work.BoseFixR.ell v μ) ^ 2 + R * ‖F.kmom k‖) := by ring
      _ ≤ 8 * π * _root_.BoseGases.a v
            + 16 * π * _root_.BoseGases.a v * (R * (s * Nk)) := by linarith [hCN']
      _ = _root_.BoseGases.a v * (8 * π + 16 * π * R * s * Nk) := by ring
  have hWk_final : Wk ≤ _root_.BoseGases.a v * (8 * π + 16 * π * R * s * Nk) :=
    le_trans hWk_le hstep
  have hEW1 : E.W1 k = uvCut fu Λ (F.kmom k) * Wk := by
    simp only [hW1eq, ← hWk]
  have hmain : E.W1 k ≤ max Wk 0 := by
    rw [hEW1]
    rcases lt_or_ge 0 Wk with h | h
    · calc uvCut fu Λ (F.kmom k) * Wk ≤ 1 * Wk :=
            mul_le_mul_of_nonneg_right (uvCut_le_one fu Λ (F.kmom k)) h.le
        _ = Wk := one_mul Wk
        _ ≤ max Wk 0 := le_max_left _ _
    · calc uvCut fu Λ (F.kmom k) * Wk ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (uvCut_nonneg fu Λ (F.kmom k)) h
        _ ≤ max Wk 0 := le_max_right _ _
  exact le_trans hmain (max_le hWk_final hRHSnn)

end Work.BoseBogFS
