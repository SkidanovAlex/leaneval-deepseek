import ChallengeDeps
import Submission.Work.BoseRowsFS.honest_A_ge_AB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- **`|Ŵ₁(k)| ≤ 16π(a v)` at the honest environment, pointwise in `μ`.**

This is `Work.BoseRowsFS.honE_W1_abs_le` with its *global* régime hypothesis
`∀ μ, 0 < μ → R ≤ ℓ(μ)χ_{R₀}` replaced by the single instance at the `μ` under
consideration: FS `eq:WSestimate` (`Work.BoseB7AK.W1rows.W1hat_abs_le`) is a
statement about one `ℓ`, so only that instance is ever consumed. -/
lemma honE_W1_abs_le_at {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hRchi : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(honE v h fc fu HM μ).W1 k| ≤ 16 * Real.pi * (honE v h fc fu HM μ).aScat := by
  intro k
  rw [honE_W1_apply v h fc fu HM μ hμ hav k]
  have hb := Work.BoseB7AK.W1rows.W1hat_abs_le (v := v) (R := R)
    (ℓ := Work.BoseBoxFock.ellH v μ) hR (Work.BoseBoxFock.ellH_pos v μ)
    hv_nonneg hvrad hv_supp h hRchi ((honF v h fc fu HM μ).kmom k)
  have hζ : |uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
      ((honF v h fc fu HM μ).kmom k)| ≤ 1 := by
    have h0 : 0 ≤ uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        ((honF v h fc fu HM μ).kmom k) := Work.BoseBoxFix.LowCut.nonneg fu _
    have h1 : uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        ((honF v h fc fu HM μ).kmom k) ≤ 1 := Work.BoseBoxFix.LowCut.le_one fu _
    rw [abs_le]
    exact ⟨by linarith, h1⟩
  calc |uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k)
        * chat (W1fun v h (Work.BoseBoxFock.ellH v μ)) ((honF v h fc fu HM μ).kmom k)|
      = |uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k)|
        * |chat (W1fun v h (Work.BoseBoxFock.ellH v μ))
            ((honF v h fc fu HM μ).kmom k)| := abs_mul _ _
    _ ≤ 1 * (16 * Real.pi * _root_.BoseGases.a v) :=
        mul_le_mul hζ hb (abs_nonneg _) (by norm_num)
    _ = 16 * Real.pi * (honE v h fc fu HM μ).aScat := by rw [one_mul]; rfl

theorem honest_A_ge_AB_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ)
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)),
        0 < μ → R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 → 0 ≤ ρ →
        hvK.t ≤ t₀ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).PH
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
            0 < (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k)
        ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).PH
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
            2 * |(Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).B k|
              ≤ (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k) := by
  classical
  obtain ⟨t₀, ht₀pos, ht₀⟩ := arith_tauTilde_ge_PH (16 * Real.pi) (by positivity)
  refine ⟨min t₀ 1, lt_min ht₀pos one_pos, ?_⟩
  intro HM μ ρ hvK hμ hRchi hρ ht hsc
  -- ## the dilute range `μa³ ≤ 1`, hence the honest view
  have ht1 : hvK.t ≤ 1 := le_trans ht (min_le_right _ _)
  have hμa1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := by
    have hmueq := hvK.mu_eq
    have hE : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).mu = μ := rfl
    have hA : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).aScat = _root_.BoseGases.a v :=
      rfl
    rw [hE, hA] at hmueq
    rw [hmueq]
    exact ht1
  have hv : FSParamsView (honE v h fc fu HM μ) :=
    (Work.BoseBoxFock.nonempty_fsParamsView_HonestBoxFam (HM := HM) (μ := μ) hμ hav hμa1).some
  -- ## positivity of the parameters
  have hℓE : 0 < (honE v h fc fu HM μ).ell := Work.BoseB7.ell_pos _ hv
  have hX : 0 < (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat :=
    mul_pos (lt_of_lt_of_le zero_lt_one hv.one_le_KH) hv.a_pos
  -- ## the density upper bound at `KzEnvAt`
  have hρE : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).rho = ρ :=
    rho_KzEnvAt_RowsFS _ hρ hℓE
  have hρub : ρ ≤ 3 * (honE v h fc fu HM μ).mu / 2 := by
    have hrc := hvK.rho_close
    have hmu : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).mu
        = (honE v h fc fu HM μ).mu := rfl
    rw [hρE, hmu] at hrc
    linarith [abs_le.mp hrc]
  -- ## the diluteness of the honest view
  have ht' : hv.t ≤ t₀ := by
    have h2 : hv.t = μ * (_root_.BoseGases.a v) ^ 3 := by
      have hh := hv.mu_eq
      have hE : (honE v h fc fu HM μ).mu = μ := rfl
      have hA : (honE v h fc fu HM μ).aScat = _root_.BoseGases.a v := rfl
      rw [hE, hA] at hh
      exact hh.symm
    have h3 : hvK.t = μ * (_root_.BoseGases.a v) ^ 3 := by
      have hh := hvK.mu_eq
      have hE : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).mu = μ := rfl
      have hA : (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ).aScat
          = _root_.BoseGases.a v := rfl
      rw [hE, hA] at hh
      exact hh.symm
    have h4 : hvK.t ≤ t₀ := le_trans ht (min_le_left _ _)
    linarith
  -- ## the `Ŵ₁` bound (FS `eq:WSestimate`, pointwise in `μ`)
  have hW1le : ∀ k : Lab (HM μ).N,
      |(honE v h fc fu HM μ).W1 k| ≤ (16 * Real.pi) * (honE v h fc fu HM μ).aScat :=
    honE_W1_abs_le_at R hR hav hv_nonneg hvrad hv_supp HM μ hμ hRchi
  -- ## the kinetic domination on `P_H`
  have hτdom : ∀ q : Lab (HM μ).N,
      (honF v h fc fu HM μ).PH (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
        ‖(honF v h fc fu HM μ).kmom q‖ ^ 2 / 2
          + 3 * ρ * (16 * Real.pi) * (honE v h fc fu HM μ).aScat
          ≤ (honE v h fc fu HM μ).tau q := by
    intro q hq
    have hq' : 1 / (2 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
        ≤ ‖(honF v h fc fu HM μ).kmom q‖ := by
      simpa only [FockData.PH] using hq
    have h1 := ht₀ (E := honE v h fc fu HM μ) hv ρ hρ hρub ht' hsc
      ‖(honF v h fc fu HM μ).kmom q‖ hq'
    have hφ : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
      fun r => Work.BoseBoxFock.tauProf_spec.2.2.1 r
    have heT0 : 0 ≤ (honE v h fc fu HM μ).eT := by
      rw [hv.eT_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
    have heT1 : (honE v h fc fu HM μ).eT ≤ 1 := by
      rw [hv.eT_eq]
      exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
    have hs0 : 0 < (honE v h fc fu HM μ).s := by
      rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
    have hd0 : 0 < (honE v h fc fu HM μ).d := by
      rw [hv.d_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
    have h2 := Work.BoseGateFS.tauTilde_ge_kink (φ := Work.BoseBoxFock.tauProf) hφ heT0 heT1
      hs0 hd0 hℓE ((honF v h fc fu HM μ).kmom q)
    have h4 : Work.BoseGateFS.tauTilde Work.BoseBoxFock.tauProf (honE v h fc fu HM μ).eT
        (honE v h fc fu HM μ).s (honE v h fc fu HM μ).d (honE v h fc fu HM μ).ell
        ((honF v h fc fu HM μ).kmom q) = (honE v h fc fu HM μ).tau q :=
      (honE_tau v h fc fu HM μ q).symm
    rw [h4] at h2
    linarith
  exact A_ge_AB_of_PH (F := honF v h fc fu HM μ) (E := honE v h fc fu HM μ)
    (K₀ := 16 * Real.pi) (ρ := ρ) hW1le hρ (by positivity) hv.a_pos.le hX hτdom

end

end Work.BoseRowsFS
