import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.viewFS_of_gate
import Submission.Work.BoseGateFS.TauRows
import Submission.Work.BoseRowsFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowsFS/honest_A_ge_AB.lean`

**The two mode-level `P_H` rows at the honest environment**, on the (weaker) `P_H`
region rather than the `P_H^q` region, and at the design's smallness threshold
`aK_H/(sℓ) ≤ 1/16`:

* `0 < 𝒜 k` and `2|ℬ k| ≤ 𝒜 k` for every `k` with `|k| ≥ (2K_Ha)⁻¹`, for every
  admissible density `ρ` (`|ρ − μ| ≤ μ/2`, which at `KzEnvAt E ρ` is exactly the
  `FSParamsView`'s `rho_close`).

The two ingredients are

1. `honE_W1_abs_le` — FS `eq:WSestimate`, `|Ŵ₁(k)| ≤ 16π(a v)`, at the honest
   environment (the UV cut is `≤ 1`, the régime `R ≤ ℓχ_{R₀}` is a hypothesis);
2. `arith_tauTilde_ge_PH` — the kinetic domination of the *smoothed* symbol
   `τ̃` on `P_H = {|k| ≥ (2K_Ha)⁻¹}` at the threshold `aK_H/(sℓ) ≤ 1/16`,
   i.e. `|k|²/2 + 3ρK₀a ≤ τ̃(k)`.  This is the variant of
   `Work.BoseGateFS.arith_tauTilde_ge_rho` adapted to the `P_H` region: halving
   the region's lower threshold pays for halving the smallness threshold (the
   kink gain needs `(sℓ)⁻¹ ≤ r/8`, and `r ≥ (2K_Ha)⁻¹` with `aK_H/(sℓ) ≤ 1/16`
   gives exactly that), while the potential allowance `3ρK₀a ≤ r²/8` follows
   from `r ≥ (2K_Ha)⁻¹` even more easily than from `r ≥ (4K_Ha)⁻¹` (it only
   needs `≤ r²/32`).

The assembly `A_ge_AB_of_PH` is the `P_H`-form of `Work.BoseGateFS.A_ge_of_taurad`
(the `A_ge`/`ABq` rows at `KzEnvAt E ρ`), with the additional strict positivity
`0 < 𝒜 k` that FS's Bogoliubov diagonalisation consumes.
-/

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

noncomputable section

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. The density at a `KzEnvAt` datum -/

/-- `ρ_z = ρ` at the `KzEnvAt` datum, for `ρ ≥ 0` and `ℓ > 0`. -/
lemma rho_KzEnvAt_RowsFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (KzEnvAt E ρ).rho = ρ := by
  rw [Q3Env.rho, KzEnvAt, Work.BoseB7.rhoZ]
  simp only []
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-! ## 2. FS `eq:WSestimate` at the honest environment -/

/-- **`|Ŵ₁(k)| ≤ 16π(a v)` at the honest environment** (`Ŵ₁ = ζ_{Λ_N}·Ŵ₁`):
the UV-cut profile is bounded by `1`, and the bare kernel obeys
`Work.BoseB7AK.W1rows.W1hat_abs_le` in the régime `R ≤ ℓ·χ_{R₀}`. -/
lemma honE_W1_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hrég : ∀ μ : ℝ, 0 < μ → R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (hμ : 0 < μ) :
    ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(honE v h fc fu HM μ).W1 k| ≤ 16 * Real.pi * (honE v h fc fu HM μ).aScat := by
  intro k
  rw [honE_W1_apply v h fc fu HM μ hμ hav k]
  have hb := Work.BoseB7AK.W1rows.W1hat_abs_le (v := v) (R := R)
    (ℓ := Work.BoseBoxFock.ellH v μ) hR (Work.BoseBoxFock.ellH_pos v μ)
    hv_nonneg hvrad hv_supp h (hrég μ hμ) ((honF v h fc fu HM μ).kmom k)
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

/-! ## 3. The kinetic domination of `τ̃` on `P_H` -/

/-- **The kinetic domination of the smoothed symbol `τ̃` on `P_H`.**

At FS's parameter point `FSParamsView E`, for `r ≥ (2K_Ha)⁻¹` and the design's
smallness `aK_H/(sℓ) ≤ 1/16`,

`r²/2 + 3ρK₀a ≤ (1−ε_T)(r−(sℓ)⁻¹)₊² + ε_T(r−(dsℓ)⁻¹)₊²`,

the right-hand side being the kinked lower bound of `τ̃` (`tauTilde_ge_kink`).
This differs from `Work.BoseGateFS.arith_tauTilde_ge_rho` only in the region's
threshold (`(2K_Ha)⁻¹` instead of `(4K_Ha)⁻¹`) and in the correspondingly weaker
smallness threshold (`1/16` instead of `1/32`). -/
lemma arith_tauTilde_ge_PH (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
      (E : Q3Env Mode) (hv : FSParamsView E) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 3 * E.mu / 2 → hv.t ≤ t₀ →
      E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 16 → ∀ r : ℝ,
      1 / (2 * E.KH * E.aScat) ≤ r →
        r ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤
          (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
            + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
  obtain ⟨t₀, ht₀pos, ht₀⟩ := Work.BoseK15.exists_tau_params K₀
  refine ⟨t₀, ht₀pos, ?_⟩
  intro Mode _ _ E hv ρ hρ0 hρub ht h16 r hr
  obtain ⟨heT, hKl⟩ := ht₀ E hv ht
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have heTnn : 0 ≤ E.eT := by rw [hv.eT_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have h1eT : 0 ≤ 1 - E.eT := by linarith
  have hrnn : 0 ≤ r := le_trans (by positivity) hr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  -- **Step 1: the kinetic threshold `(sℓ)⁻¹ ≤ r/8`.**
  have hx : (E.s * E.ell)⁻¹ ≤ r / 8 := by
    have hstep : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) ≤
        (1 / (E.aScat * E.KH)) * (1 / 16) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have hL : (1 / (E.aScat * E.KH)) * (E.aScat * E.KH / (E.s * E.ell)) =
        (E.s * E.ell)⁻¹ := by field_simp
    have hR : (1 / (E.aScat * E.KH)) * (1 / 16) = (1 / (2 * (E.KH * E.aScat))) / 8 := by
      field_simp
      ring
    rw [hL, hR] at hstep
    have h2 : 1 / (2 * (E.KH * E.aScat)) ≤ r := by
      have h3 : 1 / (2 * (E.KH * E.aScat)) = 1 / (2 * E.KH * E.aScat) := by
        simp only [mul_assoc]
      rw [h3]; exact hr
    linarith
  -- **Step 2: `τ̃(r) ≥ (49(1 − eT)/64)·r²`.**
  have hmax : 49 * r ^ 2 / 64 ≤ max (r - (E.s * E.ell)⁻¹) 0 ^ 2 :=
    Work.BoseK15.max_sq_lower hx hrnn
  have hRHS : 49 * (1 - E.eT) / 64 * r ^ 2 ≤
      (1 - E.eT) * max (r - (E.s * E.ell)⁻¹) 0 ^ 2
        + E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 := by
    have hA : (1 - E.eT) * (49 * r ^ 2 / 64) ≤
        (1 - E.eT) * (max (r - (E.s * E.ell)⁻¹) 0 ^ 2) :=
      mul_le_mul_of_nonneg_left hmax h1eT
    have hB : 0 ≤ E.eT * max (r - (E.d * E.s * E.ell)⁻¹) 0 ^ 2 :=
      mul_nonneg heTnn (sq_nonneg _)
    have hA' : (1 - E.eT) * (49 * r ^ 2 / 64) = 49 * (1 - E.eT) / 64 * r ^ 2 := by ring
    rw [hA'] at hA
    linarith
  -- **Step 3: the potential term is dominated.**
  have hLHS : r ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ 49 * (1 - E.eT) / 64 * r ^ 2 := by
    have hcoef : (5 / 8 : ℝ) ≤ 49 * (1 - E.eT) / 64 := by linarith
    have hcf : (5 / 8) * r ^ 2 ≤ 49 * (1 - E.eT) / 64 * r ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef hr2
    have hterm : 3 * ρ * K₀ * E.aScat ≤ r ^ 2 / 8 := by
      rcases le_or_gt K₀ 0 with hK | hK
      · have h3 : 3 * ρ * K₀ * E.aScat ≤ 0 := by
          have hpos : 0 ≤ 3 * ρ * E.aScat := by positivity
          nlinarith [hK, hpos]
        linarith
      · have hKA : E.mu * K₀ * E.aScat = K₀ * E.lille / (E.KH * E.aScat) ^ 2 := by
          rw [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
          field_simp
        have hlille_nn : 0 ≤ E.lille := by
          rw [Work.BoseB7.lille_val E hv]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
        have h4 : 1 ≤ r * (2 * E.KH * E.aScat) := by
          have h2 : 1 / (2 * (E.KH * E.aScat)) ≤ r := by
            have h3 : 1 / (2 * (E.KH * E.aScat)) = 1 / (2 * E.KH * E.aScat) := by
              simp only [mul_assoc]
            rw [h3]; exact hr
          have h5 : 1 / (2 * E.KH * E.aScat) ≤ r := hr
          rw [div_le_iff₀ (by positivity)] at h5
          linarith [h5]
        have h5 : 1 ≤ (r * (2 * E.KH * E.aScat)) ^ 2 := one_le_pow₀ h4
        have h5' : 1 ≤ 4 * r ^ 2 * (E.KH * E.aScat) ^ 2 := by nlinarith [h5]
        have hinv : 1 / (E.KH * E.aScat) ^ 2 ≤ 4 * r ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith [h5']
        have hle : 3 * ρ * K₀ * E.aScat ≤ (9 / 2) * (E.mu * K₀ * E.aScat) := by
          have h7 : 3 * ρ ≤ (9 / 2) * E.mu := by linarith
          have h8 : 3 * ρ * K₀ ≤ (9 / 2) * E.mu * K₀ :=
            mul_le_mul_of_nonneg_right h7 hK.le
          have h9 : 3 * ρ * K₀ * E.aScat ≤ (9 / 2) * E.mu * K₀ * E.aScat :=
            mul_le_mul_of_nonneg_right h8 ha.le
          linarith [h9]
        have hB : (9 / 2) * (E.mu * K₀ * E.aScat) ≤ r ^ 2 / 32 := by
          rw [hKA]
          have hnn : 0 ≤ (9 / 2) * (K₀ * E.lille) :=
            mul_nonneg (by norm_num) (mul_nonneg hK.le hlille_nn)
          calc (9 / 2) * (K₀ * E.lille / (E.KH * E.aScat) ^ 2)
              = (9 / 2) * (K₀ * E.lille) * (1 / (E.KH * E.aScat) ^ 2) := by ring
            _ ≤ (9 / 2) * (K₀ * E.lille) * (4 * r ^ 2) := mul_le_mul_of_nonneg_left hinv hnn
            _ ≤ (9 / 2) * (1 / 576) * (4 * r ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKl (by norm_num))
                  (by positivity)
            _ = r ^ 2 / 32 := by ring
        have hB' : (9 / 2) * (E.mu * K₀ * E.aScat) ≤ r ^ 2 / 8 := by
          have : r ^ 2 / 32 ≤ r ^ 2 / 8 := by linarith [hr2]
          linarith
        linarith
    linarith
  linarith

/-! ## 4. The two `P_H` rows at `KzEnvAt E ρ` -/

/-- **`0 < 𝒜` and `2|ℬ| ≤ 𝒜` on `P_H`**, from a kinetic domination of the symbol
on the same region.  The `P_H`-analogue of `Work.BoseGateFS.A_ge_of_taurad`, with
the strict positivity of `𝒜` that the Bogoliubov diagonalisation needs. -/
lemma A_ge_AB_of_PH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} {E : Q3Env Mode} {K₀ ρ : ℝ}
    (hW1 : ∀ k : Mode, |E.W1 k| ≤ K₀ * E.aScat) (hρ : 0 ≤ ρ) (hK₀ : 0 ≤ K₀)
    (ha : 0 ≤ E.aScat) (hX : 0 < E.KH * E.aScat)
    (htaurad : ∀ q : Mode, F.PH E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q) :
    (∀ q : Mode, F.PH E.KH E.aScat q → 0 < (KzEnvAt E ρ).A q) ∧
      (∀ q : Mode, F.PH E.KH E.aScat q →
        2 * |(KzEnvAt E ρ).B q| ≤ (KzEnvAt E ρ).A q) := by
  have hkey : ∀ q : Mode, F.PH E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 2 * ρ * K₀ * E.aScat ≤ (KzEnvAt E ρ).A q := by
    intro q hq
    have h1 := htaurad q hq
    have h2 := (abs_le.mp (hW1 q)).1
    have h4 : (KzEnvAt E ρ).A q = E.tau q + ρ * E.W1 q := rfl
    have h5 : ρ * (-(K₀ * E.aScat)) ≤ ρ * E.W1 q := mul_le_mul_of_nonneg_left h2 hρ
    rw [h4]
    linarith
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have h := hkey q hq
    have hq' : 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hq
    have hpos : 0 < 1 / (2 * E.KH * E.aScat) := by
      have h2 : 0 < 2 * (E.KH * E.aScat) := by linarith
      have h4 : 2 * (E.KH * E.aScat) = 2 * E.KH * E.aScat := by ring
      rw [← h4]
      exact one_div_pos.mpr h2
    have hnorm : 0 < ‖F.kmom q‖ := lt_of_lt_of_le hpos hq'
    have hsq : 0 < ‖F.kmom q‖ ^ 2 / 2 := by positivity
    have hnn : 0 ≤ 2 * ρ * K₀ * E.aScat := by
      have h2 := mul_nonneg (mul_nonneg hρ hK₀) ha
      linarith
    linarith
  · have h := hkey q hq
    have hA : (KzEnvAt E ρ).A q = E.tau q + ρ * E.W1 q := rfl
    have hB : (KzEnvAt E ρ).B q = ρ * E.W1 q := rfl
    rw [hA] at h
    have h3 : |ρ * E.W1 q| = ρ * |E.W1 q| := by rw [abs_mul, abs_of_nonneg hρ]
    rw [hB, h3]
    have h2 : ρ * (2 * |E.W1 q|) ≤ ρ * (2 * (K₀ * E.aScat)) :=
      mul_le_mul_of_nonneg_left (by linarith [hW1 q]) hρ
    nlinarith [h, h2]

/-! ## 5. The target -/

theorem honest_A_ge_AB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hrég : ∀ μ : ℝ, 0 < μ → R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ)
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)),
        0 < μ → 0 ≤ ρ → hvK.t ≤ t₀ →
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
  intro HM μ ρ hvK hμ hρ ht hsc
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
  -- ## the `Ŵ₁` bound
  have hW1le : ∀ k : Lab (HM μ).N,
      |(honE v h fc fu HM μ).W1 k| ≤ (16 * Real.pi) * (honE v h fc fu HM μ).aScat :=
    honE_W1_abs_le R hR hav hv_nonneg hvrad hv_supp hrég HM μ hμ
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
