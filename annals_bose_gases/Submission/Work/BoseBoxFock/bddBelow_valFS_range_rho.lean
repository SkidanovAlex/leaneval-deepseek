import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.KzBogFS_window_ge_env
import Submission.Work.BoseBoxFock.Q2ex_window_ge_env
import Submission.Work.BoseBoxFock.Q3T_window_ge_env
import Submission.Work.BoseBoxFock.linOpT_window_ge_env
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bddBelow_valFS_range_rho`

`valFS ρ` is the infimum of the Rayleigh quotient of FS's substituted Hamiltonian
`KzOpFS ρ` over FS's spectral window `1_{[0,𝓜]}(n₊)`.  This file proves that
`ρ ↦ valFS ρ` is bounded below on `ρ ≥ 0`, so that `⨅_{ρ ≥ 0} valFS ρ` is not the
junk value `0` (`ciInf_le` at a single `ρ` is the only way to compare it with a
definite number, e.g. in `model_kafz`).

## The bound

Every row of `KzOpFS ρ` is bounded below by `-C·(1+ρ^{3/2})·‖g‖²` on the window
(`genv ρ = 1 + √ρ·ρ`), by

* `gap_row_env`, `NH_row_env` — the `ρ`-independent gap rows `(b/2ℓ²)n₊`,
  `(ε_Tb/2d²ℓ²)n₊^H`;
* `nPlus_row_env` — the row `((ρ−μ)Ŵ₁(0))n₊`;
* `KzBogFS_window_ge_env`, `linOpT_window_ge_env`, `Q2ex_window_ge_env`,
  `Q3T_window_ge_env` — the four genuinely `ρ`-dependent rows;

while the `c`-number row is *exactly*
`[½ℓ³(ĝ(0)+Ŵ₁ω(0))ρ² − μℓ³ĝ(0)ρ]·‖g‖²`, with positive leading coefficient
(`0 < ℓ` and `ĝ(0) = 8π·a v > 0`).  Summing, `valFS ρ ≥ aρ² − bρ − C(1+ρ^{3/2})`
with `a = ½ℓ³(ĝ(0)+Ŵ₁ω(0)) > 0`, and the right-hand side is bounded below on
`[0,∞)` because `ρ²` dominates `ρ^{3/2}` (`bddBelow_rhoPoly`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The scalar endgame -/

/-- The polynomial `t ↦ a t⁴ − b t³ − c t² − C(1 + t³)` on `t ≥ 0` is bounded below
when `a > 0`. -/
private lemma poly4_bddBelow (a bb C : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → K ≤ a * t ^ 4 - bb * t ^ 2 - C * (1 + t ^ 3) := by
  set D : ℝ := |bb| + |C| with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hDbb : |bb| ≤ D := by rw [hD]; linarith [abs_nonneg C]
  have hDC : |C| ≤ D := by rw [hD]; linarith [abs_nonneg bb]
  have hsq3 : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ 1 + t ^ 3 := by
    intro t ht
    rcases lt_or_ge t 1 with h | h
    · have h1 : t ^ 2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ t ^ 3 := pow_nonneg ht 3
      linarith
    · have h1 : t ^ 2 ≤ t ^ 3 := by nlinarith
      linarith
  have key : ∀ t : ℝ, 0 ≤ t →
      a * t ^ 4 - D * (1 + t ^ 3) ≤ a * t ^ 4 - bb * t ^ 2 - C * (1 + t ^ 3) := by
    intro t ht
    have h1 : bb * t ^ 2 ≤ |bb| * (1 + t ^ 3) := by
      have ha1 : bb * t ^ 2 ≤ |bb| * t ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self bb) (by positivity)
      have ha2 : |bb| * t ^ 2 ≤ |bb| * (1 + t ^ 3) :=
        mul_le_mul_of_nonneg_left (hsq3 t ht) (abs_nonneg bb)
      linarith
    have h2 : C * (1 + t ^ 3) ≤ |C| * (1 + t ^ 3) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith [hD]
  set T : ℝ := max 1 (D / a) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT2 : D / a ≤ T := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  refine ⟨-D * (1 + T ^ 3), fun t ht => ?_⟩
  have hkey := key t ht
  suffices hsuff : -D * (1 + T ^ 3) ≤ a * t ^ 4 - D * (1 + t ^ 3) by linarith
  rcases lt_or_ge t (D / a) with h | h
  · have htT : t ≤ T := le_trans (le_of_lt h) hT2
    have h7 : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht htT 3
    have ht4 : 0 ≤ a * t ^ 4 := mul_nonneg (le_of_lt ha) (pow_nonneg ht 4)
    have h8 : 0 ≤ D * t ^ 3 := mul_nonneg hD0 (pow_nonneg ht 3)
    nlinarith
  · have hDa : D ≤ a * t := by
      rw [div_le_iff₀ ha] at h; linarith
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
    have h4 : D * t ^ 3 ≤ a * t ^ 4 := by
      have h5 : D * t ^ 3 ≤ (a * t) * t ^ 3 := mul_le_mul_of_nonneg_right hDa ht3
      nlinarith
    have h6 : -D * (1 + T ^ 3) ≤ -D := by
      have h7 : 0 ≤ D * T ^ 3 := mul_nonneg hD0 (pow_nonneg hT0 3)
      nlinarith
    linarith

/-- For `a > 0`: `ρ ↦ aρ² − bρ − C(1 + ρ^{3/2})` is bounded below on `[0,∞)`. -/
private lemma bddBelow_rhoPoly (a bb C : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → K ≤ a * ρ ^ 2 - bb * ρ - C * genv ρ := by
  obtain ⟨K, hK⟩ := poly4_bddBelow a bb C ha
  refine ⟨K, fun ρ hρ => ?_⟩
  have ht : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hmm : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ
  have h2 : ρ ^ 2 = (Real.sqrt ρ) ^ 4 := by
    have : (Real.sqrt ρ * Real.sqrt ρ) ^ 2 = (Real.sqrt ρ) ^ 4 := by ring
    rwa [hmm] at this
  have h3 : Real.sqrt ρ * ρ = (Real.sqrt ρ) ^ 3 := by
    have : Real.sqrt ρ * (Real.sqrt ρ * Real.sqrt ρ) = (Real.sqrt ρ) ^ 3 := by ring
    rwa [hmm] at this
  have h4 : bb * ρ = bb * (Real.sqrt ρ) ^ 2 := by
    rw [show (Real.sqrt ρ) ^ 2 = ρ from Real.sq_sqrt hρ]
  rw [genv, h2, h3, h4]
  exact hK (Real.sqrt ρ) ht

/-! ## 2. The `ρ`-independent rows (and the number row) -/

/-- If `A ≥ 0` and `W ≥ 0` then `-(A·genv ρ)·W ≤ -A·W`. -/
private lemma env_coef_le (A W ρ : ℝ) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    -(A * genv ρ) * W ≤ -A * W := by
  have h1 : (1 : ℝ) ≤ genv ρ := one_le_genv ρ
  have h2 : A ≤ A * genv ρ := by
    have := mul_nonneg hA (by linarith : (0 : ℝ) ≤ genv ρ - 1)
    nlinarith [this]
  have h3 := mul_le_mul_of_nonneg_right h2 hW
  linarith [h3]

/-- The gap row `c • T.N`: bounded below by `-(|c|·M)·genv ρ·‖g‖²`. -/
private lemma gap_row_env (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (c M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, ∀ g : F.H, T.NWindow M g →
      -(C * genv ρ) * F.normSq g ≤ c * F.qw g T.N := by
  refine ⟨|c| * M, mul_nonneg (abs_nonneg c) hM, fun ρ g hg => ?_⟩
  have hcM : 0 ≤ |c| * M := mul_nonneg (abs_nonneg c) hM
  have h1 : -(|c| * M) * F.normSq g ≤ c * F.qw g T.N :=
    neg_abs_mul_le_smul (T.N_nonneg g) (Work.BoseB7A.NWindow_bp_N_le F T hM hg)
      (mul_nonneg hM (F.normSq_nonneg g))
  have h2 : -(|c| * M * genv ρ) * F.normSq g ≤ -(|c| * M) * F.normSq g :=
    env_coef_le (|c| * M) (F.normSq g) ρ hcM (F.normSq_nonneg g)
  linarith

/-- The `n₊^H` row `c • T.NH`: bounded below by `-(|c|·KNH)·genv ρ·‖g‖²`. -/
private lemma NH_row_env (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (c KNH M : ℝ) (hM : 0 ≤ M) (hKNH : 0 ≤ KNH)
    (hNH : ∀ g : F.H, T.NWindow M g → F.bp (T.NH g) g ≤ KNH * F.normSq g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, ∀ g : F.H, T.NWindow M g →
      -(C * genv ρ) * F.normSq g ≤ c * F.qw g T.NH := by
  refine ⟨|c| * KNH, mul_nonneg (abs_nonneg c) hKNH, fun ρ g hg => ?_⟩
  have hcK : 0 ≤ |c| * KNH := mul_nonneg (abs_nonneg c) hKNH
  have h1 : -(|c| * KNH) * F.normSq g ≤ c * F.qw g T.NH :=
    neg_abs_mul_le_smul (T.NH_nonneg g) (hNH g hg) (mul_nonneg hKNH (F.normSq_nonneg g))
  have h2 : -(|c| * KNH * genv ρ) * F.normSq g ≤ -(|c| * KNH) * F.normSq g :=
    env_coef_le (|c| * KNH) (F.normSq g) ρ hcK (F.normSq_nonneg g)
  linarith

/-- The number row `((ρ−μ)Ŵ₁(0)) · n₊`: bounded below by `-(C·genv ρ)‖g‖²`. -/
private lemma nPlus_row_env (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (Cn M : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : F.H, T.NWindow M g →
      -(C * genv ρ) * F.normSq g
        ≤ ((ρ - E.mu) * E.W1 0) * (∑ k : Mode, F.qw g (F.nOp k)) := by
  refine ⟨2 * (1 + |E.mu|) * |E.W1 0| * (Cn * M), by positivity, fun ρ hρ g hg => ?_⟩
  set S : ℝ := ∑ k : Mode, F.qw g (F.nOp k) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun k _ => by
      rw [← normSq_a_eq_qw_nOp F k g]; exact F.bp_nonneg _
  have hSle : S ≤ Cn * M * F.normSq g := by
    rw [hS]
    exact sum_qw_nOp_le F T hM hCn0 hBessel hg
  have hQ0 : 0 ≤ F.normSq g := F.normSq_nonneg g
  have hCnM : 0 ≤ Cn * M := mul_nonneg hCn0 hM
  have hW0 : 0 ≤ |E.W1 0| := abs_nonneg _
  have hA0 : 0 ≤ 1 + |E.mu| := by positivity
  have habs : |ρ - E.mu| ≤ (1 + |E.mu|) * (1 + ρ) := by
    have h1 : |ρ - E.mu| ≤ ρ + |E.mu| := by
      rw [abs_sub_le_iff]; constructor <;> linarith [le_abs_self E.mu, neg_abs_le E.mu]
    nlinarith [abs_nonneg E.mu, hρ]
  have h2 : (1 : ℝ) + ρ ≤ 2 * genv ρ := by
    have h3 : ρ ≤ genv ρ := self_le_genv hρ
    have h4 : 1 ≤ genv ρ := one_le_genv ρ
    linarith
  have hcoef : |(ρ - E.mu) * E.W1 0| * (Cn * M)
      ≤ (2 * (1 + |E.mu|) * |E.W1 0| * (Cn * M)) * genv ρ := by
    rw [abs_mul]
    have hW0M : 0 ≤ |E.W1 0| * (Cn * M) := mul_nonneg hW0 hCnM
    have hA : |ρ - E.mu| * |E.W1 0| * (Cn * M)
        ≤ ((1 + |E.mu|) * (1 + ρ)) * |E.W1 0| * (Cn * M) := by
      nlinarith [mul_le_mul_of_nonneg_right habs hW0M]
    have hB : ((1 + |E.mu|) * (1 + ρ)) * |E.W1 0| * (Cn * M)
        ≤ ((1 + |E.mu|) * (2 * genv ρ)) * |E.W1 0| * (Cn * M) := by
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2 hA0) hW0M]
    calc |ρ - E.mu| * |E.W1 0| * (Cn * M)
        ≤ ((1 + |E.mu|) * (1 + ρ)) * |E.W1 0| * (Cn * M) := hA
      _ ≤ ((1 + |E.mu|) * (2 * genv ρ)) * |E.W1 0| * (Cn * M) := hB
      _ = (2 * (1 + |E.mu|) * |E.W1 0| * (Cn * M)) * genv ρ := by ring
  have hstep1 : -(2 * (1 + |E.mu|) * |E.W1 0| * (Cn * M) * genv ρ) * F.normSq g
      ≤ -(|(ρ - E.mu) * E.W1 0| * (Cn * M)) * F.normSq g := by
    have := mul_le_mul_of_nonneg_right hcoef hQ0
    linarith [neg_le_neg this]
  have hstep2 : -(|(ρ - E.mu) * E.W1 0| * (Cn * M)) * F.normSq g
      ≤ -|(ρ - E.mu) * E.W1 0| * S := by
    have h := mul_le_mul_of_nonpos_left hSle
      (neg_nonpos.mpr (abs_nonneg ((ρ - E.mu) * E.W1 0)))
    linarith [h]
  have hstep3 : -|(ρ - E.mu) * E.W1 0| * S ≤ ((ρ - E.mu) * E.W1 0) * S :=
    mul_le_mul_of_nonneg_right (neg_abs_le _) hS0
  linarith

/-! ## 3. The assembly -/

/-- **The assembly.**  If every row of `KzOpFS ρ` is bounded below by `-Cᵢ·genv ρ·‖g‖²`
on the window (with `ρ`-independent constants) and the `c`-number coefficient is
positive, then `valFS` is bounded below on `ρ ≥ 0`. -/
private lemma valFS_bddBelow_of_rows (D : Work.BoseFixR.KzDatum) (M Cn KNH : ℝ)
    (hM0 : 0 ≤ M) (hCn0 : 0 ≤ Cn) (hKNH : 0 ≤ KNH) (hbig : D.E.bigM ≤ M)
    (hell : 0 < D.E.ell) (hg0 : 0 < D.gHat0) (hw0 : 0 ≤ D.E.W1omega0)
    (hBessel : ∀ f : D.F.H, D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f ≤ Cn * D.F.bp (D.T.N f) f)
    (hNH : ∀ f : D.F.H, D.T.NWindow M f → D.F.bp (D.T.NH f) f ≤ KNH * D.F.normSq f)
    (cBog cQ3T cLin cQ2ex : ℝ) (hcBog : 0 ≤ cBog) (hcQ3T : 0 ≤ cQ3T) (hcLin : 0 ≤ cLin)
    (hcQ2ex : 0 ≤ cQ2ex)
    (hBog : ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : D.F.H, D.T.NWindow M g →
      -(cBog * genv ρ) * D.F.normSq g ≤ D.F.qw g (KzBogFS D.F D.E ρ))
    (hQ3T : ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : D.F.H, D.T.NWindow M g →
      -(cQ3T * genv ρ) * D.F.normSq g ≤ D.F.qw g (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)))
    (hLin : ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : D.F.H, D.T.NWindow M g →
      -(cLin * genv ρ) * D.F.normSq g ≤ D.F.qw g (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ)))
    (hQ2ex : ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : D.F.H, D.T.NWindow M g →
      -(cQ2ex * genv ρ) * D.F.normSq g ≤ D.F.qw g (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))) :
    BddBelow (Set.range (fun ρ : {ρ : ℝ // 0 ≤ ρ} => D.valFS ρ.1)) := by
  obtain ⟨C1, hC1, hgap⟩ := gap_row_env D.F D.T (D.E.b / (2 * D.E.ell ^ 2)) M hM0
  obtain ⟨C2, hC2, hNHrow⟩ :=
    NH_row_env D.F D.T (D.E.eT * D.E.b / (2 * D.E.d ^ 2 * D.E.ell ^ 2)) KNH M hM0 hKNH hNH
  obtain ⟨C3, hC3, hnPlus⟩ := nPlus_row_env D.F D.T D.E Cn M hM0 hCn0 hBessel
  set a : ℝ := (1 / 2) * D.E.ell ^ 3 * (D.gHat0 + D.E.W1omega0) with ha
  set bb : ℝ := D.E.mu * D.E.ell ^ 3 * D.gHat0 with hbb
  have hapos : 0 < a := by
    rw [ha]
    have h1 : 0 < D.E.ell ^ 3 := by positivity
    have h2 : 0 < D.gHat0 + D.E.W1omega0 := by linarith
    positivity
  set Ctot : ℝ := C1 + C2 + C3 + cBog + cQ3T + cLin + cQ2ex with hCtot
  obtain ⟨K, hK⟩ := bddBelow_rhoPoly a bb Ctot hapos
  refine ⟨min K 0, ?_⟩
  rintro y ⟨⟨ρ, hρ⟩, rfl⟩
  change min K 0 ≤ D.valFS ρ
  by_cases hne : Nonempty {f : D.F.H // D.T.NWindow D.E.bigM f ∧ f ≠ 0}
  · haveI := hne
    refine le_trans (min_le_left _ _) (le_ciInf (fun f => ?_))
    have hg : D.T.NWindow M f.1 := D.T.NWindow_mono f.2.1 hbig
    have hnn : 0 ≤ D.F.normSq f.1 := D.F.normSq_nonneg f.1
    have hpos : 0 < D.F.normSq f.1 :=
      lt_of_le_of_ne hnn (Ne.symm (fun hc => f.2.2 (D.F.bp_def f.1 hc)))
    rw [le_div_iff₀ hpos]
    have hscal : K ≤ a * ρ ^ 2 - bb * ρ - Ctot * genv ρ := hK ρ hρ
    have hrow : (a * ρ ^ 2 - bb * ρ - Ctot * genv ρ) * D.F.normSq f.1
        ≤ D.F.qw f.1 (KzOpFS D.F D.T D.E D.gHat0 ρ) := by
      have e1 := hgap ρ f.1 hg
      have e2 := hNHrow ρ f.1 hg
      have e3 := hnPlus ρ hρ f.1 hg
      have e4 := hBog ρ hρ f.1 hg
      have e5 := hQ3T ρ hρ f.1 hg
      have e6 := hLin ρ hρ f.1 hg
      have e7 := hQ2ex ρ hρ f.1 hg
      have hexp : D.F.qw f.1 (KzOpFS D.F D.T D.E D.gHat0 ρ)
          = (D.E.b / (2 * D.E.ell ^ 2)) * D.F.qw f.1 D.T.N
            + (D.E.eT * D.E.b / (2 * D.E.d ^ 2 * D.E.ell ^ 2)) * D.F.qw f.1 D.T.NH
            + (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
                + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0
                + (1 / 2) * ρ ^ 2 * D.E.W1omega0)) * D.F.normSq f.1
            + D.F.qw f.1 (KzBogFS D.F D.E ρ)
            + ((ρ - D.E.mu) * D.E.W1 0) * (∑ k : D.Mode, D.F.qw f.1 (D.F.nOp k))
            + D.F.qw f.1 (D.T.linOpT (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw f.1 (D.F.Q2ex (Work.BoseFixR.KzEnvAt D.E ρ))
            + D.F.qw f.1 (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)) := by
        simp only [KzOpFS, Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_smul,
          qw_one, qw_finset_sum]
      have hcrow : (D.E.ell ^ 3 * (-(1 / 2) * D.E.mu ^ 2 * D.gHat0
            + (1 / 2) * (ρ - D.E.mu) ^ 2 * D.gHat0 + (1 / 2) * ρ ^ 2 * D.E.W1omega0))
            * D.F.normSq f.1
          = ((1 / 2) * D.E.ell ^ 3 * (D.gHat0 + D.E.W1omega0) * ρ ^ 2
              - (D.E.mu * D.E.ell ^ 3 * D.gHat0) * ρ) * D.F.normSq f.1 := by
        ring
      rw [ha, hbb, hCtot]
      linarith [hexp, hcrow, e1, e2, e3, e4, e5, e6, e7]
    have := mul_le_mul_of_nonneg_right hscal hnn
    linarith
  · haveI : IsEmpty {f : D.F.H // D.T.NWindow D.E.bigM f ∧ f ≠ 0} := not_nonempty_iff.mp hne
    have h0 : D.valFS ρ = 0 := by
      show Work.BoseBoxFock.KzValFS D.F D.T D.E D.gHat0 ρ = 0
      rw [KzValFS, iInf_of_isEmpty, Real.sInf_empty]
    rw [h0]
    exact min_le_right _ _

theorem bddBelow_valFS_range_rho (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ Kw Kχ : ℝ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hω0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hKχ : 0 ≤ Kχ)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ Kχ) :
    BddBelow (Set.range (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ.1)) := by
  let D : Work.BoseFixR.KzDatum := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ
  let M : ℝ := max D.E.bigM 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbig : D.E.bigM ≤ M := le_max_left _ _
  have hCn0 : (0 : ℝ) ≤ 48 / Real.pi := by positivity
  have hBessel : ∀ f : D.F.H,
      D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f ≤ (48 / Real.pi) * D.F.bp (D.T.N f) f :=
    fun f => Work.BoseBoxFock.bessel_honest v h fc fu HM μ f
  have hell : 0 < D.E.ell := by
    show 0 < Work.BoseBox.sideAt μ (BoseGases.a v)
    exact Work.BoseBox.sideAt_pos hμ hav
  have hg0 : 0 < D.gHat0 := by
    show 0 < 8 * Real.pi * BoseGases.a v
    positivity
  have hw0 : 0 ≤ D.E.W1omega0 := hω0
  have hNH : ∀ f : D.F.H, D.T.NWindow M f →
      D.F.bp (D.T.NH f) f ≤ ((1 / 32) * ((48 / Real.pi) * M)) * D.F.normSq f := by
    intro f hf
    have h1 : D.F.qw f D.T.NH
        ≤ (1 / 32) * D.F.qw f (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.nOp k) :=
      Work.BoseBoxFock.honest_NH_qw_le v h fc fu HM μ f
    have hsplit : D.F.qw f (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.nOp k)
        = ∑ k ∈ Work.BoseB7.excited D.Mode, D.F.qw f (D.F.nOp k) :=
      qw_finset_sum D.F f _ _
    have hsub : (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.qw f (D.F.nOp k))
        ≤ ∑ k : D.Mode, D.F.qw f (D.F.nOp k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x _ _ => by rw [← normSq_a_eq_qw_nOp]; exact D.F.bp_nonneg _)
    have hsum := sum_qw_nOp_le D.F D.T (M := M) hM0 hCn0 hBessel hf
    have h2 : D.F.qw f D.T.NH ≤ (1 / 32) * (∑ k : D.Mode, D.F.qw f (D.F.nOp k)) := by
      rw [hsplit] at h1
      linarith [h1, hsub]
    have h3 : (1 / 32) * (∑ k : D.Mode, D.F.qw f (D.F.nOp k))
        ≤ (1 / 32) * ((48 / Real.pi) * M * D.F.normSq f) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hone : D.F.bp (D.T.NH f) f = D.F.qw f D.T.NH := rfl
    rw [hone]
    nlinarith [h2, h3]
  obtain ⟨cBog, hcBog, hBog⟩ :=
    Work.BoseBoxFock.KzBogFS_window_ge_env D.F D.T D.E M (48 / Real.pi) hM0 hCn0 hBessel
  obtain ⟨cQ3T, hcQ3T, hQ3T⟩ :=
    Work.BoseBoxFock.Q3T_window_ge_env D.F D.T D.E M (48 / Real.pi) hM0 hCn0 hBessel
  obtain ⟨cLin, hcLin, hLin⟩ :=
    Work.BoseBoxFock.linOpT_window_ge_env D.F D.T D.E M hM0
  obtain ⟨cQ2ex, hcQ2ex, hQ2ex⟩ :=
    Work.BoseBoxFock.Q2ex_window_ge_env D.F D.T D.E (48 / Real.pi) M hM0 hCn0 hBessel
  exact Work.BoseBoxFock.valFS_bddBelow_of_rows D M (48 / Real.pi)
    ((1 / 32) * ((48 / Real.pi) * M)) hM0 hCn0 (by positivity) hbig hell hg0 hw0 hBessel hNH
    cBog cQ3T cLin cQ2ex hcBog hcQ3T hcLin hcQ2ex hBog hQ3T hLin hQ2ex

end Work.BoseBoxFock
