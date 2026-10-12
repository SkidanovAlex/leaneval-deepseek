import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.wLocG0MassBound
import Submission.Work.BoseBoxFock.frkD4Aux
import Submission.Work.BoseBoxFock.kinFormB_le_of_isLowB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.kinFormBLowParams` — the a-priori kinetic bound of a low box state,
at the parameter conditions `ParamsOK` alone

(The ancestor of this statement is `Work.BoseBoxFock.kinFormB_le_of_isLowB`, which reaches the same
conclusion from FS's *admissibility* bundle `Work.BoseBoxFix.Adm v ε₀ μ`.  That bundle carries two
independent things: the range condition `R ≤ ℓ·chiR0` — supplied here as a hypothesis, exactly as
in the sibling `Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair` — and the diluteness cap
`μ(a v)³ ≤ ε₀`.  This file shows that the diluteness cap is **not needed**: everything that uses it
in the old proof is either replaced by the unconditional one-body mass bound
`Work.AprioriCount.wLocG0MassBound`, or derived from the parameter conditions themselves.)

The target (FS `eq:aprioriPsi` ⟹ FS's a-priori kinetic bound): a low box state at FS's parameters
has `⟨kin⟩ ≲ (a v) μ² ℓ³ ‖Φ‖²`, with the constant *independent of the state*.

## The route (all inputs are PROVED corpus lemmas)

1. **The parameter conditions force the diluteness to be at most `1`**
   (`mu_mul_a_cube_le_one_of_paramsOK`): the first conjunct of `con:eTdK`,
   `(d K_ℓ)² ≤ ε_T K_ℓ^{-2}`, reads at `P = fsParams t`, `t = μ(a v)³` as the monomial comparison
   `t^{9/323} ≤ t^{(35/4)/323}` (the two `mon_*` normalisations below), i.e.
   `t^{1/1292} ≤ 1`, i.e. `t ≤ 1`.
2. **The low threshold is nonpositive** (`theta_nonpos_of_KB_cube`): from `J ≤ K_B³ = t^{-18/323}`
   and `t ≤ 1`, `J√(μ(a v)³) ≤ t^{287/646} ≤ 1`, so
   `Theta (a v) J μ = −4πμ²(a v)(1 − J√(μ(a v)³)) ≤ 0`.
3. **The box-word splitting** (`Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair`):
   `wordB = kinFormB − μ·potMass + pairPartB`, so with `pairPartB ≥ 0`
   (`Work.BoseFixB1B.pairPartB_nonneg`) and `wordB ≤ ℓ³·Theta·normB ≤ 0` (1 + 2),
   `kinFormB ≤ μ·potMass`.
4. **The one-body mass bound** (`Work.AprioriCount.wLocG0MassBound`, which needs *no* diluteness
   parameter, only the range condition): there is a fixed `K > 0` with
   `μ·potMass ≤ μ·K·n·normB`, and `n ≤ 2μℓ³` closes it:
   `kinFormB ≤ 2K·μ²·ℓ³·normB`.  Dividing by `(a v) > 0` gives the target's shape with
   `C = 2K/(a v)`.

Note the target's `hv`, `hv1`, `hvrad` enter only through `wLocG0MassBound` (via
`fibre_integral_abs_le`), and `hJ`/`hL` only through (2) and (3); no diluteness hypothesis is
needed anywhere.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseBoxFock.PCFU

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The monomial normalisations of `fsParams` -/

/-- `(fsParams t).d = X⁶` by definition. -/
lemma fsParams_d (t : ℝ) : (Work.BoseBox.fsParams t).d = Work.BoseBox.fsXp t 6 := rfl

/-- `(fsParams t).K_ℓ = X^{-3/2}` by definition. -/
lemma fsParams_Kl (t : ℝ) : (Work.BoseBox.fsParams t).Kl = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) :=
  rfl

/-- `(fsParams t).ε_T = X^{23/4}` by definition. -/
lemma fsParams_eT (t : ℝ) : (Work.BoseBox.fsParams t).eT = Work.BoseBox.fsXp t (23 / 4 : ℝ) :=
  rfl

/-- `(d K_ℓ)² = X^{9}` at FS's parameter choice. -/
lemma mon_dKl_sq {t : ℝ} (ht : 0 < t) :
    ((Work.BoseBox.fsParams t).d * (Work.BoseBox.fsParams t).Kl) ^ 2
      = Work.BoseBox.fsXp t 9 := by
  dsimp only [Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [← Real.rpow_add ht]
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  norm_num

/-- `ε_T K_ℓ^{-2} = X^{35/4}` at FS's parameter choice. -/
lemma mon_eT_Kl_inv_sq {t : ℝ} (ht : 0 < t) :
    (Work.BoseBox.fsParams t).eT * (Work.BoseBox.fsParams t).Kl ^ (-(2 : ℝ))
      = Work.BoseBox.fsXp t (35 / 4) := by
  dsimp only [Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [← Real.rpow_mul ht.le]
  rw [← Real.rpow_add ht]
  congr 1
  norm_num

/-! ## 2. The diluteness cap implied by the parameter conditions -/

/-- **`ParamsOK` forces the diluteness to be at most `1`.**

The parameter conditions of FS `sec:params` hold at the *concrete* choice `fsParams t`
(`Work.BoseB7.paramsOK_fsParams_le_one`), and the first conjunct of `con:eTdK` alone is already
incompatible with `t > 1`: `(d K_ℓ)² = X⁹` must be at most `ε_T K_ℓ^{-2} = X^{35/4}`, an inequality
opposite to the monotonicity of `X ↦ X^c` for `X > 1`. -/
lemma mu_mul_a_cube_le_one_of_paramsOK {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hOK : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ a) (μ * a ^ 3)) :
    μ * a ^ 3 ≤ 1 := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have h := hOK.eTdK.1
  dsimp only [Work.BoseBox.paramsAt] at h
  rw [mon_dKl_sq (t := μ * a ^ 3) ht, mon_eT_Kl_inv_sq (t := μ * a ^ 3) ht] at h
  dsimp only [Work.BoseBox.fsXp] at h
  -- `h : t^{9/323} ≤ t^{(35/4)/323}`, i.e. `t^{36/1292} ≤ t^{35/1292}`
  rw [show (9 : ℝ) / 323 = 36 / 1292 by norm_num,
    show ((35 : ℝ) / 4) / 323 = 35 / 1292 by norm_num] at h
  have hfac : (μ * a ^ 3) ^ (36 / 1292 : ℝ)
      = (μ * a ^ 3) ^ (35 / 1292 : ℝ) * (μ * a ^ 3) ^ (1 / 1292 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  rw [hfac] at h
  have hpos : 0 < (μ * a ^ 3) ^ (35 / 1292 : ℝ) := Real.rpow_pos_of_pos ht _
  have hle : (μ * a ^ 3) ^ (1 / 1292 : ℝ) ≤ 1 := by
    have h' : (μ * a ^ 3) ^ (35 / 1292 : ℝ) * (μ * a ^ 3) ^ (1 / 1292 : ℝ)
        ≤ (μ * a ^ 3) ^ (35 / 1292 : ℝ) * 1 := by simpa using h
    exact (mul_le_mul_iff_of_pos_left hpos).mp h'
  rcases (Real.rpow_le_one_iff_of_pos ht).mp hle with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h2 (by norm_num)
  · exact h1

/-! ## 3. The low threshold is nonpositive under `J ≤ K_B³` and `μ(a v)³ ≤ 1` -/

/-- **`J√(μa³) ≤ 1` from `J ≤ K_B³ = (μa³)^{-18/323}` and `μa³ ≤ 1`** (FS `eq:Xchoice`). -/
lemma J_mul_sqrt_le_one {a μ J : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1)
    (hJ : J ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3) : J * Real.sqrt (μ * a ^ 3) ≤ 1 := by
  have htpos : 0 < μ * a ^ 3 := by positivity
  rw [theta_neg_of_KB_aux_KB_cube_eq (μ := μ) (a := a) htpos.le] at hJ
  have h1 : J * (μ * a ^ 3) ^ (1 / 2 : ℝ)
      ≤ (μ * a ^ 3) ^ (-(18 / 323) : ℝ) * (μ * a ^ 3) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg htpos.le _)
  rw [← Real.rpow_add htpos] at h1
  have h2 : (μ * a ^ 3) ^ (-(18 / 323) + 1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one htpos.le ht (by norm_num)
  calc J * Real.sqrt (μ * a ^ 3) = J * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ 1 := le_trans h1 h2

/-- **The low-state threshold is nonpositive**: `Theta a J μ ≤ 0` for `0 < a`, `0 < μ`,
`μa³ ≤ 1` and `J ≤ K_B³`. -/
lemma theta_nonpos_of_KB_cube {a μ J : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1)
    (hJ : J ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3) : Work.UBB.Theta a J μ ≤ 0 := by
  have hJs := J_mul_sqrt_le_one hμ ha ht hJ
  rw [Work.UBB.Theta]
  have hcoef : 0 ≤ 4 * Real.pi * μ ^ 2 * a := by positivity
  have h1s : 0 ≤ 1 - J * Real.sqrt (μ * a ^ 3) := by linarith
  have hfin : 0 ≤ 4 * Real.pi * μ ^ 2 * a * (1 - J * Real.sqrt (μ * a ^ 3)) :=
    mul_nonneg hcoef h1s
  linarith

/-! ## 4. The target -/

theorem kinFormBLowParams {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R J : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, 0 < μ →
      Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ (BoseGases.a v)) (μ * (BoseGases.a v) ^ 3) →
      R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ C * (BoseGases.a v) * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
              * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨K, hKpos, _hfib, hmassgen⟩ := Work.AprioriCount.wLocG0MassBound (v := v) h hR hv_supp
  refine ⟨2 * K / BoseGases.a v, div_nonneg (by linarith) hav.le, ?_⟩
  intro μ hμ hOK hRℓ hJ n Φ hnc hnorm hL
  have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    nlinarith [hR, hRℓ, Submission.BoseGases.chiR0_pos]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- (1) the diluteness cap, from the parameter conditions
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 :=
    mu_mul_a_cube_le_one_of_paramsOK (a := BoseGases.a v) hμ hav hOK
  -- (2) the low threshold is nonpositive
  have hΘ : Work.UBB.Theta (BoseGases.a v) J μ ≤ 0 :=
    theta_nonpos_of_KB_cube (a := BoseGases.a v) hμ hav ht1 hJ
  -- (3) the box-word splitting
  have hsplit := Work.AprioriCount.wordB_eq_kin_sub_potMass_add_pair (v := v) h hv1 hR hv_supp
    (μ := μ) (n := n) hRℓ Φ
  have hpair : 0 ≤ Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) := Work.BoseFixB1B.pairPartB_nonneg hv _ _
  have hword : Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hh := hL
    unfold Work.BoseBoxFix.IsLowB at hh
    exact hh
  have hneg : Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hℓpos.le 3) hΘ) hnorm.le
  -- (4) the unconditional one-body mass bound
  have hpot : Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (BoseGases.a v)) v h
      (Φ : Submission.BoseGases.X n → ℝ)
      = ∫ (x : Submission.BoseGases.X n) in Submission.BoseGases.abox n
          (Work.BoseBox.sideAt μ (BoseGases.a v)),
          (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
            ∑ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin 3)),
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y := by
    simp only [Work.AprioriCount.potMass, Work.BoseBox.potBr]
  have hnormB : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := rfl
  have hmass : μ * Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (BoseGases.a v)) v h
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ μ * (K * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [hpot, hnormB]
    exact mul_le_mul_of_nonneg_left
      (hmassgen n (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ)
        hℓpos hRℓ hΦc) hμ.le
  -- the `n ≤ 2μℓ³` step, then the division by `(a v) > 0`
  have hstep : μ * (K * (n : ℝ)
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ 2 * K * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [show μ * (K * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        = K * μ * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) from by ring]
    have h2 : K * μ * (n : ℝ) ≤ K * μ * (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3) :=
      mul_le_mul_of_nonneg_left hnc (mul_nonneg hKpos.le hμ.le)
    have h3 := mul_le_mul_of_nonneg_right h2 hnorm.le
    calc K * μ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ K * μ * (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := h3
      _ = 2 * K * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by ring
  have hkin : Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ 2 * K * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    linarith [hsplit, hpair, hmass, hstep, hword, hneg]
  calc Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ 2 * K * μ ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := hkin
    _ ≤ (2 * K / BoseGases.a v) * (BoseGases.a v) * μ ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        le_of_eq (by rw [div_mul_cancel₀ (2 * K) hav.ne'])

end Work.BoseBoxFock.PCFU
