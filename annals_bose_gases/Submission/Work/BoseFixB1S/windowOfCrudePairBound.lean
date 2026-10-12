import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.paramsAt_facts
import Submission.Work.BoseFixB1B.boxFormB_budgetAlt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.windowOfCrudePairBound` — the CRUDE particle window from a CRUDE pair bound

This file is the second half of the reduction of `Work.BoseFixB1S.pairCountRegimeB1`
(see `FINDING_pairCountRegimeB1_reduction.md` §7): the target needs only the **crude** particle
window

    (W)  ∃ Cw εw, 0 < Cw ∧ 0 < εw ∧ ∀ μ admissible, J ≤ K_B³ →
           ∀ n Φ, 0 < ‖Φ‖² → IsLowB ⟹ (n:ℝ) ≤ Cw·μ·ℓ³ ,

with `Cw` **free** (`pairCountRegimeB1_of_window`, proved in `pairCountRegimeB1.lean`).  Here we
show that (W) follows from the single **crude** mean-field lower bound

    (E)  kinFormB + pairPartB ≥ c·(a v)·n(n−1)·ℓ^{-3}·‖Φ‖²      (any `c > 0`),

i.e. from a *non-sharp* (Dyson-type) mean-field bound for the box, with no LHY correction.

## The proof

* `boxFormB_budgetAlt` (PROVED, `Submission/Work/BoseFixB1B/boxFormB_budgetAlt.lean`) is the
  low-state budget
  `kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))·‖Φ‖² ≤ μ·M`, `M` = the flat mass
  `∫_{abox}Φ²·Σᵢ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y`.
* `J ≤ K_B³` and `K_B³·√(μ(a v)³) ≤ 1` (`KB_cube_mul_sqrt_le_one_sbf`; `K_B³ = t^{-18/323}`,
  `√t = t^{1/2}`, product `t^{287/646} ≤ 1` for `t = μ(a v)³ ≤ 1`) give `1 − J√(μ(a v)³) ≥ 0`,
  hence `kinFormB + pairPartB ≤ μ·M`.
* The pointwise fibre bound `hfib` gives `Σᵢ∫_y wLoc ≤ nK`, hence `M ≤ nK·‖Φ‖²`.
* Combining with (E) and cancelling `n·‖Φ‖² > 0` gives
  `(n − 1) ≤ μKℓ³/(c(a v))`, and `1 ≤ μℓ³` (`mu_ell_cube_fsParams`: `μℓ³ = t^{-166/323}` for
  `t ≤ 1`) absorbs the `1`: `n ≤ (1 + K/(c(a v)))·μℓ³`.

So the whole residual of `pairCountRegimeB1` is (E), a **classical** (Dyson-type) theorem, not
FS's sharp a priori bound.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Two elementary parameter facts -/

lemma lhyC_pos_sbf : 0 < Work.UBB.lhyC := by
  unfold Work.UBB.lhyC
  have h : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **`K_B³·√(μ a³) ≤ 1`** at FS's parameters when `μ a³ ≤ 1`: `K_B³ = t^{-18/323}`, `√t = t^{1/2}`
and the product is `t^{287/646} ≤ 1`. -/
lemma KB_cube_mul_sqrt_le_one_sbf {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (ht1 : μ * a ^ 3 ≤ 1) : (Work.BoseBox.paramsAt μ a).KB ^ 3 * Real.sqrt (μ * a ^ 3) ≤ 1 := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hKB : (Work.BoseBox.paramsAt μ a).KB = Work.BoseBox.fsXp (μ * a ^ 3) (-6) := rfl
  have hpow : (Work.BoseBox.paramsAt μ a).KB ^ 3 = Work.BoseBox.fsXp (μ * a ^ 3) (-18) := by
    rw [hKB, Work.BoseBox.fsXp_pow ht.le (-6) 3]
    norm_num
  have hsqrt : Real.sqrt (μ * a ^ 3) = Work.BoseBox.fsXp (μ * a ^ 3) (323 / 2) := by
    rw [Real.sqrt_eq_rpow]
    unfold Work.BoseBox.fsXp
    congr 1
    norm_num
  rw [hpow, hsqrt, Work.BoseBox.fsXp_mul ht,
    show (-18 : ℝ) + 323 / 2 = 287 / 2 by norm_num]
  exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)

/-- **`1 ≤ μ ℓ³`** at FS's parameters when `μ a³ ≤ 1`. -/
lemma one_le_mu_sideAt_cube_sbf {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (ht1 : μ * a ^ 3 ≤ 1) : 1 ≤ μ * (Work.BoseBox.sideAt μ a) ^ 3 := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hside : Work.BoseBox.sideAt μ a
      = Work.BoseBox.boxSide (Work.BoseBox.fsParams (μ * a ^ 3)) μ a := rfl
  rw [hside, Work.BoseBox.mu_ell_cube_fsParams hμ ha]
  have hinv : 1 ≤ ((μ * a ^ 3) ^ (166 / 323 : ℝ))⁻¹ := by
    have hA : (μ * a ^ 3) ^ (166 / 323 : ℝ) ≤ 1 :=
      Real.rpow_le_one ht.le ht1 (by norm_num)
    have := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1)
      (Real.rpow_pos_of_pos ht (166 / 323))).mpr hA
    simpa using this
  have hneg : ((μ * a ^ 3) ^ (166 / 323 : ℝ))⁻¹ = (μ * a ^ 3) ^ (-(166 / 323) : ℝ) := by
    rw [Real.rpow_neg ht.le]
  rwa [hneg] at hinv

/-! ## 2. The pure-real sandwich -/

/-- **The sandwich arithmetic.**  If `kinpair ≤ μM`, `M ≤ nK‖Φ‖²`, `‖Φ‖² > 0`, `n ≥ 1` and
`c·a·n(n−1)/ℓ³·‖Φ‖² ≤ kinpair`, then `n ≤ (1 + K/(ca))·μℓ³`. -/
lemma count_le_of_sandwich {a c K μ ℓ M kinpair normB : ℝ} {n : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hK : 0 ≤ K) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hmuℓ : 1 ≤ μ * ℓ ^ 3) (hnorm : 0 < normB)
    (hKin : kinpair ≤ μ * M) (hM : M ≤ (n : ℝ) * K * normB)
    (hE : c * a * (n : ℝ) * ((n : ℝ) - 1) / ℓ ^ 3 * normB ≤ kinpair) :
    (n : ℝ) ≤ (1 + K / (c * a)) * μ * ℓ ^ 3 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have : 0 ≤ (1 + K / (c * a)) * μ * ℓ ^ 3 := by positivity
    simpa using this
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have h1 : c * a * (n : ℝ) * ((n : ℝ) - 1) / ℓ ^ 3 * normB
        ≤ μ * ((n : ℝ) * K * normB) :=
      le_trans hE (le_trans hKin (mul_le_mul_of_nonneg_left hM hμ.le))
    have h2 : c * a * ((n : ℝ) - 1) / ℓ ^ 3 * normB ≤ μ * K * normB := by
      have h2' : (c * a * ((n : ℝ) - 1) / ℓ ^ 3 * normB) * (n : ℝ)
          ≤ (μ * K * normB) * (n : ℝ) := by
        calc (c * a * ((n : ℝ) - 1) / ℓ ^ 3 * normB) * (n : ℝ)
            = c * a * (n : ℝ) * ((n : ℝ) - 1) / ℓ ^ 3 * normB := by ring
          _ ≤ μ * ((n : ℝ) * K * normB) := h1
          _ = (μ * K * normB) * (n : ℝ) := by ring
      exact le_of_mul_le_mul_right h2' hnR
    have h3 : c * a * ((n : ℝ) - 1) / ℓ ^ 3 ≤ μ * K :=
      le_of_mul_le_mul_right h2 hnorm
    have h4 : ((n : ℝ) - 1) ≤ μ * K * ℓ ^ 3 / (c * a) := by
      rw [le_div_iff₀ (mul_pos hc ha)]
      calc ((n : ℝ) - 1) * (c * a) = c * a * ((n : ℝ) - 1) := by ring
        _ = c * a * ((n : ℝ) - 1) / ℓ ^ 3 * ℓ ^ 3 := by
              rw [div_mul_cancel₀]
              exact pow_ne_zero 3 (ne_of_gt hℓ)
        _ ≤ μ * K * ℓ ^ 3 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hℓ.le 3)
    have h5 : (n : ℝ) ≤ 1 + μ * K * ℓ ^ 3 / (c * a) := by linarith
    have h6 : 1 + μ * K * ℓ ^ 3 / (c * a) ≤ (1 + K / (c * a)) * μ * ℓ ^ 3 := by
      have h7 : μ * K * ℓ ^ 3 / (c * a) = (K / (c * a)) * (μ * ℓ ^ 3) := by ring
      rw [h7]
      have h8 : 0 ≤ K / (c * a) := div_nonneg hK (mul_pos hc ha).le
      nlinarith [hmuℓ, h8]
    linarith

/-! ## 3. The target of this file -/

set_option maxHeartbeats 1600000 in
theorem windowOfCrudePairBound {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hfib : ∀ (ℓ : ℝ) (x : E3),
      |∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y| ≤ K)
    (hIntA : ∀ (μ : ℝ) (n : ℕ)
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (-μ * (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y)))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (hIntB : ∀ (μ : ℝ) (n : ℕ)
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0
            (x ij.1.1) (x ij.1.2)))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (hE : ∀ (μ : ℝ) (n : ℕ)
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      Work.BoseBoxFix.Adm v (1 / 16) μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
      Work.BoseBoxFix.IsLowB v h J μ n Φ →
      c * (_root_.BoseGases.a v) * (n : ℝ) * ((n : ℝ) - 1)
          / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)) :
    ∃ Cw εw : ℝ, 0 < Cw ∧ 0 < εw ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v εw μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          (n : ℝ) ≤ Cw * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
  refine ⟨1 + K / (c * (_root_.BoseGases.a v)), 1 / 16, ?_, by norm_num, ?_⟩
  · have : 0 ≤ K / (c * (_root_.BoseGases.a v)) := div_nonneg hK (by positivity)
    linarith
  · intro μ hAdm hKB n Φ hpos hlow
    obtain ⟨hμ, hε, hP⟩ := hAdm
    have hav' : 0 < _root_.BoseGases.a v := hav
    have hJ0 : 0 ≤ J := le_trans (le_of_lt lhyC_pos_sbf) hJ
    have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := by linarith
    have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
      rw [show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          = Work.BoseBox.boxSide (Work.BoseBox.fsParams (μ * (_root_.BoseGases.a v) ^ 3)) μ
              (_root_.BoseGases.a v) from rfl, Work.BoseBox.boxSide]
      exact mul_pos (Work.BoseBox.fsXp_pos (by positivity))
        (Real.rpow_pos_of_pos (by positivity) _)
    have hmuℓ : 1 ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
      one_le_mu_sideAt_cube_sbf hμ hav' ht1
    -- the coefficient `1 - J√(μ(a v)³)` is nonnegative
    have hKB3 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) ≤ 1 :=
      KB_cube_mul_sqrt_le_one_sbf hμ hav' ht1
    have hJt1 : J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) ≤ 1 := by
      have h2 : 0 ≤ Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hKB h2, hKB3]
    have hβ : 0 ≤ 1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := by linarith
    -- the budget
    have hbud := Work.BoseFixB1B.boxFormB_budgetAlt (v := v) h hv hJ0 (μ := μ) (n := n)
      (Φ := Φ) hlow (hIntA μ n Φ) (hIntB μ n Φ)
    -- nonnegativity of the LHY term
    have hZnn : 0 ≤ 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) hβ) ?_
      · positivity
      · exact sq_nonneg μ
      · exact hav'.le
      · exact pow_nonneg hℓpos.le 3
      · have : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
          rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
          exact integral_nonneg fun x => sq_nonneg _
        exact this
    have hKin : Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              (∑ i : Fin n, ∫ y : E3,
                Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
      nlinarith [hbud, hZnn]
    -- the flat mass is bounded by `n·K·‖Φ‖²`
    have hIntSum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
      have hμne : μ ≠ 0 := ne_of_gt hμ
      have h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
          -(1 / μ) * (((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (-μ * (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y))))
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
        (hIntA μ n Φ).const_mul (-(1 / μ))
      refine h1.congr ?_
      filter_upwards with x
      field_simp
    have hIntc : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 * ((n : ℝ) * K))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
      have hsq : MeasureTheory.IntegrableOn
          (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
        ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓpos)
          ((Φ.contDiff.continuous.pow 2).continuousOn)
      exact hsq.mul_const _
    have hM : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y))
        ≤ (n : ℝ) * K * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      have hpoint : ∀ x : Submission.BoseGases.X n,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y)
          ≤ ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 * ((n : ℝ) * K) := by
        intro x
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc (∑ i : Fin n, ∫ y : E3,
                Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.g0 v h) 0 (x i) y)
            ≤ ∑ _i : Fin n, K := Finset.sum_le_sum (fun i _ =>
                le_trans (le_abs_self _) (hfib (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (x i)))
          _ = (n : ℝ) * K := by simp
      have := MeasureTheory.setIntegral_mono_on hIntSum hIntc
        (Submission.BoseGases.abox_measurable n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (fun x _ => hpoint x)
      rw [MeasureTheory.integral_mul_const] at this
      simpa [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, mul_assoc, mul_comm, mul_left_comm]
        using this
    -- assemble
    refine count_le_of_sandwich (a := _root_.BoseGases.a v) (c := c) (K := K) (μ := μ)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (M := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              (∑ i : Fin n, ∫ y : E3,
                Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.g0 v h) 0 (x i) y))
      (kinpair := Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ))
      (normB := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      (n := n) hav' hc hK hμ hℓpos hmuℓ hpos hKin hM
      (hE μ n Φ ⟨hμ, hε, hP⟩ hKB hpos hlow)

end Work.BoseFixB1S
