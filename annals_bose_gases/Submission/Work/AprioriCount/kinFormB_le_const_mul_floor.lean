import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.chiSqMassBridge
import Submission.Work.AprioriCount.fibMass_le_chiCount
import Submission.Work.BoseFixB1S.countWindowUnif_of_aprioriUnif
import Submission.Work.BoseFixB1S.windowOfCrudePairBound
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
import Submission.Work.BoseFixB2.Energy.potWordU_integrable_b2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.AprioriCount.kinFormB_le_const_mul_floor`

**The kinetic floor of a low box state**: there is a constant `κ`, depending only on `(v,h,R)`,
such that every `IsLowB` (FS `eq:aprioriPsi`) box state at an admissible chemical potential
satisfies

    kinFormB ≤ κ·μ²·(a v)·ℓ³·‖Φ‖² ,        ℓ = sideAt μ (a v) .

The constant is `κ = 16π·chiSup³·Cw + 4π`, where `Cw` is the constant of the `J`-uniform particle
count window `n ≤ Cw·μℓ³` obtained from the a-priori interface `AprioriUnif v h`
(`Work.BoseFixB1S.countWindowUnif_of_aprioriUnif`).

## Route

Write `k = kinFormB`, `B = pairPartB`, `M = ∫_{abox} Φ²·Σᵢ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y`
(the *flat one-body mass*), `N = normB`, `A = 4πμ²(a v)ℓ³`.

1. **The budget of `boxFormB_budgetAlt`** (the split `wordB = k + chemPartB + B` with
   `chemPartB = −μM`, together with `IsLowB`): `k + B + A(1 − J√(μa³))N ≤ μM`. Since
   `J√(μa³) ≤ 1` (`J ≤ K_B³` and `K_B³√(μa³) ≤ 1` at `μa³ ≤ 1`,
   `Work.BoseFixB1S.KB_cube_mul_sqrt_le_one_sbf`) the gap term is `≥ −AN`; and `B ≥ 0` for
   `v ≥ 0`. Hence

       k ≤ μM + A·N .

2. **The flat mass is mean-field sized**: `M ≤ fsqC1(a v)·chiCount ℓ Φ`
   (`Work.AprioriCount.fibMass_le_chiCount`) with `chiCount ≤ chiSup·n·N`
   (`chiCount_le_normB` below). Hence `M ≤ fsqC1(a v)·chiSup·n·N`.

3. **The count window** `n ≤ Cw·μℓ³` (needed only when `N > 0`; for `N = 0` both sides of the
   final inequality vanish) turns this into `μM ≤ 16π·chiSup³·Cw·μ²(a v)ℓ³·N`.

Adding the two: `k ≤ (16π·chiSup³·Cw + 4π)·μ²(a v)ℓ³·N`.

The two integrability inputs of step 1 are proved below (`chemInt_integrable`, `pairInt_integrable`)
from the corpus's per-coordinate chemical integrability
(`Work.BoseFixB2.Energy.integrableOn_chemP_coord`) and its per-pair integrability
(`Work.BoseFixB2.Energy.integrableOn_wPairC_pair`), together with the boundedness of `Φ²` on the
compact box.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The two integrability inputs of the box-word splitting -/

/-- **The chemical integrand is integrable on the box.**  Each coordinate's fibre integral
`x ↦ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y = chemP ℓ (g₀ v h) (xᵢ)` is integrable on `abox n ℓ`
(`Work.BoseFixB2.Energy.integrableOn_chemP_coord`), and multiplying by the bounded continuous
factor `Φ²` preserves integrability. -/
private theorem chemInt_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {R ℓ μ : ℝ} {n : ℕ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n ℓ) := by
  have hterm : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        -μ * ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      (Submission.BoseGases.abox n ℓ) := by
    intro i
    have hb := Work.BoseFixB2.Energy.integrableOn_chemP_coord (ℓ := ℓ) hℓ
      (Submission.BoseGases.g0_integrable hR hv_supp h) i
    refine (hb.const_mul (-μ)).congr (Filter.Eventually.of_forall fun x => ?_)
    exact congrArg (fun t => -μ * t)
      (show Work.BoseFixB2.Energy.chemP ℓ (Submission.BoseGases.g0 v h) (x i)
          = ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y from by
        rw [Work.BoseFixB2.Energy.chemP]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y =>
          (Work.BoseFixB2.Energy.wLoc_zero_eq_wPairC ℓ (Submission.BoseGases.g0 v h) (x i) y).symm))
  have hsum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, -μ * ∫ y : E3,
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      (Submission.BoseGases.abox n ℓ) :=
    MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin n))
      (f := fun i (x : Submission.BoseGases.X n) =>
        -μ * ∫ y : E3, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      (fun i _ => hterm i)
  refine MeasureTheory.IntegrableOn.continuousOn_mul ((hΦ.continuous.pow 2).continuousOn)
    (hsum.congr (Filter.Eventually.of_forall fun x => ?_))
    (Submission.BoseGases.abox_compact n hℓ)
  exact (Finset.mul_sum Finset.univ
    (fun i : Fin n => ∫ y : E3,
      Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y) (-μ)).symm

/-- **The pair integrand is integrable on the box.**  Each pair kernel
`x ↦ wLoc ℓ v 0 (xᵢ) (xⱼ) = wPairC ℓ v (xᵢ) (xⱼ)` is integrable on `abox n ℓ`
(`Work.BoseFixB2.Energy.integrableOn_wPairC_pair`), so is the finite sum over the pairs, and
multiplying by the bounded continuous factor `Φ²` preserves integrability. -/
private theorem pairInt_integrable {v : E3 → ℝ} {R ℓ : ℝ} {n : ℕ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hv1 : MeasureTheory.MemLp v 1) (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ) := by
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hterm : ∀ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
      (Submission.BoseGases.abox n ℓ) := by
    intro ij
    exact (Work.BoseFixB2.Energy.integrableOn_wPairC_pair (ℓ := ℓ) hℓ (v := v) hv_int
      (n := n) (i := ij.1.1) (j := ij.1.2) (ne_of_lt ij.2)).congr
      (Filter.Eventually.of_forall fun x =>
        (Work.BoseFixB2.Energy.wLoc_zero_eq_wPairC ℓ v (x ij.1.1) (x ij.1.2)).symm)
  have hsum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
      (Submission.BoseGases.abox n ℓ) :=
    MeasureTheory.integrable_finsetSum (Finset.univ : Finset {ij : Fin n × Fin n | ij.1 < ij.2})
      (f := fun ij (x : Submission.BoseGases.X n) =>
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
      (fun ij _ => hterm ij)
  exact MeasureTheory.IntegrableOn.continuousOn_mul ((hΦ.continuous.pow 2).continuousOn) hsum
    (Submission.BoseGases.abox_compact n hℓ)

/-! ## 2. The χ-count of a box state is at most `chiSup·n·‖Φ‖²` -/

/-- `chiCount ℓ Φ ≤ chiSup·n·‖Φ‖²`: pointwise `Σᵢχ_ℓ(xᵢ) ≤ n·chiSup`, against `Φ² ≥ 0`. -/
private theorem chiCount_le_normB {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    chiCount ℓ Φ ≤ Submission.BoseGases.chiSup * (n : ℝ) * Work.BoseKinLoc.sqNormB n ℓ Φ := by
  have hcomp : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_compact n hℓ
  have hsqcont : Continuous fun x : Submission.BoseGases.X n => (Φ x) ^ 2 := hΦ.pow 2
  have hchain : Continuous fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) :=
    continuous_finsetSum _ fun i _ =>
      (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)
        ≤ (Φ x) ^ 2 * ((n : ℝ) * Submission.BoseGases.chiSup) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)
        ≤ ∑ _i : Fin n, Submission.BoseGases.chiSup := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact le_trans (le_abs_self _) (Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x i))
      _ = (n : ℝ) * Submission.BoseGases.chiSup := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul hchain).continuousOn
  have h2 : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((n : ℝ) * Submission.BoseGases.chiSup))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp (hsqcont.mul continuous_const).continuousOn
  have hmono := integral_mono h1 h2 hpt
  have hRHS : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ((n : ℝ) * Submission.BoseGases.chiSup))
      = Submission.BoseGases.chiSup * (n : ℝ) * Work.BoseKinLoc.sqNormB n ℓ Φ := by
    rw [MeasureTheory.integral_mul_const, Work.BoseKinLoc.sqNormB]
    ring
  rw [chiCount]
  exact le_trans hmono (le_of_eq hRHS)

/-! ## 3. The pure arithmetic of the final assembly -/

/-- With `M ≤ fsqC1 a·chiSup·n·N`, `n·N ≤ (C μℓ³)·N` and `μ, N, C ≥ 0`:
`μM ≤ 16π·chiSup³·C·μ²aℓ³N` (using `fsqC1 a = chiSup²·2·(8πa)`). -/
private lemma mu_mul_le_of {n μ aa ℓ N M C : ℝ} (hμ : 0 ≤ μ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hfsq : 0 ≤ Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup)
    (hn : n * N ≤ (C * μ * ℓ ^ 3) * N)
    (hM : M ≤ Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * n * N) :
    μ * M ≤ (16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * C) * μ ^ 2 * aa * ℓ ^ 3 * N := by
  have h1 : μ * M ≤ μ * (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * n * N) :=
    mul_le_mul_of_nonneg_left hM hμ
  have h2 : Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * n * N
      ≤ Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * (C * μ * ℓ ^ 3) * N := by
    have h3 : (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup) * (n * N)
        ≤ (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup)
            * ((C * μ * ℓ ^ 3) * N) :=
      mul_le_mul_of_nonneg_left hn hfsq
    calc Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * n * N
        = (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup) * (n * N) := by ring
      _ ≤ (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup)
            * ((C * μ * ℓ ^ 3) * N) := h3
      _ = Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * (C * μ * ℓ ^ 3) * N := by
          ring
  have h2' : μ * (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * n * N)
      ≤ μ * (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * (C * μ * ℓ ^ 3) * N) :=
    mul_le_mul_of_nonneg_left h2 hμ
  have h4 : μ * (Submission.BoseGases.fsqC1 aa * Submission.BoseGases.chiSup * (C * μ * ℓ ^ 3) * N)
      = (16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * C) * μ ^ 2 * aa * ℓ ^ 3 * N := by
    rw [Submission.BoseGases.fsqC1]; ring
  linarith [h1, h2', h4]

/-! ## 4. The target -/

theorem kinFormB_le_const_mul_floor {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hA : Work.BoseFixB1S.AprioriUnif v h) :
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ J : ℝ, Work.UBB.lhyC ≤ J →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
            Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ)
              ≤ κ * μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the `J`-uniform particle count window
  obtain ⟨εw, Cw, hεw, hCw0, hwin⟩ :=
    Work.BoseFixB1S.countWindowUnif_of_aprioriUnif (v := v) h hv hv1 hvrad hR hv_supp hav hA
  -- the small-diluteness threshold producing the large-box régime `R ≤ ℓ·chiR0`
  obtain ⟨εχ, hεχ, hreg⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  have hchi0 : (0 : ℝ) < Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos
  have hκpos : 0 < 16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw + 4 * Real.pi := by
    have h1 : 0 ≤ 16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (pow_nonneg hchi0.le 3)) hCw0
    linarith [Real.pi_pos]
  refine ⟨16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw + 4 * Real.pi,
    min εχ (min εw 1), hκpos, lt_min hεχ (lt_min hεw one_pos), ?_⟩
  intro μ hAdm
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  intro J hJ hJK n Φ hlow
  set N : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hNdef
  have hμ : 0 < μ := hAdm.1
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hAdmχ : Work.BoseBoxFix.Adm v εχ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmw : Work.BoseBoxFix.Adm v εw μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0 := by
    rw [hℓdef]; exact hreg μ hAdmχ
  have hN0 : 0 ≤ N := by rw [hNdef]; exact Work.BoseFixB1.normB_nonneg _
  have ha0 : 0 ≤ _root_.BoseGases.a v := hav.le
  have hJ0 : 0 ≤ J := le_trans (le_of_lt Work.UBB.lhyC_pos) hJ
  have hJt0 : 0 ≤ J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) :=
    mul_nonneg hJ0 (Real.sqrt_nonneg _)
  have hKB3 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) ≤ 1 :=
    Work.BoseFixB1S.KB_cube_mul_sqrt_le_one_sbf hμ hav ht1
  have hJt1 : J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) ≤ 1 := by
    have h2 : 0 ≤ Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hJK h2, hKB3]
  have habs : |1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  -- ## integrability of the two pieces of the word
  have hAint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        (-μ * (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n ℓ) :=
    chemInt_integrable (v := v) h hR hv_supp hℓ (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff
  have hBint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ) :=
    pairInt_integrable (v := v) hR hv_supp hv1 hℓ (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff
  -- ## the budget
  have hbud := Work.BoseFixB1B.boxFormB_budgetAlt (v := v) h hv hJ0 (μ := μ) (n := n) (Φ := Φ)
    hlow hAint hBint
  have hpairnn : 0 ≤ Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1B.pairPartB_nonneg hv ℓ _
  have hA0 : 0 ≤ 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (sq_nonneg μ)) ha0) (pow_nonneg hℓ.le 3)
  have hZlo : -(4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3 * N)
      ≤ 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) * N := by
    have hc : -(4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3)
        ≤ 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
          * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)) := by
      have h1 : (-1 : ℝ) ≤ 1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) :=
        (abs_le.mp habs).1
      have h2 := mul_le_mul_of_nonneg_left h1 hA0
      linarith
    have h3 := mul_le_mul_of_nonneg_right hc hN0
    linarith
  have hstep1 : Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ μ * (∫ x in Submission.BoseGases.abox n ℓ, (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
          ∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3 * N := by
    linarith [hbud, hZlo, hpairnn]
  -- ## the flat mass bound
  have hfsq0 : 0 ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) := by
    rw [Submission.BoseGases.fsqC1]
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (by norm_num)) ?_
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ha0
  have hMle : (∫ x in Submission.BoseGases.abox n ℓ, (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        ∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) * Submission.BoseGases.chiSup
          * (n : ℝ) * N := by
    have h1 := Work.AprioriCount.fibMass_le_chiCount (v := v) h hv hv1 hvrad hR hℓ hv_supp hRℓ
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
    have h2 := chiCount_le_normB (n := n) hℓ Φ.contDiff.continuous
    calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
          ∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * chiCount ℓ (Φ : Submission.BoseGases.X n → ℝ) := h1
      _ ≤ Submission.BoseGases.fsqC1 (_root_.BoseGases.a v)
            * (Submission.BoseGases.chiSup * (n : ℝ) * N) := mul_le_mul_of_nonneg_left h2 hfsq0
      _ = Submission.BoseGases.fsqC1 (_root_.BoseGases.a v) * Submission.BoseGases.chiSup
            * (n : ℝ) * N := by ring
  -- ## the count window (needed only when `N > 0`)
  have hnN : (n : ℝ) * N ≤ (Cw * μ * ℓ ^ 3) * N := by
    by_cases hNB : 0 < N
    · have hn := hwin J μ hAdmw hJK n Φ hNB hlow
      exact mul_le_mul_of_nonneg_right hn hN0
    · have hNz : N = 0 := le_antisymm (le_of_not_gt hNB) hN0
      rw [hNz]
      simp
  have hMn : μ * (∫ x in Submission.BoseGases.abox n ℓ, (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        ∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)
      ≤ (16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw) * μ ^ 2
          * (_root_.BoseGases.a v) * ℓ ^ 3 * N :=
    mu_mul_le_of hμ.le hN0 hCw0 (mul_nonneg hfsq0 hchi0.le) hnN hMle
  -- ## assembly
  have hcombine : (16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw) * μ ^ 2
        * (_root_.BoseGases.a v) * ℓ ^ 3 * N
      + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3 * N
      = (16 * Real.pi * Submission.BoseGases.chiSup ^ 3 * Cw + 4 * Real.pi) * μ ^ 2
          * (_root_.BoseGases.a v) * ℓ ^ 3 * N := by ring
  linarith [hstep1, hMn, hcombine]

end Work.AprioriCount
