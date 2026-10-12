import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.boxFormB_budgetAlt
import Submission.Work.BoseFixB1B.integrableOn_oneBody_wPair
import Submission.Work.BoseFixB1B.integrableOn_pair_wPair
import Submission.Work.BoseFixB1S.boxBogPortSliding
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.slidingWindowComparisonWeighted`

See `FINDING_slidingWindowComparisonWeighted.md` (same directory) for the full analysis of the
target: the statement is TRUE; the route is the *windowed-H¹* comparison of `bSpectralCube` with
the box kinetic word `kinFormB` (filed as the sibling `BoseFixB1B/bSpectralCubeLeKinFormB`) plus
the budget `kinFormB + pairPartB ≤ μ·M_w` and the regime arithmetic of the FINDING's §4.

This file proves, above the target, the **budget adapter** `lowBudgetSupply`: the integrability
side conditions of `Work.BoseFixB1B.boxFormB_budgetAlt` hold under the target's own hypotheses
(scattering solution, nonnegative radial `L¹` potential of range `R`, `Adm`, `IsLowB`), so the box
budget `kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μ·M_w` is available in the
target's exact vocabulary.  That is the "supply" half of the assembly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The low-state box budget in the target's vocabulary.**  For a low box state at FS's
parameters, the localised kinetic word plus the pair part plus the (nonnegative) gap term is at
most the one-body mass `μ·M_w`:

`kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μ·M_w`.

This is `Work.BoseFixB1B.boxFormB_budgetAlt` with its two `IntegrableOn` side conditions discharged
from the ambient hypotheses (the corpus's `integrableOn_oneBody_wPair`/`integrableOn_pair_wPair`
at the range condition `R ≤ ℓ·chiR0`, from `exists_adm_chiR0_ge`), and `0 ≤ J` from `lhyC_pos`. -/
theorem lowBudgetSupply {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
          + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                (∑ i : Fin n, ∫ y : E3,
                  Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
  obtain ⟨εR, hεRpos, hεR⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  refine ⟨εR, hεRpos, fun μ hAdm _ n Φ hL => ?_⟩
  have hJ0 : 0 ≤ J := le_trans Work.UBB.lhyC_pos.le hJ
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
    hεR μ hAdm
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hvzero : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport v := subset_tsupport v (Function.mem_support.mpr hne)
    have hb := hv_supp hmem
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact absurd hb (not_lt.mpr hz)
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hint1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) (x i) y))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    integrableOn_oneBody_wPair hℓpos (le_of_lt hR) hRℓ hg0int hg0supp hΦc
  have hint2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v
          (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    integrableOn_pair_wPair hℓpos (le_of_lt hR) hRℓ hv1 hvzero hΦc
  have hwlpt : ∀ (gg : E3 → ℝ) (a b : E3),
      Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) gg 0 a b
        = Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) gg a b :=
    fun gg a b => by
      simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
        Submission.BoseGases.chiScale]
  have hsumEq : ∀ (gg : E3 → ℝ) (x : Submission.BoseGases.X n),
      (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) gg 0 (x i) y)
        = ∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) gg (x i) y :=
    fun gg x => Finset.sum_congr rfl fun i _ => MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => hwlpt gg (x i) y)
  have hsumEq2 : ∀ x : Submission.BoseGases.X n,
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0
            (x ij.1.1) (x ij.1.2))
        = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v
              (x ij.1.1) (x ij.1.2) :=
    fun x => Finset.sum_congr rfl fun ij _ => hwlpt v _ _
  have hint1' : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) 0 (x i) y))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    hint1.congr_fun (fun x _ => by simp only [hsumEq (Submission.BoseGases.g0 v h) x])
      (Submission.BoseGases.abox_measurable n _)
  have hint2' : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0
          (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    hint2.congr_fun (fun x _ => by simp only [hsumEq2 x])
      (Submission.BoseGases.abox_measurable n _)
  have hApre : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (-μ) * ((Φ x) ^ 2 *
        (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    hint1'.const_mul (-μ)
  have hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    hApre.congr_fun (fun x _ => by ring) (Submission.BoseGases.abox_measurable n _)
  exact boxFormB_budgetAlt h hv hJ0 hL hA hint2'

/-- `wLoc ℓ gg 0 a b = wPair ℓ gg a b` (the anchored potential is the sliding one at `u = 0`). -/
private lemma wLoc_eq_wPair (ℓ : ℝ) (gg : E3 → ℝ) (a b : E3) :
    Submission.BoseGases.wLoc ℓ gg 0 a b = Submission.BoseGases.wPair ℓ gg a b := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
    Submission.BoseGases.chiScale]

/-- **The one-body (chemical) mass is bounded by `K·n·‖Φ‖²` with the *universal* constant
`K = 16π·chiSup²·(a v)`** — the `hMupper` estimate used by the row-payment arithmetic of
`FINDING_slidingWindowComparisonWeighted.md` §4 (it is the estimate proved inside
`Work.BoseFixB1B.isLowB_count_le_lower`, exposed here as a standalone interface so that the
assembly does not have to re-run the `IntegrableOn` bookkeeping). -/
theorem chemMassLe {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                (∑ i : Fin n, ∫ y : E3,
                  Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.g0 v h) 0 (x i) y))
          ≤ 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εR, hεRpos, hεR⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  refine ⟨εR, hεRpos, fun μ hAdm n Φ => ?_⟩
  have hμ : 0 < μ := hAdm.1
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
    hεR μ hAdm
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hg0nonneg : ∀ᵐ z : E3, 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hAbsEq : (∫ z : E3, |Submission.BoseGases.g0 v h z|) =
      ∫ z : E3, Submission.BoseGases.g0 v h z :=
    MeasureTheory.integral_congr_ae
      (hg0nonneg.mono fun _ hz => abs_of_nonneg hz)
  have hIntEq : (∫ z : E3, Submission.BoseGases.g0 v h z) = 8 * Real.pi * (_root_.BoseGases.a v) :=
    Submission.BoseGases.g0_integral hR hv_supp h
  set K : ℝ := Submission.BoseGases.chiSup ^ 2 * 2 * (∫ z : E3, |Submission.BoseGases.g0 v h z|)
    with hKdef
  have hfib : ∀ u : E3,
      |∫ y : E3, Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.g0 v h) 0 u y| ≤ K := by
    intro u
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => wLoc_eq_wPair _ _ u y)]
    exact Submission.BoseGases.fibre_integral_abs_le hℓpos (le_of_lt hR) hRℓ hg0int hg0supp u
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hsumEq : ∀ x : Submission.BoseGases.X n,
      (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y)
        = ∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) (x i) y :=
    fun x => Finset.sum_congr rfl fun i _ => MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => wLoc_eq_wPair _ _ (x i) y)
  have hint1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wPair (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) (x i) y))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    integrableOn_oneBody_wPair hℓpos (le_of_lt hR) hRℓ hg0int hg0supp hΦc
  have hint1' : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) 0 (x i) y))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    hint1.congr_fun (fun x _ => by simp only [hsumEq x])
      (Submission.BoseGases.abox_measurable n _)
  have hmajor : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((n : ℝ) * K))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    ((hΦc.pow 2).mul_const ((n : ℝ) * K)).continuousOn.integrableOn_compact
      (Submission.BoseGases.abox_compact n hℓpos)
  have hnormB : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := rfl
  have hstep : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y))
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 * ((n : ℝ) * K) := by
    refine MeasureTheory.integral_mono hint1' hmajor fun x => ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y)
        ≤ ∑ _i : Fin n, K :=
          Finset.sum_le_sum fun i _ => le_trans (le_abs_self _) (hfib (x i))
      _ = (n : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
  have hconst : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 * ((n : ℝ) * K))
      = ((n : ℝ) * K) * ∫ x in Submission.BoseGases.abox n
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hmass : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y))
      ≤ K * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hnormB]
    calc _ ≤ ((n : ℝ) * K) * ∫ x in Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
          rw [← hconst]; exact hstep
      _ = K * (n : ℝ) * ∫ x in Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by ring
  have hKval : K = 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) := by
    rw [hKdef, hAbsEq, hIntEq]
    ring
  calc μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y))
      ≤ μ * (K * (n : ℝ) * Work.BoseBoxFix.normB v μ n
          (Φ : Submission.BoseGases.X n → ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hμ.le
    _ = 16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (_root_.BoseGases.a v) * μ * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
        rw [hKval]; ring

/-- The `chiB`/`chiSmallB` window comparison `Work.BoseFixB1B.slidingWindowComparison`, with the
weighted-mass row `C·μ·M_w(Φ)` added, where
`M_w(Φ) = ∫_{abox n ℓ} Φ² Σᵢ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y` is the object of the PROVED
`Work.BoseFixB1B.isLowB_chemBoundAlt`.

**Purpose.**  This is the *independent* repair of the frozen vocabulary's ball/cube window
mismatch: `Work.BoseFixB1S.bSpectralCube` is the spectral slot at the cube cutoff `chiSmallB` (the
cutoff that the localised pairing kernel `wSmallPair` actually carries), while
`Work.BoseFixB1.bSpectral` is the *ball*-windowed slot that the kinetic word `sbKin` carries.
Since `bSpectralCube ≈ 25·bSpectral` in the bulk, no free constant absorbs the difference on the
wrong side of the ledger, so the fixed-factor transfer `Work.BoseFixB1S.tBdiagWindowTransferB1`
does not compose; the row added here is the honest payment.

**Do NOT establish this by importing/consuming `Submission.Work.BoseFixB1B.slidingWindowComparison`
(that module carries a `sorry`); the point of this file is an independent route.**  A proof through
it would be `sorryAx`-tainted and is not what is wanted.

**Expected route** (all inputs proved): `bSpectralCube` is the
`chiScale ℓ · chiSmall M(·)`-windowed spectral slot, and `chiSmall M ≤ chiSmallDecay M` is a *fixed*
multiplier, so `bSpectralCube ≤ (chiSmallDecay M)²·`(the `chiScale ℓ`-windowed slot at the same
cutoff); that slot is a summand of `Work.BoseKinLoc.kinFormB` (`mainWord`,
`bsOneBody ℓ (fsKinCoeff ((2*s*ℓ)⁻¹))`, and `fsKinCoeff c ≤ fsKinCoeff ((2*s*ℓ)⁻¹)` because
`c = (d*s*ℓ)⁻¹ ≥ (2*s*ℓ)⁻¹` for `d ≤ 2`), so `bSpectralCube ≤ C·kinFormB`; and `IsLowB` gives
`kinFormB ≤ μ·M_w` (split `wordB = kinFormB + chemPartB + pairPartB`, use
`Work.BoseFixB1B.isLowB_chemBoundAlt` for `μ·M_w ≥ 4πμ²(a v)ℓ³(1−J√(μ(a v)³))‖Φ‖² ≥ 0` together with
`kinFormB ≥ 0`, `pairPartB ≥ 0`, and `wordB ≤ ℓ³·Theta·normB ≤ 0` for `t < J^{-2}`).  One also
needs `0 ≤ bSpectral` and the rows `≥ 0` to land on the two-sided right-hand side. -/
theorem slidingWindowComparisonWeighted {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u
            ≤ Work.BoseFixB1.bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
              + C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ (-2 : ℤ)
                  * Submission.BoseGases.chiSupAbs ^ 2
                  * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                      (Φ : Submission.BoseGases.X n → ℝ)
                  + (μ ^ 2 * (_root_.BoseGases.a v)
                        * Work.SmallBoxSliding.chiMass
                            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                      + μ * (_root_.BoseGases.a v))
                      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + μ ^ 2 * (_root_.BoseGases.a v)
                      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                        (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
                          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                            (Submission.BoseGases.g0 v h) 0 (x i) y))) := by sorry

end Work.BoseFixB1B
