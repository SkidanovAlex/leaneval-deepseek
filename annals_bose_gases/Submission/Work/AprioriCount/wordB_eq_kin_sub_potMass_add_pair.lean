import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.AprioriCount.pairHalfDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AprioriCount

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `wLoc ℓ gg 0 a b = wPair ℓ gg a b`: the anchored potential `w_{1,u}` at `u = 0` is the sliding
kernel of `KernelIds`. -/
private lemma wLoc_zero_eq_wPair (ℓ : ℝ) (gg : E3 → ℝ) (a b : E3) :
    Submission.BoseGases.wLoc ℓ gg 0 a b = Submission.BoseGases.wPair ℓ gg a b := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPair, Submission.BoseGases.chiU,
    Submission.BoseGases.chiScale]

/-- The one-body (`wLoc ℓ g 0`) mass integrand is `L¹` on the box `abox n ℓ`, in the anchored
form: transport the anchored kernel to the sliding one pointwise and use
`Work.BoseFixB1B.integrableOn_oneBody_wPair`. -/
private lemma integrableOn_oneBody_wLoc_zero {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {g : E3 → ℝ} (hi : MeasureTheory.Integrable g)
    (hsupp : ∀ z : E3, R ≤ ‖z‖ → g z = 0) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, ∫ y : E3, Submission.BoseGases.wLoc ℓ g 0 (x i) y))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 := Work.BoseFixB1B.integrableOn_oneBody_wPair hℓ hR hRℓ hi hsupp hΦc
  have hsumEq : ∀ x : Submission.BoseGases.X n,
      (∑ i : Fin n, ∫ y : E3, Submission.BoseGases.wLoc ℓ g 0 (x i) y)
        = ∑ i : Fin n, ∫ y : E3, Submission.BoseGases.wPair ℓ g (x i) y :=
    fun x => Finset.sum_congr rfl fun i _ => MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => wLoc_zero_eq_wPair ℓ g (x i) y)
  exact h1.congr_fun (fun x _ => by simp only [hsumEq x])
    (Submission.BoseGases.abox_measurable n ℓ)

/-- The two-body (`wLoc ℓ v 0`) mass integrand is `L¹` on the box `abox n ℓ`, in the anchored
form: transport the anchored kernel to the sliding one pointwise and use
`Work.BoseFixB1B.integrableOn_pair_wPair`. -/
private lemma integrableOn_pair_wLoc_zero {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {vv : E3 → ℝ} (hv1 : MeasureTheory.MemLp vv 1)
    (hsupp : ∀ z : E3, R ≤ ‖z‖ → vv z = 0) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc ℓ vv 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 := Work.BoseFixB1B.integrableOn_pair_wPair hℓ hR hRℓ hv1 hsupp hΦc
  have hsumEq : ∀ x : Submission.BoseGases.X n,
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ vv 0 (x ij.1.1) (x ij.1.2))
        = ∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
            Submission.BoseGases.wPair ℓ vv (x ij.1.1) (x ij.1.2) :=
    fun x => Finset.sum_congr rfl fun ij _ => wLoc_zero_eq_wPair ℓ vv _ _
  exact h1.congr_fun (fun x _ => by simp only [hsumEq x])
    (Submission.BoseGases.abox_measurable n ℓ)

/-- **The box-word splitting in the `potMass` currency** (reviewed; the `ε₀` of the first draft is
replaced by the explicit range condition `hRℓ`, which is the only thing the measure theory needs).

For `μ` with `R ≤ sideAt μ (a v)·chiR0` and any smooth symmetric box state `Φ` (no support
condition) at the sliding box `ℓ = sideAt μ (a v)`,

`wordB v h μ n Φ = kinFormB … Φ − μ·potMass ℓ v h Φ + pairPartB n v ℓ Φ`.

Proof template: `Work.BoseFixB1B.lowBudgetSupply`
(`Submission/Work/BoseFixB1B/slidingWindowComparisonWeighted.lean`) **minus its `0 ≤ v` hypothesis**
(which that file only passes through to `boxFormB_budgetAlt`, whose proof never uses it): discharge
the two `IntegrableOn` side conditions of
`Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable` with
`Work.BoseFixB1B.integrableOn_oneBody_wPair` (`hh := g₀ v h`, integrable by `g0_integrable` and
vanishing for `R ≤ ‖z‖` by `g0_zero_of_norm_ge`) and
`Work.BoseFixB1B.integrableOn_pair_wPair` (`vv := v`, `hv1`; `∀z, R ≤ ‖z‖ → v z = 0` from
`subset_tsupport` and `hv_supp`), rewriting `wPair ℓ g a b = wLoc ℓ g 0 a b` pointwise as in
`lowBudgetSupply`; then `wordB = boxFormB` is `rfl` and `chemPartB n (g₀ v h) ℓ μ Φ = −μ·potMass`
by `MeasureTheory.integral_const_mul` after unfolding `potMass`/`potBr`
(`potBr ℓ gK u a := ∫_y wLoc ℓ gK u a y`).  No `0 ≤ v`, no `IsLowB`, no `J`. -/
theorem wordB_eq_kin_sub_potMass_add_pair {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ : ℝ} (hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
          (Φ : Submission.BoseGases.X n → ℝ)
        - μ * Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v h
            (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the range condition forces the sliding side to be positive (`chiR0 > 0`)
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    nlinarith [hR, hRℓ, Submission.BoseGases.chiR0_pos]
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
  -- the two `IntegrableOn` side conditions of `boxFormB_eq_parts_of_integrable`
  have hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : E3,
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
    have h1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
      integrableOn_oneBody_wLoc_zero hℓpos (le_of_lt hR) hRℓ hg0int hg0supp hΦc
    have h2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (-μ) *
        ((Φ x) ^ 2 * (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y)))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
      MeasureTheory.Integrable.const_mul h1 (-μ)
    exact h2.congr_fun (fun x _ => by ring) (Submission.BoseGases.abox_measurable n _)
  have hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0
          (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    integrableOn_pair_wLoc_zero hℓpos (le_of_lt hR) hRℓ hv1 hvzero hΦc
  -- the splitting of the box form
  have hsplit := Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (μ := μ)
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
    (v := v) (g := Submission.BoseGases.g0 v h)
    (Φ : Submission.BoseGases.X n → ℝ) hA hB
  -- the chemical part is `−μ·potMass`
  have hchem : Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ (Φ : Submission.BoseGases.X n → ℝ)
      = -μ * Work.AprioriCount.potMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v h
          (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseKinLoc.chemPartB, Work.AprioriCount.potMass]
    simp only [Work.BoseBox.potBr]
    have hpt : ∀ x : Submission.BoseGases.X n, (Φ x) ^ 2 * (-μ * (∑ i : Fin n, ∫ y : E3,
          Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 (x i) y))
        = (-μ) * ((Φ x) ^ 2 * (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0 (x i) y)) := fun x => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_const_mul]
  -- `wordB` is `boxFormB` by definition
  have hword : Work.BoseBoxFix.wordB v h μ n (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) μ
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
          (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hword, hsplit, hchem]
  ring

end Work.AprioriCount
