import Mathlib
import Submission.NormalSplit
import Submission.ThresholdMeas
import Submission.BernoulliSmallBall
import Submission.GeoBridge
import Submission.Commons.Measure.Probability.indepFun_measureReal_le_mul_of_fiber_le

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetFiber

attribute [local instance] Classical.propDecidable

open Submission.NormalSplit
open Submission.IncompReduction
open Submission.ThresholdMeas

/-- General fibre bound: for a measurable set `H` of candidate normals on which
the last-column fibre small-ball bound holds with constant `c`, the probability
of `{normalLe r ∧ Y ∈ H}` is at most `c` times the probability of `{Y ∈ H}`. -/
theorem fiber_bound_general {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 1 ≤ n) {p : I}
    (Bc : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => Bc ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (Bc · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (Bc · i j) (bernoulliMeasure 1 0 p) P)
    {s L r S : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hS : 0 < S)
    {H : Set (Fin n → ℝ)} (hH : MeasurableSet H)
    (hbound : ∀ a : Fin n → ℝ, a ∈ H →
      (P.map (lastColMap hn Bc)).real {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r}
        ≤ L * max (2 * S) r) :
    P.real {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧ yfnMap s Bc ω ∈ H}
      ≤ (L * max (2 * S) r) * P.real {ω : Ω | yfnMap s Bc ω ∈ H} := by
  let A : Ω → (Fin n → ℝ) := yfnMap s Bc
  let Z : Ω → (Fin n → ℝ) := lastColMap hn Bc
  let Sf : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {pp | |∑ i : Fin n, (pp.2 i + s) * pp.1 i| ≤ r}
  let c : ℝ := L * max (2 * S) r
  have hAmeas : Measurable A := measurable_yfnMap s Bc hBmeas
  have hZmeas : Measurable Z := measurable_lastColMap hn Bc hBmeas
  have hind : ProbabilityTheory.IndepFun A Z P := by
    dsimp [A, Z]
    exact indepFun_yfnMap_lastColMap hn P s Bc hBmeas hBind
  have hSf : MeasurableSet Sf := by
    dsimp [Sf]
    exact measurableSet_fiberPair s r
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hL0 : 0 ≤ L := by linarith
    exact mul_nonneg hL0 (le_trans (le_of_lt hr) (le_max_right (2 * S) r))
  have hfib := Commons.Measure.Probability.indepFun_measureReal_le_mul_of_fiber_le P A Z
    hAmeas.aemeasurable hZmeas.aemeasurable hind Sf hSf H hH c hc0
    (fun a ha => by simpa only [c, Sf, Set.mem_setOf_eq] using hbound a ha)
  have hEvMain : {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧ yfnMap s Bc ω ∈ H}
      = {ω : Ω | (A ω, Z ω) ∈ Sf ∧ A ω ∈ H} := by
    ext ω
    dsimp [A, Z, Sf]
    rw [normalLe_shift_iff hn s (Bc ω) r]
    rfl
  calc P.real {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧ yfnMap s Bc ω ∈ H}
      = P.real {ω : Ω | (A ω, Z ω) ∈ Sf ∧ A ω ∈ H} := by rw [hEvMain]
    _ ≤ c * P.real {ω : Ω | A ω ∈ H} := hfib
    _ = (L * max (2 * S) r) * P.real {ω : Ω | yfnMap s Bc ω ∈ H} := by
        dsimp [c, A]

/-- Fibre bound over the threshold annulus `(T/2, T]` (measurable entries). -/
theorem fiber_bound_annulus_meas {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 1 ≤ n) {p : I}
    (Bc : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => Bc ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (Bc · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (Bc · i j) (bernoulliMeasure 1 0 p) P)
    {s L T r : ℝ} (hL : 1 ≤ L) (hT : 0 < T) (hr : 0 < r) :
    P.real {ω : Ω | normalLe hn (shiftMatrix s (Bc ω)) r ∧
        T / 2 < Submission.Threshold.threshold p (yfnMap s Bc ω) L ∧
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ T}
      ≤ (L * max (2 * T) r) * P.real {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (yfnMap s Bc ω) L ∧
        Submission.Threshold.threshold p (yfnMap s Bc ω) L ≤ T} := by
  have hH : MeasurableSet {y : Fin n → ℝ |
      T / 2 < Submission.Threshold.threshold p y L ∧
      Submission.Threshold.threshold p y L ≤ T} :=
    measurableSet_threshold_annulus p hL (by linarith) (by linarith)
  -- independence of the last-column entries and their laws
  have hbXind : ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun ω : Ω => Bc ω i (lastFin hn)) P := by
    have hg : Function.Injective (fun i : Fin n => (i, lastFin hn)) := by
      intro a b h
      exact congrArg Prod.fst h
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (Bc · x.1 x.2))
      (g := fun i : Fin n => (i, lastFin hn)) hg hBind
    simpa using hpre
  have hbXmeas : ∀ i : Fin n, Measurable (fun ω : Ω => Bc ω i (lastFin hn)) :=
    fun i => hBmeas i (lastFin hn)
  have hbXlaw : ∀ i : Fin n, HasLaw (fun ω : Ω => Bc ω i (lastFin hn))
      (bernoulliMeasure 1 0 p) P := fun i => hBlaw i (lastFin hn)
  refine fiber_bound_general P hn Bc hBmeas hBind hBlaw hL hr hT hH ?_
  intro a ha
  have haT : Submission.Threshold.threshold p a L ≤ T := ha.2
  have hbb := Submission.BernoulliSmallBall.bernoulli_vector_smallBall_le_of_threshold P
    (X := fun i : Fin n => fun ω : Ω => Bc ω i (lastFin hn))
    hbXmeas hbXind hbXlaw (y := a) hL hr hT haT (s * ∑ i : Fin n, a i) (0 : ℝ)
  -- identify the two events
  have hEvE : {b : Fin n → ℝ | (a, b) ∈ ({pp : (Fin n → ℝ) × (Fin n → ℝ) |
        |∑ i : Fin n, (pp.2 i + s) * pp.1 i| ≤ r})}
      = {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r} := by
    ext b
    rfl
  have hPre : (lastColMap hn Bc) ⁻¹' {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r}
      = {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := by
    ext ω
    rfl
  have hMeasE : MeasurableSet {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r} := by
    have hG : Measurable (fun b : Fin n → ℝ => |∑ i : Fin n, (b i + s) * a i|) := by
      fun_prop
    change MeasurableSet ((fun b : Fin n → ℝ => |∑ i : Fin n, (b i + s) * a i|) ⁻¹' (Set.Iic r))
    exact hG (isClosed_Iic.measurableSet)
  have hmap : (P.map (lastColMap hn Bc)).real
        {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r}
      = P.real {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := by
    rw [Measure.real_def, Measure.real_def, Measure.map_apply (measurable_lastColMap hn Bc hBmeas) hMeasE,
      hPre]
  have hsum : {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r}
      = {ω : Ω | |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r} := by
    ext ω
    have hs : (∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i)
        = (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * (∑ i : Fin n, a i) := by
      calc (∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i)
          = ∑ i : Fin n, (Bc ω i (lastFin hn) * a i + s * a i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + ∑ i : Fin n, s * a i := by
            rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * (∑ i : Fin n, a i) := by
            rw [Finset.mul_sum]
    simp only [Set.mem_setOf_eq]
    rw [hs]
  have hbb' : P.real {ω : Ω |
        |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r}
      ≤ L * max (2 * T) r := by
    simpa using hbb
  calc (P.map (lastColMap hn Bc)).real {b : Fin n → ℝ | |∑ i : Fin n, (b i + s) * a i| ≤ r}
      = P.real {ω : Ω | |∑ i : Fin n, (Bc ω i (lastFin hn) + s) * a i| ≤ r} := hmap
    _ = P.real {ω : Ω | |(∑ i : Fin n, Bc ω i (lastFin hn) * a i) + s * ∑ i : Fin n, a i| ≤ r} := by
        rw [hsum]
    _ ≤ L * max (2 * T) r := hbb'

/-- Fibre bound over the threshold annulus `(T/2, T]` (law-only hypotheses). -/
theorem fiber_bound_annulus {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 1 ≤ n) {p : I}
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    {s L T r : ℝ} (hL : 1 ≤ L) (hT : 0 < T) (hr : 0 < r) :
    P.real {ω : Ω | normalLe hn (shiftMatrix s (B ω)) r ∧
        T / 2 < Submission.Threshold.threshold p (yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ T}
      ≤ (L * max (2 * T) r) * P.real {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ T} := by
  classical
  rcases Submission.GeoBridge.exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  have hmain := fiber_bound_annulus_meas P hn (Bc := Bc) hcm hcind hclaw (s := s) (L := L)
    (T := T) (r := r) hL hT hr
  let S1 : Set (Matrix (Fin n) (Fin n) ℝ) := {M | normalLe hn (shiftMatrix s M) r ∧
      T / 2 < Submission.Threshold.threshold p (yfnOf s M) L ∧
      Submission.Threshold.threshold p (yfnOf s M) L ≤ T}
  let S2 : Set (Matrix (Fin n) (Fin n) ℝ) := {M |
      T / 2 < Submission.Threshold.threshold p (yfnOf s M) L ∧
      Submission.Threshold.threshold p (yfnOf s M) L ≤ T}
  have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) :=
    fun i j => (hcae i j).symm
  have htr1 : P.real {ω : Ω | B ω ∈ S1} = P.real {ω : Ω | Bc ω ∈ S1} :=
    Submission.GeoBridge.measureReal_matrix_event_eq_of_ae P B Bc hae' S1
  have htr2 : P.real {ω : Ω | B ω ∈ S2} = P.real {ω : Ω | Bc ω ∈ S2} :=
    Submission.GeoBridge.measureReal_matrix_event_eq_of_ae P B Bc hae' S2
  have hmain' : P.real {ω : Ω | Bc ω ∈ S1} ≤ (L * max (2 * T) r) * P.real {ω : Ω | Bc ω ∈ S2} := by
    simpa [S1, S2, yfnMap] using hmain
  calc P.real {ω : Ω | normalLe hn (shiftMatrix s (B ω)) r ∧
        T / 2 < Submission.Threshold.threshold p (yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ T}
      = P.real {ω : Ω | B ω ∈ S1} := by rfl
    _ = P.real {ω : Ω | Bc ω ∈ S1} := htr1
    _ ≤ (L * max (2 * T) r) * P.real {ω : Ω | Bc ω ∈ S2} := hmain'
    _ = (L * max (2 * T) r) * P.real {ω : Ω | B ω ∈ S2} := by rw [htr2]
    _ = (L * max (2 * T) r) * P.real {ω : Ω |
          T / 2 < Submission.Threshold.threshold p (yfnOf s (B ω)) L ∧
          Submission.Threshold.threshold p (yfnOf s (B ω)) L ≤ T} := by rfl

end Submission.NetFiber
