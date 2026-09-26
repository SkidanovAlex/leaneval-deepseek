import Mathlib
import Submission.Commons.Topology.OneManifold.arc_extension_or_compact
import Submission.Commons.Topology.OneManifold.oneManifold_dichotomy

open Set Filter
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-- The open unit interval `(0,1)` is not compact (as a topological space). -/
theorem unitInterval_not_compact : ¬ CompactSpace ORI := by
  intro h
  have hIs : IsCompact (Set.Ioo (0 : ℝ) 1 : Set ℝ) := isCompact_iff_compactSpace.mpr h
  have hle : (1 : ℝ) ≤ 0 := isCompact_Ioo_iff.mp hIs
  norm_num at hle

/-- A compact space cannot be homeomorphic to the open unit interval. -/
theorem not_homeo_unitInterval_of_compact {X : Type*} [TopologicalSpace X]
    (hcmp : CompactSpace X) : ¬ Nonempty (ORI ≃ₜ X) := by
  rintro ⟨e⟩
  haveI : CompactSpace X := hcmp
  exact unitInterval_not_compact (e.symm.compactSpace)

/-- **Zorn maximal proper open arc.**  A connected Hausdorff second-countable
locally interval-charted space that is not itself an open unit interval
contains a proper open arc which is maximal (cannot be strictly enlarged to
another open arc). -/
lemma exists_maximal_proper_open_arc {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    (hArc : ¬ Nonempty (ORI ≃ₜ X)) :
    ∃ P : Set X, IsOpen P ∧ P ≠ Set.univ ∧ Nonempty (ORI ≃ₜ P) ∧
      ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  rcases local_unit_arc (X := X) hLoc x₀ with ⟨U₀, hU₀open, hx₀U₀, eU₀⟩
  have hU₀ne : U₀ ≠ Set.univ := by
    intro hU
    apply hArc
    rcases eU₀ with ⟨e⟩
    rw [hU] at e
    exact ⟨e.trans (Homeomorph.Set.univ X)⟩
  have hU₀S : U₀ ∈ OpenArc U₀ := ⟨hU₀open, Subset.rfl, hU₀ne, eU₀⟩
  have hbdd : ∀ c : Set (Set X), c ⊆ OpenArc U₀ →
      IsChain (fun A B : Set X => A ⊆ B) c → ∃ ub ∈ OpenArc U₀, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hch
    exact open_arcs_chain_upper_bound hArc hU₀S hcS hch
  rcases zorn_subset (OpenArc U₀) hbdd with ⟨m, hm⟩
  have hmS : m ∈ OpenArc U₀ := hm.1
  have hmmax : ∀ y : Set X, y ∈ OpenArc U₀ → m ⊆ y → y ⊆ m := by
    intro y hy
    exact hm.2 hy
  have hmopen : IsOpen m := hmS.1
  have hU₀m : U₀ ⊆ m := hmS.2.1
  have hmne : m ≠ Set.univ := hmS.2.2.1
  have hem : Nonempty (ORI ≃ₜ m) := hmS.2.2.2
  refine ⟨m, hmopen, hmne, hem, ?_⟩
  rintro ⟨Q, hQopen, hPQ, hQarc⟩
  by_cases hQuniv : Q = Set.univ
  · apply hArc
    rcases hQarc with ⟨eq⟩
    rw [hQuniv] at eq
    exact ⟨eq.trans (Homeomorph.Set.univ X)⟩
  · have hQS : Q ∈ OpenArc U₀ := ⟨hQopen, Subset.trans hU₀m hPQ.1, hQuniv, hQarc⟩
    have hQm : Q ⊆ m := hmmax Q hQS hPQ.1
    exact hPQ.2 hQm

/-- **End convergence of a maximal arc.**  A maximal proper open arc
`P` misses exactly one point `z₀` of `X`; the two ends of the arc converge
to `z₀`, and every other point of `X` lies in `P`. -/
lemma maximal_arc_end_convergence {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)) :
    ∃ z₀ : X, z₀ ∉ P ∧
      (∀ V : Set X, IsOpen V → z₀ ∈ V →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ORI, (t : ℝ) < δ → ChartVal.chartVal (Classical.choice eP) t ∈ V) ∧
      (∀ V : Set X, IsOpen V → z₀ ∈ V →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ORI, 1 - δ < (t : ℝ) → ChartVal.chartVal (Classical.choice eP) t ∈ V) ∧
      (∀ y : X, y ≠ z₀ → y ∈ P) := by
  classical
  let e := Classical.choice eP
  rcases BdryExt.maximal_arc_ends_close hLoc eP hPopen hPproper hPmax with ⟨z₀, hz₀P, hattL, hattR, hunique⟩
  have hdense : closure P = Set.univ := BdryExt.maximal_arc_dense hLoc eP hPopen hPproper hPmax
  have hz₀b : z₀ ∈ closure P \ P := ⟨by rw [hdense]; trivial, hz₀P⟩
  rcases BdryExt.boundary_points_isolated_of_maximal hLoc eP hPopen hPproper hPmax hz₀b with
    ⟨W, hWopen, hz₀W, ψ, hEq⟩
  let c₀ : ℝ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).1
  have hc₀₀ : 0 < c₀ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.1
  have hc₀₁ : c₀ < 1 := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.2
  have hz₀ψ : z₀ = BdryExt.cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W} => (w : X))
      (ψ.apply_symm_apply ⟨z₀, hz₀W⟩)
    change z₀ = (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).1
    dsimp [c₀, BdryExt.cv]
    exact hh.symm
  have hstruct : P ∩ W = W \ {BdryExt.cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
    simpa [hz₀ψ] using hEq
  have hattLψ : ∀ a : ℝ, 0 < a → a < 1 →
      BdryExt.cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a) := by
    intro a ha0 ha1
    rw [← hz₀ψ]
    exact hattL a ha0 ha1
  have hattRψ : ∀ b : ℝ, 0 < b → b < 1 →
      BdryExt.cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e b 1) := by
    intro b hb0 hb1
    rw [← hz₀ψ]
    exact hattR b hb0 hb1
  refine ⟨z₀, hz₀P, ?_, ?_, hunique⟩
  · -- left end convergence
    intro V hVopen hzV
    exact TailConv.left_tail_converges e hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattLψ hVopen
      (by simpa [hz₀ψ] using hzV)
  · -- right end convergence
    intro V hVopen hzV
    exact TailConv.right_tail_converges e hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattRψ hVopen
      (by simpa [hz₀ψ] using hzV)

end Commons.Topology.OneManifold

namespace Commons.Topology.OneManifold

namespace CircleData

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P : Set X}

/-- The closed-up arc curve `ℝ → X`: the chart `e` on `(0,1)`, and the
boundary point `z₀` everywhere else. -/
noncomputable def arcCurve (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) : ℝ → X :=
  fun r => if h : r ∈ Set.Ioo (0 : ℝ) 1 then ChartVal.chartVal e ⟨r, h⟩ else z₀

lemma arcCurve_of_mem (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) : arcCurve e z₀ r = ChartVal.chartVal e ⟨r, hr⟩ := by
  simp [arcCurve, hr]

lemma arcCurve_of_not_mem (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) {r : ℝ}
    (hr : r ∉ Set.Ioo (0 : ℝ) 1) : arcCurve e z₀ r = z₀ := by
  simp [arcCurve, hr]

lemma not_mem_Ioo_of_le_zero {r : ℝ} (hr : r ≤ (0 : ℝ)) : r ∉ Set.Ioo (0 : ℝ) 1 := by
  intro h
  exact (not_lt_of_ge hr) h.1

lemma not_mem_Ioo_of_one_le {r : ℝ} (hr : (1 : ℝ) ≤ r) : r ∉ Set.Ioo (0 : ℝ) 1 := by
  intro h
  exact (not_le_of_gt h.2) hr

lemma arcCurve_zero (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) : arcCurve e z₀ 0 = z₀ := by
  apply arcCurve_of_not_mem
  exact not_mem_Ioo_of_le_zero le_rfl

lemma arcCurve_one (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) : arcCurve e z₀ 1 = z₀ := by
  apply arcCurve_of_not_mem
  exact not_mem_Ioo_of_one_le le_rfl

lemma arcCurve_zero_eq_one (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    arcCurve e z₀ 0 = arcCurve e z₀ 1 := by
  rw [arcCurve_zero, arcCurve_one]

/-- Continuity on the middle open interval. -/
lemma arcCurve_contOn_mid (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    ContinuousOn (arcCurve e z₀) (Set.Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (Set.Ioo (0 : ℝ) 1).domRestrict (arcCurve e z₀) = ChartVal.chartVal e := by
    funext t
    change arcCurve e z₀ (t : ℝ) = ChartVal.chartVal e t
    rw [arcCurve_of_mem e z₀ t.2]
  rw [hEq]
  exact ChartVal.chartVal_continuous e

/-- Constancy on the left ray. -/
lemma arcCurve_eq_z₀_left (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    Set.EqOn (arcCurve e z₀) (fun _ : ℝ => z₀) (Set.Iio (0 : ℝ)) := by
  intro r hr
  apply arcCurve_of_not_mem
  exact not_mem_Ioo_of_le_zero (le_of_lt hr)

lemma arcCurve_contOn_left (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    ContinuousOn (arcCurve e z₀) (Set.Iio (0 : ℝ)) := by
  exact (continuousOn_congr (g := arcCurve e z₀) (f := fun _ : ℝ => z₀)
    (s := Set.Iio (0 : ℝ)) (arcCurve_eq_z₀_left e z₀)).mpr continuousOn_const

/-- Constancy on the right ray. -/
lemma arcCurve_eq_z₀_right (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    Set.EqOn (arcCurve e z₀) (fun _ : ℝ => z₀) (Set.Ioi (1 : ℝ)) := by
  intro r hr
  apply arcCurve_of_not_mem
  exact not_mem_Ioo_of_one_le (le_of_lt hr)

lemma arcCurve_contOn_right (e : ORI ≃ₜ {x : X // x ∈ P}) (z₀ : X) :
    ContinuousOn (arcCurve e z₀) (Set.Ioi (1 : ℝ)) := by
  exact (continuousOn_congr (g := arcCurve e z₀) (f := fun _ : ℝ => z₀)
    (s := Set.Ioi (1 : ℝ)) (arcCurve_eq_z₀_right e z₀)).mpr continuousOn_const

/-- Continuity at `0` from the left-tail convergence of the arc. -/
lemma arcCurve_continuousAt_zero (e : ORI ≃ₜ {x : X // x ∈ P}) {z₀ : X}
    (hleft : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, (t : ℝ) < δ → ChartVal.chartVal e t ∈ V) :
    ContinuousAt (arcCurve e z₀) 0 := by
  rw [ContinuousAt, arcCurve_zero e z₀]
  rw [tendsto_nhds]
  intro V hVopen hzV
  rcases hleft V hVopen hzV with ⟨δ, hδ₀, htail⟩
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδ₀, ?_⟩
  intro y hy
  change arcCurve e z₀ y ∈ V
  have hyδ : |y| < δ := by
    simpa [Real.dist_eq, sub_zero] using hy
  by_cases hy0 : y = 0
  · rw [hy0, arcCurve_zero e z₀]
    exact hzV
  · rcases lt_or_gt_of_ne hy0 with hyneg | hypos
    · rw [arcCurve_of_not_mem e z₀ (not_mem_Ioo_of_le_zero (le_of_lt hyneg))]
      exact hzV
    · by_cases hy1 : y < 1
      · let t : ORI := ⟨y, ⟨hypos, hy1⟩⟩
        have hyt : (t : ℝ) < δ := by
          dsimp [t]
          rw [abs_of_pos hypos] at hyδ
          exact hyδ
        have hyV : ChartVal.chartVal e t ∈ V := htail t hyt
        rw [arcCurve_of_mem e z₀ ⟨hypos, hy1⟩]
        exact hyV
      · have hyge1 : 1 ≤ y := le_of_not_gt hy1
        rw [arcCurve_of_not_mem e z₀ (not_mem_Ioo_of_one_le hyge1)]
        exact hzV

/-- Continuity at `1` from the right-tail convergence of the arc. -/
lemma arcCurve_continuousAt_one (e : ORI ≃ₜ {x : X // x ∈ P}) {z₀ : X}
    (hright : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, 1 - δ < (t : ℝ) → ChartVal.chartVal e t ∈ V) :
    ContinuousAt (arcCurve e z₀) 1 := by
  rw [ContinuousAt, arcCurve_one e z₀]
  rw [tendsto_nhds]
  intro V hVopen hzV
  rcases hright V hVopen hzV with ⟨δ, hδ₀, htail⟩
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδ₀, ?_⟩
  intro y hy
  change arcCurve e z₀ y ∈ V
  have hyδ : |y - 1| < δ := by
    simpa [Real.dist_eq] using hy
  by_cases hyge1 : 1 ≤ y
  · rw [arcCurve_of_not_mem e z₀ (not_mem_Ioo_of_one_le hyge1)]
    exact hzV
  · have hy1 : y < 1 := lt_of_not_ge hyge1
    by_cases hyle0 : y ≤ 0
    · rw [arcCurve_of_not_mem e z₀ (not_mem_Ioo_of_le_zero hyle0)]
      exact hzV
    · have hypos : 0 < y := lt_of_not_ge hyle0
      have hyδ' : 1 - δ < y := by
        have habs : |1 - y| < δ := by
          simpa [abs_sub_comm] using hyδ
        have hpos : 0 < 1 - y := sub_pos.mpr hy1
        have h1y : 1 - y < δ := by
          simpa [abs_of_pos hpos] using habs
        linarith
      let t : ORI := ⟨y, ⟨hypos, hy1⟩⟩
      have hyt : 1 - δ < (t : ℝ) := by
        dsimp [t]
        exact hyδ'
      have hyV : ChartVal.chartVal e t ∈ V := htail t hyt
      rw [arcCurve_of_mem e z₀ ⟨hypos, hy1⟩]
      exact hyV

/-- The closed arc curve is continuous everywhere. -/
lemma arcCurve_continuous (e : ORI ≃ₜ {x : X // x ∈ P}) {z₀ : X}
    (hleft : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, (t : ℝ) < δ → ChartVal.chartVal e t ∈ V)
    (hright : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, 1 - δ < (t : ℝ) → ChartVal.chartVal e t ∈ V) :
    Continuous (arcCurve e z₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hxlt | hxeq | hxgt
  · exact ContinuousOn.continuousAt (arcCurve_contOn_left e z₀) (isOpen_Iio.mem_nhds hxlt)
  · subst hxeq
    exact arcCurve_continuousAt_zero e hleft
  · rcases lt_trichotomy x 1 with hxlt1 | hxeq1 | hxgt1
    · exact ContinuousOn.continuousAt (arcCurve_contOn_mid e z₀)
        (isOpen_Ioo.mem_nhds ⟨hxgt, hxlt1⟩)
    · subst hxeq1
      exact arcCurve_continuousAt_one e hright
    · exact ContinuousOn.continuousAt (arcCurve_contOn_right e z₀) (isOpen_Ioi.mem_nhds hxgt1)

/-- The curve takes the value `z₀` exactly outside the open interval `(0,1)`. -/
lemma arcCurve_eq_z₀_iff (e : ORI ≃ₜ {x : X // x ∈ P}) {z₀ : X} (hz₀P : z₀ ∉ P) {r : ℝ} :
    arcCurve e z₀ r = z₀ ↔ r ∉ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · intro h hr
    have hval : arcCurve e z₀ r = ChartVal.chartVal e ⟨r, hr⟩ := arcCurve_of_mem e z₀ hr
    have hP : arcCurve e z₀ r ∈ P := by
      rw [hval]
      exact (e ⟨r, hr⟩).2
    exact hz₀P (by rwa [h] at hP)
  · intro hr
    exact arcCurve_of_not_mem e z₀ hr

/-- Injectivity of the curve on `[0,1)`: two half-open representatives
with the same curve value coincide. -/
lemma arcCurve_eq_of_Ico (e : ORI ≃ₜ {x : X // x ∈ P}) {z₀ : X} (hz₀P : z₀ ∉ P) {a b : ℝ}
    (ha : a ∈ Set.Ico (0 : ℝ) 1) (hb : b ∈ Set.Ico 0 1)
    (h : arcCurve e z₀ a = arcCurve e z₀ b) : a = b := by
  by_cases ha0 : a = 0
  · have hfa : arcCurve e z₀ a = z₀ := by
      rw [ha0]
      exact arcCurve_zero e z₀
    have hfb : arcCurve e z₀ b = z₀ := by
      calc
        arcCurve e z₀ b = arcCurve e z₀ a := h.symm
        _ = z₀ := hfa
    by_contra hab
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hab
      rw [ha0, hb0]
    have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
    have hbmem : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨hbpos, hb.2⟩
    have hbval : arcCurve e z₀ b = ChartVal.chartVal e ⟨b, hbmem⟩ := arcCurve_of_mem e z₀ hbmem
    have hbP : arcCurve e z₀ b ∈ P := by
      rw [hbval]
      exact (e ⟨b, hbmem⟩).2
    exact hz₀P (by rwa [hfb] at hbP)
  · have hapos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hamem : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨hapos, ha.2⟩
    have hfaP : arcCurve e z₀ a ∈ P := by
      rw [arcCurve_of_mem e z₀ hamem]
      exact (e ⟨a, hamem⟩).2
    have hb0 : b ≠ 0 := by
      intro hb0
      have hfb : arcCurve e z₀ b = z₀ := by
        rw [hb0]
        exact arcCurve_zero e z₀
      have hzmem : arcCurve e z₀ a = z₀ := by
        calc
          arcCurve e z₀ a = arcCurve e z₀ b := h
          _ = z₀ := hfb
      exact hz₀P (by simpa [hzmem] using hfaP)
    have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
    have hbmem : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨hbpos, hb.2⟩
    have hEq : ChartVal.chartVal e ⟨a, hamem⟩ = ChartVal.chartVal e ⟨b, hbmem⟩ := by
      rw [← arcCurve_of_mem e z₀ hamem, ← arcCurve_of_mem e z₀ hbmem]
      exact h
    have haEqb : (⟨a, hamem⟩ : ORI) = (⟨b, hbmem⟩ : ORI) := ChartVal.chartVal_injective e hEq
    exact congrArg (fun w : ORI => (w : ℝ)) haEqb

end CircleData

end Commons.Topology.OneManifold

namespace Commons.Topology.OneManifold

theorem compact_connected_oneManifold_circle
    {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    (hconn : ConnectedSpace X) (hcmp : CompactSpace X) :
    Nonempty (Circle ≃ₜ X) := by
  classical
  letI : ConnectedSpace X := hconn
  letI : CompactSpace X := hcmp
  have hArc : ¬ Nonempty (ORI ≃ₜ X) := not_homeo_unitInterval_of_compact hcmp
  rcases exists_maximal_proper_open_arc hLoc hArc with ⟨P, hPopen, hPproper, eP, hPmax⟩
  rcases maximal_arc_end_convergence hLoc eP hPopen hPproper hPmax with
    ⟨z₀, hz₀P, hleftConv, hrightConv, hunique⟩
  let e := Classical.choice eP
  let f : ℝ → X := CircleData.arcCurve e z₀
  have hfcont : Continuous f := by
    dsimp [f]
    exact CircleData.arcCurve_continuous e hleftConv hrightConv
  have hf01 : f 0 = f 1 := by
    dsimp [f]
    exact CircleData.arcCurve_zero_eq_one e z₀
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let φ : AddCircle (1 : ℝ) → X := AddCircle.liftIco (p := (1 : ℝ)) (a := 0) f
  have hφcont : Continuous φ := by
    dsimp [φ]
    exact AddCircle.liftIco_zero_continuous (p := (1 : ℝ)) hf01 hfcont.continuousOn
  -- surjectivity
  have hφsurj : Function.Surjective φ := by
    intro x
    by_cases hxz : x = z₀
    · refine ⟨0, ?_⟩
      have hφ0 : φ (0 : AddCircle (1 : ℝ)) = f 0 := by
        dsimp [φ]
        simpa using (AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ)) (f := f) (x := (0 : ℝ))
          (by simp : (0 : ℝ) ∈ Set.Ico 0 (1 : ℝ)))
      rw [hxz]
      calc
        φ (0 : AddCircle (1 : ℝ)) = f 0 := hφ0
        _ = z₀ := by
          dsimp [f]
          exact CircleData.arcCurve_zero e z₀
    · have hxP : x ∈ P := hunique x hxz
      have hxr : x ∈ Set.range (ChartVal.chartVal e) := by
        rw [ChartVal.chartVal_range e]
        exact hxP
      rcases hxr with ⟨t, ht⟩
      refine ⟨((t : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      have htIco : (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt t.2.1, t.2.2⟩
      calc
        φ ((t : ℝ) : AddCircle (1 : ℝ)) = f (t : ℝ) := by
          dsimp [φ]
          simpa using (AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ)) (f := f) (x := (t : ℝ)) htIco)
        _ = ChartVal.chartVal e t := by
          dsimp [f]
          exact CircleData.arcCurve_of_mem e z₀ t.2
        _ = x := ht
  -- injectivity
  have hφinj : Function.Injective φ := by
    intro u v huv
    let s := AddCircle.equivIco (p := (1 : ℝ)) (a := 0) u
    let t := AddCircle.equivIco (p := (1 : ℝ)) (a := 0) v
    have hφs : φ u = f (s : ℝ) := by
      dsimp [φ, s]
      rfl
    have hφt : φ v = f (t : ℝ) := by
      dsimp [φ, t]
      rfl
    have hEq : f (s : ℝ) = f (t : ℝ) := by
      calc
        f (s : ℝ) = φ u := hφs.symm
        _ = φ v := huv
        _ = f (t : ℝ) := hφt
    have hs_mem : (s : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simpa using s.2
    have ht_mem : (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simpa using t.2
    have hsv : (s : ℝ) = (t : ℝ) := by
      exact CircleData.arcCurve_eq_of_Ico e hz₀P hs_mem ht_mem (by simpa [f] using hEq)
    have hsEq : s = t := by
      apply Subtype.ext
      exact hsv
    apply (AddCircle.equivIco (p := (1 : ℝ)) (a := 0)).injective
    exact hsEq
  -- assemble the homeomorphism AddCircle 1 ≃ₜ X
  let H : AddCircle (1 : ℝ) ≃ₜ X := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφcont
  -- and Circle ≃ₜ AddCircle 1, so Circle ≃ₜ X
  exact ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) (by norm_num)).symm.trans H⟩

end Commons.Topology.OneManifold
