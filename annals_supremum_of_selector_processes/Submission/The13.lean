import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
import Submission.Multi
import Submission.MultiMass
import Submission.MultiAdd
import Submission.MultiW2
import Submission.MultiWtype
import Submission.Discret1
import Submission.Discret2
import Submission.MultiCost
import Submission.DiscretLvl
import Submission.DiscretLvl2
import Submission.The13Meas
import Submission.The13SupEval
import Submission.DiscretLvl3

/-!
# Theorem 1.3: final discretization assembly (skeleton; sub-lemmas have `sorry` to be filled).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace SupremumOfSelectorProcesses

/-- the constant of Theorem 1.3 (shared by Submission.lean's L₃) -/
noncomputable def L3v : ℝ≥0 := 2 * (10 : ℝ≥0) ^ 82

lemma L3v_pos : 0 < L3v := by
  unfold L3v
  positivity

/-- max' is independent of the nonemptiness proof -/
private lemma finset_max'_proof_irrel {α : Type*} [LinearOrder α] {s : Finset α}
    (h1 h2 : s.Nonempty) : s.max' h1 = s.max' h2 := by
  apply le_antisymm
  · exact Finset.max'_le s h1 (s.max' h2) (fun y hy => Finset.le_max' s y hy)
  · exact Finset.max'_le s h2 (s.max' h1) (fun y hy => Finset.le_max' s y hy)

/-- max' over equal finsets with different nonemptiness proofs -/
private lemma max'_congr_image {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (h1 : s.Nonempty) (h2 : t.Nonempty) : s.max' h1 = t.max' h2 := by
  subst t
  exact finset_max'_proof_irrel h1 h2


/-- max of (a i / c) equals (max of a i)/c for 0 < c -/
private lemma maxR_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hI : (Finset.univ : Finset ι).Nonempty) (a : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    ((Finset.univ.image (fun i : ι => a i / c)).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩))
      = ((Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / c := by
  classical
  apply le_antisymm
  · refine Finset.max'_le (Finset.univ.image (fun i : ι => a i / c)) (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      (((Finset.univ.image a).max' (by
      rcases hI with ⟨i, hi⟩
      exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / c) ?_
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨i, hi, rfl⟩
    have hle : a i ≤ (Finset.univ.image a).max' (by
        rcases hI with ⟨i0, hi0⟩
        exact ⟨a i0, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩) :=
      Finset.le_max' (Finset.univ.image a) (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    exact div_le_div_of_nonneg_right hle (le_of_lt hc)
  · have hmain : (Finset.univ.image a).max' (by
        rcases hI with ⟨i, hi⟩
        exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) ≤
        c * ((Finset.univ.image (fun i : ι => a i / c)).max' (by
          rcases hI with ⟨i, hi⟩
          exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) := by
      refine Finset.max'_le (Finset.univ.image a) (by
        rcases hI with ⟨i, hi⟩
        exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        (c * ((Finset.univ.image (fun i : ι => a i / c)).max' (by
          rcases hI with ⟨i, hi⟩
          exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩))) ?_
      intro y hy
      rcases (Finset.mem_image.mp hy) with ⟨i, hi, rfl⟩
      have hle : a i / c ≤ (Finset.univ.image (fun i0 : ι => a i0 / c)).max' (by
          rcases hI with ⟨i0, hi0⟩
          exact ⟨a i0 / c, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩) :=
        Finset.le_max' (Finset.univ.image (fun i0 : ι => a i0 / c)) (a i / c)
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hm : a i ≤ c * (a i / c) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      have hstep : c * (a i / c) ≤ c * ((Finset.univ.image (fun i0 : ι => a i0 / c)).max' (by
          rcases hI with ⟨i0, hi0⟩
          exact ⟨a i0 / c, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩)) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hc)
      linarith
    have hdiv : (c * ((Finset.univ.image (fun i : ι => a i / c)).max' (by
        rcases hI with ⟨i, hi⟩
        exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩))) / c
        = (Finset.univ.image (fun i : ι => a i / c)).max' (by
          rcases hI with ⟨i, hi⟩
          exact ⟨a i / c, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
        field_simp [ne_of_gt hc]
    rw [← hdiv]
    exact div_le_div_of_nonneg_right hmain (le_of_lt hc)

/-- every subset of a finite type with measurable singletons is measurable -/
private lemma finite_measurableSet_all {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (s : Set α) : MeasurableSet s := by
  classical
  have hs : s.Finite := Set.toFinite s
  rw [← Set.biUnion_of_singleton s]
  refine MeasurableSet.biUnion (s := s) hs.countable ?_
  intro x hx
  exact measurableSet_singleton x

/-- functions from a finite type with measurable singletons are measurable -/
private lemma measurable_of_finite_domain {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {C : Type*} [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] (f : C → β) : Measurable f := by
  intro s hs
  exact finite_measurableSet_all (f ⁻¹' s)

/-- the sup over an empty family of NNReal-valued functions is the zero function -/
private lemma empty_sup_fun {ι Ω : Type*} (a : ι → Ω → ℝ≥0) :
    (⨆ f ∈ (∅ : Set ι), a f) = (fun _ : Ω => (0 : ℝ≥0)) := by
  classical
  funext x
  have hpeel : ((⨆ f : ι, (⨆ (_ : f ∈ (∅ : Set ι)), a f)) x)
      = ⨆ f : ι, (⨆ (_ : f ∈ (∅ : Set ι)), a f x) := by
    rw [iSup_apply]
    congr
    funext f
    exact (iSup_apply (f := (fun _ : f ∈ (∅ : Set ι) => a f)) (a := x))
  rw [hpeel]
  apply le_antisymm
  · exact ciSup_le' (fun f => by
      exact ciSup_le' (fun hf => False.elim ((Set.mem_empty_iff_false f).mp hf)))
  · exact bot_le

/-- big structural lemma: the cover events exist and satisfy coverage + probability bound.
This lemma is the entire discretization; it takes the same hypotheses as theorem_1_3. -/
theorem discretization_main (N : ℕ) (N_pos : N > 0) (𝕋 : Type*) (t𝕋 : TopologicalSpace 𝕋)
    (p𝕋 : PolishSpace 𝕋) (m𝕋 : MeasurableSpace 𝕋) (b𝕋 : BorelSpace 𝕋) (ν : Measure 𝕋)
    (hν : IsProbabilityMeasure ν) (Ω : Type*) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
    (Y : Fin N → Ω → 𝕋) (Y_indep : iIndepFun Y P) (Y_law_ν : ∀ i, HasLaw (Y i) ν P)
    (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}) (h𝓕 : Finite 𝓕)
    (hZ₀ : 0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]) (hZ : 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞) :
    ∃ 𝓒 : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}),
      {ω | ⨆ f ∈ 𝓕, Z N Y f ω ≥ L3v * 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]} ⊆ ⋃ c ∈ 𝓒, {ω | c.2 ≤ Z N Y c.1 ω}
      ∧ ∑ c : 𝓒, P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ 2⁻¹ := by
  classical
  -- 1. E := (lintegral).toReal > 0
  let muinf : ℝ≥0∞ := 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]
  have hmuinf_fin : muinf ≠ ∞ := by
    exact ne_of_lt hZ
  have hZ₀' : 0 < muinf := by
    simpa [muinf] using hZ₀
  have hmuinf_nz : muinf ≠ 0 := ne_of_gt hZ₀' 
  let E : ℝ := muinf.toReal
  have hEpos : 0 < E := by
    unfold E
    exact ENNReal.toReal_pos hmuinf_nz hmuinf_fin
  -- 2. finite index type I := ↥𝓕, functions and Z-values
  haveI : Finite ↥𝓕 := h𝓕
  letI : Fintype ↥𝓕 := Fintype.ofFinite ↥𝓕
  let fF : ↥𝓕 → 𝕋 → ℝ≥0 := fun i => (i.1 : 𝕋 → ℝ≥0)
  let valZ : ↥𝓕 → Ω → ℝ≥0 := fun i => Z N Y (fF i)
  -- 3. sup over 𝓕 equals the sup over the index type (as ∞-valued functions of ω)
  have hsup_inf : ∀ ω : Ω, (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) = (⨆ i : ↥𝓕, ((valZ i ω : ℝ≥0) : ℝ≥0∞)) := by
    intro ω
    rw [iSup_subtype']
  -- A. P is a probability measure
  haveI hPprob : IsProbabilityMeasure P := by
    exact (Y_indep.iIndep).isProbabilityMeasure
  -- A0. the index type is nonempty
  have hIne : (Finset.univ : Finset ↥𝓕).Nonempty := by
    by_contra hne
    have huniv : (Finset.univ : Finset ↥𝓕) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hsub_empty (i : ↥𝓕) : False := by
      have : i ∈ (Finset.univ : Finset ↥𝓕) := Finset.mem_univ i
      simpa [huniv] using this
    have hz (ω : Ω) : (⨆ i : ↥𝓕, ((valZ i ω : ℝ≥0) : ℝ≥0∞)) = 0 := by
      apply le_antisymm
      · exact iSup_le (fun i => False.elim (hsub_empty i))
      · exact bot_le
    have hFempty : 𝓕 = ∅ := by
      ext f
      constructor
      · intro hf
        exact False.elim (hsub_empty ⟨f, hf⟩)
      · intro hf
        simp at hf
    have hf0 : (⨆ f ∈ 𝓕, fun x : Ω => Z N Y (↑f) x) = (fun _ : Ω => (0 : ℝ≥0)) := by
      rw [hFempty]
      exact empty_sup_fun (a := fun f : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} =>
        fun x : Ω => Z N Y (↑f) x)
    have hmu0 : muinf = 0 := by
      unfold muinf
      rw [hf0]
      simp
    exact hmuinf_nz hmu0

  -- D. measurable modification Y' of the sample functions (measurable, iid, a.e. equal to Y)
  let Y' : Fin N → Ω → 𝕋 := fun i => AEMeasurable.mk (Y i) (Y_law_ν i).aemeasurable
  have hY'meas (i : Fin N) : Measurable (Y' i) := (Y_law_ν i).aemeasurable.measurable_mk
  have hY'ae (i : Fin N) : Y i =ᵐ[P] Y' i := (Y_law_ν i).aemeasurable.ae_eq_mk
  have hY'law (i : Fin N) : HasLaw (Y' i) ν P := by
    have hc := HasLaw.congr (X := Y i) (μ := ν) (P := P) (Y_law_ν i) (hY'ae i).symm
    simpa [Y'] using hc
  have hY'indep : iIndepFun Y' P := by
    classical
    unfold iIndepFun at Y_indep ⊢
    exact Kernel.iIndepFun.congr' Y_indep (fun i => by
      apply Filter.Eventually.of_forall
      intro a
      simpa using (hY'ae i))
  -- a.e.-equality of the sup-process between Y and Y' (each f measurable)
  have hsup_inf' : ∀ ω : Ω, (⨆ f ∈ 𝓕, (Z N Y' f ω : ℝ≥0∞)) = (⨆ i : ↥𝓕, ((Z N Y' (fF i) ω : ℝ≥0) : ℝ≥0∞)) := by
    intro ω
    rw [iSup_subtype']
  have hZ_ae : (fun ω : Ω => (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞))) =ᵐ[P]
      fun ω : Ω => (⨆ f ∈ 𝓕, (Z N Y' f ω : ℝ≥0∞)) := by
    classical
    have hdiff (i : Fin N) : P {ω : Ω | Y' i ω ≠ Y i ω} = 0 := by
      have hae : ∀ᵐ (ω : Ω) ∂P, Y' i ω = Y i ω := (hY'ae i).symm
      rw [MeasureTheory.ae_iff] at hae
      simpa [Ne] using hae
    have hbad : P {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} = 0 := by
      have hsub : {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} ⊆
          ⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω} := by
        intro ω hω
        rcases hω with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hle : P (⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω}) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω} := by
        simpa using (measure_biUnion_finset_le (Finset.univ : Finset (Fin N))
          (fun i : Fin N => {ω : Ω | Y' i ω ≠ Y i ω}))
      have hsum0 : (∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω}) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hdiff i
      apply le_antisymm
      · calc
          P {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} ≤ P (⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω}) := measure_mono hsub
          _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω} := hle
          _ = 0 := hsum0
      · exact bot_le
    have hall : ∀ᵐ (ω : Ω) ∂P, ∀ i : Fin N, Y' i ω = Y i ω := by
      rw [MeasureTheory.ae_iff]
      simpa [Ne] using hbad
    filter_upwards [hall] with ω hω
    -- per-index equality of Z values
    have hz (i : ↥𝓕) : Z N Y (fF i) ω = Z N Y' (fF i) ω := by
      unfold Z
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun t : 𝕋 => fF i t) (hω j).symm
    rw [hsup_inf ω, hsup_inf' ω]
    congr
    funext i
    exact congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) (hz i)
  -- B. real max of the Z-values over the index type
  let zm : Ω → ℝ≥0 := fun ω =>
    (Finset.univ.image (fun i : ↥𝓕 => valZ i ω)).max' (by
      rcases hIne with ⟨i, hi⟩
      exact ⟨valZ i ω, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  -- identity: the ∞-sup equals the coe of the real max
  have hzm_sup (ω : Ω) : (⨆ i : ↥𝓕, ((valZ i ω : ℝ≥0) : ℝ≥0∞)) = (zm ω : ℝ≥0∞) := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      exact ENNReal.coe_le_coe.mpr (Finset.le_max' (Finset.univ.image (fun i : ↥𝓕 => valZ i ω))
        (valZ i ω) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    · have hm := Finset.max'_mem (Finset.univ.image (fun i : ↥𝓕 => valZ i ω)) (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨valZ i ω, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      rcases (Finset.mem_image.mp hm) with ⟨i0, hi0, hEq⟩
      have hEq2 : zm ω = valZ i0 ω := by
        unfold zm
        rw [finset_max'_proof_irrel]
        exact hEq.symm
      rw [hEq2]
      exact le_iSup (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ≥0∞)) i0
  -- Z-values of the Y'-process are genuinely measurable
  have hZmeas' (i : ↥𝓕) : Measurable (fun ω : Ω => (Z N Y' (fF i) ω : ℝ≥0)) := by
    have hsum (j : Fin N) : Measurable (fun ω : Ω => (fF i (Y' j ω) : ℝ≥0)) := by
      change Measurable (fun ω : Ω => ((i.1 : 𝕋 → ℝ≥0) (Y' j ω) : ℝ≥0))
      exact (i.1.2.1).comp (hY'meas j)
    have htot : Measurable (fun ω : Ω => (∑ j : Fin N, (fF i (Y' j ω) : ℝ≥0))) := by
      simpa using (Finset.measurable_sum (Finset.univ : Finset (Fin N)) (fun j hj => hsum j))
    unfold Z
    simpa using (htot.const_mul ((N : ℝ≥0)⁻¹))
  -- the real-coe of the Z-value is measurable
  have hZmeasR' (i : ↥𝓕) : Measurable (fun ω : Ω => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ)) := by
    exact (NNReal.continuous_coe.measurable).comp (hZmeas' i)
  -- the real max of Y'-Z-values is measurable
  let zmY : Ω → ℝ≥0 := fun ω =>
    (Finset.univ.image (fun i : ↥𝓕 => Z N Y' (fF i) ω)).max' (by
      rcases hIne with ⟨i, hi⟩
      exact ⟨Z N Y' (fF i) ω, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  have hzmY_measR : Measurable (fun ω : Ω => (zmY ω : ℝ)) := by
    -- max of the real casts equals the cast of the NNReal-max (The13Meas.maxR_coe_ident)
    have hident : (fun ω : Ω => (zmY ω : ℝ)) = fun ω : Ω =>
        (Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ))).max' (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨((Z N Y' (fF i) ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      funext ω
      unfold zmY
      exact The13Meas.maxR_coe_ident hIne (fun i : ↥𝓕 => Z N Y' (fF i) ω)
    rw [hident]
    exact The13Meas.measurable_finset_maxR hIne (fun i : ↥𝓕 => fun ω : Ω => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ)) hZmeasR'
  -- sup over the Y'-process equals coe of zmY (pointwise)
  have hzmY_sup (ω : Ω) : (⨆ i : ↥𝓕, ((Z N Y' (fF i) ω : ℝ≥0) : ℝ≥0∞)) = (zmY ω : ℝ≥0∞) := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      exact ENNReal.coe_le_coe.mpr (Finset.le_max' (Finset.univ.image (fun i : ↥𝓕 => Z N Y' (fF i) ω))
        (Z N Y' (fF i) ω) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    · have hm := Finset.max'_mem (Finset.univ.image (fun i : ↥𝓕 => Z N Y' (fF i) ω)) (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨Z N Y' (fF i) ω, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      rcases (Finset.mem_image.mp hm) with ⟨i0, hi0, hEq⟩
      have hEq2 : zmY ω = Z N Y' (fF i0) ω := by
        unfold zmY
        rw [finset_max'_proof_irrel]
        exact hEq.symm
      rw [hEq2]
      exact le_iSup (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ≥0∞)) i0
  -- a.e. equality of zm and zmY (real casts)
  have hYeq_all : ∀ᵐ (ω : Ω) ∂P, ∀ i : Fin N, Y' i ω = Y i ω := by
    classical
    have hdiff (i : Fin N) : P {ω : Ω | Y' i ω ≠ Y i ω} = 0 := by
      have hae : ∀ᵐ (ω : Ω) ∂P, Y' i ω = Y i ω := (hY'ae i).symm
      rw [MeasureTheory.ae_iff] at hae
      simpa [Ne] using hae
    have hbad : P {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} = 0 := by
      have hsub : {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} ⊆
          ⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω} := by
        intro ω hω
        rcases hω with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hle : P (⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω}) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω} := by
        simpa using (measure_biUnion_finset_le (Finset.univ : Finset (Fin N))
          (fun i : Fin N => {ω : Ω | Y' i ω ≠ Y i ω}))
      have hsum0 : (∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω}) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hdiff i
      apply le_antisymm
      · calc
          P {ω : Ω | ∃ i : Fin N, Y' i ω ≠ Y i ω} ≤ P (⋃ i : Fin N, {ω : Ω | Y' i ω ≠ Y i ω}) := measure_mono hsub
          _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' i ω ≠ Y i ω} := hle
          _ = 0 := hsum0
      · exact bot_le
    rw [MeasureTheory.ae_iff]
    simpa [Ne] using hbad
  have hZm_eq : (fun ω : Ω => (zm ω : ℝ)) =ᵐ[P] fun ω : Ω => (zmY ω : ℝ) := by
    filter_upwards [hYeq_all] with ω hω
    have hz (i : ↥𝓕) : Z N Y (fF i) ω = Z N Y' (fF i) ω := by
      unfold Z
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun t : 𝕋 => fF i t) (hω j).symm
    have him : (Finset.univ.image (fun i : ↥𝓕 => valZ i ω)) =
        (Finset.univ.image (fun i : ↥𝓕 => Z N Y' (fF i) ω)) := by
      congr 1
      funext i
      exact hz i
    unfold zm zmY
    congr 1
    exact max'_congr_image him _ _
  -- the real sup function is a.e.-strongly measurable
  have hZm_ae : AEStronglyMeasurable (fun ω : Ω => (zm ω : ℝ)) P := by
    exact (hzmY_measR.aestronglyMeasurable).congr hZm_eq.symm
  -- C. real integral of the sup equals E
  have hzm_int_eq : (∫ (ω : Ω), (zm ω : ℝ) ∂P) = E := by
    -- 1. real integral of zmY equals toReal of the lintegral of coe(zmY)
    have hIntY : (∫ (ω : Ω), (zmY ω : ℝ) ∂P) =
        (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P).toReal := by
      have hnn : 0 ≤ᵐ[P] (fun ω : Ω => (zmY ω : ℝ)) := by
        exact Filter.Eventually.of_forall (fun ω => NNReal.coe_nonneg (zmY ω))
      have hInt := integral_eq_lintegral_of_nonneg_ae (μ := P)
        (f := (fun ω : Ω => (zmY ω : ℝ))) hnn hzmY_measR.aestronglyMeasurable
      rw [hInt]
      congr 1
      apply lintegral_congr
      intro ω
      -- ofReal ((zmY ω : ℝ)) = (zmY ω : ℝ≥0∞)
      rw [ENNReal.ofReal_coe_nnreal]
    -- 2. ∫⁻ coe(zmY) = muinf
    have hLint : (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P) = muinf := by
      calc
        (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P)
            = ∫⁻ (ω : Ω), (⨆ i : ↥𝓕, ((Z N Y' (fF i) ω : ℝ≥0) : ℝ≥0∞)) ∂P := by
                apply lintegral_congr
                intro ω
                rw [← hzmY_sup ω]
        _ = ∫⁻ (ω : Ω), (⨆ f ∈ 𝓕, (Z N Y' f ω : ℝ≥0∞)) ∂P := by
                apply lintegral_congr
                intro ω
                rw [← hsup_inf' ω]
        _ = ∫⁻ (ω : Ω), (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) ∂P := by
                exact lintegral_congr_ae hZ_ae.symm
        _ = muinf := by
                apply lintegral_congr
                intro ω
                symm
                -- muinf integrand at ω = coe((⨆ f∈𝓕, fun x => Z N Y (↑f) x) ω)
                calc
                  ((⨆ f ∈ 𝓕, fun x : Ω => Z N Y (↑f) x) ω : ℝ≥0∞)
                      = ⨆ i : {f : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} // f ∈ 𝓕},
                          ((Z N Y (↑i.1) ω : ℝ≥0) : ℝ≥0∞) := by
                          exact The13SupEval.eval_sup_coe (𝓕 := 𝓕) h𝓕
                            (Z := fun f : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} =>
                              fun x : Ω => Z N Y (↑f) x) ω
                  _ = ⨆ i : ↥𝓕, ((valZ i ω : ℝ≥0) : ℝ≥0∞) := by
                          congr 1
                  _ = ⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞) := by
                          rw [hsup_inf ω]
    -- 3. combine
    calc
      (∫ (ω : Ω), (zm ω : ℝ) ∂P) = ∫ (ω : Ω), (zmY ω : ℝ) ∂P := by
          exact integral_congr_ae hZm_eq
      _ = (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P).toReal := hIntY
      _ = muinf.toReal := by rw [hLint]
      _ = E := rfl
  have hLint2 : (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P) = muinf := by
    calc
      (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P)
          = ∫⁻ (ω : Ω), (⨆ i : ↥𝓕, ((Z N Y' (fF i) ω : ℝ≥0) : ℝ≥0∞)) ∂P := by
              apply lintegral_congr
              intro ω
              rw [← hzmY_sup ω]
      _ = ∫⁻ (ω : Ω), (⨆ f ∈ 𝓕, (Z N Y' f ω : ℝ≥0∞)) ∂P := by
              apply lintegral_congr
              intro ω
              rw [← hsup_inf' ω]
      _ = ∫⁻ (ω : Ω), (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) ∂P := by
              exact lintegral_congr_ae hZ_ae.symm
      _ = muinf := by
              apply lintegral_congr
              intro ω
              symm
              calc
                ((⨆ f ∈ 𝓕, fun x : Ω => Z N Y (↑f) x) ω : ℝ≥0∞)
                    = ⨆ i : {f : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} // f ∈ 𝓕},
                        ((Z N Y (↑i.1) ω : ℝ≥0) : ℝ≥0∞) := by
                        exact The13SupEval.eval_sup_coe (𝓕 := 𝓕) h𝓕
                          (Z := fun f : {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν} =>
                            fun x : Ω => Z N Y (↑f) x) ω
                _ = ⨆ i : ↥𝓕, ((valZ i ω : ℝ≥0) : ℝ≥0∞) := by
                        congr 1
                _ = ⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞) := by
                        rw [hsup_inf ω]
  -- E0. grid constants
  let eta : ℝ := (1 : ℝ) / (10 : ℝ) ^ 60
  have heta : 0 < eta := by norm_num [eta]
  have heta0 : 0 ≤ eta := le_of_lt heta
  -- E1. a.e. bounds of the normalized functions (from MemLp f ∞ ν)
  let fn : ↥𝓕 → 𝕋 → ℝ := fun i y => ((fF i y : ℝ≥0) : ℝ) / E
  have hbound_i (i : ↥𝓕) : ∃ B : ℝ, ∀ᵐ y ∂ν, fn i y ≤ B := by
    classical
    let f0 : 𝕋 → ℝ≥0 := fF i
    have hmem : MemLp f0 ∞ ν := by
      simpa [f0, fF] using (i.1.2.2)
    have hnorm : eLpNorm f0 ∞ ν < ∞ := hmem.eLpNorm_lt_top
    have h1 : MeasureTheory.eLpNormEssSup f0 ν < ∞ := by
      simpa [eLpNorm] using hnorm
    have h2 : essSup (fun y : 𝕋 => ‖f0 y‖ₑ) ν < ∞ := by
      simpa [MeasureTheory.eLpNormEssSup_eq_essSup_enorm] using h1
    let u : 𝕋 → ℝ≥0∞ := fun y => ‖f0 y‖ₑ
    have hfin : essSup u ν < ∞ := by simpa [u] using h2
    let b : ℝ≥0∞ := essSup u ν + 1
    have hb : essSup u ν < b := by
      unfold b
      exact ENNReal.lt_add_right (ne_of_lt hfin) (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    have hev : ∀ᵐ y ∂ν, u y < b := by
      exact Filter.eventually_lt_of_limsup_lt hb
    have hbfin : b ≠ ∞ := by
      unfold b
      exact ENNReal.add_ne_top.mpr ⟨ne_of_lt hfin, ENNReal.coe_ne_top⟩
    refine ⟨b.toReal / E, ?_⟩
    filter_upwards [hev] with y hy
    have hle : u y ≤ b := le_of_lt hy
    have hval : ‖f0 y‖ₑ = (f0 y : ℝ≥0∞) := by rfl
    have hu : (f0 y : ℝ≥0∞) ≤ b := by
      simpa [u, hval] using hle
    have hto := (ENNReal.toReal_le_toReal (by exact ENNReal.coe_ne_top : (f0 y : ℝ≥0∞) ≠ ∞) hbfin).mpr hu
    have hcast : (f0 y : ℝ) ≤ b.toReal := by simpa using hto
    unfold fn
    simp [f0]
    exact div_le_div_of_nonneg_right hcast (le_of_lt hEpos)
  let bnd : ↥𝓕 → ℝ := fun i => Classical.choose (hbound_i i)
  have hbnd_i (i : ↥𝓕) : ∀ᵐ y ∂ν, fn i y ≤ bnd i := by
    exact Classical.choose_spec (hbound_i i)
  -- a single common bound U (over the finite index type)
  let Ub : ℝ := (Finset.univ.image bnd).max' (by
    rcases hIne with ⟨i, hi⟩
    exact ⟨bnd i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  have hU : (∀ᵐ y ∂ν, ∀ i : ↥𝓕, fn i y ≤ Ub) := by
    have hall_i : ∀ᵐ y ∂ν, ∀ i ∈ (Finset.univ : Finset ↥𝓕), fn i y ≤ bnd i := by
      refine (ae_ball_iff (Finset.countable_toSet (Finset.univ : Finset ↥𝓕))).2 ?_
      intro i hi
      exact hbnd_i i
    filter_upwards [hall_i] with y hy
    intro i
    have hb : fn i y ≤ bnd i := hy i (Finset.mem_univ i)
    have hle : bnd i ≤ Ub := Finset.le_max' (Finset.univ.image bnd) (bnd i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    linarith
  -- E3. number of levels L and the cell type
  have hLx : ∃ L : ℕ, (L : ℝ) * eta > Ub := by
    rcases exists_nat_gt (Ub / eta) with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hdiv : (Ub / eta) * eta = Ub := by
      field_simp [ne_of_gt heta]
    have hlt : Ub / eta < (L : ℝ) := hL
    have hmul : (Ub / eta) * eta < (L : ℝ) * eta := mul_lt_mul_of_pos_right hlt heta
    rw [hdiv] at hmul
    exact hmul
  let Ln : ℕ := Classical.choose hLx
  have hLtop : (Ln : ℝ) * eta > Ub := Classical.choose_spec hLx
  have hLtop' : ((Ln + 1 : ℕ) : ℝ) * eta > Ub := by
    have hcast : (((Ln + 1 : ℕ) : ℝ)) = (Ln : ℝ) + 1 := by
      rw [Nat.cast_add]
      norm_num
    have hc : (((Ln + 1 : ℕ) : ℝ)) * eta = (Ln : ℝ) * eta + eta := by
      rw [hcast]
      ring
    have hbig : (Ln : ℝ) * eta + eta > Ub := by nlinarith
    rwa [hc]
  -- cells
  let C := ↥𝓕 → Fin (Ln + 1)
  haveI hCfin : Fintype C := by
    dsimp [C]
    infer_instance
  haveI hCde : DecidableEq C := by
    dsimp [C]
    infer_instance
  haveI hCsing : MeasurableSingletonClass C := by
    dsimp [C]
    infer_instance
  -- level of a value (in range 0..Ln) and the map π
  let lv : ↥𝓕 → 𝕋 → ℕ := fun i y => DiscretLvl.lvl eta Ln (fn i y)
  have lv_le (i : ↥𝓕) (y : 𝕋) : lv i y ≤ Ln := DiscretLvl.lvl_le heta Ln (fn i y)
  let pi : 𝕋 → C := fun y i => (⟨lv i y, Nat.lt_succ_of_le (lv_le i y)⟩ : Fin (Ln + 1))
  -- cell weights
  let lamC : ↥𝓕 → C → ℝ := fun i c => ((c i : Fin (Ln + 1)).val : ℝ) * eta
  -- the escape (bad) region: samples whose normalized value overflows the grid
  let ESC : Set 𝕋 := {y | ∃ i : ↥𝓕, ((Ln + 1 : ℕ) : ℝ) * eta ≤ fn i y}
  -- the cell of a level-k value: (pi y i).val = lv i y
  have hpi (y : 𝕋) (i : ↥𝓕) : (pi y i).val = lv i y := rfl
  -- per-coordinate pointwise error bound
  have hpi_val (y : 𝕋) (i : ↥𝓕) : (pi y i : Fin (Ln + 1)).val = lv i y := rfl
  have herr (y : 𝕋) (hy : y ∉ ESC) (i : ↥𝓕) :
      |fn i y - lamC i (pi y)| ≤ eta := by
    have hnot : fn i y < ((Ln + 1 : ℕ) : ℝ) * eta := by
      have : ¬ (((Ln + 1 : ℕ) : ℝ) * eta ≤ fn i y) := by
        intro hle
        exact hy ⟨i, hle⟩
      linarith
    have hge : 0 ≤ fn i y := by
      dsimp [fn]
      exact div_nonneg (NNReal.coe_nonneg _) (le_of_lt hEpos)
    have herr0 := DiscretLvl.lvl_error (ε := eta) heta Ln (fn i y) hge hnot
    have hval : lamC i (pi y) = (lv i y : ℝ) * eta := by
      dsimp [lamC, pi, lv]
    rw [hval]
    simpa [lv] using herr0
  -- ESC is ν-null
  have hESCnull : ν ESC = 0 := by
    have hU' : ν {y : 𝕋 | ¬ ∀ i : ↥𝓕, fn i y ≤ Ub} = 0 := by
      have hUae : ∀ᵐ y ∂ν, ∀ i : ↥𝓕, fn i y ≤ Ub := hU
      rw [MeasureTheory.ae_iff] at hUae
      simpa using hUae
    have hsub : ESC ⊆ {y : 𝕋 | ¬ ∀ i : ↥𝓕, fn i y ≤ Ub} := by
      intro y hy hcontra
      rcases hy with ⟨i, htop⟩
      have hfn : fn i y ≤ Ub := hcontra i
      have : fn i y < ((Ln + 1 : ℕ) : ℝ) * eta := by
        have hUbig : Ub < ((Ln + 1 : ℕ) : ℝ) * eta := hLtop'
        linarith
      linarith
    apply le_antisymm
    · calc
        ν ESC ≤ ν {y : 𝕋 | ¬ ∀ i : ↥𝓕, fn i y ≤ Ub} := measure_mono hsub
        _ = 0 := hU'
    · exact bot_le
  -- pi is measurable (coordinate-wise levels of measurable functions)
  have hpi_meas : Measurable pi := by
    classical
    have hcoord (i : ↥𝓕) : Measurable (fun y : 𝕋 => (pi y i : Fin (Ln + 1))) := by
      change Measurable (fun y : 𝕋 => (⟨lv i y, Nat.lt_succ_of_le (lv_le i y)⟩ : Fin (Ln + 1)))
      have hfnm : Measurable (fn i) := by
        dsimp [fn]
        exact ((NNReal.continuous_coe.measurable.comp (i.1.2.1)).div_const E)
      have hge (x : 𝕋) : 0 ≤ fn i x := by
        dsimp [fn]
        exact div_nonneg (NNReal.coe_nonneg _) (le_of_lt hEpos)
      exact DiscretLvl3.measurable_level_fin eta heta Ln (fn i) hfnm hge
    exact measurable_pi_lambda (fun y : 𝕋 => fun i : ↥𝓕 => pi y i) hcoord
  -- ESC is measurable
  have hESCmeas : MeasurableSet ESC := by
    dsimp [ESC]
    change MeasurableSet {y : 𝕋 | ∃ i : ↥𝓕, ((Ln + 1 : ℕ) : ℝ) * eta ≤ fn i y}
    have hEq : {y : 𝕋 | ∃ i : ↥𝓕, ((Ln + 1 : ℕ) : ℝ) * eta ≤ fn i y}
        = ⋃ i ∈ (Set.univ : Set ↥𝓕), {y : 𝕋 | ((Ln + 1 : ℕ) : ℝ) * eta ≤ fn i y} := by
      ext y
      simp
    rw [hEq]
    refine MeasurableSet.biUnion (s := (Set.univ : Set ↥𝓕)) Set.countable_univ ?_
    intro i hi
    have hfnm : Measurable (fn i) := by
      dsimp [fn]
      exact ((NNReal.continuous_coe.measurable.comp (i.1.2.1)).div_const E)
    exact measurableSet_le (f := fun _ : 𝕋 => ((Ln + 1 : ℕ) : ℝ) * eta) (g := fn i) measurable_const hfnm
  -- cell-valued samples
  let Xs : Fin N → Ω → C := fun j ω => pi (Y' j ω)
  have hXsmeas (j : Fin N) : Measurable (Xs j) := hpi_meas.comp (hY'meas j)
  have hXsiid : iIndepFun Xs P := iIndepFun.comp hY'indep (fun _ : Fin N => pi) (fun j => hpi_meas)
  -- atom masses over the cells
  let muC : C → ℝ≥0 := fun c => ((ν.map pi) {c}).toNNReal
  have hmuCsum : (∑ c : C, (muC c : ℝ≥0∞)) = 1 := by
    classical
    have hfin (c : C) : (ν.map pi) {c} ≠ ∞ := by
      have hle : (ν.map pi) {c} ≤ (ν.map pi) Set.univ := measure_mono (by intro x hx; trivial)
      have huniv : (ν.map pi) Set.univ = 1 := by
        rw [Measure.map_apply hpi_meas MeasurableSet.univ]
        rw [Set.preimage_univ]
        exact hν.measure_univ
      rw [huniv] at hle
      exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
    have h1 : (∑ c : C, (muC c : ℝ≥0∞)) = ∑ c : C, ((ν.map pi) {c}) := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      dsimp [muC]
      exact (ENNReal.coe_toNNReal (hfin c))
    have hdisj : (((Finset.univ : Finset C) : Set C).PairwiseDisjoint (fun c : C => ({c} : Set C))) := by
      intro a ha b hb hne
      change Disjoint ({a} : Set C) ({b} : Set C)
      rw [Set.disjoint_singleton_left]
      rw [Set.mem_singleton_iff]
      exact hne
    have hmeas (c : C) : MeasurableSet ({c} : Set C) := measurableSet_singleton c
    calc
      (∑ c : C, (muC c : ℝ≥0∞)) = ∑ c : C, ((ν.map pi) {c}) := h1
      _ = (ν.map pi) (⋃ c ∈ (Finset.univ : Finset C), ({c} : Set C)) := by
        exact (measure_biUnion_finset hdisj (fun c hc => hmeas c)).symm
      _ = (ν.map pi) Set.univ := by
        congr 1
        ext x
        simp
      _ = 1 := by
        rw [Measure.map_apply hpi_meas MeasurableSet.univ]
        rw [Set.preimage_univ]
        exact hν.measure_univ
  have hmuCnonneg (c : C) : 0 ≤ (muC c : ℝ) := by exact NNReal.coe_nonneg _
  have hmuCsumR : (∑ c : C, (muC c : ℝ)) = 1 := by
    have hENN := hmuCsum
    have hsum_toReal : (∑ c : C, (muC c : ℝ≥0∞)).toReal = ∑ c : C, (muC c : ℝ) := by
      rw [ENNReal.toReal_sum]
      · simp
      · intro c hc
        exact ENNReal.coe_ne_top
    calc
      (∑ c : C, (muC c : ℝ)) = (∑ c : C, (muC c : ℝ≥0∞)).toReal := by rw [hsum_toReal]
      _ = (1 : ℝ≥0∞).toReal := by rw [hENN]
      _ = 1 := by simp
  -- law of the cell-valued samples
  have hXsLaw (j : Fin N) (c : C) : P {ω | Xs j ω = c} = (muC c : ℝ≥0∞) := by
    have hmap : (P.map (Xs j)) = ν.map pi := by
      calc
        P.map (Xs j) = (P.map (Y' j)).map pi := by
          change P.map (pi ∘ Y' j) = (P.map (Y' j)).map pi
          rw [Measure.map_map hpi_meas (hY'meas j)]
        _ = ν.map pi := by rw [(hY'law j).map_eq]
    have hfin : (ν.map pi) {c} ≠ ∞ := by
      have hle : (ν.map pi) {c} ≤ (ν.map pi) Set.univ := measure_mono (by intro x hx; trivial)
      have huniv : (ν.map pi) Set.univ = 1 := by
        rw [Measure.map_apply hpi_meas MeasurableSet.univ]
        rw [Set.preimage_univ]
        exact hν.measure_univ
      rw [huniv] at hle
      exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
    calc
      P {ω | Xs j ω = c} = (P.map (Xs j)) {c} := by
        rw [Measure.map_apply (hXsmeas j) (measurableSet_singleton c)]
        rfl
      _ = (ν.map pi) {c} := by rw [hmap]
      _ = (muC c : ℝ≥0∞) := by
        dsimp [muC]
        exact (ENNReal.coe_toNNReal (hfin)).symm
  -- the empirical count vector and its multinomial law
  let Wcnt : Ω → C → ℕ := fun ω c => Discret1.countVec (fun j : Fin N => Xs j ω) c
  have hWlawENN (m : C → ℕ) (hm : (∑ c : C, m c) = N) :
      P {ω | ∀ c : C, Wcnt ω c = m c}
        = ((Nat.factorial N : ℝ≥0∞) * ∏ c : C, (muC c : ℝ≥0∞) ^ m c *
            (Nat.factorial (m c) : ℝ≥0∞)⁻¹) := by
    exact Discret1.prob_countVec (Ω := Ω) P (X := Xs) (μ := muC) (m := m) hXsiid hXsmeas hXsLaw hm
  have hWlawReal (m : C → ℕ) (hm : (∑ c : C, m c) = N) :
      (P {ω | ∀ c : C, Wcnt ω c = m c}).toReal = Multi.mass N (fun c : C => (muC c : ℝ)) m := by
    simpa [Wcnt] using (Discret2.mass_eq_prob_toReal (Ω := Ω) P (X := Xs) (μ := muC) (m := m) hXsiid hXsmeas hXsLaw hm)
  -- normalized sample sup (over the Y'-process), and its cell version
  let supS : Ω → ℝ := fun ω => (zmY ω : ℝ) / E
  let supCell : Ω → ℝ := fun ω =>
    (Finset.univ.image (fun i : ↥𝓕 =>
      (1 / (N : ℝ)) * (∑ c : C, (Wcnt ω c : ℝ) * lamC i c))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ c : C, (Wcnt ω c : ℝ) * lamC i c), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  -- E[supS] = 1
  have hEsupS : (∫ (ω : Ω), supS ω ∂P) = 1 := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hIntY : (∫ (ω : Ω), (zmY ω : ℝ) ∂P) = E := by
      calc
        (∫ (ω : Ω), (zmY ω : ℝ) ∂P) = ∫ (ω : Ω), (zm ω : ℝ) ∂P := by
          exact integral_congr_ae hZm_eq.symm
        _ = E := hzm_int_eq
    have hdiv : (∫ (ω : Ω), (zmY ω : ℝ) / E ∂P) = (∫ (ω : Ω), (zmY ω : ℝ) ∂P) / E := by
      have hpoint : (fun ω : Ω => (zmY ω : ℝ) / E) = fun ω : Ω => (zmY ω : ℝ) * (E⁻¹) := by
        funext ω
        field_simp [hEne]
      have hmul : (∫ (ω : Ω), (zmY ω : ℝ) * (E⁻¹) ∂P) = (∫ (ω : Ω), (zmY ω : ℝ) ∂P) * E⁻¹ :=
        MeasureTheory.integral_mul_const (f := fun ω : Ω => (zmY ω : ℝ)) E⁻¹
      rw [hpoint, hmul]
      field_simp [hEne]
    calc
      (∫ (ω : Ω), supS ω ∂P) = ∫ (ω : Ω), (zmY ω : ℝ) / E ∂P := rfl
      _ = (∫ (ω : Ω), (zmY ω : ℝ) ∂P) / E := hdiv
      _ = E / E := by rw [hIntY]
      _ = 1 := by
        field_simp [hEne]
  -- good set: no sample falls into the escape region
  let good : Set Ω := {ω | ∀ j : Fin N, Y' j ω ∉ ESC}
  have hgoodmeas : MeasurableSet good := by
    classical
    have hg (j : Fin N) : MeasurableSet {ω | Y' j ω ∉ ESC} := by
      exact (hY'meas j) (MeasurableSet.compl hESCmeas)
    -- good = ⋂ j, that
    have hEq : good = ⋂ j : Fin N, {ω : Ω | Y' j ω ∉ ESC} := by
      ext ω
      simp [good]
    rw [hEq]
    exact MeasurableSet.iInter (fun j : Fin N => hg j)
  have hgoodP : P good = 1 := by
    classical
    have hbad : P {ω : Ω | ∃ j : Fin N, Y' j ω ∈ ESC} = 0 := by
      have hle : P (⋃ j : Fin N, {ω : Ω | Y' j ω ∈ ESC}) ≤
          ∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' j ω ∈ ESC} := by
        simpa using (measure_biUnion_finset_le (Finset.univ : Finset (Fin N))
          (fun j : Fin N => {ω : Ω | Y' j ω ∈ ESC}))
      have hsum0 : (∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' j ω ∈ ESC}) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hlaw := (hY'law j).measure_eq (p := fun y : 𝕋 => y ∈ ESC) hESCmeas
        -- P{ω | Y'j ω ∈ ESC} = ν ESC
        have hval : P {ω : Ω | Y' j ω ∈ ESC} = ν ESC := by
          simpa using hlaw
        rw [hval, hESCnull]
      have hsub : {ω : Ω | ∃ j : Fin N, Y' j ω ∈ ESC} ⊆ ⋃ j : Fin N, {ω : Ω | Y' j ω ∈ ESC} := by
        intro ω hω
        rcases hω with ⟨j, hj⟩
        exact Set.mem_iUnion.mpr ⟨j, hj⟩
      apply le_antisymm
      · calc
          P {ω : Ω | ∃ j : Fin N, Y' j ω ∈ ESC} ≤ P (⋃ j : Fin N, {ω : Ω | Y' j ω ∈ ESC}) := measure_mono hsub
          _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω : Ω | Y' j ω ∈ ESC} := hle
          _ = 0 := hsum0
      · exact bot_le
    -- good^c = {∃ j ∈ ESC}
    have hcompl : {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)} = {ω : Ω | ∃ j : Fin N, Y' j ω ∈ ESC} := by
      ext ω
      simp [good]
    -- P good = 1: univ ⊆ good ∪ goodᶜ and P goodᶜ = 0
    have hle1 : (1 : ℝ≥0∞) ≤ P good := by
      have huniv : Set.univ ⊆ good ∪ {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)} := by
        intro ω hω
        by_cases hg : ∀ j : Fin N, Y' j ω ∉ ESC
        · exact Or.inl hg
        · exact Or.inr hg
      have hP : P Set.univ ≤ P (good ∪ {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)}) := measure_mono huniv
      have hPle : P (good ∪ {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)}) ≤ P good + P {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)} := by
        exact measure_union_le _ _
      calc
        (1 : ℝ≥0∞) = P Set.univ := hPprob.measure_univ.symm
        _ ≤ P (good ∪ {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)}) := hP
        _ ≤ P good + P {ω : Ω | ¬ (∀ j : Fin N, Y' j ω ∉ ESC)} := hPle
        _ = P good + 0 := by rw [hcompl, hbad]
        _ = P good := by simp
    have hle2 : P good ≤ 1 := by
      calc
        P good ≤ P Set.univ := measure_mono (by intro ω hω; trivial)
        _ = 1 := hPprob.measure_univ
    exact le_antisymm hle2 hle1
  -- per-sample level sum over samples in a cell: a reindexing identity
  have hsumreidx (i : ↥𝓕) (ω : Ω) :
      (∑ j : Fin N, lamC i (pi (Y' j ω))) = ∑ c : C, (Wcnt ω c : ℝ) * lamC i c := by
    have hre := Discret2.sum_coord (t := fun j : Fin N => Xs j ω) (f := fun c : C => lamC i c)
    dsimp [Wcnt, Xs] at hre ⊢
    exact hre
  -- supS as the pointwise real max over per-sample averages
  have hsupS_form (ω : Ω) : supS ω =
      (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
    classical
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    have hper (i : ↥𝓕) : (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω))
        = ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E := by
      have hsumdiv : (∑ j : Fin N, (fF i (Y' j ω) : ℝ) / E) = (∑ j : Fin N, (fF i (Y' j ω) : ℝ)) / E := by
        rw [← Finset.sum_div]
      have hZc : ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) = ((N : ℝ≥0)⁻¹ : ℝ≥0) * (∑ j : Fin N, (fF i (Y' j ω) : ℝ)) := by
        simp [Z, NNReal.coe_mul, NNReal.coe_sum]
      have hcast : (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = 1 / (N : ℝ) := by norm_num [one_div]
      dsimp [fn]
      calc
        (1 / (N : ℝ)) * (∑ j : Fin N, (fF i (Y' j ω) : ℝ) / E) = (1 / (N : ℝ)) * ((∑ j : Fin N, (fF i (Y' j ω) : ℝ)) / E) := by rw [hsumdiv]
        _ = ((1 / (N : ℝ)) * (∑ j : Fin N, (fF i (Y' j ω) : ℝ))) / E := by ring
        _ = (((N : ℝ≥0)⁻¹ : ℝ≥0) * (∑ j : Fin N, (fF i (Y' j ω) : ℝ))) / E := by rw [hcast]
        _ = ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E := by rw [hZc]
    have hmaxdiv : (Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E)).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        = ((Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨((Z N Y' (fF i) ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / E := by
      exact maxR_div hIne (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ)) E hEpos
    have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω))))
        = (Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E)) := by
      congr 1
      funext i
      exact hper i
    have hzm : (zmY ω : ℝ) = (Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨((Z N Y' (fF i) ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      dsimp [zmY]
      exact The13Meas.maxR_coe_ident hIne (fun i : ↥𝓕 => Z N Y' (fF i) ω)
    calc
      supS ω = (zmY ω : ℝ) / E := rfl
      _ = ((Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨((Z N Y' (fF i) ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / E := by
            rw [hzm]
      _ = (Finset.univ.image (fun i : ↥𝓕 => ((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E)).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨(((Z N Y' (fF i) ω : ℝ≥0) : ℝ) / E), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
            exact hmaxdiv.symm
      _ = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
            exact (max'_congr_image him _ _).symm
  have hptw (ω : Ω) (hω : ω ∈ good) : |supS ω - supCell ω| ≤ eta := by
    -- per-coordinate, per-sample bound
    have hps (i : ↥𝓕) (j : Fin N) : |fn i (Y' j ω) - lamC i (pi (Y' j ω))| ≤ eta := by
      exact herr (Y' j ω) (hω j) i
    have hpsum (i : ↥𝓕) : |(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)) -
          (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω)))| ≤ eta := by
      have hcast0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
      have hcast : (N : ℝ) ≠ 0 := ne_of_gt hcast0
      have hsum : |(∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω)))| ≤ (N : ℝ) * eta := by
        calc
          |(∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω)))|
              = |∑ j : Fin N, (fn i (Y' j ω) - lamC i (pi (Y' j ω)))| := by
                  congr 1
                  rw [← Finset.sum_sub_distrib]
          _ ≤ ∑ j : Fin N, |fn i (Y' j ω) - lamC i (pi (Y' j ω))| := by
                  exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin N, eta := by
                  apply Finset.sum_le_sum
                  intro j hj
                  exact hps i j
          _ = (N : ℝ) * eta := by simp
      have hpos : 0 ≤ (1 / (N : ℝ)) := by positivity
      have hmain : |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω))))| ≤ eta := by
        calc
          |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω))))|
              = (1 / (N : ℝ)) * |(∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω)))| := by
                  rw [abs_mul]
                  congr 1
                  rw [abs_of_nonneg hpos]
          _ ≤ (1 / (N : ℝ)) * ((N : ℝ) * eta) := mul_le_mul_of_nonneg_left hsum hpos
          _ = eta := by
                  field_simp [hcast]
      have hEq : |(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)) - (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω)))|
          = |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y' j ω)) - (∑ j : Fin N, lamC i (pi (Y' j ω))))| := by
          congr 1
          ring
      rwa [hEq]
    -- sup over i of both sides
    -- sup over i of both sides
    have hsplit : supS ω = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      exact hsupS_form ω
    have hsplit2 : supCell ω = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω))))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω))), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ c : C, (Wcnt ω c : ℝ) * lamC i c)))
          = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω))))) := by
        congr 1
        funext i
        congr 1
        exact (hsumreidx i ω).symm
      unfold supCell
      exact max'_congr_image him _ _
    rw [hsplit, hsplit2]
    exact DiscretLvl.sup_abs_sub_le eta (Finset.univ : Finset ↥𝓕)
      (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y' j ω)))
      (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y' j ω)))) hIne
      (fun i hi => hpsum i)
  have hsupS_mble : Measurable (fun ω : Ω => supS ω) := by
    dsimp [supS]
    exact hzmY_measR.div_const E
  have hsupS_nonneg : ∀ ω : Ω, 0 ≤ supS ω := by
    intro ω
    dsimp [supS]
    exact div_nonneg (NNReal.coe_nonneg (zmY ω)) (le_of_lt hEpos)
  have hZmY_int : Integrable (fun ω : Ω => (zmY ω : ℝ)) P := by
    rw [MeasureTheory.Integrable]
    constructor
    · exact hzmY_measR.aestronglyMeasurable
    · rw [HasFiniteIntegral]
      have hval : (∫⁻ (ω : Ω), ‖(zmY ω : ℝ)‖ₑ ∂P) ≤ (∫⁻ (ω : Ω), (zmY ω : ℝ≥0∞) ∂P) := by
        exact MeasureTheory.lintegral_mono (by
          intro ω
          have hc : 0 ≤ (zmY ω : ℝ) := NNReal.coe_nonneg (zmY ω)
          simp [Real.norm_eq_abs, abs_of_nonneg hc])
      apply lt_of_le_of_lt hval
      rw [hLint2]
      exact hZ
  have hsupS_int : Integrable (fun ω : Ω => supS ω) P := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hpoint : (fun ω : Ω => supS ω) = fun ω : Ω => (zmY ω : ℝ) * (E⁻¹) := by
      funext ω
      dsimp [supS]
      field_simp [hEne]
    rw [hpoint]
    exact hZmY_int.mul_const E⁻¹
  -- goodᶜ-measurable and its integral-vanish facts
  have hgoodc_meas : MeasurableSet (goodᶜ) := MeasurableSet.compl hgoodmeas
  have hgoodc_P : P (goodᶜ) = 0 := by
    have hfin : P good ≠ ∞ := by
      have hle : P good ≤ P Set.univ := measure_mono (by intro x hx; trivial)
      rw [hPprob.measure_univ] at hle
      exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
    have hc := MeasureTheory.measure_compl hgoodmeas hfin
    -- hc : P goodᶜ = P univ - P good
    rw [hc, hPprob.measure_univ, hgoodP]
    simp
  let massC : (C → ℕ) → ℝ := fun m => Multi.mass N (fun c : C => (muC c : ℝ)) m
  let supOf : (C → ℕ) → ℝ := fun m =>
    (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))).max' (by
      rcases hIne with ⟨i, hi⟩
      exact ⟨(∑ c : C, (m c : ℝ) * lamC i c), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  let EsupI : ℝ := (∑ m ∈ Multi.msizeExact (X := C) N, massC m * supOf m)
  have hEsupCell_form (ω : Ω) : supCell ω = (1 / (N : ℝ)) * supOf (Wcnt ω) := by
    classical
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    let s : ↥𝓕 → ℝ := fun i => ∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)
    have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * s i)) =
        (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))) := by
      congr 1
      funext i
      ring
    have hform : supCell ω =
        (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      unfold supCell
      refine max'_congr_image ?_ _ _
      · simpa [s] using him
    have hmax : (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        = ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ) := by
      simpa using (maxR_div hIne s (N : ℝ) hNposR)
    calc
      supCell ω = (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := hform
      _ = ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ) := hmax
      _ = (1 / (N : ℝ)) * supOf (Wcnt ω) := by
        calc
          ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ)
              = (1 / (N : ℝ)) * (Finset.univ.image s).max' (by
                  rcases hIne with ⟨i, hi⟩
                  exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
                  ring
          _ = (1 / (N : ℝ)) * supOf (Wcnt ω) := by
                  congr 1
  -- Wcnt has size N and its events are measurable
  have hWsize (ω : Ω) : (∑ c : C, Wcnt ω c) = N := by
    dsimp [Wcnt]
    exact Discret1.sum_countVec (fun j : Fin N => Xs j ω)
  have hWm_meas (m : C → ℕ) : MeasurableSet {ω : Ω | Wcnt ω = m} := by
    classical
    have htup : Measurable (fun ω : Ω => (fun j : Fin N => Xs j ω)) := by
      exact measurable_pi_lambda (fun ω : Ω => fun j : Fin N => Xs j ω) (fun j => hXsmeas j)
    have hTuplesMeas : MeasurableSet (↑(Discret1.Tuples N m) : Set (Fin N → C)) := by
      refine Finset.induction_on (Discret1.Tuples N m) ?_ ?_
      · simp
      · intro t s his ih
        have hcyl : MeasurableSet ({t} : Set (Fin N → C)) := by
          have hEq : ({t} : Set (Fin N → C)) = ⋂ j : Fin N, {g : Fin N → C | g j = t j} := by
            ext g
            simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
            exact (funext_iff (f := g) (g := t))
          rw [hEq]
          refine MeasurableSet.iInter (fun j : Fin N => ?_)
          have hproj : Measurable (fun g : Fin N → C => g j) := measurable_pi_apply j
          exact hproj (measurableSet_singleton (t j))
        rw [show (↑(insert t s) : Set (Fin N → C)) = ({t} : Set (Fin N → C)) ∪ ↑s by
          ext g
          simp]
        exact hcyl.union ih
    have hEq : {ω : Ω | Wcnt ω = m} = (fun ω : Ω => (fun j : Fin N => Xs j ω)) ⁻¹' (↑(Discret1.Tuples N m) : Set (Fin N → C)) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [funext_iff]
      dsimp [Wcnt]
      exact (Discret1.mem_Tuples (N := N) (m := m) (t := fun j : Fin N => Xs j ω)).symm
    rw [hEq]
    exact htup hTuplesMeas
  have hwlaw (m : C → ℕ) (hm : m ∈ Multi.msizeExact (X := C) N) :
      (P {ω : Ω | Wcnt ω = m}).toReal = massC m := by
    have hsize : (∑ c : C, m c) = N := (Multi.mem_msizeExact_iff (X := C) (M := N)).mp hm
    have hset : {ω : Ω | Wcnt ω = m} = {ω : Ω | ∀ c : C, Discret1.countVec (fun i : Fin N => Xs i ω) c = m c} := by
      ext ω
      simp [Wcnt]
      rw [funext_iff]
    rw [hset]
    simpa [massC] using (Discret2.mass_eq_prob_toReal (Ω := Ω) P (X := Xs) (μ := muC) (m := m) hXsiid hXsmeas hXsLaw hsize)
  have hind_int (m : C → ℕ) :
      (∫ (ω : Ω), (if Wcnt ω = m then (1 : ℝ) else 0) ∂P) = (P {ω : Ω | Wcnt ω = m}).toReal := by
    have hA : MeasurableSet {ω : Ω | Wcnt ω = m} := hWm_meas m
    have hfun : (fun ω : Ω => if Wcnt ω = m then (1 : ℝ) else 0) = ({ω : Ω | Wcnt ω = m}).indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      by_cases h : Wcnt ω = m <;> simp [h]
    rw [hfun]
    rw [MeasureTheory.integral_indicator hA]
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def]
    simp
  have hsumfun : (fun ω : Ω => supCell ω) = fun ω : Ω =>
      ∑ m ∈ Multi.msizeExact (X := C) N, (if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0) := by
    funext ω
    have hmem : Wcnt ω ∈ Multi.msizeExact (X := C) N := Multi.mem_msizeExact (hWsize ω)
    rw [Finset.sum_eq_single (Wcnt ω) (s := Multi.msizeExact (X := C) N) (f := fun m : C → ℕ => if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0)]
    · have hif : (if Wcnt ω = Wcnt ω then (1 / (N : ℝ)) * supOf (Wcnt ω) else 0) = (1 / (N : ℝ)) * supOf (Wcnt ω) := by simp
      rw [hif]
      exact hEsupCell_form ω
    · intro b hb hne
      have hnot : ¬ Wcnt ω = b := by
        intro h
        exact hne h.symm
      simp [hnot]
    · intro hnotmem
      exact False.elim (hnotmem hmem)
  have hEsupI_eq : EsupI = (N : ℝ) * (∫ (ω : Ω), supCell ω ∂P) := by
    have hterm_int (m : C → ℕ) (hm : m ∈ Multi.msizeExact (X := C) N) :
        (∫ (ω : Ω), (if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0) ∂P)
          = (1 / (N : ℝ)) * supOf m * (P {ω : Ω | Wcnt ω = m}).toReal := by
      have hfun : (fun ω : Ω => if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0)
          = fun ω : Ω => ((1 / (N : ℝ)) * supOf m) * (if Wcnt ω = m then (1 : ℝ) else 0) := by
        funext ω
        by_cases h : Wcnt ω = m <;> simp [h]
      rw [hfun]
      rw [MeasureTheory.integral_const_mul (r := ((1 / (N : ℝ)) * supOf m)) (f := fun ω : Ω => (if Wcnt ω = m then (1 : ℝ) else 0))]
      rw [hind_int m]
    have hinteg : (∫ (ω : Ω), supCell ω ∂P)
        = ∑ m ∈ Multi.msizeExact (X := C) N, (1 / (N : ℝ)) * supOf m * (P {ω : Ω | Wcnt ω = m}).toReal := by
      rw [hsumfun]
      rw [MeasureTheory.integral_finset_sum (s := Multi.msizeExact (X := C) N) (f := fun m : C → ℕ => fun ω : Ω => (if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0))]
      · apply Finset.sum_congr rfl
        intro m hm
        exact hterm_int m hm
      · intro m hm
        -- integrable: constant × indicator of the measurable event
        have hc : Integrable (fun _ : Ω => ((1 / (N : ℝ)) * supOf m)) P := by
          exact MeasureTheory.integrable_const (μ := P) (c := ((1 / (N : ℝ)) * supOf m))
        have hterm := hc.indicator (hWm_meas m)
        have hfun : (fun ω : Ω => (if Wcnt ω = m then ((1 / (N : ℝ)) * supOf m) else 0))
            = ({ω : Ω | Wcnt ω = m}).indicator (fun _ : Ω => ((1 / (N : ℝ)) * supOf m)) := by
          funext ω
          by_cases h : Wcnt ω = m <;> simp [h]
        rw [hfun]
        exact hterm
    calc
      EsupI = ∑ m ∈ Multi.msizeExact (X := C) N, massC m * supOf m := by
        rfl
      _ = (N : ℝ) * (∑ m ∈ Multi.msizeExact (X := C) N,
            (1 / (N : ℝ)) * supOf m * (P {ω : Ω | Wcnt ω = m}).toReal) := by
        have hcastN : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N_pos)
        calc
          (∑ m ∈ Multi.msizeExact (X := C) N, massC m * supOf m)
              = (N : ℝ) * (∑ m ∈ Multi.msizeExact (X := C) N, (1 / (N : ℝ)) * supOf m * massC m) := by
                  rw [mul_comm (N : ℝ) (∑ m ∈ Multi.msizeExact (X := C) N, (1 / (N : ℝ)) * supOf m * massC m)]
                  rw [Finset.sum_mul]
                  congr 1
                  funext m
                  field_simp [hcastN]
          _ = (N : ℝ) * (∑ m ∈ Multi.msizeExact (X := C) N, (1 / (N : ℝ)) * supOf m * (P {ω : Ω | Wcnt ω = m}).toReal) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro m hm
                  rw [hwlaw m hm]
      _ = (N : ℝ) * (∫ (ω : Ω), supCell ω ∂P) := by
        rw [hinteg]
  -- helper: supCell and 1_{good}·supS are integrable and the bad parts vanish
  have hsupCell_mble : Measurable (fun ω : Ω => supCell ω) := by
    rw [hsumfun]
    refine Finset.measurable_sum (Multi.msizeExact (X := C) N) (fun m hm => ?_)
    have hcst : Measurable (fun _ : Ω => ((1 / (N : ℝ)) * supOf m)) := measurable_const
    have hind := hcst.indicator (hWm_meas m)
    have hfun : (fun ω : Ω => (if Wcnt ω = m then (1 / (N : ℝ)) * supOf m else 0))
        = ({ω : Ω | Wcnt ω = m}).indicator (fun _ : Ω => ((1 / (N : ℝ)) * supOf m)) := by
      funext ω
      by_cases h : Wcnt ω = m <;> simp [h]
    rwa [hfun]
  have hCellb : ∀ ω : Ω, |supCell ω| ≤ (Ln : ℝ) * eta := by
    intro ω
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    have hpos : 0 ≤ supCell ω := by
      rw [hEsupCell_form ω]
      have h0 : 0 ≤ supOf (Wcnt ω) := by
        unfold supOf
        have hm := Finset.max'_mem (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)))) (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨(∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        rcases (Finset.mem_image.mp hm) with ⟨i, hi, hEq⟩
        rw [← hEq]
        exact Finset.sum_nonneg (by
          intro c hc
          exact mul_nonneg (by exact_mod_cast Nat.zero_le (Wcnt ω c)) (by
            dsimp [lamC]
            exact mul_nonneg (by exact_mod_cast Nat.zero_le (c i).val) heta0))
      have hrec : 0 ≤ (1 / (N : ℝ)) := by
        exact div_nonneg zero_le_one (le_of_lt hNposR)
      exact mul_nonneg hrec h0
    have hle : supCell ω ≤ (Ln : ℝ) * eta := by
      rw [hEsupCell_form ω]
      have htop : supOf (Wcnt ω) ≤ (Ln : ℝ) * eta * (N : ℝ) := by
        unfold supOf
        refine Finset.max'_le (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)))) (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨(∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
          ((Ln : ℝ) * eta * (N : ℝ)) ?_
        intro y hy
        rcases (Finset.mem_image.mp hy) with ⟨i, hi, rfl⟩
        calc
          (∑ c : C, ((Wcnt ω c : ℝ) * lamC i c)) ≤ ∑ c : C, ((Wcnt ω c : ℝ) * ((Ln : ℝ) * eta)) := by
            exact Finset.sum_le_sum (by
              intro c hc
              exact mul_le_mul_of_nonneg_left (by
                dsimp [lamC]
                have hlt : (c i).val ≤ Ln := Nat.le_of_lt_succ (c i).isLt
                have hc2 : ((c i).val : ℝ) ≤ (Ln : ℝ) := by exact_mod_cast hlt
                exact mul_le_mul_of_nonneg_right hc2 heta0) (by exact_mod_cast Nat.zero_le (Wcnt ω c)))
          _ = (Ln : ℝ) * eta * (∑ c : C, (Wcnt ω c : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c hc
            ring
          _ = (Ln : ℝ) * eta * (N : ℝ) := by
            have hW := hWsize ω
            have hWc : ((∑ c : C, Wcnt ω c : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hW
            rw [← hWc]
            norm_num
      have hrec : 0 ≤ (1 / (N : ℝ)) := by
        exact div_nonneg zero_le_one (le_of_lt hNposR)
      calc
        (1 / (N : ℝ)) * supOf (Wcnt ω) ≤ (1 / (N : ℝ)) * ((Ln : ℝ) * eta * (N : ℝ)) := by
                exact mul_le_mul_of_nonneg_left htop hrec
        _ = (Ln : ℝ) * eta := by
                have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N_pos)
                field_simp [hNne]
    have hAbs : |supCell ω| = supCell ω := abs_of_nonneg hpos
    rw [hAbs]
    exact hle
  have hsupCell_int : Integrable (fun ω : Ω => supCell ω) P := by
    have hb : ∀ᵐ (ω : Ω) ∂P, ‖supCell ω‖ ≤ ‖(Ln : ℝ) * eta‖ := by
      exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 ≤ (Ln : ℝ) * eta := by positivity
        have h := hCellb ω
        simpa [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg heta0] using h)
    exact MeasureTheory.Integrable.mono (MeasureTheory.integrable_const (μ := P) (c := ((Ln : ℝ) * eta))) (hsupCell_mble.aestronglyMeasurable) hb
  have hnull_cell : (∫ (ω : Ω), (if ω ∈ goodᶜ then supCell ω else 0) ∂P) = 0 := by
    have hgc : ∀ᵐ (ω : Ω) ∂P, ω ∉ goodᶜ := by
      rw [MeasureTheory.ae_iff]
      have hset : {ω : Ω | ¬ ¬ (ω ∈ goodᶜ)} = goodᶜ := by
        ext ω
        constructor
        · intro hh
          by_contra hc
          exact hh hc
        · intro hω
          intro hn
          exact hn hω
      rw [hset]
      exact hgoodc_P
    have hae : (fun ω : Ω => (if ω ∈ goodᶜ then supCell ω else 0)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
      filter_upwards [hgc] with ω hω
      simp [hω]
    exact MeasureTheory.integral_eq_zero_of_ae hae
  have hnull_supS : (∫ (ω : Ω), (if ω ∈ goodᶜ then supS ω else 0) ∂P) = 0 := by
    have hgc : ∀ᵐ (ω : Ω) ∂P, ω ∉ goodᶜ := by
      rw [MeasureTheory.ae_iff]
      have hset : {ω : Ω | ¬ ¬ (ω ∈ goodᶜ)} = goodᶜ := by
        ext ω
        constructor
        · intro hh
          by_contra hc
          exact hh hc
        · intro hω
          intro hn
          exact hn hω
      rw [hset]
      exact hgoodc_P
    have hae : (fun ω : Ω => (if ω ∈ goodᶜ then supS ω else 0)) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
      filter_upwards [hgc] with ω hω
      simp [hω]
    exact MeasureTheory.integral_eq_zero_of_ae hae
  -- the expectation of supCell is within eta of 1 (compare to supS, whose integral is 1)
  have hEsupCell : |(∫ (ω : Ω), supCell ω ∂P) - 1| ≤ eta := by
    have hd_int : Integrable (fun ω : Ω => supCell ω - supS ω) P := hsupCell_int.sub hsupS_int
    have hInt : (∫ (ω : Ω), supCell ω ∂P) - 1 = ∫ (ω : Ω), (supCell ω - supS ω) ∂P := by
      calc
        (∫ (ω : Ω), supCell ω ∂P) - 1 = (∫ (ω : Ω), supCell ω ∂P) - (∫ (ω : Ω), supS ω ∂P) := by
                rw [hEsupS]
        _ = ∫ (ω : Ω), (supCell ω - supS ω) ∂P := by
                rw [MeasureTheory.integral_sub hsupCell_int hsupS_int]
    have hnn : ‖∫ (ω : Ω), (supCell ω - supS ω) ∂P‖ ≤
        (∫ (ω : Ω), ‖supCell ω - supS ω‖ ∂P) := by
      exact MeasureTheory.norm_integral_le_integral_norm (f := fun ω : Ω => supCell ω - supS ω)
    have hEqNorm : (∫ (ω : Ω), ‖supCell ω - supS ω‖ ∂P) = (∫ (ω : Ω), |supCell ω - supS ω| ∂P) := by
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs]))
    have hAbsStep : |(∫ (ω : Ω), supCell ω ∂P) - 1| ≤ ∫ (ω : Ω), |supCell ω - supS ω| ∂P := by
      rw [hInt]
      rw [hEqNorm] at hnn
      simpa [Real.norm_eq_abs] using hnn
    have hgood_ae : ∀ᵐ (ω : Ω) ∂P, ω ∈ good := by
      rw [MeasureTheory.ae_iff]
      change P {ω : Ω | ¬ ω ∈ good} = 0
      rw [show {ω : Ω | ¬ ω ∈ good} = goodᶜ by rfl]
      exact hgoodc_P
    let bd1 : Ω → ℝ := (good).indicator (fun _ : Ω => eta)
    let bd2 : Ω → ℝ := (goodᶜ).indicator (fun ω : Ω => |supCell ω - supS ω|)
    have hnull2 : (∫ (ω : Ω), bd2 ω ∂P) = 0 := by
      have hae : bd2 =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
        filter_upwards [hgood_ae] with ω hω
        dsimp [bd2]
        simp [hω]
      exact MeasureTheory.integral_eq_zero_of_ae hae
    have hbd : (fun ω : Ω => |supCell ω - supS ω|) ≤ fun ω : Ω => bd1 ω + bd2 ω := by
      intro ω
      dsimp
      by_cases hg : ω ∈ good
      · have h1 : bd1 ω = eta := by dsimp [bd1]; simp [hg]
        have h2 : bd2 ω = 0 := by dsimp [bd2]; simp [hg]
        have hd : |supCell ω - supS ω| ≤ eta := by
          rw [abs_sub_comm]
          exact hptw ω hg
        rw [h1, h2]
        simpa using hd
      · have h1 : bd1 ω = 0 := by dsimp [bd1]; simp [hg]
        have h2 : bd2 ω = |supCell ω - supS ω| := by dsimp [bd2]; simp [hg]
        rw [h1, h2]
        simp
    have hd_abs_int : Integrable (fun ω : Ω => |supCell ω - supS ω|) P := by
      have hEq : (fun ω : Ω => ‖supCell ω - supS ω‖) =ᵐ[P] (fun ω : Ω => |supCell ω - supS ω|) := by
        exact Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs])
      exact MeasureTheory.Integrable.congr hd_int.norm hEq
    have hbd1_int : Integrable bd1 P := by
      have hcst := (MeasureTheory.integrable_const (μ := P) (c := eta)).indicator hgoodmeas
      have hfun : bd1 = (good).indicator (fun _ : Ω => eta) := by
        rfl
      rwa [hfun]
    have hbd2_int : Integrable bd2 P := by
      refine MeasureTheory.Integrable.mono hd_abs_int ?_ ?_
      · exact hd_abs_int.aestronglyMeasurable.indicator hgoodc_meas
      · filter_upwards with ω
        by_cases h : ω ∈ good
        · have hb : bd2 ω = 0 := by dsimp [bd2]; simp [h]
          rw [hb]
          have hz : ‖(0 : ℝ)‖ = 0 := by simp
          rw [hz]
          exact norm_nonneg _
        · have hb : bd2 ω = |supCell ω - supS ω| := by dsimp [bd2]; simp [h]
          rw [hb]
    have hmono : (∫ (ω : Ω), |supCell ω - supS ω| ∂P) ≤ (∫ (ω : Ω), (bd1 ω + bd2 ω) ∂P) := by
      exact MeasureTheory.integral_mono hd_abs_int (hbd1_int.add hbd2_int) hbd
    have hbnd_val : (∫ (ω : Ω), (bd1 ω + bd2 ω) ∂P) = eta := by
      rw [MeasureTheory.integral_add hbd1_int hbd2_int]
      rw [hnull2]
      have hfirst : (∫ (ω : Ω), bd1 ω ∂P) = eta := by
        dsimp [bd1]
        rw [MeasureTheory.integral_indicator hgoodmeas]
        rw [MeasureTheory.setIntegral_const]
        rw [MeasureTheory.measureReal_def]
        rw [hgoodP]
        simp
      rw [hfirst]
      simp
    calc
      |(∫ (ω : Ω), supCell ω ∂P) - 1| ≤ ∫ (ω : Ω), |supCell ω - supS ω| ∂P := hAbsStep
      _ ≤ eta := by
              rw [← hbnd_val]
              exact hmono
  have hEsupI_pos : 0 < EsupI := by
    rw [hEsupI_eq]
    have hc := abs_le.mp hEsupCell
    have heta1 : eta < 1 := by norm_num [eta]
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast N_pos
    have hpos : 0 < (∫ (ω : Ω), supCell ω ∂P) := by linarith
    exact mul_pos hN0 hpos
  have hEsupI_le : EsupI ≤ (N : ℝ) * (2 - eta / Multi.Lw) := by
    rw [hEsupI_eq]
    have hA : eta / Multi.Lw ≤ eta := by
      have hLwpos : 0 < Multi.Lw := by unfold Multi.Lw Multi.Kbig; norm_num
      have hLw1 : (1 : ℝ) ≤ Multi.Lw := by unfold Multi.Lw Multi.Kbig; norm_num
      have h1 : eta ≤ eta * Multi.Lw := by
        simpa using (mul_le_mul_of_nonneg_left hLw1 heta0)
      rw [div_le_iff₀ hLwpos]
      exact h1
    have hB : eta + eta / Multi.Lw ≤ 2 * eta := by nlinarith
    have hC : 2 * eta ≤ 1 := by norm_num [eta]
    have h1 : (∫ (ω : Ω), supCell ω ∂P) ≤ 1 + eta := by
      have hc := abs_le.mp hEsupCell
      linarith
    have h2 : 1 + eta ≤ 2 - eta / Multi.Lw := by linarith
    have h3 : (∫ (ω : Ω), supCell ω ∂P) ≤ 2 - eta / Multi.Lw := by linarith
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    exact mul_le_mul_of_nonneg_left h3 hN0
  -- the multiset theorem produces a cover of the threshold family over cells
  have hsupI_eq (m : C → ℕ) : Multi.supI lamC m = supOf m := by
    have h1 : (Finset.univ.image (fun i : ↥𝓕 => Multi.lamSumI (X := C) lamC i m)) =
        (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))) := by
      congr 1
    by_cases hne : ((Finset.univ : Finset ↥𝓕).image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))).Nonempty
    · have hne' : ((Finset.univ : Finset ↥𝓕).image (fun i : ↥𝓕 => Multi.lamSumI (X := C) lamC i m)).Nonempty := by
        rwa [h1]
      have hres : Multi.supI lamC m = (Finset.univ.image (fun i : ↥𝓕 => Multi.lamSumI (X := C) lamC i m)).max' hne' := by
        simp [Multi.supI, hne']
      have hres2 : (Finset.univ.image (fun i : ↥𝓕 => Multi.lamSumI (X := C) lamC i m)).max' hne'
          = (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))).max' hne :=
        max'_congr_image h1 hne' hne
      have hres3 : (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))).max' hne = supOf m := by
        unfold supOf
        exact finset_max'_proof_irrel _ _
      calc
        Multi.supI lamC m = (Finset.univ.image (fun i : ↥𝓕 => Multi.lamSumI (X := C) lamC i m)).max' hne' := hres
        _ = (Finset.univ.image (fun i : ↥𝓕 => (∑ c : C, (m c : ℝ) * lamC i c))).max' hne := hres2
        _ = supOf m := hres3
    · exfalso
      exact hne ⟨(∑ c : C, (m c : ℝ) * lamC (Classical.choose hIne) c),
        Finset.mem_image.mpr ⟨Classical.choose hIne, Finset.mem_univ _, rfl⟩⟩
  have hEsupI_multi : 0 < Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC := by
    have heq : Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC = EsupI := by
      unfold Multi.EsupI EsupI massC
      apply Finset.sum_congr rfl
      intro m hm
      rw [hsupI_eq m]
    rw [heq]
    exact hEsupI_pos
  have hEsupI_le_multi : Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC
      ≤ (N : ℝ) * (2 - eta / Multi.Lw) := by
    have heq : Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC = EsupI := by
      unfold Multi.EsupI EsupI massC
      apply Finset.sum_congr rfl
      intro m hm
      rw [hsupI_eq m]
    rw [heq]
    exact hEsupI_le
  have hlam0 (i : ↥𝓕) (c : C) : 0 ≤ lamC i c := by
    dsimp [lamC]
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (c i).val)) heta0
  have hmulti := Multi.multi_w_type N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC N_pos
    (fun c : C => NNReal.coe_nonneg (muC c)) hmuCsumR hlam0 (by
      -- hEpos for multi_w_type: EsupI N μ I lam > 0:
      simpa using hEsupI_multi)
  rcases hmulti with ⟨Cov0, hCov0, hCost0⟩
  -- trim the cover: drop multisets supported on mass-zero cells, and trim each coordinate
  let Gtrim : (C → ℕ) → C → ℕ := fun G c => if (N : ℝ) * (muC c : ℝ) ≤ (G c : ℝ) then G c else 0
  let Cov1 : Finset (C → ℕ) := (Cov0.image Gtrim).filter (fun G => ∀ c : C, muC c = 0 → G c = 0)
  have hCov1cover : ∀ S ∈ (Multi.threshFamilyI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC : Set (C → ℕ)),
      (∀ c : C, muC c = 0 → S c = 0) → ∃ G ∈ Cov1, Multi.subM G S := by
    intro S hS hS0
    have hcov0 := hCov0 S hS
    rcases hcov0 with ⟨G0, hG0, hsub⟩
    have hsubM : Multi.subM G0 S := hsub
    have hG0free : ∀ c : C, muC c = 0 → G0 c = 0 := by
      intro c hμ0
      have hle : G0 c ≤ S c := hsubM c
      have hSc : S c = 0 := hS0 c hμ0
      omega
    let G : C → ℕ := Gtrim G0
    have hGimg : G ∈ Cov0.image Gtrim := by
      exact Finset.mem_image.mpr ⟨G0, hG0, rfl⟩
    have hGfilter : ∀ c : C, muC c = 0 → G c = 0 := by
      intro c hμ0
      have hG0c : G0 c = 0 := hG0free c hμ0
      dsimp [G, Gtrim]
      rw [hG0c]
      simp
    refine ⟨G, ?_, ?_⟩
    · unfold Cov1
      exact Finset.mem_filter.mpr ⟨hGimg, hGfilter⟩
    · intro c
      have htrim_le : Gtrim G0 c ≤ G0 c := by
        dsimp [Gtrim]
        by_cases h : (N : ℝ) * (muC c : ℝ) ≤ (G0 c : ℝ)
        · simp [h]
        · simp [h]
      exact le_trans htrim_le (hsubM c)
  have hCov1cost : Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov1 ≤ (2 : ℝ)⁻¹ := by
    calc
      Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov1
          ≤ Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) (Cov0.image Gtrim) := by
              have hnonneg (G : C → ℕ) : 0 ≤ Multi.wCost (Multi.eN N) (fun c : C => (muC c : ℝ)) G := by
                dsimp [Multi.wCost]
                exact Finset.prod_nonneg (by
                  intro c hc
                  have hbase : 0 ≤ Multi.eN N * (muC c : ℝ) := mul_nonneg (MultiCost.eN_nonneg N) (NNReal.coe_nonneg (muC c))
                  have hpw : 0 ≤ (Multi.eN N * (muC c : ℝ)) ^ (G c) := pow_nonneg hbase _
                  have hfac : 0 < (Nat.factorial (G c) : ℝ) := by exact_mod_cast Nat.factorial_pos (G c)
                  exact div_nonneg hpw (le_of_lt hfac))
              unfold Multi.mTotalCost
              unfold Cov1
              exact Finset.sum_le_sum_of_subset_of_nonneg (by
                intro G hG
                exact (Finset.mem_filter.mp hG).1) (fun G hGt hGnot => hnonneg G)
      _ ≤ Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov0 := by
              exact MultiCost.total_cost_trim_le N (fun c : C => (muC c : ℝ))
                (fun c => NNReal.coe_nonneg (muC c)) Cov0
      _ ≤ (2 : ℝ)⁻¹ := hCost0
  -- per-G events
  let gTN : (C → ℕ) → C → ℝ := fun G c => Discret2.gT N muC G c
  let tTtilde : (C → ℕ) → ℝ := fun G => Discret2.tT N muC G
  let costG : (C → ℕ) → ℝ := fun G => Discret2.costG N muC G
  have hGtrim (G : C → ℕ) (hG : G ∈ Cov1) (c : C) (hGc : 0 < G c) :
      (N : ℝ) * (muC c : ℝ) ≤ (G c : ℝ) := by
    have hmem : G ∈ (Cov0.image Gtrim).filter (fun G => ∀ c : C, muC c = 0 → G c = 0) := hG
    rcases (Finset.mem_filter.mp hmem) with ⟨him, hnf⟩
    rcases (Finset.mem_image.mp him) with ⟨G0, hG0, hEq⟩
    have hval : G c = Gtrim G0 c := by rw [hEq]
    by_cases hcase : (N : ℝ) * (muC c : ℝ) ≤ (G0 c : ℝ)
    · have hkeep : Gtrim G0 c = G0 c := by
        dsimp [Gtrim]
        simp [hcase]
      rw [hval, hkeep]
      exact hcase
    · exfalso
      have htrim0 : Gtrim G0 c = 0 := by
        dsimp [Gtrim]
        simp [hcase]
      have hz : G c = 0 := by rw [hval, htrim0]
      exact (ne_of_gt hGc) hz
  have hGpos (G : C → ℕ) (hG : G ∈ Cov1) (c : C) (hGc : 0 < G c) : 0 < (muC c : ℝ) := by
    have hmem : G ∈ (Cov0.image Gtrim).filter (fun G => ∀ c : C, muC c = 0 → G c = 0) := hG
    have hnf : ∀ c : C, muC c = 0 → G c = 0 := (Finset.mem_filter.mp hmem).2
    have hne : muC c ≠ 0 := by
      intro h0
      exact (ne_of_gt hGc) (hnf c h0)
    have hneR : (muC c : ℝ) ≠ 0 := by exact_mod_cast hne
    exact lt_of_le_of_ne (NNReal.coe_nonneg (muC c)) hneR.symm
  have hcost_mem (G : C → ℕ) (hG : G ∈ Cov1) : costG G ≤ (2 : ℝ)⁻¹ := by
    have hw : Multi.wCost (Multi.eN N) (fun c : C => (muC c : ℝ)) G = costG G := by
      dsimp [costG]
      unfold Discret2.costG Multi.wCost Multi.eN
      rfl
    have hnonneg_all : ∀ H ∈ Cov1, 0 ≤ Multi.wCost (Multi.eN N) (fun c : C => (muC c : ℝ)) H := by
      intro H hH
      have hterm (c : C) : 0 ≤ (Multi.eN N) * (muC c : ℝ) := by
        have h1 : 0 ≤ (Multi.eN N) := by
          unfold Multi.eN Multi.ee
          positivity
        exact mul_nonneg h1 (NNReal.coe_nonneg (muC c))
      dsimp [Multi.wCost]
      exact Finset.prod_nonneg (by
        intro c hc
        have hpw : 0 ≤ (Multi.eN N * (muC c : ℝ)) ^ H c := pow_nonneg (hterm c) _
        exact div_nonneg hpw (by positivity))
    have hle : costG G ≤ Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov1 := by
      rw [← hw]
      unfold Multi.mTotalCost
      exact Finset.single_le_sum (by intro H hH; exact hnonneg_all H hH) hG
    exact le_trans hle hCov1cost
  have htT_nonpos (G : C → ℕ) (hG : G ∈ Cov1) : tTtilde G ≤ 0 := by
    dsimp [tTtilde]
    unfold Discret2.tT
    exact Finset.sum_nonpos (by
      intro c hc
      by_cases hG0 : G c = 0
      · have hg : Discret2.gT N muC G c = 0 := by simp [Discret2.gT, hG0]
        rw [hg]
        simp
      · have hpos : 0 < G c := Nat.pos_of_ne_zero hG0
        have hg : Discret2.gT N muC G c ≤ 0 := Discret2.gT_nonpos N muC G hpos (hGtrim G hG c hpos)
        have h1 : 0 ≤ (G c : ℝ) := by exact_mod_cast Nat.zero_le (G c)
        exact mul_nonpos_of_nonneg_of_nonpos h1 hg)
  have htT_neg (G : C → ℕ) (hG : G ∈ Cov1) : tTtilde G < 0 := by
    classical
    by_contra hn
    have hle0 : tTtilde G ≤ 0 := htT_nonpos G hG
    have hz : tTtilde G = 0 := le_antisymm hle0 (le_of_not_gt hn)
    have uterm (c : C) : (G c : ℝ) * gTN G c ≤ 0 := by
      by_cases hGc : G c = 0
      · have hg : gTN G c = 0 := by
          dsimp [gTN]
          unfold Discret2.gT
          simp [hGc]
        rw [hg]
        simp
      · have hpos : 0 < G c := Nat.pos_of_ne_zero hGc
        have hg : gTN G c ≤ 0 := by
          dsimp [gTN]
          exact Discret2.gT_nonpos N muC G hpos (hGtrim G hG c hpos)
        exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast Nat.zero_le (G c)) hg
    have hsum0 : (∑ c : C, (G c : ℝ) * gTN G c) = 0 := by
      dsimp [tTtilde] at hz
      unfold Discret2.tT at hz
      simpa [gTN] using hz
    have hterm0 : ∀ c : C, (G c : ℝ) * gTN G c = 0 := by
      intro c
      have u_le : (G c : ℝ) * gTN G c ≤ 0 := uterm c
      have u_ge : 0 ≤ (G c : ℝ) * gTN G c := by
        have hs := Finset.single_le_sum (s := Finset.univ) (f := fun c : C => - ((G c : ℝ) * gTN G c))
          (by
            intro x hx
            exact neg_nonneg.mpr (uterm x)) (Finset.mem_univ c)
        have hz' : (∑ x : C, - ((G x : ℝ) * gTN G x)) = 0 := by
          calc
            (∑ x : C, - ((G x : ℝ) * gTN G x)) = - (∑ x : C, (G x : ℝ) * gTN G x) := by rw [Finset.sum_neg_distrib]
            _ = 0 := by rw [hsum0]; simp
        have hsz : (∑ x ∈ (Finset.univ : Finset C), - ((G x : ℝ) * gTN G x)) = 0 := by simpa using hz'
        linarith
      exact le_antisymm u_le u_ge
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.exp_strictMono.monotone (by norm_num : (0 : ℝ) ≤ 1))
    have hfact (c : C) : 1 ≤ (Real.exp 1 * (N : ℝ) * (muC c : ℝ)) ^ (G c) / (Nat.factorial (G c) : ℝ) := by
      by_cases hGc : G c = 0
      · rw [hGc]
        norm_num
      · have hpos : 0 < G c := Nat.pos_of_ne_zero hGc
        have hg0 : gTN G c = 0 := by
          have hu := hterm0 c
          have hGcR : (G c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
          exact (mul_eq_zero.mp hu).resolve_left hGcR
        have hμ0 : 0 < (muC c : ℝ) := hGpos G hG c hpos
        have harg : 0 < (N : ℝ) * (muC c : ℝ) / (G c : ℝ) := by
          exact div_pos (mul_pos (by exact_mod_cast N_pos) hμ0) (by exact_mod_cast hpos)
        have hdiv : (N : ℝ) * (muC c : ℝ) / (G c : ℝ) = 1 := by
          have h1 := Real.exp_log harg
          have h2 : Real.exp (Real.log ((N : ℝ) * (muC c : ℝ) / (G c : ℝ))) = 1 := by
            dsimp [gTN] at hg0
            unfold Discret2.gT at hg0
            rw [dif_neg (ne_of_gt hpos)] at hg0
            rw [hg0]
            norm_num
          rwa [h1] at h2
        have hEq : (N : ℝ) * (muC c : ℝ) = (G c : ℝ) := by
          have hGcR : (G c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
          field_simp [hGcR] at hdiv
          exact hdiv
        -- base equality e·N·μc = e·Gc, then (e·Gc)^k ≥ k!
        have hbase : (Real.exp 1) * (N : ℝ) * (muC c : ℝ) = (Real.exp 1) * (G c : ℝ) := by
          calc
            (Real.exp 1) * (N : ℝ) * (muC c : ℝ) = (Real.exp 1) * ((N : ℝ) * (muC c : ℝ)) := by ring
            _ = (Real.exp 1) * (G c : ℝ) := by rw [hEq]
        have hb' : (Real.exp 1 * (N : ℝ) * (muC c : ℝ)) ^ (G c) = (Real.exp 1 * (G c : ℝ)) ^ (G c) := by
          rw [hbase]
        have hk0 : 0 ≤ (G c : ℝ) := by exact_mod_cast Nat.zero_le (G c)
        have hgle : (G c : ℝ) ≤ Real.exp 1 * (G c : ℝ) := by
          calc
            (G c : ℝ) = 1 * (G c : ℝ) := by ring
            _ ≤ Real.exp 1 * (G c : ℝ) := mul_le_mul_of_nonneg_right he1 hk0
        have hpowge : (G c : ℝ) ^ (G c) ≤ (Real.exp 1 * (G c : ℝ)) ^ (G c) := by
          exact pow_le_pow_left₀ hk0 hgle (G c)
        have hfact1 : (Nat.factorial (G c) : ℝ) ≤ (G c : ℝ) ^ (G c) := by
          simpa using (MultiCost.factorial_le_self_pow (G c))
        have hfact2 : (Nat.factorial (G c) : ℝ) ≤ (Real.exp 1 * (G c : ℝ)) ^ (G c) :=
          le_trans hfact1 hpowge
        have hfacpos : 0 < (Nat.factorial (G c) : ℝ) := by positivity
        have hone : (1 : ℝ) ≤ (Real.exp 1 * (G c : ℝ)) ^ (G c) / (Nat.factorial (G c) : ℝ) := by
          exact (le_div_iff₀ hfacpos).mpr (by simpa using hfact2)
        rw [hb']
        exact hone
    -- total cost is ≥ 1, contradicting costG G ≤ 1/2
    have hcost1 : (1 : ℝ) ≤ costG G := by
      unfold costG
      unfold Discret2.costG
      calc
        (1 : ℝ) = ∏ c : C, (1 : ℝ) := by simp
        _ ≤ ∏ c : C, ((Real.exp 1) * (N : ℝ) * (muC c : ℝ)) ^ (G c) / (Nat.factorial (G c) : ℝ) := by
                exact Finset.prod_le_prod (by intro c hc; norm_num) (by intro c hc; exact hfact c)
    have hle := hcost_mem G hG
    linarith
  -- the functions g_G : 𝕋 → ℝ≥0 (measurable) and thresholds t_G : ℝ≥0
  have hneg0 (G : C → ℕ) (hG : G ∈ Cov1) (c : C) : 0 ≤ - (N : ℝ) * gTN G c := by
    by_cases hGc : G c = 0
    · have hg : Discret2.gT N muC G c = 0 := by simp [Discret2.gT, hGc]
      dsimp [gTN]
      rw [hg]
      simp
    · have hpos : 0 < G c := Nat.pos_of_ne_zero hGc
      have hg : Discret2.gT N muC G c ≤ 0 := Discret2.gT_nonpos N muC G hpos (hGtrim G hG c hpos)
      have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      dsimp [gTN]
      have hmn : (N : ℝ) * Discret2.gT N muC G c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 hg
      linarith
  -- event probabilities via Discret2 (Y'-based, measurable samples)
  have hprobG (G : C → ℕ) (hG : G ∈ Cov1) :
      (P {ω | (∑ j : Fin N, gTN G (Xs j ω)) ≤ tTtilde G}).toReal ≤ costG G := by
    exact Discret2.prob_sum_gT_le_tT (Ω := Ω) P N_pos Xs muC G hXsiid hXsmeas hXsLaw (by
      intro c hc
      exact hGpos G hG c hc) (by
      intro c hc
      exact hGtrim G hG c hc)
  -- =================================================================
  -- Y-side: all containment arguments are done pointwise with the ORIGINAL Y
  -- =================================================================
  let XsY : Fin N → Ω → C := fun j ω => pi (Y j ω)
  let WcntY : Ω → C → ℕ := fun ω c => Discret1.countVec (fun j : Fin N => XsY j ω) c
  let supSY : Ω → ℝ := fun ω => (zm ω : ℝ) / E
  let supCellY : Ω → ℝ := fun ω =>
    (Finset.univ.image (fun i : ↥𝓕 =>
      (1 / (N : ℝ)) * (∑ c : C, (WcntY ω c : ℝ) * lamC i c))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ c : C, (WcntY ω c : ℝ) * lamC i c), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  have hWcntY_size (ω : Ω) : (∑ c : C, WcntY ω c) = N := by
    dsimp [WcntY]
    exact Discret1.sum_countVec (fun j : Fin N => XsY j ω)
  have hsumreidxY (i : ↥𝓕) (ω : Ω) :
      (∑ j : Fin N, lamC i (pi (Y j ω))) = ∑ c : C, (WcntY ω c : ℝ) * lamC i c := by
    have hre := Discret2.sum_coord (t := fun j : Fin N => XsY j ω) (f := fun c : C => lamC i c)
    dsimp [WcntY, XsY] at hre ⊢
    exact hre
  have supCellY_form (ω : Ω) : supCellY ω = (1 / (N : ℝ)) * supOf (WcntY ω) := by
    classical
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    let s : ↥𝓕 → ℝ := fun i => ∑ c : C, ((WcntY ω c : ℝ) * lamC i c)
    have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * s i)) =
        (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))) := by
      congr 1
      funext i
      ring
    have hform : supCellY ω =
        (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      unfold supCellY
      refine max'_congr_image ?_ _ _
      · simpa [s] using him
    have hmax : (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        = ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ) := by
      simpa using (maxR_div hIne s (N : ℝ) hNposR)
    calc
      supCellY ω = (Finset.univ.image (fun i : ↥𝓕 => s i / (N : ℝ))).max' (by
          rcases hIne with ⟨i, hi⟩
          exact ⟨s i / (N : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := hform
      _ = ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ) := hmax
      _ = (1 / (N : ℝ)) * supOf (WcntY ω) := by
        calc
          ((Finset.univ.image s).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / (N : ℝ)
              = (1 / (N : ℝ)) * (Finset.univ.image s).max' (by
                  rcases hIne with ⟨i, hi⟩
                  exact ⟨s i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
                  ring
          _ = (1 / (N : ℝ)) * supOf (WcntY ω) := by
                  congr 1
  -- the real sup over Y equals the per-i average max (identity for supSY)
  have hsupS_formY (ω : Ω) : supSY ω =
      (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
    classical
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    have hper (i : ↥𝓕) : (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω))
        = ((valZ i ω : ℝ≥0) : ℝ) / E := by
      have hsumdiv : (∑ j : Fin N, (fF i (Y j ω) : ℝ) / E) = (∑ j : Fin N, (fF i (Y j ω) : ℝ)) / E := by
        rw [← Finset.sum_div]
      have hZc : ((Z N Y (fF i) ω : ℝ≥0) : ℝ) = ((N : ℝ≥0)⁻¹ : ℝ≥0) * (∑ j : Fin N, (fF i (Y j ω) : ℝ)) := by
        simp [Z, NNReal.coe_mul, NNReal.coe_sum]
      have hcast : (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = 1 / (N : ℝ) := by norm_num [one_div]
      have hval : (valZ i ω : ℝ) = ((Z N Y (fF i) ω : ℝ≥0) : ℝ) := rfl
      dsimp [fn]
      calc
        (1 / (N : ℝ)) * (∑ j : Fin N, (fF i (Y j ω) : ℝ) / E) = (1 / (N : ℝ)) * ((∑ j : Fin N, (fF i (Y j ω) : ℝ)) / E) := by rw [hsumdiv]
        _ = ((1 / (N : ℝ)) * (∑ j : Fin N, (fF i (Y j ω) : ℝ))) / E := by ring
        _ = (((N : ℝ≥0)⁻¹ : ℝ≥0) * (∑ j : Fin N, (fF i (Y j ω) : ℝ))) / E := by rw [hcast]
        _ = ((Z N Y (fF i) ω : ℝ≥0) : ℝ) / E := by rw [hZc]
        _ = ((valZ i ω : ℝ≥0) : ℝ) / E := by rw [hval]
    have hmaxdiv : (Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ) / E)).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(((valZ i ω : ℝ≥0) : ℝ) / E), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
        = ((Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨((valZ i ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / E := by
      exact maxR_div hIne (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ)) E hEpos
    have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω))))
        = (Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ) / E)) := by
      congr 1
      funext i
      exact hper i
    have hzm : (zm ω : ℝ) = (Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨((valZ i ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      dsimp [zm]
      exact The13Meas.maxR_coe_ident hIne (fun i : ↥𝓕 => valZ i ω)
    calc
      supSY ω = (zm ω : ℝ) / E := rfl
      _ = ((Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨((valZ i ω : ℝ≥0) : ℝ), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)) / E := by
            rw [hzm]
      _ = (Finset.univ.image (fun i : ↥𝓕 => ((valZ i ω : ℝ≥0) : ℝ) / E)).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨(((valZ i ω : ℝ≥0) : ℝ) / E), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
            exact hmaxdiv.symm
      _ = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)))).max' (by
            rcases hIne with ⟨i, hi⟩
            exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
            exact (max'_congr_image him _ _).symm
  -- |supSY − supCellY| ≤ eta whenever no Y-sample falls in ESC
  have hptwY (ω : Ω) (hω : ∀ j : Fin N, Y j ω ∉ ESC) : |supSY ω - supCellY ω| ≤ eta := by
    have hps (i : ↥𝓕) (j : Fin N) : |fn i (Y j ω) - lamC i (pi (Y j ω))| ≤ eta := by
      exact herr (Y j ω) (hω j) i
    have hpsum (i : ↥𝓕) : |(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)) -
          (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω)))| ≤ eta := by
      have hcast0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
      have hcast : (N : ℝ) ≠ 0 := ne_of_gt hcast0
      have hsum : |(∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω)))| ≤ (N : ℝ) * eta := by
        calc
          |(∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω)))|
              = |∑ j : Fin N, (fn i (Y j ω) - lamC i (pi (Y j ω)))| := by
                  congr 1
                  rw [← Finset.sum_sub_distrib]
          _ ≤ ∑ j : Fin N, |fn i (Y j ω) - lamC i (pi (Y j ω))| := by
                  exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin N, eta := by
                  apply Finset.sum_le_sum
                  intro j hj
                  exact hps i j
          _ = (N : ℝ) * eta := by simp
      have hpos : 0 ≤ (1 / (N : ℝ)) := by positivity
      have hmain : |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω))))| ≤ eta := by
        calc
          |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω))))|
              = (1 / (N : ℝ)) * |(∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω)))| := by
                  rw [abs_mul]
                  congr 1
                  rw [abs_of_nonneg hpos]
          _ ≤ (1 / (N : ℝ)) * ((N : ℝ) * eta) := mul_le_mul_of_nonneg_left hsum hpos
          _ = eta := by
                  field_simp [hcast]
      have hEq : |(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)) - (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω)))|
          = |(1 / (N : ℝ)) * ((∑ j : Fin N, fn i (Y j ω)) - (∑ j : Fin N, lamC i (pi (Y j ω))))| := by
          congr 1
          ring
      rwa [hEq]
    have hsplit : supSY ω = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      exact hsupS_formY ω
    have hsplit2 : supCellY ω = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω))))).max' (by
        rcases hIne with ⟨i, hi⟩
        exact ⟨(1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω))), Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
      have him : (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ c : C, (WcntY ω c : ℝ) * lamC i c)))
          = (Finset.univ.image (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω))))) := by
        congr 1
        funext i
        congr 1
        exact (hsumreidxY i ω).symm
      unfold supCellY
      exact max'_congr_image him _ _
    rw [hsplit, hsplit2]
    exact DiscretLvl.sup_abs_sub_le eta (Finset.univ : Finset ↥𝓕)
      (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, fn i (Y j ω)))
      (fun i : ↥𝓕 => (1 / (N : ℝ)) * (∑ j : Fin N, lamC i (pi (Y j ω)))) hIne
      (fun i hi => hpsum i)
  -- the ESC condition and the "goodY" set (only used for containment; no measurability needed)
  let goodY : Set Ω := {ω | ∀ j : Fin N, Y j ω ∉ ESC}
  have hLw_eq : Multi.Lw = (10 : ℝ) ^ 82 := by
    unfold Multi.Lw Multi.Kbig
    norm_num
  -- E-condition ⇒ supSY ≥ 2·Lw
  have hL3 : (L3v : ℝ) = 2 * Multi.Lw := by
    rw [hLw_eq]
    unfold L3v
    norm_num
  -- the ℝ≥0-sup over 𝓕 of the empirical values is at most the max zm
  have hsupR_le (ω : Ω) : (⨆ f ∈ 𝓕, Z N Y (↑f) ω) ≤ zm ω := by
    classical
    refine ciSup_le' (fun f => ?_)
    refine ciSup_le' (fun h : f ∈ 𝓕 => ?_)
    have hmem : (Z N Y (↑f) ω : ℝ≥0) ∈ Finset.univ.image (fun i : ↥𝓕 => valZ i ω) := by
      refine Finset.mem_image.mpr ⟨⟨f, h⟩, Finset.mem_univ _, ?_⟩
      dsimp [valZ, fF]
    have hle : Z N Y (↑f) ω ≤ zm ω := by
      dsimp [zm]
      exact Finset.le_max' (Finset.univ.image (fun i : ↥𝓕 => valZ i ω)) (Z N Y (↑f) ω) hmem
    exact hle
  have hE_big (ω : Ω) (hω : (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) ≥ L3v * muinf) : (2 * Multi.Lw) ≤ supSY ω := by
    have hz' : (zm ω : ℝ≥0∞) ≥ L3v * muinf := by
      rw [hsup_inf ω, hzm_sup ω] at hω
      exact hω
    have hfin1 : ((zm ω : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have hfin2 : ((L3v : ℝ≥0) : ℝ≥0∞) * muinf ≠ ∞ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hmuinf_fin
    have hto := (ENNReal.toReal_le_toReal hfin2 hfin1).mpr hz'
    -- hto : (L3v·muinf).toReal ≤ (zmω).toReal
    have hto' : (L3v : ℝ) * E ≤ (zm ω : ℝ) := by
      have hval : ((((L3v : ℝ≥0) : ℝ≥0∞) * muinf).toReal) = (L3v : ℝ) * E := by
        rw [ENNReal.toReal_mul]
        simp [E]
      rwa [hval] at hto
    have hle : (L3v : ℝ) ≤ supSY ω := by
      dsimp [supSY]
      exact (le_div_iff₀ hEpos).mpr hto'
    rwa [hL3] at hle
  -- membership: supI(WcntY ω) ≥ Lw·EsupI
  have hmemY (ω : Ω) (hgood : ω ∈ goodY) (hbig : (2 * Multi.Lw) ≤ supSY ω) :
      WcntY ω ∈ Multi.threshFamilyI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC := by
    classical
    have hptw0 : |supSY ω - supCellY ω| ≤ eta := hptwY ω (by simpa [goodY] using hgood)
    -- supCellY ≥ supSY − eta ≥ 2·Lw − eta
    have hd := abs_le.mp hptw0
    have hge1 : (2 * Multi.Lw - eta) ≤ supCellY ω := by
      have hb : supSY ω - eta ≤ supCellY ω := by linarith [hd.2]
      have hle : 2 * Multi.Lw - eta ≤ supSY ω - eta := by linarith
      linarith
    have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have hN0' : 0 < (N : ℝ) := by exact_mod_cast N_pos
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0'
    have hbig2 : (N : ℝ) * (2 * Multi.Lw - eta) ≤ (N : ℝ) * supCellY ω := mul_le_mul_of_nonneg_left hge1 hN0
    have hLw0 : 0 ≤ Multi.Lw := by
      rw [hLw_eq]
      positivity
    have hLwne : Multi.Lw ≠ 0 := by
      have : 0 < Multi.Lw := by
        rw [hLw_eq]
        positivity
      exact ne_of_gt this
    have hmem_step : Multi.Lw * Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC ≤ supOf (WcntY ω) := by
      have h1 : Multi.Lw * Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC ≤ (N : ℝ) * (2 * Multi.Lw - eta) := by
        calc
          Multi.Lw * Multi.EsupI N (fun c : C => (muC c : ℝ)) ↥𝓕 lamC
              ≤ Multi.Lw * ((N : ℝ) * (2 - eta / Multi.Lw)) := mul_le_mul_of_nonneg_left hEsupI_le_multi hLw0
          _ = (N : ℝ) * (2 * Multi.Lw - eta) := by
                  field_simp [hLwne]
      have h2 : (N : ℝ) * (2 * Multi.Lw - eta) ≤ supOf (WcntY ω) := by
        have hNf : supOf (WcntY ω) = (N : ℝ) * supCellY ω := by
          have hc := supCellY_form ω
          calc
            supOf (WcntY ω) = (N : ℝ) * ((1 / (N : ℝ)) * supOf (WcntY ω)) := by
                    field_simp [hNne]
            _ = (N : ℝ) * supCellY ω := by rw [hc]
        rw [hNf]
        exact hbig2
      exact le_trans h1 h2
    have hsi : Multi.supI lamC (WcntY ω) = supOf (WcntY ω) := hsupI_eq (WcntY ω)
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact (Multi.mem_msizeExact_iff (X := C) (M := N)).mpr (hWcntY_size ω)
    · rw [hsi]
      exact hmem_step
  -- =========================================================
  -- escape set ESCB = ESC ∪ cells of mass zero
  -- =========================================================
  let nullC : Set C := {c | muC c = 0}
  let ESCB : Set 𝕋 := ESC ∪ {y | ∃ c : C, muC c = 0 ∧ pi y = c}
  have hESCB_eq : {y | ∃ c : C, muC c = 0 ∧ pi y = c} = pi ⁻¹' nullC := by
    ext y
    simp [nullC]
  have hnullCmeas : MeasurableSet nullC := by
    unfold nullC
    apply finite_measurableSet_all
  have hESCBmeas : MeasurableSet ESCB := by
    dsimp [ESCB]
    rw [hESCB_eq]
    exact hESCmeas.union (hpi_meas hnullCmeas)
  have hnullcell (c : C) (hμ0 : muC c = 0) : ν {y | pi y = c} = 0 := by
    have hfin : (ν.map pi) {c} ≠ ∞ := by
      have hle : (ν.map pi) {c} ≤ (ν.map pi) Set.univ := measure_mono (by intro x hx; trivial)
      have huniv : (ν.map pi) Set.univ = 1 := by
        rw [Measure.map_apply hpi_meas MeasurableSet.univ]
        rw [Set.preimage_univ]
        exact hν.measure_univ
      rw [huniv] at hle
      exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
    have hmap : ν {y | pi y = c} = (ν.map pi) {c} := by
      rw [Measure.map_apply hpi_meas (measurableSet_singleton c)]
      rfl
    have hμ : (ν.map pi) {c} = (muC c : ℝ≥0∞) := by
      dsimp [muC]
      exact (ENNReal.coe_toNNReal hfin).symm
    calc
      ν {y | pi y = c} = (ν.map pi) {c} := hmap
      _ = (muC c : ℝ≥0∞) := hμ
      _ = 0 := by rw [hμ0]; simp
  have hESCnull' : ν {y | ∃ c : C, muC c = 0 ∧ pi y = c} = 0 := by
    classical
    let T := {c : C // muC c = 0}
    haveI : Fintype T := by
      dsimp [T]
      infer_instance
    have hEq : {y | ∃ c : C, muC c = 0 ∧ pi y = c} = ⋃ c : T, {y | pi y = c.1} := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨c, hμ, hπ⟩
        exact Set.mem_iUnion.mpr ⟨⟨c, hμ⟩, hπ⟩
      · intro hy
        rcases (Set.mem_iUnion.mp hy) with ⟨c, hπ⟩
        exact ⟨c.1, c.2, hπ⟩
    have hle : ν (⋃ c : T, {y | pi y = c.1}) ≤ ∑ c ∈ (Finset.univ : Finset T), ν {y | pi y = c.1} := by
      simpa using (measure_biUnion_finset_le (Finset.univ : Finset T) (fun c : T => {y | pi y = c.1}))
    have hsum : (∑ c ∈ (Finset.univ : Finset T), ν {y | pi y = c.1}) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      exact hnullcell c.1 c.2
    rw [hEq]
    apply le_antisymm
    · calc
        ν (⋃ c : T, {y | pi y = c.1}) ≤ ∑ c ∈ (Finset.univ : Finset T), ν {y | pi y = c.1} := hle
        _ = 0 := hsum
    · exact bot_le
  have hESCBnull : ν ESCB = 0 := by
    have hle : ν (ESC ∪ {y | ∃ c : C, muC c = 0 ∧ pi y = c}) ≤ ν ESC + ν {y | ∃ c : C, muC c = 0 ∧ pi y = c} := by
      exact measure_union_le _ _
    apply le_antisymm
    · calc
        ν ESCB ≤ ν ESC + ν {y | ∃ c : C, muC c = 0 ∧ pi y = c} := by
                simpa [ESCB] using hle
        _ = 0 := by rw [hESCnull, hESCnull']; simp
    · exact bot_le
  let goodYB : Set Ω := {ω | ∀ j : Fin N, Y j ω ∉ ESCB}
  -- samples with no ESCB-hit are μ0-free and ESC-free
  have hgoodYB_μ0free (ω : Ω) (hgood : ω ∈ goodYB) : ∀ c : C, muC c = 0 → WcntY ω c = 0 := by
    intro c hμ0
    -- WcntY ω c > 0 means some sample hits cell c
    by_contra hc0
    have hpos : 0 < WcntY ω c := Nat.pos_of_ne_zero hc0
    have hhit : ∃ j : Fin N, XsY j ω = c := by
      have hc : 0 < (Finset.univ.filter (fun j : Fin N => XsY j ω = c)).card := by
        simpa [WcntY, Discret1.countVec] using hpos
      have hnon := Finset.card_pos.mp hc
      rcases hnon with ⟨j, hj⟩
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    rcases hhit with ⟨j, hj⟩
    have hYj : Y j ω ∉ ESCB := by
      exact hgood j
    have hpiY : pi (Y j ω) = c := by
      dsimp [XsY] at hj
      exact hj
    exact hYj (by
      dsimp [ESCB]
      exact Or.inr ⟨c, hμ0, hpiY⟩)
  have hgoodYB_ESCFree (ω : Ω) (hgood : ω ∈ goodYB) : ∀ j : Fin N, Y j ω ∉ ESC := by
    intro j
    intro hj
    exact hgood j (by
      dsimp [ESCB]
      exact Or.inl hj)
  -- probability of the Y-events equals that of the Y'-events (a.e. equality of samples)
  have hprobGY (G : C → ℕ) (hG : G ∈ Cov1) :
      (P {ω | (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G}).toReal ≤ costG G := by
    have heq : P {ω | (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G} =
        P {ω | (∑ j : Fin N, gTN G (Xs j ω)) ≤ tTtilde G} := by
      apply MeasureTheory.measure_congr
      filter_upwards [hYeq_all] with ω hω
      apply propext
      constructor
      · intro h
        have hmem : (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G := by
          exact (Set.mem_setOf_eq.mp h)
        have hsum : (∑ j : Fin N, gTN G (Xs j ω)) = (∑ j : Fin N, gTN G (pi (Y j ω))) := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [Xs]
          rw [hω j]
        exact (Set.mem_setOf_eq.mpr (by rw [hsum]; exact hmem))
      · intro h
        have hmem : (∑ j : Fin N, gTN G (Xs j ω)) ≤ tTtilde G := by
          exact (Set.mem_setOf_eq.mp h)
        have hsum : (∑ j : Fin N, gTN G (Xs j ω)) = (∑ j : Fin N, gTN G (pi (Y j ω))) := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [Xs]
          rw [hω j]
        exact (Set.mem_setOf_eq.mpr (by rwa [hsum] at hmem))
    rw [heq]
    exact hprobG G hG
  have hw_id (G : C → ℕ) : costG G = Multi.wCost (Multi.eN N) (fun c : C => (muC c : ℝ)) G := by
    dsimp [costG]
    unfold Discret2.costG Multi.wCost Multi.eN
    rfl
  -- total probability of the Y-events over the cover
  have hprobSumY : (∑ G ∈ Cov1, (P {ω | (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G}).toReal) ≤ (2 : ℝ)⁻¹ := by
    calc
      (∑ G ∈ Cov1, (P {ω | (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G}).toReal)
          ≤ ∑ G ∈ Cov1, costG G := Finset.sum_le_sum (by intro G hG; exact hprobGY G hG)
      _ = Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov1 := by
              unfold Multi.mTotalCost
              apply Finset.sum_congr rfl
              intro G hG
              exact hw_id G
      _ ≤ (2 : ℝ)⁻¹ := hCov1cost
  -- escape indicator and threshold
  let gEsc : 𝕋 → ℝ≥0 := fun y => if y ∈ ESCB then (1 : ℝ≥0) else 0
  have hgEsc_meas : Measurable gEsc := by
    have hfun : gEsc = ESCB.indicator (fun _ : 𝕋 => (1 : ℝ≥0)) := by
      funext y
      by_cases h : y ∈ ESCB <;> simp [gEsc, h]
    rw [hfun]
    exact Measurable.indicator measurable_const hESCBmeas
  let tEsc : ℝ≥0 := (N : ℝ≥0)⁻¹
  have htEsc : 0 < tEsc := by
    dsimp [tEsc]
    exact inv_pos.mpr (by exact_mod_cast N_pos)
  -- count of samples in ESCB
  have hZesc_real (ω : Ω) : ((Z N Y gEsc ω : ℝ≥0) : ℝ)
      = ((Finset.univ.filter (fun j : Fin N => Y j ω ∈ ESCB)).card : ℝ) / (N : ℝ) := by
    let cnt : ℕ := (Finset.univ.filter (fun j : Fin N => Y j ω ∈ ESCB)).card
    have hcoeff : (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (N : ℝ)⁻¹ := by norm_num [one_div]
    have hcntsum : (∑ j : Fin N, (gEsc (Y j ω) : ℝ)) = (cnt : ℝ) := by
      calc
        (∑ j : Fin N, (gEsc (Y j ω) : ℝ)) = ∑ j : Fin N, (if Y j ω ∈ ESCB then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases h : Y j ω ∈ ESCB <;> simp [gEsc, h]
        _ = (cnt : ℝ) := by
                dsimp [cnt]
                exact_mod_cast (Finset.sum_boole (s := (Finset.univ : Finset (Fin N)))
                  (p := fun j : Fin N => Y j ω ∈ ESCB))
    calc
      ((Z N Y gEsc ω : ℝ≥0) : ℝ) = ((N : ℝ)⁻¹) * (∑ j : Fin N, (gEsc (Y j ω) : ℝ)) := by
              unfold Z
              rw [NNReal.coe_mul, NNReal.coe_sum]
              simp [hcoeff]
      _ = ((N : ℝ)⁻¹) * (cnt : ℝ) := by rw [hcntsum]
      _ = (cnt : ℝ) / (N : ℝ) := by field_simp
      _ = ((Finset.univ.filter (fun j : Fin N => Y j ω ∈ ESCB)).card : ℝ) / (N : ℝ) := by
              dsimp [cnt]
  have hesc_event_eq (ω : Ω) : (tEsc ≤ Z N Y gEsc ω) ↔ ∃ j : Fin N, Y j ω ∈ ESCB := by
    have hZ := hZesc_real ω
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N_pos
    constructor
    · intro h
      have hr : (tEsc : ℝ) ≤ ((Z N Y gEsc ω : ℝ≥0) : ℝ) := by exact_mod_cast h
      rw [hZ] at hr
      have h1 := (le_div_iff₀ hN0).mp hr
      have ht : (tEsc : ℝ) = (N : ℝ)⁻¹ := by dsimp [tEsc]; norm_num [one_div]
      rw [ht, inv_mul_cancel₀ (ne_of_gt hN0)] at h1
      have hpos : 0 < (Finset.univ.filter (fun j : Fin N => Y j ω ∈ ESCB)).card := by exact_mod_cast h1
      have hnon := Finset.card_pos.mp hpos
      rcases hnon with ⟨j, hj⟩
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    · intro h
      rcases h with ⟨j, hj⟩
      have hjm : j ∈ Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      have hc1 : 1 ≤ (Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).card := by
        have hnon : (Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).Nonempty := ⟨j, hjm⟩
        have hpos : 0 < (Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).card := Finset.card_pos.mpr hnon
        omega
      have hr : (tEsc : ℝ) ≤ ((Z N Y gEsc ω : ℝ≥0) : ℝ) := by
        rw [hZ]
        have h1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).card : ℝ) := by exact_mod_cast hc1
        have h2 : (N : ℝ)⁻¹ ≤ ((Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).card : ℝ) / (N : ℝ) := by
          have h3 : (N : ℝ)⁻¹ * (N : ℝ) ≤ ((Finset.univ.filter (fun j0 : Fin N => Y j0 ω ∈ ESCB)).card : ℝ) := by
            rw [inv_mul_cancel₀ (ne_of_gt hN0)]
            simpa using h1
          exact (le_div_iff₀ hN0).mpr h3
        simpa [tEsc] using h2
      exact_mod_cast hr

  -- sample law of ESCB-events
  have hYlaw_esc (j : Fin N) : P {ω | Y j ω ∈ ESCB} = ν ESCB := by
    exact (Y_law_ν j).measure_eq (p := fun y : 𝕋 => y ∈ ESCB) hESCBmeas
  let escB : Set Ω := {ω | ∃ j : Fin N, Y j ω ∈ ESCB}
  have hPescB : P escB = 0 := by
    have hsub : escB ⊆ ⋃ j : Fin N, {ω | Y j ω ∈ ESCB} := by
      intro ω hω
      rcases (Set.mem_setOf_eq.mp hω) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have hle : P (⋃ j : Fin N, {ω | Y j ω ∈ ESCB}) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω | Y j ω ∈ ESCB} := by
      simpa using (measure_biUnion_finset_le (Finset.univ : Finset (Fin N))
        (fun j : Fin N => {ω | Y j ω ∈ ESCB}))
    have hsum : (∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω | Y j ω ∈ ESCB}) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hYlaw_esc j, hESCBnull]
    apply le_antisymm
    · calc
        P escB ≤ P (⋃ j : Fin N, {ω | Y j ω ∈ ESCB}) := measure_mono hsub
        _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin N)), P {ω | Y j ω ∈ ESCB} := hle
        _ = 0 := hsum
    · exact bot_le
  -- the pair data
  let gOf (G : C → ℕ) (hG : G ∈ Cov1) : C → ℝ≥0 := fun c => ⟨- (N : ℝ) * gTN G c, hneg0 G hG c⟩
  have hgOf_meas (G : C → ℕ) (hG : G ∈ Cov1) : Measurable (gOf G hG) := by
    exact measurable_of_finite_domain (α := 𝕋) (β := ℝ≥0) (gOf G hG)
  let gG (G : C → ℕ) (hG : G ∈ Cov1) : 𝕋 → ℝ≥0 := fun y => gOf G hG (pi y)
  have hgG_meas (G : C → ℕ) (hG : G ∈ Cov1) : Measurable (gG G hG) := by
    dsimp [gG]
    exact (hgOf_meas G hG).comp hpi_meas
  let tG (G : C → ℕ) (hG : G ∈ Cov1) : ℝ≥0 := ⟨- tTtilde G, by linarith [htT_nonpos G hG]⟩
  have htG_pos (G : C → ℕ) (hG : G ∈ Cov1) : 0 < tG G hG := by
    dsimp [tG]
    change (0 : ℝ) < - tTtilde G
    linarith [htT_neg G hG]
  let tGpos (G : C → ℕ) (hG : G ∈ Cov1) : {t : ℝ≥0 | t > 0} := ⟨tG G hG, htG_pos G hG⟩
  have hZg (G : C → ℕ) (hG : G ∈ Cov1) (ω : Ω) :
      ((Z N Y (gG G hG) ω : ℝ≥0) : ℝ) = - (∑ j : Fin N, gTN G (pi (Y j ω))) := by
    have hcoeff : (((N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (N : ℝ)⁻¹ := by norm_num [one_div]
    have hsum (c : C) : ((gOf G hG c : ℝ≥0) : ℝ) = - (N : ℝ) * gTN G c := rfl
    have hbody : (∑ j : Fin N, ((gG G hG (Y j ω) : ℝ≥0) : ℝ))
        = - (N : ℝ) * (∑ j : Fin N, gTN G (pi (Y j ω))) := by
      calc
        (∑ j : Fin N, ((gG G hG (Y j ω) : ℝ≥0) : ℝ)) = ∑ j : Fin N, (- (N : ℝ) * gTN G (pi (Y j ω))) := by
                apply Finset.sum_congr rfl
                intro j hj
                dsimp [gG]
                exact hsum (pi (Y j ω))
        _ = - (N : ℝ) * (∑ j : Fin N, gTN G (pi (Y j ω))) := by
                rw [← Finset.mul_sum]
    have hZval : ((Z N Y (gG G hG) ω : ℝ≥0) : ℝ) = ((N : ℝ)⁻¹) * (∑ j : Fin N, ((gG G hG (Y j ω) : ℝ≥0) : ℝ)) := by
      unfold Z
      rw [NNReal.coe_mul, NNReal.coe_sum]
      simp [hcoeff]
    calc
      ((Z N Y (gG G hG) ω : ℝ≥0) : ℝ) = ((N : ℝ)⁻¹) * (∑ j : Fin N, ((gG G hG (Y j ω) : ℝ≥0) : ℝ)) := hZval
      _ = ((N : ℝ)⁻¹) * (- (N : ℝ) * (∑ j : Fin N, gTN G (pi (Y j ω)))) := by rw [hbody]
      _ = - (∑ j : Fin N, gTN G (pi (Y j ω))) := by
              have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N_pos)
              field_simp [hNne]
  -- the pair event coincides with the H_G(Y) event
  have hev_set_eq (G : C → ℕ) (hG : G ∈ Cov1) :
      {ω | (tG G hG : ℝ≥0) ≤ Z N Y (gG G hG) ω} = {ω | (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G} := by
    ext ω
    have hZ := hZg G hG ω
    have ht : ((tG G hG : ℝ≥0) : ℝ) = - tTtilde G := rfl
    constructor
    · intro h
      have hr : ((tG G hG : ℝ≥0) : ℝ) ≤ ((Z N Y (gG G hG) ω : ℝ≥0) : ℝ) := by exact_mod_cast h
      rw [ht, hZ] at hr
      exact (Set.mem_setOf_eq.mpr (by linarith))
    · intro h
      have hle : (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G := by
        exact (Set.mem_setOf_eq.mp h)
      have hr : - tTtilde G ≤ - (∑ j : Fin N, gTN G (pi (Y j ω))) := by
        linarith
      have hr' : ((tG G hG : ℝ≥0) : ℝ) ≤ ((Z N Y (gG G hG) ω : ℝ≥0) : ℝ) := by
        rw [ht, hZ]
        exact hr
      exact (Set.mem_setOf_eq.mpr hr')

  -- the E-condition set
  let Eset : Set Ω := {ω | (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) ≥ L3v * muinf}
  -- event function on pairs
  let Pev (p : {g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) : ℝ≥0∞ :=
    P {ω | (p.2 : ℝ≥0) ≤ Z N Y (p.1 : 𝕋 → ℝ≥0) ω}
  let pairG (a : {G : C → ℕ // G ∈ Cov1}) : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) :=
    (⟨gG a.1 a.2, hgG_meas a.1 a.2⟩, tGpos a.1 a.2)
  let Pairs : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) := (Cov1.attach.image pairG)
  let EscPair : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) := (⟨gEsc, hgEsc_meas⟩, ⟨tEsc, htEsc⟩)
  let AllPairs : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) := insert EscPair Pairs
  have hpair_event (a : {G : C → ℕ // G ∈ Cov1}) :
      {ω | (pairG a).2 ≤ Z N Y (pairG a).1 ω} = {ω | (∑ j : Fin N, gTN a.1 (pi (Y j ω))) ≤ tTtilde a.1} := by
    have h := hev_set_eq a.1 a.2
    dsimp [pairG]
    simpa [pairG] using h
  have hEsc_event : {ω | EscPair.2 ≤ Z N Y EscPair.1 ω} = escB := by
    dsimp [EscPair]
    ext ω
    exact hesc_event_eq ω
  have hPevG (a : {G : C → ℕ // G ∈ Cov1}) : (Pev (pairG a)).toReal ≤ costG a.1 := by
    have heq : Pev (pairG a) = P {ω | (∑ j : Fin N, gTN a.1 (pi (Y j ω))) ≤ tTtilde a.1} := by
      dsimp [Pev]
      rw [hpair_event a]
    rw [heq]
    exact hprobGY a.1 a.2
  have hPevEsc : (Pev EscPair).toReal = 0 := by
    have heq : Pev EscPair = P escB := by
      dsimp [Pev]
      rw [hEsc_event]
    rw [heq]
    rw [hPescB]
    simp
  -- containment of the events over the cover (union over the subtype of Cov1)
  have hchainS (ω : Ω) (hω : ω ∈ Eset) :
      ω ∈ (⋃ a : {G : C → ℕ // G ∈ Cov1}, {ω | (∑ j : Fin N, gTN a.1 (pi (Y j ω))) ≤ tTtilde a.1}) ∪ escB := by
    by_cases hnotesc : ω ∉ escB
    · left
      have hgood : ∀ j : Fin N, Y j ω ∉ ESCB := by
        intro j hj
        exact hnotesc ⟨j, hj⟩
      have hgoodY' : ω ∈ goodY := by
        intro j
        exact hgoodYB_ESCFree ω (by intro j0; exact hgood j0) j
      have hbig : (2 * Multi.Lw) ≤ supSY ω := hE_big ω (by simpa [Eset] using hω)
      have hm := hmemY ω hgoodY' hbig
      have hμ0free : ∀ c : C, muC c = 0 → WcntY ω c = 0 := by
        intro c hμ0
        exact hgoodYB_μ0free ω (by intro j0; exact hgood j0) c hμ0
      rcases (hCov1cover (WcntY ω) hm hμ0free) with ⟨G, hGCov1, hsub⟩
      refine Set.mem_iUnion.mpr ⟨⟨G, hGCov1⟩, ?_⟩
      have hsumc : (∑ j : Fin N, gTN G (pi (Y j ω))) = ∑ c : C, (WcntY ω c : ℝ) * gTN G c := by
        have hre := Discret2.sum_coord (t := fun j : Fin N => XsY j ω) (f := fun c : C => gTN G c)
        dsimp [XsY] at hre
        simpa [XsY, WcntY] using hre
      have hle2 : (∑ c : C, (WcntY ω c : ℝ) * gTN G c) ≤ tTtilde G := by
        have hgw : ∀ c : C, G c ≤ WcntY ω c := hsub
        dsimp [tTtilde, gTN]
        exact Discret2.sum_gT_le N muC G (WcntY ω) hgw (fun c hc => hGtrim G hGCov1 c hc)
      have hev0 : (∑ j : Fin N, gTN G (pi (Y j ω))) ≤ tTtilde G := by
        rw [hsumc]
        simpa using hle2
      simpa using (Set.mem_setOf_eq.mpr hev0)
    · right
      simpa [escB] using hnotesc
  -- final containment
  have hcontFinal : Eset ⊆ ⋃ c ∈ AllPairs, {ω | c.2 ≤ Z N Y c.1 ω} := by
    intro ω hω
    have hc := hchainS ω hω
    rcases hc with hc | hc
    · rcases (Set.mem_iUnion.mp hc) with ⟨a, hev⟩
      let c : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) := pairG a
      have hcPairs : c ∈ Pairs := by
        dsimp [c, Pairs]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_attach _ a, rfl⟩
      have hcAll : c ∈ AllPairs := by
        dsimp [AllPairs]
        exact Finset.mem_insert_of_mem hcPairs
      have hev' : ω ∈ {ω | (c.2 : ℝ≥0) ≤ Z N Y (c.1 : 𝕋 → ℝ≥0) ω} := by
        have hset : {ω | (c.2 : ℝ≥0) ≤ Z N Y (c.1 : 𝕋 → ℝ≥0) ω} = {ω | (∑ j : Fin N, gTN a.1 (pi (Y j ω))) ≤ tTtilde a.1} := by
          dsimp [c]
          simpa using (hpair_event a)
        rwa [hset]
      exact Set.mem_biUnion (by simpa using hcAll) hev'
    · have hev' : ω ∈ {ω | (EscPair.2 : ℝ≥0) ≤ Z N Y (EscPair.1 : 𝕋 → ℝ≥0) ω} := by
        rwa [hEsc_event]
      have hcAll : EscPair ∈ AllPairs := by simp [AllPairs]
      exact Set.mem_biUnion (by simpa using hcAll) hev'
  -- probability bound (real)
  have hprobSumY' : (∑ G ∈ Cov1, costG G) ≤ (2 : ℝ)⁻¹ := by
    calc
      (∑ G ∈ Cov1, costG G) = Multi.mTotalCost (Multi.eN N) (fun c : C => (muC c : ℝ)) Cov1 := by
              unfold Multi.mTotalCost
              apply Finset.sum_congr rfl
              intro G hG
              exact hw_id G
      _ ≤ (2 : ℝ)⁻¹ := hCov1cost
  have hPevEsc0 : (Pev EscPair).toReal = 0 := hPevEsc
  have hsumreal : (∑ c ∈ AllPairs, (Pev c).toReal) ≤ (2 : ℝ)⁻¹ := by
    have hsplit : (∑ c ∈ AllPairs, (Pev c).toReal) ≤ (Pev EscPair).toReal + (∑ c ∈ Pairs, (Pev c).toReal) := by
      dsimp [AllPairs]
      by_cases hmem : EscPair ∈ Pairs
      · have hEq : insert EscPair Pairs = Pairs := Finset.insert_eq_of_mem hmem
        rw [hEq]
        have hnn : 0 ≤ (Pev EscPair).toReal := ENNReal.toReal_nonneg
        linarith
      · rw [Finset.sum_insert (by simpa using hmem)]
    have hpairs : (∑ c ∈ Pairs, (Pev c).toReal) ≤ ∑ G ∈ Cov1, costG G := by
      have hnonneg (p : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0})) : 0 ≤ (Pev p).toReal := ENNReal.toReal_nonneg
      calc
        (∑ c ∈ Pairs, (Pev c).toReal) ≤ ∑ a ∈ Cov1.attach, (Pev (pairG a)).toReal := by
                dsimp [Pairs]
                exact MultiCost.sum_le_sum_image (s := Cov1.attach) (f := pairG) (g := fun p => (Pev p).toReal)
                  (by intro y hy; exact hnonneg y)
        _ ≤ ∑ a ∈ Cov1.attach, costG a.1 := Finset.sum_le_sum (by intro a ha; exact hPevG a)
        _ = ∑ G ∈ Cov1, costG G := by rw [Finset.sum_attach]
    have hto : (∑ c ∈ AllPairs, (Pev c).toReal) ≤ (Pev EscPair).toReal + (∑ G ∈ Cov1, costG G) := by
      have h1 := hsplit
      have h2 := hpairs
      linarith
    calc
      (∑ c ∈ AllPairs, (Pev c).toReal) ≤ (Pev EscPair).toReal + (∑ G ∈ Cov1, costG G) := hto
      _ ≤ (2 : ℝ)⁻¹ := by
              rw [hPevEsc0]
              linarith [hprobSumY']
  have hlt_top (n : ℕ) : (n : ℝ≥0∞) < ∞ := by
    exact (ENNReal.coe_lt_top : ((n : ℝ≥0) : ℝ≥0∞) < ∞)
  have hsumrealAll : (∑ c : AllPairs, (Pev c.val).toReal) ≤ (2 : ℝ)⁻¹ := by
    have hcc := Finset.sum_coe_sort (AllPairs) (fun p : ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}) => (Pev p).toReal)
    rw [hcc]
    exact hsumreal
  have hfiniteAll (c : ↥AllPairs) : Pev c.val ≠ ∞ := by
    have hle : Pev c.val ≤ P Set.univ := by
      dsimp [Pev]
      exact measure_mono (by intro ω hω; trivial)
    rw [hPprob.measure_univ] at hle
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
  have hXfin : (∑ c : AllPairs, Pev c.val) ≠ ∞ := by
    have hle1 : (∑ c : AllPairs, Pev c.val) ≤ (AllPairs.card : ℝ≥0∞) := by
      calc
        (∑ c : AllPairs, Pev c.val) ≤ ∑ c : AllPairs, (1 : ℝ≥0∞) := by
                exact Finset.sum_le_sum (by intro c hc; exact (by
                  have h1 : Pev c.val ≤ 1 := by
                    dsimp [Pev]
                    have h : P {ω | (c.val.2 : ℝ≥0) ≤ Z N Y (c.val.1 : 𝕋 → ℝ≥0) ω} ≤ P Set.univ := measure_mono (by intro ω hω; trivial)
                    rw [hPprob.measure_univ] at h
                    simpa using h
                  simpa using h1))
        _ = (AllPairs.card : ℝ≥0∞) := by simp
    exact ne_of_lt (lt_of_le_of_lt hle1 (hlt_top (AllPairs.card)))
  -- final answer
  refine ⟨AllPairs, ?_, ?_⟩
  · -- containment
    intro ω hω
    have hzm : (zm ω : ℝ≥0∞) ≥ L3v * muinf := by
      have hle : ((⨆ f ∈ 𝓕, Z N Y (↑f) ω : ℝ≥0) : ℝ≥0∞) ≤ (zm ω : ℝ≥0∞) := by
        exact ENNReal.coe_le_coe.mpr (hsupR_le ω)
      exact le_trans hω hle
    have hw : ω ∈ Eset := by
      have hz' : (⨆ f ∈ 𝓕, (Z N Y f ω : ℝ≥0∞)) ≥ L3v * muinf := by
        rw [hsup_inf ω, hzm_sup ω]
        exact hzm
      simpa [Eset] using hz'
    exact hcontFinal hw
  · -- probability
    have hXfinG : (∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω}) ≠ ∞ := by
      have hle1 : (∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω}) ≤ (AllPairs.card : ℝ≥0∞) := by
        calc
          (∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω}) ≤ ∑ c : AllPairs, (1 : ℝ≥0∞) := by
                  exact Finset.sum_le_sum (by intro c hc; exact (by
                    have h : P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ P Set.univ := measure_mono (by intro ω hω; trivial)
                    rw [hPprob.measure_univ] at h
                    simpa using h))
          _ = (AllPairs.card : ℝ≥0∞) := by simp
      exact ne_of_lt (lt_of_le_of_lt hle1 (hlt_top (AllPairs.card)))
    have hXto : (∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω}).toReal =
        ∑ c : AllPairs, (Pev c.val).toReal := by
      have hsets : (fun c : ↥AllPairs => P {ω | c.val.2 ≤ Z N Y c.val.1 ω}) = (fun c : ↥AllPairs => Pev c.val) := by
        funext c
        rfl
      rw [hsets]
      calc
        (∑ c : AllPairs, Pev c.val).toReal = (∑ c ∈ (Finset.univ : Finset ↥AllPairs), Pev c.val).toReal := by rfl
        _ = ∑ c ∈ (Finset.univ : Finset ↥AllPairs), (Pev c.val).toReal := by
                rw [ENNReal.toReal_sum]
                intro c hc
                exact hfiniteAll c
        _ = ∑ c : AllPairs, (Pev c.val).toReal := by rfl
    calc
      (∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω})
          = ENNReal.ofReal ((∑ c : AllPairs, P {ω | c.val.2 ≤ Z N Y c.val.1 ω}).toReal) := by
              exact (ENNReal.ofReal_toReal hXfinG).symm
      _ ≤ ENNReal.ofReal ((2 : ℝ)⁻¹) := by
              rw [hXto]
              exact ENNReal.ofReal_le_ofReal hsumrealAll
      _ ≤ (2 : ℝ≥0∞)⁻¹ := by
              have hid : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
                rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
                rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
              rw [hid]

end SupremumOfSelectorProcesses
