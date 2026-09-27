import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.shapeAvg_lintegral_eq
import Submission.Work.EKLC6Core.HcondSigFree.HcondSig_le_lintegral_atomInfo_mp
import Submission.Work.EKLC6Core.growth_le_HcondSig_mp
import Submission.Work.EKLC6Core.HaarPlan
import Submission.Work.EKLC6Core.negMulLog_le_sum_mul_negLog
import Submission.Work.EKLC6Core.lintegral_ofReal_shift_sub_le_ae
import Submission.Work.EKLRelCross.leafwise_exists
import Submission.Work.EKLComp.prove_X3

/-!
# Clash-free copy of `Work.EKLC6Core.HcondSig_le_ofReal_haar_uij`

This file contains the *identical* proof of the colleague-proved Pisa 7.9/7.55 bound for the root
group `Uij`, under a globally distinct name.  It exists only because the proved files
`Work.EKLC6Core.HcondSig_le_ofReal_haar_uij` and `Work.EKLC6Core.fiber_leafwise_uij` both declare a
theorem named `uij_contraction`, so they cannot be imported into one module; here that helper is
renamed `haarUij_contraction` and the main theorem `HcondSig_le_ofReal_haar_uij_cf`.  The
mathematics is entirely due to the prover of `HcondSig_le_ofReal_haar_uij`.
-/

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-! ## Lebesgue (Haar) measure on the root group `U_ij` -/

/-- Lebesgue measure on `U_ij`, pushed forward from `ℝ` by `s ↦ u_ij hij s`. -/
noncomputable def mUij {i j : Fin 3} (hij : i ≠ j) : Measure SL3 :=
  Measure.map (fun s : ℝ => uij hij s) volume

lemma mUij_apply {i j : Fin 3} (hij : i ≠ j) {E : Set SL3} (hE : MeasurableSet E) :
    mUij hij E = volume {s : ℝ | uij hij s ∈ E} :=
  Measure.map_apply (Work.EKLContract.Lemmas.horoUij_cont hij).measurable hE

lemma measurableSet_Uij {i j : Fin 3} (hij : i ≠ j) :
    MeasurableSet (Uij hij : Set SL3) :=
  (Work.EKLContract.Lemmas.horoUij_isClosed hij).measurableSet

lemma coe_uij_entry {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    (Work.EKLContract.toMat (uij hij s)) i j = s := by
  rw [Work.EKLContract.Lemmas.horoUij_toMat hij s]
  simp [Matrix.add_apply, Matrix.one_apply_ne hij]

/-- `mUij` is carried by `U_ij`. -/
lemma mUij_compl {i j : Fin 3} (hij : i ≠ j) : mUij hij (Uij hij : Set SL3)ᶜ = 0 := by
  rw [mUij_apply hij (measurableSet_Uij hij).compl]
  have h : {s : ℝ | uij hij s ∈ (Uij hij : Set SL3)ᶜ} = ∅ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact Subgroup.subset_closure (Set.mem_range_self s)
  rw [h, measure_empty]

/-- `mUij` is positive on any open set meeting `U_ij`. -/
lemma mUij_pos_of_open {i j : Fin 3} (hij : i ≠ j) {O : Set SL3} (hO : IsOpen O)
    (hOu : ∃ v ∈ Uij hij, v ∈ O) : 0 < mUij hij O := by
  obtain ⟨v, hvU, hvO⟩ := hOu
  obtain ⟨s₀, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij v).mp hvU
  rw [mUij_apply hij hO.measurableSet]
  have hcont : Continuous (fun s : ℝ => uij hij s) := Work.EKLContract.Lemmas.horoUij_cont hij
  have hopen : IsOpen {s : ℝ | uij hij s ∈ O} := hO.preimage hcont
  have hmem : s₀ ∈ {s : ℝ | uij hij s ∈ O} := hvO
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s₀ hmem
  have hsub : Set.Ioo (s₀ - ε) (s₀ + ε) ⊆ {s : ℝ | uij hij s ∈ O} := by
    intro s hs
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rw [Set.mem_Ioo] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  calc 0 < volume (Set.Ioo (s₀ - ε) (s₀ + ε)) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
    _ ≤ volume {s : ℝ | uij hij s ∈ O} := measure_mono hsub

/-- The entrywise box `{|g k l| ≤ C}` is closed, hence Borel. -/
lemma measurableSet_entryBox (C : ℝ) :
    MeasurableSet {g : SL3 | ∀ k l : Fin 3, |(Work.EKLContract.toMat g) k l| ≤ C} := by
  have hclosed : IsClosed {g : SL3 | ∀ k l : Fin 3, |(Work.EKLContract.toMat g) k l| ≤ C} := by
    rw [show {g : SL3 | ∀ k l : Fin 3, |(Work.EKLContract.toMat g) k l| ≤ C}
        = ⋂ (p : Fin 3 × Fin 3), {g : SL3 | |(Work.EKLContract.toMat g) p.1 p.2| ≤ C} from by
      ext g; simp [Set.mem_iInter]]
    exact isClosed_iInter fun p => isClosed_le (by fun_prop) continuous_const
  exact hclosed.measurableSet

/-- `mUij` is finite on entrywise-bounded sets. -/
lemma mUij_lt_top_of_entryBounded {i j : Fin 3} (hij : i ≠ j) {E : Set SL3}
    {C : ℝ} (hC : 0 ≤ C)
    (hE : E ⊆ {g : SL3 | ∀ k l : Fin 3, |(Work.EKLContract.toMat g) k l| ≤ C}) :
    mUij hij E < ⊤ := by
  calc mUij hij E
      ≤ mUij hij {g : SL3 | ∀ k l : Fin 3, |(Work.EKLContract.toMat g) k l| ≤ C} :=
        measure_mono hE
    _ = volume {s : ℝ | uij hij s ∈ {g : SL3 | ∀ k l : Fin 3,
            |(Work.EKLContract.toMat g) k l| ≤ C}} :=
        mUij_apply hij (measurableSet_entryBox C)
    _ ≤ volume (Set.Icc (-C) C) := by
        refine measure_mono ?_
        intro s hs
        rw [Set.mem_ofPred_eq] at hs
        have h1 : |s| ≤ C := by
          have := hs i j
          rwa [coe_uij_entry hij s] at this
        exact abs_le.mp h1
    _ = ENNReal.ofReal (C - (-C)) := Real.volume_Icc
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Lebesgue measure scales by `c` under `x ↦ c * x` (`c > 0`). -/
lemma volume_image_mul_pos (c : ℝ) (hc : 0 < c) {S : Set ℝ} (hS : MeasurableSet S) :
    volume ((fun x : ℝ => c * x) '' S) = ENNReal.ofReal c * volume S := by
  have h1 : (fun x : ℝ => c * x) '' S = (fun x : ℝ => c⁻¹ * x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage]; show c⁻¹ * (c * y) ∈ S
      rw [inv_mul_cancel_left₀ (ne_of_gt hc)]; exact hy
    · intro hx
      refine ⟨c⁻¹ * x, hx, ?_⟩
      show c * (c⁻¹ * x) = x
      rw [mul_inv_cancel_left₀ (ne_of_gt hc)]
  rw [h1, ← Measure.map_apply (measurable_const_mul c⁻¹) hS,
    Real.map_volume_mul_left (inv_ne_zero (ne_of_gt hc)), Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [inv_inv, abs_of_pos hc]

lemma hexp_sub {i j : Fin 3} (t : Fin 3 → ℝ) :
    Real.exp (t i - t j) = (Real.exp (t j - t i))⁻¹ := by
  rw [← Real.exp_neg]; congr 1; ring

lemma exp_mul_inv {i j : Fin 3} (t : Fin 3 → ℝ) (x : ℝ) :
    Real.exp (t i - t j) * (Real.exp (t j - t i) * x) = x := by
  rw [← mul_assoc, ← Real.exp_add]
  have h : (t i - t j) + (t j - t i) = 0 := by ring
  rw [h, Real.exp_zero, one_mul]

/-- Pisa (7.55a): conjugation by `aDiag (-t)` scales the Haar measure `mUij` by
`exp (t j - t i)`. -/
lemma mUij_conjBy_neg {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) {E : Set SL3}
    (hE : MeasurableSet E) (hEU : E ⊆ (Uij hij : Set SL3)) :
    mUij hij (conjBy (-t) E)
      = ENNReal.ofReal (Real.exp (t j - t i)) * mUij hij E := by
  have hmeas : MeasurableSet (conjBy (-t) E) := by
    have h : conjBy (-t) E = (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' E := by
      ext h
      simp only [conjBy, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨g, hg, rfl⟩
        show aDiag t * (aDiag (-t) * g * (aDiag (-t))⁻¹) * (aDiag t)⁻¹ ∈ E
        convert hg using 2
        rw [aDiag_neg_eq_inv]; group
      · intro hh
        exact ⟨aDiag t * h * (aDiag t)⁻¹, hh, by rw [aDiag_neg_eq_inv]; group⟩
    rw [h]; exact hE.preimage (by fun_prop)
  have hS : MeasurableSet {s : ℝ | uij hij s ∈ E} :=
    hE.preimage (Work.EKLContract.Lemmas.horoUij_cont hij).measurable
  have hkey1 : ∀ s : ℝ, uij hij s ∈ conjBy (-t) E ↔
      (aDiag t * uij hij s * (aDiag t)⁻¹) ∈ E := by
    intro s
    rw [conjBy, Set.mem_image]
    constructor
    · rintro ⟨g, hgE, hg⟩
      have hgs : g = aDiag t * uij hij s * (aDiag t)⁻¹ := by rw [← hg, aDiag_neg_eq_inv]; group
      rwa [hgs] at hgE
    · intro hE'
      refine ⟨aDiag t * uij hij s * (aDiag t)⁻¹, hE', ?_⟩
      rw [aDiag_neg_eq_inv]; group
  have hset : {s : ℝ | uij hij s ∈ conjBy (-t) E}
      = (fun x : ℝ => Real.exp (t j - t i) * x) '' {s : ℝ | uij hij s ∈ E} := by
    ext s
    rw [Set.mem_ofPred_eq, hkey1 s, Set.mem_image]
    constructor
    · intro hs
      rw [Work.EKLContract.Lemmas.horoUij_aDiag_conj t hij s, hexp_sub t] at hs
      refine ⟨(Real.exp (t j - t i))⁻¹ * s, ?_, ?_⟩
      · show uij hij ((Real.exp (t j - t i))⁻¹ * s) ∈ E
        exact hs
      · show Real.exp (t j - t i) * ((Real.exp (t j - t i))⁻¹ * s) = s
        rw [mul_inv_cancel_left₀ (Real.exp_ne_zero _)]
    · rintro ⟨x, hx, rfl⟩
      rw [Work.EKLContract.Lemmas.horoUij_aDiag_conj t hij (Real.exp (t j - t i) * x)]
      rw [exp_mul_inv t x]
      exact hx
  rw [mUij_apply hij hmeas, mUij_apply hij hE, hset,
    volume_image_mul_pos _ (Real.exp_pos _) hS]

/-! ## The leaf-wise system for the root group `U_ij` -/

/-- `U_ij` is a horospherical subgroup. -/
lemma isHoro_Uij_of_ne {i j : Fin 3} (hij : i ≠ j) : IsHoro (Uij hij) :=
  Work.EKLContract.Lemmas.isHoro_Uij hij

/-- If `t i < t j` then `aDiag t` contracts `U_ij` to the identity. -/
lemma haarUij_contraction {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (hlt : t i < t j) :
    ∀ u ∈ Uij hij,
      Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1) := by
  intro u hu
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij u).mp hu
  exact Work.EKLContract.Lemmas.horoUij_tendsto_conj t hij hlt s

/-- For an invariant probability measure, the root group `U_ij` admits a leaf-wise system
(Pisa Thm 6.3). -/
lemma exists_leafwise_uij {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ)
    (hlt : t i < t j)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => aDiag t • x) μ μ) :
    ∃ (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
      (X' : Set Work.EKLContract.X3), IsLeafwise μ (Uij hij) ν X' :=
  Work.EKLRelCross.leafwise_exists Work.EKLComp.prove_X3 μ (Uij hij)
    (isHoro_Uij_of_ne hij) t hmp (haarUij_contraction hij t hlt)


/-! ## Haar-measure infrastructure for the root group `U_ij` (Pisa 7.9 / §7.55) -/

section HaarUij

variable {i j : Fin 3}

/-- `mUij` is finite on compact subsets of `SL₃(ℝ)`. -/
lemma mUij_isFiniteMeasureOnCompacts (hij : i ≠ j) :
    IsFiniteMeasureOnCompacts (mUij hij) := by
  refine ⟨fun K hK => ?_⟩
  have hbdd : ∀ k l : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, |(toMat g) k l| ≤ C := by
    intro k l
    have hcont : Continuous fun g : SL3 => (toMat g) k l := by
      change Continuous fun g : SL3 => ((g : Matrix (Fin 3) (Fin 3) ℝ)) k l
      fun_prop
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun g hg => ?_⟩
    have h1 := hC g hg
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  choose C hC0 hC using hbdd
  set D : ℝ := ∑ k : Fin 3, ∑ l : Fin 3, C k l with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hC0 k l
  refine lt_of_le_of_lt (measure_mono ?_)
    (mUij_lt_top_of_entryBounded hij hD0
      (E := {g : SL3 | ∀ k l : Fin 3, |(toMat g) k l| ≤ D}) fun g hg => hg)
  intro g hg k l
  have h1 : C k l ≤ ∑ l' : Fin 3, C k l' :=
    Finset.single_le_sum (fun l' _ => hC0 k l') (Finset.mem_univ l)
  have h2 : (∑ l' : Fin 3, C k l') ≤ ∑ k' : Fin 3, ∑ l' : Fin 3, C k' l' :=
    Finset.single_le_sum (fun k' _ => Finset.sum_nonneg fun l' _ => hC0 k' l')
      (Finset.mem_univ k)
  exact le_trans (hC k l g hg) (le_trans h1 h2)

/-- Right translation by an element of `U_ij` preserves `mUij`. -/
lemma mUij_mul_uij (hij : i ≠ j) {E : Set SL3} (hE : MeasurableSet E) (s : ℝ) :
    mUij hij ((fun e : SL3 => e * uij hij s) '' E) = mUij hij E := by
  have hset : (fun e : SL3 => e * uij hij s) '' E
      = (fun g : SL3 => g * (uij hij s)⁻¹) ⁻¹' E := by
    ext g
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa using he
    · intro hg
      exact ⟨g * (uij hij s)⁻¹, hg, by simp⟩
  have hmeas : MeasurableSet ((fun e : SL3 => e * uij hij s) '' E) := by
    rw [hset]
    exact hE.preimage (Continuous.mul continuous_id continuous_const).measurable
  have hset2 : {t : ℝ | uij hij t ∈ (fun e : SL3 => e * uij hij s) '' E}
      = (fun t : ℝ => -s + t) ⁻¹' {u : ℝ | uij hij u ∈ E} := by
    ext t
    show uij hij t ∈ (fun e : SL3 => e * uij hij s) '' E ↔ uij hij (-s + t) ∈ E
    rw [hset]
    show uij hij t * (uij hij s)⁻¹ ∈ E ↔ uij hij (-s + t) ∈ E
    have h1 : uij hij t * (uij hij s)⁻¹ = uij hij (-s + t) := by
      simp only [Work.EKLContract.uij]
      rw [Matrix.SpecialLinearGroup.transvection_inv,
        ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      ring
    rw [h1]
  rw [mUij_apply hij hmeas, mUij_apply hij hE, hset2, measure_preimage_add]

/-- Right translation by an element of `U_ij` preserves `mUij` (membership form). -/
lemma mUij_mul_mem_Uij (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) {E : Set SL3}
    (hE : MeasurableSet E) :
    mUij hij ((fun e : SL3 => e * g) '' E) = mUij hij E := by
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij g).mp hg
  exact mUij_mul_uij hij hE s

/-- The Haar measure of the shape of the `A`-atom at a point of the base set is positive. -/
lemma mUij_shape_pos {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) {y : X3} (hyZ : y ∈ Z) :
    0 < mUij hij (shape A (Uij hij) y) := by
  obtain ⟨O, hOopen, hOeq⟩ := (hplq.2.2.2 y hyZ).2.2.1
  have hyatom : y ∈ atom A y := by
    rw [Work.EKLContract.atom, Set.mem_sInter]
    rintro s ⟨-, hs⟩
    exact hs
  have h1shape : (1 : SL3) ∈ shape A (Uij hij) y :=
    ⟨(Uij hij).one_mem, by rw [one_smul]; exact hyatom⟩
  have h1O : (1 : SL3) ∈ O := by rw [hOeq] at h1shape; exact h1shape.1
  have hUc : MeasurableSet ((Uij hij : Set SL3)) :=
    (Work.EKLContract.Lemmas.horoUij_isClosed hij).measurableSet
  have hsplit : mUij hij (O ∩ (Uij hij : Set SL3)) + mUij hij (O \ (Uij hij : Set SL3))
      = mUij hij O := measure_inter_add_diff O hUc
  have hcompl : mUij hij (O \ (Uij hij : Set SL3)) = 0 :=
    measure_mono_null (fun z hz => hz.2) (mUij_compl hij)
  have hval : mUij hij O = mUij hij (O ∩ (Uij hij : Set SL3)) := by
    rw [← hsplit, hcompl, add_zero]
  rw [hOeq, ← hval]
  exact mUij_pos_of_open hij hOopen ⟨1, (Uij hij).one_mem, h1O⟩

/-- **The key geometric comparison.**  If `y` lies in the `B`-atom of `x` (`B = comap (aDiag t ·) A`),
then the Haar measure of the part of the pull-back shape of `x` lying over the `A`-atom of `y`
dominates the Haar measure of the shape of the `A`-atom of `y`. -/
lemma mUij_shape_atom_le {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ)
    (hdec : MeasurableSpace.comap (fun z : X3 => aDiag t • z) A ≤ A)
    {x y : X3} (hx : aDiag t • x ∈ Z) (hyZ : y ∈ Z)
    (hy : y ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x) :
    mUij hij (shape A (Uij hij) y) ≤
      mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) (Uij hij) x
        ∩ {u : SL3 | u • x ∈ atom A y}) := by
  classical
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  set B : MeasurableSpace X3 := MeasurableSpace.comap (fun z : X3 => aDiag t • z) A with hBdef
  have hyT : aDiag t • y ∈ atom A (aDiag t • x) := by
    have h := hcsg_atom_comap (fun z : X3 => aDiag t • z) A x
    rw [hBdef] at hy
    rw [h] at hy
    exact hy
  obtain ⟨u, huU, hug⟩ := (hplq.2.2.2 (aDiag t • x) hx).2.1 hyT
  set g : SL3 := aDiag (-t) * u * aDiag t with hgdef
  have hgU : g ∈ Uij hij := by
    have h : aDiag (-t) * u * (aDiag (-t))⁻¹ ∈ Uij hij := hU.2.1 (-t) u huU
    rw [aDiag_neg_eq_inv] at h
    rw [hgdef]
    simpa [aDiag_neg_eq_inv] using h
  have hug' : u • (aDiag t • x) = aDiag t • y := hug
  have hgx : g • x = y := by
    rw [hgdef]
    calc (aDiag (-t) * u * aDiag t) • x
        = aDiag (-t) • (u • (aDiag t • x)) := by simp only [mul_smul]
      _ = aDiag (-t) • (aDiag t • y) := by rw [hug']
      _ = y := by rw [← mul_smul, aDiag_neg_eq_inv, inv_mul_cancel, one_smul]
  have hyA : atom A y ⊆ atom B x := by
    have h1 : atom A y ⊆ atom B y := hcsg_atom_mono (m := B) (A := A) hdec y
    have h2 : atom B y = atom B x := hcsg_atom_eq_of_mem hy
    rw [h2] at h1
    exact h1
  have hsub : (fun e : SL3 => e * g) '' (shape A (Uij hij) y) ⊆
      shape B (Uij hij) x ∩ {u : SL3 | u • x ∈ atom A y} := by
    rintro w ⟨v, hvE, rfl⟩
    have hvU : v ∈ Uij hij := hvE.1
    have hvy : v • y ∈ atom A y := hvE.2
    have hvx : (v * g) • x = v • y := by rw [mul_smul, hgx]
    refine ⟨⟨(Uij hij).mul_mem hvU hgU, ?_⟩, ?_⟩
    · show (v * g) • x ∈ atom B x
      rw [hvx]; exact hyA hvy
    · show (v * g) • x ∈ atom A y
      rw [hvx]; exact hvy
  have hEmeas : MeasurableSet (shape A (Uij hij) y) := measurableSet_shape hU hplq hyZ
  calc mUij hij (shape A (Uij hij) y)
      = mUij hij ((fun e : SL3 => e * g) '' (shape A (Uij hij) y)) :=
          (mUij_mul_mem_Uij hij hgU hEmeas).symm
    _ ≤ mUij hij (shape B (Uij hij) x ∩ {u : SL3 | u • x ∈ atom A y}) := measure_mono hsub

end HaarUij





/-! ## The Haar surprisal -/

/-- `Φ(x) = log m_U(V_x)`: the logarithm of the Haar measure of the shape of the `A`-atom. -/
noncomputable def hPhi {i j : Fin 3} (hij : i ≠ j) (A : MeasurableSpace X3) (x : X3) : ℝ :=
  Real.log ((mUij hij (shape A (Uij hij) x)).toReal)

/-- `-log (m_U(V_x) / m_U(W_x))`: the Haar version of the pointwise surprisal of the `A`-atom
inside the `B`-atom (`B = comap (aDiag t ·) A`). -/
noncomputable def hsurp {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (A : MeasurableSpace X3)
    (x : X3) : ℝ :=
  Real.log ((mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A)
    (Uij hij) x)).toReal) - hPhi hij A x

@[simp] lemma hsurp_def {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (A : MeasurableSpace X3)
    (x : X3) :
    hsurp hij t A x = Real.log ((mUij hij (shape (MeasurableSpace.comap
      (fun z : X3 => aDiag t • z) A) (Uij hij) x)).toReal) - hPhi hij A x := rfl

/-- The conditional probability of the `k`-th part of a finite partition w.r.t. the pull-back
algebra `comap (aDiag t ·) A`. -/
noncomputable def ceOf {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ)
    (μ : @Measure X3 instMeasurableSpaceX3) (S : Work.EKLRelCross.MSAlg)
    (P : @FinPart X3 instMeasurableSpaceX3) (x : X3) (k : Fin P.n) : ℝ :=
  MeasureTheory.condExp (MeasurableSpace.comap (fun z : X3 => aDiag t • z) S.m) μ
    ((P.parts k).indicator (fun _ => (1 : ℝ))) x

/-- The Haar measure of the shape of an `A`-atom at a point of the base set is finite. -/
lemma mUij_shape_lt_top {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) {y : X3} (hyZ : y ∈ Z) :
    mUij hij (shape A (Uij hij) y) < ⊤ := by
  obtain ⟨C, hC⟩ := (hplq.2.2.2 y hyZ).2.2.2
  have hyatom : y ∈ atom A y := by
    rw [Work.EKLContract.atom, Set.mem_sInter]
    rintro s ⟨-, hs⟩
    exact hs
  have h1 : (1 : SL3) ∈ shape A (Uij hij) y :=
    ⟨(Uij hij).one_mem, by rw [one_smul]; exact hyatom⟩
  refine mUij_lt_top_of_entryBounded hij (le_trans (abs_nonneg _) (hC 1 h1 0 0)) ?_
  intro u hu
  exact hC u hu

/-- The Haar measure of the pull-back shape, by scaling. -/
lemma mass_Wsh_eq {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) :
    mUij hij (Wsh t ⟨A⟩ (Uij hij) x)
      = ENNReal.ofReal (Real.exp (t j - t i)) * mUij hij (shape A (Uij hij) (aDiag t • x)) := by
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  have hshape : Wsh t ⟨A⟩ (Uij hij) x = conjBy (-t) (shape A (Uij hij) (aDiag t • x)) := by
    rw [Wsh_def]
    exact hcsg_shape_comap_eq hU A t x
  rw [hshape]
  exact mUij_conjBy_neg hij t (measurableSet_shape hU hplq hTxZ) (fun u hu => hu.1)

lemma mUij_Wsh_pos {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) : 0 < mUij hij (Wsh t ⟨A⟩ (Uij hij) x) := by
  rw [mass_Wsh_eq hij hplq t hTxZ]
  exact ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    (ne_of_gt (mUij_shape_pos hij hplq hTxZ))

lemma mUij_Wsh_lt_top {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) : mUij hij (Wsh t ⟨A⟩ (Uij hij) x) < ⊤ := by
  rw [mass_Wsh_eq hij hplq t hTxZ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (mUij_shape_lt_top hij hplq hTxZ)

/-- **The Haar scaling identity in logarithmic form.** -/
lemma log_mass_shape_comap {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) :
    Real.log ((mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A)
      (Uij hij) x)).toReal)
      = (t j - t i) + hPhi hij A (aDiag t • x) := by
  show Real.log ((mUij hij (Wsh t ⟨A⟩ (Uij hij) x)).toReal) = _
  rw [mass_Wsh_eq hij hplq t hTxZ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hne : (mUij hij (shape A (Uij hij) (aDiag t • x))).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (mUij_shape_pos hij hplq hTxZ))
      (ne_of_lt (mUij_shape_lt_top hij hplq hTxZ)))
  rw [Real.log_mul (Real.exp_ne_zero _) hne, Real.log_exp, hPhi]

/-- **Monotonicity of the Haar surprisal along the diagonal flow.** -/
lemma hPhi_le {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ)
    (hdec : MeasurableSpace.comap (fun z : X3 => aDiag t • z) A ≤ A)
    {x : X3} (hxZ : x ∈ Z) (hTxZ : aDiag t • x ∈ Z) :
    hPhi hij A x ≤ (t j - t i) + hPhi hij A (aDiag t • x) := by
  have hsub : shape A (Uij hij) x
      ⊆ shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) (Uij hij) x :=
    fun u hu => ⟨hu.1, hcsg_atom_mono hdec x hu.2⟩
  have hle : mUij hij (shape A (Uij hij) x)
      ≤ mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) (Uij hij) x) :=
    measure_mono hsub
  have hpos : 0 < (mUij hij (shape A (Uij hij) x)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (mUij_shape_pos hij hplq hxZ))
      (ne_of_lt (mUij_shape_lt_top hij hplq hxZ))
  have htop : mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A)
      (Uij hij) x) ≠ ⊤ :=
    ne_of_lt (mUij_Wsh_lt_top hij hplq t hTxZ)
  have hle' : (mUij hij (shape A (Uij hij) x)).toReal
      ≤ (mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A)
          (Uij hij) x)).toReal := ENNReal.toReal_mono htop hle
  calc hPhi hij A x = Real.log ((mUij hij (shape A (Uij hij) x)).toReal) := rfl
    _ ≤ Real.log ((mUij hij (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A)
          (Uij hij) x)).toReal) := Real.log_le_log hpos hle'
    _ = (t j - t i) + hPhi hij A (aDiag t • x) := log_mass_shape_comap hij hplq t hTxZ

/-- The `B`-shape of `u • x` is the right translate of the `B`-shape of `x` by `u⁻¹`. -/
lemma Wsh_smul_eq {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} (t : Fin 3 → ℝ)
    {x : X3} {u : SL3} (hu : u ∈ Wsh t ⟨A⟩ (Uij hij) x) :
    Wsh t ⟨A⟩ (Uij hij) (u • x) = (fun v : SL3 => v * u⁻¹) '' Wsh t ⟨A⟩ (Uij hij) x := by
  have hatom : atom (betaAlg t ⟨A⟩) (u • x) = atom (betaAlg t ⟨A⟩) x :=
    hcsg_atom_eq_of_mem hu.2
  ext v
  rw [Wsh_def, Wsh_def]
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hv
    refine ⟨v * u, ?_, by simp⟩
    refine ⟨(Uij hij).mul_mem hv.1 hu.1, ?_⟩
    have h1 : (v * u) • x = v • (u • x) := by rw [mul_smul]
    rw [h1, ← hatom]
    exact hv.2
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(Uij hij).mul_mem hw.1 ((Uij hij).inv_mem hu.1), ?_⟩
    have h1 : (w * u⁻¹) • (u • x) = w • x := by
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1, hatom]
    exact hw.2

/-- The Haar measure of the pull-back shape is unchanged along the leaf. -/
lemma mUij_Wsh_of_mem {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) {u : SL3} (hu : u ∈ Wsh t ⟨A⟩ (Uij hij) x) :
    mUij hij (Wsh t ⟨A⟩ (Uij hij) (u • x)) = mUij hij (Wsh t ⟨A⟩ (Uij hij) x) := by
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  have hmeas : MeasurableSet (Wsh t ⟨A⟩ (Uij hij) x) := by
    rw [Wsh_def]
    exact measurableSet_shape hU (isPlaqueAlgebra_betaAlg hU hplq t) hTxZ
  rw [Wsh_smul_eq hij t hu]
  exact mUij_mul_mem_Uij hij ((Uij hij).inv_mem hu.1) hmeas

/-- `hsurp` along the leaf, written in terms of the mass of the pull-back shape. -/
lemma hsurp_of_mem_Wsh {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) {x : X3}
    (hTxZ : aDiag t • x ∈ Z) {u : SL3} (hu : u ∈ Wsh t ⟨A⟩ (Uij hij) x) :
    hsurp hij t A (u • x)
      = Real.log ((mUij hij (Wsh t ⟨A⟩ (Uij hij) x)).toReal) - hPhi hij A (u • x) := by
  rw [hsurp_def]
  have h := mUij_Wsh_of_mem hij hplq t hTxZ hu
  simp only [Wsh_def, betaAlg_def] at h
  rw [h]
  simp only [Wsh_def, betaAlg_def]

/-- The comparison of the mass of the piece over the partition element containing `u • x`. -/
lemma mass_atom_le_mass_Dpat {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ)
    (hdec : MeasurableSpace.comap (fun z : X3 => aDiag t • z) A ≤ A)
    {x : X3} {u : SL3} (hxTZ : aDiag t • x ∈ Z) (huZ : u • x ∈ Z)
    (hu : u ∈ Wsh t ⟨A⟩ (Uij hij) x) {C : Set X3} (hC : MeasurableSet[A] C) (huC : u • x ∈ C) :
    mUij hij (shape A (Uij hij) (u • x))
      ≤ mUij hij (Wsh t ⟨A⟩ (Uij hij) x ∩ {v : SL3 | v • x ∈ C}) := by
  have hmem : u • x ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x := hu.2
  have hsub : atom A (u • x) ⊆ C := hcsg_atom_subset_of_mem hC huC
  refine le_trans (mUij_shape_atom_le hij hplq t hdec hxTZ huZ hmem) (measure_mono ?_)
  rintro v ⟨hvW, hvA⟩
  exact ⟨hvW, hsub hvA⟩

/-- **The main pointwise comparison**: the Haar surprisal dominates `-log τ` on the piece of the
pull-back shape over the partition element containing `u • x`. -/
lemma negLog_tau_le_hsurp {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ)
    (hdec : MeasurableSpace.comap (fun z : X3 => aDiag t • z) A ≤ A)
    {x : X3} {u : SL3} (hxTZ : aDiag t • x ∈ Z) (huZ : u • x ∈ Z)
    (hu : u ∈ Wsh t ⟨A⟩ (Uij hij) x) {C : Set X3} (hC : MeasurableSet[A] C) (huC : u • x ∈ C) :
    - Real.log ((mUij hij (Wsh t ⟨A⟩ (Uij hij) x ∩ {v : SL3 | v • x ∈ C})).toReal
        / (mUij hij (Wsh t ⟨A⟩ (Uij hij) x)).toReal) ≤ hsurp hij t A (u • x) := by
  set W : Set SL3 := Wsh t ⟨A⟩ (Uij hij) x with hWdef
  set a : ℝ≥0∞ := mUij hij (W ∩ {v : SL3 | v • x ∈ C}) with hadef
  set b : ℝ≥0∞ := mUij hij W with hbdef
  have hle : mUij hij (shape A (Uij hij) (u • x)) ≤ a :=
    mass_atom_le_mass_Dpat hij hplq t hdec hxTZ huZ hu hC huC
  have hposV : 0 < mUij hij (shape A (Uij hij) (u • x)) := mUij_shape_pos hij hplq huZ
  have hltV : mUij hij (shape A (Uij hij) (u • x)) < ⊤ := mUij_shape_lt_top hij hplq huZ
  have hltb : b < ⊤ := by rw [hbdef, hWdef]; exact mUij_Wsh_lt_top hij hplq t hxTZ
  have hposb : 0 < b := by rw [hbdef, hWdef]; exact mUij_Wsh_pos hij hplq t hxTZ
  have hposa : 0 < a := lt_of_lt_of_le hposV hle
  have hlta : a < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hltb
  have hlog : Real.log ((mUij hij (shape A (Uij hij) (u • x))).toReal) ≤ Real.log a.toReal :=
    Real.log_le_log (ENNReal.toReal_pos (ne_of_gt hposV) (ne_of_lt hltV))
      (ENNReal.toReal_mono (ne_of_lt hlta) hle)
  have hsurp_eq : hsurp hij t A (u • x)
      = Real.log b.toReal - Real.log ((mUij hij (shape A (Uij hij) (u • x))).toReal) := by
    rw [hsurp_of_mem_Wsh hij hplq t hxTZ hu]
    simp only [hbdef, hWdef, hPhi]
  have hlogdiv : - Real.log (a.toReal / b.toReal) = Real.log b.toReal - Real.log a.toReal := by
    rw [Real.log_div (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposa) (ne_of_lt hlta)))
      (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposb) (ne_of_lt hltb)))]
    ring
  rw [hsurp_eq, hlogdiv]
  linarith

/-- For a finite measurable partition of a set of finite `ν`-measure, the normalized masses sum
to `1`. -/
lemma sum_mass_div_eq_one {α : Type*} [MeasurableSpace α] {ν : Measure α} {ι : Type*}
    [Fintype ι] {W : Set α} {D : ι → Set α} (hD : ∀ i, MeasurableSet (D i))
    (hd : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (hcov : Set.iUnion D = W)
    (hW0 : ν W ≠ 0) (hWtop : ν W ≠ ⊤) :
    ∑ i, (ν (D i)).toReal / (ν W).toReal = 1 := by
  have hle : ∀ i, ν (D i) ≤ ν W := fun i => by
    rw [← hcov]; exact measure_mono (Set.subset_iUnion D i)
  have hfin : ∀ i, ν (D i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hWtop (hle i)
  have hsum : ∑ i, ν (D i) = ν W := by
    have h := measure_biUnion_finset (μ := ν) (s := Finset.univ) (f := D)
      (fun i _ j _ hij => hd i j hij) (fun i _ => hD i)
    have hunion : (⋃ b ∈ (Finset.univ : Finset ι), D b) = Set.iUnion D := by
      ext u
      simp
    rw [hunion, hcov] at h
    exact h.symm
  have hsumR : ∑ i, (ν (D i)).toReal = (ν W).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => hfin i), hsum]
  have hne : (ν W).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hW0 hWtop)
  rw [← Finset.sum_div, hsumR, div_self hne]


section HaarUij2

/-- **The pointwise entropy bound.**  For a.e. `x`, the Shannon entropy of the finite partition `P`
inside its `B`-atom is at most the `ν x`-average of the Haar surprisal over the pull-back shape. -/
lemma hsurp_shapeAvg_bound {i j : Fin 3} (hij : i ≠ j)
    {μ : @Measure X3 instMeasurableSpaceX3} [MeasureTheory.IsProbabilityMeasure μ]
    {Z : Set X3} (S : Work.EKLRelCross.MSAlg) (hplq : IsPlaqueAlgebra (Uij hij) Z S.m)
    (t : Fin 3 → ℝ) (hdec : MeasurableSpace.comap (fun z : X3 => aDiag t • z) S.m ≤ S.m)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uij hij) ν X')
    (hmp : MeasurePreserving (fun z : X3 => aDiag t • z) μ μ) (hZ : μ Zᶜ = 0)
    (P : @FinPart X3 instMeasurableSpaceX3) (hP : partSigma P ≤ S.m) :
    ∀ᵐ x ∂μ, ENNReal.ofReal (∑ k : Fin P.n, Real.negMulLog (ceOf hij t μ S P x k))
      ≤ shapeAvg t S (Uij hij) ν (fun y => ENNReal.ofReal (hsurp hij t S.m y)) x := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have hTZmeas : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hTZ : μ ((fun z : X3 => aDiag t • z) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hTZmeas.compl.nullMeasurableSet, hZ]
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hTZ
  have hratio : ∀ᵐ x ∂μ, ∀ k : Fin P.n, ceOf hij t μ S P x k
      = (ν x (Wsh t S (Uij hij) x ∩ {u : SL3 | u • x ∈ P.parts k})).toReal
        / (ν x (Wsh t S (Uij hij) x)).toReal := by
    rw [Filter.eventually_all]
    intro k
    have h := hcsg_ae_condExp_eq_shape_ratio hU hL hmp (P.measurable k) hplq hZ
    filter_upwards [h] with x hx
    simpa only [ceOf, Wsh_def, betaAlg_def] using hx
  have hleaf : ∀ᵐ x ∂μ, ∀ᵐ u ∂(ν x), u ∈ Wsh t S (Uij hij) x → u • x ∈ Z := by
    have h := ae_Wsh_mem_of_null hU hL t hmp hTZmeas.compl hZ hplq hZ
    filter_upwards [h] with x hx
    filter_upwards [hx] with u hu
    intro huW
    exact Set.notMem_compl_iff.mp (hu huW)
  filter_upwards [hX'ae, hZae, hTZae, hratio, hleaf] with x hxX' hxZ hxTZ hxr hxleaf
  set W : Set SL3 := Wsh t S (Uij hij) x with hWdef
  set D : Fin P.n → Set SL3 := fun k => W ∩ {u : SL3 | u • x ∈ P.parts k} with hDdef
  have hDsub : ∀ k, D k ⊆ Wsh t S (Uij hij) x := fun k u hu => by
    simp only [hDdef, hWdef] at hu
    exact hu.1
  have hWmass_pos : 0 < ν x W := (mass_Wsh (S := S) hU hL hplq t hxX' hxTZ).1
  have hWmass_top : ν x W < ⊤ := (mass_Wsh (S := S) hU hL hplq t hxX' hxTZ).2
  have hWmU_pos : 0 < mUij hij W := by rw [hWdef]; exact mUij_Wsh_pos hij hplq t hxTZ
  have hWmU_top : mUij hij W < ⊤ := by rw [hWdef]; exact mUij_Wsh_lt_top hij hplq t hxTZ
  have hWmeas : MeasurableSet W := by
    rw [hWdef, Wsh_def]
    exact measurableSet_shape hU (isPlaqueAlgebra_betaAlg hU hplq t) hxTZ
  have hDmeas : ∀ k, MeasurableSet (D k) := fun k => by
    rw [hDdef]
    exact hWmeas.inter
      ((P.measurable k).preimage (continuous_id.smul continuous_const).measurable)
  have hDdisj : ∀ k l : Fin P.n, k ≠ l → Disjoint (D k) (D l) := fun k l hkl => by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    simp only [hDdef] at hu1 hu2
    exact (Set.disjoint_left.mp (P.disjoint hkl)) hu1.2 hu2.2
  have hDcov : Set.iUnion D = W := by
    ext u
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hu⟩
      simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at hu
      exact hu.1
    · intro hu
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (by rw [P.cover]; exact Set.mem_univ (u • x))
      exact ⟨k, by simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq]; exact ⟨hu, hk⟩⟩
  have hsum_sigma : ∑ k, ceOf hij t μ S P x k = 1 := by
    rw [Finset.sum_congr rfl (fun k _ => hxr k)]
    exact sum_mass_div_eq_one hDmeas hDdisj hDcov (ne_of_gt hWmass_pos) (ne_of_lt hWmass_top)
  have hsum_tau : ∑ k, (mUij hij (D k)).toReal / (mUij hij W).toReal ≤ 1 := by
    rw [sum_mass_div_eq_one hDmeas hDdisj hDcov (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top)]
  have hsigma_nn : ∀ k, 0 ≤ ceOf hij t μ S P x k := fun k => by rw [hxr k]; positivity
  have htau_nn : ∀ k, 0 ≤ (mUij hij (D k)).toReal / (mUij hij W).toReal := fun k => by positivity
  have hDleW : ∀ k, mUij hij (D k) ≤ mUij hij W := fun k => by
    simp only [hDdef, hWdef]
    exact measure_mono Set.inter_subset_left
  have hDltW : ∀ k, mUij hij (D k) < ⊤ := fun k => lt_of_le_of_lt (hDleW k) hWmU_top
  have htau_pos : ∀ k, ceOf hij t μ S P x k ≠ 0 →
      (mUij hij (D k)).toReal / (mUij hij W).toReal ≠ 0 := by
    intro k hk
    have h1 : (ν x (D k)).toReal / (ν x W).toReal ≠ 0 := by rw [← hxr k]; exact hk
    have h2 : ν x (D k) ≠ 0 := by
      intro h0
      refine h1 ?_
      rw [h0]
      simp
    have hS0 : ν x {u : SL3 | u ∈ Wsh t S (Uij hij) x ∧ u • x ∉ Z} = 0 := by
      have h := MeasureTheory.ae_iff.mp hxleaf
      have hset : {u : SL3 | ¬ (u ∈ Wsh t S (Uij hij) x → u • x ∈ Z)}
          = {u : SL3 | u ∈ Wsh t S (Uij hij) x ∧ u • x ∉ Z} := by
        ext u; simp only [Set.mem_ofPred_eq, Classical.not_imp, Set.mem_setOf_eq]
      rw [← hset]
      exact h
    have h3 : ∃ u ∈ D k, u • x ∈ Z := by
      by_contra hc
      have hc' : ∀ u, u ∈ D k → u • x ∉ Z := by
        intro u hu hux
        exact hc ⟨u, hu, hux⟩
      have hsub : D k ⊆ {u : SL3 | u ∈ Wsh t S (Uij hij) x ∧ u • x ∉ Z} :=
        fun u hu => ⟨hDsub k hu, hc' u hu⟩
      exact h2 (measure_mono_null hsub hS0)
    obtain ⟨u, huD, huZ⟩ := h3
    have huW : u ∈ Wsh t S (Uij hij) x := hDsub k huD
    have huC : u • x ∈ P.parts k := by
      simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at huD
      exact huD.2
    have hC : MeasurableSet[S.m] (P.parts k) := hP _ (hcsg_partSigma_mem P k)
    have hDk : D k = Wsh t S (Uij hij) x ∩ {v : SL3 | v • x ∈ P.parts k} := by
      simp only [hDdef, hWdef]
    have hbnd : mUij hij (shape S.m (Uij hij) (u • x)) ≤ mUij hij (D k) := by
      rw [hDk]
      exact mass_atom_le_mass_Dpat hij hplq t hdec hxTZ huZ huW hC huC
    have hposD : mUij hij (D k) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (mUij_shape_pos hij hplq huZ) hbnd)
    exact div_ne_zero (ne_of_gt (ENNReal.toReal_pos hposD (ne_of_lt (hDltW k))))
      (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top)))
  have htau_le_one : ∀ k, (mUij hij (D k)).toReal / (mUij hij W).toReal ≤ 1 := by
    intro k
    have hle : mUij hij (D k) ≤ mUij hij W := by
      rw [hDdef]
      exact measure_mono Set.inter_subset_left
    have htop : mUij hij W ≠ ⊤ := ne_of_lt hWmU_top
    have h1 : (mUij hij (D k)).toReal ≤ (mUij hij W).toReal := ENNReal.toReal_mono htop hle
    exact (div_le_one (ENNReal.toReal_pos (ne_of_gt hWmU_pos) (ne_of_lt hWmU_top))).mpr h1
  have htau_log_nn : ∀ k, 0 ≤ - Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal) :=
    fun k => neg_nonneg.mpr (Real.log_nonpos (by positivity) (htau_le_one k))
  have hgibbs : ∑ k, Real.negMulLog (ceOf hij t μ S P x k)
      ≤ ∑ k, ceOf hij t μ S P x k
        * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)) :=
    negMulLog_le_sum_mul_negLog _ _ hsigma_nn hsum_sigma htau_nn hsum_tau htau_pos
  have hofReal_ce : ∀ k, ENNReal.ofReal (ceOf hij t μ S P x k)
      = ν x (D k) / (ν x W) := by
    intro k
    rw [hxr k]
    have hDk : D k = W ∩ {u : SL3 | u • x ∈ P.parts k} := by simp only [hDdef]
    rw [hDk]
    exact ofReal_toReal_div_eq
      (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hWmass_top))
      (ne_of_gt hWmass_pos) (ne_of_lt hWmass_top)
  have hterm : ∀ k : Fin P.n, ENNReal.ofReal (ceOf hij t μ S P x k
        * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)))
      ≤ (∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)) / (ν x W) := by
    intro k
    have hkey : ν x (D k) * ENNReal.ofReal
        (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))
        ≤ ∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x) := by
      have hpt : ∀ᵐ u ∂((ν x).restrict (D k)), ENNReal.ofReal
          (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))
          ≤ ENNReal.ofReal (hsurp hij t S.m (u • x)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (hDmeas k),
          MeasureTheory.ae_restrict_of_ae hxleaf] with u huD huWZ
        have huW : u ∈ Wsh t S (Uij hij) x := hDsub k huD
        have huC : u • x ∈ P.parts k := by
          simp only [hDdef, Set.mem_inter_iff, Set.mem_setOf_eq] at huD
          exact huD.2
        exact ENNReal.ofReal_le_ofReal (negLog_tau_le_hsurp hij hplq t hdec hxTZ (huWZ huW)
          huW (hP _ (hcsg_partSigma_mem P k)) huC)
      calc ν x (D k) * ENNReal.ofReal (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))
          = ENNReal.ofReal (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))
              * ν x (D k) := mul_comm _ _
          _ = ∫⁻ u in D k, ENNReal.ofReal
              (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)) ∂(ν x) :=
            (MeasureTheory.setLIntegral_const _ _).symm
          _ ≤ ∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x) :=
            MeasureTheory.lintegral_mono_ae hpt
    calc ENNReal.ofReal (ceOf hij t μ S P x k
          * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)))
        = (ν x (D k) / (ν x W)) * ENNReal.ofReal
            (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)) := by
          rw [ENNReal.ofReal_mul (hsigma_nn k), hofReal_ce k]
      _ = (ν x (D k) * ENNReal.ofReal
            (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))) / (ν x W) := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
      _ ≤ (∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)) / (ν x W) :=
          ENNReal.div_le_div_right hkey _
  have hfibre : ENNReal.ofReal (∑ k, ceOf hij t μ S P x k
        * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)))
      ≤ shapeAvg t S (Uij hij) ν (fun y => ENNReal.ofReal (hsurp hij t S.m y)) x := by
    rw [shapeAvg_def, ← hWdef]
    have hsum : ∑ k, ∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)
        = ∫⁻ u in W, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x) := by
      rw [← hDcov,
        MeasureTheory.lintegral_iUnion (fun k => hDmeas k) (fun i j hij' => hDdisj i j hij')
          (fun u => ENNReal.ofReal (hsurp hij t S.m (u • x))), tsum_fintype]
    calc ENNReal.ofReal (∑ k, ceOf hij t μ S P x k
            * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal)))
        = ∑ k, ENNReal.ofReal (ceOf hij t μ S P x k
            * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))) :=
          ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hsigma_nn k) (htau_log_nn k))
      _ ≤ ∑ k, (∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)) / (ν x W) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (∑ k, ∫⁻ u in D k, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)) / (ν x W) := by
          conv_rhs => rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => ENNReal.div_eq_inv_mul)
      _ = (∫⁻ u in W, ENNReal.ofReal (hsurp hij t S.m (u • x)) ∂(ν x)) / (ν x W) := by
          rw [hsum]
  calc ENNReal.ofReal (∑ k, Real.negMulLog (ceOf hij t μ S P x k))
      ≤ ENNReal.ofReal (∑ k, ceOf hij t μ S P x k
          * (- Real.log ((mUij hij (D k)).toReal / (mUij hij W).toReal))) :=
        ENNReal.ofReal_le_ofReal hgibbs
    _ ≤ shapeAvg t S (Uij hij) ν (fun y => ENNReal.ofReal (hsurp hij t S.m y)) x := hfibre

end HaarUij2


/-! ## Measurability of the shape mass -/

@[simp] lemma hPhi_def {i j : Fin 3} (hij : i ≠ j) (A : MeasurableSpace X3) (x : X3) :
    hPhi hij A x = Real.log ((mUij hij (shape A (Uij hij) x)).toReal) := rfl

/-- Measurability of the Haar mass of the shape, for a σ-algebra generated by a sequence. -/
lemma measurable_shape_mass_of_seq {i j : Fin 3} (hij : i ≠ j) {E : ℕ → Set X3}
    (hE : ∀ n, MeasurableSet (E n)) :
    @Measurable X3 ℝ≥0∞ instMeasurableSpaceX3 ENNReal.measurableSpace
      (fun x : X3 => mUij hij (shape (MeasurableSpace.generateFrom (Set.range E))
        (Uij hij) x)) := by
  have hU : IsClosed ((Uij hij : Subgroup SL3) : Set SL3) :=
    Work.EKLContract.Lemmas.horoUij_isClosed hij
  have hSmeas : MeasurableSet {p : X3 × SL3 |
      p.2 ∈ shape (MeasurableSpace.generateFrom (Set.range E)) (Uij hij) p.1} :=
    measurableSet_shapeGraph hU hE
  have hmain : @Measurable X3 ℝ≥0∞ instMeasurableSpaceX3 ENNReal.measurableSpace
      (fun x : X3 => mUij hij (Prod.mk x ⁻¹' {p : X3 × SL3 |
        p.2 ∈ shape (MeasurableSpace.generateFrom (Set.range E)) (Uij hij) p.1})) :=
    measurable_apply_section (κ := fun _ : X3 => mUij hij)
      (fun f => measurable_const) (fun _ => mUij_isFiniteMeasureOnCompacts hij) hSmeas
  exact hmain

/-- Measurability of the Haar mass of the shape of an `A`-plaque algebra. -/
lemma measurable_mass_shape {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) :
    @Measurable X3 ℝ≥0∞ instMeasurableSpaceX3 ENNReal.measurableSpace
      (fun x : X3 => mUij hij (shape A (Uij hij) x)) := by
  obtain ⟨E, hE, hAgen⟩ := exists_generating_sequence hplq.1 hplq.2.1
  rw [hAgen]
  exact measurable_shape_mass_of_seq hij hE

/-- Measurability of the Haar mass of the shape of the pull-back plaque algebra. -/
lemma measurable_mass_shape_comap {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3}
    {Z : Set X3} (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) :
    @Measurable X3 ℝ≥0∞ instMeasurableSpaceX3 ENNReal.measurableSpace
      (fun x : X3 => mUij hij (shape (MeasurableSpace.comap
        (fun z : X3 => aDiag t • z) A) (Uij hij) x)) := by
  have hA' : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ borel X3 :=
    comap_le_borel_of_le hplq.1 t
  have hcount' : ∃ b' : Set (Set X3), b'.Countable ∧
      MeasurableSpace.comap (fun y : X3 => aDiag t • y) A = MeasurableSpace.generateFrom b' := by
    obtain ⟨b, hbc, hbA⟩ := hplq.2.1
    exact ⟨Set.preimage (fun y : X3 => aDiag t • y) '' b, hbc.image _, by
      rw [hbA, MeasurableSpace.comap_generateFrom]⟩
  obtain ⟨E', hE', hA'gen⟩ := exists_generating_sequence hA' hcount'
  rw [hA'gen]
  exact measurable_shape_mass_of_seq hij hE'

lemma aemeasurable_hPhi {i j : Fin 3} (hij : i ≠ j)
    {μ : @Measure X3 instMeasurableSpaceX3} {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) :
    @AEMeasurable X3 ℝ Real.measurableSpace instMeasurableSpaceX3 (hPhi hij A) μ := by
  have h := (measurable_mass_shape hij hplq).ennreal_toReal
  exact Real.measurable_log.comp_aemeasurable h.aemeasurable

lemma measurable_hsurp {i j : Fin 3} (hij : i ≠ j) {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uij hij) Z A) (t : Fin 3 → ℝ) :
    @Measurable X3 ℝ instMeasurableSpaceX3 Real.measurableSpace (hsurp hij t A) := by
  have h1 := (measurable_mass_shape hij hplq).ennreal_toReal
  have h2 := (measurable_mass_shape_comap hij hplq t).ennreal_toReal
  have h3 := (Real.measurable_log.comp h2).sub (Real.measurable_log.comp h1)
  exact h3

/-! ## The target theorem

The proof (Pisa 7.9/7.55, the convexity bound) proceeds as follows.  Fix a leaf-wise system `ν`
for `U_ij` and a finite partition `P` with `partSigma P ≤ A`, put `B = comap (aDiag t ·) A`,
`σ i x = condExp B μ (1_{P_i}) x` and `τ i x = mUij (Dpart x i) / mUij (Wsh x)`.  Then

* `σ i x = ν x (Dpart x i) / ν x (Wsh x)` (`hcsg_ae_condExp_eq_shape_ratio`), `∑ σ = 1`;
* Gibbs (`negMulLog_le_sum_mul_negLog`) gives `∑ negMulLog (σ i) ≤ ∑ σ i * (-log (τ i)) =: Φ`;
* `Φ ≤ J + h ∘ T - L` where `h y = log (mUij (shape A U y))` and
  `L x = log (mUij (Dpart x (the part of x)))` (Pisa 7.55a: `log mUij (Wsh x) = J + h (T x)`);
* `h ≤ J + h ∘ T` and `h ≤ L`, so Bobylev's/Fatou argument gives `∫⁻ ofReal Φ ≤ ofReal J`
  and `HcondSig ≤ ofReal J`. -/
theorem HcondSig_le_ofReal_haar_uij_cf {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (hlt : t i < t j)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (herg : ∀ s : Set Work.EKLContract.X3, MeasurableSet s →
      (∃ N : Set Work.EKLContract.X3, μ N = 0 ∧ ∀ x : Work.EKLContract.X3, x ∉ N → x ∈ s →
        Work.EKLContract.aDiag t • x ∈ s) → μ s = 0 ∨ μ sᶜ = 0)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A)
      ≤ ENNReal.ofReal (t j - t i) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uij hij) := Work.EKLContract.Lemmas.isHoro_Uij hij
  have hJ : 0 ≤ t j - t i := by linarith
  obtain ⟨ν, X', hL⟩ := exists_leafwise_uij hij t hlt hmp
  have hPhi_ae : AEMeasurable (hPhi hij A) μ := aemeasurable_hPhi hij hplq
  have hsurp_meas : Measurable (hsurp hij t A) := measurable_hsurp hij hplq t
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have hTZmeas : MeasurableSet Z := hplq.1 Z hplq.2.2.1
  have hTZ : μ ((fun z : X3 => aDiag t • z) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hTZmeas.compl.nullMeasurableSet, hZ]
  have hTZae : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hTZ
  have hle_ae : ∀ᵐ x ∂μ, hPhi hij A x ≤ (t j - t i) + hPhi hij A (aDiag t • x) := by
    filter_upwards [hZae, hTZae] with x hxZ hxTZ
    exact hPhi_le hij hplq t hdec hxZ hxTZ
  rw [HcondSig]
  refine iSup_le ?_
  rintro ⟨P, hP⟩
  have hb := hsurp_shapeAvg_bound hij (S := ⟨A⟩) hplq t hdec hL hmp hZ P hP
  change ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ P
      (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A)) ≤ ENNReal.ofReal (t j - t i)
  calc ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ P
        (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A))
      = ENNReal.ofReal (∫ x, ∑ k : Fin P.n,
          Real.negMulLog (ceOf hij t μ ⟨A⟩ P x k) ∂μ) := by
        rw [Hcond]; rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ k : Fin P.n,
          Real.negMulLog (ceOf hij t μ ⟨A⟩ P x k)) ∂μ :=
        ofReal_integral_le_lintegral_ofReal' _
    _ ≤ ∫⁻ x, shapeAvg t ⟨A⟩ (Uij hij) ν
          (fun y => ENNReal.ofReal (hsurp hij t A y)) x ∂μ :=
        lintegral_mono_ae hb
    _ = ∫⁻ x, ENNReal.ofReal (hsurp hij t A x) ∂μ :=
        shapeAvg_lintegral_eq hU hL t hmp (S := ⟨A⟩) hplq hZ _
          hsurp_meas.ennreal_ofReal
    _ = ∫⁻ x, ENNReal.ofReal ((t j - t i) + hPhi hij A (aDiag t • x) - hPhi hij A x) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hZae, hTZae] with x hxZ hxTZ
        rw [hsurp_def, log_mass_shape_comap hij hplq t hxTZ]
    _ ≤ ENNReal.ofReal (t j - t i) :=
        lintegral_ofReal_shift_sub_le_ae hmp hPhi_ae hJ hle_ae


end Work.EKLC6Core
