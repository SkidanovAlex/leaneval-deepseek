import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLC6Core.measurable_apply_section
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLRelCross.SL3famDefs
import Submission.Work.EKLRelCross.SL3criterion

/-!
# `Work.EKLRelCross.covariance_bad_measurable`

Measurability of the set of *bad* points for the leafwise covariance relation (EKL (4)):

`{p : X₃ × ℝ³ | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
   ¬ ∃ c ≠ 0, c ≠ ⊤, ν (aDiag p.2 • p.1) = c • (ν p.1).map (conj (aDiag p.2))}`.

This is the measurability input to the Fubini argument that upgrades covariance at Lebesgue-a.e. `t`
to covariance at every `t`.

## Proof

* `p ↦ aDiag p.2 • p.1` is continuous, and `p ↦ aDiag p.2 * g * (aDiag p.2)⁻¹` is jointly
  continuous.
* Replace `ν` off the conull set `X'` by `0`: `leafwiseOff ν X'`.  The replaced family is
  weakly measurable and finite on compact sets (`hL.measurable`/`hL.radon`), so
  `Work.EKLC6Core.measurable_apply_section` applied to the two families
  `p ↦ leafwiseOff ν X' p.1` and `p ↦ leafwiseOff ν X' (aDiag p.2 • p.1)` shows that
  `p ↦ (conjPush ν' p) A` and `p ↦ (diagPush ν' p) A` are measurable for every Borel `A`.
* On the good set `p.1 ∈ X'`, `aDiag p.2 • p.1 ∈ X'` both measures are non-zero
  (`hL.normalised` gives mass `1` on `Box1 U`) and finite on compacts, so the countable
  criterion `Work.EKLRelCross.SL3Criterion` characterises proportionality
  (`Work.EKLRelCross.SL3criterion`).
* The criterion is a countable Boolean combination of the evaluations above, hence the bad set is
  measurable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option maxHeartbeats 800000

noncomputable section
namespace Work.EKLRelCross

theorem continuous_aDiag_ekl : Continuous fun t : Fin 3 → ℝ => aDiag t := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun t : Fin 3 → ℝ => Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3))) ?_ ?_
  · apply continuous_matrix
    intro k l
    simp only [Matrix.diagonal_apply]
    by_cases hkl : k = l
    · simp only [hkl, if_true]; fun_prop
    · simp only [hkl, if_false]; exact continuous_const

theorem continuous_aDiag_smul_pair : Continuous fun p : X3 × (Fin 3 → ℝ) => aDiag p.2 • p.1 :=
  continuous_smul.comp ((continuous_aDiag_ekl.comp continuous_snd).prodMk continuous_fst)

theorem continuous_conj_aDiag (t : Fin 3 → ℝ) :
    Continuous fun g : SL3 => aDiag t * g * (aDiag t)⁻¹ :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem continuous_conj_aDiag_fam :
    Continuous fun q : (X3 × (Fin 3 → ℝ)) × SL3 => aDiag q.1.2 * q.2 * (aDiag q.1.2)⁻¹ := by
  have h1 : Continuous fun q : (X3 × (Fin 3 → ℝ)) × SL3 => aDiag q.1.2 :=
    continuous_aDiag_ekl.comp (continuous_snd.comp continuous_fst)
  have h2 : Continuous fun q : (X3 × (Fin 3 → ℝ)) × SL3 => (aDiag q.1.2)⁻¹ := by
    have h : (fun q : (X3 × (Fin 3 → ℝ)) × SL3 => (aDiag q.1.2)⁻¹)
        = fun q => aDiag (-(q.1.2)) := by
      funext q
      exact inv_eq_of_mul_eq_one_right (aDiag_mul_neg q.1.2)
    rw [h]
    exact continuous_aDiag_ekl.comp (continuous_neg.comp (continuous_snd.comp continuous_fst))
  exact (h1.mul continuous_snd).mul h2

noncomputable def leafwiseOff (ν : X3 → Measure SL3) (X' : Set X3) : X3 → Measure SL3 := by
  classical
  exact fun x => if x ∈ X' then ν x else 0

def conjPush (ν : X3 → Measure SL3) (p : X3 × (Fin 3 → ℝ)) : Measure SL3 :=
  (ν p.1).map (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)

def diagPush (ν : X3 → Measure SL3) (p : X3 × (Fin 3 → ℝ)) : Measure SL3 :=
  ν (aDiag p.2 • p.1)

lemma isFiniteMeasureOnCompacts_map_conj {ν : Measure SL3} (hν : IsFiniteMeasureOnCompacts ν)
    (t : Fin 3 → ℝ) :
    IsFiniteMeasureOnCompacts (ν.map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)) := by
  refine ⟨fun K hK => ?_⟩
  have hpre : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' K
      = (fun g : SL3 => (aDiag t)⁻¹ * g * aDiag t) '' K := by
    ext g
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hg
      refine ⟨aDiag t * g * (aDiag t)⁻¹, hg, ?_⟩
      group
    · rintro ⟨k, hk, rfl⟩
      have hcomp : aDiag t * ((aDiag t)⁻¹ * k * aDiag t) * (aDiag t)⁻¹ = k := by group
      rwa [hcomp]
  rw [Measure.map_apply (continuous_conj_aDiag t).measurable hK.measurableSet, hpre]
  exact hν.lt_top_of_isCompact (hK.image ((continuous_const.mul continuous_id).mul continuous_const))


theorem covariance_bad_measurable {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    MeasurableSet {p : Work.EKLContract.X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧
      Work.EKLContract.aDiag p.2 • p.1 ∈ X' ∧
      ¬ ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (Work.EKLContract.aDiag p.2 • p.1) = c • (ν p.1).map (fun g : Work.EKLContract.SL3 => Work.EKLContract.aDiag p.2 * g * (Work.EKLContract.aDiag p.2)⁻¹)} := by
  show MeasurableSet {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
      ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ diagPush ν p = c • conjPush ν p}
  classical
  set ν' : X3 → Measure SL3 := leafwiseOff ν X' with hν'
  have hν'weak : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable fun x : X3 => ∫ g, f g ∂(ν' x) := by
    intro f
    have hpt : (fun x : X3 => ∫ g, f g ∂(ν' x))
        = fun x => if x ∈ X' then (∫ g, f g ∂(ν x)) else 0 := by
      funext x
      by_cases hx : x ∈ X'
      · simp only [hν', leafwiseOff, if_pos hx]
      · simp only [hν', leafwiseOff, if_neg hx]
        exact integral_zero_measure f
    rw [hpt]
    exact Measurable.piecewise hL.meas_dom (hL.measurable f) measurable_const
  have hν'fin : ∀ x : X3, IsFiniteMeasureOnCompacts (ν' x) := by
    intro x
    by_cases hx : x ∈ X'
    · have hx' : ν' x = ν x := by simp only [hν', leafwiseOff]; rw [if_pos hx]
      rw [hx']; exact hL.radon x hx
    · have hx' : ν' x = 0 := by simp only [hν', leafwiseOff]; rw [if_neg hx]
      rw [hx']; exact ⟨fun K hK => by simp⟩
  have heval2 : ∀ A : Set SL3, MeasurableSet A →
      Measurable fun p : X3 × (Fin 3 → ℝ) => (diagPush ν' p) A := by
    intro A hA
    have hκ : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        Measurable fun p : X3 × (Fin 3 → ℝ) => ∫ g, f g ∂(diagPush ν' p) := by
      intro f
      have hcomp : (fun p : X3 × (Fin 3 → ℝ) => ∫ g, f g ∂(diagPush ν' p))
          = (fun x : X3 => ∫ g, f g ∂(ν' x))
            ∘ (fun p : X3 × (Fin 3 → ℝ) => aDiag p.2 • p.1) := rfl
      rw [hcomp]
      exact (hν'weak f).comp continuous_aDiag_smul_pair.measurable
    have hT : MeasurableSet {q : (X3 × (Fin 3 → ℝ)) × SL3 | q.2 ∈ A} :=
      hA.preimage continuous_snd.measurable
    have hsec := Work.EKLC6Core.measurable_apply_section
      (κ := fun p : X3 × (Fin 3 → ℝ) => diagPush ν' p) hκ
      (fun p => hν'fin (aDiag p.2 • p.1)) hT
    have hset : ∀ p : X3 × (Fin 3 → ℝ),
        Prod.mk p ⁻¹' ({q : (X3 × (Fin 3 → ℝ)) × SL3 | q.2 ∈ A} : Set _) = A := by
      intro p; ext g; simp
    convert hsec using 1
    funext p
    rw [hset p]
  have heval1 : ∀ A : Set SL3, MeasurableSet A →
      Measurable fun p : X3 × (Fin 3 → ℝ) => (conjPush ν' p) A := by
    intro A hA
    have hκ : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        Measurable fun p : X3 × (Fin 3 → ℝ) => ∫ g, f g ∂(ν' p.1) :=
      fun f => (hν'weak f).comp measurable_fst
    have hT : MeasurableSet {q : (X3 × (Fin 3 → ℝ)) × SL3 |
        aDiag q.1.2 * q.2 * (aDiag q.1.2)⁻¹ ∈ A} :=
      hA.preimage continuous_conj_aDiag_fam.measurable
    have hsec := Work.EKLC6Core.measurable_apply_section
      (κ := fun p : X3 × (Fin 3 → ℝ) => ν' p.1) hκ (fun p => hν'fin p.1) hT
    have hset : ∀ p : X3 × (Fin 3 → ℝ),
        Prod.mk p ⁻¹' ({q : (X3 × (Fin 3 → ℝ)) × SL3 |
          aDiag q.1.2 * q.2 * (aDiag q.1.2)⁻¹ ∈ A} : Set _)
        = (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹) ⁻¹' A := by
      intro p; ext g; simp
    convert hsec using 1
    funext p
    rw [hset p, show conjPush ν' p = (ν' p.1).map (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)
      from rfl, Measure.map_apply (continuous_conj_aDiag p.2).measurable hA]
  have hne1 : ∀ p : X3 × (Fin 3 → ℝ), p.1 ∈ X' → conjPush ν' p ≠ 0 := by
    intro p h1 hzero
    have hBox : MeasurableSet (Box1 U) := Work.EKLC6Core.measurableSet_box1 hU
    have hA : MeasurableSet ((fun g : SL3 => (aDiag p.2)⁻¹ * g * aDiag p.2) ⁻¹' Box1 U) :=
      hBox.preimage (((continuous_const.mul continuous_id).mul continuous_const).measurable)
    have hval : (conjPush ν' p) ((fun g : SL3 => (aDiag p.2)⁻¹ * g * aDiag p.2) ⁻¹' Box1 U)
        = ν' p.1 (Box1 U) := by
      rw [show conjPush ν' p = (ν' p.1).map (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)
        from rfl, Measure.map_apply (continuous_conj_aDiag p.2).measurable hA]
      congr 1
      ext g
      simp only [Set.mem_preimage]
      have hg : (aDiag p.2)⁻¹ * (aDiag p.2 * g * (aDiag p.2)⁻¹) * aDiag p.2 = g := by group
      rw [hg]
    have hν1 : ν' p.1 = ν p.1 := by simp only [hν', leafwiseOff]; rw [if_pos h1]
    have hval1 : (conjPush ν' p) ((fun g : SL3 => (aDiag p.2)⁻¹ * g * aDiag p.2) ⁻¹' Box1 U) = 1 := by
      rw [hval, hν1, hL.normalised p.1 h1]
    rw [hzero] at hval1
    exact (zero_ne_one : (0 : ℝ≥0∞) ≠ 1) (by simpa using hval1)
  have hne2 : ∀ p : X3 × (Fin 3 → ℝ), aDiag p.2 • p.1 ∈ X' → diagPush ν' p ≠ 0 := by
    intro p h2 hzero
    have hval : (diagPush ν' p) (Box1 U) = 1 := by
      rw [show diagPush ν' p = ν' (aDiag p.2 • p.1) from rfl]
      have hν2 : ν' (aDiag p.2 • p.1) = ν (aDiag p.2 • p.1) := by
        simp only [hν', leafwiseOff]; rw [if_pos h2]
      rw [hν2, hL.normalised (aDiag p.2 • p.1) h2]
    rw [hzero] at hval
    exact (zero_ne_one : (0 : ℝ≥0∞) ≠ 1) (by simpa using hval)
  have hcrit : ∀ p : X3 × (Fin 3 → ℝ), p.1 ∈ X' → aDiag p.2 • p.1 ∈ X' →
      ((∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ diagPush ν p = c • conjPush ν p) ↔
        SL3Criterion (conjPush ν' p) (diagPush ν' p)) := by
    intro p h1 h2
    have hν1 : ν' p.1 = ν p.1 := by simp only [hν', leafwiseOff]; rw [if_pos h1]
    have hν2 : ν' (aDiag p.2 • p.1) = ν (aDiag p.2 • p.1) := by
      simp only [hν', leafwiseOff]; rw [if_pos h2]
    have hp1 : conjPush ν' p = conjPush ν p := by simp only [conjPush, hν1]
    have hp2 : diagPush ν' p = diagPush ν p := by simp only [diagPush, hν2]
    rw [← hp1, ← hp2]
    refine SL3criterion ?_ ?_ ?_ ?_
    · exact isFiniteMeasureOnCompacts_map_conj (hν'fin p.1) p.2
    · exact hν'fin (aDiag p.2 • p.1)
    · exact hne1 p h1
    · exact hne2 p h2
  have hZeq : {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
        ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ diagPush ν p = c • conjPush ν p}
      = {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X'} ∩
        {p : X3 × (Fin 3 → ℝ) | ¬ SL3Criterion (conjPush ν' p) (diagPush ν' p)} := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun hc => h3 ((hcrit p h1 h2).mpr hc)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun hP => h3 ((hcrit p h1 h2).mp hP)⟩
  rw [hZeq]
  refine MeasurableSet.inter ?_ ?_
  · exact (hL.meas_dom.preimage measurable_fst).inter
      (hL.meas_dom.preimage continuous_aDiag_smul_pair.measurable)
  · have hunion : MeasurableSet (⋃ p₀ : ℕ × Finset ℕ,
        ({p : X3 × (Fin 3 → ℝ) | 0 < (conjPush ν' p) (SL3fam p₀)} ∩
          ({p : X3 × (Fin 3 → ℝ) | 0 < (diagPush ν' p) (SL3fam p₀)} ∩
            (⋂ p' : ℕ × Finset ℕ,
              ({p : X3 × (Fin 3 → ℝ) |
                  (diagPush ν' p) (SL3fam p') * (conjPush ν' p) (SL3fam p₀) ≤
                    (conjPush ν' p) (SL3fam p') * (diagPush ν' p) (SL3fam p₀)} ∩
               {p : X3 × (Fin 3 → ℝ) |
                  (conjPush ν' p) (SL3fam p') * (diagPush ν' p) (SL3fam p₀) ≤
                    (diagPush ν' p) (SL3fam p') * (conjPush ν' p) (SL3fam p₀)}))))) := by
      refine MeasurableSet.iUnion fun p₀ => ?_
      refine MeasurableSet.inter (measurableSet_lt measurable_const (heval1 _ (measurableSet_SL3fam p₀))) ?_
      refine MeasurableSet.inter (measurableSet_lt measurable_const (heval2 _ (measurableSet_SL3fam p₀))) ?_
      refine MeasurableSet.iInter fun p' => ?_
      exact (measurableSet_le ((heval2 _ (measurableSet_SL3fam p')).mul
          (heval1 _ (measurableSet_SL3fam p₀)))
        ((heval1 _ (measurableSet_SL3fam p')).mul (heval2 _ (measurableSet_SL3fam p₀)))).inter
        (measurableSet_le ((heval1 _ (measurableSet_SL3fam p')).mul
          (heval2 _ (measurableSet_SL3fam p₀)))
        ((heval2 _ (measurableSet_SL3fam p')).mul (heval1 _ (measurableSet_SL3fam p₀))))
    have hcritmeas : MeasurableSet {p : X3 × (Fin 3 → ℝ) |
        SL3Criterion (conjPush ν' p) (diagPush ν' p)} := by
      rw [show {p : X3 × (Fin 3 → ℝ) | SL3Criterion (conjPush ν' p) (diagPush ν' p)}
          = (⋃ p₀ : ℕ × Finset ℕ,
        ({p : X3 × (Fin 3 → ℝ) | 0 < (conjPush ν' p) (SL3fam p₀)} ∩
          ({p : X3 × (Fin 3 → ℝ) | 0 < (diagPush ν' p) (SL3fam p₀)} ∩
            (⋂ p' : ℕ × Finset ℕ,
              ({p : X3 × (Fin 3 → ℝ) |
                  (diagPush ν' p) (SL3fam p') * (conjPush ν' p) (SL3fam p₀) ≤
                    (conjPush ν' p) (SL3fam p') * (diagPush ν' p) (SL3fam p₀)} ∩
               {p : X3 × (Fin 3 → ℝ) |
                  (conjPush ν' p) (SL3fam p') * (diagPush ν' p) (SL3fam p₀) ≤
                    (diagPush ν' p) (SL3fam p') * (conjPush ν' p) (SL3fam p₀)}))))) from by
        ext p
        simp only [SL3Criterion, Set.mem_iUnion, Set.mem_iInter, Set.mem_inter_iff,
          Set.mem_ofPred_eq, le_antisymm_iff]]
      exact hunion
    exact hcritmeas.compl

end Work.EKLRelCross
