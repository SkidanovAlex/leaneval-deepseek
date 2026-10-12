import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Sector.fibre_fibState_eq
import Submission.Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre_anyL
import Submission.Work.BoseKinLoc.Sector.potIntegral_fibreSum
import Submission.Work.BoseKinLoc.Sector.slotBox_setIntegral_slotIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. Monotonicity of the boxes at the ambient scale `max L ℓ` -/

/-- `acube L ⊆ acube (max L ℓ)`, with no positivity hypothesis on `L`. -/
private lemma acube_subset_acube_max_gen (L ℓ : ℝ) : acube L ⊆ acube (max L ℓ) := by
  intro y hy m
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ((Submission.BoseGases.mem_acube_iff L y).mp hy m)
  exact Set.mem_Icc.mpr
    ⟨by linarith [h1, le_max_left L ℓ], by linarith [h2, le_max_left L ℓ]⟩

/-- `abox N L ⊆ abox N (max L ℓ)`, with no positivity hypothesis on `L`. -/
private lemma abox_subset_abox_max_gen (N : ℕ) (L ℓ : ℝ) : abox N L ⊆ abox N (max L ℓ) :=
  fun x hx i => acube_subset_acube_max_gen L ℓ (hx i)

/-! ## 2. The support of the slot-`i` kinetic integrand -/

/-- **The slot-`i` kinetic integrand vanishes off `abox N (max L ℓ)`.**  If some slot `j` of the
configuration `x` leaves `acube (max L ℓ)` then either `j = i`, in which case the indicator
`indU ℓ 0 (xᵢ)` vanishes (`acube ℓ ⊆ acube (max L ℓ)`), or `j ≠ i`, in which case the fibre
`z ↦ Ψ (x with xᵢ = z)` is identically zero (its `j`-th slot is `x_j ∉ acube L`), so `fsT` of it
vanishes by `Word.fsT_zero`. -/
lemma indU_mul_fsT_fibre_eq_zero_of_notMem_abox_max {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : X N → ℝ} (hsupp : tsupport Ψ ⊆ abox N L) {x : X N}
    (hx : x ∉ abox N (max L ℓ)) (i : Fin N) :
    indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin N, x j ∉ acube (max L ℓ) := by
    by_contra h
    exact hx fun k => not_not.mp (not_exists.mp h k)
  by_cases hji : j = i
  · rw [hji] at hj
    have hnot : x i ∉ lamBox ℓ 0 := by
      intro hc
      exact hj (Submission.BoseGases.acube_mono hℓ.le (le_max_right L ℓ)
        (by simpa [lamBox, Work.BSKinetic.bsBox] using hc))
    rw [show indU ℓ 0 (x i) = 0 from Set.indicator_of_notMem hnot _, zero_mul]
  · have hfib : fibre N i Ψ x = 0 := by
      funext z
      show Ψ (Function.update x i z) = 0
      refine Work.BoseKinLoc.Word.eq_zero_of_not_mem_abox hsupp ?_
      intro hmem
      have hcoord : x j ∈ acube L := by
        have h := hmem j
        rwa [Function.update_of_ne hji z x] at h
      exact hj (acube_subset_acube_max_gen L ℓ hcoord)
    rw [hfib, Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]

/-! ## 3. The partition of an integral over the slot sets -/

/-- **The slot sets partition the configuration space**, so an integral is the sum over
`S : Finset (Fin N)` of the integral over `slotSet B S`. -/
lemma integral_eq_sum_setIntegral_slotSet {B : Set ℝ³} (hB : MeasurableSet B)
    {g : X N → ℝ} (hg : Integrable g) :
    ∫ x : X N, g x = ∑ S : Finset (Fin N), ∫ x in Work.PerSector.slotSet B S, g x := by
  classical
  have hsum : ∀ x : X N, g x
      = ∑ S : Finset (Fin N), (Work.PerSector.slotSet B S).indicator g x := by
    intro x
    obtain ⟨S₀, hS₀⟩ := Set.mem_iUnion.mp
      (by rw [Work.PerSector.iUnion_slotSet B]; exact Set.mem_univ x)
    rw [Finset.sum_eq_single S₀]
    · exact (Set.indicator_of_mem hS₀ g).symm
    · intro T _ hT
      rw [Set.indicator_of_notMem]
      exact fun hTmem => hT (Work.PerSector.slotSet_eq_of_mem hTmem hS₀)
    · intro h
      exact absurd (Finset.mem_univ S₀) h
  have hone : (∫ x : X N, g x)
      = ∑ S : Finset (Fin N), ∫ x : X N, (Work.PerSector.slotSet B S).indicator g x := by
    rw [show (∫ x : X N, g x) = ∫ x : X N, ∑ S : Finset (Fin N),
        (Work.PerSector.slotSet B S).indicator g x from
      integral_congr_ae (Filter.Eventually.of_forall hsum)]
    rw [integral_finsetSum _ (fun S _ => hg.indicator (Work.PerSector.slotSet_measurable B hB S))]
  rw [hone]
  exact Finset.sum_congr rfl fun S _ =>
    MeasureTheory.integral_indicator (Work.PerSector.slotSet_measurable B hB S)

/-! ## 4. The unconditional re-indexing of the slot box -/

/-- **Re-indexing the slot box for the Bochner integral** (unconditional form, for a measurable
box `B`).  The order isomorphism `slotIso S : SlotIn N S ≃ Fin S.card` re-indexes the
in-box configuration space, and it maps the box `slotBox B` over `SlotIn N S` onto the box
`slotBox B` over `Fin S.card`.  The proof uses the unconditional change of variables
`MeasurePreserving.integral_comp'` for the measurable equivalence `piCongrLeft` generated by
`(slotIso S).symm`, together with `integral_indicator` (which is where measurability of `B` is
needed). -/
lemma slotBox_setIntegral_slotIso_measurable (S : Finset (Fin N)) {B : Set ℝ³}
    (hB : MeasurableSet B) (F : (Fin S.card → ℝ³) → ℝ) :
    (∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
        F (fun m : Fin S.card => z ((slotIso S).symm m)))
      = ∫ x in (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)), F x := by
  classical
  let Φ : (Fin S.card → ℝ³) ≃ᵐ (Work.PerSector.SlotIn N S → ℝ³) :=
    MeasurableEquiv.piCongrLeft (fun _ : Work.PerSector.SlotIn N S => ℝ³) (slotIso S).symm
  have hΦ : ∀ (x : Fin S.card → ℝ³) (i : Work.PerSector.SlotIn N S), Φ x i = x (slotIso S i) := by
    intro x i
    have h1 : Φ x ((slotIso S).symm ((slotIso S) i)) = x ((slotIso S) i) :=
      Equiv.piCongrLeft_apply_apply (P := fun _ : Work.PerSector.SlotIn N S => ℝ³)
        (e := (slotIso S).symm) x ((slotIso S) i)
    rwa [Equiv.symm_apply_apply] at h1
  have hsymm : ∀ z : Work.PerSector.SlotIn N S → ℝ³,
      Φ.symm z = fun m : Fin S.card => z ((slotIso S).symm m) := by
    intro z
    funext m
    have h := hΦ (Φ.symm z) ((slotIso S).symm m)
    simp only [MeasurableEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have hmp : MeasurePreserving Φ volume volume :=
    volume_measurePreserving_piCongrLeft _ (slotIso S).symm
  have hmeasmem : ∀ z : Work.PerSector.SlotIn N S → ℝ³,
      Φ.symm z ∈ (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³))
        ↔ z ∈ (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)) := by
    intro z
    simp only [Work.PerSector.mem_slotBox_iff, hsymm]
    exact ⟨fun h i => by simpa using h (slotIso S i), fun h m => h ((slotIso S).symm m)⟩
  have hpt : ∀ z : Work.PerSector.SlotIn N S → ℝ³,
      (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)).indicator F (Φ.symm z)
        = (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)).indicator
            (fun z => F (Φ.symm z)) z := by
    intro z
    by_cases h : z ∈ (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³))
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmeasmem z).mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h ((hmeasmem z).mp hc))]
  calc (∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
        F (fun m : Fin S.card => z ((slotIso S).symm m)))
      = ∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
          (fun z => F (Φ.symm z)) z := by
        refine setIntegral_congr_fun
          (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotIn N S) hB)
          (fun z _ => ?_)
        rw [hsymm]
    _ = ∫ z : Work.PerSector.SlotIn N S → ℝ³,
          (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)).indicator
            (fun z => F (Φ.symm z)) z :=
        (MeasureTheory.integral_indicator
          (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotIn N S) hB)).symm
    _ = ∫ z : Work.PerSector.SlotIn N S → ℝ³,
          (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)).indicator F (Φ.symm z) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)
    _ = ∫ x : Fin S.card → ℝ³,
          (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)).indicator F x :=
        MeasurePreserving.integral_comp' hmp.symm _
    _ = ∫ x in (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)), F x :=
        MeasureTheory.integral_indicator
          (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Fin S.card) hB)

/-! ## 5. The integral over a slot set of the slot-`i` kinetic integrand -/

/-- **Vanishing of the slot-`i` kinetic integrand on the slot set of a slot `S ∌ i`**: on
`slotSet (acube ℓ) S` the `i`-th coordinate lies outside `acube ℓ`, so the indicator
`indU ℓ 0 (xᵢ)` kills the integrand. -/
lemma setIntegral_slotSet_eq_zero_of_not_mem {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : X N → ℝ} (hsupp : tsupport Ψ ⊆ abox N L) (i : Fin N) {S : Finset (Fin N)}
    (hi : i ∉ S) :
    (∫ x in Work.PerSector.slotSet (acube ℓ) S,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x)) = 0 := by
  have hzero : ∀ x ∈ Work.PerSector.slotSet (acube ℓ) S,
      indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) = 0 := by
    intro x hx
    have hxi : x i ∉ acube ℓ := fun h => hi ((hx i).mp h)
    have hnot : x i ∉ lamBox ℓ 0 := by
      intro hc
      exact hxi (by simpa [lamBox, Work.BSKinetic.bsBox] using hc)
    rw [show indU ℓ 0 (x i) = 0 from Set.indicator_of_notMem hnot _, zero_mul]
  rw [MeasureTheory.setIntegral_congr_fun
    (Work.PerSector.slotSet_measurable (acube ℓ) (Submission.BoseGases.acube_measurable ℓ) S) hzero]
  simp

/-- **The slot-set integral of the slot-`i` kinetic integrand at a slot set containing `i`.**  The
slot sets partition the configuration space and the integrand is integrable, so the integral over
the slot set is `∫ x, 1_{slotSet}·(the integrand)`, which vanishes off `abox N (max L ℓ)`; the slot
splitting `Work.SlotWord.slotSplit_integral_slotBox` then gives the iterated integral over the
in-configuration `z` and the outside configuration `y`.  On the domain the indicator of the slot set
is one, `indU ℓ 0 (z ⟨i,·⟩) = 1` and the fibre of `Ψ` at `slotComb S z y` is the fibre of the fibre
state `fibState S Ψ y` at the re-indexed configuration (`fibre_fibState_eq`); the re-indexing of the
in-box integral along `slotIso S` is `slotBox_setIntegral_slotIso_measurable`. -/
lemma setIntegral_slotSet_eq_of_mem {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hsupp : tsupport Ψ ⊆ abox N L) {i : Fin N}
    (hF : MeasureTheory.Integrable (fun x : X N =>
      indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x)))
    {S : Finset (Fin N)} (hi : i ∈ S) :
    (∫ x in Work.PerSector.slotSet (acube ℓ) S,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x))
      = ∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
          ∫ z in (Submission.BoseGases.abox S.card ℓ : Set (Submission.BoseGases.X S.card)),
            fsT ℓ d s εT b 0
              (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) z) := by
  classical
  set B : Set ℝ³ := acube ℓ with hBdef
  set L' : ℝ := max L ℓ with hL'def
  have hBL : B ⊆ acube L' := by
    rw [hBdef, hL'def]
    exact Submission.BoseGases.acube_mono hℓ.le (le_max_right L ℓ)
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact Submission.BoseGases.acube_measurable ℓ
  set F : X N → ℝ :=
    fun x => indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) with hFdef
  set G : X N → ℝ := (Work.PerSector.slotSet B S).indicator F with hGdef
  have hGint : MeasureTheory.Integrable G :=
    hF.indicator (Work.PerSector.slotSet_measurable B hBmeas S)
  have hGzero : ∀ x : X N, G x ≠ 0 → x ∈ Work.PerSector.slotSet B S := by
    intro x hx
    by_contra hc
    exact hx (by rw [hGdef, Set.indicator_of_notMem hc])
  -- step 1: the slot-set integral is the integral of the indicator
  have h1 : (∫ x in Work.PerSector.slotSet B S, F x) = ∫ x : X N, G x :=
    (MeasureTheory.integral_indicator
      (Work.PerSector.slotSet_measurable B hBmeas S)).symm
  -- step 2: the support of the indicator lies in `abox N L'`
  have h2 : (∫ x : X N, G x) = ∫ x in abox N L', G x :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      by_cases hxs : x ∈ Work.PerSector.slotSet B S
      · rw [hGdef, Set.indicator_of_mem hxs]
        exact indU_mul_fsT_fibre_eq_zero_of_notMem_abox_max (N := N) (L := L) (ℓ := ℓ) hℓ hsupp
          (by rwa [hL'def] at hx) i
      · rw [hGdef, Set.indicator_of_notMem hxs]).symm
  -- step 3: the slot splitting
  have h3 : (∫ x in abox N L', G x)
      = ∫ y in Work.PerSector.slotOutside L' B S,
          ∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
            G (Work.PerSector.slotComb S z y) := by
    refine Work.SlotWord.slotSplit_integral_slotBox L' S hBL ?_ hGint.integrableOn ?_ ?_
    · exact hGint.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · intro x hx j
      exact fun hxj => j.2 ((hGzero x hx j.1).mp hxj)
    · intro x hx j
      exact (hGzero x hx j.1).mpr j.2
  -- step 4: the pointwise identification on the slot box and the re-indexing
  have h4 : (∫ y in Work.PerSector.slotOutside L' B S,
          ∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
            G (Work.PerSector.slotComb S z y))
      = ∫ y in Work.PerSector.slotOutside L' B S,
          ∫ z in (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³)),
            fsT ℓ d s εT b 0
              (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) z) := by
    refine setIntegral_congr_fun ?_ (fun y hy => ?_)
    · exact Work.PerSector.Work.PerSector.slotBox_measurable
        ((Submission.BoseGases.acube_measurable L').inter hBmeas.compl)
    · refine Eq.trans ?_ (slotBox_setIntegral_slotIso_measurable S hBmeas
          (fun x : Fin S.card → ℝ³ => fsT ℓ d s εT b 0
            (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) x)))
      refine setIntegral_congr_fun
        (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotIn N S) hBmeas)
        (fun z hz => ?_)
      obtain ⟨hy1, hy2⟩ := (Work.PerSector.mem_slotOutside_iff).mp hy
      have hz' := (Work.PerSector.mem_slotBox_iff).mp hz
      have hmem : Work.PerSector.slotComb S z y ∈ Work.PerSector.slotSet B S :=
        (Work.PerSector.slotComb_mem_slotSet_iff B S z y).mpr ⟨hz', hy2⟩
      have hzi : (Work.PerSector.slotComb S z y) i = z ⟨i, hi⟩ := by
        rw [Work.PerSector.slotComb_apply, dif_pos hi]
      have hind : indU ℓ 0 (z ⟨i, hi⟩) = 1 := by
        refine Set.indicator_of_mem ?_ 1
        have hzB : z ⟨i, hi⟩ ∈ Submission.BoseGases.acube ℓ := hBdef ▸ hz' ⟨i, hi⟩
        show z ⟨i, hi⟩ - ℓ • (0 : ℝ³) ∈ Submission.BoseGases.acube ℓ
        simpa using hzB
      simp only [hGdef, Set.indicator_of_mem hmem, hFdef]
      rw [hzi, hind, one_mul]
      exact congrArg (fun w => fsT ℓ d s εT b 0 w)
        (fibre_fibState_eq S ⟨i, hi⟩ Ψ y z).symm
  -- step 5: the slot box over `Fin S.card` is the corpus box `abox S.card ℓ`
  have hset : (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³))
      = (Submission.BoseGases.abox S.card ℓ : Set (X S.card)) := by
    ext x
    simp only [Work.PerSector.mem_slotBox_iff, Submission.BoseGases.abox,
      Set.mem_ofPred_eq, hBdef]
  rw [h1, h2, h3, h4]
  refine setIntegral_congr_fun ?_ (fun y _ => ?_)
  · exact Work.PerSector.Work.PerSector.slotBox_measurable
      ((Submission.BoseGases.acube_measurable L').inter hBmeas.compl)
  · rw [hset]

/-! ## 6. Integrability in the outside configuration of the iterated fibre integral -/

/-- **Integrability of the iterated fibre kinetic integral in the outside configuration.**  The
joint integrand `(z, y) ↦ 1_{slotSet B S}(slotComb S z y) · indU ℓ 0 (zᵢ) · fsT … 0 (fibre …)` is
integrable on the product of the two slot boxes over `acube (max L ℓ)` (transport of the
integrability of the slot integrand along the measure-preserving slot equivalence,
`integrable_slotComb_prod`), so its outside marginal
`y ↦ ∫ z, 1_{slotSet B S}(slotComb S z y)·(…)` is integrable
(`Integrable.integral_prod_right`).  On `slotOutside (max L ℓ) (acube ℓ) S` that marginal is the
iterated fibre integral `y ↦ ∫_{abox |S| ℓ} fsT … 0 (fibre … (fibState S Ψ y))`: the domain shrinks
from `slotBox (acube (max L ℓ))` to `slotBox (acube ℓ)` (off it some in-slot coordinate leaves
`acube ℓ`, which leaves the slot set), the indicator becomes one, `indU ℓ 0 (zᵢ) = 1` on the box,
the fibre identity `fibre_fibState_eq` re-writes the fibre, and
`slotBox_setIntegral_slotIso_measurable` re-indexes the box integral. -/
lemma integrableOn_iterated_fsT_fibre {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hsupp : tsupport Ψ ⊆ abox N L) {i : Fin N}
    (hF : MeasureTheory.Integrable (fun x : X N =>
      indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x)))
    {S : Finset (Fin N)} (hi : i ∈ S) :
    MeasureTheory.IntegrableOn
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫ z in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
          fsT ℓ d s εT b 0
            (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) z))
      (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S) := by
  classical
  set B : Set ℝ³ := acube ℓ with hBdef
  set L' : ℝ := max L ℓ with hL'def
  have hBL : B ⊆ acube L' := by
    rw [hBdef, hL'def]
    exact Submission.BoseGases.acube_mono hℓ.le (le_max_right L ℓ)
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact Submission.BoseGases.acube_measurable ℓ
  have hL'meas : MeasurableSet (Submission.BoseGases.acube L') :=
    Submission.BoseGases.acube_measurable L'
  set F : X N → ℝ :=
    fun x => indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) with hFdef
  set G : X N → ℝ := (Work.PerSector.slotSet B S).indicator F with hGdef
  have hGint : MeasureTheory.Integrable G :=
    hF.indicator (Work.PerSector.slotSet_measurable B hBmeas S)
  have hHint : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫ z : Work.PerSector.SlotIn N S → ℝ³, G (Work.PerSector.slotComb S z y)
          ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Work.PerSector.SlotIn N S → ℝ³)).restrict
              (Work.PerSector.slotBox (Submission.BoseGases.acube L'))))
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotBox (Submission.BoseGases.acube L'))) :=
    MeasureTheory.Integrable.integral_prod_right
      (integrable_slotComb_prod L' S (hint := hGint.integrableOn))
  -- the pointwise identification on `slotOutside`
  have hpt : ∀ y ∈ Work.PerSector.slotOutside L' B S,
      (∫ z : Work.PerSector.SlotIn N S → ℝ³, G (Work.PerSector.slotComb S z y)
          ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Work.PerSector.SlotIn N S → ℝ³)).restrict
              (Work.PerSector.slotBox (Submission.BoseGases.acube L'))))
        = ∫ z in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            fsT ℓ d s εT b 0
              (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) z) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := (Work.PerSector.mem_slotOutside_iff).mp hy
    -- shrink the in-box domain from `acube (max L ℓ)` to `acube ℓ`
    have hshrink : (∫ z : Work.PerSector.SlotIn N S → ℝ³, G (Work.PerSector.slotComb S z y)
          ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Work.PerSector.SlotIn N S → ℝ³)).restrict
              (Work.PerSector.slotBox (Submission.BoseGases.acube L'))))
        = ∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
            G (Work.PerSector.slotComb S z y) := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotIn N S)
          (Submission.BoseGases.acube_measurable L'))
        (Work.PerSector.Work.PerSector.slotBox_mono (ι := Work.PerSector.SlotIn N S) hBL) ?_
      intro z hz
      have hznot : z ∉ (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)) := hz.2
      have hnotmem : Work.PerSector.slotComb S z y ∉ Work.PerSector.slotSet B S := by
        intro hmem
        obtain ⟨j, hj⟩ : ∃ j : Work.PerSector.SlotIn N S, z j ∉ B := by
          by_contra h
          exact hznot fun i => not_not.mp (not_exists.mp h i)
        have hzj : z j ∈ B := by
          have h1 := (hmem j.1).mpr j.2
          rwa [Work.PerSector.slotComb_apply, dif_pos j.2] at h1
        exact hj hzj
      rw [hGdef, Set.indicator_of_notMem hnotmem]
    -- on the box the indicator is one and the fibre identity applies
    have hpt2 : (∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
            G (Work.PerSector.slotComb S z y))
        = ∫ z in (Work.PerSector.slotBox B : Set (Work.PerSector.SlotIn N S → ℝ³)),
            (fun x : Fin S.card → ℝ³ => fsT ℓ d s εT b 0
              (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) x))
              (fun m : Fin S.card => z ((slotIso S).symm m)) := by
      refine setIntegral_congr_fun
        (Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotIn N S) hBmeas)
        (fun z hz => ?_)
      have hz' := (Work.PerSector.mem_slotBox_iff).mp hz
      have hmem : Work.PerSector.slotComb S z y ∈ Work.PerSector.slotSet B S :=
        (Work.PerSector.slotComb_mem_slotSet_iff B S z y).mpr ⟨hz', hy2⟩
      have hzi : (Work.PerSector.slotComb S z y) i = z ⟨i, hi⟩ := by
        rw [Work.PerSector.slotComb_apply, dif_pos hi]
      have hind : indU ℓ 0 (z ⟨i, hi⟩) = 1 := by
        refine Set.indicator_of_mem ?_ 1
        have hzB : z ⟨i, hi⟩ ∈ Submission.BoseGases.acube ℓ := hBdef ▸ hz' ⟨i, hi⟩
        show z ⟨i, hi⟩ - ℓ • (0 : ℝ³) ∈ Submission.BoseGases.acube ℓ
        simpa using hzB
      simp only [hGdef, Set.indicator_of_mem hmem, hFdef]
      rw [hzi, hind, one_mul]
      exact congrArg (fun w => fsT ℓ d s εT b 0 w)
        (fibre_fibState_eq S ⟨i, hi⟩ Ψ y z).symm
    -- re-index and pass to the corpus box
    have hset : (Work.PerSector.slotBox B : Set (Fin S.card → ℝ³))
        = (Submission.BoseGases.abox S.card ℓ : Set (X S.card)) := by
      ext x
      simp only [Work.PerSector.mem_slotBox_iff, Submission.BoseGases.abox,
        Set.mem_ofPred_eq, hBdef]
    rw [hshrink, hpt2, slotBox_setIntegral_slotIso_measurable S hBmeas
      (fun x : Fin S.card → ℝ³ => fsT ℓ d s εT b 0
        (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) x)), hset]
  -- restrict to the outside box and convert
  have hHrestr : MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫ z : Work.PerSector.SlotIn N S → ℝ³, G (Work.PerSector.slotComb S z y)
          ∂((MeasureTheory.volume : MeasureTheory.Measure
              (Work.PerSector.SlotIn N S → ℝ³)).restrict
              (Work.PerSector.slotBox (Submission.BoseGases.acube L'))))
      (((MeasureTheory.volume : MeasureTheory.Measure
          (Work.PerSector.SlotOut N S → ℝ³)).restrict
          (Work.PerSector.slotBox (Submission.BoseGases.acube L'))).restrict
        (Work.PerSector.slotOutside L' B S)) :=
    MeasureTheory.Integrable.integrableOn hHint
  rw [show (((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → ℝ³)).restrict
        (Work.PerSector.slotBox (Submission.BoseGases.acube L'))).restrict
        (Work.PerSector.slotOutside L' B S))
      = (MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut N S → ℝ³)).restrict
          (Work.PerSector.slotOutside L' B S) from
    MeasureTheory.Measure.restrict_restrict_of_subset
      (Work.PerSector.Work.PerSector.slotBox_mono (ι := Work.PerSector.SlotOut N S)
        Set.inter_subset_left)] at hHrestr
  refine hHrestr.congr ?_
  have hOutMeas : MeasurableSet (Work.PerSector.slotOutside L' B S) :=
    Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotOut N S)
      ((Submission.BoseGases.acube_measurable L').inter hBmeas.compl)
  have hae : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → ℝ³)).restrict (Work.PerSector.slotOutside L' B S)),
      (∫ z : Work.PerSector.SlotIn N S → ℝ³, G (Work.PerSector.slotComb S z y)
        ∂((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotIn N S → ℝ³)).restrict
            (Work.PerSector.slotBox (Submission.BoseGases.acube L'))))
        = ∫ z in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            fsT ℓ d s εT b 0 (fibre S.card (slotIso S ⟨i, hi⟩) (fibState S Ψ y) z) := by
    rw [MeasureTheory.ae_restrict_iff' hOutMeas]
    exact Filter.Eventually.of_forall fun y hy => hpt y hy
  exact hae

/-! ## 7. Integrability of the `kinFormB` of the fibre state -/

/-- **Integrability of the `i'`-th summand of `kinFormB` at the fibre.**  The summand
`y ↦ ∫_{abox |S| ℓ} indU ℓ 0 (x i') · fsT … 0 (fibre i' (fibState S Ψ y))` is the iterated fibre
kinetic integral of `integrableOn_iterated_fsT_fibre` with the (box-)redundant factor
`indU ℓ 0 (x i')`, which is one on `abox |S| ℓ`. -/
lemma integrableOn_kinFormB_summand {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (hsupp : tsupport Ψ ⊆ abox N L)
    {S : Finset (Fin N)} (i' : Fin S.card) :
    MeasureTheory.IntegrableOn
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
          indU ℓ 0 (x i') * fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x))
      (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S) := by
  classical
  have hOutMeas : MeasurableSet (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S) :=
    Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotOut N S)
      ((Submission.BoseGases.acube_measurable (max L ℓ)).inter
        (Submission.BoseGases.acube_measurable ℓ).compl)
  set j : Work.PerSector.SlotIn N S := (slotIso S).symm i' with hjdef
  have hFint : MeasureTheory.Integrable (fun x : X N =>
      indU ℓ 0 (x j.1) * fsT ℓ d s εT b 0 (fibre N j.1 Ψ x)) :=
    integrable_indU_mul_fsT_fibre_anyL (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s)
      (εT := εT) (b := b) hℓ hΨ hsupp j.1
  have hbase := integrableOn_iterated_fsT_fibre (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hsupp hFint j.2
  have hcast : slotIso S j = i' := by
    show (slotIso S) ((slotIso S).symm i') = i'
    exact Equiv.apply_symm_apply (slotIso S) i'
  rw [hcast] at hbase
  refine MeasureTheory.Integrable.congr hbase ?_
  show ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure
      (Work.PerSector.SlotOut N S → ℝ³)).restrict
      (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S)),
    (∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
        fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x))
      = ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
          indU ℓ 0 (x i') * fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x)
  rw [MeasureTheory.ae_restrict_iff' hOutMeas]
  refine Filter.Eventually.of_forall fun y _ => ?_
  refine MeasureTheory.setIntegral_congr_fun
    (Submission.BoseGases.abox_measurable S.card ℓ) (fun x hx => ?_)
  have hind : indU ℓ 0 (x i') = 1 := by
    refine Set.indicator_of_mem ?_ 1
    have hxB : x i' ∈ Submission.BoseGases.acube ℓ := hx i'
    show x i' - ℓ • (0 : ℝ³) ∈ Submission.BoseGases.acube ℓ
    simpa using hxB
  rw [hind, one_mul]

/-- **Integrability of the `kinFormB` of the fibre state.** -/
lemma integrableOn_kinFormB_fibState {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (hsupp : tsupport Ψ ⊆ abox N L)
    (S : Finset (Fin N)) :
    MeasureTheory.IntegrableOn
      (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S) := by
  classical
  have hfun : (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      = fun y => ℓ ^ (-3 : ℤ) * ∑ i' : Fin S.card,
          ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            indU ℓ 0 (x i') * fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x) := by
    funext y
    rfl
  rw [hfun]
  refine MeasureTheory.Integrable.const_mul ?_ _
  exact MeasureTheory.integrable_finsetSum _
    (fun i' _ => integrableOn_kinFormB_summand (N := N) hℓ hΨ hsupp i')

/-! ## 8. The `S`-term of the fibre sum -/

/-- **The `S`-term of the fibre kinetic sum.**  The integral over the outside configurations of the
box-restricted kinetic word of the fibre state is `ℓ⁻³` times the sum over the slots of `S` of the
slot-set integrals of the slot-`i` kinetic integrand: unfold `kinFormB`, pull the constant and the
finite sum out of the `y`-integral (the per-summand integrability is
`integrableOn_kinFormB_summand`), and identify each term with the slot-set integral by
`setIntegral_slotSet_eq_of_mem` (together with the fact that `indU ℓ 0 (x i')` is one on
`abox |S| ℓ`). -/
lemma fibreSumTerm_eq {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (hsupp : tsupport Ψ ⊆ abox N L)
    (S : Finset (Fin N)) :
    (∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
        Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      = ℓ ^ (-3 : ℤ) * ∑ i' : Fin S.card,
          ∫ x in Work.PerSector.slotSet (acube ℓ) S,
            indU ℓ 0 (x ((slotIso S).symm i').1)
              * fsT ℓ d s εT b 0 (fibre N ((slotIso S).symm i').1 Ψ x) := by
  classical
  have hOutMeas : MeasurableSet (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S) :=
    Work.PerSector.Work.PerSector.slotBox_measurable (ι := Work.PerSector.SlotOut N S)
      ((Submission.BoseGases.acube_measurable (max L ℓ)).inter
        (Submission.BoseGases.acube_measurable ℓ).compl)
  have hfun : (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
        Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
      = fun y => ℓ ^ (-3 : ℤ) * ∑ i' : Fin S.card,
          ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            indU ℓ 0 (x i') * fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x) := by
    funext y
    rfl
  rw [hfun, MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finsetSum _
    (fun i' _ => integrableOn_kinFormB_summand (N := N) hℓ hΨ hsupp i')]
  refine Finset.sum_congr rfl fun i' _ => ?_
  set j : Work.PerSector.SlotIn N S := (slotIso S).symm i' with hjdef
  have hFint : MeasureTheory.Integrable (fun x : X N =>
      indU ℓ 0 (x j.1) * fsT ℓ d s εT b 0 (fibre N j.1 Ψ x)) :=
    integrable_indU_mul_fsT_fibre_anyL (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s)
      (εT := εT) (b := b) hℓ hΨ hsupp j.1
  have hmain := setIntegral_slotSet_eq_of_mem (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hsupp hFint j.2
  have hcast : slotIso S j = i' := by
    show (slotIso S) ((slotIso S).symm i') = i'
    exact Equiv.apply_symm_apply (slotIso S) i'
  rw [hcast] at hmain
  calc (∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
          ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            indU ℓ 0 (x i') * fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x))
      = ∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
          ∫ x in (Submission.BoseGases.abox S.card ℓ : Set (X S.card)),
            fsT ℓ d s εT b 0 (fibre S.card i' (fibState S Ψ y) x) := by
        refine MeasureTheory.setIntegral_congr_fun hOutMeas (fun y _ => ?_)
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable S.card ℓ) (fun x hx => ?_)
        have hind : indU ℓ 0 (x i') = 1 := by
          refine Set.indicator_of_mem ?_ 1
          have hxB : x i' ∈ Submission.BoseGases.acube ℓ := hx i'
          show x i' - ℓ • (0 : ℝ³) ∈ Submission.BoseGases.acube ℓ
          simpa using hxB
        rw [hind, one_mul]
    _ = ∫ x in Work.PerSector.slotSet (acube ℓ) S,
            indU ℓ 0 (x j.1) * fsT ℓ d s εT b 0 (fibre N j.1 Ψ x) := hmain.symm

/-! ## 9. The kinetic half of the sector decomposition -/

/-- **The sector decomposition of the kinetic word.**  The `N`-body kinetic word
`kinForm N ℓ d s εT b 0 Ψ` of a smooth state supported in `abox N L` is the sum, over the slot sets
`S : Finset (Fin N)`, of the integral over the outside configurations of the box-restricted kinetic
word `kinFormB |S| ℓ d s εT b` of the fibre state `fibState S Ψ y`, and each outside integrand is
integrable. -/
theorem kinForm_fibreSum {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (hsupp : tsupport Ψ ⊆ abox N L) :
    (Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ
      = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
    ∧ (∀ S : Finset (Fin N),
        MeasureTheory.IntegrableOn
          (fun y : Work.PerSector.SlotOut N S → ℝ³ =>
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
          (Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S)) := by
  classical
  have hFint : ∀ i : Fin N, MeasureTheory.Integrable (fun x : X N =>
      indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x)) := fun i =>
    integrable_indU_mul_fsT_fibre_anyL (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s)
      (εT := εT) (b := b) hℓ hΨ hsupp i
  constructor
  · -- the equality
    have hA : Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ
        = ∑ i : Fin N, ℓ ^ (-3 : ℤ) * ∑ S : Finset (Fin N),
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) := by
      simp only [Work.BoseKinLoc.kinForm, Work.BoseKinLoc.slotForm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_eq_sum_setIntegral_slotSet (Submission.BoseGases.acube_measurable ℓ)
        (hFint i)]
    have hB : ∀ S : Finset (Fin N),
        (∑ i : Fin N, ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x))
          = ∑ i' : Fin S.card,
              ∫ x in Work.PerSector.slotSet (acube ℓ) S,
                indU ℓ 0 (x ((slotIso S).symm i').1)
                  * fsT ℓ d s εT b 0 (fibre N ((slotIso S).symm i').1 Ψ x) := by
      intro S
      set g : Fin N → ℝ := fun i => ∫ x in Work.PerSector.slotSet (acube ℓ) S,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) with hgdef
      have h1 : (∑ i ∈ Finset.univ.filter (fun i : Fin N => i ∈ S), g i) = ∑ i : Fin N, g i :=
        Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact setIntegral_slotSet_eq_zero_of_not_mem (N := N) hℓ hsupp i hi)
      rw [← h1, Finset.sum_subtype (p := fun i : Fin N => i ∈ S)
        (Finset.univ.filter (fun i : Fin N => i ∈ S)) (fun i => by simp) g]
      exact (Fintype.sum_equiv (slotIso S).symm
        (fun i' : Fin S.card => g ((slotIso S).symm i').1)
        (fun a : Work.PerSector.SlotIn N S => g a.1) (fun i' => rfl)).symm
    calc Work.BoseKinLoc.kinForm N ℓ d s εT b 0 Ψ
        = ∑ i : Fin N, ℓ ^ (-3 : ℤ) * ∑ S : Finset (Fin N),
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) := hA
      _ = ℓ ^ (-3 : ℤ) * ∑ i : Fin N, ∑ S : Finset (Fin N),
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) := by
          rw [Finset.mul_sum]
      _ = ℓ ^ (-3 : ℤ) * ∑ S : Finset (Fin N), ∑ i : Fin N,
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Ψ x) := by
          rw [Finset.sum_comm]
      _ = ℓ ^ (-3 : ℤ) * ∑ S : Finset (Fin N), ∑ i' : Fin S.card,
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x ((slotIso S).symm i').1)
                * fsT ℓ d s εT b 0 (fibre N ((slotIso S).symm i').1 Ψ x) := by
          rw [Finset.sum_congr rfl (fun S _ => hB S)]
      _ = ∑ S : Finset (Fin N), ℓ ^ (-3 : ℤ) * ∑ i' : Fin S.card,
            ∫ x in Work.PerSector.slotSet (acube ℓ) S,
              indU ℓ 0 (x ((slotIso S).symm i').1)
                * fsT ℓ d s εT b 0 (fibre N ((slotIso S).symm i').1 Ψ x) := by
          rw [Finset.mul_sum]
      _ = ∑ S : Finset (Fin N),
          ∫ y in Work.PerSector.slotOutside (max L ℓ) (acube ℓ) S,
            Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          exact (fibreSumTerm_eq (N := N) hℓ hΨ hsupp S).symm
  · -- the integrability
    exact fun S => integrableOn_kinFormB_fibState (N := N) hℓ hΨ hsupp S

/-- **The sector decomposition of the localised box form, integrable case (equality).**  For a smooth state `Ψ` supported in `abox N L` whose potential integrand `x ↦ Ψ x ^ 2 * potWordU N v g ℓ μ 0 x` is integrable, the whole-space form is *equal* to the sum, over the slot sets `S`, of the box forms `boxFormB |S| …` of the fibre states (integrated over the outside configurations): `boxForm N … 0 Ψ = fibreSum v g ℓ L μ d s εT b Ψ`.  With the potential integrand integrable, the signed Fubini/Tonelli identities needed for the potential part are available, and the kinetic part is always integrable (bounded measurable integrand with compact support), so the sector decomposition is an identity rather than an inequality.  (The inequality direction is *false* without the integrability hypothesis: when the whole-space potential integral is Mathlib's junk value `0`, the fibre-side terms with `|S| ≤ 1` have no pair contribution and can survive, making the fibre sum strictly larger.) -/
theorem boxForm_fibre_sum_of_integrable {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ (0 : ℝ³) x)) :
    Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b 0 Ψ
      = fibreSum v g ℓ L μ d s εT b Ψ := by
  classical
  -- the two halves of the sector decomposition
  have hK := kinForm_fibreSum (N := N) (ℓ := ℓ) (L := L) (d := d) (s := s) (εT := εT)
    (b := b) hℓ hΨ hsupp
  have hP := potIntegral_fibreSum (N := N) (v := v) (g := g) (ℓ := ℓ) (L := L) (μ := μ)
    hℓ hΨ hsupp hint
  -- the fibre sum splits into the kinetic and the potential fibre sums
  have hfib : fibreSum v g ℓ L μ d s εT b Ψ
      = ∑ S : Finset (Fin N),
          ((∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
              Work.BoseKinLoc.kinFormB S.card ℓ d s εT b (fibState S Ψ y))
            + ∫ y in Work.PerSector.slotOutside (max L ℓ) (Submission.BoseGases.acube ℓ) S,
                ∫ z in (Submission.BoseGases.abox S.card ℓ : Set (Submission.BoseGases.X S.card)),
                  (fibState S Ψ y z) ^ 2
                    * Work.BoseKinLoc.potWordU S.card v g ℓ μ (0 : ℝ³) z) := by
    simp only [fibreSum, Work.BoseKinLoc.boxFormB]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [MeasureTheory.integral_add (hK.2 S) (hP.2 S)]
  rw [hfib, Finset.sum_add_distrib, ← hK.1, ← hP.1]
  rfl

end Work.BoseKinLoc.Sector

