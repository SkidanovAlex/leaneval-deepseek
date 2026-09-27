import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.horoUnimodular
import Submission.Work.EKLRelCross.pushforward_relation_of_condExp
import Submission.Work.EKLComp.measurableSet_smul_mem_atom
import Submission.Work.EKLRelCross.local_flower
import Submission.Work.EKLC7.LeafwiseGeom

/-!
# `Work.EKLUInv.local_invariance_of_ae_haar` — local `U`-invariance of `μ` from a.e. Haar
leafwise measures (Pisa 6.27, direction `⟸`)

If the leafwise measures of `(μ, U)` are `μ`-a.e. right-`U`-invariant, then `μ` is preserved by
every `u ∈ U` sufficiently close to `1`.

## Structure of the proof

The geometric input is a countable family of *plaque algebras* with "big" atoms
(`Work.EKLUInv.flowers_big_atoms`, the flowers of Pisa Cor. 6.15): countably many
`(Z n, m n)` with `IsPlaqueAlgebra U (Z n) (m n)`, measurable bases `G n ⊆ Z n` covering a.e.,
and `V R ∩ U ⊆ shape (m n) U x` for `x ∈ G n`.

* `good_of_atom` (**the measure-theoretic heart**): for a plaque algebra `(Z, m)`, an element
  `u ∈ U`, and a measurable `A` contained in the region
  `Θ = {a ∈ Z | u • a ∈ atom m a}` where the shape contains `u`, one has `μ (u • A) = μ A`.
  The proof uses the `condexp` axiom of `IsLeafwise` twice (for `1_A` and `1_{u · A}`) and the
  pointwise identity of the two leafwise averages: the parameter sets
  `(fun w => u * w) ⁻¹' shape m U x ∩ {v | v • x ∈ A}` and `shape m U x ∩ {v | v • x ∈ A}`
  coincide (`preimage_shape_inter_eq`), because for `a ∈ A` the point `u • a` lies in its own atom
  and `A ⊆ Z` is a union of atoms.  Left-invariance of `ν x` (from `hae` and `horoUnimodular`)
  then turns this into an identity of integrals.
* `measurePreserving_of_countable_good` (**globalization**): if countably many measurable sets
  `Θ n` cover `X₃` a.e. and every measurable subset of `Θ n` is `u`-invariant in mass, then
  `μ` is preserved by `x ↦ u • x`.  The proof is elementary: disjointify, use the fact that each
  `Θ n` has `μ (u • Θ n) = μ (Θ n)` (so the remainder `N = (⋃ Θ n)ᶜ` satisfies `μ (u • N) = 0`),
  and decompose an arbitrary measurable `A` along the disjoint cover.
* the main theorem takes `R = 1` (so that `u ∈ V (1/4) ⊆ V 1`) and applies the two steps with
  `Θ n = {y ∈ Z n | u • y ∈ atom (m n) y} ⊇ G n`.

All lemmas below are complete; the geometric input is `bigAtoms_flowers` (assembled here from
the local flower `Work.EKLRelCross.local_flower`).
-/

open MeasureTheory Work.EKLContract
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLUInv

variable {μ : Measure X3} [IsProbabilityMeasure μ]
variable {U : Subgroup SL3} {ν : X3 → Measure SL3} {X' : Set X3}

/-! ## Elementary lemmas on atoms and images -/

/-- Atoms of a countably generated σ-algebra on `X₃` are measurable for that σ-algebra. -/
lemma atom_measurable_of_countablyGenerated (m : MeasurableSpace X3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) (y : X3) :
    @MeasurableSet X3 m (atom m y) := by
  classical
  letI : MeasurableSpace X3 := m
  haveI : MeasurableSpace.CountablyGenerated X3 :=
    ⟨hgen.choose, hgen.choose_spec.1, hgen.choose_spec.2⟩
  have hbridge : atom m y = measurableAtom y := by
    ext z
    simp only [atom, measurableAtom, Set.mem_sInter, Set.mem_iInter, Set.mem_setOf_eq]
    tauto
  rw [hbridge]
  exact MeasurableSpace.measurableSet_measurableAtom y

/-- Two points of the same atom have the same atom. -/
lemma atom_eq_of_mem {m : MeasurableSpace X3}
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) {x y : X3}
    (h : y ∈ atom m x) : atom m y = atom m x := by
  refine Set.Subset.antisymm ?_ ?_
  · exact Set.sInter_subset_of_mem ⟨atom_measurable_of_countablyGenerated m hgen x, h⟩
  · have hx : x ∈ atom m y := by
      refine Set.mem_sInter.mpr fun s hs => ?_
      by_contra hxs
      have : y ∈ sᶜ := Set.mem_sInter.mp h sᶜ ⟨hs.1.compl, hxs⟩
      exact this hs.2
    exact Set.sInter_subset_of_mem ⟨atom_measurable_of_countablyGenerated m hgen y, hx⟩

/-- The image of a set under `z ↦ u • z` is a preimage under the inverse action. -/
lemma smul_image_eq_preimage (u : SL3) (A : Set X3) :
    (fun z : X3 => u • z) '' A = (fun z : X3 => u⁻¹ • z) ⁻¹' A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    show u⁻¹ • (u • a) ∈ A
    rwa [inv_smul_smul]
  · intro h
    refine ⟨u⁻¹ • z, h, ?_⟩
    show u • (u⁻¹ • z) = z
    rw [smul_inv_smul]

/-- The complement of the image of `A` is the image of the complement of `A`. -/
lemma smul_image_compl (u : SL3) (A : Set X3) :
    (fun z : X3 => u • z) '' Aᶜ = ((fun z : X3 => u • z) '' A)ᶜ := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    refine ha ?_
    have h : b = a := by
      have := congrArg (fun w : X3 => u⁻¹ • w) hba
      simpa using this
    rwa [h] at hb
  · intro hz
    refine ⟨u⁻¹ • z, ?_, by simp⟩
    intro hmem
    exact hz ⟨u⁻¹ • z, hmem, by simp⟩

/-- Images of disjoint sets under the action are disjoint. -/
lemma disjoint_image_smul {u : SL3} {s t : Set X3} (h : Disjoint s t) :
    Disjoint ((fun x : X3 => u • x) '' s) ((fun x : X3 => u • x) '' t) := by
  rw [Set.disjoint_iff_inter_eq_empty] at h ⊢
  have hkey : (fun x : X3 => u • x) '' s ∩ (fun x : X3 => u • x) '' t
      = (fun x : X3 => u • x) '' (s ∩ t) := by
    ext z
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have h' : b = a := by
        have := congrArg (fun w : X3 => u⁻¹ • w) hba
        simpa using this
      rwa [h'] at hb
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩
  rw [hkey, h, Set.image_empty]

/-! ## The key set identity -/

/-- **Inner-region identity.**  If `A` is contained in the region where `u` keeps points inside
their own atom, then the `u`-preimage of a shape `shape m U x` meets the parameter set of `A`
exactly as the shape itself does. -/
lemma preimage_shape_inter_eq {m : MeasurableSpace X3} {Z : Set X3}
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b)
    {u : SL3} (hu : u ∈ U) {A : Set X3}
    (hA : ∀ a ∈ A, a ∈ Z ∧ u • a ∈ atom m a) {x : X3} :
    (fun w : SL3 => u * w) ⁻¹' shape m U x ∩ {v : SL3 | v • x ∈ A}
      = shape m U x ∩ {v : SL3 | v • x ∈ A} := by
  ext v
  constructor
  · rintro ⟨hv, hvA⟩
    have hvU : u * v ∈ U := hv.1
    have hvU' : v ∈ U := by
      have : u⁻¹ * (u * v) ∈ U := U.mul_mem (U.inv_mem hu) hvU
      simpa using this
    have huvx : (u * v) • x ∈ atom m x := hv.2
    have huvx' : (u * v) • x ∈ atom m (v • x) := by
      have := (hA (v • x) hvA).2
      simpa [mul_smul] using this
    have h1 : atom m (v • x) = atom m x :=
      (atom_eq_of_mem hgen huvx').symm.trans (atom_eq_of_mem hgen huvx)
    exact ⟨⟨hvU', by rw [← h1]; exact Set.mem_sInter.mpr fun s hs => hs.2⟩, hvA⟩
  · rintro ⟨hv, hvA⟩
    have hvU : v ∈ U := hv.1
    have hvx : v • x ∈ atom m x := hv.2
    have hatom : atom m (v • x) = atom m x := atom_eq_of_mem hgen hvx
    have huvx' : (u * v) • x ∈ atom m (v • x) := by
      have := (hA (v • x) hvA).2
      simpa [mul_smul] using this
    exact ⟨⟨U.mul_mem hu hvU, by
      show (u * v) • x ∈ atom m x
      rw [← hatom]
      exact huvx'⟩, hvA⟩

/-! ## Local goodness of a plaque algebra with a big atom -/

/-- **The `μ`-mass of a measurable subset of the inner region of a plaque algebra is `u`-invariant.**

`Z` is the domain of a plaque algebra, `A ⊆ Z` is measurable and lies in the region
`Θ = {a ∈ Z | u • a ∈ atom m a}` in which the shape of `m` at `a` contains `u`, and `u ∈ U`.  Then
`μ (u • A) = μ A`.

Proof: the `condexp` axiom of `IsLeafwise` applied to the plaque algebra `(Z, m)` expresses the
conditional average of `1_A` (and of `1_{u · A}`) on `Z` as the normalised leafwise average over
the shape.  The two leafwise averages agree pointwise (for *every* `x ∈ Z`), by
`preimage_shape_inter_eq` together with the left-invariance of `ν x` (which follows from `hae`
and `horoUnimodular`), so the two integrals over `Z` are equal; since `A ⊆ Z` and `u • A ⊆ Z`,
they are the `.toReal` of `μ A` and `μ (u • A)`. -/
theorem good_of_atom (hU : IsHoro U) (hL : IsLeafwise μ U ν X')
    (hae : Work.EKLRelCross.AeHaar μ U ν) {u : SL3} (hu : u ∈ U)
    {Z : Set X3} (𝔪 : Work.EKLComp.SigAlg) (hpla : IsPlaqueAlgebra U Z 𝔪.m)
    {A : Set X3} (hAmeas : MeasurableSet A)
    (hAΘ : ∀ a ∈ A, a ∈ Z ∧ u • a ∈ atom 𝔪.m a) :
    μ ((fun y : X3 => u • y) '' A) = μ A := by
  classical
  set uA : Set X3 := (fun y : X3 => u • y) '' A with huA
  have huAmeas : MeasurableSet uA := by
    rw [huA]
    exact (Homeomorph.measurableEmbedding
      (Homeomorph.smul (G := SL3) (α := X3) u)).measurableSet_image' hAmeas
  have huA_Z : uA ⊆ Z := by
    rintro z ⟨a, ha, rfl⟩
    exact (hpla.2.2.2 a (hAΘ a ha).1).1 (hAΘ a ha).2
  have hAZ : A ⊆ Z := fun a ha => (hAΘ a ha).1
  have hX' : ∀ᵐ x ∂(μ.restrict Z), x ∈ X' :=
    MeasureTheory.ae_restrict_of_ae (by
      rw [MeasureTheory.ae_iff, show {a : X3 | ¬ a ∈ X'} = X'ᶜ from rfl]
      exact hL.conull)
  have hZae : ∀ᵐ x ∂(μ.restrict Z), x ∈ Z := by
    rw [MeasureTheory.ae_restrict_iff' (hpla.1 _ hpla.2.2.1)]
    exact Filter.Eventually.of_forall fun x hx => hx
  have hAe : ∀ᵐ x ∂(μ.restrict Z), ∀ w ∈ U, (ν x).map (fun σ : SL3 => σ * w) = ν x :=
    MeasureTheory.ae_restrict_of_ae hae
  have hleft : ∀ᵐ x ∂(μ.restrict Z), ∀ E : Set SL3, MeasurableSet E →
      ν x ((fun w : SL3 => u * w) '' E) = ν x E := by
    filter_upwards [hX', hAe] with x hxX hxAe
    have hne : ν x ≠ 0 := by
      intro h0
      have h1 := hL.normalised x hxX
      rw [h0] at h1
      simp at h1
    have hmap : (ν x).map (fun σ : SL3 => u * σ) = ν x :=
      (Work.EKLRelCross.horoUnimodular hU (ν x) (hL.radon x hxX) (hL.carried x hxX) hne
        hxAe).1 u hu
    intro E hE
    have himg : (fun w : SL3 => u * w) '' E = (fun σ : SL3 => u⁻¹ * σ) ⁻¹' E := by
      ext σ
      constructor
      · rintro ⟨w, hw, rfl⟩
        show u⁻¹ * (u * w) ∈ E
        rwa [inv_mul_cancel_left]
      · intro h
        exact ⟨u⁻¹ * σ, h, by
          show u * (u⁻¹ * σ) = σ
          rw [mul_inv_cancel_left]⟩
    have hmeas : MeasurableSet ((fun w : SL3 => u * w) '' E) := by
      rw [himg]
      exact hE.preimage (by fun_prop : Measurable fun σ : SL3 => u⁻¹ * σ)
    have h1 := congrArg (fun (ρ : Measure SL3) => ρ ((fun w : SL3 => u * w) '' E)) hmap
    rw [MeasureTheory.Measure.map_apply
      (by fun_prop : Measurable fun σ : SL3 => u * σ) hmeas] at h1
    have hpre : (fun σ : SL3 => u * σ) ⁻¹' ((fun w : SL3 => u * w) '' E) = E := by
      ext σ
      constructor
      · rintro ⟨w, hw, hwσ⟩
        rwa [mul_left_cancel hwσ] at hw
      · intro hσ
        exact ⟨σ, hσ, rfl⟩
    rw [hpre] at h1
    exact h1.symm
  have hφae : ∀ᵐ x ∂(μ.restrict Z),
      (∫ v in shape 𝔪.m U x, uA.indicator (1 : X3 → ℝ) (v • x) ∂(ν x))
        = (∫ v in shape 𝔪.m U x, A.indicator (1 : X3 → ℝ) (v • x) ∂(ν x)) := by
    filter_upwards [hleft, hZae] with x hleftx hxZ
    have hSmeas : MeasurableSet (shape 𝔪.m U x) := by
      obtain ⟨O, hO, hshape⟩ := (hpla.2.2.2 x hxZ).2.2.1
      rw [hshape]
      exact hO.measurableSet.inter hU.1.measurableSet
    rw [Work.EKLRelCross.setIntegral_indicator_smul (ν x) (shape 𝔪.m U x) uA x hSmeas huAmeas,
      Work.EKLRelCross.setIntegral_indicator_smul (ν x) (shape 𝔪.m U x) A x hSmeas hAmeas]
    congr 1
    have hsetu : (fun v : SL3 => v • x) ⁻¹' uA
        = (fun w : SL3 => u * w) '' ((fun v : SL3 => v • x) ⁻¹' A) := by
      ext v
      constructor
      · intro hv
        obtain ⟨a, ha, hav⟩ := hv
        simp only [] at hav
        refine ⟨u⁻¹ * v, ?_, by simp⟩
        show (u⁻¹ * v) • x ∈ A
        rw [mul_smul, ← hav, inv_smul_smul]
        exact ha
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w • x, hw, by
          show u • (w • x) = (u * w) • x
          rw [mul_smul]⟩
    rw [hsetu]
    have hkey := preimage_shape_inter_eq hpla.2.1 hu hAΘ (m := 𝔪.m) (x := x)
    have himg : (fun w : SL3 => u * w) '' ((fun w : SL3 => u * w) ⁻¹' shape 𝔪.m U x
          ∩ (fun v : SL3 => v • x) ⁻¹' A)
        = shape 𝔪.m U x ∩ (fun w : SL3 => u * w) '' ((fun v : SL3 => v • x) ⁻¹' A) := by
      ext z
      constructor
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
        exact ⟨hw1, ⟨w, hw2, rfl⟩⟩
      · rintro ⟨hz, w, hw, rfl⟩
        exact ⟨w, ⟨hz, hw⟩, rfl⟩
    rw [← himg]
    have hEm : MeasurableSet ((fun w : SL3 => u * w) ⁻¹' shape 𝔪.m U x
        ∩ (fun v : SL3 => v • x) ⁻¹' A) := by
      refine MeasurableSet.inter ?_ ?_
      · exact hSmeas.preimage (by fun_prop : Measurable fun w : SL3 => u * w)
      · exact hAmeas.preimage (by fun_prop : Measurable fun v : SL3 => v • x)
    rw [hleftx _ hEm]
    show ν x ((fun w : SL3 => u * w) ⁻¹' shape 𝔪.m U x
          ∩ {v : SL3 | v • x ∈ A})
        = ν x (shape 𝔪.m U x ∩ {v : SL3 | v • x ∈ A})
    rw [hkey]
  have hφb : ∃ C, ∀ y : X3, |uA.indicator (1 : X3 → ℝ) y| ≤ C :=
    ⟨1, fun y => by
      by_cases hy : y ∈ uA <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]⟩
  have hφm : Measurable[instMeasurableSpaceX3] (uA.indicator (1 : X3 → ℝ)) :=
    (measurable_const : Measurable[instMeasurableSpaceX3] (1 : X3 → ℝ)).indicator huAmeas
  have hψb : ∃ C, ∀ y : X3, |A.indicator (1 : X3 → ℝ) y| ≤ C :=
    ⟨1, fun y => by
      by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]⟩
  have hψm : Measurable[instMeasurableSpaceX3] (A.indicator (1 : X3 → ℝ)) :=
    (measurable_const : Measurable[instMeasurableSpaceX3] (1 : X3 → ℝ)).indicator hAmeas
  have hconduA := hL.condexp Z 𝔪.m hpla (uA.indicator (1 : X3 → ℝ)) hφm hφb
  have hcondA := hL.condexp Z 𝔪.m hpla (A.indicator (1 : X3 → ℝ)) hψm hψb
  have hIntEq : (∫ y in Z, uA.indicator (1 : X3 → ℝ) y ∂μ)
      = ∫ y in Z, A.indicator (1 : X3 → ℝ) y ∂μ := by
    have h1 : (∫ y in Z, condExp 𝔪.m (μ.restrict Z) (uA.indicator (1 : X3 → ℝ)) y ∂μ)
        = ∫ y in Z, uA.indicator (1 : X3 → ℝ) y ∂μ :=
      integral_condExp (μ := μ.restrict Z) (m := 𝔪.m) (f := uA.indicator (1 : X3 → ℝ)) hpla.1
    have h2 : (∫ y in Z, condExp 𝔪.m (μ.restrict Z) (A.indicator (1 : X3 → ℝ)) y ∂μ)
        = ∫ y in Z, A.indicator (1 : X3 → ℝ) y ∂μ :=
      integral_condExp (μ := μ.restrict Z) (m := 𝔪.m) (f := A.indicator (1 : X3 → ℝ)) hpla.1
    have h3 : (∫ y in Z, condExp 𝔪.m (μ.restrict Z) (uA.indicator (1 : X3 → ℝ)) y ∂μ)
        = ∫ y in Z, (∫ v in shape 𝔪.m U y,
              uA.indicator (1 : X3 → ℝ) (v • y) ∂(ν y)) /
                (ν y (shape 𝔪.m U y)).toReal ∂μ :=
      integral_congr_ae hconduA
    have h4 : (∫ y in Z, condExp 𝔪.m (μ.restrict Z) (A.indicator (1 : X3 → ℝ)) y ∂μ)
        = ∫ y in Z, (∫ v in shape 𝔪.m U y,
              A.indicator (1 : X3 → ℝ) (v • y) ∂(ν y)) /
                (ν y (shape 𝔪.m U y)).toReal ∂μ :=
      integral_congr_ae hcondA
    have h5 : (∫ y in Z, (∫ v in shape 𝔪.m U y,
              uA.indicator (1 : X3 → ℝ) (v • y) ∂(ν y)) /
                (ν y (shape 𝔪.m U y)).toReal ∂μ)
        = ∫ y in Z, (∫ v in shape 𝔪.m U y,
              A.indicator (1 : X3 → ℝ) (v • y) ∂(ν y)) /
                (ν y (shape 𝔪.m U y)).toReal ∂μ :=
      integral_congr_ae (hφae.mono fun y hy => by
        show (∫ v in shape 𝔪.m U y, uA.indicator (1 : X3 → ℝ) (v • y) ∂(ν y))
              / ((ν y) (shape 𝔪.m U y)).toReal
            = (∫ v in shape 𝔪.m U y, A.indicator (1 : X3 → ℝ) (v • y) ∂(ν y))
              / ((ν y) (shape 𝔪.m U y)).toReal
        rw [hy])
    rw [← h1, h3, h5, ← h4, h2]
  have hrealA : (μ uA).toReal = ∫ y in Z, uA.indicator (1 : X3 → ℝ) y ∂μ := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.integral_indicator_one huAmeas]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      show uA.indicator (1 : X3 → ℝ) y = 0
      exact Set.indicator_of_notMem (fun h => hy (huA_Z h)) (1 : X3 → ℝ))).symm
  have hrealB : (μ A).toReal = ∫ y in Z, A.indicator (1 : X3 → ℝ) y ∂μ := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.integral_indicator_one hAmeas]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      show A.indicator (1 : X3 → ℝ) y = 0
      exact Set.indicator_of_notMem (fun h => hy (hAZ h)) (1 : X3 → ℝ))).symm
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ uA) (measure_ne_top μ A),
    hrealA, hrealB, hIntEq]

/-! ## Globalization -/

/-- **Globalization.**  If countably many measurable "good" sets `Θ n` cover `X₃` up to a null set
and every measurable subset of `Θ n` has `u`-invariant `μ`-mass, then `μ` is preserved by
`x ↦ u • x`. -/
theorem measurePreserving_of_countable_good {u : SL3} (Θ : ℕ → Set X3)
    (hmeas : ∀ n, MeasurableSet (Θ n))
    (hgood : ∀ n, ∀ A : Set X3, MeasurableSet A → A ⊆ Θ n →
      μ ((fun y : X3 => u • y) '' A) = μ A)
    (hcover : μ (⋃ n, Θ n)ᶜ = 0) :
    MeasurePreserving (fun x : X3 => u • x) μ μ := by
  classical
  set Θ' : ℕ → Set X3 := fun n => Θ n \ ⋃ k ∈ Finset.range n, Θ k with hΘ'def
  have hΘ'meas : ∀ n, MeasurableSet (Θ' n) := fun n =>
    (hmeas n).diff (Finset.measurableSet_biUnion _ fun k _ => hmeas k)
  have hΘ'sub : ∀ n, Θ' n ⊆ Θ n := fun n => Set.sdiff_subset
  have hdisj : Pairwise (fun m n => Disjoint (Θ' m) (Θ' n)) := by
    intro m n hmn
    refine Set.disjoint_left.mpr fun x hxm hxn => ?_
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hxn.2 (Set.mem_biUnion (Finset.mem_range.mpr h) hxm.1)
    · exact hxm.2 (Set.mem_biUnion (Finset.mem_range.mpr h) hxn.1)
  have hgood' : ∀ n, ∀ A : Set X3, MeasurableSet A → A ⊆ Θ' n →
      μ ((fun y : X3 => u • y) '' A) = μ A := fun n A hA hAsub =>
    hgood n A hA (fun a ha => hΘ'sub n (hAsub ha))
  have himg_meas : ∀ A : Set X3, MeasurableSet A →
      MeasurableSet ((fun x : X3 => u • x) '' A) := by
    intro A hA
    rw [smul_image_eq_preimage u A]
    exact hA.preimage (by fun_prop : Measurable fun z : X3 => u⁻¹ • z)
  set M : Set X3 := ⋃ n, Θ' n with hMdef
  have hMmeas : MeasurableSet M := MeasurableSet.iUnion hΘ'meas
  have hMsub : M ⊆ ⋃ n, Θ n :=
    Set.iUnion_subset fun n => Set.Subset.trans (hΘ'sub n) (Set.subset_iUnion _ n)
  have hunion : (⋃ n, Θ' n) = ⋃ n, Θ n := by
    refine le_antisymm (Set.iUnion_subset fun n =>
      Set.Subset.trans (hΘ'sub n) (Set.subset_iUnion _ n)) ?_
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    have hex : ∃ k, x ∈ Θ k := ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro hcon
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hcon
    obtain ⟨hkr, hxk⟩ := Set.mem_iUnion.mp hk
    have h1 : Nat.find hex ≤ k := Nat.find_min' hex hxk
    have h2 : k < Nat.find hex := Finset.mem_range.mp hkr
    omega
  have hMnull : μ Mᶜ = 0 := by
    rw [hMdef, hunion]
    exact hcover
  have hMu : μ ((fun x : X3 => u • x) '' M) = μ M := by
    have hdisj' : Pairwise (fun m n => Disjoint ((fun x : X3 => u • x) '' Θ' m)
        ((fun x : X3 => u • x) '' Θ' n)) := fun m n hmn => disjoint_image_smul (hdisj hmn)
    rw [hMdef, Set.image_iUnion,
      MeasureTheory.measure_iUnion hdisj' (fun n => himg_meas _ (hΘ'meas n)),
      MeasureTheory.measure_iUnion hdisj hΘ'meas]
    congr 1
    funext n
    exact hgood' n _ (hΘ'meas n) (Set.Subset.refl _)
  have hMnull_u : μ ((fun x : X3 => u • x) '' Mᶜ) = 0 := by
    have hcompl : ((fun x : X3 => u • x) '' M)ᶜ = (fun x : X3 => u • x) '' Mᶜ :=
      (smul_image_compl u M).symm
    have hMu_one : μ ((fun x : X3 => u • x) '' M) = 1 := by
      rw [hMu]
      have hsum := MeasureTheory.measure_add_measure_compl (μ := μ) hMmeas
      rw [hMnull, add_zero, MeasureTheory.measure_univ] at hsum
      exact hsum
    rw [← hcompl, MeasureTheory.measure_compl (himg_meas M hMmeas) (measure_ne_top μ _),
      hMu_one, MeasureTheory.measure_univ, tsub_self]
  have hgoodM : ∀ A : Set X3, MeasurableSet A →
      μ ((fun x : X3 => u • x) '' (A ∩ M)) = μ (A ∩ M) := by
    intro A hA
    have hdisj'' : Pairwise (fun m n => Disjoint ((fun x : X3 => u • x) '' (A ∩ Θ' m))
        ((fun x : X3 => u • x) '' (A ∩ Θ' n))) :=
      fun m n hmn => disjoint_image_smul ((hdisj hmn).mono Set.inter_subset_right Set.inter_subset_right)
    have hdisjA : Pairwise (fun m n => Disjoint (A ∩ Θ' m) (A ∩ Θ' n)) :=
      fun m n hmn => (hdisj hmn).mono Set.inter_subset_right Set.inter_subset_right
    rw [show A ∩ M = ⋃ n, A ∩ Θ' n from by rw [hMdef, Set.inter_iUnion], Set.image_iUnion,
      MeasureTheory.measure_iUnion hdisj'' (fun n => himg_meas _ (hA.inter (hΘ'meas n))),
      MeasureTheory.measure_iUnion hdisjA (fun n => hA.inter (hΘ'meas n))]
    congr 1
    funext n
    exact hgood' n _ (hA.inter (hΘ'meas n)) Set.inter_subset_right
  have hMS : ∀ S : Set X3, MeasurableSet S → μ (S ∩ M) = μ S := by
    intro S hS
    refine le_antisymm (MeasureTheory.measure_mono Set.inter_subset_left) ?_
    have hsplit : S ⊆ (S ∩ M) ∪ (S ∩ Mᶜ) := by
      intro x hx
      by_cases h : x ∈ M
      · exact Set.mem_union_left _ ⟨hx, h⟩
      · exact Set.mem_union_right _ ⟨hx, h⟩
    have h2 : μ (S ∩ Mᶜ) = 0 :=
      MeasureTheory.measure_mono_null Set.inter_subset_right hMnull
    calc μ S ≤ μ ((S ∩ M) ∪ (S ∩ Mᶜ)) := MeasureTheory.measure_mono hsplit
      _ ≤ μ (S ∩ M) + μ (S ∩ Mᶜ) := MeasureTheory.measure_union_le _ _
      _ = μ (S ∩ M) + 0 := by rw [h2]
      _ = μ (S ∩ M) := add_zero _
  have hmain : ∀ S : Set X3, MeasurableSet S → μ ((fun x : X3 => u • x) '' S) = μ S := by
    intro S hS
    have hdecomp : S = (S ∩ M) ∪ (S ∩ Mᶜ) := by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ M
        · exact Set.mem_union_left _ ⟨hx, h⟩
        · exact Set.mem_union_right _ ⟨hx, h⟩
      · rintro (h | h)
        · exact h.1
        · exact h.1
    have hsub2 : (fun x : X3 => u • x) '' (S ∩ Mᶜ) ⊆ (fun x : X3 => u • x) '' Mᶜ :=
      Set.image_mono Set.inter_subset_right
    have hzero : μ ((fun x : X3 => u • x) '' (S ∩ Mᶜ)) = 0 :=
      MeasureTheory.measure_mono_null hsub2 hMnull_u
    have himage : (fun x : X3 => u • x) '' S
        = (fun x : X3 => u • x) '' (S ∩ M) ∪ (fun x : X3 => u • x) '' (S ∩ Mᶜ) := by
      rw [← Set.image_union, ← hdecomp]
    refine le_antisymm ?_ ?_
    · calc μ ((fun x : X3 => u • x) '' S)
          = μ ((fun x : X3 => u • x) '' (S ∩ M) ∪ (fun x : X3 => u • x) '' (S ∩ Mᶜ)) := by
            rw [himage]
        _ ≤ μ ((fun x : X3 => u • x) '' (S ∩ M))
              + μ ((fun x : X3 => u • x) '' (S ∩ Mᶜ)) := MeasureTheory.measure_union_le _ _
        _ = μ (S ∩ M) + 0 := by rw [hgoodM S hS, hzero]
        _ = μ S := by rw [add_zero, hMS S hS]
    · calc μ S = μ (S ∩ M) := (hMS S hS).symm
        _ = μ ((fun x : X3 => u • x) '' (S ∩ M)) := (hgoodM S hS).symm
        _ ≤ μ ((fun x : X3 => u • x) '' S) :=
            MeasureTheory.measure_mono (Set.image_mono Set.inter_subset_left)
  refine ⟨(by fun_prop : Measurable fun x : X3 => u • x), ?_⟩
  ext A hA
  rw [MeasureTheory.Measure.map_apply (by fun_prop : Measurable fun x : X3 => u • x) hA]
  have hpre : (fun x : X3 => u • x) ⁻¹' A = (fun z : X3 => u⁻¹ • z) '' A := by
    ext z
    constructor
    · intro hz
      exact ⟨u • z, hz, by
        show u⁻¹ • (u • z) = z
        rw [inv_smul_smul]⟩
    · rintro ⟨b, hb, rfl⟩
      show u • (u⁻¹ • b) ∈ A
      rwa [smul_inv_smul]
  rw [hpre]
  have hmeas' : MeasurableSet ((fun z : X3 => u⁻¹ • z) '' A) := by
    rw [show (fun z : X3 => u⁻¹ • z) '' A = (fun z : X3 => u • z) ⁻¹' A from hpre.symm]
    exact hA.preimage (by fun_prop : Measurable fun z : X3 => u • z)
  have heq : (fun x : X3 => u • x) '' ((fun z : X3 => u⁻¹ • z) '' A) = A := by
    ext z
    constructor
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      show u • (u⁻¹ • a) ∈ A
      rwa [smul_inv_smul]
    · intro hz
      exact ⟨u⁻¹ • z, ⟨z, hz, rfl⟩, by
        show u • (u⁻¹ • z) = z
        rw [smul_inv_smul]⟩
  have hmain' := hmain ((fun z : X3 => u⁻¹ • z) '' A) hmeas'
  rw [show (fun x : X3 => u • x) '' ((fun z : X3 => u⁻¹ • z) '' A) = A from heq] at hmain'
  exact hmain'.symm

/-! ## The geometric flower input

The following is the countable family of plaque algebras with big atoms (Pisa Cor. 6.15),
assembled from the local flower `Work.EKLRelCross.local_flower` over a countable basis of `X₃`. -/

/-- The empty set carries a plaque algebra: all the pointwise axioms are vacuous. -/
lemma isPlaqueAlgebra_empty (U : Subgroup SL3) :
    IsPlaqueAlgebra U (∅ : Set X3) (⊥ : MeasurableSpace X3) := by
  refine ⟨bot_le, ?_, ?_, ?_⟩
  · exact ⟨∅, Set.countable_empty, MeasurableSpace.generateFrom_empty.symm⟩
  · exact @MeasurableSet.empty X3 ⊥
  · intro x hx
    exact absurd hx (Set.notMem_empty x)

/-- **Big-atom flowers** (Pisa Cor. 6.15): countably many plaque algebras with measurable bases
covering `X₃` up to a null set, whose shapes contain the whole `R`-plaque at every point of the
base. -/
theorem bigAtoms_flowers (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      μ (⋃ n, G n)ᶜ = 0 ∧
      (∀ n, ∀ x ∈ G n, V R ∩ (U : Set SL3) ⊆ shape (m n) U x) := by
  classical
  have hfree_ae : ∀ᵐ x ∂μ, ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
    filter_upwards [Work.EKLRelCross.ae_free_orbit h2 μ U hU t0 ht0 hcontr] with x hx
    intro u₁ h₁ u₂ h₂ heq
    have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
    have h1 : u₂⁻¹ * u₁ = 1 := hx _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
    calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
      _ = u₂ := by rw [h1, mul_one]
  have hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s :=
    Work.EKLC7.ae_isOpen_pos (μ := μ)
  set S : Set X3 := {x | (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) ∧
    (∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s)} with hSdef
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hfree_ae, hpos] with x h1 h2
    exact ⟨h1, h2⟩
  have hloc : ∀ x : S, ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧ @MeasurableSet X3 instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      IsPlaqueAlgebra U Z m ∧ (x : X3) ∈ G ∧
      O ∩ {y | ∀ u ∈ U, u • y = y → u = 1} ⊆ G ∧
      ∀ y ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U y :=
    fun x => Work.EKLRelCross.local_flower h2 hU (x : X3) x.2.1 R hR
  choose Zf mf Gf Of hOfopen hxO hGmeas hGsub hplaq hxG hOG hshape using hloc
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  let sel : ℕ → Option S := fun n =>
    if h : ∃ s : S, basis n ⊆ Of s then some h.choose else none
  have hsel_sub : ∀ n (s : S), sel n = some s → basis n ⊆ Of s := by
    intro n s hs
    by_cases h : ∃ s : S, basis n ⊆ Of s
    · have hval : sel n = some h.choose := by
        show (if h' : ∃ s : S, basis n ⊆ Of s then some h'.choose else none) = some h.choose
        rw [dif_pos h]
      rw [hval] at hs
      have hsc : h.choose = s := Option.some.inj hs
      rw [← hsc]
      exact h.choose_spec
    · have hval : sel n = none := by
        show (if h' : ∃ s : S, basis n ⊆ Of s then some h'.choose else none) = none
        rw [dif_neg h]
      rw [hval] at hs
      exact absurd hs (by simp)
  let Zn : ℕ → Set X3 := fun n => (sel n).elim (∅ : Set X3) Zf
  let Gn : ℕ → Set X3 := fun n => (sel n).elim (∅ : Set X3) Gf
  let mn : ℕ → MeasurableSpace X3 := fun n => (sel n).elim (⊥ : MeasurableSpace X3) mf
  have hZn : ∀ n, Zn n = (sel n).elim (∅ : Set X3) Zf := fun n => rfl
  have hGn : ∀ n, Gn n = (sel n).elim (∅ : Set X3) Gf := fun n => rfl
  have hmn : ∀ n, mn n = (sel n).elim (⊥ : MeasurableSpace X3) mf := fun n => rfl
  refine ⟨Zn, Gn, mn, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hs : sel n with _ | s
    · have hmn0 : mn n = (⊥ : MeasurableSpace X3) := by rw [hmn n, hs]; rfl
      have hZn0 : Zn n = (∅ : Set X3) := by rw [hZn n, hs]; rfl
      rw [hmn0, hZn0]
      exact isPlaqueAlgebra_empty U
    · have hZn1 : Zn n = Zf s := by rw [hZn n, hs]; rfl
      have hmn1 : mn n = mf s := by rw [hmn n, hs]; rfl
      rw [hZn1, hmn1]
      exact hplaq s
  · intro n
    rcases hs : sel n with _ | s
    · have hG : Gn n = (∅ : Set X3) := by rw [hGn n, hs]; rfl
      have hZ : Zn n = (∅ : Set X3) := by rw [hZn n, hs]; rfl
      rw [hG, hZ]
      exact ⟨MeasurableSet.empty, Set.Subset.refl _⟩
    · have hG : Gn n = Gf s := by rw [hGn n, hs]; rfl
      have hZ : Zn n = Zf s := by rw [hZn n, hs]; rfl
      rw [hG, hZ]
      exact ⟨hGmeas s, hGsub s⟩
  · have hcover : ∀ᵐ y ∂μ, y ∈ ⋃ n, Gn n := by
      filter_upwards [hSae] with y hyS
      have hyO : y ∈ Of ⟨y, hyS⟩ := hxO ⟨y, hyS⟩
      obtain ⟨t, htB, hyt, hts⟩ := hbas.exists_subset_of_mem_open hyO (hOfopen ⟨y, hyS⟩)
      obtain ⟨n, rfl⟩ := htB
      have hhex : ∃ s : S, basis n ⊆ Of s := ⟨⟨y, hyS⟩, hts⟩
      have hval : sel n = some hhex.choose := by
        show (if h' : ∃ s : S, basis n ⊆ Of s then some h'.choose else none) = some hhex.choose
        rw [dif_pos hhex]
      have hyfree : y ∈ {z : X3 | ∀ u ∈ U, u • z = z → u = 1} := by
        intro u hu huy
        exact hyS.1 u hu 1 U.one_mem (by rw [huy, one_smul])
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      have hGn' : Gn n = Gf hhex.choose := by rw [hGn n, hval]; rfl
      rw [hGn']
      exact hOG hhex.choose ⟨hsel_sub n hhex.choose hval hyt, hyfree⟩
    have h := MeasureTheory.ae_iff.mp hcover
    simpa [Set.compl_def] using h
  · intro n y hy
    rcases hs : sel n with _ | s
    · have hG : Gn n = (∅ : Set X3) := by rw [hGn n, hs]; rfl
      rw [hG] at hy
      exact absurd hy (Set.notMem_empty y)
    · have hG : Gn n = Gf s := by rw [hGn n, hs]; rfl
      have hZ : Zn n = Zf s := by rw [hZn n, hs]; rfl
      have hmn' : mn n = mf s := by rw [hmn n, hs]; rfl
      rw [hG] at hy
      have hgoal := hshape s y hy
      rw [hmn']
      exact hgoal

/-! ## The main theorem -/

/-- **The target theorem**, derived from the geometric flower input. -/
theorem local_invariance_of_ae_haar_of_flowers
    (hgeom : ∀ R : ℝ, 0 < R → ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      μ (⋃ n, G n)ᶜ = 0 ∧
      (∀ n, ∀ x ∈ G n, V R ∩ (U : Set SL3) ⊆ shape (m n) U x))
    (h2 : P_X3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hL : IsLeafwise μ U ν X') (hae : Work.EKLRelCross.AeHaar μ U ν) :
    ∃ ε > 0, ∀ u ∈ U, u ∈ V ε → MeasurePreserving (fun x : X3 => u • x) μ μ := by
  refine ⟨1 / 4, by norm_num, fun u hu huV => ?_⟩
  obtain ⟨Z, G, m, hpla, hG, hcov, hshp⟩ := hgeom 1 (by norm_num)
  have huV1 : u ∈ V 1 ∩ (U : Set SL3) :=
    ⟨fun i j => lt_trans (huV i j) (by norm_num), hu⟩
  refine measurePreserving_of_countable_good (μ := μ) (u := u)
    (fun n : ℕ => {y : X3 | y ∈ Z n ∧ u • y ∈ atom (m n) y}) ?_ ?_ ?_
  · intro n
    have h1 : MeasurableSet {y : X3 | u • y ∈ atom (m n) y} :=
      Work.EKLComp.measurableSet_smul_mem_atom ⟨m n⟩ (hpla n).1 (hpla n).2.1 u
    exact ((hpla n).1 _ (hpla n).2.2.1).inter h1
  · intro n A hA hAsub
    exact good_of_atom (μ := μ) hU hL hae hu (⟨m n⟩ : Work.EKLComp.SigAlg) (hpla n) hA
      (fun a ha => ⟨(hAsub ha).1, (hAsub ha).2⟩)
  · have hsub : (⋃ n, G n) ⊆ (⋃ n : ℕ, {y : X3 | y ∈ Z n ∧ u • y ∈ atom (m n) y}) := by
      intro x hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n, (hG n).2 hxn, (hshp n x hxn huV1).2⟩
    exact MeasureTheory.measure_mono_null (Set.compl_subset_compl.mpr hsub) hcov

/-- **Local invariance of `μ` under the `U`-action from a.e. Haar leafwise measures**
(Pisa 6.27, direction `⟸`).

If the leafwise measures of `(μ, U)` are `μ`-a.e. right-`U`-invariant, then `μ` is preserved by
every `u ∈ U` sufficiently close to `1`.  The proof takes the geometric flower input
(`bigAtoms_flowers`, Pisa Cor. 6.15), the local goodness `good_of_atom` and the globalization
`measurePreserving_of_countable_good`. -/
theorem local_invariance_of_ae_haar (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hae : Work.EKLRelCross.AeHaar μ U ν) :
    ∃ ε > 0, ∀ u ∈ U, u ∈ Work.EKLContract.V ε →
      MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => u • x) μ μ := by
  exact local_invariance_of_ae_haar_of_flowers
    (fun R hR => bigAtoms_flowers h2 μ U hU t0 ht0 hcontr R hR) h2 hU t0 ht0 hcontr hL hae

end Work.EKLUInv
