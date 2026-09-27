import Mathlib
import Submission.Work.EKLC7.LeafNuGood
import Submission.Work.EKLC7.LeafNuFields
import Submission.Work.EKLC7.LeafOrbImgTools

/-!
# `Work.EKLC7.measurable_nu` — measurability of the patched leafwise measures

The patched family `F.nu coord X' : X₃ → Measure SL₃(ℝ)` built in
`Submission/Work/EKLC7/LeafNuDefs.lean` from a family of flowers `F : FlowerFam U μ` is *weakly
measurable*: for every compactly supported continuous `f : SL₃(ℝ) → ℝ` the function
`x ↦ ∫ g, f g ∂(F.nu coord X' x)` is measurable.  This is the `measurable` field of
`Work.EKLContract.IsLeafwise` for this family (Pisa Theorem 6.3(vi)).

## The shape of the argument

`F.nu coord X' x` is `F.raw coord x` on the good set `X'` and the Dirac mass at `1` outside it, and

`F.raw coord x = Measure.sum (fun n => F.trm coord n x)`,
`F.trm coord n x = (F.dd n x)⁻¹ • ((F.kap n x).map (coord x)).restrict (Ann U n)`.

* The compact support of `f` meets only finitely many annuli: if `N` is such that
  `tsupport f ∩ U ⊆ Blk U N`, then for `n > N` the measure `F.trm coord n x` is carried by
  `Ann U n`, where `f` vanishes, so `∫ f ∂(F.trm coord n x) = 0`.  Consequently `f` is integrable
  for `F.raw coord x` at every point of `X'` (each annulus term is a finite measure and the
  sequence of norms is finitely supported), and
  `∫ f ∂(F.raw coord x) = ∑_{n ≤ N} ∫ f ∂(F.trm coord n x)`.
* Each annulus term is measurable.  On the measurable piece `{x | F.chose n x = j}` the chosen
  flower is the fixed `j`-th flower, and the term equals the *fixed-`j`* expression

  `((F.ddAt j x)⁻¹).toReal * ∫ y, (Ann U n).indicator (fun g => f g) (coord x y) ∂(F.kappa j x)`

  (`trm_eq_glue`), a product of two measurable functions: the first because
  `F.ddAt j x = (F.kappa j x) ((· • x) '' Box1 U)` is the mass of the *moving* plaque
  `(· • x) '' Box1 U`, which is measurable by `Work.EKLC7.OrbImgTools.measurable_kernel_orbImg`, and the
  second because it is the integral of a jointly measurable function against the fixed kernel
  `F.kappa j` (`StronglyMeasurable.integral_kernel_prod_right`).
* Finally the whole function is the `if x ∈ X' then (finite sum) else f 1` of two measurable
  functions.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Classical
open ProbabilityTheory (Kernel)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC7

open Work.EKLContract Work.EKLComp

variable {U : Subgroup SL3} {μ : Measure X3}

/-! ## 0. The conditional kernel with the ambient σ-algebra as source

`F.kappa j x = condExpKernel (μ.restrict (F.Z j)) (F.m j) x` is a kernel whose *source*
σ-algebra is the plaque algebra `F.m j`, not the Borel σ-algebra of `X₃`.  The measurability
inputs (`StronglyMeasurable.integral_kernel_prod_right`,
`Work.EKLC7.OrbImgTools.measurable_kernel_orbImg`) are stated for kernels with a fixed source
σ-algebra, so we transport `F.kappa j` to the ambient σ-algebra along the identity — which is
measurable because `F.m j ≤ Borel X₃`, the first field of `IsPlaqueAlgebra`. -/

/-- The conditional kernel of the `j`-th flower, seen as a kernel with the ambient (Borel)
σ-algebra on its source. -/
noncomputable def kappaK (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) : Kernel X3 X3 :=
  @Kernel.comap X3 X3 (F.m j) (borel X3) X3 (borel X3)
    (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict (F.Z j)) (F.m j))
    id (measurable_id'' (F.big j).1.1)

theorem kappaK_apply (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) (x : X3) :
    kappaK F j x = F.kappa j x := by
  rw [kappaK, Kernel.comap_apply]
  rfl

theorem isFiniteMeasure_kappaK (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) (x : X3) :
    IsFiniteMeasure (kappaK F j x) := by
  rw [kappaK_apply]
  show IsFiniteMeasure (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
    (μ.restrict (F.Z j)) (F.m j) x)
  infer_instance

instance instIsSFiniteKernel_kappaK (F : FlowerFam U μ) [IsFiniteMeasure μ] (j : ℕ) :
    ProbabilityTheory.IsSFiniteKernel (kappaK F j) := by
  rw [show kappaK F j = @Kernel.comap X3 X3 (F.m j) (borel X3) X3 (borel X3)
    (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict (F.Z j)) (F.m j))
    id (measurable_id'' (F.big j).1.1) from rfl]
  exact @Kernel.IsSFiniteKernel.comap X3 X3 (F.m j) (borel X3) X3 (borel X3) id
    (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict (F.Z j)) (F.m j))
    inferInstance (measurable_id'' (F.big j).1.1)

/-! ## 1. Measurability of the normalising constants -/

/-- `Box1 U` is contained in `U`, so its orbit image is the plaque `(· • x) '' Box1 U`. -/
theorem orbImg_box1 (x : X3) :
    Work.EKLC7.OrbImgTools.orbImg U x (Box1 U) = (fun g : SL3 => g • x) '' (Box1 U) := by
  rw [Work.EKLC7.OrbImgTools.orbImg, Set.inter_eq_left.mpr (fun g hg => hg.1)]

/-- The mass of the moving plaque `(· • x) '' Box1 U` under the `j`-th conditional kernel is
measurable in `x`; this is the normalising constant `F.ddAt j` of the `j`-th flower. -/
theorem meas_ddAt (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ) [IsFiniteMeasure μ]
    (j : ℕ) : Measurable fun x => F.ddAt j x := by
  have h := Work.EKLC7.OrbImgTools.measurable_kernel_orbImg (U := U) hUcl (kappaK F j)
    (fun x => isFiniteMeasure_kappaK F j x) (Work.EKLC7.OrbImgTools.isCompact_box1 U hUcl)
  rw [show (fun x => F.ddAt j x)
      = fun x => kappaK F j x (Work.EKLC7.OrbImgTools.orbImg U x (Box1 U)) from by
    funext x
    rw [FlowerFam.ddAt, kappaK_apply, orbImg_box1]]
  exact h

/-! ## 2. Measurability of the annulus integral against the fixed kernel -/

/-- The integral of the annulus-truncated test function against the `j`-th conditional kernel is
measurable in the base point. -/
theorem meas_kernelIntegral (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsFiniteMeasure μ] (coord : X3 → X3 → SL3)
    (hcoordm : Measurable fun p : X3 × X3 => coord p.1 p.2)
    (n j : ℕ) (f : CompactlySupportedContinuousMap SL3 ℝ) :
    Measurable fun x => ∫ y, (Ann U n).indicator (fun g : SL3 => f g) (coord x y)
      ∂(F.kappa j x) := by
  have hg : StronglyMeasurable (fun g : SL3 => (Ann U n).indicator (fun h : SL3 => f h) g) :=
    (f.continuous.stronglyMeasurable).indicator (Work.EKLC7.measurableSet_Ann hUcl n)
  have hsm : StronglyMeasurable (Function.uncurry (fun (x y : X3) =>
      (Ann U n).indicator (fun g : SL3 => f g) (coord x y))) := hg.comp_measurable hcoordm
  have hmain := (StronglyMeasurable.integral_kernel_prod_right (κ := kappaK F j) hsm).measurable
  convert hmain using 1
  ext x
  rw [kappaK_apply]

/-! ## 3. The measurable pieces `{x | F.chose n x = j}` -/

/-- The part of the `i`-th base consisting of flowers of radius at least `n + 2`. -/
def admE (F : FlowerFam U μ) (n i : ℕ) : Set X3 :=
  if ((n : ℝ) + 2 ≤ F.R i) then F.E i else ∅

theorem mem_admE {F : FlowerFam U μ} {n i : ℕ} {x : X3} :
    x ∈ admE F n i ↔ x ∈ F.E i ∧ (n : ℝ) + 2 ≤ F.R i := by
  by_cases h : (n : ℝ) + 2 ≤ F.R i
  · rw [admE, if_pos h]
    exact ⟨fun hx => ⟨hx, h⟩, fun hx => hx.1⟩
  · rw [admE, if_neg h]
    exact ⟨fun hx => absurd hx (Set.notMem_empty x), fun hx => absurd hx.2 h⟩

theorem measurableSet_admE (F : FlowerFam U μ) (n i : ℕ) : MeasurableSet (admE F n i) := by
  by_cases h : (n : ℝ) + 2 ≤ F.R i
  · rw [admE, if_pos h]; exact F.measE i
  · rw [admE, if_neg h]; exact MeasurableSet.empty

/-- `Nat.find` over the admissible bases computes `F.chose`. -/
theorem chose_eq (F : FlowerFam U μ) (n : ℕ) (x : X3) :
    F.chose n x = if h : ∃ i, x ∈ admE F n i then Nat.find h else 0 := by
  rw [FlowerFam.chose]
  by_cases h : ∃ j, x ∈ F.E j ∧ (n : ℝ) + 2 ≤ F.R j
  · have h' : ∃ i, x ∈ admE F n i := ⟨h.choose, mem_admE.mpr h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    exact le_antisymm (Nat.find_le (h := h) (mem_admE.mp (Nat.find_spec h')))
      (Nat.find_le (h := h') (mem_admE.mpr (Nat.find_spec h)))
  · have h' : ¬ ∃ i, x ∈ admE F n i := fun hh => h ⟨hh.choose, mem_admE.mp hh.choose_spec⟩
    rw [dif_neg h, dif_neg h']

/-- **The set on which the `n`-th chosen flower is the `j`-th flower is Borel.** -/
theorem measurableSet_chose_eq (F : FlowerFam U μ) (n j : ℕ) :
    MeasurableSet {x : X3 | F.chose n x = j} := by
  cases j with
  | zero =>
    have key : {x : X3 | F.chose n x = 0} = admE F n 0 ∪ (⋃ i, admE F n i)ᶜ := by
      ext x
      rw [Set.mem_ofPred_eq, chose_eq F n x]
      by_cases h : ∃ i, x ∈ admE F n i
      · rw [dif_pos h]
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
        rw [Nat.find_eq_zero]
        exact ⟨fun h0 => Or.inl h0, fun hc => hc.elim id (fun hno => absurd h hno)⟩
      · rw [dif_neg h]
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
        exact ⟨fun _ => Or.inr h, fun _ => trivial⟩
    rw [key]
    exact MeasurableSet.union (measurableSet_admE F n 0)
      (MeasurableSet.compl (MeasurableSet.iUnion fun i => measurableSet_admE F n i))
  | succ j =>
    have key : {x : X3 | F.chose n x = j + 1}
        = admE F n (j+1) ∩ (⋂ (i : ℕ) (_ : i < j + 1), (admE F n i)ᶜ) := by
      ext x
      rw [Set.mem_ofPred_eq, chose_eq F n x]
      by_cases h : ∃ i, x ∈ admE F n i
      · rw [dif_pos h, Nat.find_eq_iff h]
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      · rw [dif_neg h]
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
        exact ⟨fun hc => absurd hc (by omega),
          fun hc => absurd hc.1 (fun hmem => h ⟨j + 1, hmem⟩)⟩
    rw [key]
    exact MeasurableSet.inter (measurableSet_admE F n (j+1))
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        (measurableSet_admE F n i).compl)

/-- **Gluing lemma.**  A function which agrees on every member of a countable measurable cover
with a measurable function is measurable. -/
theorem measurable_of_pieces {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ι : Sort*}
    [Countable ι] {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (g : α → β) (gl : ι → α → β)
    (hgl : ∀ i, Measurable (gl i)) (hcover : ∀ x, ∃ i, x ∈ A i)
    (h : ∀ i, ∀ x ∈ A i, g x = gl i x) : Measurable g := by
  intro s hs
  have hpre : g ⁻¹' s = ⋃ i, (A i ∩ (gl i) ⁻¹' s) := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hcover x
      exact ⟨i, hi, by change gl i x ∈ s; rw [← h i x hi]; exact hx⟩
    · rintro ⟨i, hi, hx⟩
      change g x ∈ s
      rw [h i x hi]
      exact hx
  rw [hpre]
  exact MeasurableSet.iUnion fun i => (hA i).inter (hgl i hs)

/-! ## 4. The fixed-`j` annulus term, and the identity on the pieces -/

/-- The fixed-`j` version of the `n`-th annulus term: the `j`-th conditional measure, pushed to
the group by the leaf coordinate and normalised by the `j`-th normalising constant. -/
noncomputable def glue (F : FlowerFam U μ) [IsFiniteMeasure μ]
    (coord : X3 → X3 → SL3) (n j : ℕ) (f : CompactlySupportedContinuousMap SL3 ℝ) (x : X3) : ℝ :=
  ((F.ddAt j x)⁻¹).toReal
    * ∫ y, (Ann U n).indicator (fun g : SL3 => f g) (coord x y) ∂(F.kappa j x)

/-- On the piece where the chosen flower is the `j`-th one, the `n`-th annulus term is `glue`. -/
theorem trm_eq_glue (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ) [IsFiniteMeasure μ]
    (coord : X3 → X3 → SL3) (hcoordm : Measurable fun p : X3 × X3 => coord p.1 p.2)
    (n j : ℕ) (f : CompactlySupportedContinuousMap SL3 ℝ) {x : X3} (hx : F.chose n x = j) :
    (∫ g, f g ∂(F.trm coord n x)) = glue F coord n j f x := by
  have hdd : F.dd n x = F.ddAt j x := by rw [F.dd_eq_ddAt, hx]
  have hprp : F.prp coord n x = (F.kappa j x).map (coord x) := by rw [F.prp_eq, hx]
  have hg : StronglyMeasurable (fun g : SL3 => (Ann U n).indicator (fun h : SL3 => f h) g) :=
    (f.continuous.stronglyMeasurable).indicator (Work.EKLC7.measurableSet_Ann hUcl n)
  have hm : Measurable (fun y : X3 => coord x y) :=
    hcoordm.comp (measurable_const.prodMk measurable_id)
  rw [glue, FlowerFam.trm, hdd, hprp, MeasureTheory.integral_smul_measure,
    ← MeasureTheory.integral_indicator (Work.EKLC7.measurableSet_Ann hUcl n)]
  congr 1
  exact MeasureTheory.integral_map hm.aemeasurable hg.aestronglyMeasurable

/-- **Each annulus term is measurable.** -/
theorem meas_term (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ) [IsFiniteMeasure μ]
    (coord : X3 → X3 → SL3) (hcoordm : Measurable fun p : X3 × X3 => coord p.1 p.2)
    (n : ℕ) (f : CompactlySupportedContinuousMap SL3 ℝ) :
    Measurable fun x => ∫ g, f g ∂(F.trm coord n x) := by
  refine measurable_of_pieces (A := fun j : ℕ => {x : X3 | F.chose n x = j})
    (fun j => measurableSet_chose_eq F n j) _ (fun j => glue F coord n j f) ?_ ?_ ?_
  · intro j
    exact ((meas_ddAt hUcl F j).inv.ennreal_toReal).mul
      (meas_kernelIntegral hUcl F coord hcoordm n j f)
  · intro x
    exact ⟨F.chose n x, rfl⟩
  · intro j x hx
    exact trm_eq_glue hUcl F coord hcoordm n j f hx

/-! ## 5. Vanishing of the far-away annulus terms -/

/-- **The annulus term vanishes beyond the support of the test function.**  If `tsupport f ∩ U` is
contained in `Blk U N` and `n > N`, then `F.trm coord n x` is carried by `Ann U n`, where `f`
vanishes, so the integral is `0`. -/
theorem trm_integral_eq_zero (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (n : ℕ)
    (f : CompactlySupportedContinuousMap SL3 ℝ) {N : ℕ}
    (hN : tsupport (fun g : SL3 => f g) ∩ (U : Set SL3) ⊆ Blk U N) (hn : N < n) (x : X3) :
    ∫ g, f g ∂(F.trm coord n x) = 0 := by
  have hAnn : MeasurableSet (Ann U n) := Work.EKLC7.measurableSet_Ann hUcl n
  have hcompl : (F.trm coord n x) (Ann U n)ᶜ = 0 := by
    rw [FlowerFam.trm, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hAnn.compl]
    have : (Ann U n)ᶜ ∩ Ann U n = ∅ := Set.compl_inter_self _
    rw [this, measure_empty, mul_zero]
  have hae : (fun g : SL3 => f g) =ᵐ[F.trm coord n x] 0 := by
    show ∀ᵐ g ∂(F.trm coord n x), f g = 0
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun y hy => ?_) hcompl
    simp only [Set.mem_ofPred_eq] at hy
    intro hyAnn
    exact hy (image_eq_zero_of_notMem_tsupport (f := fun g : SL3 => f g) fun hts =>
      Set.disjoint_left.mp (Ann_disjoint_Blk U hn) hyAnn
        (hN ⟨hts, Ann_subset_U U n hyAnn⟩))
  rw [MeasureTheory.integral_congr_ae hae]
  simp

/-- The norm version of `trm_integral_eq_zero`. -/
theorem trm_norm_integral_eq_zero (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsFiniteMeasure μ] (coord : X3 → X3 → SL3) (n : ℕ)
    (f : CompactlySupportedContinuousMap SL3 ℝ) {N : ℕ}
    (hN : tsupport (fun g : SL3 => f g) ∩ (U : Set SL3) ⊆ Blk U N) (hn : N < n) (x : X3) :
    ∫ g, ‖f g‖ ∂(F.trm coord n x) = 0 := by
  have hAnn : MeasurableSet (Ann U n) := Work.EKLC7.measurableSet_Ann hUcl n
  have hcompl : (F.trm coord n x) (Ann U n)ᶜ = 0 := by
    rw [FlowerFam.trm, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hAnn.compl]
    have : (Ann U n)ᶜ ∩ Ann U n = ∅ := Set.compl_inter_self _
    rw [this, measure_empty, mul_zero]
  have hae : (fun g : SL3 => ‖f g‖) =ᵐ[F.trm coord n x] 0 := by
    show ∀ᵐ g ∂(F.trm coord n x), ‖f g‖ = 0
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun y hy => ?_) hcompl
    simp only [Set.mem_ofPred_eq] at hy
    intro hyAnn
    exact hy (norm_eq_zero.mpr (image_eq_zero_of_notMem_tsupport (f := fun g : SL3 => f g)
      fun hts => Set.disjoint_left.mp (Ann_disjoint_Blk U hn) hyAnn
        (hN ⟨hts, Ann_subset_U U n hyAnn⟩)))
  rw [MeasureTheory.integral_congr_ae hae]
  simp

/-! ## 6. Integrability of the test function for the patched measure on the good set -/

/-- On the good set each annulus term is a finite measure, so the bounded (compactly supported)
test function is integrable for it. -/
theorem integrable_trm (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsProbabilityMeasure μ] {X' : Set X3} (hX' : F.Good X') (coord : X3 → X3 → SL3)
    (n : ℕ) (f : CompactlySupportedContinuousMap SL3 ℝ) {x : X3} (hx : x ∈ X') :
    Integrable (fun g : SL3 => f g) (F.trm coord n x) := by
  haveI hfin : IsFiniteMeasure ((F.prp coord n x).restrict (Ann U n)) := by
    show IsFiniteMeasure (Measure.restrict (Measure.map (coord x)
      (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3)
        (μ.restrict (F.Z (F.chose n x))) (F.m (F.chose n x)) x)) (Ann U n))
    infer_instance
  have hint : Integrable (fun g : SL3 => f g) ((F.prp coord n x).restrict (Ann U n)) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hne : (F.dd n x)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (F.dd_ne_zero hX' hx n)
  have := hint.smul_measure hne
  rwa [show (F.trm coord n x)
    = (F.dd n x)⁻¹ • ((F.prp coord n x).restrict (Ann U n)) from rfl]

/-- **On the good set the test function is integrable for the patched measure.** -/
theorem integrable_raw (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsProbabilityMeasure μ] {X' : Set X3} (hX' : F.Good X') (coord : X3 → X3 → SL3)
    (f : CompactlySupportedContinuousMap SL3 ℝ) {N : ℕ}
    (hN : tsupport (fun g : SL3 => f g) ∩ (U : Set SL3) ⊆ Blk U N) {x : X3} (hx : x ∈ X') :
    Integrable (fun g : SL3 => f g) (F.raw coord x) := by
  rw [FlowerFam.raw]
  refine integrable_sum_measure_iff.mpr ⟨fun n => integrable_trm hUcl F hX' coord n f hx, ?_⟩
  refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  exact trm_norm_integral_eq_zero hUcl F coord n f hN hn x

/-- **The patched measure integrates the test function as a finite sum over the annuli.** -/
theorem integral_raw_eq_sum (hUcl : IsClosed (U : Set SL3)) (F : FlowerFam U μ)
    [IsProbabilityMeasure μ] {X' : Set X3} (hX' : F.Good X') (coord : X3 → X3 → SL3)
    (f : CompactlySupportedContinuousMap SL3 ℝ) {N : ℕ}
    (hN : tsupport (fun g : SL3 => f g) ∩ (U : Set SL3) ⊆ Blk U N) {x : X3} (hx : x ∈ X') :
    (∫ g, f g ∂(F.raw coord x))
      = ∑ n ∈ Finset.range (N + 1), ∫ g, f g ∂(F.trm coord n x) := by
  rw [FlowerFam.raw, integral_sum_measure (integrable_raw hUcl F hX' coord f hN hx)]
  exact tsum_eq_sum fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    exact trm_integral_eq_zero hUcl F coord n f hN hn x

/-! ## 7. `measurable_nu` -/

theorem measurable_nu {U : Subgroup Work.EKLContract.SL3} {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (F : Work.EKLC7.FlowerFam U μ)
    (hU : Work.EKLContract.IsHoro U)
    (coord : Work.EKLContract.X3 → Work.EKLContract.X3 → Work.EKLContract.SL3)
    (hcoordm : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.X3 => coord p.1 p.2)
    {X' : Set Work.EKLContract.X3} (hX' : Work.EKLC7.FlowerFam.Good F X')
    (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) :
    Measurable fun x => ∫ g, f g ∂(Work.EKLC7.FlowerFam.nu F coord X' x) := by
  obtain ⟨N, hN⟩ := exists_blk_of_isCompact U (tsupport (fun g : SL3 => f g))
    f.hasCompactSupport.isCompact
  have hsum : Measurable fun x => ∑ n ∈ Finset.range (N + 1), ∫ g, f g ∂(F.trm coord n x) :=
    Finset.measurable_sum _ fun n _ => meas_term hU.1 F coord hcoordm n f
  have hfun : (fun x => if x ∈ X' then
        (∑ n ∈ Finset.range (N + 1), ∫ g, f g ∂(F.trm coord n x)) else f 1)
      = fun x => ∫ g, f g ∂(F.nu coord X' x) := by
    funext x
    by_cases hx : x ∈ X'
    · rw [if_pos hx, FlowerFam.nu_of_mem hx, integral_raw_eq_sum hU.1 F hX' coord f hN hx]
    · rw [if_neg hx, FlowerFam.nu_of_notMem hx,
        MeasureTheory.integral_dirac (fun g : SL3 => f g) 1]
  rw [← hfun]
  exact Measurable.ite hX'.meas hsum measurable_const

end Work.EKLC7
