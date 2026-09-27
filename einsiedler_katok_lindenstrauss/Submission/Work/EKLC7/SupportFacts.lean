import Mathlib
import Submission.Work.EKLC7.Defs

/-!
# Support facts for measures on `SL₃(ℝ)` (component `C7`)

Three elementary but technically useful facts about `Measure.support` on
`SL₃(ℝ) = SL(3, ℝ)`:

* a measure whose support is the singleton `{1}` is a multiple of the Dirac mass `δ₁`
  (the space is second countable, so the support is conull);
* the support of a product measure is the product of the supports;
* an open set of measure zero is disjoint from the support.

As `SL₃(ℝ)` is a closed subspace of a finite product of copies of `ℝ`, it is a Polish
(hence second countable, hence hereditarily Lindelöf) locally compact σ-compact space; the
relevant instances are recorded at the top since type class search does not unfold the
`def Matrix` nor closedness of the locus `det = 1`.
-/

noncomputable section

namespace Work.EKLC7

set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open Work.EKLContract

/-! ## Topological instances for the matrix space and for `SL₃(ℝ)` -/

/-- The matrix space is Polish: it is a finite product of copies of `ℝ`.

(Mathlib has this for the product `m → n → R`, and `Matrix m n R` is definitionally that
product, but instance search does not unfold the `def Matrix`.) -/
instance instPolishMatrix3 : PolishSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (PolishSpace (Fin 3 → Fin 3 → ℝ))

/-- The matrix space is σ-compact: it is a finite product of copies of `ℝ`. -/
instance instSigmaCompactMatrix3 : SigmaCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (SigmaCompactSpace (Fin 3 → Fin 3 → ℝ))

/-- `SL₃(ℝ)` is closed in the matrix space, being the locus `det = 1`. -/
theorem isClosed_sl3 : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} :=
  isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const

instance instPolishSL3 : PolishSpace SL3 := isClosed_sl3.polishSpace

instance instSigmaCompactSL3 : SigmaCompactSpace SL3 := isClosed_sl3.sigmaCompactSpace

instance instSecondCountableSL3 : SecondCountableTopology SL3 := inferInstance

instance instHereditarilyLindelofSL3 : HereditarilyLindelofSpace SL3 := inferInstance

/-! ## A measure carried by a singleton is a multiple of the Dirac mass -/

/-- If the complement of a singleton is `ν`-null then `ν` is a multiple of `δ_x`.

This holds on any topological space with measurable singletons; no regularity of `ν` is
needed. -/
theorem eq_smul_dirac_of_compl_singleton_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (ν : Measure X) (x : X) (h : ν ({x} : Set X)ᶜ = 0) :
    ν = ν Set.univ • Measure.dirac x := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' x hA]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    have hAc : ν Aᶜ = 0 :=
      Measure.mono_null (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) h
    rw [← measure_add_measure_compl hA, hAc, add_zero]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    exact Measure.mono_null (Set.subset_compl_singleton_iff.mpr hx) h

/-- If the support of a measure on `SL₃(ℝ)` finite on compact sets is the singleton `{1}`
then the measure is a multiple of `δ₁`.  (Second countability makes the support conull.) -/
theorem support_singleton_eq_smul_dirac (ν : Measure SL3) [IsFiniteMeasureOnCompacts ν]
    (h : ν.support = {1}) : ν = ν Set.univ • Measure.dirac 1 := by
  have hcomp : ν ({1} : Set SL3)ᶜ = 0 := by
    have := Measure.measure_compl_support (μ := ν)
    rwa [h] at this
  exact eq_smul_dirac_of_compl_singleton_eq_zero ν 1 hcomp

/-! ## Support of a product measure -/

/-- The support of a product of two measures finite on compact sets is the product of the
supports.  (Finiteness on compact sets upgrades to `σ`-finiteness on the σ-compact space
`SL₃(ℝ)`, which is what the product formula `prod_prod` needs.) -/
theorem prod_support (β₁ β₂ : Measure SL3) [IsFiniteMeasureOnCompacts β₁]
    [IsFiniteMeasureOnCompacts β₂] :
    (β₁.prod β₂).support = β₁.support ×ˢ β₂.support := by
  haveI : SFinite β₂ := inferInstance
  ext p
  obtain ⟨x, y⟩ := p
  simp only [Set.mem_prod]
  constructor
  · intro hp
    constructor
    · by_contra hx
      obtain ⟨U, hU, hU0⟩ := Measure.notMem_support_iff_exists.mp hx
      have hmem : U ×ˢ (Set.univ : Set SL3) ∈ 𝓝 (x, y) := by
        rw [nhds_prod_eq]
        exact mem_prod_iff.mpr ⟨U, hU, Set.univ, univ_mem, fun z hz => hz⟩
      have hzero : (β₁.prod β₂) (U ×ˢ (Set.univ : Set SL3)) = 0 := by
        refine nonpos_iff_eq_zero.mp ?_
        calc (β₁.prod β₂) (U ×ˢ Set.univ) ≤ β₁ U * β₂ Set.univ := Measure.prod_prod_le U Set.univ
          _ = 0 := by rw [hU0, zero_mul]
      exact Measure.notMem_support_iff_exists.mpr ⟨_, hmem, hzero⟩ hp
    · by_contra hy
      obtain ⟨V, hV, hV0⟩ := Measure.notMem_support_iff_exists.mp hy
      have hmem : (Set.univ : Set SL3) ×ˢ V ∈ 𝓝 (x, y) := by
        rw [nhds_prod_eq]
        exact mem_prod_iff.mpr ⟨Set.univ, univ_mem, V, hV, fun z hz => hz⟩
      have hzero : (β₁.prod β₂) ((Set.univ : Set SL3) ×ˢ V) = 0 := by
        refine nonpos_iff_eq_zero.mp ?_
        calc (β₁.prod β₂) (Set.univ ×ˢ V) ≤ β₁ Set.univ * β₂ V := Measure.prod_prod_le Set.univ V
          _ = 0 := by rw [hV0, mul_zero]
      exact Measure.notMem_support_iff_exists.mpr ⟨_, hmem, hzero⟩ hp
  · rintro ⟨hx, hy⟩
    rw [Measure.support_eq_forall_isOpen] at hx hy ⊢
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    intro W hW hWopen
    obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hWopen x y hW
    calc 0 < β₁ U * β₂ V := ENNReal.mul_pos_iff.mpr ⟨hx U hxU hUopen, hy V hyV hVopen⟩
      _ = (β₁.prod β₂) (U ×ˢ V) := (Measure.prod_prod U V).symm
      _ ≤ (β₁.prod β₂) W := measure_mono hUV

/-! ## Open null sets are disjoint from the support -/

/-- An open set of measure zero is disjoint from the support. -/
theorem disjoint_of_isOpen_measure_eq_zero (β : Measure SL3) [IsFiniteMeasureOnCompacts β]
    (U : Set SL3) (hU : IsOpen U) (h : β U = 0) : Disjoint U β.support := by
  rw [Set.disjoint_left]
  intro x hxU hxsupp
  exact Measure.subset_compl_support_of_isOpen hU h hxU hxsupp

/-- The support facts needed by component `C7`. -/
theorem SupportFacts :
    (∀ (ν : MeasureTheory.Measure Work.EKLContract.SL3)
      [MeasureTheory.IsFiniteMeasureOnCompacts ν],
      ν.support = {1} → ν = ν Set.univ • MeasureTheory.Measure.dirac 1)
    ∧ (∀ (β₁ β₂ : MeasureTheory.Measure Work.EKLContract.SL3)
        [MeasureTheory.IsFiniteMeasureOnCompacts β₁] [MeasureTheory.IsFiniteMeasureOnCompacts β₂],
        (β₁.prod β₂).support = β₁.support ×ˢ β₂.support)
    ∧ (∀ (β : MeasureTheory.Measure Work.EKLContract.SL3)
        [MeasureTheory.IsFiniteMeasureOnCompacts β] (U : Set Work.EKLContract.SL3),
        IsOpen U → β U = 0 → Disjoint U β.support) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ν hν h
    exact support_singleton_eq_smul_dirac ν h
  · intro β₁ β₂ h₁ h₂
    exact prod_support β₁ β₂
  · intro β hβ U hU hU0
    exact disjoint_of_isOpen_measure_eq_zero β U hU hU0

end Work.EKLC7
