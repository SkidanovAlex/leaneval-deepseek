import Mathlib

/-!
# `Work.EKLC6Core.fiber_inv_finite`

For a finite measure `μ` on a standard Borel space `X` and a measure preserving self-map
`T : X → X`, the conditional measures

`ν_x := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x`

of `μ` on the σ-algebra of `T`-invariant measurable sets are, for `μ`-a.e. `x`, invariant under
`T`: `T_* ν_x = ν_x` (`MeasureTheory.MeasurePreserving T ν_x ν_x`).

## The argument

Let `m := MeasurableSpace.invariants T`, `hm : m ≤ ‹MeasurableSpace X›`, and let
`K := condExpKernel μ m : @Kernel X X m ‹MeasurableSpace X›` be the conditional kernel.  Write
`μᵐ := μ.trim hm` for the restriction of `μ` to `m` and `diag : X → X × X` for the diagonal.

1. `ProbabilityTheory.compProd_trim_condExpKernel hm` says that `diag_* μ = μᵐ ⊗ₘ K`, i.e. `K` is a
   disintegration of the diagonal measure.

2. We show `μᵐ ⊗ₘ (K.map T) = μᵐ ⊗ₘ K`.  Both sides are measures on
   `(X × X, m.prod ‹MeasurableSpace X›)`, and the rectangles `A ×ˢ B` with `A` `m`-measurable and
   `B` measurable form a π-system generating the product σ-algebra
   (`generateFrom_prod_eq`).  On such a rectangle, using `Measure.compProd_apply_prod`,
   `Kernel.map_apply'` and step 1,
   * `(μᵐ ⊗ₘ K.map T)(A × B) = (μᵐ ⊗ₘ K)(A × T ⁻¹' B) = μ (A ∩ T ⁻¹' B)`, and
   * `(μᵐ ⊗ₘ K)(A × B) = μ (A ∩ B)`;
   these agree because `A` is `T`-invariant (`A = T ⁻¹' A`, as `A ∈ m`) and `T` preserves `μ`, so
   `A ∩ T ⁻¹' B = T ⁻¹' (A ∩ B)` has the same measure as `A ∩ B`.

3. `ProbabilityTheory.Kernel.compProd_eq_iff` (two finite kernels with the same composition product
   with a finite measure disagree only on a `μᵐ`-null set) now yields `K.map T =ᵐ[μᵐ] K`, i.e.
   `(K x).map T = K x` for `μᵐ`-a.e. `x`.  Since `μ ≤ μᵐ` (`MeasureTheory.le_trim`) this holds
   `μ`-a.e. as well, and `MeasurePreserving T (K x) (K x)` follows from `hT`.

Note that no separability/ergodicity assumption is used beyond `X` being standard Borel (which is
needed for the existence of the conditional kernel and for
`Kernel.compProd_eq_iff`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Work.EKLC6Core

/-- The composition products of `μ.trim hm` with the conditional kernel on the invariant
σ-algebra and with its push-forward by `T` agree (`hm` is `MeasurableSpace.invariants_le T`). -/
private lemma compProd_map_eq {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ((μ.trim (MeasurableSpace.invariants_le T)) ⊗ₘ
        ((condExpKernel μ (MeasurableSpace.invariants T)).map T))
      = ((μ.trim (MeasurableSpace.invariants_le T)) ⊗ₘ
        condExpKernel μ (MeasurableSpace.invariants T)) := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  have hmk : IsMarkovKernel ((condExpKernel μ (MeasurableSpace.invariants T)).map T) :=
    Kernel.IsMarkovKernel.map _ hT
  have hdiag : @Measurable X (X × X) ‹MeasurableSpace X›
      ((MeasurableSpace.invariants T).prod ‹MeasurableSpace X›) Function.diag := by
    have h1 : @Measurable X X ‹MeasurableSpace X› (MeasurableSpace.invariants T) id :=
      measurable_id'' hm
    have h2 : @Measurable X X ‹MeasurableSpace X› ‹MeasurableSpace X› id := measurable_id
    exact Measurable.prodMk h1 h2
  let S : Set (Set (X × X)) := Set.image2 (· ×ˢ ·)
    {A : Set X | MeasurableSet[MeasurableSpace.invariants T] A}
    {B : Set X | MeasurableSet[(‹MeasurableSpace X› : MeasurableSpace X)] B}
  have hgen : ((MeasurableSpace.invariants T).prod ‹MeasurableSpace X›)
      = MeasurableSpace.generateFrom S := by
    have key := @generateFrom_prod_eq X X
      {A : Set X | MeasurableSet[MeasurableSpace.invariants T] A}
      {B : Set X | MeasurableSet[(‹MeasurableSpace X› : MeasurableSpace X)] B}
      (@isCountablySpanning_measurableSet X (MeasurableSpace.invariants T))
      (@isCountablySpanning_measurableSet X (‹MeasurableSpace X› : MeasurableSpace X))
    have hC : MeasurableSpace.generateFrom
        {A : Set X | MeasurableSet[MeasurableSpace.invariants T] A}
        = MeasurableSpace.invariants T :=
      @MeasurableSpace.generateFrom_measurableSet X (MeasurableSpace.invariants T)
    have hD : MeasurableSpace.generateFrom
        {B : Set X | MeasurableSet[(‹MeasurableSpace X› : MeasurableSpace X)] B}
        = (‹MeasurableSpace X› : MeasurableSpace X) :=
      @MeasurableSpace.generateFrom_measurableSet X (‹MeasurableSpace X› : MeasurableSpace X)
    rw [hC, hD] at key
    exact key
  have hpi : IsPiSystem S :=
    IsPiSystem.prod
      (@MeasurableSpace.isPiSystem_measurableSet X (MeasurableSpace.invariants T))
      (@MeasurableSpace.isPiSystem_measurableSet X (‹MeasurableSpace X› : MeasurableSpace X))
  have heq : ∀ s ∈ S, ((μ.trim hm) ⊗ₘ (condExpKernel μ (MeasurableSpace.invariants T)).map T) s
      = ((μ.trim hm) ⊗ₘ condExpKernel μ (MeasurableSpace.invariants T)) s := by
    intro s hs
    obtain ⟨A, hA, B, hB, rfl⟩ := hs
    have hA' : MeasurableSet[MeasurableSpace.invariants T] A := hA
    have hB' : MeasurableSet B := hB
    have hAΩ : MeasurableSet A := hm A hA'
    have hAB : @MeasurableSet (X × X) ((MeasurableSpace.invariants T).prod ‹MeasurableSpace X›)
        (A ×ˢ (T ⁻¹' B)) :=
      @MeasurableSet.prod X X (MeasurableSpace.invariants T) ‹MeasurableSpace X› A (T ⁻¹' B)
        hA' (hT hB')
    have hAB2 : @MeasurableSet (X × X) ((MeasurableSpace.invariants T).prod ‹MeasurableSpace X›)
        (A ×ˢ B) :=
      @MeasurableSet.prod X X (MeasurableSpace.invariants T) ‹MeasurableSpace X› A B hA' hB'
    have hmap : ∀ x, ((condExpKernel μ (MeasurableSpace.invariants T)).map T) x B
        = (condExpKernel μ (MeasurableSpace.invariants T)) x (T ⁻¹' B) :=
      fun x => Kernel.map_apply' (condExpKernel μ (MeasurableSpace.invariants T)) hT x hB'
    have hTA : T ⁻¹' A = A := (MeasurableSpace.measurableSet_invariants (f := T)).mp hA' |>.2
    have hL : ((μ.trim hm) ⊗ₘ (condExpKernel μ (MeasurableSpace.invariants T)).map T)
        (A ×ˢ B) = μ (A ∩ B) := by
      rw [Measure.compProd_apply_prod hA' hB']
      simp_rw [hmap]
      rw [← Measure.compProd_apply_prod hA' (hT hB'), compProd_trim_condExpKernel hm,
        Measure.map_apply hdiag hAB]
      have hpre : Function.diag ⁻¹' (A ×ˢ (T ⁻¹' B)) = T ⁻¹' (A ∩ B) := by
        rw [Set.preimage_inter, hTA]
        ext x
        simp [Set.mem_inter_iff, Set.mem_preimage]
      rw [hpre]
      exact hmp.measure_preimage (hAΩ.inter hB').nullMeasurableSet
    have hR : ((μ.trim hm) ⊗ₘ condExpKernel μ (MeasurableSpace.invariants T)) (A ×ˢ B)
        = μ (A ∩ B) := by
      rw [compProd_trim_condExpKernel hm, Measure.map_apply hdiag hAB2]
      have hpre : Function.diag ⁻¹' (A ×ˢ B) = A ∩ B := by
        ext x
        simp [Set.mem_inter_iff]
      rw [hpre]
    rw [hL, hR]
  refine Measure.ext_of_generateFrom_of_iUnion S (fun _ => Set.univ) hgen hpi ?_ ?_ ?_ heq
  · rw [Set.iUnion_const]
  · intro i
    exact Set.mem_image2.mpr ⟨Set.univ, by simp, Set.univ, by simp, Set.univ_prod_univ⟩
  · intro i
    rw [Measure.compProd_apply_univ]
    exact measure_ne_top (μ.trim hm) Set.univ

theorem fiber_inv_finite {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, MeasureTheory.MeasurePreserving T
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) := by
  have hae : (condExpKernel μ (MeasurableSpace.invariants T)).map T
      =ᵐ[μ.trim (MeasurableSpace.invariants_le T)] condExpKernel μ (MeasurableSpace.invariants T) :=
    Kernel.compProd_eq_iff.mp (compProd_map_eq μ T hT hmp)
  have hae' : ∀ᵐ x ∂μ, ((condExpKernel μ (MeasurableSpace.invariants T)).map T) x
      = (condExpKernel μ (MeasurableSpace.invariants T)) x := by
    change ∀ᵐ x ∂(μ.trim (MeasurableSpace.invariants_le T)),
      ((condExpKernel μ (MeasurableSpace.invariants T)).map T) x
        = (condExpKernel μ (MeasurableSpace.invariants T)) x at hae
    rw [MeasureTheory.ae_iff] at hae ⊢
    exact le_antisymm (le_trans (le_trim (MeasurableSpace.invariants_le T)) (le_of_eq hae)) zero_le
  filter_upwards [hae'] with x hx
  rw [Kernel.map_apply (condExpKernel μ (MeasurableSpace.invariants T)) hT x] at hx
  exact ⟨hT, hx⟩

end Work.EKLC6Core
