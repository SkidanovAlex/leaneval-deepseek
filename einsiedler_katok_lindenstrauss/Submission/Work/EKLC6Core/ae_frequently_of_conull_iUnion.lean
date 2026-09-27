import Mathlib

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped Classical

/-- Auxiliary measure-theoretic fact: if `T` preserves the measure `μ` and `C` is
measurable, then the set of points whose `T`-orbit is eventually contained in `C`
has `μ`-measure at most `μ C`.

The proof observes that this set is `⋃ N, T^[N] ⁻¹' F` where `F = ⋂ n, T^[n] ⁻¹' C`
is the set of points whose whole orbit lies in `C`; each `T^[N] ⁻¹' F` has measure
`μ F` by measure preservation, and `F ⊆ C`. -/
theorem measure_eventually_mem_le {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {T : X → X} (hT : MeasureTheory.MeasurePreserving T μ μ) {C : Set X}
    (hC : MeasurableSet C) :
    μ {x | ∀ᶠ n in Filter.atTop, T^[n] x ∈ C} ≤ μ C := by
  set F : Set X := ⋂ n, (T^[n]) ⁻¹' C with hFdef
  have hFmeas : MeasurableSet F := by
    rw [hFdef]
    exact MeasurableSet.iInter (fun n => (hT.iterate n).measurable hC)
  have hFC : F ⊆ C := by
    intro x hx
    simp only [hFdef, Set.mem_iInter, Set.mem_preimage] at hx
    simpa using hx 0
  have hstep : ∀ y, y ∈ F → T y ∈ F := by
    intro y hy
    simp only [hFdef, Set.mem_iInter, Set.mem_preimage] at hy ⊢
    intro m
    rw [← Function.iterate_succ_apply]
    exact hy (m + 1)
  have hfwd : ∀ d, ∀ y ∈ F, T^[d] y ∈ F := by
    intro d
    induction d with
    | zero => intro y hy; simpa using hy
    | succ d ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      exact hstep _ (ih y hy)
  set s : ℕ → Set X := fun N => (T^[N]) ⁻¹' F with hsdef
  have hsmono : Monotone s := by
    intro N M hNM x hx
    simp only [hsdef, Set.mem_preimage] at hx ⊢
    have hMN : (M - N) + N = M := Nat.sub_add_cancel hNM
    rw [← hMN, Function.iterate_add_apply]
    exact hfwd (M - N) (T^[N] x) hx
  have hμs : ∀ N, μ (s N) = μ F :=
    fun N => (hT.iterate N).measure_preimage hFmeas.nullMeasurableSet
  have htend : Tendsto (fun N => μ (s N)) atTop (nhds (μ (⋃ N, s N))) :=
    tendsto_measure_iUnion_atTop hsmono
  have hconst : Tendsto (fun N => μ (s N)) atTop (nhds (μ F)) := by
    simp only [hμs]; exact tendsto_const_nhds
  have hμU : μ (⋃ N, s N) = μ F := tendsto_nhds_unique htend hconst
  have hSU : (⋃ N, s N) = {x | ∀ᶠ n in atTop, T^[n] x ∈ C} := by
    ext x
    simp only [Set.mem_iUnion, hsdef, Set.mem_preimage, hFdef, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      refine ⟨N, fun n hn => ?_⟩
      have : T^[n] x = T^[n - N] (T^[N] x) := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        rw [Function.iterate_add_apply]
      rw [this]; exact hN (n - N)
    · rintro ⟨N, hN⟩
      refine ⟨N, fun m => ?_⟩
      have : T^[m] (T^[N] x) = T^[m + N] x := by rw [Function.iterate_add_apply]
      rw [this]; exact hN (m + N) (Nat.le_add_left N m)
  rw [hSU] at hμU
  rw [hμU]
  exact measure_mono hFC

theorem ae_frequently_of_conull_iUnion {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasureTheory.MeasurePreserving T μ μ)
    {A : ℕ → Set X} (hA : ∀ k, MeasurableSet (A k)) (hmono : Monotone A)
    (hconull : μ (⋃ k, A k) = 1) :
    ∀ᵐ x ∂μ, ∃ k : ℕ, ∃ᶠ n in Filter.atTop, T^[n] x ∈ A k := by
  rw [MeasureTheory.ae_iff]
  set bad : Set X := ⋂ k, {x | ∀ᶠ n in atTop, T^[n] x ∈ (A k)ᶜ} with hbaddef
  have hgoal_eq : {x | ¬ ∃ k, ∃ᶠ n in atTop, T^[n] x ∈ A k} = bad := by
    rw [hbaddef]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, not_exists,
      Filter.not_frequently]
  rw [hgoal_eq]
  have hbound : ∀ k, μ bad ≤ μ ((A k)ᶜ) := by
    intro k
    rw [hbaddef]
    exact le_trans (measure_mono (Set.iInter_subset _ k)) (measure_eventually_mem_le hT (hA k).compl)
  have htend : Tendsto (fun k => μ ((A k)ᶜ)) atTop (nhds 0) := by
    have hmeas : (∀ k, NullMeasurableSet ((A k)ᶜ) μ) := fun k => (hA k).compl.nullMeasurableSet
    have hanti : Antitone (fun k => (A k)ᶜ) := fun a b hab => Set.compl_subset_compl.mpr (hmono hab)
    have hfin : ∃ k, μ ((A k)ᶜ) ≠ ⊤ := ⟨0, by
      have h1 : μ ((A 0)ᶜ) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [measure_univ] at h1
      exact ne_top_of_le_ne_top ENNReal.one_ne_top h1⟩
    have ht := tendsto_measure_iInter_atTop hmeas hanti hfin
    have hzero : μ (⋂ k, (A k)ᶜ) = 0 := by
      rw [← Set.compl_iUnion]
      rw [measure_compl (MeasurableSet.iUnion hA) (by rw [hconull]; exact ENNReal.one_ne_top),
          hconull, measure_univ]
      simp
    rw [hzero] at ht
    exact ht
  exact le_antisymm (ge_of_tendsto' htend hbound) (by simp)

end Work.EKLC6Core
