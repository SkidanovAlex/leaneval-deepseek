import Mathlib
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.cp_compl_homeo
import Submission.Work.Projective.HomologyPieces
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.PairSequence

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The complement of a point in `ℂPⁿ` -/

/-- **The complement of the point `[1 : 0 : … : 0]` in `ℂPⁿ` is the union `cpV n` of the charts
`i ≠ 0`.**  A point of `ℂPⁿ` different from `[1 : 0 : … : 0]` has a nonzero homogeneous coordinate
somewhere other than the `0`-th. -/
theorem cpV_eq_compl_cpOrigin (n : ℕ) : cpV n = {y : CPSpace n | y ≠ cpOrigin n} := by
  ext p
  constructor
  · intro hp h
    rw [h] at hp
    exact cpOrigin_notMem_cpV n hp
  · intro hp
    by_contra hmem
    have hpU : p ∈ cpU n := by
      have h : p ∈ cpU n ∪ cpV n := by rw [cpU_union_cpV]; exact trivial
      rcases h with h1 | h1
      · exact h1
      · exact absurd h1 hmem
    -- the chart coordinates of `p` at `0` all vanish
    have hw : chartFun 0 p = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ : ∃ k, chartFun 0 p k ≠ 0 := by
        by_contra h
        push Not at h
        exact hne (funext fun k => h k)
      have hmem' : p ∈ chartSet ((0 : Fin (n + 1)).succAbove k) := by
        rw [← chartInv_chartFun 0 p hpU, chartInv_apply]
        exact (mem_chartSet_iff ((0 : Fin (n + 1)).succAbove k) _).mpr (by
          simpa only [Subtype.coe_mk, Fin.insertNth_apply_succAbove] using hk)
      exact hmem (mem_cpV_iff.mpr ⟨(0 : Fin (n + 1)).succAbove k, Fin.succAbove_ne 0 k, hmem'⟩)
    have hpc : p = cpOrigin n := by
      rw [← chartInv_chartFun 0 p hpU, hw]
      rfl
    exact hp hpc

/-- `cp2V = chartSet 1 ∪ chartSet 2` agrees with the general `cpV 2`. -/
theorem cp2V_eq_cpV_two : cp2V = cpV 2 := by
  ext p
  rw [cp2V, Set.mem_union, mem_cpV_iff]
  constructor
  · rintro (h | h)
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
  · rintro ⟨i, hi, hmem⟩
    fin_cases i
    · exact absurd rfl hi
    · exact Or.inl hmem
    · exact Or.inr hmem

/-- **`cp2V` is the complement of the point `[1 : 0 : 0]` in `ℂP²`.** -/
theorem cp2V_eq_compl_cpOrigin : cp2V = {y : CPSpace 2 | y ≠ cpOrigin 2} := by
  rw [cp2V_eq_cpV_two, cpV_eq_compl_cpOrigin]

/-- **The third homology of the complement of a point in `ℂP²` vanishes.**  The complement is
homeomorphic (by `cp_compl_homeo`) to `cp2V`, which is homotopy equivalent to `S²`. -/
theorem isZero_homology_three_compl_point (x : CPSpace 2) :
    IsZero ((singularChains ℤ (TopCat.of ↥({y : CPSpace 2 | y ≠ x}))).homology 3) := by
  have hh : ↥({y : CPSpace 2 | y ≠ x}) ≃ₜ ↥(cp2V : Set (CPSpace 2)) :=
    (cp_compl_homeo 2 x).some.symm.trans (Homeomorph.setCongr cp2V_eq_compl_cpOrigin).symm
  obtain ⟨e⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv hh.toHomotopyEquiv 3
  exact IsZero.of_iso (isZero_cochainV_homology_cp2 (n := 3) (by norm_num) (by norm_num)) e

/-- The image of a generator of a `ℤ`-module under a surjective `ℤ`-linear map generates. -/
lemma span_singleton_map_eq_top' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) (x : M)
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]
    simp
  rw [← h1, hx, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- The fundamental class of `ℂP²` in the sense of the duality project: the image of `cp2C` in
each local relative group `H₄(ℂP², ℂP²∖{x})` is a generator — i.e. `cp2C` has local degree `±1`
at every point ("`cp2C` is a fundamental class").  Suggested proof: the connecting map
`H₄(ℂP², ℂP²∖{x}) → H₃(ℂP²∖{x})` of the long exact sequence of the pair vanishes because
`H₃(ℂP²∖{x}) = 0` (`cp_compl_homeo` identifies the complement of `x` with `cpV 2`, whose third
homology vanishes, `isZero_cochainV_homology_cp2`), so the map `H₄(ℂP²) → H₄(ℂP², ℂP²∖{x})` is
surjective; the image of the generator `cp2C` under a surjection generates. -/
theorem cp2_hc (x : Work.Projective.CPSpace 2) :
    Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (Work.Projective.CPSpace 2)
            {y : Work.Projective.CPSpace 2 | y ≠ x}))) 4) Work.Projective.cp2C} = ⊤ := by
  -- vanishing of `H₃` of the complement of `x`
  have hzero : IsZero ((singularChains ℤ
      (TopCat.of ↥({y : CPSpace 2 | y ≠ x}))).homology 3) :=
    isZero_homology_three_compl_point x
  -- the connecting map of the pair vanishes
  have hδ : hPairδ (CPSpace 2) {y : CPSpace 2 | y ≠ x} 3 = 0 :=
    IsZero.eq_zero_of_tgt hzero _
  -- hence the map `H₄(ℂP²) → H₄(ℂP², ℂP²∖{x})` is onto
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (CPSpace 2) {y : CPSpace 2 | y ≠ x})) 4).hom := by
    have hex := hPair_exact₃ (CPSpace 2) {y : CPSpace 2 | y ≠ x} 3
    have hker : LinearMap.ker (hPairδ (CPSpace 2) {y : CPSpace 2 | y ≠ x} 3).hom = ⊤ := by
      rw [hδ, ModuleCat.hom_zero, LinearMap.ker_zero]
    have hrange : LinearMap.range (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (CPSpace 2) {y : CPSpace 2 | y ≠ x})) (3 + 1)).hom = ⊤ := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker hex, hker]
    rw [show (4 : ℕ) = 3 + 1 from rfl]
    exact LinearMap.range_eq_top.mp hrange
  -- the image of a generator of `H₄(ℂP²)` generates the relative group
  exact span_singleton_map_eq_top'
    (HomologicalComplex.homologyMap
      (cokernel.π (inclChains (CPSpace 2) {y : CPSpace 2 | y ≠ x})) 4).hom
    hsurj cp2C cp2C_span

end

end Work.Projective
