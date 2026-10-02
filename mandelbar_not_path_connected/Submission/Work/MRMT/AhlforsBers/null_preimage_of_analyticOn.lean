import Mathlib
import Submission.Work.MRMT.AhlforsBers.null_preimage_entire

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.AhlforsBers

open MeasureTheory Complex Function Filter Set
open scoped Topology ENNReal

/-! ## The `N`-property of a non-constant holomorphic function on a domain

`Work.MRMT.AhlforsBers.null_preimage_entire` proves the `N`-property for a non-constant *entire*
function.  Here we record the form in which the quasiconformal theory needs it: `g` is only assumed
to be holomorphic on a *domain* `U ⊆ ℂ` (open and preconnected), and the conclusion is that
`g ⁻¹' N ∩ U` is null for null `N`.

The proof is the same as in the entire case.

* At a point `z ∈ U` with `deriv g z ≠ 0`, the inverse function theorem produces an open
  neighbourhood on which `g` is injective with nonvanishing derivative, and the local
  change-of-variables argument of `null_preimage_of_injOn_of_differentiableAt` applies.
* The critical set `{z ∈ U | deriv g z = 0}` is a discrete subset of `U` — the principle of
  isolated zeros applied to the analytic function `deriv g` on `U` gives
  `(deriv g) ⁻¹' {0}ᶜ ∈ codiscreteWithin U` — and `U` is second countable, hence Lindelöf, so the
  critical set is countable and therefore null.
* Second countability of `U` turns the open cover of the regular points into a countable one,
  and `g ⁻¹' N ∩ U` is a countable union of null sets.

Preconnectedness of `U` is essential: on a disconnected open set a locally constant (but globally
non-constant) `g` would have `g ⁻¹' {c}` of positive measure. -/

/-- **The `N`-property of a non-constant holomorphic function on a domain.**  If `U ⊆ ℂ` is open
and preconnected, `g` is analytic on `U` and not constant on `U`, then `g` pulls Lebesgue-null sets
back to Lebesgue-null sets. -/
theorem null_preimage_of_analyticOn {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hnc : ¬ ∃ c : ℂ, ∀ z ∈ U, g z = c)
    {N : Set ℂ} (hN : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ U) = 0 := by
  classical
  have hdiff : ∀ z ∈ U, DifferentiableAt ℂ g z := fun z hz => (hg z hz).differentiableAt
  -- `U` is non-empty, since `g` is not constant on the empty set
  have hUne : U.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hnc ⟨0, fun z hz => by rw [h] at hz; exact absurd hz (Set.notMem_empty z)⟩
  -- and `g` has a regular point in `U`, since otherwise `g` is constant on the domain `U`
  have hone : ∃ z ∈ U, deriv g z ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := hUne
    by_contra h
    rw [not_exists] at h
    have hzero : EqOn (deriv g) 0 U := fun z hz => by
      by_contra hne
      exact h z ⟨hz, hne⟩
    exact hnc ⟨g z₀,
      fun z hz => hU.is_const_of_deriv_eq_zero hUc hg.differentiableOn hzero hz hz₀⟩
  -- the critical set
  set C : Set ℂ := {z : ℂ | z ∈ U ∧ deriv g z = 0} with hCdef
  have hcod : ({z : ℂ | deriv g z = 0})ᶜ ∈ Filter.codiscreteWithin U := by
    obtain ⟨z₁, hz₁U, hz₁⟩ := hone
    exact hg.deriv.preimage_zero_mem_codiscreteWithin hz₁ hz₁U ⟨hUne, hUc⟩
  -- so the critical set is countable, hence null
  have hdisC : IsDiscrete C := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    have h := (mem_codiscreteWithin_accPt.mp hcod) x hx.1
    have hCD : U \ ({z : ℂ | deriv g z = 0})ᶜ = C := by
      ext y
      simp [hCdef]
    rw [hCD] at h
    rwa [AccPt, Filter.not_neBot] at h
  have hCcount : Set.Countable C := Set.countable_coe_iff.mp <|
    @countable_of_Lindelof_of_discrete C _
      inferInstance (isDiscrete_iff_discreteTopology.mp hdisC)
  have hCnull : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ C) = 0 :=
    MeasureTheory.measure_mono_null Set.inter_subset_right (Set.Countable.measure_zero hCcount _)
  -- good neighbourhoods at the regular points
  have hgood : ∀ z : {z : ℂ // z ∈ U ∧ deriv g z ≠ 0},
      ∃ V : Set ℂ, IsOpen V ∧ (z : ℂ) ∈ V ∧ V ⊆ U ∧ Set.InjOn g V ∧ ∀ w ∈ V, deriv g w ≠ 0 := by
    rintro ⟨z, hzU, hz⟩
    have hstrict : HasStrictDerivAt g (deriv g z) z := (hg z hzU).hasStrictDerivAt
    have hSF := hstrict.hasStrictFDerivAt_equiv hz
    let e : OpenPartialHomeomorph ℂ ℂ := hSF.toOpenPartialHomeomorph g
    have hzsrc : z ∈ e.source := hSF.mem_toOpenPartialHomeomorph_source
    have hcont : ContinuousOn (deriv g) U := hg.deriv.continuousOn
    exact ⟨e.source ∩ (U ∩ (deriv g) ⁻¹' {0}ᶜ),
      e.open_source.inter (hcont.isOpen_inter_preimage hU isOpen_compl_singleton),
      ⟨hzsrc, hzU, hz⟩, Set.inter_subset_right.trans Set.inter_subset_left,
      e.injOn.mono Set.inter_subset_left, fun w hw => hw.2.2⟩
  choose V hVopen hVmem hVsubU hVinj hVderiv using hgood
  -- second countability of `U` extracts a countable subcover of the regular points
  obtain ⟨J, hJcount, hJcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : {z : ℂ // z ∈ U ∧ deriv g z ≠ 0} => V z) (fun z => hVopen z)
  have hnull_reg : ∀ z : {z : ℂ // z ∈ U ∧ deriv g z ≠ 0},
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ V z) = 0 :=
    fun z => null_preimage_of_injOn_of_differentiableAt (hVopen z)
      (fun w hw => hdiff w (hVsubU z hw)) (hVderiv z) (hVinj z) hN
  have hCcompl : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ U ∩ Cᶜ) = 0 := by
    have hsub2 : U ∩ Cᶜ ⊆ ⋃ z : {z : ℂ // z ∈ U ∧ deriv g z ≠ 0}, V z := by
      intro y hy
      have hyne : deriv g y ≠ 0 := by
        intro h0
        exact hy.2 ⟨hy.1, h0⟩
      exact Set.mem_iUnion.mpr ⟨⟨y, hy.1, hyne⟩, hVmem ⟨y, hy.1, hyne⟩⟩
    have hsub : g ⁻¹' N ∩ U ∩ Cᶜ ⊆ ⋃ z ∈ J, (g ⁻¹' N ∩ V z) := by
      intro x hx
      have hxmem : x ∈ ⋃ z ∈ J, V z := hJcover.symm ▸ hsub2 ⟨hx.1.2, hx.2⟩
      obtain ⟨z, hzJ, hzx⟩ := Set.mem_iUnion₂.mp hxmem
      exact Set.mem_iUnion₂.mpr ⟨z, hzJ, hx.1.1, hzx⟩
    exact MeasureTheory.measure_mono_null hsub
      ((MeasureTheory.measure_biUnion_null_iff hJcount).mpr fun z _ => hnull_reg z)
  -- assemble: `g ⁻¹' N ∩ U` is the union of its critical and regular parts
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hCnull hCcompl)
  intro x hx
  by_cases h : x ∈ C
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨hx, h⟩

end Work.MRMT.AhlforsBers
