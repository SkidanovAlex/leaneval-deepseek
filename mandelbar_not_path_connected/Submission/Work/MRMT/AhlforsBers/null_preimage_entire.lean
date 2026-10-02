import Mathlib
import Submission.Work.MRMT.QC.CompHolo.null_preimage

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.AhlforsBers

open MeasureTheory Complex Function Filter Set
open scoped Topology ENNReal

/-! ## The `N`-property of a non-constant entire function

A non-constant entire function `g : ℂ → ℂ` pulls Lebesgue-null sets back to Lebesgue-null sets.
This is the classical input behind the `N`-property of quasiconformal maps in the Ahlfors--Bers
theory: a non-constant holomorphic map is locally `w ↦ w ^ m` composed with a local
biholomorphism, hence is locally `m`-to-one, so it can only increase the size of a set by the
multiplicity of the map.

The proof is assembled from two independent ingredients, both proved below.

* `null_preimage_of_injOn`: the **local** `N`-property.  If `U` is open, `g` maps `U` injectively
  into `ℂ` and `deriv g ≠ 0` on `U`, then `volume (g ⁻¹' N ∩ U) = 0` for every null `N`.  This is
  the change-of-variables formula `lintegral_abs_det_fderiv_eq_addHaar_image` applied to
  `s = g ⁻¹' M ∩ U` (with `M ⊇ N` measurable and null), exactly as in
  `Work.MRMT.QC.CompHolo.null_preimage`; the Jacobian `|det (fderiv ℝ g z)| = ‖deriv g z‖ ^ 2`
  is strictly positive on `U`.

* `countable_setOf_deriv_eq_zero`: the **critical set** `{z | deriv g z = 0}` of a non-constant
  entire function is countable.  Indeed `deriv g` is again entire and not identically zero (else
  `g` is constant by `is_const_of_deriv_eq_zero`), so by the principle of isolated zeros its zero
  set is closed and discrete; a closed discrete subset of the second countable (hence Lindelöf)
  space `ℂ` is countable.

To conclude, cover the complement of the critical set by good open neighbourhoods.  Every regular
point `z` has such a neighbourhood by the inverse function theorem (the source of the
`OpenPartialHomeomorph` attached to the strict derivative is an open neighbourhood of `z` on which
`g` is injective, intersected with the open set where `deriv g ≠ 0`).  Second countability of `ℂ`
(`TopologicalSpace.isOpen_iUnion_countable`) turns this open cover into a *countable* one.  Finally
`g ⁻¹' N ⊆ (g ⁻¹' N ∩ C) ∪ ⋃ᵢ (g ⁻¹' N ∩ Uᵢ)` is a countable union of null sets. -/

/-! ## The local `N`-property -/

/-- **Local `N`-property.**  If `U` is open, `g` is complex differentiable at every point of `U`,
`g` is injective on `U` and `deriv g` does not vanish on `U`, then `g ⁻¹' N ∩ U` is null whenever
`N` is null.

The proof is the change-of-variables formula `lintegral_abs_det_fderiv_eq_addHaar_image` applied to
`s = g ⁻¹' M ∩ U`, where `M ⊇ N` is measurable and null: the Jacobian `|det (fderiv ℝ g z)|` equals
`‖deriv g z‖ ^ 2`, which is strictly positive on `U`, so it can only vanish on a null set. -/
theorem null_preimage_of_injOn_of_differentiableAt {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hdiff : ∀ z ∈ U, DifferentiableAt ℂ g z) (hderiv : ∀ z ∈ U, deriv g z ≠ 0)
    (hinj : Set.InjOn g U) {N : Set ℂ}
    (hN : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ U) = 0 := by
  classical
  -- enlarge the null set `N` to a measurable null set `M`
  obtain ⟨M, hNM, hMmeas, hM0⟩ := MeasureTheory.exists_measurable_superset_of_null hN
  set s : Set ℂ := g ⁻¹' M ∩ U with hsdef
  -- `g` is continuous on the open set `U`, hence measurable enough
  have hcont : ContinuousOn g U := fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
  have hsmeas : MeasurableSet s := by
    have hgm : Measurable (U.piecewise g (fun _ => 0)) :=
      hcont.measurable_piecewise continuous_const.continuousOn hU.measurableSet
    have heq : g ⁻¹' M ∩ U = (U.piecewise g (fun _ => 0)) ⁻¹' M ∩ U := by
      ext x
      by_cases hx : x ∈ U <;> simp [Set.piecewise, hx]
    rw [hsdef, heq]
    exact (hMmeas.preimage hgm).inter hU.measurableSet
  have hsU : s ⊆ U := Set.inter_subset_right
  -- `g` is differentiable on `s`, with real derivative `fderiv ℝ g`
  have hderiv' : ∀ z ∈ s, HasFDerivWithinAt g (fderiv ℝ g z) s z := by
    intro z hz
    have h : HasFDerivAt g (fderiv ℝ g z) z := by
      rw [Work.MRMT.QC.fderiv_real_eq_smul_one (hdiff z (hsU hz))]
      exact (hdiff z (hsU hz)).hasDerivAt.complexToReal_fderiv
    exact h.hasFDerivWithinAt
  -- change of variables
  have hcov := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (f := g) (f' := fun z => fderiv ℝ g z) hsmeas hderiv' (hinj.mono hsU)
  -- the image of `s` is contained in the null set `M`
  have himg : g '' s ⊆ M := by
    rintro y ⟨z, hz, rfl⟩
    exact hz.1
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g '' s) = 0 :=
    MeasureTheory.measure_mono_null himg hM0
  have hzero : ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ g z).det| = 0 := by rw [hcov, hvol]
  -- the integrand is a.e. measurable and strictly positive on `s`
  have hae := MeasureTheory.aemeasurable_ofReal_abs_det_fderivWithin
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (f := g) (f' := fun z => fderiv ℝ g z) hsmeas hderiv'
  have hne : ∀ z ∈ s, ENNReal.ofReal |(fderiv ℝ g z).det| ≠ 0 := by
    intro z hz
    have hpos : 0 < |(fderiv ℝ g z).det| := by
      rw [Work.MRMT.QC.abs_det_fderiv_eq (hdiff z (hsU hz))]
      exact pow_pos (norm_pos_iff.mpr (hderiv z (hsU hz))) 2
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  have hzero' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      x ∈ s → ENNReal.ofReal |(fderiv ℝ g x).det| = 0 :=
    (MeasureTheory.setLIntegral_eq_zero_iff' hsmeas hae).mp hzero
  -- so `s` itself is a null set
  have hcompl : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), x ∉ s := by
    filter_upwards [hzero'] with x hx hxs
    exact hne x hxs (hx hxs)
  have hs0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) s = 0 := by
    have h := MeasureTheory.ae_iff.mp hcompl
    simpa using h
  have hsub : g ⁻¹' N ∩ U ⊆ s := by
    intro x hx
    rw [hsdef, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hNM hx.1, hx.2⟩
  exact MeasureTheory.measure_mono_null hsub hs0

/-- **Local `N`-property**, entire form: the specialization of
`null_preimage_of_injOn_of_differentiableAt` to a globally entire `g`. -/
theorem null_preimage_of_injOn {g : ℂ → ℂ} (hg : Differentiable ℂ g) {U : Set ℂ} (hU : IsOpen U)
    (hinj : Set.InjOn g U) (hderiv : ∀ z ∈ U, deriv g z ≠ 0) {N : Set ℂ}
    (hN : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ U) = 0 :=
  null_preimage_of_injOn_of_differentiableAt hU (fun z _ => hg z) hderiv hinj hN

/-! ## Countability of zero sets -/

/-- **The zero set of a non-constant entire function is countable.**  An entire function which is
not identically zero has at most countably many zeros.

Indeed, by the principle of isolated zeros (`AnalyticOnNhd.preimage_zero_mem_codiscrete`) the zero
set is a discrete subset of `ℂ`, and `ℂ` is second countable, hence Lindelöf, so a discrete subset
of it is countable. -/
theorem countable_zero_set_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ z, f z ≠ 0) : Set.Countable {z : ℂ | f z = 0} := by
  obtain ⟨x0, hx0⟩ := hne
  have han : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hcod : ({z : ℂ | f z = 0})ᶜ ∈ Filter.codiscrete ℂ := by
    have h := han.preimage_zero_mem_codiscrete (x := x0) hx0
    simpa [Set.preimage, Set.compl_ofPred, eq_comm] using h
  have hdis : IsDiscrete {z : ℂ | f z = 0} := (compl_mem_codiscrete_iff.mp hcod).2
  exact Set.countable_coe_iff.mp <|
    @countable_of_Lindelof_of_discrete {z : ℂ | f z = 0} _
      inferInstance (isDiscrete_iff_discreteTopology.mp hdis)

/-- **The critical set of a non-constant entire function is countable.** -/
theorem countable_setOf_deriv_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c) :
    Set.Countable {z : ℂ | deriv g z = 0} := by
  -- `deriv g` is not identically zero, since otherwise `g` is constant
  have hne : ∃ z, deriv g z ≠ 0 := by
    by_contra h
    push Not at h
    exact hnc ⟨g 0, fun z => is_const_of_deriv_eq_zero hg h z 0⟩
  exact countable_zero_set_of_entire hg.deriv hne

/-! ## The global `N`-property -/

/-- **The `N`-property of a non-constant entire function.**  A non-constant entire function pulls
Lebesgue-null sets back to Lebesgue-null sets.

This is the classical fact behind the `N`-property of quasiconformal maps in the Ahlfors--Bers
theory: a non-constant holomorphic map is locally `w ↦ w ^ m` composed with a local
biholomorphism, hence is locally `m`-to-one and maps null sets to null sets.

Suggested route (all ingredients are available in the workspace or Mathlib):
* **local version.**  If `U` is open, `g` is holomorphic on `U`, `Set.InjOn g U` and
  `deriv g ≠ 0` on `U`, then `volume (g ⁻¹' N ∩ U) = 0` for null `N`.  Same argument as
  `Submission.Work.MRMT.QC.CompHolo.null_preimage` (Mathlib's change of variables
  `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` applied to `s = g ⁻¹' N ∩ U`, where
  `|det (fderiv ℝ g z)| = ‖deriv g z‖ ^ 2 > 0`), on `U` rather than `ℂ`.
* **the critical set is countable.**  `C := {z | deriv g z = 0}`: if `deriv g` were identically
  `0` then `g` is constant, so `deriv g` is a non-constant entire function whose zero set is
  locally finite (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`), hence countable.
* **covering the complement.**  Every `z` with `deriv g z ≠ 0` has a neighbourhood on which `g`
  is injective and `deriv g ≠ 0` (inverse function theorem: `HasStrictDerivAt.localInverse` /
  `AnalyticAt.analyticAt_invFun`).  By second countability `{deriv g ≠ 0}` is covered by countably
  many such `U_i`; apply the local version on each.
Conclude `volume (g ⁻¹' N) ≤ volume (g ⁻¹' N ∩ C) + Σᵢ volume (g ⁻¹' N ∩ Uᵢ) = 0`.

The statement is the same as the (still `sorry`'d) `Work.MRMT.QC.null_preimage_of_entire`; this
copy is at a fresh path so that the Ahlfors--Bers development can import a proven version.-/
theorem null_preimage_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c) {N : Set ℂ}
    (hN : (MeasureTheory.volume : MeasureTheory.Measure ℂ) N = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N) = 0 := by
  classical
  -- the critical set is countable, hence null
  have hCcount : Set.Countable {z : ℂ | deriv g z = 0} := countable_setOf_deriv_eq_zero hg hnc
  have hCnull : (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (g ⁻¹' N ∩ {z : ℂ | deriv g z = 0}) = 0 :=
    MeasureTheory.measure_mono_null Set.inter_subset_right
      (Set.Countable.measure_zero hCcount _)
  -- at each regular point, a good neighbourhood where the local version applies
  have hco : Continuous (deriv g) := (hg.contDiff (n := 1)).continuous_deriv le_rfl
  have hgood : ∀ z : {z : ℂ // deriv g z ≠ 0},
      ∃ V : Set ℂ, IsOpen V ∧ (z : ℂ) ∈ V ∧ Set.InjOn g V ∧ ∀ w ∈ V, deriv g w ≠ 0 := by
    rintro ⟨z, hz⟩
    have hstrict : HasStrictDerivAt g (deriv g z) z := (hg.analyticAt z).hasStrictDerivAt
    have hSF := hstrict.hasStrictFDerivAt_equiv hz
    let e : OpenPartialHomeomorph ℂ ℂ := hSF.toOpenPartialHomeomorph g
    have hzsrc : z ∈ e.source := hSF.mem_toOpenPartialHomeomorph_source
    exact ⟨e.source ∩ {w | deriv g w ≠ 0},
      e.open_source.inter (isOpen_ne_fun hco continuous_const), ⟨hzsrc, hz⟩,
      e.injOn.mono Set.inter_subset_left, fun w hw => hw.2⟩
  choose V hVopen hVmem hVinj hVderiv using hgood
  -- second countability of `ℂ` extracts a countable subcover of the regular points
  obtain ⟨J, hJcount, hJcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : {z : ℂ // deriv g z ≠ 0} => V z) (fun z => hVopen z)
  have hnull_reg : ∀ z : {z : ℂ // deriv g z ≠ 0},
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) (g ⁻¹' N ∩ V z) = 0 :=
    fun z => null_preimage_of_injOn hg (hVopen z) (hVinj z) (hVderiv z) hN
  have hCcompl : (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (g ⁻¹' N ∩ {z : ℂ | deriv g z = 0}ᶜ) = 0 := by
    have hsub2 : {z : ℂ | deriv g z = 0}ᶜ ⊆
        ⋃ z : {z : ℂ // deriv g z ≠ 0}, V z := by
      intro y hy
      have hy' : deriv g y ≠ 0 := by simpa using hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy'⟩, hVmem ⟨y, hy'⟩⟩
    have hsub : g ⁻¹' N ∩ {z : ℂ | deriv g z = 0}ᶜ ⊆ ⋃ z ∈ J, (g ⁻¹' N ∩ V z) := by
      intro x hx
      have hxmem : x ∈ ⋃ z ∈ J, V z := hJcover.symm ▸ hsub2 hx.2
      obtain ⟨z, hzJ, hzx⟩ := Set.mem_iUnion₂.mp hxmem
      exact Set.mem_iUnion₂.mpr ⟨z, hzJ, hx.1, hzx⟩
    exact MeasureTheory.measure_mono_null hsub
      ((MeasureTheory.measure_biUnion_null_iff hJcount).mpr fun z _ => hnull_reg z)
  -- assemble
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hCnull hCcompl)
  intro x hx
  by_cases h : deriv g x = 0
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

end Work.MRMT.AhlforsBers
