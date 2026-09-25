import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-! ## The canonical lift `iwRep`

The canonical real representative of a circle point (`iwRep = AddCircle.liftIoc 1 (-1/2) id`, taking
values in `Ioc (-1/2) (1/2]`) is the section of the quotient map on the fundamental domain; the
elementary facts below are proved here (rather than imported from `memLp_scaled_bump` /
`mstKernel_helpers`) so that the module stays a leaf of the dependency graph. -/

private lemma iwRep_mem_Ioc' (ξ : Circ) :
    iwRep ξ ∈ Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1) :=
  (AddCircle.equivIoc (1:ℝ) (-(1/2)) ξ).2

private lemma coe_iwRep' (ξ : Circ) : ((iwRep ξ : ℝ) : Circ) = ξ := by
  have := AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -(1/2)) (y := ξ)
  simpa only [iwRep, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_apply] using this

private lemma iwRep_coe_of_mem' {y : ℝ} (hy : y ∈ Set.Ioc (-(1/2:ℝ)) (1/2)) :
    iwRep (y : Circ) = y := by
  have h := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
    (f := fun x : ℝ => x) (x := y) (by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hy)
  simpa only [iwRep] using h

/-! ## The singleton `{1/2}` of the circle is null -/

/-- **Every singleton of the circle is `haarAddCircle`-null.** Since on `AddCircle 1` the
`volume` is the Haar measure, and `QuotientAddGroup.mk` maps `volume` restricted to the fundamental
domain `Ioc (-1/2) (1/2]` to `volume` (`AddCircle.measurePreserving_mk`), the preimage of a
singleton meets the fundamental domain in a subsingleton, hence is null. -/
private lemma haarAddCircle_singleton_zero (c : Circ) :
    (AddCircle.haarAddCircle (T := 1)) {c} = 0 := by
  have hvol : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have hmk := AddCircle.measurePreserving_mk (T := 1) (-(1/2:ℝ))
  have h1 : (volume.restrict (Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1))) (QuotientAddGroup.mk ⁻¹' {c})
      = (volume : Measure (AddCircle (1:ℝ))) {c} :=
    hmk.measure_preimage (measurableSet_singleton c).nullMeasurableSet
  have h2 : (volume.restrict (Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1))) (QuotientAddGroup.mk ⁻¹' {c})
      = volume (QuotientAddGroup.mk ⁻¹' {c} ∩ Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1)) :=
    Measure.restrict_apply' measurableSet_Ioc
  have hss : (QuotientAddGroup.mk ⁻¹' {c} ∩ Set.Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1)).Subsingleton := by
    intro x hx y hy
    have hx1 : ((x:ℝ) : Circ) = c := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.1
    have hy1 : ((y:ℝ) : Circ) = c := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy.1
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hx.2 hy.2).mp (hx1.trans hy1.symm)
  rw [← hvol, ← h1, h2]
  exact hss.measure_zero (volume : Measure ℝ)

/-- The set where the canonical lift takes the value `1/2` is null. -/
private lemma iwRep_eq_half_null :
    (AddCircle.haarAddCircle (T := 1)) {ζ : Circ | iwRep ζ = 1/2} = 0 := by
  refine measure_mono_null ?_ (haarAddCircle_singleton_zero (((1/2:ℝ)) : Circ))
  intro ζ hζ
  rw [Set.mem_singleton_iff]
  have h := coe_iwRep' ζ
  rw [hζ] at h
  exact h.symm

/-! ## The canonical lift is odd off the single point `1/2` -/

/-- The canonical lift is odd at every point whose lift is not exactly the endpoint `1/2`. -/
private lemma iwRep_neg_of_ne (ζ : Circ) (h : iwRep ζ ≠ 1/2) :
    iwRep (-ζ) = -iwRep ζ := by
  have hmem : iwRep ζ ∈ Set.Ioc (-(1/2:ℝ)) (1/2) := by
    have := iwRep_mem_Ioc' ζ
    rwa [show (-(1/2:ℝ) + 1) = 1/2 by norm_num] at this
  have hneg : -(iwRep ζ) ∈ Set.Ioc (-(1/2:ℝ)) (1/2) := by
    rw [Set.mem_Ioc] at hmem ⊢
    exact ⟨by linarith [lt_of_le_of_ne hmem.2 h], by linarith [hmem.1]⟩
  have hcoe : (((-(iwRep ζ) : ℝ)) : Circ) = -ζ := by
    rw [AddCircle.coe_neg, coe_iwRep']
  calc iwRep (-ζ) = iwRep (((-(iwRep ζ) : ℝ)) : Circ) := by rw [← hcoe]
    _ = -(iwRep ζ) := iwRep_coe_of_mem' hneg

/-- **The canonical lift is odd, almost everywhere.** -/
private lemma iwRep_neg_ae' :
    ∀ᵐ ζ ∂(AddCircle.haarAddCircle (T := 1)), iwRep (-ζ) = -iwRep ζ := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ iwRep_eq_half_null
  intro ζ hζ
  simp only [Set.mem_ofPred_eq] at hζ ⊢
  by_contra hne
  exact hζ (iwRep_neg_of_ne ζ hne)

/-! ## The profile is conjugate-symmetric -/

/-- The conjugate of the oscillatory profile is the profile at the reflected frequency:
`star (Φ_N β) = Φ_N (-β)`. -/
private lemma star_polyProfile_eq_neg (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    star (polyProfile P N β) = polyProfile P N (-β) := by
  rw [← starRingEnd_apply, star_polyProfile, polyProfile_eq_polyE]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [neg_mul]

/-- **The oscillatory profile is conjugate-symmetric on the circle, almost everywhere.** With
`mstProf P N ζ = polyProfile P N (iwRep ζ)` (`mst_scalar_defs.lean`) and
`star (polyProfile P N β) = ∫_0^1 polyE (-(β P(N s))) ds` (`star_polyProfile`), one has
  `∀ᵐ ζ ∂(AddCircle.haarAddCircle (T := 1)), mstProf P N (-ζ) = star (mstProf P N ζ)`,
i.e. `Φ_N(-ζ) = conj (Φ_N ζ)` for a.e. circle point.  Route: `mstProf P N (-ζ) =
polyProfile P N (iwRep (-ζ))` and `star (mstProf P N ζ) = polyProfile P N (-iwRep ζ)`
(from `star_polyProfile`, whose right side is the defining integral of `polyProfile P N (-iwRep ζ)`),
so the claim reduces to `iwRep (-ζ) = -iwRep ζ`, true off the single point `ζ = 1/2` (a.e.).  The
oddness of `iwRep` off `1/2` can be proved inline: for `w := iwRep ζ ≠ 1/2` one has
`-w ∈ Ioc (-1/2) (1/2]` and `-ζ = ((-w : ℝ) : Circle)`, so `iwRep (-ζ) = -w` by
`iwRep_coe_of_mem`; the exceptional point `1/2` is null (`haarAddCircle = volume` on `AddCircle 1`
and the singleton is null). -/
theorem mstProf_neg_ae (P : Polynomial ℤ) (N : ℕ) :
    ∀ᵐ ζ ∂(AddCircle.haarAddCircle (T := 1)),
      Work.BourgainPlan.Maximal.mstProf P N (-ζ)
        = star (Work.BourgainPlan.Maximal.mstProf P N ζ) := by
  filter_upwards [iwRep_neg_ae'] with ζ hζ
  simp only [mstProf_apply]
  rw [hζ]
  exact (star_polyProfile_eq_neg P N (iwRep ζ)).symm

end

end Work.BourgainPlan.Maximal
