import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Closers

open MeasureTheory Set Filter

/-- **A.e. strong measurability of the tail primitive on `(0,∞)`.**
For an arbitrary `Ψ : ℝ → ℝ` (no measurability of `Ψ` is assumed, and none is derivable), the
map `z ↦ ∫ s in (z,∞), Ψ s` is a.e. strongly measurable for `volume` restricted to `(0,∞)`.

Indeed, off the "good" set — the points `z > 0` at which `Ψ` fails to be integrable on `(z,∞)` —
Mathlib's Bochner integral is `0` (`MeasureTheory.integral_undef`), while on every part of the
good set the map is an ordinary primitive of an `L¹` function, hence continuous.  The good set
`G = {z | 0 < z ∧ IntegrableOn Ψ (Ioi z)}` is upward closed, so only three cases can occur: it is
empty, it is nonempty and bounded below (with threshold `sInf G`), or it is unbounded below (in
which case it contains all of `(0,∞)`; note that boundedness below is what the bounded-interval
template `Work.FTS.CoercivityFix.Coer1T.Hardy.aesm_prim_Ioc` has for free). -/
theorem aesm_tailPrim_Ioi (Ψ : ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∫ s in Set.Ioi z, Ψ s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  set F : ℝ → ℝ := fun z => ∫ s in Ioi z, Ψ s with hF
  change AEStronglyMeasurable F (volume.restrict (Ioi 0))
  -- the "good" set: `z > 0` and `Ψ` integrable on `(z,∞)`
  set G : Set ℝ := {z | 0 < z ∧ IntegrableOn Ψ (Ioi z)} with hG
  -- `G` is upward closed
  have hup : ∀ z ∈ G, ∀ y, 0 < y → z ≤ y → y ∈ G := by
    rintro z ⟨_, hz3⟩ y hy hzy
    exact ⟨hy, hz3.mono_set fun s hs => lt_of_le_of_lt hzy hs⟩
  -- the local identity: for `a ∈ G` and `a ≤ t`, the tail integral at `t` is a constant minus
  -- the primitive over `[a,t]`
  have hlocal : ∀ a ∈ G, ∀ t, a ≤ t → F t = (∫ s in Ioi a, Ψ s) - ∫ s in a..t, Ψ s := by
    intro a haG t hat
    have htG : t ∈ G := hup a haG t (lt_of_lt_of_le haG.1 hat) hat
    have h3 := intervalIntegral.integral_interval_add_Ioi haG.2 htG.2
    change (∫ s in Ioi t, Ψ s) = (∫ s in Ioi a, Ψ s) - ∫ s in a..t, Ψ s
    linarith
  -- consequently `F` is continuous at every point having a good point strictly below it
  have hcont : ∀ x, (∃ a ∈ G, a < x) → ContinuousAt F x := by
    intro x ⟨a, haG, hax⟩
    have heq : F =ᶠ[nhds x] (fun t => (∫ s in Ioi a, Ψ s) - ∫ s in a..t, Ψ s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hax] with t ht
      exact hlocal a haG t ht.le
    have hle : a ≤ x + 1 := le_of_lt (lt_of_lt_of_le hax (le_of_lt (lt_add_one x)))
    have hint : IntervalIntegrable Ψ volume a (x + 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
        (haG.2.mono_set fun s hs => hs.1)
    have hcio : ContinuousOn (fun t => ∫ s in a..t, Ψ s) (Icc a (x + 1)) := by
      have h := intervalIntegral.continuousOn_primitive_interval' (a := a) (b₁ := a)
        (b₂ := x + 1) hint (by rw [uIcc_of_le hle]; exact ⟨le_rfl, hle⟩)
      rwa [uIcc_of_le hle] at h
    have hcat : ContinuousAt (fun t => ∫ s in a..t, Ψ s) x :=
      hcio.continuousAt (Icc_mem_nhds hax (lt_add_one x))
    have hcont_prim : ContinuousAt (fun t => (∫ s in Ioi a, Ψ s) - ∫ s in a..t, Ψ s) x :=
      ContinuousAt.sub continuousAt_const hcat
    exact hcont_prim.congr heq.symm
  by_cases hGne : G.Nonempty
  · by_cases hGbdd : BddBelow G
    · -- `G` is nonempty and bounded below: threshold `z₁ = sInf G`
      have hz1le : ∀ z ∈ G, sInf G ≤ z := fun z hz => csInf_le hGbdd hz
      -- strictly below `sInf G` the integrand is not integrable, so the (junk) integral is `0`
      have hF0 : ∀ z, 0 < z → z < sInf G → F z = 0 := by
        intro z hz hlt
        have hcon : ¬ IntegrableOn Ψ (Ioi z) :=
          fun h => absurd (hz1le z ⟨hz, h⟩) (not_le.mpr hlt)
        change (∫ s in Ioi z, Ψ s) = 0
        exact integral_undef hcon
      -- `F` is continuous on `(sInf G, ∞)`
      have hcontOn : ContinuousOn F (Ioi (sInf G)) := by
        intro x hx
        have hex : ∃ a ∈ G, a < x := by
          by_contra h
          push Not at h
          exact absurd (le_csInf hGne h) (not_le.mpr hx)
        exact (hcont x hex).continuousWithinAt
      have h1 : AEStronglyMeasurable F (volume.restrict (Ioi (sInf G))) :=
        hcontOn.aestronglyMeasurable measurableSet_Ioi
      -- below `sInf G` the function vanishes a.e. (only `sInf G` itself can be exceptional)
      have h2 : AEStronglyMeasurable F (volume.restrict (Iic (sInf G) ∩ Ioi 0)) := by
        have hae : F =ᵐ[volume.restrict (Iic (sInf G) ∩ Ioi 0)] (fun _ : ℝ => 0) := by
          rw [Filter.EventuallyEq,
            ae_restrict_iff' (measurableSet_Iic.inter measurableSet_Ioi), MeasureTheory.ae_iff]
          refine measure_mono_null ?_ (measure_singleton (sInf G))
          intro z hz
          rw [Set.mem_singleton_iff]
          obtain ⟨hzle, hzpos, hzF⟩ : z ≤ sInf G ∧ 0 < z ∧ ¬(F z = 0) := by
            simpa [not_imp, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi] using hz
          rcases lt_or_eq_of_le hzle with hlt | heq
          · exact absurd (hF0 z hzpos hlt) hzF
          · exact heq
        exact (aestronglyMeasurable_const (b := (0 : ℝ))).congr hae.symm
      have hU : AEStronglyMeasurable F
          (volume.restrict (Ioi (sInf G) ∪ (Iic (sInf G) ∩ Ioi 0))) :=
        aestronglyMeasurable_union_iff.mpr ⟨h1, h2⟩
      refine hU.mono_measure (Measure.restrict_mono ?_ le_rfl)
      intro z hz
      rcases lt_or_ge (sInf G) z with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨hge, hz⟩
    · -- `G` is unbounded below: then it contains all of `(0,∞)` and `F` is the honest primitive
      have hcontOn : ContinuousOn F (Ioi 0) := by
        intro x hx
        obtain ⟨a, haG, hax⟩ := (not_bddBelow_iff.mp hGbdd) x
        exact (hcont x ⟨a, haG, hax⟩).continuousWithinAt
      exact hcontOn.aestronglyMeasurable measurableSet_Ioi
  · -- `G` is empty: `F` vanishes identically on `(0,∞)`
    have hzero : ∀ z, 0 < z → F z = 0 := by
      intro z hz
      have hcon : ¬ IntegrableOn Ψ (Ioi z) := fun h => hGne ⟨z, hz, h⟩
      change (∫ s in Ioi z, Ψ s) = 0
      exact integral_undef hcon
    have hae : F =ᵐ[volume.restrict (Ioi 0)] (fun _ : ℝ => 0) := by
      rw [Filter.EventuallyEq]
      refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      filter_upwards with z hz
      exact hzero z hz
    exact (aestronglyMeasurable_const (b := (0 : ℝ))).congr hae.symm

end Work.FTS.EllExist.Closers
