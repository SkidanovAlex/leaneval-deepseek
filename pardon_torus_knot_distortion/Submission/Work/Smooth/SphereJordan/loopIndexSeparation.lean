import Mathlib
import Submission.Work.Smooth.SphereJordan.flatChordSide
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Smooth.SphereJordan.argChangeLift

/-!
# The index of a loop is constant on the components of the complement of its trace

This file records the `loopIndex`-versions of the two facts that the Jordan-curve chapter
(`windNumber_eq_of_segment`, `windNumber_eq_of_preconnected`) states for `2π`-periodic curves:
the index of a closed path about a point is constant on the connected components of the complement
of its trace.  It also records the computation that identifies the *difference* of the indices
about two points with the index of the quotient loop `(Λ - p)/(Λ - q)`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- The loop `Λ - z`, as a continuous map. -/
def loopSub (Λ : C(unitInterval, ℂ)) (z : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Λ t - z, Λ.continuous.sub continuous_const⟩

@[simp] theorem loopSub_apply (Λ : C(unitInterval, ℂ)) (z : ℂ) (t : unitInterval) :
    loopSub Λ z t = Λ t - z := rfl

theorem loopSub_ne_zero {Λ : C(unitInterval, ℂ)} {z : ℂ} (hz : ∀ t, Λ t ≠ z) :
    ∀ t, loopSub Λ z t ≠ 0 := fun t => sub_ne_zero.mpr (hz t)

theorem loopSub_loop {Λ : C(unitInterval, ℂ)} {z : ℂ} (hloop : Λ 0 = Λ 1) :
    loopSub Λ z 0 = loopSub Λ z 1 := by
  simp only [loopSub_apply, hloop]

/-- **The index of a loop about two points joined by a segment the loop avoids is the same.** -/
theorem loopIndex_sub_eq_of_segment {Λ : C(unitInterval, ℂ)} (hloop : Λ 0 = Λ 1)
    {x y : ℂ} (hx : ∀ t : unitInterval, Λ t ≠ x) (hy : ∀ t : unitInterval, Λ t ≠ y)
    (hseg : ∀ (t : unitInterval) (s : ℝ), s ∈ Set.Icc 0 1 → Λ t ≠ (1 - s) * x + s * y) :
    loopIndex (loopSub Λ x) = loopIndex (loopSub Λ y) := by
  have hne₀ : ∀ t, loopSub Λ x t ≠ 0 := loopSub_ne_zero hx
  have hne₁ : ∀ t, loopSub Λ y t ≠ 0 := loopSub_ne_zero hy
  have hl₀ : loopSub Λ x 0 = loopSub Λ x 1 := loopSub_loop hloop
  have hl₁ : loopSub Λ y 0 = loopSub Λ y 1 := loopSub_loop hloop
  have hslit : ∀ t : unitInterval, loopSub Λ y t / loopSub Λ x t ∈ Complex.slitPlane := by
    intro t
    simp only [loopSub_apply]
    exact div_sub_mem_slitPlane_of_notMem_segment (fun s hs => hseg t s hs)
  exact (loopIndex_eq_of_pointwise_div_mem_slitPlane (loopSub Λ y) (loopSub Λ x)
    hne₁ hne₀ hl₁ hl₀ hslit).symm

/-- **The index of a loop is constant on the preconnected sets that avoid its trace.** -/
theorem loopIndex_eq_of_preconnected {Λ : C(unitInterval, ℂ)} (hloop : Λ 0 = Λ 1)
    {W : Set ℂ} (hW : IsPreconnected W) (hsub : W ⊆ (Set.range Λ)ᶜ) {p q : ℂ}
    (hp : p ∈ W) (hq : q ∈ W) :
    loopIndex (loopSub Λ p) = loopIndex (loopSub Λ q) := by
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp ⟨⟨p, hp⟩, hW⟩
  have hball' : ∀ {z : ℂ}, z ∈ W → ∃ ε > 0, Metric.ball z ε ⊆ (Set.range Λ)ᶜ := by
    intro z hz
    exact Metric.isOpen_iff.mp (isCompact_range Λ.continuous).isClosed.isOpen_compl z (hsub hz)
  have hloc : IsLocallyConstant
      (fun z : W => loopIndex (loopSub Λ z.1)) := by
    intro t
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hball⟩ := hball' z.2
    have hmem : Subtype.val ⁻¹' Metric.ball z.1 ε ∈ nhds z :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    have hyB : y.1 ∈ Metric.ball z.1 ε := hy
    have hzB : z.1 ∈ Metric.ball z.1 ε := Metric.mem_ball_self hε
    have hconst : loopIndex (loopSub Λ y.1) = loopIndex (loopSub Λ z.1) := by
      refine loopIndex_sub_eq_of_segment hloop (fun t ht => hball hyB ⟨t, ht⟩)
        (fun t ht => hball hzB ⟨t, ht⟩) (fun t s hs => ?_)
      · have hconv : Convex ℝ (Metric.ball (z.1 : ℂ) ε) := convex_ball _ _
        have hmem2 : (1 - s) • (↑y : ℂ) + s • (↑z : ℂ) ∈ Metric.ball z.1 ε :=
          hconv hyB hzB (by linarith [hs.1, hs.2]) hs.1 (by ring)
        have hgoal : ((1 - s : ℝ) : ℂ) * (↑y) + (s : ℂ) * (↑z) ∈ Metric.ball z.1 ε := by
          simpa [Complex.real_smul] using hmem2
        intro h
        exact hball hgoal ⟨t, by rw [h]; push_cast; ring⟩
    change loopIndex (loopSub Λ y.1) ∈ t
    rw [hconst]
    exact hz
  have hcont : Continuous (fun z : W => loopIndex (loopSub Λ z.1)) := hloc.continuous
  have hpre : IsPreconnected (Set.range (fun z : W => loopIndex (loopSub Λ z.1))) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ hcont.continuousOn
  have hmem : loopIndex (loopSub Λ p) ∈ Set.range (fun z : W => loopIndex (loopSub Λ z.1)) :=
    ⟨⟨p, hp⟩, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre) ({loopIndex (loopSub Λ p)} : Set ℤ)
    ({loopIndex (loopSub Λ p)}ᶜ) (isClosed_discrete _) (isClosed_discrete _)
    (fun x _ => by by_cases h : x = loopIndex (loopSub Λ p) <;> simp [h]) (by simp) with h | h
  · exact (Set.mem_singleton_iff.mp (h ⟨⟨q, hq⟩, rfl⟩)).symm
  · exact absurd (h hmem) (by simp)

/-- **The index of the quotient loop is the difference of the indices.** -/
theorem loopIndex_div_eq_sub {Λ : C(unitInterval, ℂ)} (hloop : Λ 0 = Λ 1) {p q : ℂ}
    (hp : ∀ t : unitInterval, Λ t ≠ p) (hq : ∀ t : unitInterval, Λ t ≠ q) :
    loopIndex ⟨fun t => (Λ t - p) / (Λ t - q),
        (Λ.continuous.sub continuous_const).div (Λ.continuous.sub continuous_const)
          (fun t => sub_ne_zero.mpr (hq t))⟩
      = loopIndex (loopSub Λ p) - loopIndex (loopSub Λ q) := by
  set γmin : C(unitInterval, ℂ) := loopSub Λ p with hγmin
  set γplus : C(unitInterval, ℂ) := loopSub Λ q with hγplus
  set c : C(unitInterval, ℂ) :=
    ⟨fun t => (Λ t - p) / (Λ t - q),
      (Λ.continuous.sub continuous_const).div (Λ.continuous.sub continuous_const)
        (fun t => sub_ne_zero.mpr (hq t))⟩ with hc
  have hγminapp : ∀ t, γmin t = Λ t - p := fun t => rfl
  have hγplusapp : ∀ t, γplus t = Λ t - q := fun t => rfl
  have hcapp : ∀ t, c t = (Λ t - p) / (Λ t - q) := fun t => rfl
  have hγminne : ∀ t, γmin t ≠ 0 := fun t => by rw [hγminapp]; exact sub_ne_zero.mpr (hp t)
  have hγplusne : ∀ t, γplus t ≠ 0 := fun t => by rw [hγplusapp]; exact sub_ne_zero.mpr (hq t)
  have hcne : ∀ t, c t ≠ 0 := fun t => by
    rw [hcapp]; exact div_ne_zero (sub_ne_zero.mpr (hp t)) (sub_ne_zero.mpr (hq t))
  have hγminloop : γmin 0 = γmin 1 := by rw [hγminapp, hγminapp, hloop]
  have hγplusloop : γplus 0 = γplus 1 := by rw [hγplusapp, hγplusapp, hloop]
  have hcloop : c 0 = c 1 := by rw [hcapp, hcapp, hloop]
  obtain ⟨Λm, hΛm, -, -⟩ := argChangeLift γmin hγminne
  obtain ⟨Λp, hΛp, -, -⟩ := argChangeLift γplus hγplusne
  have hΛd : ∀ s : unitInterval, Complex.exp ((Λm - Λp) s) = c s := by
    intro s
    rw [ContinuousMap.sub_apply, Complex.exp_sub, hΛm s, hΛp s, hcapp s, hγminapp s,
      hγplusapp s]
  have hspec_c := loopIndex_spec c hcne hcloop (Λm - Λp) hΛd
  have hspec_min := loopIndex_spec γmin hγminne hγminloop Λm hΛm
  have hspec_plus := loopIndex_spec γplus hγplusne hγplusloop Λp hΛp
  have hkey : ((loopIndex c : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      = ((loopIndex γmin - loopIndex γplus : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hdiff : (Λm - Λp) 1 - (Λm - Λp) 0 = (Λm 1 - Λm 0) - (Λp 1 - Λp 0) := by
      simp only [ContinuousMap.sub_apply]
      ring
    rw [← hspec_c, hdiff, hspec_min, hspec_plus]
    push_cast
    ring
  have heq : loopIndex c = loopIndex γmin - loopIndex γplus := by
    have h1 : ((loopIndex c : ℤ) : ℂ)
        = ((loopIndex γmin - loopIndex γplus : ℤ) : ℂ) :=
      mul_right_cancel₀ two_pi_I_ne_zero hkey
    exact_mod_cast h1
  rw [heq]

end

end Work.Smooth.SphereJordan
