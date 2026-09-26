import Mathlib

/-! # A bijective holomorphic map onto the disc is a homeomorphism

Auxiliary lemma for `Work.Smooth.SphereJordan.planeDomain_homeo_unitBall`.

If `g` is holomorphic on an open preconnected `s ⊆ ℂ`, maps `s` bijectively onto the open unit
disc, then `s` and the disc are homeomorphic: `g` is non-constant (its image is the disc, which
has more than one point), hence an open map by the open mapping theorem
(`AnalyticOnNhd.is_constant_or_isOpen`), so the induced bijection `s → 𝔻` is a continuous open
bijection, i.e. a homeomorphism (`Equiv.toHomeomorphOfContinuousOpen`).
-/

namespace Work.Smooth.SphereJordan

open Set Metric

theorem bijOn_ball_homeo {s : Set ℂ} (hs : IsOpen s) (hsp : IsPreconnected s) {g : ℂ → ℂ}
    (hg : Set.BijOn g s (Metric.ball (0 : ℂ) 1)) (hd : DifferentiableOn ℂ g s) :
    Nonempty (s ≃ₜ Metric.ball (0 : ℂ) 1) := by
  have hana : AnalyticOnNhd ℂ g s := hd.analyticOnNhd hs
  have hnonconst : ¬ ∃ w : ℂ, ∀ z ∈ s, g z = w := by
    rintro ⟨w, hw⟩
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    have h2 : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      norm_num
    obtain ⟨z₀, hz₀, hz₀'⟩ := hg.2.2 h0
    obtain ⟨z₁, hz₁, hz₁'⟩ := hg.2.2 h2
    rw [hw z₀ hz₀] at hz₀'
    rw [hw z₁ hz₁] at hz₁'
    have : (0 : ℂ) = 1 / 2 := by rw [← hz₀', hz₁']
    norm_num at this
  have hopen : ∀ t ⊆ s, IsOpen t → IsOpen (g '' t) := by
    rcases hana.is_constant_or_isOpen hsp with h | h
    · exact absurd h hnonconst
    · exact h
  let G : s → Metric.ball (0 : ℂ) 1 := fun z => ⟨g z.1, hg.1 z.2⟩
  have hGbij : Function.Bijective G := by
    constructor
    · intro z w hzw
      exact Subtype.ext (hg.2.1 z.2 w.2 (congrArg Subtype.val hzw))
    · intro y
      obtain ⟨z, hz, hz'⟩ := hg.2.2 y.2
      exact ⟨⟨z, hz⟩, Subtype.ext hz'⟩
  have hGcont : Continuous G :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hd.continuousOn)
      fun z => hg.1 z.2
  have hGopen : IsOpenMap G := by
    intro t ht
    have htopen : IsOpen (Subtype.val '' t) := by
      rcases isOpen_induced_iff.mp ht with ⟨W, hW, hWt⟩
      have : Subtype.val '' t = W ∩ s := by
        rw [← hWt, Set.image_preimage_eq_inter_range, Subtype.range_val]
      rw [this]
      exact hW.inter hs
    have himg : G '' t = Subtype.val ⁻¹' (g '' (Subtype.val '' t)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.1, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, hz, hzx⟩, hxy⟩
        refine ⟨z, hz, Subtype.ext ?_⟩
        show g z.1 = y.1
        rw [hzx, hxy]
    rw [himg]
    exact isOpen_induced_iff.mpr ⟨g '' (Subtype.val '' t), hopen _ (by
      rintro x ⟨z, hz, rfl⟩
      exact z.2) htopen, rfl⟩
  exact ⟨Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective G hGbij) hGcont hGopen⟩

end Work.Smooth.SphereJordan
