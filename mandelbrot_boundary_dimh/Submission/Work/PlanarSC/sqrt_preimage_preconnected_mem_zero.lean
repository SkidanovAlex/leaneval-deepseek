import Mathlib

namespace Work.PlanarSC

open Set.Notation

/-- For nonnegative reals `a b`, `min a b ^ 2 ≤ a * b`. -/
private lemma sq_min_le_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ^ 2 ≤ a * b := by
  have h1 : min a b ≤ a := min_le_left a b
  have h2 : min a b ≤ b := min_le_right a b
  have h0 : 0 ≤ min a b := le_min ha hb
  calc min a b ^ 2 = min a b * min a b := by ring
    _ ≤ a * b := mul_le_mul h1 h2 h0 ha

/-- Key estimate: if `r ^ 2 = ζ` and `w ^ 2 = z`, the distance from `r` to the nearer of
`±w` is controlled by `‖ζ - z‖`. -/
private lemma min_norm_le {r w ζ z : ℂ} (hr : r ^ 2 = ζ) (hw : w ^ 2 = z) :
    min ‖r - w‖ ‖r + w‖ ^ 2 ≤ ‖ζ - z‖ := by
  have hfac : (r - w) * (r + w) = ζ - z := by rw [← hr, ← hw]; ring
  have hprod : ‖r - w‖ * ‖r + w‖ = ‖ζ - z‖ := by rw [← hfac, norm_mul]
  have h := sq_min_le_mul (norm_nonneg (r - w)) (norm_nonneg (r + w))
  rwa [hprod] at h

private lemma min_norm_lt {r w ζ z : ℂ} (hr : r ^ 2 = ζ) (hw : w ^ 2 = z) {ε : ℝ}
    (hε : 0 < ε) (h : ‖ζ - z‖ < ε ^ 2) : min ‖r - w‖ ‖r + w‖ < ε := by
  have h1 := min_norm_le hr hw
  have h2 : min ‖r - w‖ ‖r + w‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt h1 h
  have h0 : 0 ≤ min ‖r - w‖ ‖r + w‖ := le_min (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Every complex number has a square root. -/
private lemma exists_sq_eq_complex (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, by norm_num⟩
  · refine ⟨Complex.sqrt z, ?_⟩
    rw [sqrt_eq_exp hz, pow_two, ← Complex.exp_add]
    have : Complex.log z / 2 + Complex.log z / 2 = Complex.log z := by ring
    rw [this, Complex.exp_log hz]

/-- If `Ω` is open and preconnected and contains `0`, then the preimage of `Ω` under the
squaring map `w ↦ w ^ 2` is preconnected. -/
theorem sqrt_preimage_preconnected_mem_zero {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω) :
    IsPreconnected {w : ℂ | w ^ 2 ∈ Ω} := by
  set S : Set ℂ := {w : ℂ | w ^ 2 ∈ Ω} with hS
  have h0S : (0 : ℂ) ∈ S := by rw [hS]; simpa using h0
  have hSopen : IsOpen S := by
    rw [hS]; exact hΩo.preimage (continuous_pow 2)
  set C : Set ℂ := connectedComponentIn S 0 with hC
  have hCsub : C ⊆ S := by rw [hC]; exact connectedComponentIn_subset S 0
  have hCpre : IsPreconnected C := by rw [hC]; exact isPreconnected_connectedComponentIn
  have h0C : (0 : ℂ) ∈ C := by rw [hC]; exact mem_connectedComponentIn h0S
  have hCopen : IsOpen C := by rw [hC]; exact hSopen.connectedComponentIn
  -- `C` is closed within `S`
  have hCclosedInS : ∀ w : ℂ, w ∈ S →
      (∀ δ : ℝ, 0 < δ → ∃ t : ℂ, t ∈ C ∧ ‖t - w‖ < δ) → w ∈ C := by
    intro w hwS hclose
    have hmem : w ∈ closure C := by
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨t, htC, ht⟩ := hclose δ hδ
      refine ⟨t, htC, ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact ht
    have hpre : IsPreconnected (insert w C) :=
      IsPreconnected.subset_closure hCpre (Set.subset_insert w C) (by
        intro x hx
        rcases hx with rfl | hxC
        · exact hmem
        · exact subset_closure hxC)
    have hsub : insert w C ⊆ S := by
      intro x hx
      rcases hx with rfl | hxC
      · exact hwS
      · exact hCsub hxC
    have hsub2 : insert w C ⊆ C := by
      have hh : insert w C ⊆ connectedComponentIn S 0 :=
        hpre.subset_connectedComponentIn (Set.mem_insert_of_mem w h0C) hsub
      rwa [← hC] at hh
    exact hsub2 (by simp)
  -- the set of `z ∈ Ω` all of whose square roots lie in `C`
  set D : Set ℂ := {z : ℂ | z ∈ Ω ∧ ∀ w : ℂ, w ^ 2 = z → w ∈ C} with hD
  have h0D : (0 : ℂ) ∈ D := by
    rw [hD]
    exact ⟨h0, fun w hw => by rw [sq_eq_zero_iff.mp hw]; exact h0C⟩
  -- `D` is open in `Ω`
  have hDopen : ∀ z ∈ D, ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : ℂ, ‖ζ - z‖ < δ → ζ ∈ Ω → ζ ∈ D := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · obtain ⟨ρ, hρ, hρC⟩ := Metric.isOpen_iff.mp hCopen 0 h0C
      refine ⟨ρ ^ 2, pow_pos hρ 2, ?_⟩
      intro ζ hζ hζΩ
      refine ⟨hζΩ, ?_⟩
      intro w hw
      have h1 : ‖w‖ ^ 2 = ‖ζ‖ := by rw [← hw, norm_pow]
      have h2 : ‖w‖ < ρ := by
        have h3 : ‖w‖ ^ 2 < ρ ^ 2 := by rw [h1]; simpa using hζ
        nlinarith [norm_nonneg w, hρ]
      exact hρC (by rw [Metric.mem_ball, dist_zero_right]; exact h2)
    · obtain ⟨w, hw⟩ := exists_sq_eq_complex z
      have hwC : w ∈ C := hz.2 w hw
      have hnwC : -w ∈ C := hz.2 (-w) (by rw [neg_sq]; exact hw)
      obtain ⟨ε₁, hε₁, hε₁C⟩ := Metric.isOpen_iff.mp hCopen w hwC
      obtain ⟨ε₂, hε₂, hε₂C⟩ := Metric.isOpen_iff.mp hCopen (-w) hnwC
      set ε : ℝ := min ε₁ ε₂ with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₁ hε₂
      have hε₁le : ε ≤ ε₁ := by rw [hεdef]; exact min_le_left _ _
      have hε₂le : ε ≤ ε₂ := by rw [hεdef]; exact min_le_right _ _
      refine ⟨ε ^ 2, pow_pos hεpos 2, ?_⟩
      intro ζ hζ hζΩ
      refine ⟨hζΩ, ?_⟩
      intro r hr
      rcases eq_or_ne ζ 0 with rfl | hζ0
      · rw [sq_eq_zero_iff.mp hr]; exact h0C
      · have hlt : min ‖r - w‖ ‖r + w‖ < ε := min_norm_lt hr hw hεpos hζ
        rcases min_lt_iff.mp hlt with hh | hh
        · exact hε₁C (Metric.mem_ball.mpr (by
            rw [dist_eq_norm]; exact lt_of_lt_of_le hh hε₁le))
        · exact hε₂C (Metric.mem_ball.mpr (by
            rw [dist_eq_norm, sub_neg_eq_add]; exact lt_of_lt_of_le hh hε₂le))
  -- `D` is closed in `Ω`
  have hDclosed : ∀ z : ℂ, z ∈ Ω →
      (∀ δ : ℝ, 0 < δ → ∃ ζ : ℂ, ζ ∈ D ∧ ‖ζ - z‖ < δ) → z ∈ D := by
    intro z hzΩ hnb
    by_contra hzD
    have hnot : ∃ w : ℂ, w ^ 2 = z ∧ w ∉ C := by
      by_contra h
      apply hzD
      refine ⟨hzΩ, ?_⟩
      intro w hw
      by_contra hwc
      exact h ⟨w, hw, hwc⟩
    obtain ⟨w, hw, hwc⟩ := hnot
    have hwS : w ∈ S := by
      rw [hS]
      change w ^ 2 ∈ Ω
      rw [hw]; exact hzΩ
    have hfar : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, t ∈ C → ε ≤ ‖t - w‖ := by
      by_contra h
      apply hwc
      apply hCclosedInS w hwS
      intro δ hδ
      by_contra h'
      exact h ⟨δ, hδ, fun t ht => not_lt.mp fun hlt => h' ⟨t, ht, hlt⟩⟩
    obtain ⟨ε, hε, hfar⟩ := hfar
    obtain ⟨ζ, hζD, hζdist⟩ := hnb (ε ^ 2) (pow_pos hε 2)
    obtain ⟨r, hr⟩ := exists_sq_eq_complex ζ
    have hrC : r ∈ C := hζD.2 r hr
    have hnrC : -r ∈ C := hζD.2 (-r) (by rw [neg_sq]; exact hr)
    have hlt : min ‖r - w‖ ‖r + w‖ < ε := min_norm_lt hr hw hε hζdist
    rcases min_lt_iff.mp hlt with hh | hh
    · exact absurd (hfar r hrC) (not_le.mpr hh)
    · have hneg : ‖(-r) - w‖ < ε := by
        rw [show -r - w = -(r + w) by ring, norm_neg]; exact hh
      exact absurd (hfar (-r) hnrC) (not_le.mpr hneg)
  have hPCS : PreconnectedSpace Ω := Subtype.preconnectedSpace hΩc
  have hDopen_sub : IsOpen (Ω ↓∩ D) := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hxD : (x : ℂ) ∈ D := hx
    obtain ⟨δ, hδ, hδD⟩ := hDopen (x : ℂ) hxD
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    rw [Metric.mem_ball] at hy
    show (y : ℂ) ∈ D
    refine hδD (y : ℂ) ?_ y.2
    have h2 := hy
    rw [Subtype.dist_eq, dist_eq_norm] at h2
    exact h2
  have hDclosed_sub : IsClosed (Ω ↓∩ D) := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    rw [Metric.mem_closure_iff] at hx
    have hnb : ∀ δ : ℝ, 0 < δ → ∃ ζ : ℂ, ζ ∈ D ∧ ‖ζ - (x : ℂ)‖ < δ := by
      intro δ hδ
      obtain ⟨b, hb, hbd⟩ := hx δ hδ
      refine ⟨(b : ℂ), hb, ?_⟩
      have h2 := hbd
      rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at h2
      exact h2
    show (x : ℂ) ∈ D
    exact hDclosed (x : ℂ) x.2 hnb
  have hDΩ : IsClopen (Ω ↓∩ D) := ⟨hDclosed_sub, hDopen_sub⟩
  have hne : ((Set.univ : Set Ω) ∩ (Ω ↓∩ D)).Nonempty :=
    ⟨⟨(0 : ℂ), h0⟩, Set.mem_univ _, h0D⟩
  have hsubu : (Set.univ : Set Ω) ⊆ (Ω ↓∩ D) :=
    hPCS.isPreconnected_univ.subset_isClopen hDΩ hne
  have hDall : Ω ⊆ D := by
    intro z hz
    have hh := hsubu (Set.mem_univ (⟨z, hz⟩ : Ω))
    exact hh
  have hSC : S ⊆ C := fun w hw => (hDall hw).2 w rfl
  have hSeq : S = C := Set.Subset.antisymm hSC hCsub
  rw [hSeq]
  exact hCpre

end Work.PlanarSC
