import Mathlib
import Submission.Work.CoreTopology.Disk

namespace Work.CoreTopology

set_option linter.unusedVariables false

/-- **Pardon's Lemma `spherefamily` (abstract form, surgical hypotheses made explicit).** Let `A = H₁(F;ℚ)` for a closed orientable surface `F` of genus `g ≥ 1` (so `1 < finrank ℚ A`), and let `W t ≤ A` be the image of `H₁(F ∩ int S_t; ℚ)` in `H₁(F;ℚ)` along a one-parameter family of spheres `S_t`, `t ∈ [0,1]`. The geometric inputs are: (i) each `W t` is either `⊥` or `⊤` (the invariant `dim_ℚ im(H₁ → H₁(F))` is `0` or `2g`); (ii) the family is *locally constant except at surgery times and jumps by at most 1 there* — formalised as: for every `t` there is `ε > 0` such that the dimensions of `W s` and `W t` differ by at most `1` for `|s - t| < ε`; this is exactly what "no surgery, so no change; one surgery, so a change of at most 1" provides. Then `W 1 = ⊤`; and if in addition `W 1 = W₁ ⊔ W₂` with each of `W₁, W₂` equal to `⊥` or `⊤` (the two halves of a double bubble), then `W₁ = ⊤` or `W₂ = ⊤`, i.e. one of the two halves contains an essential loop. -/
theorem sphere_family {A : Type*} [AddCommGroup A] [Module ℚ A] [FiniteDimensional ℚ A]
    (W : ℝ → Submodule ℚ A) (W₁ W₂ : Submodule ℚ A)
    (hA : 1 < Module.finrank ℚ A)
    (hval : ∀ t : ℝ, W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (h0 : W 0 = ⊤) (hdecomp : W 1 = W₁ ⊔ W₂)
    (hval1 : W₁ = ⊥ ∨ W₁ = ⊤) (hval2 : W₂ = ⊥ ∨ W₂ = ⊤) :
    W₁ = ⊤ ∨ W₂ = ⊤ := by
  -- Dimensions of the two special submodules.
  have hfbot : Module.finrank ℚ ↥(⊥ : Submodule ℚ A) = 0 :=
    Submodule.finrank_eq_zero.mpr rfl
  have hftop : Module.finrank ℚ ↥(⊤ : Submodule ℚ A) = Module.finrank ℚ A :=
    finrank_top ℚ A
  -- The two prescribed values are distinct, because `finrank ℚ A > 1 > 0`.
  have htopbot : (⊤ : Submodule ℚ A) ≠ ⊥ := by
    intro h
    have hz : Module.finrank ℚ A = 0 := by rw [← hftop, h, hfbot]
    omega
  -- Because the dimensions of `W s` and `W t` differ by at most one, and every
  -- value has dimension `0` or `finrank ℚ A > 1`, `W` is *locally constant*.
  have hlocal : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε → W s = W t := by
    intro t
    obtain ⟨ε, hε, h⟩ := hstep t
    refine ⟨ε, hε, fun s hs => ?_⟩
    obtain ⟨h1, h2⟩ := h s hs
    rcases hval s with hsb | hst
    · rcases hval t with htb | htt
      · rw [hsb, htb]
      · exfalso
        rw [hsb, htt, hftop, hfbot] at h2
        omega
    · rcases hval t with htb | htt
      · exfalso
        rw [hst, htb, hftop, hfbot] at h1
        omega
      · rw [hst, htt]
  -- Both level sets are open; they are disjoint and cover `ℝ`; `0` lies in the
  -- `⊤`-level set. As `ℝ` is preconnected, the `⊤`-level set is all of `ℝ`.
  have hPopen : IsOpen {t : ℝ | W t = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε, hε, hc⟩ := hlocal t
    filter_upwards [Metric.ball_mem_nhds t hε] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    rw [hc s hs]
    exact ht
  have hNopen : IsOpen {t : ℝ | W t = ⊥} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ε, hε, hc⟩ := hlocal t
    filter_upwards [Metric.ball_mem_nhds t hε] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    rw [hc s hs]
    exact ht
  have hdisj : Disjoint {t : ℝ | W t = ⊤} {t : ℝ | W t = ⊥} := by
    rw [Set.disjoint_left]
    intro t ht hb
    change W t = ⊥ at hb
    change W t = ⊤ at ht
    rw [ht] at hb
    exact htopbot hb
  have hcover : (Set.univ : Set ℝ) ⊆ {t : ℝ | W t = ⊤} ∪ {t : ℝ | W t = ⊥} := by
    intro t _
    rcases hval t with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hsub := IsPreconnected.subset_or_subset hPopen hNopen hdisj hcover isPreconnected_univ
  have hW1 : W 1 = ⊤ := by
    rcases hsub with h | h
    · exact h (Set.mem_univ 1)
    · have hz : W 0 = ⊥ := h (Set.mem_univ 0)
      rw [h0] at hz
      exact absurd hz htopbot
  -- Finally, `W₁ ⊔ W₂ = W 1 = ⊤`, and `W₁` is `⊥` or `⊤`.
  rcases hval1 with h1 | h1
  · right
    rw [← bot_sup_eq W₂, ← h1, ← hdecomp, hW1]
  · left; exact h1

end Work.CoreTopology
