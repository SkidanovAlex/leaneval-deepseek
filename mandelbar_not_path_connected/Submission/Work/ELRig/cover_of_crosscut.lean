import Mathlib
import Submission.Work.ELRig.crossing_separation
import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

open Set Metric
open scoped Topology

namespace Work.ELRig

noncomputable section

/-- Two points of an *open* set lying in the same connected component are joined by a path inside
that set.  (Open subsets of `ℂ` are locally path connected, so for open `W` the connected
components are path connected.) -/
private lemma joinedIn_of_mem_connectedComponentIn {W : Set ℂ} (hW : IsOpen W) {x y : ℂ}
    (hxy : connectedComponentIn W x = connectedComponentIn W y) (hx : x ∈ W) (hy : y ∈ W) :
    JoinedIn W x y := by
  have hx' : x ∈ connectedComponentIn W x := mem_connectedComponentIn hx
  have hy' : y ∈ connectedComponentIn W x := hxy ▸ mem_connectedComponentIn hy
  have hopen : IsOpen (connectedComponentIn W x) := hW.connectedComponentIn
  have hconn : IsConnected (connectedComponentIn W x) :=
    isConnected_connectedComponentIn_iff.mpr hx
  have hpath : IsPathConnected (connectedComponentIn W x) :=
    (hopen.isConnected_iff_isPathConnected).mp hconn
  exact (hpath.joinedIn x hx' y hy').mono (connectedComponentIn_subset W x)

theorem cover_of_crosscut {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {γ : ℝ → ℂ} {s₁ s₀ s₂ : ℝ}
    (h₁ : s₁ < s₀) (h₂ : s₀ < s₂)
    (hcont : Continuous γ) (hinj : Set.InjOn γ (Set.Icc s₁ s₂))
    (hγ₀ : γ s₀ = p)
    (hint : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) p < ρ)
    (hsph₁ : dist (γ s₁) p = ρ) (hsph₂ : dist (γ s₂) p = ρ)
    (hre₁ : (γ s₁).re < p.re) (hre₂ : p.re < (γ s₂).re)
    (hcross : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → 0 < ((γ s).re - p.re) * (s - s₀)) :
    ∀ w ∈ Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂),
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p + (ρ / 2) * Complex.I) ∨
      JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) w (p - (ρ / 2) * Complex.I) := by
  intro w hw
  -- the arc is compact, hence closed
  have hArcClosed : IsClosed (γ '' Set.Icc s₁ s₂) :=
    (isCompact_Icc.image_of_continuousOn hcont.continuousOn).isClosed
  have hWopen : IsOpen (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂)) :=
    Metric.isOpen_ball.sdiff hArcClosed
  -- the two distinguished points on the perpendicular diameter
  have ha_dist : dist (p + (ρ / 2) * Complex.I) p = ρ / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    norm_num
  have hb_dist : dist (p - (ρ / 2) * Complex.I) p = ρ / 2 := by
    rw [dist_eq_norm]
    have h1 : p - (ρ / 2) * Complex.I - p = -((ρ / 2) * Complex.I) := by ring
    rw [h1, norm_neg, norm_mul, Complex.norm_I, mul_one,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    norm_num
  have ha_ball : p + (ρ / 2) * Complex.I ∈ Metric.ball p ρ := by
    rw [Metric.mem_ball, ha_dist]; linarith
  have hb_ball : p - (ρ / 2) * Complex.I ∈ Metric.ball p ρ := by
    rw [Metric.mem_ball, hb_dist]; linarith
  have ha_re : (p + (ρ / 2) * Complex.I).re = p.re := by simp
  have hb_re : (p - (ρ / 2) * Complex.I).re = p.re := by simp
  -- the two points avoid the arc
  have ha_notArc : p + (ρ / 2) * Complex.I ∉ γ '' Set.Icc s₁ s₂ := by
    rintro ⟨s, hs, hsA⟩
    rcases eq_or_ne s s₀ with rfl | hne
    · have hpa : p + (ρ / 2) * Complex.I = p := hsA.symm.trans hγ₀
      have h0 := congrArg (fun z => dist z p) hpa
      rw [ha_dist, dist_self] at h0
      linarith
    · have hx := hcross s hs hne
      have hγre : (γ s).re = p.re := by rw [hsA]; simp
      rw [hγre, sub_self, zero_mul] at hx
      exact lt_irrefl 0 hx
  have hb_notArc : p - (ρ / 2) * Complex.I ∉ γ '' Set.Icc s₁ s₂ := by
    rintro ⟨s, hs, hsA⟩
    rcases eq_or_ne s s₀ with rfl | hne
    · have hpb : p - (ρ / 2) * Complex.I = p := hsA.symm.trans hγ₀
      have h0 := congrArg (fun z => dist z p) hpb
      rw [hb_dist, dist_self] at h0
      linarith
    · have hx := hcross s hs hne
      have hγre : (γ s).re = p.re := by rw [hsA]; simp
      rw [hγre, sub_self, zero_mul] at hx
      exact lt_irrefl 0 hx
  -- the two points are *not* joined inside the punctured disc
  have hbridge : p + ↑(ρ / 2) * Complex.I = p + (ρ / 2) * Complex.I := by push_cast; ring
  have hbridge' : p - ↑(ρ / 2) * Complex.I = p - (ρ / 2) * Complex.I := by push_cast; ring
  have hnotjoin : ¬ JoinedIn (Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂))
      (p + (ρ / 2) * Complex.I) (p - (ρ / 2) * Complex.I) := by
    have hkey := crossing_separation hρ h₁ h₂ hcont hinj hγ₀ hint hsph₁ hsph₂ hre₁ hre₂ hcross
      (ρ / 2) (by linarith) (by linarith)
    rwa [hbridge, hbridge'] at hkey
  -- reparametrise the arc on `[0,1]`
  have hΔpos : 0 < s₂ - s₁ := by linarith
  have hΔne : (s₂ - s₁) ≠ 0 := ne_of_gt hΔpos
  have hmaps : ∀ u : Set.Icc (0:ℝ) 1, s₁ + (u:ℝ) * (s₂ - s₁) ∈ Set.Icc s₁ s₂ := by
    intro u
    exact ⟨by nlinarith [u.2.1, u.2.2, hΔpos], by nlinarith [u.2.1, u.2.2, hΔpos]⟩
  set β : C(Set.Icc (0:ℝ) 1, ℂ) :=
    ⟨fun u => γ (s₁ + (u:ℝ) * (s₂ - s₁)), hcont.comp (by fun_prop)⟩ with hβdef
  have hrange : Set.range β = γ '' Set.Icc s₁ s₂ := by
    ext z; constructor
    · rintro ⟨u, rfl⟩
      exact ⟨s₁ + (u:ℝ) * (s₂ - s₁), hmaps u, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨(s - s₁) / (s₂ - s₁), ?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hs.1]) (le_of_lt hΔpos)
      · rw [div_le_one hΔpos]; linarith [hs.2]
      · change γ (s₁ + ((s - s₁) / (s₂ - s₁)) * (s₂ - s₁)) = γ s
        rw [show s₁ + ((s - s₁) / (s₂ - s₁)) * (s₂ - s₁) = s by field_simp; ring]
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : γ (s₁ + (u:ℝ) * (s₂ - s₁)) = γ (s₁ + (v:ℝ) * (s₂ - s₁)) := huv
    have h2 := hinj (hmaps u) (hmaps v) h1
    have h3 : (u:ℝ) * (s₂ - s₁) = (v:ℝ) * (s₂ - s₁) := by linarith
    exact Subtype.ext (mul_right_cancel₀ hΔne h3)
  have hβ0 : β 0 ∈ Metric.sphere p ρ := by
    have h : (β 0 : ℂ) = γ s₁ := by
      change γ (s₁ + ((0 : Set.Icc (0:ℝ) 1) : ℝ) * (s₂ - s₁)) = γ s₁
      congr 1; simp
    rw [h, Metric.mem_sphere]; exact hsph₁
  have hβ1 : β 1 ∈ Metric.sphere p ρ := by
    have h : (β 1 : ℂ) = γ s₂ := by
      change γ (s₁ + ((1 : Set.Icc (0:ℝ) 1) : ℝ) * (s₂ - s₁)) = γ s₂
      congr 1
      rw [show ((1 : Set.Icc (0:ℝ) 1) : ℝ) = 1 from rfl, one_mul,
        show s₁ + (s₂ - s₁) = s₂ by ring]
    rw [h, Metric.mem_sphere]; exact hsph₂
  have hβint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 →
      β t ∈ Metric.ball p ρ := by
    intro t ht0 ht1
    change γ (s₁ + (t:ℝ) * (s₂ - s₁)) ∈ Metric.ball p ρ
    have ht := hmaps t
    have hne0 : s₁ + (t:ℝ) * (s₂ - s₁) ≠ s₁ := by
      intro hc
      apply ht0
      have htz : (t:ℝ) = 0 := by
        have : (t:ℝ) * (s₂ - s₁) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_right hΔne
      exact congrArg β (Subtype.ext htz)
    have hne1 : s₁ + (t:ℝ) * (s₂ - s₁) ≠ s₂ := by
      intro hc
      apply ht1
      have htz : (t:ℝ) = 1 := by
        have h2 : (t:ℝ) * (s₂ - s₁) = 1 * (s₂ - s₁) := by rw [one_mul]; linarith
        exact mul_right_cancel₀ hΔne h2
      exact congrArg β (Subtype.ext htz)
    have hthis := hint (s₁ + (t:ℝ) * (s₂ - s₁)) ht hne0 hne1
    rw [Metric.mem_ball]
    exact hthis
  -- at most two connected components
  have hkey := Commons.Topology.Jordan.crosscut_complement_at_most_two (c := p) (r := ρ) hρ β
    hβinj hβ0 hβ1 hβint (x := w) (y := p + (ρ / 2) * Complex.I)
    (z := p - (ρ / 2) * Complex.I) hw.1 ha_ball hb_ball
    (by rw [hrange]; exact hw.2) (by rw [hrange]; exact ha_notArc)
    (by rw [hrange]; exact hb_notArc)
  rw [hrange] at hkey
  -- conclude: the two points are in different components, so `w` joins one of them
  have haW : p + (ρ / 2) * Complex.I ∈ Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂) :=
    ⟨ha_ball, ha_notArc⟩
  have hbW : p - (ρ / 2) * Complex.I ∈ Metric.ball p ρ \ (γ '' Set.Icc s₁ s₂) :=
    ⟨hb_ball, hb_notArc⟩
  rcases hkey with h | h | h
  · left
    exact joinedIn_of_mem_connectedComponentIn hWopen h hw haW
  · exact absurd (joinedIn_of_mem_connectedComponentIn hWopen h haW hbW) hnotjoin
  · right
    exact joinedIn_of_mem_connectedComponentIn hWopen h hw hbW

end

end Work.ELRig
