import Mathlib
import Submission.Work.ELRig.sign_flip_of_two_components_horiz
import Submission.Work.Topology.crosscut_axis_separation_v2
import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two
import Submission.Work.ELRig.crossing_arc_separation
import Submission.Work.ELRig.joined_of_not_crossing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-! ## Comparison of the local and the global crossing conditions -/

private lemma crossing_iff_global_aux {f : ℝ → ℝ} {sL sR s₀ : ℝ} (hsL : sL < s₀) (hsR : s₀ < sR)
    (hf : ContinuousOn f (Set.Icc sL sR)) (hne : ∀ s ∈ Set.Icc sL sR, s ≠ s₀ → f s ≠ 0) :
    ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, f s < 0) ∧ (∀ s ∈ Set.Ioo s₀ (s₀ + ε), 0 < f s)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, 0 < f s) ∧ (∀ s ∈ Set.Ioo s₀ (s₀ + ε), f s < 0)))
    ↔
    ((∀ s ∈ Set.Ioo sL s₀, f s < 0) ∧ (∀ s ∈ Set.Ioo s₀ sR, 0 < f s)) ∨
      ((∀ s ∈ Set.Ioo sL s₀, 0 < f s) ∧ (∀ s ∈ Set.Ioo s₀ sR, f s < 0)) := by
  have hIccL : Set.Ioo sL s₀ ⊆ Set.Icc sL sR := fun x hx =>
    ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hsR)⟩
  have hIccR : Set.Ioo s₀ sR ⊆ Set.Icc sL sR := fun x hx =>
    ⟨le_of_lt (lt_trans hsL hx.1), le_of_lt hx.2⟩
  have hpcL : IsPreconnected (Set.Ioo sL s₀) := isPreconnected_Ioo
  have hpcR : IsPreconnected (Set.Ioo s₀ sR) := isPreconnected_Ioo
  have hcontL : ContinuousOn f (Set.Ioo sL s₀) := hf.mono hIccL
  have hcontR : ContinuousOn f (Set.Ioo s₀ sR) := hf.mono hIccR
  have hneL : ∀ s ∈ Set.Ioo sL s₀, f s ≠ 0 := fun s hs => hne s (hIccL hs) (ne_of_lt hs.2)
  have hneR : ∀ s ∈ Set.Ioo s₀ sR, f s ≠ 0 := fun s hs => hne s (hIccR hs) (ne_of_gt hs.1)
  have keyL : ∀ ε > 0, ∃ s' ∈ Set.Ioo sL s₀, s' ∈ Set.Ioo (s₀ - ε) s₀ := by
    intro ε hε
    have hm : max (s₀ - ε) sL < s₀ := by rw [max_lt_iff]; exact ⟨by linarith, hsL⟩
    refine ⟨(max (s₀ - ε) sL + s₀) / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have := le_max_right (s₀ - ε) sL; linarith
    · linarith
    · have := le_max_left (s₀ - ε) sL; linarith
    · linarith
  have keyR : ∀ ε > 0, ∃ s' ∈ Set.Ioo s₀ sR, s' ∈ Set.Ioo s₀ (s₀ + ε) := by
    intro ε hε
    have hm : s₀ < min (s₀ + ε) sR := by rw [lt_min_iff]; exact ⟨by linarith, hsR⟩
    refine ⟨(s₀ + min (s₀ + ε) sR) / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith
    · have := min_le_right (s₀ + ε) sR; linarith
    · linarith
    · have := min_le_left (s₀ + ε) sR; linarith
  constructor
  · rintro (⟨ε, hε, hL, hR⟩ | ⟨ε, hε, hL, hR⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · intro s hs
        obtain ⟨s', hs', hs'e⟩ := keyL ε hε
        have hlt : f s' < 0 := hL s' hs'e
        have hns : ¬ (0 < f s) := fun h =>
          (not_lt.mpr hlt.le) ((sign_iff_of_isPreconnected hpcL hcontL hneL hs hs').mp h)
        exact lt_of_le_of_ne (le_of_not_gt hns) (hneL s hs)
      · intro s hs
        obtain ⟨s', hs', hs'e⟩ := keyR ε hε
        have hpos : 0 < f s' := hR s' hs'e
        have hns : ¬ (f s < 0) := fun h =>
          (not_lt.mpr h.le) ((sign_iff_of_isPreconnected hpcR hcontR hneR hs hs').mpr hpos)
        exact lt_of_le_of_ne (le_of_not_gt hns) (Ne.symm (hneR s hs))
    · refine Or.inr ⟨?_, ?_⟩
      · intro s hs
        obtain ⟨s', hs', hs'e⟩ := keyL ε hε
        have hpos : 0 < f s' := hL s' hs'e
        have hns : ¬ (f s < 0) := fun h =>
          (not_lt.mpr h.le) ((sign_iff_of_isPreconnected hpcL hcontL hneL hs hs').mpr hpos)
        exact lt_of_le_of_ne (le_of_not_gt hns) (Ne.symm (hneL s hs))
      · intro s hs
        obtain ⟨s', hs', hs'e⟩ := keyR ε hε
        have hlt : f s' < 0 := hR s' hs'e
        have hns : ¬ (0 < f s) := fun h =>
          (not_lt.mpr hlt.le) ((sign_iff_of_isPreconnected hpcR hcontR hneR hs hs').mp h)
        exact lt_of_le_of_ne (le_of_not_gt hns) (hneR s hs)
  · rintro (⟨hL, hR⟩ | ⟨hL, hR⟩)
    · refine Or.inl ⟨min (s₀ - sL) (sR - s₀), lt_min (by linarith) (by linarith), ?_, ?_⟩
      · intro s hs
        exact hL s ⟨by have := min_le_left (s₀ - sL) (sR - s₀); linarith [hs.1], hs.2⟩
      · intro s hs
        exact hR s ⟨hs.1, by have := min_le_right (s₀ - sL) (sR - s₀); linarith [hs.2]⟩
    · refine Or.inr ⟨min (s₀ - sL) (sR - s₀), lt_min (by linarith) (by linarith), ?_, ?_⟩
      · intro s hs
        exact hL s ⟨by have := min_le_left (s₀ - sL) (sR - s₀); linarith [hs.1], hs.2⟩
      · intro s hs
        exact hR s ⟨hs.1, by have := min_le_right (s₀ - sL) (sR - s₀); linarith [hs.2]⟩

/-! ## Constant sign of a zero-free continuous function on a preconnected set -/

private lemma const_sign_of_preconnected {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsPreconnected s) {g : Y → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0) :
    (∀ x ∈ s, g x < 0) ∨ (∀ x ∈ s, 0 < g x) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact Or.inl (fun x hx => absurd hx (Set.notMem_empty x))
  · rcases lt_trichotomy (g x0) 0 with h | h | h
    · left; intro x hx
      have hiff := sign_iff_of_isPreconnected hs hg hne hx hx0
      by_contra hcon
      exact absurd (hiff.mp (lt_of_le_of_ne (le_of_not_gt hcon) (Ne.symm (hne x hx))))
        (not_lt.mpr h.le)
    · exact absurd h (hne x0 hx0)
    · right; intro x hx
      exact (sign_iff_of_isPreconnected hs hg hne hx hx0).mpr h

/-! ## Connected components of the complement -/

private lemma joinedIn_of_mem_comp {W : Set ℂ} (hW : IsOpen W) {x y : ℂ}
    (hxy : connectedComponentIn W x = connectedComponentIn W y) (hx : x ∈ W) (hy : y ∈ W) :
    JoinedIn W x y := by
  have hx' : x ∈ connectedComponentIn W x := mem_connectedComponentIn hx
  have hy' : y ∈ connectedComponentIn W x := hxy ▸ mem_connectedComponentIn hy
  have hopen : IsOpen (connectedComponentIn W x) := hW.connectedComponentIn
  have hconn : IsConnected (connectedComponentIn W x) := isConnected_connectedComponentIn_iff.mpr hx
  have hpath : IsPathConnected (connectedComponentIn W x) :=
    (hopen.isConnected_iff_isPathConnected).mp hconn
  exact (hpath.joinedIn x hx' y hy').mono (connectedComponentIn_subset W x)

private lemma sign_const_on_comp {W : Set ℂ} {g : ℂ → ℝ} (hcont : ContinuousOn g W)
    (hne : ∀ w ∈ W, g w ≠ 0) {u v : ℂ} (hu : u ∈ W) (hv : v ∈ W)
    (huv : connectedComponentIn W u = connectedComponentIn W v) : (0 < g u ↔ 0 < g v) := by
  have hu' : u ∈ connectedComponentIn W u := mem_connectedComponentIn hu
  have hv' : v ∈ connectedComponentIn W u := huv ▸ mem_connectedComponentIn hv
  have hpc : IsPreconnected (connectedComponentIn W u) := isPreconnected_connectedComponentIn
  have hc : ContinuousOn g (connectedComponentIn W u) := hcont.mono (connectedComponentIn_subset W u)
  have hn : ∀ w ∈ connectedComponentIn W u, g w ≠ 0 :=
    fun w hw => hne w (connectedComponentIn_subset W u hw)
  exact sign_iff_of_isPreconnected hpc hc hn hu' hv'

/-- At most two connected components of `ball p r \ A '' [sL,sR]`. -/
private lemma at_most_two_components {p : ℂ} {r : ℝ} (hr : 0 < r) {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hsL : sL < s₀) (hsR : s₀ < sR) (hAc : ContinuousOn A (Set.Icc sL sR))
    (hAi : Set.InjOn A (Set.Icc sL sR))
    (hsphL : A sL ∈ Metric.sphere p r) (hsphR : A sR ∈ Metric.sphere p r)
    (hint : ∀ s ∈ Set.Ioo sL sR, A s ∈ Metric.ball p r)
    {x y z : ℂ} (hx : x ∈ Metric.ball p r \ (A '' Set.Icc sL sR))
    (hy : y ∈ Metric.ball p r \ (A '' Set.Icc sL sR))
    (hz : z ∈ Metric.ball p r \ (A '' Set.Icc sL sR)) :
    connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) x =
        connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) y ∨
      connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) y =
        connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) z ∨
      connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) x =
        connectedComponentIn (Metric.ball p r \ (A '' Set.Icc sL sR)) z := by
  have hΔpos : 0 < sR - sL := by linarith
  have hΔne : (sR - sL) ≠ 0 := ne_of_gt hΔpos
  have hmaps : ∀ u : Set.Icc (0:ℝ) 1, sL + (u:ℝ) * (sR - sL) ∈ Set.Icc sL sR := by
    intro u
    exact ⟨by nlinarith [u.2.1, u.2.2, hΔpos], by nlinarith [u.2.1, u.2.2, hΔpos]⟩
  have hβcont : Continuous (fun u : Set.Icc (0:ℝ) 1 => A (sL + (u:ℝ) * (sR - sL))) :=
    hAc.comp_continuous (by fun_prop) hmaps
  set β : C(Set.Icc (0:ℝ) 1, ℂ) :=
    ⟨fun u => A (sL + (u:ℝ) * (sR - sL)), hβcont⟩ with hβdef
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : A (sL + (u:ℝ) * (sR - sL)) = A (sL + (v:ℝ) * (sR - sL)) := huv
    have h2 := hAi (hmaps u) (hmaps v) h1
    have : (u:ℝ) * (sR - sL) = (v:ℝ) * (sR - sL) := by linarith
    have h3 : (u:ℝ) = (v:ℝ) := mul_right_cancel₀ hΔne this
    exact Subtype.ext h3
  have hrange : Set.range β = A '' Set.Icc sL sR := by
    ext w; constructor
    · rintro ⟨u, rfl⟩
      exact ⟨sL + (u:ℝ) * (sR - sL), hmaps u, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨(s - sL) / (sR - sL), ?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hs.1]) (le_of_lt hΔpos)
      · rw [div_le_one hΔpos]; linarith [hs.2]
      · change A (sL + ((s - sL) / (sR - sL)) * (sR - sL)) = A s
        rw [show sL + ((s - sL) / (sR - sL)) * (sR - sL) = s by field_simp; ring]
  have hβ0 : β 0 ∈ Metric.sphere p r := by
    have h : (β 0 : ℂ) = A sL := by
      change A (sL + ((0:Set.Icc (0:ℝ) 1):ℝ) * (sR - sL)) = A sL
      congr 1; simp
    rw [h]; exact hsphL
  have hβ1 : β 1 ∈ Metric.sphere p r := by
    have h : (β 1 : ℂ) = A sR := by
      change A (sL + ((1:Set.Icc (0:ℝ) 1):ℝ) * (sR - sL)) = A sR
      congr 1
      rw [show ((1:Set.Icc (0:ℝ) 1):ℝ) = 1 from rfl, one_mul,
        show sL + (sR - sL) = sR from by ring]
    rw [h]; exact hsphR
  have hβint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball p r := by
    intro t ht0 ht1
    have ht := hmaps t
    change A (sL + (t:ℝ) * (sR - sL)) ∈ Metric.ball p r
    have hne0 : sL + (t:ℝ) * (sR - sL) ≠ sL := by
      intro hc
      apply ht0
      have : (β t : ℂ) = A sL := by
        change A (sL + (t:ℝ) * (sR - sL)) = A sL
        rw [hc]
      rw [show (β 0 : ℂ) = A sL from by
        change A (sL + ((0:Set.Icc (0:ℝ) 1):ℝ) * (sR - sL)) = A sL
        congr 1; simp, this]
    have hne1 : sL + (t:ℝ) * (sR - sL) ≠ sR := by
      intro hc
      apply ht1
      have : (β t : ℂ) = A sR := by
        change A (sL + (t:ℝ) * (sR - sL)) = A sR
        rw [hc]
      rw [show (β 1 : ℂ) = A sR from by
        change A (sL + ((1:Set.Icc (0:ℝ) 1):ℝ) * (sR - sL)) = A sR
        congr 1
        rw [show ((1:Set.Icc (0:ℝ) 1):ℝ) = 1 from rfl, one_mul,
          show sL + (sR - sL) = sR from by ring], this]
    exact hint _ ⟨lt_of_le_of_ne ht.1 (Ne.symm hne0), lt_of_le_of_ne ht.2 hne1⟩
  have hkey := Commons.Topology.Jordan.crosscut_complement_at_most_two p hr β hβinj hβ0 hβ1
    hβint hx.1 hy.1 hz.1 (by rw [hrange]; exact hx.2) (by rw [hrange]; exact hy.2)
    (by rw [hrange]; exact hz.2)
  rw [hrange] at hkey
  exact hkey

/-! ## Both signs occur arbitrarily close to the centre -/

private lemma both_signs {p : ℂ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hp0 : (h p).im = 0)
    (hopen : ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball p r → IsOpen (h '' s)) :
    (∀ ε > 0, ∃ w : ℂ, ‖w - p‖ < ε ∧ ‖w - p‖ < r ∧ 0 < (h w).im) ∧
      (∀ ε > 0, ∃ w : ℂ, ‖w - p‖ < ε ∧ ‖w - p‖ < r ∧ (h w).im < 0) := by
  have openness_step : ∀ ε > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ρ < r ∧
      ∃ δ > 0, Metric.ball (h p) δ ⊆ h '' Metric.ball p ρ := by
    intro ε hε
    set ρ : ℝ := min ε r / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hρltε : ρ < ε := by
      rw [hρdef]; have := min_le_left ε r; have := min_le_right ε r; linarith
    have hρltr : ρ < r := by rw [hρdef]; have := min_le_right ε r; linarith
    have hop : IsOpen (h '' Metric.ball p ρ) :=
      hopen _ Metric.isOpen_ball (Metric.ball_subset_ball hρltr.le)
    have hpin : p ∈ Metric.ball p ρ := by rw [Metric.mem_ball, dist_self]; exact hρpos
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hop (h p) ⟨p, hpin, rfl⟩
    exact ⟨ρ, hρpos, hρltε, hρltr, δ, hδpos, hδsub⟩
  constructor
  · intro ε hε
    obtain ⟨ρ, hρpos, hρltε, hρltr, δ, hδpos, hδsub⟩ := openness_step ε hε
    have hmpos : 0 < min δ 1 / 2 := by positivity
    set q : ℂ := h p + (((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I with hqdef
    have hqim : q.im = min δ 1 / 2 := by rw [hqdef]; simp [Complex.add_im, Complex.mul_im, hp0]
    have hqdist : dist q (h p) < δ := by
      rw [hqdef, dist_eq_norm,
        show h p + (((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I - h p
          = (((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I by ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hmpos]
      have := min_le_left δ 1; linarith
    obtain ⟨w, hwball, hwq⟩ := hδsub hqdist
    have hw1 : ‖w - p‖ < ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwball
    exact ⟨w, lt_of_lt_of_le hw1 hρltε.le, lt_of_lt_of_le hw1 hρltr.le,
      by rw [hwq, hqim]; exact hmpos⟩
  · intro ε hε
    obtain ⟨ρ, hρpos, hρltε, hρltr, δ, hδpos, hδsub⟩ := openness_step ε hε
    have hmpos : 0 < min δ 1 / 2 := by positivity
    set q : ℂ := h p - (((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I with hqdef
    have hqim : q.im = -(min δ 1 / 2) := by rw [hqdef]; simp [Complex.sub_im, Complex.mul_im, hp0]
    have hqdist : dist q (h p) < δ := by
      rw [hqdef, dist_eq_norm,
        show h p - (((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I - h p
          = -((((min δ 1 / 2 : ℝ)) : ℂ) * Complex.I) by ring,
        norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hmpos]
      have := min_le_left δ 1; linarith
    obtain ⟨w, hwball, hwq⟩ := hδsub hqdist
    have hw1 : ‖w - p‖ < ρ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwball
    exact ⟨w, lt_of_lt_of_le hw1 hρltε.le, lt_of_lt_of_le hw1 hρltr.le,
      by rw [hwq, hqim]; linarith⟩

/-! ## The main theorem -/

set_option linter.unusedVariables false in
theorem crossing_of_local_structure {p : ℂ} {r : ℝ} (hr : 0 < r) {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hsL : sL < s₀) (hsR : s₀ < sR)
    (hAc : ContinuousOn A (Set.Icc sL sR)) (hAi : Set.InjOn A (Set.Icc sL sR)) (hAp : A s₀ = p)
    (hsphL : A sL ∈ Metric.sphere p r) (hsphR : A sR ∈ Metric.sphere p r)
    (hint : ∀ s ∈ Set.Ioo sL sR, A s ∈ Metric.ball p r)
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    {h : ℂ → ℂ} (hcont : ContinuousOn h (Metric.ball p r))
    (hopen : ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball p r → IsOpen (h '' s))
    (hzero : ∀ w : ℂ, ‖w - p‖ ≤ r → ((h w).im = 0 ↔ ∃ s ∈ Set.Icc sL sR, A s = w))
    (hray : ∀ t : ℝ, 0 < t → t ≤ r → p + t ∉ Set.range A ∧ p - t ∉ Set.range A) :
    ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (A s).im < p.im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), p.im < (A s).im)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, p.im < (A s).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (A s).im < p.im))) ↔
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      ((0 < (h (p + t)).im ∧ (h (p - t)).im < 0) ∨
        ((h (p + t)).im < 0 ∧ 0 < (h (p - t)).im))) := by
  have hp0 : (h p).im = 0 :=
    (hzero p (by rw [sub_self, norm_zero]; exact hr.le)).mpr
      ⟨s₀, ⟨le_of_lt hsL, le_of_lt hsR⟩, hAp⟩
  have hline' : ∀ s ∈ Set.Icc sL sR, s ≠ s₀ → (A s).im ≠ p.im := by
    intro s hs hne him
    have hAsp : A s = p := by
      by_contra hc; exact (hline s hs hc) him
    exact hne (hAi hs ⟨le_of_lt hsL, le_of_lt hsR⟩ (hAsp.trans hAp.symm))
  have hclosed : ∀ s ∈ Set.Icc sL sR, A s ∈ Metric.closedBall p r := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1]; exact Metric.sphere_subset_closedBall hsphL
    · rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2]; exact Metric.sphere_subset_closedBall hsphR
      · exact Metric.ball_subset_closedBall (hint s ⟨h1, h2⟩)
  set Z : Set ℂ := A '' Set.Icc sL sR with hZdef
  set W : Set ℂ := Metric.ball p r \ Z with hWdef
  let g : ℂ → ℝ := fun w => (h w).im
  have hW_eq : W = Metric.ball p r \ (A '' Set.Icc sL sR) := by rw [hWdef, hZdef]
  have hZclosed : IsClosed Z := by
    rw [hZdef]; exact (isCompact_Icc.image_of_continuousOn hAc).isClosed
  have hWopen : IsOpen W := by rw [hWdef]; exact Metric.isOpen_ball.sdiff hZclosed
  have hgcontW : ContinuousOn g W :=
    (Complex.continuous_im.comp_continuousOn hcont).mono Set.sdiff_subset
  have hgneW : ∀ w ∈ W, g w ≠ 0 := by
    intro w hw h0
    rw [hWdef] at hw
    have hwr : ‖w - p‖ < r := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw.1
    exact hw.2 (by rw [hZdef]; exact (hzero w (le_of_lt hwr)).mp h0)
  have hmemA : ∀ (σ : ℂ) (t : ℝ), 0 < t → (σ = p + (t:ℂ) ∨ σ = p - (t:ℂ)) → σ ∉ Z := by
    intro σ t ht hσ hZ
    rw [hZdef] at hZ
    obtain ⟨s, hs, hsA⟩ := hZ
    have him : (A s).im = p.im := by
      rcases hσ with hσ | hσ
      · rw [hsA, hσ]; simp
      · rw [hsA, hσ]; simp
    have hss : s = s₀ := by by_contra hne; exact hline' s hs hne him
    have hσp : σ = p := by rw [← hsA, hss, hAp]
    rcases hσ with hσ | hσ
    · exact absurd (by exact_mod_cast (add_eq_left.mp (hσ.symm.trans hσp) : (t:ℂ) = 0) : t = 0)
        (ne_of_gt ht)
    · exact absurd (by exact_mod_cast (sub_eq_self.mp (hσ.symm.trans hσp) : (t:ℂ) = 0) : t = 0)
        (ne_of_gt ht)
  have hmemW : ∀ t : ℝ, 0 < t → t < r → p + (t:ℂ) ∈ W ∧ p - (t:ℂ) ∈ W := by
    intro t ht htr
    exact ⟨⟨by rw [Metric.mem_ball, dist_add_real, abs_of_pos ht]; exact htr, hmemA _ t ht (Or.inl rfl)⟩,
      ⟨by rw [Metric.mem_ball, dist_sub_real, abs_of_pos ht]; exact htr,
        hmemA _ t ht (Or.inr rfl)⟩⟩
  have hfcont : ContinuousOn (fun s : ℝ => (A s).im - p.im) (Set.Icc sL sR) :=
    (Complex.continuous_im.comp_continuousOn hAc).sub continuousOn_const
  have hfne : ∀ s ∈ Set.Icc sL sR, s ≠ s₀ → (A s).im - p.im ≠ 0 :=
    fun s hs hne h0 => hline' s hs hne (sub_eq_zero.mp h0)
  have hsubL : Set.Ioo sL s₀ ⊆ Set.Icc sL sR := fun x hx =>
    ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hsR)⟩
  have hsubR : Set.Ioo s₀ sR ⊆ Set.Icc sL sR := fun x hx =>
    ⟨le_of_lt (lt_trans hsL hx.1), le_of_lt hx.2⟩
  have hLiff :
      ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (A s).im < p.im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), p.im < (A s).im)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, p.im < (A s).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (A s).im < p.im))) ↔
      (((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)) ∨
        ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im))) := by
    have hkey := crossing_iff_global_aux (f := fun s : ℝ => (A s).im - p.im) hsL hsR hfcont hfne
    constructor
    · intro hh
      have h1 : ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (A s).im - p.im < 0) ∧
            (∀ s ∈ Set.Ioo s₀ (s₀ + ε), 0 < (A s).im - p.im)) ∨
          (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, 0 < (A s).im - p.im) ∧
            (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (A s).im - p.im < 0))) := by
        simpa only [sub_neg, sub_pos] using hh
      have h2 := hkey.mp h1
      simpa only [sub_neg, sub_pos] using h2
    · intro hh
      have h1 : (((∀ s ∈ Set.Ioo sL s₀, (A s).im - p.im < 0) ∧
            (∀ s ∈ Set.Ioo s₀ sR, 0 < (A s).im - p.im)) ∨
          ((∀ s ∈ Set.Ioo sL s₀, 0 < (A s).im - p.im) ∧
            (∀ s ∈ Set.Ioo s₀ sR, (A s).im - p.im < 0))) := by
        simpa only [sub_neg, sub_pos] using hh
      have h2 := hkey.mpr h1
      simpa only [sub_neg, sub_pos] using h2
  have hsigL : (∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∨
      (∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) := by
    rcases const_sign_of_preconnected isPreconnected_Ioo (hfcont.mono hsubL)
      (fun s hs => hfne s (hsubL hs) (ne_of_lt hs.2)) with hh | hh
    · left; intro s hs; have := hh s hs; rwa [sub_neg] at this
    · right; intro s hs; have := hh s hs; rwa [sub_pos] at this
  have hsigR : (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im) ∨
      (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im) := by
    rcases const_sign_of_preconnected isPreconnected_Ioo (hfcont.mono hsubR)
      (fun s hs => hfne s (hsubR hs) (ne_of_gt hs.1)) with hh | hh
    · left; intro s hs; have := hh s hs; rwa [sub_neg] at this
    · right; intro s hs; have := hh s hs; rwa [sub_pos] at this
  have htrich :
      (((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)) ∨
        ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im))) ∨
      (((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im)) ∨
        ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im))) := by
    rcases hsigL with hl | hl <;> rcases hsigR with hr | hr
    · exact Or.inr (Or.inl ⟨hl, hr⟩)
    · exact Or.inl (Or.inl ⟨hl, hr⟩)
    · exact Or.inl (Or.inr ⟨hl, hr⟩)
    · exact Or.inr (Or.inr ⟨hl, hr⟩)
  constructor
  · -- L → R
    intro hL
    have hcross := hLiff.mp hL
    obtain ⟨hpos, hneg⟩ := both_signs hr hp0 hopen
    have memW_of : ∀ w : ℂ, ‖w - p‖ < r → g w ≠ 0 → w ∈ W := by
      intro w hwr hwne
      rw [hWdef]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]; exact hwr
      · intro hZmem
        rw [hZdef] at hZmem
        obtain ⟨s, hs, hsA⟩ := hZmem
        have hle : ‖A s - p‖ ≤ r := by rw [hsA]; exact le_of_lt hwr
        have h0 : (h (A s)).im = 0 := (hzero (A s) hle).mpr ⟨s, hs, rfl⟩
        rw [hsA] at h0
        exact hwne h0
    have hcomp_ne : ∀ t : ℝ, 0 < t → t < r →
        connectedComponentIn W (p + (t:ℂ)) ≠ connectedComponentIn W (p - (t:ℂ)) := by
      intro t ht htr heq
      exact (crossing_arc_separation hr hsL hsR hAc hAi hAp hsphL hsphR hint hline hcross
          t ht htr)
        (by
          rw [← hW_eq]
          exact joinedIn_of_mem_comp hWopen heq (hmemW t ht htr).1 (hmemW t ht htr).2)
    have hsign_opp : ∀ t : ℝ, 0 < t → t < r →
        (0 < g (p + (t:ℂ)) ∧ g (p - (t:ℂ)) < 0) ∨
          (g (p + (t:ℂ)) < 0 ∧ 0 < g (p - (t:ℂ))) := by
      intro t ht htr
      obtain ⟨wp, hwpr, -, hwppos⟩ := hpos r hr
      obtain ⟨wm, hwmr, -, hwmneg⟩ := hneg r hr
      have hwpW : wp ∈ W := memW_of wp hwpr (ne_of_gt hwppos)
      have hwmW : wm ∈ W := memW_of wm hwmr (ne_of_lt hwmneg)
      have hptW : p + (t:ℂ) ∈ W := (hmemW t ht htr).1
      have hmtW : p - (t:ℂ) ∈ W := (hmemW t ht htr).2
      have hpm_ne : connectedComponentIn W wp ≠ connectedComponentIn W wm := by
        intro heq
        have hiff := sign_const_on_comp hgcontW hgneW hwpW hwmW heq
        exact absurd (hiff.mp hwppos) (not_lt.mpr hwmneg.le)
      have hpt_comp := at_most_two_components hr hsL hsR hAc hAi hsphL hsphR hint
        hptW hwpW hwmW
      have hpt_cases : connectedComponentIn W (p + (t:ℂ)) = connectedComponentIn W wp ∨
          connectedComponentIn W (p + (t:ℂ)) = connectedComponentIn W wm := by
        rcases hpt_comp with h | h | h
        · exact Or.inl h
        · exact absurd h hpm_ne
        · exact Or.inr h
      have hmt_comp := at_most_two_components hr hsL hsR hAc hAi hsphL hsphR hint
        hmtW hwpW hwmW
      have hmt_cases : connectedComponentIn W (p - (t:ℂ)) = connectedComponentIn W wp ∨
          connectedComponentIn W (p - (t:ℂ)) = connectedComponentIn W wm := by
        rcases hmt_comp with h | h | h
        · exact Or.inl h
        · exact absurd h hpm_ne
        · exact Or.inr h
      have hne_pt_mt : connectedComponentIn W (p + (t:ℂ)) ≠
          connectedComponentIn W (p - (t:ℂ)) := hcomp_ne t ht htr
      rcases hpt_cases with hptwp | hptwm
      · have hgpt : 0 < g (p + (t:ℂ)) :=
          (sign_const_on_comp hgcontW hgneW hptW hwpW hptwp).mpr hwppos
        have hmtwm : connectedComponentIn W (p - (t:ℂ)) = connectedComponentIn W wm := by
          rcases hmt_cases with h | h
          · exact absurd (h ▸ hptwp) hne_pt_mt
          · exact h
        have hgmt : g (p - (t:ℂ)) < 0 := by
          have hiff := sign_const_on_comp hgcontW hgneW hmtW hwmW hmtwm
          refine lt_of_le_of_ne (le_of_not_gt ?_) (hgneW _ hmtW)
          intro h
          exact absurd (hiff.mp h) (not_lt.mpr hwmneg.le)
        exact Or.inl ⟨hgpt, hgmt⟩
      · have hgpt : g (p + (t:ℂ)) < 0 := by
          have hiff := sign_const_on_comp hgcontW hgneW hptW hwmW hptwm
          refine lt_of_le_of_ne (le_of_not_gt ?_) (hgneW _ hptW)
          intro h
          exact absurd (hiff.mp h) (not_lt.mpr hwmneg.le)
        have hmtwp : connectedComponentIn W (p - (t:ℂ)) = connectedComponentIn W wp := by
          rcases hmt_cases with h | h
          · exact h
          · exact absurd (h ▸ hptwm) hne_pt_mt
        have hgmt : 0 < g (p - (t:ℂ)) :=
          (sign_const_on_comp hgcontW hgneW hmtW hwpW hmtwp).mpr hwppos
        exact Or.inr ⟨hgpt, hgmt⟩
    have hφcont : ContinuousOn (fun u : ℝ => g (p + (u:ℂ))) (Set.Ioo (0:ℝ) r) :=
      hgcontW.comp' (by fun_prop : ContinuousOn (fun u : ℝ => p + (u:ℂ)) (Set.Ioo (0:ℝ) r))
        (fun u hu => (hmemW u hu.1 hu.2).1)
    have hφne : ∀ u ∈ Set.Ioo (0:ℝ) r, g (p + (u:ℂ)) ≠ 0 :=
      fun u hu => hgneW _ (hmemW u hu.1 hu.2).1
    have hψcont : ContinuousOn (fun u : ℝ => g (p - (u:ℂ))) (Set.Ioo (0:ℝ) r) :=
      hgcontW.comp' (by fun_prop : ContinuousOn (fun u : ℝ => p - (u:ℂ)) (Set.Ioo (0:ℝ) r))
        (fun u hu => (hmemW u hu.1 hu.2).2)
    have hψne : ∀ u ∈ Set.Ioo (0:ℝ) r, g (p - (u:ℂ)) ≠ 0 :=
      fun u hu => hgneW _ (hmemW u hu.1 hu.2).2
    refine ⟨r, hr, ?_⟩
    intro t ht
    have htIoo : t ∈ Set.Ioo (0:ℝ) r := ht
    have hhalf : (r/2 : ℝ) ∈ Set.Ioo (0:ℝ) r := ⟨by linarith, by linarith⟩
    rcases hsign_opp (r/2) (by linarith) (by linarith) with hcase | hcase
    · left
      refine ⟨(sign_iff_of_isPreconnected isPreconnected_Ioo hφcont hφne htIoo hhalf).mpr hcase.1, ?_⟩
      have hiff := sign_iff_of_isPreconnected isPreconnected_Ioo hψcont hψne htIoo hhalf
      refine lt_of_le_of_ne (le_of_not_gt ?_) (hgneW _ (hmemW t ht.1 ht.2).2)
      intro h
      exact absurd (hiff.mp h) (not_lt.mpr hcase.2.le)
    · right
      refine ⟨?_, (sign_iff_of_isPreconnected isPreconnected_Ioo hψcont hψne htIoo hhalf).mpr hcase.2⟩
      have hiff := sign_iff_of_isPreconnected isPreconnected_Ioo hφcont hφne htIoo hhalf
      refine lt_of_le_of_ne (le_of_not_gt ?_) (hgneW _ (hmemW t ht.1 ht.2).1)
      intro h
      exact absurd (hiff.mp h) (not_lt.mpr hcase.1.le)
  · -- R → L  (contrapositive)
    intro hR
    by_contra hLnot
    have hsame : ((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧
        (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im)) ∨
        ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)) := by
      rcases htrich with hc | hs
      · exact absurd (hLiff.mpr hc) hLnot
      · exact hs
    obtain ⟨δ, hδpos, hδ⟩ := hR
    set t0 : ℝ := min δ r / 2 with ht0def
    have ht0pos : 0 < t0 := by rw [ht0def]; positivity
    have ht0ltδ : t0 < δ := by
      rw [ht0def]; have := min_le_left δ r; have := min_le_right δ r; linarith
    have ht0ltr : t0 < r := by
      rw [ht0def]; have := min_le_right δ r; linarith
    have hjoined : JoinedIn W (p + (t0:ℂ)) (p - (t0:ℂ)) := by
      rw [hW_eq]
      exact joined_of_not_crossing hr hsL hsR hAc hAp hline hsame t0 ht0pos ht0ltr
    have hsame_sign : (0 < (h (p + (t0:ℂ))).im ↔ 0 < (h (p - (t0:ℂ))).im) :=
      sign_iff_of_joinedIn hgcontW hgneW hjoined
    rcases hδ t0 ⟨ht0pos, ht0ltδ⟩ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd (hsame_sign.mp ha) (not_lt.mpr hb.le)
    · exact absurd (hsame_sign.mpr hb) (not_lt.mpr ha.le)

end Work.ELRig
