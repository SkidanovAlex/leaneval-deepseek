import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# Extending a smooth map off a window, agreeing with it on a smaller window

`Work.Drive.PushDisc.extendSmoothWindow`: a map `G` which is `C^∞` on an open set `U` containing the
box `{|p.1| ≤ X₂, ‖p.2‖ ≤ ρ₂}` can be replaced by a globally `C^∞` map `S` which agrees with `G`,
together with all its derivatives, on the smaller box `{|p.1| ≤ X₁, ‖p.2‖ ≤ ρ₁}`
(`X₁ < X₂`, `ρ₁ < ρ₂`).

The proof is the classical cutoff: a smooth bump `χ`, equal to `1` on a neighbourhood of the small
box and supported in the open box `{|p.1| < X₂, ‖p.2‖ < ρ₂} ⊆ U`, is multiplied into `G`.  The bump
is built explicitly from `Real.smoothTransition`, and the smoothness of `χ • G` is the general
support lemma `contDiff_smul_of_support_subset` below.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff Topology
open Set

/-- **Smoothness of `φ • f` when `φ` is supported inside the domain of smoothness of `f`.**
If `f` is `C^∞` on the open set `u`, `φ` is `C^∞` everywhere, and `support φ ⊆ v` with
`closure v ⊆ u`, then `x ↦ φ x • f x` is `C^∞` everywhere.  (No continuity of `f` off `u` is
needed: outside `u` the multiplier `φ` already vanishes on a whole neighbourhood.) -/
theorem contDiff_smul_of_support_subset {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {φ : E → ℝ} {u v : Set E}
    (hu : IsOpen u) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f u)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hvu : closure v ⊆ u) (hsupp : Function.support φ ⊆ v) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => φ x • f x) := by
  have hts : tsupport φ ⊆ u := (closure_mono hsupp).trans hvu
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ u
  · exact hφ.contDiffAt.smul (hf.contDiffAt (hu.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h => hx (hts h)
    have hmem : ∀ᶠ w in 𝓝 x, φ w = 0 :=
      Filter.mem_of_superset ((isClosed_tsupport φ).isOpen_compl.mem_nhds hx')
        (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport φ h)))
    have hEv : (fun w => φ w • f w) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hmem] with w hw
      simp [hw]
    exact contDiffAt_const.congr_of_eventuallyEq hEv

theorem extendSmoothWindow {k : ℕ}
    (G : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin k))) (hUo : IsOpen U)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U)
    (X₁ ρ₁ X₂ ρ₂ : ℝ) (hX : X₁ < X₂) (hρ : ρ₁ < ρ₂)
    (hU : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X₂ → ‖p.2‖ ≤ ρ₂ → p ∈ U) :
    ∃ S : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S ∧
      (∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X₁ → ‖p.2‖ ≤ ρ₁ → S p = G p) ∧
      (∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X₁ → ‖p.2‖ ≤ ρ₁ →
        fderiv ℝ S p = fderiv ℝ G p) := by
  by_cases hne : ∃ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X₁ ∧ ‖p.2‖ ≤ ρ₁
  · -- The small window is nonempty: all four radii are nonnegative, and we build a cutoff.
    obtain ⟨p₀, hp₀⟩ := hne
    have hX₁ : (0 : ℝ) ≤ X₁ := le_trans (abs_nonneg p₀.1) hp₀.1
    have hρ₁ : (0 : ℝ) ≤ ρ₁ := le_trans (norm_nonneg p₀.2) hp₀.2
    have hX₂ : (0 : ℝ) < X₂ := lt_of_le_of_lt hX₁ hX
    have hρ₂ : (0 : ℝ) < ρ₂ := lt_of_le_of_lt hρ₁ hρ
    obtain ⟨r, hX₁r, hrX₂⟩ : ∃ r : ℝ, X₁ < r ∧ r < X₂ :=
      ⟨(X₁ + X₂) / 2, by linarith, by linarith⟩
    obtain ⟨s, hρ₁s, hsρ₂⟩ : ∃ s : ℝ, ρ₁ < s ∧ s < ρ₂ :=
      ⟨(ρ₁ + ρ₂) / 2, by linarith, by linarith⟩
    have hs0 : (0 : ℝ) ≤ s := le_trans hρ₁ hρ₁s.le
    have hδX : 0 < X₂ - r := by linarith
    have hδY : 0 < ρ₂ ^ 2 - s ^ 2 := by nlinarith
    -- the two cutoffs
    let ξ : ℝ → ℝ := fun t =>
      Real.smoothTransition ((t + X₂) / (X₂ - r)) * Real.smoothTransition ((X₂ - t) / (X₂ - r))
    let ψ : EuclideanSpace ℝ (Fin k) → ℝ := fun y =>
      Real.smoothTransition ((ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2))
    -- `ξ = 1` on `[-r, r]` and `ξ = 0` off `(-X₂, X₂)`
    have hξ1 : ∀ t : ℝ, |t| ≤ r → ξ t = 1 := by
      intro t ht
      have hA : 1 ≤ (t + X₂) / (X₂ - r) := by
        rw [le_div_iff₀ hδX, one_mul]
        linarith [(abs_le.mp ht).1]
      have hB : 1 ≤ (X₂ - t) / (X₂ - r) := by
        rw [le_div_iff₀ hδX, one_mul]
        linarith [(abs_le.mp ht).2]
      change Real.smoothTransition ((t + X₂) / (X₂ - r))
        * Real.smoothTransition ((X₂ - t) / (X₂ - r)) = 1
      rw [Real.smoothTransition.one_of_one_le hA, Real.smoothTransition.one_of_one_le hB,
        mul_one]
    have hξ0 : ∀ t : ℝ, X₂ ≤ |t| → ξ t = 0 := by
      intro t ht
      rcases le_total 0 t with ht0 | ht0
      · have ht' : X₂ ≤ t := by rwa [abs_of_nonneg ht0] at ht
        have hz : (X₂ - t) / (X₂ - r) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hδX.le
        change Real.smoothTransition ((t + X₂) / (X₂ - r))
          * Real.smoothTransition ((X₂ - t) / (X₂ - r)) = 0
        rw [Real.smoothTransition.zero_of_nonpos hz, mul_zero]
      · have ht' : t ≤ -X₂ := by
          have h2 : X₂ ≤ -t := by rwa [abs_of_nonpos ht0] at ht
          linarith
        have hz : (t + X₂) / (X₂ - r) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hδX.le
        change Real.smoothTransition ((t + X₂) / (X₂ - r))
          * Real.smoothTransition ((X₂ - t) / (X₂ - r)) = 0
        rw [Real.smoothTransition.zero_of_nonpos hz, zero_mul]
    -- `ψ = 1` on `B(0, s)` and `ψ = 0` off `B(0, ρ₂)`
    have hψ1 : ∀ y : EuclideanSpace ℝ (Fin k), ‖y‖ ≤ s → ψ y = 1 := by
      intro y hy
      have hys : ‖y‖ ^ 2 ≤ s ^ 2 := by nlinarith [hy, hs0, norm_nonneg y]
      have hone : 1 ≤ (ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2) := by
        rw [le_div_iff₀ hδY, one_mul]
        linarith
      change Real.smoothTransition ((ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2)) = 1
      rw [Real.smoothTransition.one_of_one_le hone]
    have hψ0 : ∀ y : EuclideanSpace ℝ (Fin k), ρ₂ ≤ ‖y‖ → ψ y = 0 := by
      intro y hy
      have hnum : ρ₂ ^ 2 - ‖y‖ ^ 2 ≤ 0 := by nlinarith [hy, hρ₂, norm_nonneg y]
      have hz : (ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnum hδY.le
      change Real.smoothTransition ((ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2)) = 0
      rw [Real.smoothTransition.zero_of_nonpos hz]
    -- both cutoffs are smooth
    have hξsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ := by
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ =>
        Real.smoothTransition ((t + X₂) / (X₂ - r))
          * Real.smoothTransition ((X₂ - t) / (X₂ - r)))
      fun_prop
    have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin k) =>
        Real.smoothTransition ((ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2)))
      have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
      have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin k) =>
          (fun _ : EuclideanSpace ℝ (Fin k) => ρ₂ ^ 2) y - (fun y => ‖y‖ ^ 2) y) :=
        ContDiff.sub contDiff_const hns
      have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin k) =>
          (ρ₂ ^ 2 - ‖y‖ ^ 2) / (ρ₂ ^ 2 - s ^ 2)) :=
        ContDiff.div_const hsub (ρ₂ ^ 2 - s ^ 2)
      exact ContDiff.comp (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))) hlin
    let χ : ℝ × EuclideanSpace ℝ (Fin k) → ℝ := fun p => ξ p.1 * ψ p.2
    have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin k) => ξ p.1 * ψ p.2)
      exact (hξsm.comp contDiff_fst).mul (hψsm.comp contDiff_snd)
    -- `χ = 1` on the small window
    have hχ_one : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ r → ‖p.2‖ ≤ s →
        χ p = 1 := by
      intro p h1 h2
      have ha : ξ p.1 = 1 := hξ1 p.1 h1
      have hb : ψ p.2 = 1 := hψ1 p.2 h2
      change ξ p.1 * ψ p.2 = 1
      rw [ha, hb, one_mul]
    -- and on a whole neighbourhood of it
    have hχ_ev : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ X₁ → ‖p.2‖ ≤ ρ₁ →
        χ =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
      intro p h1 h2
      have hpr : |p.1| < r := lt_of_le_of_lt h1 hX₁r
      have hps : ‖p.2‖ < s := lt_of_le_of_lt h2 hρ₁s
      have hmem : p ∈ Set.Ioo (-r) r ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s := by
        rw [Set.mem_prod, Metric.mem_ball, dist_zero_right]
        exact ⟨abs_lt.mp hpr, hps⟩
      have hopen : IsOpen (Set.Ioo (-r) r ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s) :=
        isOpen_Ioo.prod Metric.isOpen_ball
      have hone : ∀ q ∈ Set.Ioo (-r) r ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s,
          χ q = 1 := by
        intro q hq
        rw [Set.mem_prod, Set.mem_Ioo, Metric.mem_ball, dist_zero_right] at hq
        exact hχ_one q (le_of_lt (abs_lt.mpr hq.1)) (le_of_lt hq.2)
      filter_upwards [hopen.mem_nhds hmem] with q hq
      exact hone q hq
    -- the open box inside which the cutoff lives
    let v : Set (ℝ × EuclideanSpace ℝ (Fin k)) :=
      Set.Ioo (-X₂) X₂ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ₂
    have hcv : closure v ⊆ U := by
      have hvsub : closure v ⊆
          {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ X₂ ∧ ‖p.2‖ ≤ ρ₂} := by
        change closure (Set.Ioo (-X₂) X₂ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ₂)
          ⊆ {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ X₂ ∧ ‖p.2‖ ≤ ρ₂}
        rw [closure_prod_eq, closure_Ioo (by linarith : -X₂ ≠ X₂)]
        intro p hp
        rw [Set.mem_prod, Set.mem_Icc] at hp
        exact ⟨abs_le.mpr ⟨hp.1.1, hp.1.2⟩,
          by simpa only [dist_zero_right] using
            Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hp.2)⟩
      intro p hp
      exact hU p (hvsub hp).1 (hvsub hp).2
    have hsupp : Function.support χ ⊆ v := by
      intro p hp
      rw [Function.mem_support] at hp
      have h1 : ξ p.1 ≠ 0 := fun h => hp (by change ξ p.1 * ψ p.2 = 0; rw [h, zero_mul])
      have h2 : ψ p.2 ≠ 0 := fun h => hp (by change ξ p.1 * ψ p.2 = 0; rw [h, mul_zero])
      have hp1 : |p.1| < X₂ := by
        by_contra hcon
        exact h1 (hξ0 p.1 (le_of_not_gt hcon))
      have hp2 : ‖p.2‖ < ρ₂ := by
        by_contra hcon
        exact h2 (hψ0 p.2 (le_of_not_gt hcon))
      change p ∈ Set.Ioo (-X₂) X₂ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) ρ₂
      rw [Set.mem_prod, Metric.mem_ball, dist_zero_right]
      exact ⟨abs_lt.mp hp1, hp2⟩
    refine ⟨fun p => χ p • G p, ?_, ?_, ?_⟩
    · exact contDiff_smul_of_support_subset hUo hG hχsm hcv hsupp
    · intro p h1 h2
      show χ p • G p = G p
      rw [hχ_one p (le_trans h1 hX₁r.le) (le_trans h2 hρ₁s.le), one_smul]
    · intro p h1 h2
      have hSev : (fun q : ℝ × EuclideanSpace ℝ (Fin k) => χ q • G q) =ᶠ[𝓝 p] G := by
        filter_upwards [hχ_ev p h1 h2] with q hq
        simp [hq]
      exact hSev.fderiv_eq
  · -- The small window is empty: the zero map satisfies every requirement.
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_⟩
    · intro p h1 h2
      exact absurd ⟨p, h1, h2⟩ hne
    · intro p h1 h2
      exact absurd ⟨p, h1, h2⟩ hne

end Work.Drive.PushDisc
