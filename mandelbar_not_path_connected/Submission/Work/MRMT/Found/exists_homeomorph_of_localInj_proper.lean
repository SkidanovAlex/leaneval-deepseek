import Mathlib
import Submission.Work.MRMT.QC.plane_surjective
import Submission.Work.MRMT.Found.hasArgChange_of_homotopy
import Submission.Work.MRMT.Found.hasArgChange_inj
import Submission.Work.MRMT.Found.hasArgChange_sub_iff_of_norm_lt
import Submission.Work.MRMT.Found.surjective_of_decay
import Submission.Work.MRMT.Found.isLocalHomeomorph_of_isOpenMap_localInj
import Submission.Work.MRMT.Found.injective_of_isCoveringMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# From "locally injective, proper, `z + O(1/z)`" to a homeomorphism of `ℂ`

Main result: `Work.MRMT.Found.exists_homeomorph_of_localInj_proper`, see the individual lemmas
below.  The argument replaces Brouwer invariance of domain (absent from Mathlib) by the
*argument change* (winding number) API of `Work.MRMT.QC`.
-/

namespace Work.MRMT.Found

open Set Function Metric Topology Filter

noncomputable section

/-! ## Winding numbers of circles, and the "no extension" fact -/

/-- The positively oriented circle of radius `R > 0` has argument change `1`. -/
theorem hasArgChange_circLoop {R : ℝ} (hR : 0 < R) :
    Work.MRMT.QC.HasArgChange (Work.MRMT.QC.circLoop R) 1 := by
  refine ⟨fun t : ℝ => 2 * Real.pi * t, ⟨?_, ?_⟩, ?_⟩
  · fun_prop
  · intro t ht
    rw [Work.MRMT.QC.norm_circLoop hR.le]
    rfl
  · push_cast
    ring

/-- **No extension.**  If `g` is continuous and non-vanishing on `Metric.closedBall c r`
(`0 ≤ r`), then the boundary loop `t ↦ g (c + r e^{2πit})` has argument change `0`: the radial
homotopy `(s,t) ↦ g (c + s r e^{2πit})` runs through non-vanishing loops from the constant loop
`g c` to the boundary loop. -/
theorem hasArgChange_zero_of_ne_zero_on_closedBall {g : ℂ → ℂ} (hg : Continuous g)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (h0 : ∀ z ∈ Metric.closedBall c r, g z ≠ 0) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => g (c + Work.MRMT.QC.circLoop r t)) 0 := by
  have hconst : Work.MRMT.QC.HasArgChange (fun _ : ℝ => g c) 0 :=
    Work.MRMT.QC.hasArgChange_const (g c)
      (h0 c (by rw [Metric.mem_closedBall, dist_self]; exact hr))
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => g (c + Work.MRMT.QC.circLoop (p.1 * r) p.2)) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
    have h1 : Continuous fun p : ℝ × ℝ => c + Work.MRMT.QC.circLoop (p.1 * r) p.2 := by
      unfold Work.MRMT.QC.circLoop
      fun_prop
    exact (hg.comp h1).continuousOn
  have hloop : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      g (c + Work.MRMT.QC.circLoop (s * r) 1) = g (c + Work.MRMT.QC.circLoop (s * r) 0) := by
    intro s hs
    rw [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g (c + Work.MRMT.QC.circLoop (s * r) t) ≠ 0 := by
    intro s hs t ht
    refine h0 _ ?_
    have hsr : (0 : ℝ) ≤ s * r := mul_nonneg hs.1 hr
    have h2 : s * r ≤ r := by nlinarith [hs.1, hs.2, hr]
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Work.MRMT.QC.norm_circLoop hsr]
    exact h2
  have := hasArgChange_of_homotopy (a := 0) (b := 1) zero_le_one
    (H := fun s t : ℝ => g (c + Work.MRMT.QC.circLoop (s * r) t)) hcont hloop hne
    (by simpa [Work.MRMT.QC.circLoop] using hconst)
  simpa using this

/-! ## Uniform local injectivity -/

/-- Injectivity on the exterior, from the Lipschitz condition on `F - id`. -/
theorem injOn_of_lipschitz_away {F : ℂ → ℂ} {R : ℝ}
    (hlip : ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖) :
    Set.InjOn F {z : ℂ | R ≤ ‖z‖} := by
  intro z₁ h₁ z₂ h₂ heq
  have h := hlip z₁ z₂ h₁ h₂
  have hsub : (F z₁ - z₁) - (F z₂ - z₂) = z₂ - z₁ := by rw [heq]; ring
  rw [hsub, norm_sub_rev] at h
  have hnn : (0 : ℝ) ≤ ‖z₁ - z₂‖ := norm_nonneg _
  have hz : ‖z₁ - z₂‖ = 0 := le_antisymm (by linarith) hnn
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- **Uniform local injectivity.**  A locally injective map that is injective outside a ball is
injective on every pair of points at distance at most some `ε₀ > 0`. -/
theorem exists_uniform_local_injective {F : ℂ → ℂ}
    (hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn F U) {R : ℝ}
    (hinjExt : Set.InjOn F {z : ℂ | R ≤ ‖z‖}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ z z' : ℂ, z ≠ z' → ‖z - z'‖ ≤ ε₀ → F z ≠ F z' := by
  classical
  have key : ∀ a b : ℂ, F a = F b → a ≠ b → ‖a - b‖ ≤ 1 → ‖a‖ ≤ R + 1 := by
    intro a b hab hnab hdab
    by_contra hcon
    rw [not_le] at hcon
    have ha : R ≤ ‖a‖ := by linarith
    have hb : R ≤ ‖b‖ := by
      have h1 : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := (abs_le.mp (abs_norm_sub_norm_le a b)).2
      linarith
    exact hnab (hinjExt ha hb hab)
  have key' : ∀ a b : ℂ, F a = F b → a ≠ b → ‖a - b‖ ≤ 1 → ‖b‖ ≤ R + 1 := by
    intro a b hab hnab hdab
    exact key b a hab.symm (Ne.symm hnab) (by rwa [norm_sub_rev])
  by_contra h
  push Not at h
  choose z z' hz using fun n : ℕ => h (1 / (n + 1)) (by positivity)
  have hzn : ∀ n, z n ≠ z' n := fun n => (hz n).1
  have hzd : ∀ n, ‖z n - z' n‖ ≤ 1 / (n + 1) := fun n => (hz n).2.1
  have hzF : ∀ n, F (z n) = F (z' n) := fun n => (hz n).2.2
  have hd1 : ∀ n, ‖z n - z' n‖ ≤ 1 := by
    intro n
    have h2 : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    linarith [hzd n]
  have hmem : ∀ n, (z n, z' n) ∈
      Metric.closedBall (0 : ℂ) (R + 1) ×ˢ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro n
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using key _ _ (hzF n) (hzn n) (hd1 n),
      by simpa [Metric.mem_closedBall, dist_zero_right] using key' _ _ (hzF n) (hzn n) (hd1 n)⟩
  obtain ⟨p, hp, φ, hφmono, hφtend⟩ :=
    ((isCompact_closedBall (0 : ℂ) (R + 1)).prod
      (isCompact_closedBall (0 : ℂ) (R + 1))).tendsto_subseq (x := fun n => (z n, z' n)) hmem
  have h1 : Tendsto (fun n => z (φ n)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hφtend
  have h2 : Tendsto (fun n => z' (φ n)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hφtend
  have h3 : Tendsto (fun n => z (φ n) - z' (φ n)) atTop (𝓝 (p.1 - p.2)) := h1.sub h2
  have h4 : Tendsto (fun n => z (φ n) - z' (φ n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hzd (φ n)) ?_
    have h' : Tendsto (fun n : ℕ => (1 : ℝ) / (φ n + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφmono.tendsto_atTop
    simpa [Function.comp_def] using h'
  have hp12 : p.1 = p.2 := sub_eq_zero.mp (tendsto_nhds_unique h3 h4)
  obtain ⟨U, hU, hinjU⟩ := hli p.1
  obtain ⟨V, hVU, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hU
  have hpV2 : p.2 ∈ V := by rw [← hp12]; exact hpV
  have hV1 : ∀ᶠ n in atTop, z (φ n) ∈ V := h1.eventually (hVopen.mem_nhds hpV)
  have hV2 : ∀ᶠ n in atTop, z' (φ n) ∈ V := h2.eventually (hVopen.mem_nhds hpV2)
  obtain ⟨n, hn1, hn2⟩ := (hV1.and hV2).exists
  exact (hzn (φ n)) (hinjU (hVU hn1) (hVU hn2) (hzF (φ n)))

/-! ## The local degree far out, and its local constancy -/

/-- Far away from the origin, `F` is a `½`-perturbation of the identity, so the circle of radius
`ρ` around `z` is mapped to a loop of argument change `1`. -/
theorem argChange_small_circle_of_away {F : ℂ → ℂ} (hcont : Continuous F) {R : ℝ}
    (hlip : ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖)
    {z : ℂ} (hz : R < ‖z‖) {ρ : ℝ} (hρ : 0 < ρ) (hρz : ρ ≤ ‖z‖ - R) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) 1 := by
  have hγcont : ContinuousOn (Work.MRMT.QC.circLoop ρ) (Set.Icc 0 1) :=
    (Work.MRMT.QC.continuous_circLoop ρ).continuousOn
  have hγ'cont : ContinuousOn (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z)
      (Set.Icc 0 1) :=
    ((hcont.comp (continuous_const.add (Work.MRMT.QC.continuous_circLoop ρ))).sub
      continuous_const).continuousOn
  have hloop : Work.MRMT.QC.circLoop ρ 1 = Work.MRMT.QC.circLoop ρ 0 := by
    rw [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
  have hloop' : (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) 1
      = (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) 0 := by
    simp only [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
  refine Work.MRMT.QC.hasArgChange_of_close (hasArgChange_circLoop hρ) hloop hloop'
    hγcont hγ'cont ?_
  intro t ht
  rw [Work.MRMT.QC.norm_circLoop hρ.le]
  have hzζ : R ≤ ‖z + Work.MRMT.QC.circLoop ρ t‖ := by
    have h2 : ‖z‖ - ‖Work.MRMT.QC.circLoop ρ t‖ ≤ ‖z + Work.MRMT.QC.circLoop ρ t‖ := by
      have h3 := (abs_le.mp (abs_norm_sub_norm_le z (-(Work.MRMT.QC.circLoop ρ t)))).2
      simp only [norm_neg] at h3
      rwa [sub_neg_eq_add] at h3
    rw [Work.MRMT.QC.norm_circLoop hρ.le] at h2
    linarith
  have hl := hlip (z + Work.MRMT.QC.circLoop ρ t) z hzζ (le_of_lt hz)
  have hζ : ‖(z + Work.MRMT.QC.circLoop ρ t) - z‖ = ρ := by
    rw [add_sub_cancel_left, Work.MRMT.QC.norm_circLoop hρ.le]
  rw [hζ] at hl
  have hsub : F (z + Work.MRMT.QC.circLoop ρ t) - F z - Work.MRMT.QC.circLoop ρ t
      = (F (z + Work.MRMT.QC.circLoop ρ t) - (z + Work.MRMT.QC.circLoop ρ t)) - (F z - z) := by
    ring
  rw [hsub]
  linarith

/-- **Local constancy of the local degree.**  If `F` is injective on pairs of points at distance
`≤ ε₀`, then the argument change of the loop of radius `ρ ≤ ε₀/2` around `z` does not change when
`z` is moved by at most `ε₀/2`. -/
theorem argChange_small_circle_eq_of_close {F : ℂ → ℂ} (hcont : Continuous F) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hinj : ∀ z z' : ℂ, z ≠ z' → ‖z - z'‖ ≤ ε₀ → F z ≠ F z')
    {z z' : ℂ} (hz : ‖z - z'‖ ≤ ε₀ / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ ε₀ / 2) {k : ℤ}
    (h : Work.MRMT.QC.HasArgChange (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) k) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => F (z' + Work.MRMT.QC.circLoop ρ t) - F z') k := by
  have hρle : ρ ≤ ε₀ := by linarith
  have hcirc : Continuous fun p : ℝ × ℝ => Work.MRMT.QC.circLoop ρ p.2 :=
    (Work.MRMT.QC.continuous_circLoop ρ).comp continuous_snd
  have hlin : Continuous fun p : ℝ × ℝ => z + (p.1 : ℂ) * (z' - z) := by fun_prop
  have hcontH : ContinuousOn
      (fun p : ℝ × ℝ => F (z + (p.1 : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ p.2)
        - F (z + (p.1 : ℂ) * (z' - z))) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) :=
    ((hcont.comp (hlin.add hcirc)).sub (hcont.comp hlin)).continuousOn
  have hloopH : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      F (z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ 1) - F (z + (s : ℂ) * (z' - z))
      = F (z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ 0) - F (z + (s : ℂ) * (z' - z)) := by
    intro s hs
    rw [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
  have hneH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F (z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ t) - F (z + (s : ℂ) * (z' - z)) ≠ 0 := by
    intro s hs t ht hzero
    have hne : z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ t
        ≠ z + (s : ℂ) * (z' - z) := by
      intro hh
      have hc : Work.MRMT.QC.circLoop ρ t = 0 := by linear_combination hh
      have h2 := Work.MRMT.QC.norm_circLoop hρ.le t
      rw [hc, norm_zero] at h2
      linarith
    have hdist : ‖(z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ t)
        - (z + (s : ℂ) * (z' - z))‖ = ρ := by
      rw [show z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ t - (z + (s : ℂ) * (z' - z))
        = Work.MRMT.QC.circLoop ρ t by ring, Work.MRMT.QC.norm_circLoop hρ.le]
    exact (hinj _ _ hne (by rw [hdist]; linarith)) (sub_eq_zero.mp hzero)
  have := hasArgChange_of_homotopy (a := 0) (b := 1) zero_le_one
    (H := fun s t : ℝ => F (z + (s : ℂ) * (z' - z) + Work.MRMT.QC.circLoop ρ t)
      - F (z + (s : ℂ) * (z' - z))) hcontH hloopH hneH (by simpa using h)
  simpa using this

/-! ## `F` is open -/

/-- **Openness.**  A continuous map which is locally injective and satisfies the Lipschitz
condition on `F - id` far out is an open map. -/
theorem isOpenMap_of_localInj_of_lipschitz_away {F : ℂ → ℂ} (hcont : Continuous F)
    (hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn F U) {R : ℝ}
    (hlip : ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖) :
    IsOpenMap F := by
  have hinjExt := injOn_of_lipschitz_away hlip
  obtain ⟨ε₀, hε₀pos, hinj⟩ := exists_uniform_local_injective hli hinjExt
  have hhalf : (0 : ℝ) < ε₀ / 2 := by linarith
  have hρ4pos : (0 : ℝ) < ε₀ / 4 := by linarith
  have hρ4 : ε₀ / 4 ≤ ε₀ / 2 := by linarith
  set A : Set ℂ := {z : ℂ |
    Work.MRMT.QC.HasArgChange (fun t : ℝ => F (z + Work.MRMT.QC.circLoop (ε₀ / 4) t) - F z) 1}
    with hA
  have hloc : ∀ z z' : ℂ, ‖z - z'‖ ≤ ε₀ / 2 → (z ∈ A ↔ z' ∈ A) := by
    intro z z' hzz'
    have h1 : ∀ {k : ℤ}, Work.MRMT.QC.HasArgChange
        (fun t : ℝ => F (z + Work.MRMT.QC.circLoop (ε₀ / 4) t) - F z) k →
        Work.MRMT.QC.HasArgChange
          (fun t : ℝ => F (z' + Work.MRMT.QC.circLoop (ε₀ / 4) t) - F z') k :=
      fun hk => argChange_small_circle_eq_of_close hcont hε₀pos hinj hzz' hρ4pos hρ4 hk
    have h2 : ∀ {k : ℤ}, Work.MRMT.QC.HasArgChange
        (fun t : ℝ => F (z' + Work.MRMT.QC.circLoop (ε₀ / 4) t) - F z') k →
        Work.MRMT.QC.HasArgChange
          (fun t : ℝ => F (z + Work.MRMT.QC.circLoop (ε₀ / 4) t) - F z) k :=
      fun hk => argChange_small_circle_eq_of_close hcont hε₀pos hinj
        (by rw [norm_sub_rev]; exact hzz') hρ4pos hρ4 hk
    exact ⟨fun hz => h1 hz, fun hz => h2 hz⟩
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro z hz
    refine ⟨ε₀ / 2, hhalf, fun z' hz' => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hz'
    exact (hloc z z' (le_of_lt hz')).mp hz
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro z hz
    refine ⟨ε₀ / 2, hhalf, fun z' hz' => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hz'
    exact fun hz'A => hz ((hloc z z' (le_of_lt hz')).mpr hz'A)
  have hAne : A.Nonempty := by
    refine ⟨((max R 0 + ε₀ + 1 : ℝ) : ℂ), ?_⟩
    have hnn : (0 : ℝ) ≤ max R 0 + ε₀ + 1 := by
      have := le_max_right R 0; linarith
    have hnorm : ‖((max R 0 + ε₀ + 1 : ℝ) : ℂ)‖ = max R 0 + ε₀ + 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    have hRle : R ≤ max R 0 := le_max_left R 0
    exact argChange_small_circle_of_away hcont hlip (by rw [hnorm]; linarith) hρ4pos
      (by rw [hnorm]; linarith)
  have hAuniv : A = Set.univ := by
    rcases isClopen_iff.mp ⟨hAclosed, hAopen⟩ with h | h
    · exact absurd h (Set.Nonempty.ne_empty hAne)
    · exact h
  -- every circle has argument change `1`
  have hlooparg : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ ε₀ / 2 →
      Work.MRMT.QC.HasArgChange (fun t : ℝ => F (w + Work.MRMT.QC.circLoop ρ t) - F w) 1 := by
    intro w ρ hρ hρ2
    have hw : w ∈ A := by rw [hAuniv]; exact Set.mem_univ w
    rw [hA] at hw
    have hrad : Continuous fun p : ℝ × ℝ => ε₀ / 4 + p.1 * (ρ - ε₀ / 4) := by fun_prop
    have hcirc : Continuous fun p : ℝ × ℝ =>
        Work.MRMT.QC.circLoop (ε₀ / 4 + p.1 * (ρ - ε₀ / 4)) p.2 := by
      unfold Work.MRMT.QC.circLoop
      fun_prop
    have hcontH : ContinuousOn
        (fun p : ℝ × ℝ => F (w + Work.MRMT.QC.circLoop (ε₀ / 4 + p.1 * (ρ - ε₀ / 4)) p.2) - F w)
        (Set.Icc 0 1 ×ˢ Set.Icc 0 1) :=
      ((hcont.comp (continuous_const.add hcirc)).sub continuous_const).continuousOn
    have hloopH : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        F (w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) 1) - F w
        = F (w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) 0) - F w := by
      intro s hs
      rw [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
    have hneH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        F (w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) t) - F w ≠ 0 := by
      intro s hs t ht hzero
      have hpos : 0 < ε₀ / 4 + s * (ρ - ε₀ / 4) := by
        have h1 : ε₀ / 4 + s * (ρ - ε₀ / 4) = (1 - s) * (ε₀ / 4) + s * ρ := by ring
        rw [h1]
        nlinarith [hs.1, hs.2]
      have hle : ε₀ / 4 + s * (ρ - ε₀ / 4) ≤ ε₀ / 2 := by
        have h1 : ε₀ / 4 + s * (ρ - ε₀ / 4) = (1 - s) * (ε₀ / 4) + s * ρ := by ring
        rw [h1]
        nlinarith [hs.1, hs.2]
      have hne : w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) t ≠ w := by
        intro hh
        have hc : Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) t = 0 := by linear_combination hh
        have h2 := Work.MRMT.QC.norm_circLoop hpos.le t
        rw [hc, norm_zero] at h2
        linarith
      have hdist : ‖(w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) t) - w‖
          = ε₀ / 4 + s * (ρ - ε₀ / 4) := by
        rw [add_sub_cancel_left, Work.MRMT.QC.norm_circLoop hpos.le]
      exact (hinj _ _ hne (by rw [hdist]; linarith)) (sub_eq_zero.mp hzero)
    have := hasArgChange_of_homotopy (a := 0) (b := 1) zero_le_one
      (H := fun s t : ℝ => F (w + Work.MRMT.QC.circLoop (ε₀ / 4 + s * (ρ - ε₀ / 4)) t) - F w)
      hcontH hloopH hneH (by simpa using hw)
    simpa using this
  -- openness at every point
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hzU, rfl⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀U⟩ := Metric.isOpen_iff.mp hU z hzU
  set ρ : ℝ := min (ε₀ / 2) (δ₀ / 2) with hρdef
  have hρpos : 0 < ρ := lt_min hhalf (half_pos hδ₀pos)
  have hρle : ρ ≤ ε₀ / 2 := min_le_left _ _
  have hballU : Metric.ball z ρ ⊆ U := by
    intro ζ hζ
    rw [Metric.mem_ball] at hζ
    refine hδ₀U ?_
    rw [Metric.mem_ball]
    have h : ρ ≤ δ₀ / 2 := min_le_right _ _
    linarith
  have hloop : Work.MRMT.QC.HasArgChange
      (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) 1 := hlooparg z ρ hρpos hρle
  have hloopne : ∀ t ∈ Set.Icc (0 : ℝ) 1, F (z + Work.MRMT.QC.circLoop ρ t) - F z ≠ 0 := by
    intro t ht
    have hne : z + Work.MRMT.QC.circLoop ρ t ≠ z := by
      intro hh
      have hc : Work.MRMT.QC.circLoop ρ t = 0 := by linear_combination hh
      have h2 := Work.MRMT.QC.norm_circLoop hρpos.le t
      rw [hc, norm_zero] at h2
      linarith
    have hdist : ‖(z + Work.MRMT.QC.circLoop ρ t) - z‖ = ρ := by
      rw [add_sub_cancel_left, Work.MRMT.QC.norm_circLoop hρpos.le]
    exact sub_ne_zero.mpr (hinj _ _ hne (by rw [hdist]; linarith))
  have hγcont : ContinuousOn (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t)) (Set.Icc 0 1) :=
    ((hcont.comp (continuous_const.add (Work.MRMT.QC.continuous_circLoop ρ)))).continuousOn
  have hγloop : (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t)) 1
      = (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t)) 0 := by
    simp only [Work.MRMT.QC.circLoop_one, Work.MRMT.QC.circLoop_zero]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hasArgChange_sub_iff_of_norm_lt hγcont hγloop hloopne
  have hfalse : ¬ Work.MRMT.QC.HasArgChange
      (fun t : ℝ => F (z + Work.MRMT.QC.circLoop ρ t) - F z) 0 := by
    intro h0
    have h01 : (0 : ℤ) = 1 := hasArgChange_inj hloopne h0 hloop
    exact (by norm_num : ¬ ((0 : ℤ) = 1)) h01
  have hnotmem : F z ∉ F '' Metric.sphere z ρ := by
    rintro ⟨ζ, hζ, hζF⟩
    have hζne : ζ ≠ z := by
      intro hh
      have h1 : dist ζ z = ρ := by rwa [Metric.mem_sphere] at hζ
      rw [hh, dist_self] at h1
      exact hρpos.ne' h1.symm
    have hdist : ‖ζ - z‖ = ρ := by
      rw [Metric.mem_sphere] at hζ
      rw [dist_eq_norm] at hζ
      exact hζ
    exact (hinj ζ z hζne (by rw [hdist]; linarith)) hζF
  have hclosed : IsClosed (F '' Metric.sphere z ρ) := ((isCompact_sphere z ρ).image hcont).isClosed
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl (F z) hnotmem
  have hcover : Metric.ball (F z) (min δ₁ δ₂) ⊆ F '' Metric.ball z ρ := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    by_contra hy'
    have hy1 : ‖y - F z‖ < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : ‖y - F z‖ < δ₂ := lt_of_lt_of_le hy (min_le_right _ _)
    have hysphere : y ∉ F '' Metric.sphere z ρ := fun hmem =>
      hδ₂ (by rw [Metric.mem_ball, dist_eq_norm]; exact hy2) hmem
    have hno : y ∉ F '' Metric.closedBall z ρ := by
      rintro ⟨ζ, hζ, hζF⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hζ
      rcases lt_or_eq_of_le hζ with hlt | heq
      · exact hy' ⟨ζ, by rw [Metric.mem_ball, dist_eq_norm]; exact hlt, hζF⟩
      · exact hysphere ⟨ζ, by rw [Metric.mem_sphere, dist_eq_norm]; exact heq, hζF⟩
    have hzero := hasArgChange_zero_of_ne_zero_on_closedBall
      (g := fun u => F u - y) (hcont.sub continuous_const) hρpos.le (fun u hu => by
        rw [sub_ne_zero]
        intro huy
        exact hno ⟨u, hu, huy⟩)
    exact hfalse ((hδ₁ y hy1).mp hzero)
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (F z) (lt_min hδ₁pos hδ₂pos))
    (fun y hy => by
      obtain ⟨ζ, hζ, hζF⟩ := hcover hy
      exact ⟨ζ, hballU hζ, hζF⟩)

/-! ## Fibres of a proper locally injective map are finite -/

/-- A fibre of a proper map that is injective on a neighbourhood of every point is finite: it is
compact (properness) and discrete (local injectivity). -/
theorem finite_fiber_of_isProperMap_of_localInj {F : ℂ → ℂ} (hproper : IsProperMap F)
    (hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn F U) (x : ℂ) :
    (F ⁻¹' {x}).Finite := by
  refine (hproper.isCompact_preimage isCompact_singleton).finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro z hz
  obtain ⟨U, hU, hinj⟩ := hli z
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine ⟨V, hVopen, ?_⟩
  ext w
  constructor
  · rintro ⟨hwV, hw⟩
    have hFw : F w = x := hw
    have hFz : F z = x := hz
    exact Set.mem_singleton_iff.mpr (hinj (hVU hwV) (hVU hzV) (by rw [hFw, hFz]))
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨hzV, hz⟩

/-! ## The main theorem -/

/-- **A locally injective, proper continuous map `ℂ → ℂ` with `F z = z + O(1/‖z‖)` is a
homeomorphism of `ℂ`.** -/
theorem exists_homeomorph_of_localInj_proper {F : ℂ → ℂ} (hcont : Continuous F)
    (hli : ∀ z : ℂ, ∃ U : Set ℂ, U ∈ nhds z ∧ Set.InjOn F U)
    (hproper : IsProperMap F)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖)
    (hlip : ∃ R : ℝ, ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖) :
    ∃ φ : ℂ ≃ₜ ℂ, (φ : ℂ → ℂ) = F := by
  obtain ⟨C, R₁, hdec⟩ := hdec
  obtain ⟨R₂, hlip⟩ := hlip
  set R : ℝ := max R₁ R₂ with hRdef
  have hdec' : ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖ :=
    fun z hz => hdec z (le_trans (le_max_left _ _) hz)
  have hlip' : ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖(F z₁ - z₁) - (F z₂ - z₂)‖ ≤ (1 / 2) * ‖z₁ - z₂‖ :=
    fun z₁ z₂ h₁ h₂ => hlip z₁ z₂ (le_trans (le_max_right _ _) h₁) (le_trans (le_max_right _ _) h₂)
  have hsurj : Function.Surjective F := surjective_of_decay hcont hdec'
  have hopen : IsOpenMap F := isOpenMap_of_localInj_of_lipschitz_away hcont hli hlip'
  have hlh : IsLocalHomeomorph F := isLocalHomeomorph_of_isOpenMap_localInj hcont hopen hli
  have hfin : ∀ x : ℂ, (F ⁻¹' {x}).Finite := fun x =>
    finite_fiber_of_isProperMap_of_localInj hproper hli x
  have hcov : IsCoveringMap F := isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => hfin x)
      hlh.isLocalHomeomorphOn)
  have hinj : Function.Injective F := injective_of_isCoveringMap hcov
  have hbij : Function.Bijective F := ⟨hinj, hsurj⟩
  have hcoe : (⇑(Equiv.ofBijective F hbij) : ℂ → ℂ) = F := Equiv.coe_ofBijective F hbij
  have hcont' : Continuous ⇑(Equiv.ofBijective F hbij) := by rw [hcoe]; exact hcont
  have hclosed' : IsClosedMap ⇑(Equiv.ofBijective F hbij) := by
    rw [hcoe]; exact hproper.isClosedMap
  exact ⟨(Equiv.ofBijective F hbij).toHomeomorphOfContinuousClosed hcont' hclosed',
    (Equiv.toHomeomorphOfContinuousClosed_apply _ _ _).trans hcoe⟩

end

end Work.MRMT.Found
