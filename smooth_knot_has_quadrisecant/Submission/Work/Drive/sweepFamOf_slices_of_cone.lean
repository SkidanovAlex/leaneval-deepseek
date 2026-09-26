import Mathlib
import Submission.Work.Drive.uniformCone_of_localCone
import Submission.Work.Drive.sweepFamOf_cone
import Submission.Work.Drive.velocity_ne_zero_of_secant_growth
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.farSep_window_of_injOn
import Submission.Work.Drive.sweepFamOf_close_uc
import Submission.Work.Drive.sweepFamOf_farSep
import Submission.Work.Drive.sweepFamOf_contDiff_periodic_li
import Submission.Work.Drive.sweepFam_injOn_glue
import Submission.Work.Drive.chordSweepDefs

open LeanEval.KnotTheory.Quadrisecant

namespace Work.Drive

/-- **The slices clause from a uniform cone.**  Let `Γ` be a jointly continuous, `period`-periodic
family of loops which is `M`-Lipschitz in the loop parameter and whose every slice on the compact
window `[a,b] ⊂ (0,1)` is injective on one period.  Suppose moreover that the cone hypothesis of
`Work.Drive.uniformCone_of_localCone` holds uniformly at scale `ε > 0` with rate `c > 0` on `[a,b]`.
Then for all small widths `δ₁, δ₂ ≤ L` every slice of the double bump-blur
`Work.Drive.sweepFamOf Γ δ₁ δ₂ σ` is injective on one period **and** has nowhere vanishing velocity.

This is the abstract `sweepFamOf` form of the `havoid` slices clause: it is exactly what the
scheduled-loop consumers need, with `hcone` (the local cone, produced geometrically for the
scheduled loop `Γ` by `chamferLoopGen_localCone`) and `hinj` (the injectivity of the *raw* scheduled
loop, a purely geometric clause) as the interface.

Proof route for the prover (everything below is already proved in the workspace):
1. Replace `ε` by `min ε (period/4)` (shrinking the cone radius preserves the cone at the same
   rate: the cone at scale `ε` implies the cone at any smaller scale, with the same `n` and `c`).
   `Work.Drive.farSep_window_of_injOn` (needs `ha`, `hab`, `hb`, `hΓ`, `hper`, `hinj`, `0 < ε`,
   `2ε ≤ period`) gives `ρ₀ > 0` for the far separation at scale `ε` on `Ico 0 period`;
   `Work.Drive.farSep_real_of_Ico` extends it to all real pairs.
2. `Work.Drive.sweepFamOf_close_uc` (with `hM`, `hMnn`, `ha`, `hab`, `hb`, closeness level `ε := ρ₀/4`)
   gives `L₁ > 0` with `‖sweepFamOf Γ δ₁ δ₂ σ t - Γ σ t‖ ≤ ρ₀/4` for `δ₁, δ₂ ≤ L₁`;
   `Work.Drive.sweepFamOf_farSep_of_close` then gives `L₂ > 0`, `ρ > 0` with far separation of the
   blurred slices at scale `ε`.
3. Local injectivity at scale `ε` from `Work.Drive.sweepFamOf_cone`: for `|t₂ - t₁| ≤ ε - δ₁` the
   cone gives `c*(t₂-t₁) ≤ ⟪n, Φ t₂ - Φ t₁⟫`; if `Φ t₁ = Φ t₂` and `t₁ ≤ t₂` then `t₂ ≤ t₁`, so
   `t₁ = t₂`; the case `t₂ ≤ t₁` is symmetric.
4. `Work.Drive.injOn_Ico_of_local_and_farSep` (with `p := period`, local scale `ε' := ε`, far
   separation `ρ` at the same scale `ε`, and `2ε ≤ period`) assembles the injectivity clause.
5. Velocity: `Work.Drive.sweepFamOf_contDiff_periodic_li` (with `LocallyIntegrable` from the
   continuity of `Γ` and `δ₁, δ₂ ≠ 0`) makes each slice differentiable, and
   `Work.Drive.velocity_ne_zero_of_secant_growth` with `t₀ := t` and `h := ε - δ₁ > 0` (the cone
   gives forward secants of length `g ≤ ε - δ₁`) gives `velocity Φ t ≠ 0`.
Take `L := min L₂ (ε/3)` (so that `δ₁ ≤ L` gives `ε - δ₁ ≥ 2ε/3 > 0`).
Note: `hcone` at scale `≥ period/2` is unsatisfiable by periodicity, so shrink `ε` in step 1 and
everything stays consistent. -/
theorem sweepFamOf_slices_of_cone {Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    (hper : ∀ s t : ℝ, Γ s (t + LeanEval.KnotTheory.Quadrisecant.period) = Γ s t)
    {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hinj : ∀ s ∈ Set.Icc a b, Set.InjOn (Γ s) (Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period))
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hcone : ∀ σ ∈ Set.Icc a b, ∀ t₀ : ℝ, ∃ n : LeanEval.KnotTheory.Quadrisecant.Space,
      ∀ s ∈ Set.Icc (σ - ε) (σ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
        c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁)) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
      Set.InjOn (fun t : ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ σ t)
        (Set.Ico (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period) ∧
      ∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
        (fun t : ℝ => Work.Drive.sweepFamOf Γ δ₁ δ₂ σ t) t ≠ 0 := by
  have hp : 0 < period := period_pos
  -- Step 1: shrink the cone radius.  We use the local scale `ε' / 2` both for the local
  -- injectivity and for the far separation, so that the two scales can be glued.
  set ε' : ℝ := min ε (period / 6) with hε'def
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε (by linarith)
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hε'per : ε' ≤ period / 6 := by rw [hε'def]; exact min_le_right _ _
  have hη0 : 0 < ε' / 2 := by linarith
  have hηε : ε' / 2 ≤ ε := by linarith
  have hηper : 2 * (ε' / 2) ≤ period := by linarith
  -- the cone at the shrunken radius, with the same direction and the same rate
  have hcone' : ∀ σ ∈ Set.Icc a b, ∀ t₀ : ℝ, ∃ n : Space,
      ∀ s ∈ Set.Icc (σ - ε') (σ + ε'), ∀ t₁ t₂ : ℝ, t₀ - ε' ≤ t₁ → t₁ ≤ t₂ →
        t₂ ≤ t₀ + ε' → c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁) := by
    intro σ hσ t₀
    obtain ⟨n, hn⟩ := hcone σ hσ t₀
    refine ⟨n, ?_⟩
    intro s hs t₁ t₂ h1 h2 h3
    exact hn s ⟨by linarith [hs.1, hε'ε], by linarith [hs.2, hε'ε]⟩ t₁ t₂
      (by linarith) h2 (by linarith)
  -- Step 1 (continued): far separation of the *raw* loop at scale `ε'/2` on the fundamental
  -- domain.
  obtain ⟨ρ₀, hρ₀0, hρ₀⟩ := farSep_window_of_injOn hΓ hper ha hab hb hinj hη0 hηper
  -- Step 2: the double blur is uniformly close to the loop family on the window.
  obtain ⟨L₁, hL₁0, hclose⟩ :=
    sweepFamOf_close_uc hΓ hper hMnn hM ha hab hb (ε := ρ₀ / 4) (by linarith)
  refine ⟨min L₁ (ε' / 3), lt_min hL₁0 (by linarith), ?_⟩
  intro δ₁ δ₂ hδ₁0 hδ₁L hδ₂0 hδ₂L σ hσ
  have hδ₁L₁ : δ₁ ≤ L₁ := le_trans hδ₁L (min_le_left _ _)
  have hδ₁ε3 : δ₁ ≤ ε' / 3 := le_trans hδ₁L (min_le_right _ _)
  have hδ₁ε' : δ₁ ≤ ε' := by linarith
  have hδ₂L₁ : δ₂ ≤ L₁ := le_trans hδ₂L (min_le_left _ _)
  have hδ₂ε3 : δ₂ ≤ ε' / 3 := le_trans hδ₂L (min_le_right _ _)
  have hδ₂ε' : δ₂ ≤ ε' := by linarith
  have hηloc : ε' / 2 ≤ ε' - δ₁ := by linarith
  have hpos' : 0 < ε' - δ₁ := by linarith
  -- smoothness / periodicity of the blurred slice
  have hS := sweepFamOf_contDiff_periodic Γ hΓ hper δ₁ δ₂ (ne_of_gt hδ₁0) (ne_of_gt hδ₂0)
  have hclose_here : ∀ t : ℝ, ‖sweepFamOf Γ δ₁ δ₂ σ t - Γ σ t‖ ≤ ρ₀ / 4 :=
    fun t => hclose δ₁ δ₂ hδ₁0.le hδ₁L₁ hδ₂0.le hδ₂L₁ σ hσ t
  refine ⟨?_, ?_⟩
  · -- ## the injectivity clause
    refine injOn_Ico_of_local_and_farSep
      (γ := fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) (p := period) (ε := ε' / 2) (ρ := ρ₀ / 2)
      hp hη0 (by linarith) hηper ?_ ?_ ?_
    · -- periodicity
      intro t
      exact hS.2.1 σ t
    · -- Step 3: local injectivity, from the cone
      intro t₁ t₂ hdist heq
      have hkey : ∀ u v : ℝ, u ≤ v → v - u ≤ ε' - δ₁ →
          sweepFamOf Γ δ₁ δ₂ σ u = sweepFamOf Γ δ₁ δ₂ σ v → u = v := by
        intro u v huv huvd heq'
        obtain ⟨n, hn⟩ := hcone' σ hσ u
        have h := sweepFamOf_cone (Γ := Γ) hΓ (σ := σ) (t₀ := u) (ε := ε') (c := c) (n := n)
          (δ₁ := δ₁) (δ₂ := δ₂) hδ₁0.le hδ₂0.le hδ₂ε' hn u v (by linarith) huv (by linarith)
        have hzu : inner ℝ n (sweepFamOf Γ δ₁ δ₂ σ v - sweepFamOf Γ δ₁ δ₂ σ u) = 0 := by
          rw [heq', sub_self, inner_zero_right]
        rw [hzu] at h
        have hv : v - u ≤ 0 := by
          rcases mul_nonpos_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2
          · exact absurd h1 (not_le.mpr hc)
        linarith
      rcases le_total t₁ t₂ with hle | hle
      · refine hkey t₁ t₂ hle ?_ heq
        have h₁ : |t₂ - t₁| = t₂ - t₁ := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [h₁] at hdist
        linarith
      · have h₁ : |t₂ - t₁| = t₁ - t₂ := by
          rw [abs_of_nonpos (a := t₂ - t₁) (sub_nonpos.mpr hle), neg_sub]
        rw [h₁] at hdist
        exact (hkey t₂ t₁ hle (by linarith) heq.symm).symm
    · -- Step 2 (continued): far separation of the blurred slices
      intro t₁ t₂ ht₁ ht₂ hle hge
      have hraw := hρ₀ σ hσ t₁ ht₁ t₂ ht₂ hle hge
      have h1 : ‖Γ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₁‖ ≤ ρ₀ / 4 := by
        rw [norm_sub_rev]; exact hclose_here t₁
      have h2 : ‖sweepFamOf Γ δ₁ δ₂ σ t₂ - Γ σ t₂‖ ≤ ρ₀ / 4 := hclose_here t₂
      have htri : ‖Γ σ t₁ - Γ σ t₂‖ ≤
          ‖sweepFamOf Γ δ₁ δ₂ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₂‖ + ρ₀ / 4 + ρ₀ / 4 := by
        have hsplit : Γ σ t₁ - Γ σ t₂
            = (Γ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₁)
              + (sweepFamOf Γ δ₁ δ₂ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₂)
              + (sweepFamOf Γ δ₁ δ₂ σ t₂ - Γ σ t₂) := by abel
        rw [hsplit]
        have h5 := norm_add_le ((Γ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₁)
          + (sweepFamOf Γ δ₁ δ₂ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₂))
          (sweepFamOf Γ δ₁ δ₂ σ t₂ - Γ σ t₂)
        have h6 := norm_add_le (Γ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₁)
          (sweepFamOf Γ δ₁ δ₂ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₂)
        linarith
      linarith
  · -- ## the non-vanishing velocity clause
    intro t
    obtain ⟨n, hn⟩ := hcone' σ hσ t
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) t :=
      ((hS.2.2 σ).differentiable (by simp)).differentiableAt
    refine velocity_ne_zero_of_secant_growth (F := fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t)
      (t := t) (h := ε' - δ₁) (c := c) (n := n) hdiff hpos' hc ?_
    intro g hg0 hgh
    have h := sweepFamOf_cone (Γ := Γ) hΓ (σ := σ) (t₀ := t) (ε := ε') (c := c) (n := n)
      (δ₁ := δ₁) (δ₂ := δ₂) hδ₁0.le hδ₂0.le hδ₂ε' hn t (t + g)
      (by linarith) (by linarith) (by linarith)
    have hg' : t + g - t = g := by ring
    rw [hg'] at h
    exact h

end Work.Drive
