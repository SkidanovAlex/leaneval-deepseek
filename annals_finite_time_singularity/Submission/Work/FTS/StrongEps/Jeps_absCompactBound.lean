import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Gdot
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set

namespace Work.FTS.StrongEps

/-- **`J_ε` is dominated by the sup of the profile over a slightly larger compact set.**

For a compact `K` inside the open quadrant `Q0 = (0,∞) × (0,π/2)`, the mollifier `J_ε` at any
point of `K` is a weighted average of the values of the profile at the shifted points
`(z e^{-p₁}, arctan (tan θ e^{-p₂}))`, `|p₁|, |p₂| ≤ ε`.  Hence if the profile is bounded by `C`
on a compact set `K'` containing all those shifted points of `K`, then `|J_ε F| ≤ C` on `K`.

The shifted set of a compact `K ⊆ Q0` is again compact and *strictly* inside the open quadrant:
if `K ⊆ [z₀,z₁] × [θ₀,θ₁]` with `0 < z₀`, `0 < θ₀`, `θ₁ < π/2` — which compactness supplies — then
every shifted point lies in the box

  `[z₀ e^{-ε}, z₁ e^{ε}] × [arctan (tan θ₀ · e^{-ε}), arctan (tan θ₁ · e^{ε})]`,

whose second factor is a compact subinterval of `(0,π/2)` because `arctan < π/2` everywhere. -/
theorem Jeps_absCompactBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
        ∀ (F : Work.FTS.Galerkin.Fn) (C : ℝ), 0 ≤ C → (∀ p ∈ K', |F p.1 p.2| ≤ C) →
          ∀ p ∈ K, |Work.FTS.StrongEps.Jeps ρ ε F p.1 p.2| ≤ C := by
  intro K hK hKQ
  rcases Set.eq_empty_or_nonempty K with hE | hne
  · subst hE
    exact ⟨∅, isCompact_empty, empty_subset _, empty_subset _,
      fun F C hC hF p hp => absurd hp (by simp)⟩
  · -- the coordinate bounds of `K` and of the four tangents
    obtain ⟨pz0, hpz0K, hz0min⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨pz1, hpz1K, hz1max⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨pt0, hpt0K, ht0min⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨pt1, hpt1K, ht1max⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hz0Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpz0K)
    have hz1Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpz1K)
    have ht0Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpt0K)
    have ht1Q := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hpt1K)
    have hz_le : ∀ p ∈ K, pz0.1 ≤ p.1 := fun p hp => hz0min hp
    have hz_ge : ∀ p ∈ K, p.1 ≤ pz1.1 := fun p hp => hz1max hp
    have ht_le : ∀ p ∈ K, pt0.2 ≤ p.2 := fun p hp => ht0min hp
    have ht_ge : ∀ p ∈ K, p.2 ≤ pt1.2 := fun p hp => ht1max hp
    have htan0pos : 0 < Real.tan pt0.2 :=
      Real.tan_pos_of_pos_of_lt_pi_div_two ht0Q.2.1 ht0Q.2.2
    have htan1pos : 0 < Real.tan pt1.2 :=
      Real.tan_pos_of_pos_of_lt_pi_div_two ht1Q.2.1 ht1Q.2.2
    have hmem0 : pt0.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [ht0Q.2.1, Real.pi_pos], ht0Q.2.2⟩
    have hmem1 : pt1.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [ht1Q.2.1, Real.pi_pos], ht1Q.2.2⟩
    have hexp1 : Real.exp (-ε) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show -ε ≤ 0 by linarith)
      rwa [Real.exp_zero] at h
    have hexp2 : 1 ≤ Real.exp ε := Real.one_le_exp hε.le
    -- the enlarged box
    set a : ℝ := pz0.1 * Real.exp (-ε) with ha
    set b : ℝ := pz1.1 * Real.exp ε with hb
    set c : ℝ := Real.arctan (Real.tan pt0.2 * Real.exp (-ε)) with hc
    set d : ℝ := Real.arctan (Real.tan pt1.2 * Real.exp ε) with hd
    have hapos : 0 < a := by rw [ha]; exact mul_pos hz0Q.1 (Real.exp_pos _)
    have hcpos : 0 < c := by
      rw [hc]; exact Real.arctan_pos.mpr (mul_pos htan0pos (Real.exp_pos _))
    have hdpi : d < π / 2 := by rw [hd]; exact Real.arctan_lt_pi_div_two _
    refine ⟨Set.Icc a b ×ˢ Set.Icc c d, isCompact_Icc.prod isCompact_Icc, ?_, ?_, ?_⟩
    · -- the box lies in the open quadrant
      rintro ⟨z, θ⟩ hy
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨lt_of_lt_of_le hapos hy.1.1, lt_of_lt_of_le hcpos hy.2.1,
          lt_of_le_of_lt hy.2.2 hdpi⟩
    · -- `K` is contained in the box
      rintro ⟨z, θ⟩ hp
      have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
      have hθmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [hpQ.2.1, Real.pi_pos], hpQ.2.2⟩
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact le_trans (mul_le_of_le_one_right hz0Q.1.le hexp1) (hz_le (z, θ) hp)
      · exact le_trans (hz_ge (z, θ) hp) (le_mul_of_one_le_right hz1Q.1.le hexp2)
      · calc c = Real.arctan (Real.tan pt0.2 * Real.exp (-ε)) := hc
          _ ≤ Real.arctan (Real.tan θ) := Real.arctan_strictMono.monotone
              (le_trans (mul_le_of_le_one_right htan0pos.le hexp1)
                (Real.strictMonoOn_tan.monotoneOn hmem0 hθmem (ht_le (z, θ) hp)))
          _ = θ := Real.arctan_tan (by linarith [Real.pi_pos]) hpQ.2.2
      · calc θ = Real.arctan (Real.tan θ) :=
              (Real.arctan_tan (by linarith [Real.pi_pos]) hpQ.2.2).symm
          _ ≤ Real.arctan (Real.tan pt1.2 * Real.exp ε) := Real.arctan_strictMono.monotone
              (le_trans (Real.strictMonoOn_tan.monotoneOn hθmem hmem1 (ht_ge (z, θ) hp))
                (le_mul_of_one_le_right htan1pos.le hexp2))
          _ = d := hd.symm
    · -- the bound, by `abs_Jeps_le_sup` over the shifts of `K`
      intro F C hC hFC
      rintro ⟨z, θ⟩ hp
      have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
      have hθmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [hpQ.2.1, Real.pi_pos], hpQ.2.2⟩
      have htanθpos : 0 < Real.tan θ :=
        Real.tan_pos_of_pos_of_lt_pi_div_two hpQ.2.1 hpQ.2.2
      have ht0le : Real.tan pt0.2 ≤ Real.tan θ :=
        Real.strictMonoOn_tan.monotoneOn hmem0 hθmem (ht_le (z, θ) hp)
      have htθ1 : Real.tan θ ≤ Real.tan pt1.2 :=
        Real.strictMonoOn_tan.monotoneOn hθmem hmem1 (ht_ge (z, θ) hp)
      refine abs_Jeps_le_sup ρ hρ hε hpQ.1 hpQ.2 (M := C) ?_ hC
      intro q hq1 hq2
      have hq1a : -ε ≤ q.1 := (abs_le.mp hq1).1
      have hq1b : q.1 ≤ ε := (abs_le.mp hq1).2
      have hq2a : -ε ≤ q.2 := (abs_le.mp hq2).1
      have hq2b : q.2 ≤ ε := (abs_le.mp hq2).2
      refine hFC (zShift z q.1, thShift θ q.2) ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · -- `a ≤ z e^{-q₁}`
        rw [ha]
        exact mul_le_mul (hz_le (z, θ) hp) (Real.exp_le_exp.mpr (by linarith))
          (Real.exp_pos _).le hpQ.1.le
      · -- `z e^{-q₁} ≤ b`
        rw [hb]
        exact mul_le_mul (hz_ge (z, θ) hp) (Real.exp_le_exp.mpr (by linarith))
          (Real.exp_pos _).le (le_of_lt hz1Q.1)
      · -- `c ≤ arctan (tan θ e^{-q₂})`
        rw [hc]
        exact Real.arctan_strictMono.monotone
          (mul_le_mul ht0le (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            htanθpos.le)
      · -- `arctan (tan θ e^{-q₂}) ≤ d`
        rw [hd]
        exact Real.arctan_strictMono.monotone
          (mul_le_mul htθ1 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            htan1pos.le)

end Work.FTS.StrongEps
