import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.Jeps_absCompactBound
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `abs_mixed_Jeps_le_sup`

The mixed-slot sup bound for the mollified profile: for a compact `K` inside the open quadrant
`Q0 = (0,∞) × (0,π/2)` there is a compact `K' ⊆ Q0` containing `K` such that every mixed slot
`D_z^j D_θ^i (J_ε F)` on `K` is bounded by a constant (depending on `ρ`, `ε`, `j`, `i` only)
times the sup of `F` on `K'`.

The mathematics is entirely contained in the already-proved value bound
`Work.FTS.StrongEps.abs_mixed_Jeps_le_val`: every derivative falling on the mollified profile
`J_ε F` can be *routed onto the mollifier kernel* (by
`mixed_Jeps_kernel_partial` at `j' = i' = 0`), and the routed kernel `Kd (Jker ρ ε) j i` is
supported in the ball of radius `ε`, so only the values of `F` at the shifted points
`(z e^{-p₁}, arctan(tan θ · e^{-p₂}))`, `|p_k| ≤ ε`, enter — with the kernel's `L¹`-mass
`Kmass ρ ε j i` as the constant.

The only geometric work here is the construction of `K'`: exactly as in
`Work.FTS.StrongEps.Jeps_absCompactBound`, compactness of `K ⊆ Q0` supplies a box
`[z₀,z₁] × [θ₀,θ₁]` with `z₀ > 0` and `0 < θ₀ ≤ θ₁ < π/2`, and the enlarged box
`[z₀e^{-ε}, z₁e^{ε}] × [arctan(tan θ₀ · e^{-ε}), arctan(tan θ₁ · e^{ε})]`
is compact, still inside `Q0` (because `arctan < π/2`), contains `K`, and contains every shifted
point.
-/

namespace Work.FTS.EpsEngine

open scoped Real Topology
open Set

noncomputable section

theorem abs_mixed_Jeps_le_sup {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (j i : ℕ) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Work.FTS.Galerkin.Fn),
          Work.FTS.EllipticEst.SmoothOpen F → ∀ (B : ℝ), 0 ≤ B →
            (∀ p ∈ K', |F p.1 p.2| ≤ B) → ∀ p ∈ K,
              |Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε F) p.1 p.2| ≤ C * B := by
  intro K hK hKQ
  rcases Set.eq_empty_or_nonempty K with hE | hne
  · subst hE
    exact ⟨∅, isCompact_empty, empty_subset _, empty_subset _,
      (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i,
      mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i),
      fun F _ B _ _ p hp => absurd hp (by simp)⟩
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
    refine ⟨Set.Icc a b ×ˢ Set.Icc c d, isCompact_Icc.prod isCompact_Icc, ?_, ?_,
      (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i,
      mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i), ?_⟩
    · -- the box lies in the open quadrant
      rintro ⟨z, θ⟩ hy
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨lt_of_lt_of_le hapos hy.1.1, lt_of_lt_of_le hcpos hy.2.1, lt_of_le_of_lt hy.2.2 hdpi⟩
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
    · -- the bound: route every derivative onto the mollifier kernel and read off the values
      intro F hFsm B hB hFB
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
      have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.StrongEps.Quad :=
        fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFsm n
      -- the value bound of `F` transfers to the shifted points inside the kernel's ball
      have hval : ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
          |F (Work.FTS.StrongEps.zShift z q.1) (Work.FTS.StrongEps.thShift θ q.2)| ≤ B := by
        intro q hq1 hq2
        have hq1a : -ε ≤ q.1 := (abs_le.mp hq1).1
        have hq1b : q.1 ≤ ε := (abs_le.mp hq1).2
        have hq2a : -ε ≤ q.2 := (abs_le.mp hq2).1
        have hq2b : q.2 ≤ ε := (abs_le.mp hq2).2
        refine hFB (Work.FTS.StrongEps.zShift z q.1, Work.FTS.StrongEps.thShift θ q.2)
          ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
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
      exact Work.FTS.StrongEps.abs_mixed_Jeps_le_val (ρ := ρ) hρ hε hsm hpQ.1
        ⟨hpQ.2.1, hpQ.2.2⟩ hval j i

end

end Work.FTS.EpsEngine
