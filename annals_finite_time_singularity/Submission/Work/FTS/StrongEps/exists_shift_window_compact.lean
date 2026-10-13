/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/exists_shift_window_compact.lean`

**A compact window stable under the log-coordinate shifts.**  Let `K ⊆ Q0 = (0,∞) × (0,π/2)` be
compact and let `ε ∈ (0,1]`.  Then there is a compact `K' ⊆ Q0` with `K ⊆ K'` which contains every
shifted point

  `(zShift z q₁, thShift θ q₂) = (z e^{-q₁}, arctan (tan θ · e^{-q₂}))`,   `(z,θ) ∈ K`, `|q| ≤ ε`.

The statement is what `Work.FTS.StrongEps.epsRHSP_sup_le_of_mem` needs: the value bound
`epsWP_sup_le_of_mem` is only available on a *compact* subset of the quadrant, and the mollifier
averages `epsWP` over exactly these shifted points.

## The proof

The key structural fact is that the open quadrant is *invariant* under both shifts: for `z > 0`
the factor `e^{-q₁} > 0` keeps the `z`-coordinate positive (`zShift_pos`), and for
`θ ∈ (0,π/2)` the tangent is positive, so `arctan` of a positive number again lies in `(0,π/2)`
(`thShift_mem`).  Hence the *whole* naively chosen window already lies in `Q0` and no shrinking is
needed: take

  `K' := Φ '' (K ×ˢ ([-ε,ε] × [-ε,ε]))`,   `Φ ((z,θ), q) := (zShift z q₁, thShift θ q₂)`.

`K ×ˢ [-ε,ε]²` is compact (product of compacta) and `Φ` is continuous on it — the `z`-half is a
product of continuous functions, the `θ`-half is `arctan ∘ (tan · exp)` with `Real.continuousOn_tan`
on `{cos ≠ 0}` (the base angles of `K` lie in `(0,π/2)`, where `cos > 0`) — so `K'` is compact as
the image of a compact set under a continuous map.  It contains `K` because the zero shift is the
identity (`q = (0,0)`, `arctan (tan θ) = θ` for `θ ∈ (0,π/2)`), and it has the required shift
property by construction: membership of `q` in `[-ε,ε]²` is exactly `|q| ≤ ε` componentwise.

Everything rests on `[propext, Classical.choice, Quot.sound]`; the hypothesis `ε ≤ 1` is not needed
(the window is compact for every `ε`), it is kept because the statement is used with the uniform
scale bound of the `ε`-scheme.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps

theorem exists_shift_window_compact {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') := by
  -- the shift box `[-ε,ε]²` and the shift map
  let B : Set (ℝ × ℝ) := Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε
  let Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ :=
    fun y => (zShift y.1.1 y.2.1, thShift y.1.2 y.2.2)
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  -- `Φ` is (jointly) continuous on `K × B`: the base angles of `K` lie in `(0,π/2)`
  have hΦc : ContinuousOn Φ (K ×ˢ B) := by
    refine ContinuousOn.prodMk ?_ ?_
    · simp only [zShift]
      exact (by fun_prop : Continuous fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
        y.1.1 * Real.exp (-y.2.1)).continuousOn
    · have htan : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan y.1.2) (K ×ˢ B) :=
        Real.continuousOn_tan.comp (continuous_fst.snd.continuousOn) (fun y hy => by
          have hyθ : y.1.2 ∈ Set.Ioo 0 (π / 2) := (Set.mem_prod.mp (hKQ hy.1)).2
          exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hyθ.1, Real.pi_pos], hyθ.2⟩).ne')
      have h1 : ContinuousOn (fun y : (ℝ × ℝ) × (ℝ × ℝ) =>
          Real.tan y.1.2 * Real.exp (-y.2.2)) (K ×ˢ B) :=
        htan.mul ((Real.continuous_exp.comp (continuous_neg.comp continuous_snd.snd)).continuousOn)
      have h2 := Real.continuous_arctan.comp_continuousOn h1
      simpa only [Φ, thShift, Function.comp_def] using h2
  refine ⟨Φ '' (K ×ˢ B), ?_, ?_, ?_, ?_⟩
  · -- compactness: the image of `K × B` under the continuous map `Φ`
    exact (hK.prod hBc).image_of_continuousOn hΦc
  · -- the window stays in the open quadrant
    rintro q ⟨y, hy, rfl⟩
    exact Set.mem_prod.mpr ⟨zShift_pos (Set.mem_prod.mp (hKQ hy.1)).1,
      thShift_mem (Set.mem_prod.mp (hKQ hy.1)).2⟩
  · -- `K` sits in the window: the zero shift is the identity
    intro p hp
    have hpQ := Set.mem_prod.mp (hKQ hp)
    refine ⟨(p, (0, 0)), ⟨hp, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩, ?_⟩
    have hz : zShift p.1 0 = p.1 := by simp [zShift]
    have hth : thShift p.2 0 = p.2 := by
      simp only [thShift, neg_zero, Real.exp_zero, mul_one]
      exact Real.arctan_tan (by linarith [hpQ.2.1, Real.pi_pos]) hpQ.2.2
    exact Prod.ext hz hth
  · -- the shift property, by definition of the window
    intro p hp q hq1 hq2
    obtain ⟨hq1', hq1''⟩ := abs_le.mp hq1
    obtain ⟨hq2', hq2''⟩ := abs_le.mp hq2
    exact ⟨(p, q), ⟨hp, ⟨⟨hq1', hq1''⟩, ⟨hq2', hq2''⟩⟩⟩, rfl⟩

end Work.FTS.StrongEps
