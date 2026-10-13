import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R7d.trajectory_bounds
import Submission.Work.FTS.RegPkgGal.R7d.zBounds
import Submission.Work.FTS.RegPkgGal.R7d.thBounds
import Submission.Work.FTS.RegPkgGal.R7d.quadrant_extend

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7e

open Set Filter
open scoped Topology

/-- **Right-continuation of strict good behaviour.**  If the trajectory is strictly above the
level `L` and strictly inside the open quadrant at a time `σ < T`, then it stays so on a
further right neighbourhood of `σ` (inside `[0,T]`).  This is the `L`-analogue of
`Work.FTS.RegPkgGal.R7d.quadrant_extend`; note that `L < z` does *not* follow from `0 < z`. -/
theorem quadrant_extend_L {α : ℝ → ℝ × ℝ} {L σ T : ℝ} (hσ0 : 0 ≤ σ) (hσT : σ < T)
    (hαc : ContinuousOn α (Set.Icc 0 T)) (h1 : L < (α σ).1) (h2 : 0 < (α σ).2)
    (h3 : (α σ).2 < Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧ σ + δ ≤ T ∧
      ∀ x ∈ Set.Ioo σ (σ + δ), L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
  have hopen : IsOpen {y : ℝ × ℝ | L < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} := by
    have h1o : IsOpen {y : ℝ × ℝ | L < y.1} := isOpen_lt continuous_const continuous_fst
    have h2o : IsOpen {y : ℝ × ℝ | 0 < y.2} := isOpen_lt continuous_const continuous_snd
    have h3o : IsOpen {y : ℝ × ℝ | y.2 < Real.pi / 2} :=
      isOpen_lt continuous_snd continuous_const
    exact h1o.inter (h2o.inter h3o)
  have hσmem : σ ∈ Set.Icc 0 T := ⟨hσ0, le_of_lt hσT⟩
  have hVw : α ⁻¹' {y : ℝ × ℝ | L < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} ∈
      𝓝[Set.Icc 0 T] σ :=
    (hαc.continuousWithinAt hσmem) (hopen.mem_nhds ⟨h1, h2, h3⟩)
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hVw
  refine ⟨min (ε / 2) ((T - σ) / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · have hle : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
    linarith
  · intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := by
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
      constructor <;> linarith [hx.1, hx.2]
    have hxball : x ∈ Metric.ball σ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ ε / 2 := min_le_left _ _
      linarith [hx.2]
    exact hε ⟨hxball, hxIcc⟩

theorem trajectory_bounds_L {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {a K S τ₀ T z₀ θ₀ L : ℝ} {α : ℝ → ℝ × ℝ}
    (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hTS : T ≤ τ₀) (hτ₀S : τ₀ ≤ S)
    (hz₀ : L < z₀ * Real.exp (-(a * T)))
    (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < Real.pi / 2) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hα0 : α 0 = (z₀, θ₀))
    (hode : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α
      (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)), -(Vθ (α t).1 (α t).2 (τ₀ - t)))
      (Set.Icc (0:ℝ) T) t)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθl : ∀ z θ τ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ K * θ)
    (hVθu : ∀ z θ τ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ)) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      z₀ * Real.exp (-(a * t)) ≤ (α t).1 ∧ (α t).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * t)) ≤ (α t).2 ∧
      (α t).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * t)) := by
  -- The trajectory is strictly above the level `L` and strictly inside the open quadrant on
  -- the (a priori unknown) maximal interval `(0, σ)`.  On that interval the pointwise
  -- hypotheses on the velocity field are available, since `L < z` together with `0 ≤ L`
  -- gives `0 < z`.
  have hαc : ContinuousOn α (Set.Icc (0:ℝ) T) :=
    fun t ht => (hode t ht).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) T, HasDerivAt α
      (-((α x).1 * Vz (α x).1 (α x).2 (τ₀ - x)), -(Vθ (α x).1 (α x).2 (τ₀ - x))) x :=
    fun x hx => (hode x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  -- ## Step 1: the four bounds on `[0,b]`, given that `L < (α x).1` and the trajectory is
  -- strictly inside the open quadrant for `x ∈ (0,b)`
  have hbounds : ∀ b ∈ Set.Icc (0:ℝ) T,
      (∀ x ∈ Set.Ioo (0:ℝ) b, L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2) →
      ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) := by
    intro b hb hQ
    -- `L < z` upgrades to `0 < z`, which is what the field hypotheses and `zBounds` need
    have hQz : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < (α x).1 :=
      fun x hx => lt_of_le_of_lt hL (hQ x hx).1
    -- the fake time `τ₀ - x` is strictly positive and at most `S` on `(0,b)`
    have hτpos : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < τ₀ - x := by
      intro x hx
      have hxτ : x < τ₀ := lt_of_lt_of_le (lt_of_lt_of_le hx.2 hb.2) hTS
      linarith
    have hτle : ∀ x ∈ Set.Ioo (0:ℝ) b, τ₀ - x ≤ S := by
      intro x hx
      linarith [hx.1, hτ₀S]
    have hbc : ContinuousOn α (Set.Icc (0:ℝ) b) := hαc.mono (Icc_subset_Icc le_rfl hb.2)
    -- the `z`-bounds
    have hzB : ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ :=
      Work.FTS.RegPkgGal.R7d.zBounds (z := fun x => (α x).1)
        (V := fun x => Vz (α x).1 (α x).2 (τ₀ - x))
        (a := a) (z₀ := z₀) (T := b) hbc.fst (by rw [hα0])
        (fun x hx => Work.FTS.RegPkgGal.R7d.hasDerivAt_fst
          (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVz0 _ _ _ (hQz x hx) (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVza _ _ _ (hQz x hx) (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => (hQz x hx).le)
    -- the `θ`-bounds
    have hθB : ∀ x ∈ Set.Icc (0:ℝ) b,
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
      Work.FTS.RegPkgGal.R7d.thBounds (θ := fun x => (α x).2)
        (V := fun x => Vθ (α x).1 (α x).2 (τ₀ - x))
        (K := K) (θ₀ := θ₀) (T := b) hbc.snd (by rw [hα0])
        (fun x hx => Work.FTS.RegPkgGal.R7d.hasDerivAt_snd
          (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVθl _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVθu _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
    intro x hx
    exact ⟨(hzB x hx).1, (hzB x hx).2, (hθB x hx).1, (hθB x hx).2⟩
  -- ## Step 2: the bootstrap on the maximal time of strict good behaviour
  set G : Set ℝ := {b | b ∈ Set.Icc (0:ℝ) T ∧
    ∀ x ∈ Set.Ioo (0:ℝ) b, L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2}
  have hG0 : (0 : ℝ) ∈ G := by
    refine ⟨⟨le_rfl, hT⟩, ?_⟩
    intro x hx
    exact absurd hx.1 (not_lt.mpr hx.2.le)
  have hGne : G.Nonempty := ⟨0, hG0⟩
  have hGbdd : BddAbove G := ⟨T, fun b hb => hb.1.2⟩
  have hσ0 : 0 ≤ sSup G := le_csSup hGbdd hG0
  have hσT : sSup G ≤ T := (csSup_le_iff hGbdd hGne).mpr (fun b hb => hb.1.2)
  -- the trajectory is good on `(0, sSup G)`
  have hQsSup : ∀ x ∈ Set.Ioo (0:ℝ) (sSup G),
      L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    obtain ⟨b, hbG, hxb⟩ := (lt_csSup_iff hGbdd hGne).mp hx.2
    exact hbG.2 x ⟨hx.1, hxb⟩
  -- hence the bounds hold on `[0, sSup G]`
  have hPsSup : ∀ x ∈ Set.Icc (0:ℝ) (sSup G),
      z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
      (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
    hbounds (sSup G) ⟨hσ0, hσT⟩ hQsSup
  have hPsSup' := hPsSup (sSup G) ⟨hσ0, le_rfl⟩
  -- `z₀` is positive, and the lower `z`-bound is above `L` at `sSup G`
  have hz₀pos : 0 < z₀ :=
    pos_of_mul_pos_left (lt_of_le_of_lt hL hz₀) (Real.exp_pos _).le
  -- strict good behaviour at `sSup G`
  have hQσ : L < (α (sSup G)).1 ∧ 0 < (α (sSup G)).2 ∧ (α (sSup G)).2 < Real.pi / 2 := by
    refine ⟨?_, ?_, ?_⟩
    · have hexp_le : Real.exp (-(a * T)) ≤ Real.exp (-(a * sSup G)) := by
        rw [Real.exp_le_exp]
        linarith [mul_le_mul_of_nonneg_left hσT ha]
      have h1 : z₀ * Real.exp (-(a * T)) ≤ z₀ * Real.exp (-(a * sSup G)) :=
        mul_le_mul_of_nonneg_left hexp_le hz₀pos.le
      linarith [hPsSup'.1]
    · have hpos : 0 < θ₀ * Real.exp (-(K * sSup G)) := mul_pos hθ₀ (Real.exp_pos _)
      linarith [hPsSup'.2.2.1]
    · have hpos : 0 < (Real.pi / 2 - θ₀) * Real.exp (-(K * sSup G)) :=
        mul_pos (by linarith) (Real.exp_pos _)
      linarith [hPsSup'.2.2.2]
  -- `sSup G` is maximal: it cannot be strictly below `T`
  have hσeq : sSup G = T := by
    rcases lt_or_eq_of_le hσT with hlt | heq
    · exfalso
      obtain ⟨δ, hδ0, hσδT, hQδ⟩ :=
        quadrant_extend_L hσ0 hlt hαc hQσ.1 hQσ.2.1 hQσ.2.2
      have hmem : sSup G + δ ∈ G := by
        refine ⟨⟨by linarith, hσδT⟩, fun x hx => ?_⟩
        rcases lt_trichotomy x (sSup G) with hlt' | heq' | hgt'
        · exact hQsSup x ⟨hx.1, hlt'⟩
        · rw [heq']; exact hQσ
        · exact hQδ x ⟨hgt', hx.2⟩
      have hle : sSup G + δ ≤ sSup G := le_csSup hGbdd hmem
      linarith
    · exact heq
  -- ## Step 3: conclusion
  have hQT : ∀ x ∈ Set.Ioo (0:ℝ) T,
      L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    rw [← hσeq] at hx
    exact hQsSup x hx
  exact hbounds T ⟨hT, le_rfl⟩ hQT

end Work.FTS.RegPkgGal.R7e
