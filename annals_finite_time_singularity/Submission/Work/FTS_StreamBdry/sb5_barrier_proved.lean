import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.SB2C2Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter
open Work.FTS.StreamBdryIface (oddPerS psiP)

set_option autoImplicit false

noncomputable section

/-! ## §1 Vocabulary: the half-strips and the seam lines -/

/-- The open strip `(0,∞) × (a,b)`. -/
abbrev Strip (a b : ℝ) : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo a b

/-- The seam line `θ = 0`, `z > 0`. -/
abbrev Line0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ ({(0 : ℝ)} : Set ℝ)

/-- The seam line `θ = π/2`, `z > 0`. -/
abbrev LinePi : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ ({(Real.pi / 2)} : Set ℝ)

theorem strip_le_Qd : Strip 0 (Real.pi / 2) ⊆ Work.Construction.Qd :=
  fun p hp => ⟨hp.1, hp.2.1, hp.2.2⟩

/-- `C²` on the union of two open sets from `C²` on each. -/
theorem contDiffOn_union_of_isOpen {f : ℝ × ℝ → ℝ} {U₁ U₂ : Set (ℝ × ℝ)}
    (h1 : IsOpen U₁) (h2 : IsOpen U₂) (hd1 : ContDiffOn ℝ 2 f U₁)
    (hd2 : ContDiffOn ℝ 2 f U₂) : ContDiffOn ℝ 2 f (U₁ ∪ U₂) := by
  intro x hx
  rcases hx with hx | hx
  · exact (hd1.contDiffAt (h1.mem_nhds hx)).contDiffWithinAt
  · exact (hd2.contDiffAt (h2.mem_nhds hx)).contDiffWithinAt

abbrev Edge0 (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ z0 : ℝ, 0 < z0 →
    Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pz P)) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 0) ∧
    (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
      (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l)) ∧
    (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l) ∧
      Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
        (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l))

abbrev EdgePi (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ z0 : ℝ, 0 < z0 →
    Tendsto (Function.uncurry P) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pz P))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz P)))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
    Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth P)))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
    (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth P))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) ∧
    (∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth P)))
        (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) ∧
      Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz P)))
        (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l))

/-! ## §3 Two functions equal on an open set have equal partials -/

/-- **The six partials agree on an open set on which the two functions agree.** -/
theorem partials_eqOn_of_eqOn {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ p ∈ U, f p.1 p.2 = g p.1 p.2) :
    (∀ p ∈ U, Work.Spaces.pz f p.1 p.2 = Work.Spaces.pz g p.1 p.2) ∧
      (∀ p ∈ U, Work.Spaces.pth f p.1 p.2 = Work.Spaces.pth g p.1 p.2) ∧
      (∀ p ∈ U, Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.pz g) p.1 p.2) ∧
      (∀ p ∈ U, Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
        = Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ∧
      (∀ p ∈ U, Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.pth g) p.1 p.2) ∧
      (∀ p ∈ U, Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2
        = Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) := by
  have hmem1 : ∀ p ∈ U, ∀ᶠ w' in 𝓝 p.1, (w', p.2) ∈ U := by
    intro p hp
    exact (ContinuousAt.preimage_mem_nhds
      (continuousAt_id.prodMk continuousAt_const) (hU.mem_nhds hp))
  have hmem2 : ∀ p ∈ U, ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ U := by
    intro p hp
    exact (ContinuousAt.preimage_mem_nhds
      (continuousAt_const.prodMk continuousAt_id) (hU.mem_nhds hp))
  have h1 : ∀ p ∈ U, Work.Spaces.pz f p.1 p.2 = Work.Spaces.pz g p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem1 p hp] with w' hw'
    exact h (w', p.2) hw'
  have h2 : ∀ p ∈ U, Work.Spaces.pth f p.1 p.2 = Work.Spaces.pth g p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem2 p hp] with θ' hθ'
    exact h (p.1, θ') hθ'
  have h3 : ∀ p ∈ U, Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pz g) p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem1 p hp] with w' hw'
    exact h1 (w', p.2) hw'
  have h4 : ∀ p ∈ U, Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem2 p hp] with θ' hθ'
    exact h1 (p.1, θ') hθ'
  have h5 : ∀ p ∈ U, Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2
      = Work.Spaces.pz (Work.Spaces.pth g) p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem1 p hp] with w' hw'
    exact h2 (w', p.2) hw'
  have h6 : ∀ p ∈ U, Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2
      = Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2 := by
    intro p hp
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hmem2 p hp] with θ' hθ'
    exact h2 (p.1, θ') hθ'
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## §4 Limits at a seam from the two one-sided strips -/

/-- Composition of a quadrant limit at the seam `θ = 0` with the reflection `θ ↦ -θ`. -/
theorem tendsto_neg_comp {G : ℝ → ℝ → ℝ} {z0 l : ℝ}
    (h : Tendsto (Function.uncurry G) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l)) :
    Tendsto (fun q : ℝ × ℝ => G q.1 (-q.2)) (𝓝[Strip (-(Real.pi / 2)) 0] (z0, 0)) (𝓝 l) := by
  have hφ : Tendsto (fun q : ℝ × ℝ => (q.1, -q.2))
      (𝓝[Strip (-(Real.pi / 2)) 0] (z0, 0)) (𝓝[Work.Construction.Qd] (z0, 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun q : ℝ × ℝ => (q.1, -q.2)) (z0, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have h1 : Tendsto (fun q : ℝ × ℝ => (q.1, -q.2)) (𝓝 (z0, 0)) (𝓝 (z0, 0)) := by
        simpa using hc.tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [Set.mem_prod] at hq
      rw [Work.FTS_StreamBdry.mem_Qd]
      exact ⟨hq.1, by linarith [hq.2.2], by linarith [hq.2.1]⟩
  have h1 := h.comp hφ
  simpa only [Function.comp_def, Function.uncurry] using h1

/-- Composition of a quadrant limit at the seam `θ = π/2` with the reflection `θ ↦ π - θ`. -/
theorem tendsto_sub_comp {G : ℝ → ℝ → ℝ} {z0 l : ℝ}
    (h : Tendsto (Function.uncurry G) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) :
    Tendsto (fun q : ℝ × ℝ => G q.1 (Real.pi - q.2))
      (𝓝[Strip (Real.pi / 2) Real.pi] (z0, Real.pi / 2)) (𝓝 l) := by
  have hφ : Tendsto (fun q : ℝ × ℝ => (q.1, Real.pi - q.2))
      (𝓝[Strip (Real.pi / 2) Real.pi] (z0, Real.pi / 2))
      (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun q : ℝ × ℝ => (q.1, Real.pi - q.2)) (z0, Real.pi / 2) :=
        continuousAt_fst.prodMk (continuousAt_const.sub continuousAt_snd)
      have h2 : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
      have h1 : Tendsto (fun q : ℝ × ℝ => (q.1, Real.pi - q.2)) (𝓝 (z0, Real.pi / 2))
          (𝓝 (z0, Real.pi / 2)) := by
        simpa only [h2] using hc.tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [Set.mem_prod] at hq
      rw [Work.FTS_StreamBdry.mem_Qd]
      exact ⟨hq.1, by linarith [hq.2.2], by linarith [hq.2.1]⟩
  have h1 := h.comp hφ
  simpa only [Function.comp_def, Function.uncurry] using h1

/-- **The seam limits at `θ = 0`**: a limit along the whole punctured strip from a limit along
the upper half and one along the lower half, where the two branches of `D` are `DP` and
`σ · DP(-θ)`. -/
theorem tendsto_seam0 {D DP : ℝ → ℝ → ℝ} {σ l : ℝ} {z0 : ℝ}
    (hupper : ∀ w θ, (w, θ) ∈ Strip 0 (Real.pi / 2) → D w θ = DP w θ)
    (hlower : ∀ w θ, (w, θ) ∈ Strip (-(Real.pi / 2)) 0 → D w θ = σ * DP w (-θ))
    (hlim : Tendsto (Function.uncurry DP) (𝓝[Work.Construction.Qd] (z0, 0)) (𝓝 l))
    (hσ : σ * l = l) :
    Tendsto (Function.uncurry D)
      (𝓝[Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)] (z0, 0)) (𝓝 l) := by
  have hset : Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)
      = Strip (-(Real.pi / 2)) 0 ∪ Strip 0 (Real.pi / 2) := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show (0 : ℝ) - Real.pi / 2 = -(Real.pi / 2) from by ring,
      show (0 : ℝ) + Real.pi / 2 = Real.pi / 2 from by ring]
  rw [hset, nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · have hmain : Tendsto (fun q : ℝ × ℝ => σ * DP q.1 (-q.2))
        (𝓝[Strip (-(Real.pi / 2)) 0] (z0, 0)) (𝓝 l) := by
      have h1 : Tendsto (fun q : ℝ × ℝ => DP q.1 (-q.2))
          (𝓝[Strip (-(Real.pi / 2)) 0] (z0, 0)) (𝓝 l) := tendsto_neg_comp hlim
      have h2 := h1.const_mul σ
      rwa [hσ] at h2
    refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => σ * DP q.1 (-q.2))
      (f₂ := Function.uncurry D) ?_ hmain
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hlower q.1 q.2 hq).symm
  · refine Tendsto.congr' (f₁ := Function.uncurry DP) (f₂ := Function.uncurry D) ?_
      (hlim.mono_left (nhdsWithin_mono _ strip_le_Qd))
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hupper q.1 q.2 hq).symm

/-- **The seam limits at `θ = π/2`**: as `tendsto_seam0`, with the reflection `π - θ` on the
upper half. -/
theorem tendsto_seamPi {D DP : ℝ → ℝ → ℝ} {σ l : ℝ} {z0 : ℝ}
    (hlower : ∀ w θ, (w, θ) ∈ Strip 0 (Real.pi / 2) → D w θ = DP w θ)
    (hupper : ∀ w θ, (w, θ) ∈ Strip (Real.pi / 2) Real.pi →
      D w θ = σ * DP w (Real.pi - θ))
    (hlim : Tendsto (Function.uncurry DP) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l))
    (hσ : σ * l = l) :
    Tendsto (Function.uncurry D)
      (𝓝[Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)] (z0, Real.pi / 2))
      (𝓝 l) := by
  have hset : Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)
      = Strip 0 (Real.pi / 2) ∪ Strip (Real.pi / 2) Real.pi := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
      show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
  rw [hset, nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · refine Tendsto.congr' (f₁ := Function.uncurry DP) (f₂ := Function.uncurry D) ?_
      (hlim.mono_left (nhdsWithin_mono _ strip_le_Qd))
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hlower q.1 q.2 hq).symm
  · have hmain : Tendsto (fun q : ℝ × ℝ => σ * DP q.1 (Real.pi - q.2))
        (𝓝[Strip (Real.pi / 2) Real.pi] (z0, Real.pi / 2)) (𝓝 l) := by
      have h1 : Tendsto (fun q : ℝ × ℝ => DP q.1 (Real.pi - q.2))
          (𝓝[Strip (Real.pi / 2) Real.pi] (z0, Real.pi / 2)) (𝓝 l) := tendsto_sub_comp hlim
      have h2 := h1.const_mul σ
      rwa [hσ] at h2
    refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => σ * DP q.1 (Real.pi - q.2))
      (f₂ := Function.uncurry D) ?_ hmain
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hupper q.1 q.2 hq).symm

/-! ## §5 Continuity at a seam -/

/-- **Continuity at `(z0, 0)`** from the two one-sided limits and the value on the seam line. -/
theorem continuousAt_seam0 {F : ℝ → ℝ → ℝ} {z0 : ℝ} (hz0 : 0 < z0)
    (hval : Function.uncurry F (z0, 0) = 0)
    (hup : Tendsto (Function.uncurry F) (𝓝[Strip 0 (Real.pi / 2)] (z0, 0)) (𝓝 0))
    (hlow : Tendsto (Function.uncurry F) (𝓝[Strip (-(Real.pi / 2)) 0] (z0, 0)) (𝓝 0))
    (hline : Tendsto (Function.uncurry F) (𝓝[Line0] (z0, 0)) (𝓝 0)) :
    ContinuousAt (Function.uncurry F) (z0, 0) := by
  have hset : Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)
      = Strip 0 (Real.pi / 2) ∪ Strip (-(Real.pi / 2)) 0 ∪ Line0 := by
    ext q
    rw [Work.FTS_StreamBdry.SB25.mem_glueU]
    simp only [Strip, Line0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff]
    rw [show (0 : ℝ) - Real.pi / 2 = -(Real.pi / 2) from by ring,
      show (0 : ℝ) + Real.pi / 2 = Real.pi / 2 from by ring]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_trichotomy q.2 0 with h | h | h
      · exact Or.inl (Or.inr ⟨h1, h2, h⟩)
      · exact Or.inr ⟨h1, h⟩
      · exact Or.inl (Or.inl ⟨h1, h, h3⟩)
    · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h3⟩)
      · exact ⟨h1, by linarith, h3⟩
      · exact ⟨h1, h2, by linarith [Real.pi_pos]⟩
      · rw [h3]; exact ⟨h1, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmem : Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2) ∈ 𝓝 (z0, 0) := by
    refine (Work.FTS_StreamBdry.SB25.isOpen_glueU 0 (Real.pi / 2)).mem_nhds ?_
    rw [Work.FTS_StreamBdry.SB25.mem_glueU]
    exact ⟨hz0, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hall : Tendsto (Function.uncurry F)
      (𝓝[Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)] (z0, 0)) (𝓝 0) := by
    rw [hset, nhdsWithin_union, nhdsWithin_union]
    exact (hup.sup hlow).sup hline
  rw [nhdsWithin_eq_nhds.mpr hmem] at hall
  show Tendsto (Function.uncurry F) (𝓝 (z0, 0)) (𝓝 (Function.uncurry F (z0, 0)))
  rw [hval]
  exact hall

/-- **Continuity at `(z0, π/2)`** as `continuousAt_seam0`. -/
theorem continuousAt_seamPi {F : ℝ → ℝ → ℝ} {z0 : ℝ} (hz0 : 0 < z0)
    (hval : Function.uncurry F (z0, Real.pi / 2) = 0)
    (hup : Tendsto (Function.uncurry F) (𝓝[Strip (Real.pi / 2) Real.pi] (z0, Real.pi / 2)) (𝓝 0))
    (hlow : Tendsto (Function.uncurry F) (𝓝[Strip 0 (Real.pi / 2)] (z0, Real.pi / 2)) (𝓝 0))
    (hline : Tendsto (Function.uncurry F) (𝓝[LinePi] (z0, Real.pi / 2)) (𝓝 0)) :
    ContinuousAt (Function.uncurry F) (z0, Real.pi / 2) := by
  have hset : Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)
      = Strip 0 (Real.pi / 2) ∪ Strip (Real.pi / 2) Real.pi ∪ LinePi := by
    ext q
    rw [Work.FTS_StreamBdry.SB25.mem_glueU]
    simp only [Strip, LinePi, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff]
    rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
      show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_trichotomy q.2 (Real.pi / 2) with h | h | h
      · exact Or.inl (Or.inl ⟨h1, h2, h⟩)
      · exact Or.inr ⟨h1, h⟩
      · exact Or.inl (Or.inr ⟨h1, h, h3⟩)
    · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h3⟩)
      · exact ⟨h1, h2, by linarith [h3, Real.pi_pos]⟩
      · exact ⟨h1, by linarith [h2], h3⟩
      · rw [h3]; exact ⟨h1, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmem : Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)
      ∈ 𝓝 (z0, Real.pi / 2) := by
    refine (Work.FTS_StreamBdry.SB25.isOpen_glueU (Real.pi / 2) (Real.pi / 2)).mem_nhds ?_
    rw [Work.FTS_StreamBdry.SB25.mem_glueU]
    exact ⟨hz0, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hall : Tendsto (Function.uncurry F)
      (𝓝[Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)] (z0, Real.pi / 2))
      (𝓝 0) := by
    rw [hset, nhdsWithin_union, nhdsWithin_union]
    exact (hlow.sup hup).sup hline
  rw [nhdsWithin_eq_nhds.mpr hmem] at hall
  show Tendsto (Function.uncurry F) (𝓝 (z0, Real.pi / 2))
    (𝓝 (Function.uncurry F (z0, Real.pi / 2)))
  rw [hval]
  exact hall

end

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Lgs_le_zero_of_max =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_le_zero_of_max` — the comparison half of the SB5 barrier

Companion of `Lgs_nonneg_of_max` (leaf E4a).  It says that a `C²` function `g` on a closed
rectangle `[zlo,zhi] × [alo,ahi] ⊂ Qd` whose **boundary** values are strictly negative and whose
`Lgs α`-image is strictly negative at every **interior** point cannot be positive anywhere:
`g ≤ 0` on the whole rectangle.

The proof is the standard Fermat/compactness argument.  If `g` were positive somewhere, the
continuous function `Function.uncurry g` attains a maximum `M > 0` on the compact rectangle at
some point `(z₀,θ₀)`; since the boundary values are `< 0 < M`, that point is interior
(`z₀ ∈ Ioo zlo zhi`, `θ₀ ∈ Ioo alo ahi`, hence also `z₀ > 0` and `θ₀ ∈ Ioo 0 (π/2)`, using
`0 < zlo`, `0 < alo`, `ahi < π/2`).  A global maximum of `g` on the rectangle is in particular a
one-dimensional local maximum of both slices `z ↦ g z θ₀` and `θ ↦ g z₀ θ`, so
`Lgs_nonneg_of_max` gives `0 ≤ Lgs α g z₀ θ₀`, contradicting the strict negativity hypothesis
`hneg` at the interior point `(z₀,θ₀)`.

This is exactly the `sb5_compare`/`sb5_barrier` interface: the barrier
`(M+δφ)(z/L)^{-k} + η` minus the solution is `≤ 0` on the half-strip, with the negative boundary
data on the outer rectangle and the strictly negative `Lgs`-image on the interior.
-/

open Filter

namespace Work.FTS_StreamBdry.SB25

theorem Lgs_le_zero_of_max (α zlo zhi alo ahi : ℝ) (g : ℝ → ℝ → ℝ)
    (hz : zlo < zhi) (ha : alo < ahi) (hz0 : 0 < zlo) (ha0 : 0 < alo) (ha1 : ahi < Real.pi / 2)
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi))
    (hbd : ∀ z θ, z ∈ Set.Icc zlo zhi → θ ∈ Set.Icc alo ahi →
      (z = zlo ∨ z = zhi ∨ θ = alo ∨ θ = ahi) → g z θ < 0)
    (hC2 : ∀ z θ, z ∈ Set.Ioo zlo zhi → θ ∈ Set.Ioo alo ahi →
      ContDiffAt ℝ 2 (Function.uncurry g) (z, θ))
    (hneg : ∀ z θ, z ∈ Set.Ioo zlo zhi → θ ∈ Set.Ioo alo ahi →
      Work.FTS_StreamBdry.SB25.Lgs α g z θ < 0) :
    ∀ z θ, z ∈ Set.Icc zlo zhi → θ ∈ Set.Icc alo ahi → g z θ ≤ 0 := by
  -- suppose `g > 0` somewhere; then the maximum on the compact rectangle is positive
  by_contra hcon
  push_neg at hcon
  obtain ⟨zw, θw, hzw, hθw, hpos⟩ := hcon
  have hSne : (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi).Nonempty := ⟨(zw, θw), hzw, hθw⟩
  have hScomp : IsCompact (Set.Icc zlo zhi ×ˢ Set.Icc alo ahi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨p, hpS, hpmax⟩ := hScomp.exists_isMaxOn hSne hcont
  obtain ⟨z0, θ0⟩ := p
  rw [Set.mem_prod] at hpS
  rw [isMaxOn_iff] at hpmax
  have hmax : g zw θw ≤ g z0 θ0 := hpmax (zw, θw) ⟨hzw, hθw⟩
  have hz0posV : 0 < g z0 θ0 := lt_of_lt_of_le hpos hmax
  -- the maximiser is not on the boundary (the boundary values are `< 0`)
  have hzne : z0 ≠ zlo := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inl h)
    linarith
  have hzne' : z0 ≠ zhi := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inl h))
    linarith
  have hθne : θ0 ≠ alo := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inr (Or.inl h)))
    linarith
  have hθne' : θ0 ≠ ahi := by
    intro h
    have hb := hbd z0 θ0 hpS.1 hpS.2 (Or.inr (Or.inr (Or.inr h)))
    linarith
  have hz0Ioo : z0 ∈ Set.Ioo zlo zhi :=
    ⟨lt_of_le_of_ne hpS.1.1 (Ne.symm hzne), lt_of_le_of_ne hpS.1.2 hzne'⟩
  have hθ0Ioo : θ0 ∈ Set.Ioo alo ahi :=
    ⟨lt_of_le_of_ne hpS.2.1 (Ne.symm hθne), lt_of_le_of_ne hpS.2.2 hθne'⟩
  have hz0pos : 0 < z0 := lt_of_lt_of_le hz0 hpS.1.1
  have hθ0mem : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_lt_of_le ha0 hpS.2.1, lt_of_le_of_lt hpS.2.2 ha1⟩
  -- the maximiser is a one-dimensional local maximum of both slices
  have hmz : IsLocalMax (fun z => g z θ0) z0 := by
    rw [IsLocalMax]
    filter_upwards [isOpen_Ioo.mem_nhds hz0Ioo] with z' hz'
    exact hpmax (z', θ0) ⟨⟨le_of_lt hz'.1, le_of_lt hz'.2⟩, hpS.2⟩
  have hmθ : IsLocalMax (fun θ => g z0 θ) θ0 := by
    rw [IsLocalMax]
    filter_upwards [isOpen_Ioo.mem_nhds hθ0Ioo] with θ' hθ'
    exact hpmax (z0, θ') ⟨hpS.1, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩⟩
  -- Fermat at an interior maximum contradicts the strict sign of `Lgs`
  have hge := Lgs_nonneg_of_max α g z0 θ0 hz0pos hθ0mem (hC2 z0 θ0 hz0Ioo hθ0Ioo) hmz hmθ
  have hlt := hneg z0 θ0 hz0Ioo hθ0Ioo
  linarith

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.bslOp_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

/-- The ground-state identity of the singular stream-boundary problem, in direct (non-`Prop`)
form: for `(z,θ)` in the open quadrant and `Q` of class `C²` there,

`bslOp α Q z θ = sin(2θ) · Lgs α (Q / sin 2θ) z θ`.

This is the pointwise instance of `Work.FTS_StreamBdry.SB25.BslOpEqS2Lgs`
(proved in `SB25/bslOp_eq_s2_Lgs.lean`). -/
theorem bslOp_split (α : ℝ) (Q : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hQd : (z, θ) ∈ Work.Construction.Qd)
    (hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ)) :
    Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ *
        Work.FTS_StreamBdry.SB25.Lgs α
          (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ :=
  Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs α Q z θ hQd hQ

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.glue_line_C2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.glue_line_C2` (leaf B7c)

`GlueLineC2 h c r` states that a function `h : ℝ → ℝ → ℝ` which is `C²` on the two open
half-strips `θ < c` and `θ > c`, continuous on the full strip `(0,∞) × (c-r,c+r)`, and whose
six partial derivatives of order `≤ 2` (`∂_z`, `∂_θ`, `∂_z∂_z`, `∂_θ∂_z`, `∂_z∂_θ`, `∂_θ∂_θ`)
have limits at every point `(z₀, c)` of the seam (approached along the punctured strip), is
`C²` on the full strip.

This is the leaf-plan recipe "B7a applied to `h`, `pz h`, `pth h`, then B7b":

* `h` is `C¹` on the punctured strip (from `C²`) and continuous on the full strip, and the
  limits of `∂_z h`, `∂_θ h` at the seam are among the six assumed limits; hence
  `glue_line_C1 h c r` gives `h ∈ C¹` on the full strip, together with the *continuity* of
  `∂_z h`, `∂_θ h`, which is the extra hypothesis needed to feed `pz h` and `pth h` into
  `glue_line_C1`;
* on the punctured strip, `uncurry_partial_c1` gives `uncurry (pz h)` and `uncurry (pth h)`
  `C¹` from `uncurry h` `C²`; their limits at the seam are again among the six, so
  `glue_line_C1 (pz h) c r` and `glue_line_C1 (pth h) c r` give `C¹`-ness of the two first
  partials on the full strip;
* `contDiffOn_two_of_partials` (Mathlib's `C¹` with `C¹` partials is `C²`, on an open set)
  then upgrades to `uncurry h` `C²` on the full strip.
-/

noncomputable section

open scoped Real Topology NNReal ContDiff
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

theorem glue_line_C2 (h : ℝ → ℝ → ℝ) (c r : ℝ) :
    Work.FTS_StreamBdry.SB25.GlueLineC2 h c r := by
  intro hr hC2 hcont hlim
  have hSopen : IsOpen (glueS c r) := isOpen_glueS c r
  have hUopen : IsOpen (glueU c r) := isOpen_glueU c r
  -- the two first partials of `h` are `C¹` on the punctured strip
  obtain ⟨hpzS, hpthS⟩ := Work.Spaces.uncurry_partial_c1 hSopen hC2
  -- the limits of `∂_z h`, `∂_θ h` at the seam
  have hlim_pz : ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz h))
      (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz h) (by simp) z0 hz0
  have hlim_pth : ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth h))
      (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth h) (by simp) z0 hz0
  -- B7a for `h`: `C¹` on the full strip plus continuity of both first partials
  have hC1h := glue_line_C1 h c r hr (hC2.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hcont
    hlim_pz hlim_pth
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry h) (glueU c r) := hC1h.1
  have hcont_pz : ContinuousOn (Function.uncurry (Work.Spaces.pz h)) (glueU c r) := hC1h.2.1
  have hcont_pth : ContinuousOn (Function.uncurry (Work.Spaces.pth h)) (glueU c r) := hC1h.2.2
  -- the limits of the four second partials at the seam
  have hlim_ppz : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz (Work.Spaces.pz h)) (by simp) z0 hz0
  have hlim_ptpz : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth (Work.Spaces.pz h)) (by simp) z0 hz0
  have hlim_ppth : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pz (Work.Spaces.pth h)) (by simp) z0 hz0
  have hlim_ptpth : ∀ z0 : ℝ, 0 < z0 →
      ∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth h)))
        (𝓝[glueS c r] (z0, c)) (𝓝 l) :=
    fun z0 hz0 => hlim (Work.Spaces.pth (Work.Spaces.pth h)) (by simp) z0 hz0
  -- B7a for `∂_z h`
  have hC1pz := glue_line_C1 (Work.Spaces.pz h) c r hr hpzS hcont_pz hlim_ppz hlim_ptpz
  have hpzU : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz h)) (glueU c r) := hC1pz.1
  -- B7a for `∂_θ h`
  have hC1pth := glue_line_C1 (Work.Spaces.pth h) c r hr hpthS hcont_pth hlim_ppth hlim_ptpth
  have hpthU : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth h)) (glueU c r) := hC1pth.1
  -- B7b: `C¹` with `C¹` partials is `C²`
  exact contDiffOn_two_of_partials h (glueU c r) hUopen hC1 hpzU hpthU

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.psiP_D3_le` — the third radial derivative of the `U`-slot part

`psiP αG Ψ = -(s2 θ/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is the particular solution of the level-0
ODE `αG·D_z P + 3 P = -s2·U'(Ψ)` (`SB1/psiP_ode`), whose *first two* radial derivatives are
controlled directly by the slot bounds (`SlotBd`) through the scaling identity of the parameter
integral (`SBpsiP/DzJ_crux`, `SB3D3/DzIter2_psiP_eq_le`):

  `|D_z² (psiP αG Ψ)| ≤ M·s2 θ / 3`   (the sharp constant `1/3 = αG·∫₀¹v^{3/αG-1}dv`).

The *third* derivative is not of this form (`SlotBd` does not bound `D_z³U'`); it is obtained from
the ODE instead.  Writing `P = psiP αG Ψ`, `U = U'(Ψ)`, `c = -(s2 θ/αG)` and `k = 3/αG`, the ODE
reads `D_z P = c·U - k·P`; applying the operator `D_z = z∂_z` twice more gives the tower

  `D_z² P = c·D_z U - k·D_z P`,     `D_z³ P = c·D_z² U - k·D_z² P`,

and eliminating `D_z P` between the first identity and `αG·k = 3`, `αG·c = -s2 θ` gives

  `αG·D_z³ P + 3·D_z² P = -s2 θ·D_z² U`         (`psiP_D3_aux_tower`, `hI3` below).

Combining this with the sharp second-order bound yields

  `|D_z³ P| ≤ (s2 θ·M + 3·M·s2 θ/3)/αG = (2M/αG)·s2 θ`,

which is the statement of this file.

## Route of the tower

The tower is a statement about *slice* functions `t ↦ P t` at fixed `θ`.  Its inputs are

* `hode`: the ODE, read at fixed `θ` (`SB1.psiP_ode`);
* `hdP`: differentiability of the `z`-slices of `P` (`SB1.psiP_diff`);
* `hdφ`, `hdφ'`: differentiability of the `z`-slices of `U'` and of `∂_z U'`, from the `C²`
  regularity of the slot (`psiP_D3_aux_Uprime_c2`, proved here by the same `fderiv` computation
  as `SB1/contDiffOn_uncurry_Uprime`, one order higher).

The tower itself (`psiP_D3_aux_tower`) is then pure one-dimensional calculus: an identity
`D_z P = c·U - k·P` between functions on `(0,∞)` may be differentiated, because the two functions
agree *eventually* and `deriv` only sees the germ (`Filter.EventuallyEq.deriv_eq`); the
`DifferentiableAt` hypotheses are exactly what is needed to evaluate `deriv` of the right side and
to know that the *first* derivative function is itself differentiable for the second step.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false

/-! ## §0 The `C²` regularity of the `U`-slot and of its `z`-derivative -/

/-- `∂_z` costs one order of smoothness on an open set, at finite order. -/
theorem psiP_D3_aux_pz_smooth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **The `U`-slot is `C²` on the open quadrant** as soon as `Ψ` is `C³` there.
`U'(Ψ) = (-3Ψ - αG·z∂_zΨ)/sin 2θ`: the numerator is `C²` (`∂_z` costs one order) and the
denominator is `C^∞` and non-vanishing on `Qd`. -/
theorem psiP_D3_aux_Uprime_c2 {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    psiP_D3_aux_pz_smooth hQd h3
  have hnum : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd := by
    refine (contDiffOn_const.mul h2).sub ?_
    exact (contDiffOn_const.mul (contDiff_fst.contDiffOn)).mul hpz
  have hden : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [Real.pi_pos, hp.2.2]))
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Uprime, Work.Construction.Uop,
    Work.Construction.s2, Work.Spaces.pz, Pi.div_apply]

/-! ## §1 The one-dimensional tower for an abstract pair `(P, φ)` -/

/-- **The tower.**  If `P, φ : ℝ → ℝ` satisfy `t·P'(t) = c·φ(t) - k·P(t)` on `(0,∞)` and `P`, `φ`,
`φ'` are differentiable there, then applying `t·d/dt` to that identity twice gives

  `t·(t·P')'(t) = c·(t·φ'(t)) - k·(t·P'(t))`,
  `t·(t·(t·P')')'(t) = c·(t·(t·φ')'(t)) - k·(t·(t·P')'(t))`.

This is `(D_z P = c·U - k·P) ⟹ (D_z²P = c·D_zU - k·D_zP) ⟹ (D_z³P = c·D_z²U - k·D_z²P)`
for the *slice* functions, with `D_z = t·d/dt`. -/
theorem psiP_D3_aux_tower {c k : ℝ} {P φ : ℝ → ℝ}
    (hode : ∀ t ∈ Set.Ioi (0:ℝ), t * deriv P t = c * φ t - k * P t)
    (hdP : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ P t)
    (hdφ : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ φ t)
    (hdφ' : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun s => deriv φ s) t) :
    (∀ t ∈ Set.Ioi (0:ℝ),
        t * deriv (fun s => s * deriv P s) t = c * (t * deriv φ t) - k * (t * deriv P t)) ∧
    (∀ t ∈ Set.Ioi (0:ℝ),
        t * deriv (fun s => s * deriv (fun u => u * deriv P u) s) t
          = c * (t * deriv (fun u => u * deriv φ u) t)
            - k * (t * deriv (fun u => u * deriv P u) t)) := by
  have hb : ∀ t ∈ Set.Ioi (0:ℝ),
      t * deriv (fun s => s * deriv P s) t = c * (t * deriv φ t) - k * (t * deriv P t) := by
    intro t ht
    have hEq : (fun s => s * deriv P s) =ᶠ[𝓝 t] (fun s => c * φ s - k * P s) :=
      Set.EqOn.eventuallyEq_of_mem (fun s hs => hode s hs) (isOpen_Ioi.mem_nhds ht)
    have h1 : deriv (fun s => s * deriv P s) t = c * deriv φ t - k * deriv P t := by
      rw [hEq.deriv_eq]
      exact (((hdφ t ht).hasDerivAt.const_mul c).sub
        ((hdP t ht).hasDerivAt.const_mul k)).deriv
    rw [h1]
    ring
  refine ⟨hb, ?_⟩
  intro t ht
  have hEq2 : (fun s => s * deriv (fun u => u * deriv P u) s)
      =ᶠ[𝓝 t] (fun s => c * (s * deriv φ s) - k * (s * deriv P s)) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => hb s hs) (isOpen_Ioi.mem_nhds ht)
  have hEqP : (fun s => s * deriv P s) =ᶠ[𝓝 t] (fun s => c * φ s - k * P s) :=
    Set.EqOn.eventuallyEq_of_mem (fun s hs => hode s hs) (isOpen_Ioi.mem_nhds ht)
  have hP1 : DifferentiableAt ℝ (fun s => s * deriv P s) t :=
    hEqP.differentiableAt_iff.mpr (((hdφ t ht).const_mul c).sub ((hdP t ht).const_mul k))
  have hφ1 : DifferentiableAt ℝ (fun s => s * deriv φ s) t :=
    differentiableAt_id.mul (hdφ' t ht)
  have h1 : deriv (fun s => s * deriv (fun u => u * deriv P u) s) t
      = c * deriv (fun s => s * deriv φ s) t - k * deriv (fun s => s * deriv P s) t := by
    rw [hEq2.deriv_eq]
    exact (((hφ1.hasDerivAt.const_mul c).sub (hP1.hasDerivAt.const_mul k))).deriv
  rw [h1]
  ring

/-! ## §2 The sharp second-order bound `|D_z² psiP| ≤ M·s2 θ/3`

This is the `j = 2` case of the scaling identity for the parameter integral
`J c h z θ = ∫₀¹ v^c h(zv,θ) dv` (`SBpsiP/DzJ_crux`, proved by `J_Dz_eq`): applying it to
`h = U'(Ψ)` and then to `h = D_z U'(Ψ)` gives

  `D_z² (psiP αG Ψ) = -(s2 θ/αG)·J (3/αG-1) (D_z² U'(Ψ))`,

and the elementary estimate `|J c h| ≤ M/(c+1) = M·αG/3` (`SBpsiP/SelfBound`, for `|h| ≤ M`)
turns this into `M·s2 θ/3`.  The hypotheses of `J_Dz_eq` (continuity of the slot iterates and
their `z`-slice differentiability) are supplied by the finite-order smoothness
`SBpsiP.UprimeIterSmooth_self`.
-/

/-- `C¹` on the open quadrant implies differentiability of the `z`-slices. -/
private theorem psiP_D3_aux_slice_diff_one {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 1 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp))

/-- `C²` on the open quadrant implies differentiability of the `z`-slices. -/
private theorem psiP_D3_aux_slice_diff_two {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp))

/-- The `θ`-only multiple rule for `D_z`. -/
private theorem psiP_D3_aux_Dz_theta_mul {a : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    Work.Spaces.Dz (fun z θ => a θ * F z θ) z θ = a θ * Work.Spaces.Dz F z θ := by
  show z * deriv (fun z' => a θ * F z' θ) z = a θ * (z * deriv (fun z' => F z' θ) z)
  rw [deriv_const_mul _ hd]
  ring

/-- **The sharp second-order bound**: `|D_z² (psiP αG Ψ)| ≤ M·s2 θ/3`. -/
theorem psiP_D3_aux_DzIter2_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ / 3 := by
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot h1)
  have hc : (-1 : ℝ) < 3 / αG - 1 := by
    have : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  have hsm : ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
      (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SBpsiP.UprimeIterSmooth_self hαG h3
  have hcont_all : ∀ i : ℕ, i ≤ 2 → ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter i (Uprime αG Ψ))) Work.Construction.Qd :=
    fun i hi => (hsm i hi).continuousOn
  have hbnd_all : ∀ i : ℕ, i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter i (Uprime αG Ψ) z θ| ≤ M :=
    fun i hi z θ hzθ => SlotBd.Dz_le hslot hzθ hi
  have hslice_all : ∀ i : ℕ, i ≤ 1 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i (Uprime αG Ψ) z' θ) z := by
    intro i hi z θ hzθ
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact psiP_D3_aux_slice_diff_two hzθ (hsm 0 (by norm_num))
    · exact psiP_D3_aux_slice_diff_one hzθ (hsm 1 (by norm_num))
  -- the level-0 identity
  have hbase : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ := by
    intro z θ hzθ
    rw [Work.FTS_StreamBdry.psiP_eq_Iint, Work.FTS_StreamBdry.SB3.Iint_eq_J]
  -- the level-1 identity
  have h1pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 1 (psiP αG Ψ) z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := Work.FTS_StreamBdry.SBpsiP.J_Dz_eq (c := 3 / αG - 1) hc
      (h := Uprime αG Ψ)
      (hcont_all 0 (by norm_num)) (hcont_all 1 (by norm_num))
      (hslice_all 0 (by norm_num))
      (hbnd_all 0 (by norm_num)) (hbnd_all 1 (by norm_num)) z θ hzθ
    have hcongr : Work.Spaces.pz (psiP αG Ψ) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen hQd
        (fun q hq => by
          show Function.uncurry (psiP αG Ψ) q = Function.uncurry (fun z θ =>
            -(Work.Construction.s2 θ / αG)
              * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) q
          simpa only [Function.uncurry] using hbase q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (psiP αG Ψ) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ := by
      show z * Work.Spaces.pz (psiP αG Ψ) z θ = z * Work.Spaces.pz (fun z θ =>
        -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
      rw [psiP_D3_aux_Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 0 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ
    rw [Work.Spaces.DzIter_zero, hDz, hval]
  -- the level-2 identity
  have h2pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 2 (psiP αG Ψ) z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := Work.FTS_StreamBdry.SBpsiP.J_Dz_eq (c := 3 / αG - 1) hc
      (h := Work.Spaces.DzIter 1 (Uprime αG Ψ))
      (hcont_all 1 (by norm_num)) (hcont_all 2 (by norm_num))
      (hslice_all 1 (by norm_num))
      (hbnd_all 1 (by norm_num)) (hbnd_all 2 (by norm_num)) z θ hzθ
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen hQd
        (fun q hq => by
          show Function.uncurry (Work.Spaces.DzIter 1 (psiP αG Ψ)) q
            = Function.uncurry (fun z θ => -(Work.Construction.s2 θ / αG)
                * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                    (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) q
          simpa only [Function.uncurry] using h1pt q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = z * Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
              (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
      rw [psiP_D3_aux_Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ
    rw [hDz, hval]
  -- the integral bound
  have hJb : |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
      (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ| ≤ M * (αG / 3) := by
    have hφcont : ContinuousOn
        (fun v : ℝ => Work.Spaces.DzIter 2 (Uprime αG Ψ) (z * v) θ)
        (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (z * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := (hcont_all 2 (by norm_num)).comp hlin
        (fun v hv => ⟨mul_pos hz hv.1, hθ1, hθ2⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    have hφbd : ∀ v ∈ Set.Ioc (0 : ℝ) 1,
        |Work.Spaces.DzIter 2 (Uprime αG Ψ) (z * v) θ| ≤ M :=
      fun v hv => hbnd_all 2 (by norm_num) (z * v) θ ⟨mul_pos hz hv.1, hθ1, hθ2⟩
    have hmain := Work.FTS_StreamBdry.SBpsiP.J_bound_self (c := 3 / αG - 1) (B := M)
      hc hM hφcont hφbd
    have hsimp : M / (3 / αG - 1 + 1) = M * (αG / 3) := by
      rw [show (3 / αG - 1 + 1 : ℝ) = 3 / αG by ring, div_eq_mul_inv, inv_div]
    simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hmain.trans_eq hsimp
  -- assembly
  have hAa : |-(Work.Construction.s2 θ / αG)| = Work.Construction.s2 θ / αG := by
    rw [abs_neg, abs_of_nonneg (div_nonneg hs2nn (le_of_lt hαG))]
  rw [h2pt z θ hmem, abs_mul, hAa]
  have hstep : (Work.Construction.s2 θ / αG) * |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
        (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ|
      ≤ (Work.Construction.s2 θ / αG) * (M * (αG / 3)) :=
    mul_le_mul_of_nonneg_left hJb (div_nonneg hs2nn (le_of_lt hαG))
  have hstep2 : (Work.Construction.s2 θ / αG) * (M * (αG / 3))
      = M * Work.Construction.s2 θ / 3 := by
    field_simp
  linarith [hstep, hstep2]

/-! ## §3 The third-order bound -/

theorem psiP_D3_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ (2 * M / αG) * Work.Construction.s2 θ := by
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  -- positivity data
  have hs2pos : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
  have hMnn : 0 ≤ M := by
    have h1 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot h1)
  -- the two regularity inputs for the tower
  have hUsm : ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    psiP_D3_aux_Uprime_c2 h3
  have hpzU : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.pz (Uprime αG Ψ))) Work.Construction.Qd :=
    psiP_D3_aux_pz_smooth hQd hUsm
  have hode_psiP : Work.FTS_StreamBdry.PsiPOde αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  -- slice notation
  set P : ℝ → ℝ := fun t => Work.FTS.StreamBdryIface.psiP αG Ψ t θ with hP
  set φ : ℝ → ℝ := fun t => Work.FTS.StreamBdryIface.Uprime αG Ψ t θ with hφ
  set c₂ : ℝ := -(Work.Construction.s2 θ / αG) with hc₂
  set k : ℝ := 3 / αG with hk
  -- the ODE, slicewise
  have hode : ∀ t ∈ Set.Ioi (0:ℝ), t * deriv P t = c₂ * φ t - k * P t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h := hode_psiP t θ hmemt
    have h' : αG * (t * deriv P t) + 3 * P t = -(Work.Construction.s2 θ) * φ t := by
      have h'' : αG * t * deriv P t + 3 * P t = -(Work.Construction.s2 θ) * φ t := by
        simpa only [Work.Spaces.pz, hP, hφ] using h
      rw [mul_assoc] at h''
      exact h''
    rw [hc₂, hk]
    have h'' : αG * (t * deriv P t) = -(Work.Construction.s2 θ) * φ t - 3 * P t := by
      linarith [h']
    field_simp
    linarith [h'']
  have hdP : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ P t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    simpa only [hP] using (hpdiff t θ hmemt).1
  have hdφ : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ φ t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h1 := Work.Spaces.differentiableAt_curry_left
      ((hUsm.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    simpa only [hφ] using h1
  have hdφ' : ∀ t ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun s => deriv φ s) t := by
    intro t ht
    have hmemt : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ1, hθ2⟩
    have h1 := Work.Spaces.differentiableAt_curry_left
      ((hpzU.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    simpa only [hφ, Work.Spaces.pz] using h1
  have htower := psiP_D3_aux_tower hode hdP hdφ hdφ'
  -- the sharp second-order bound (from the level-2 scaling identity) and the slot bound
  have hb2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ M * Work.Construction.s2 θ / 3 :=
    psiP_D3_aux_DzIter2_le hαG h3 hslot z θ hmem
  have hM2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ| ≤ M :=
    Work.FTS_StreamBdry.SlotBd.Dz_le hslot hmem (j := 2) (by norm_num)
  -- the `DzIter` values are the slice values
  have hD2P : Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = z * deriv (fun s => s * deriv P s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hP]
  have hD3P : Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = z * deriv (fun s => s * deriv (fun u => u * deriv P u) s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hP]
  have hD2φ : Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ
      = z * deriv (fun s => s * deriv φ s) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz, hφ]
  -- the third-order ODE identity
  have hI3 : αG * (Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ)
      + 3 * (Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ)
      = -(Work.Construction.s2 θ)
        * (Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ) := by
    rw [hD3P, hD2P, hD2φ, htower.2 z hz, hc₂, hk]
    field_simp
    ring
  -- conclusion
  have hD3eq : Work.Spaces.DzIter 3 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = (-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ) / αG := by
    rw [eq_div_iff (ne_of_gt hαG)]
    linarith [hI3]
  rw [hD3eq]
  have h1 : |-(Work.Construction.s2 θ
        * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
        - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
      ≤ Work.Construction.s2 θ * M + 3 * (M * Work.Construction.s2 θ / 3) := by
    refine (abs_sub _ _).trans ?_
    have hle1 : |-(Work.Construction.s2 θ
          * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)|
        ≤ Work.Construction.s2 θ * M := by
      rw [abs_neg, abs_mul, abs_of_nonneg hs2nn]
      exact mul_le_mul_of_nonneg_left hM2 hs2nn
    have hle2 : |3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ 3 * (M * Work.Construction.s2 θ / 3) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
    linarith
  calc |(-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ) / αG|
      = |-(Work.Construction.s2 θ
            * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.Uprime αG Ψ) z θ)
          - 3 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| / αG := by
        rw [abs_div, abs_of_pos hαG]
    _ ≤ (Work.Construction.s2 θ * M + 3 * (M * Work.Construction.s2 θ / 3)) / αG := by
        gcongr
    _ = (2 * M / αG) * Work.Construction.s2 θ := by
        field_simp
        ring

end Work.FTS_StreamBdry.SB3
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.psiP_c2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3

theorem psiP_c2 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ))
      Work.Construction.Qd := by
  -- SB1′: on the open quadrant, `Ψ = psiP αG Ψ + κ · gaugeMode αG`
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  -- `Ψ` is `C²` and the gauge mode is analytic on `Qd`, so their difference is `C²`
  have hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
    h3.of_le (by norm_num)
  have hg : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG) p)
      Work.Construction.Qd :=
    hΨ.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

end Work.FTS_StreamBdry.SB3
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.Temps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.Temps` — the `wfun` facts used by the ODE bound

The elementary facts about `wfun θ = sin²θ cos³θ` needed by the singular-ODE bound: positivity,
the two quotient bounds, the two lower bounds and the four integral comparisons.  Everything is
derived from the unconditional identity `wfun_div_s2_eq` of `OdeFacts`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false

lemma Wpos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < wfun θ := by
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  rw [wfun]
  exact mul_pos (pow_pos hs 2) (pow_pos hc 3)

/-- `wfun` is continuous (as the product `sin²·cos³`). -/
lemma continuous_wfun : Continuous wfun := by
  have h : wfun = fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3 := rfl
  rw [h]; fun_prop

/-- `wfun θ = sin θ cos²θ / 2 · sin 2θ` on `[0, π/2]`. -/
lemma Wdiv_le_theta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    wfun θ / Real.sin (2 * θ) ≤ θ / 2 := by
  rw [wfun_div_s2_eq]
  have hsin : Real.sin θ ≤ θ := le_of_lt (Real.sin_lt hθ.1)
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hmul : Real.sin θ * Real.cos θ ^ 2 ≤ θ * 1 :=
    mul_le_mul hsin hcos (sq_nonneg (Real.cos θ)) hθ.1.le
  linarith

lemma Wdiv_le_right {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    wfun θ / Real.sin (2 * θ) ≤ (Real.pi / 2 - θ) ^ 2 / 2 := by
  rw [wfun_div_s2_eq]
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
  have hδle : δ ≤ Real.pi := by rw [hδ]; linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ = Real.sin δ := by rw [hδ, Real.sin_pi_div_two_sub]
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsδ : Real.sin δ ≤ δ := le_of_lt (Real.sin_lt hδpos)
  have hsδnn : 0 ≤ Real.sin δ := Real.sin_nonneg_of_mem_Icc ⟨hδpos.le, hδle⟩
  have hsδ2 : Real.sin δ ^ 2 ≤ δ ^ 2 := by nlinarith [hsδ, hsδnn, hδpos]
  rw [hcos]
  have hmul : Real.sin θ * Real.sin δ ^ 2 ≤ 1 * δ ^ 2 :=
    mul_le_mul hsin1 hsδ2 (sq_nonneg _) (by norm_num)
  linarith

lemma Wge_left {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 ≤ wfun θ := by
  have hsin : 2 / Real.pi * θ ≤ Real.sin θ :=
    Real.mul_le_sin hθ.1.le (by linarith [hθ.2, Real.pi_pos])
  have hsin2 : (2 / Real.pi * θ) ^ 2 ≤ Real.sin θ ^ 2 := by
    have h1 : 0 ≤ 2 / Real.pi * θ := mul_nonneg (by positivity) hθ.1.le
    nlinarith [hsin, h1]
  have hsinn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
  have hsinle : Real.sin θ ≤ Real.sqrt 2 / 2 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos, hθ.1.le])
      (by linarith [Real.pi_pos]) hθ.2
    rwa [Real.sin_pi_div_four] at h
  have hsinsq : Real.sin θ ^ 2 ≤ 1 / 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have h3 : Real.sin θ ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := by
      have hnn : 0 ≤ Real.sqrt 2 / 2 := by positivity
      nlinarith [hsinle, hnn, hsinn]
    linarith [h2, h3]
  have hcos2 : 1 / 2 ≤ Real.cos θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have hnn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hθ.1.le], by linarith [hθ.2, Real.pi_pos]⟩
    have h2 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos θ ^ 2 := by
      have h3 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
      linarith [h3, hcos2]
    nlinarith [h2, hnn, Real.sqrt_nonneg 2]
  have hcos3 : (Real.sqrt 2 / 2) ^ 3 ≤ Real.cos θ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcos 3
  have hval : (Real.sqrt 2 / 2) ^ 3 = Real.sqrt 2 / 4 := by
    rw [div_pow, show (Real.sqrt 2) ^ 3 = Real.sqrt 2 * (Real.sqrt 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  have hexp : (2 / Real.pi * θ) ^ 2 * (Real.sqrt 2 / 4)
      = Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2 := by
    field_simp
    ring
  rw [wfun]
  rw [hval] at hcos3
  calc Real.sqrt 2 * θ ^ 2 / Real.pi ^ 2
      = (2 / Real.pi * θ) ^ 2 * (Real.sqrt 2 / 4) := hexp.symm
    _ ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 :=
        mul_le_mul hsin2 hcos3 (by positivity) (sq_nonneg _)

lemma Wge_right {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    4 * (Real.pi / 2 - θ) ^ 3 / Real.pi ^ 3 ≤ wfun θ := by
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
  have hδle : δ ≤ Real.pi / 2 := by rw [hδ]; linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ = Real.sin δ := by rw [hδ, Real.sin_pi_div_two_sub]
  have hs : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδpos.le hδle
  have hs2 : (1 / 2 : ℝ) ≤ Real.sin θ ^ 2 := by
    have h1 : Real.sqrt 2 / 2 ≤ Real.sin θ := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        hθ.2.le hθ.1
      rwa [Real.sin_pi_div_four] at h
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have h3 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.sin θ ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 2 / 2) h1
      simpa [pow_two] using h
    linarith [h2, h3]
  have hc3 : (2 / Real.pi * δ) ^ 3 ≤ Real.cos θ ^ 3 := by
    rw [hcos]
    exact pow_le_pow_left₀ (by positivity) hs 3
  have hexp : (1 / 2 : ℝ) * ((2 / Real.pi * δ) ^ 3) = 4 * δ ^ 3 / Real.pi ^ 3 := by
    rw [mul_pow]
    field_simp
    ring
  rw [wfun, ← hexp]
  exact mul_le_mul hs2 hc3 (by positivity) (sq_nonneg _)

lemma Wderiv {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt wfun
      (wfun θ * (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)) θ := by
  have hsne : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hcne : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).pow 2
  have hc : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ)) θ :=
    (Real.hasDerivAt_cos θ).pow 3
  have h := hs.mul hc
  have hfun : wfun = (fun t : ℝ => Real.sin t ^ 2) * (fun t : ℝ => Real.cos t ^ 3) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hs2ne : 2 * Real.sin θ * Real.cos θ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hsne) hcne
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  simp only [Pi.mul_apply]
  field_simp
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hc4 : Real.cos θ ^ 4 = (1 - Real.sin θ ^ 2) ^ 2 := by
    rw [show Real.cos θ ^ 4 = (Real.cos θ ^ 2) ^ 2 by ring, hc2]
  rw [hc4, hc2]
  ring

lemma Wint1 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∫ t in (0 : ℝ)..θ, wfun t ≤ θ ^ 3 / 3 := by
  have hle : ∫ t in (0 : ℝ)..θ, wfun t ≤ ∫ t in (0 : ℝ)..θ, t ^ 2 := by
    refine intervalIntegral.integral_mono_on hθ.1 (continuous_wfun.intervalIntegrable 0 θ) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 θ
    · have ht1 : t ≤ Real.pi / 2 := le_trans ht.2 hθ.2
      have hsin : Real.sin t ≤ t := Real.sin_le ht.1
      have hsinn : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht1, Real.pi_pos]⟩
      have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [ht1]⟩
      have hs2 : Real.sin t ^ 2 ≤ t ^ 2 := by nlinarith [hsin, hsinn, ht.1]
      have hc2 : Real.cos t ^ 2 ≤ 1 := by nlinarith [hcos1, hcosnn]
      have hc3 : Real.cos t ^ 3 ≤ 1 := by
        calc Real.cos t ^ 3 = Real.cos t ^ 2 * Real.cos t := by ring
          _ ≤ 1 * 1 := mul_le_mul hc2 hcos1 hcosnn (by norm_num)
          _ = 1 := by norm_num
      rw [wfun]
      have := mul_le_mul hs2 hc3 (by positivity) (sq_nonneg t)
      linarith
  have hftc : ∫ t in (0 : ℝ)..θ, t ^ 2 = θ ^ 3 / 3 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) θ,
        HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      intro t ht
      have h := (hasDerivAt_id t).pow 3
      have h2 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) ((3 * t ^ (3 - 1) * 1) / 3) t :=
        h.div_const 3
      convert h2 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 θ)]
    ring
  linarith [hftc ▸ hle]

lemma Wint2 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ θ ^ 2 / 4 := by
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hle : ∫ t in (0 : ℝ)..θ, wfun t / Real.sin (2 * t) ≤ ∫ t in (0 : ℝ)..θ, t / 2 := by
    refine intervalIntegral.integral_mono_on hθ.1 (hcont1.intervalIntegrable 0 θ) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => t / 2).intervalIntegrable 0 θ
    · rw [wfun_div_s2_eq]
      have ht1 : t ≤ Real.pi / 2 := le_trans ht.2 hθ.2
      have hsin : Real.sin t ≤ t := Real.sin_le ht.1
      have hsinn : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht1, Real.pi_pos]⟩
      have hcos : Real.cos t ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.sin t)]
      have := mul_le_mul hsin hcos (sq_nonneg _) ht.1
      linarith
  have hftc : ∫ t in (0 : ℝ)..θ, t / 2 = θ ^ 2 / 4 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) θ,
        HasDerivAt (fun s : ℝ => s ^ 2 / 4) (t / 2) t := by
      intro t ht
      have h := (hasDerivAt_id t).pow 2
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 4) ((2 * t ^ (2 - 1) * 1) / 4) t :=
        h.div_const 4
      convert h2 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => t / 2).intervalIntegrable 0 θ)]
    ring
  linarith [hftc ▸ hle]

lemma Wint3 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∫ t in θ..(Real.pi / 2), wfun t ≤ (Real.pi / 2 - θ) ^ 4 / 4 := by
  have hle : ∫ t in θ..(Real.pi / 2), wfun t
      ≤ ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 3 := by
    refine intervalIntegral.integral_mono_on hθ.2.le
      (continuous_wfun.intervalIntegrable θ (Real.pi / 2)) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 3).intervalIntegrable
        θ (Real.pi / 2)
    · have ht1 : t ≤ Real.pi / 2 := ht.2
      have hcos : Real.cos t ≤ Real.pi / 2 - t := by
        have h := Real.sin_le (show (0:ℝ) ≤ Real.pi / 2 - t by linarith)
        rwa [Real.sin_pi_div_two_sub] at h
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hθ.1, ht.1], by linarith [ht1]⟩
      have hs1 : Real.sin t ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
      have hδnn : 0 ≤ Real.pi / 2 - t := by linarith
      rw [wfun]
      have hcube : Real.cos t ^ 3 ≤ (Real.pi / 2 - t) ^ 3 := pow_le_pow_left₀ hcosnn hcos 3
      have := mul_le_mul hs1 hcube (by positivity) (by norm_num : (0:ℝ) ≤ 1)
      linarith
  have hftc : ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 3 = (Real.pi / 2 - θ) ^ 4 / 4 := by
    have hd : ∀ t ∈ Set.uIcc θ (Real.pi / 2),
        HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 4 / 4) ((Real.pi / 2 - t) ^ 3) t := by
      intro t ht
      have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
      have h3 := hinner.pow 4
      have h4 : HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 4 / 4)
          (-(4 * (Real.pi / 2 - t) ^ (4 - 1) * (-1)) / 4) t := h3.neg.div_const 4
      convert h4 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 3).intervalIntegrable
        θ (Real.pi / 2))]
    ring
  linarith [hftc ▸ hle]

lemma Wint4 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t) ≤ (Real.pi / 2 - θ) ^ 3 / 6 := by
  have hcont1 : Continuous (fun t : ℝ => wfun t / Real.sin (2 * t)) := by
    have h : (fun t : ℝ => wfun t / Real.sin (2 * t))
        = fun t => Real.sin t * Real.cos t ^ 2 / 2 := by
      funext t; exact wfun_div_s2_eq t
    rw [h]; fun_prop
  have hle : ∫ t in θ..(Real.pi / 2), wfun t / Real.sin (2 * t)
      ≤ ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 2 / 2 := by
    refine intervalIntegral.integral_mono_on hθ.2.le
      (hcont1.intervalIntegrable θ (Real.pi / 2)) ?_
      (fun t ht => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 2 / 2).intervalIntegrable
        θ (Real.pi / 2)
    · rw [wfun_div_s2_eq]
      have ht1 : t ≤ Real.pi / 2 := ht.2
      have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
      have hcos : Real.cos t ≤ Real.pi / 2 - t := by
        have h := Real.sin_le (show (0:ℝ) ≤ Real.pi / 2 - t by linarith [ht.2])
        rwa [Real.sin_pi_div_two_sub] at h
      have hcosnn : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hθ.1, ht.1], by linarith [ht1]⟩
      have hδnn : 0 ≤ Real.pi / 2 - t := by linarith
      have hsq : Real.cos t ^ 2 ≤ (Real.pi / 2 - t) ^ 2 := by
        nlinarith [hcos, hcosnn, hδnn]
      have := mul_le_mul hsin1 hsq (by positivity) (by norm_num : (0:ℝ) ≤ 1)
      linarith
  have hftc : ∫ t in θ..(Real.pi / 2), (Real.pi / 2 - t) ^ 2 / 2 = (Real.pi / 2 - θ) ^ 3 / 6 := by
    have hd : ∀ t ∈ Set.uIcc θ (Real.pi / 2),
        HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 3 / 6) ((Real.pi / 2 - t) ^ 2 / 2) t := by
      intro t ht
      have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
      have h3 := hinner.pow 3
      have h4 : HasDerivAt (fun s : ℝ => -(Real.pi / 2 - s) ^ 3 / 6)
          (-(3 * (Real.pi / 2 - t) ^ (3 - 1) * (-1)) / 6) t := h3.neg.div_const 6
      convert h4 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (Real.pi / 2 - t) ^ 2 / 2).intervalIntegrable
        θ (Real.pi / 2))]
    ring
  linarith [hftc ▸ hle]

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.rates_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.rates_aux` — the weight comparisons and the `oddPerS` glue

Two groups of helpers for `sb6_rates`:

* the comparisons between the weights `(1+w)^{-k}`, `(L/w)^k` and `w^{-(k+1)}` which convert the
  compact bounds (`w ≤ L`) and the far-field bounds (`L ≤ w`) into the single weight
  `(1+w)^{-k}` of the statement;
* the agreement of `Φ = oddPerS (psiP)`, extended by `0` at `w ≤ 0`, with `psiP` on the open
  quadrant, together with the rewriting of `∂_wΦ` and `∂_θΦ` as the corresponding derivatives of
  `psiP`, and the two boundary cases `w = 0` and `θ = 0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-! ## §1 Weight comparisons -/

/-- For `0 ≤ w ≤ L` and `0 ≤ k`: `(1+L)^{-k} ≤ (1+w)^{-k}`. -/
lemma one_add_rpow_neg_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw0 : 0 ≤ w) (hw : w ≤ L) :
    (1 + L) ^ (-k) ≤ (1 + w) ^ (-k) := by
  have h1 : (0 : ℝ) ≤ 1 + w := by linarith
  have h2 : (0 : ℝ) < 1 + L := by linarith
  rw [Real.rpow_neg h1 k, Real.rpow_neg (le_of_lt h2) k]
  have h3 : (1 + w) ^ k ≤ (1 + L) ^ k := Real.rpow_le_rpow h1 (by linarith) hk
  have h4 := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 + w) k) h3
  simpa only [one_div] using h4

/-- For `L ≤ w` and `0 ≤ k`: `(L/w)^k ≤ (1+L)^k (1+w)^{-k}`. -/
lemma div_rpow_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    (L / w) ^ k ≤ (1 + L) ^ k * (1 + w) ^ (-k) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have h1L : (0 : ℝ) < 1 + L := by linarith
  have h1 : L / w ≤ (1 + L) / (1 + w) := by
    rw [div_le_iff₀ hw0]
    have he : (1 + L) / (1 + w) * w = (1 + L) * w / (1 + w) := by ring
    rw [he, le_div_iff₀ h1w]
    linarith
  have h2 : (L / w) ^ k ≤ ((1 + L) / (1 + w)) ^ k :=
    Real.rpow_le_rpow (by positivity) h1 hk
  have he : ((1 + L) / (1 + w)) ^ k = (1 + L) ^ k * (1 + w) ^ (-k) := by
    rw [Real.div_rpow (le_of_lt h1L) (le_of_lt h1w), Real.rpow_neg (le_of_lt h1w) k,
      div_eq_mul_inv]
  rwa [he] at h2

/-- For `L ≤ w` (with `L > 0`) and `0 ≤ k`: `w^{-(k+1)} ≤ (1+1/L)^{k+1} (1+w)^{-(k+1)}`. -/
lemma rpow_neg_succ_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    w ^ (-(k + 1)) ≤ (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hp : (0 : ℝ) < 1 + 1 / L := by positivity
  have h3 : (1 : ℝ) ≤ w / L := by
    rw [le_div_iff₀ hL]; linarith
  have h4 : (1 + 1 / L) * w = w + w / L := by ring
  have h2 : 1 / w ≤ (1 + 1 / L) / (1 + w) := by
    rw [div_le_iff₀ hw0]
    have he : (1 + 1 / L) / (1 + w) * w = (1 + 1 / L) * w / (1 + w) := by ring
    rw [he, le_div_iff₀ h1w]
    nlinarith [h3, h4]
  have h5 : (1 / w) ^ (k + 1) ≤ ((1 + 1 / L) / (1 + w)) ^ (k + 1) :=
    Real.rpow_le_rpow (by positivity) h2 (by linarith)
  have hw1 : w ^ (-(k + 1)) = (1 / w) ^ (k + 1) := by
    rw [Real.rpow_neg (le_of_lt hw0) (k + 1), one_div,
      Real.inv_rpow (le_of_lt hw0) (k + 1)]
  have he : ((1 + 1 / L) / (1 + w)) ^ (k + 1)
      = (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
    rw [Real.div_rpow (le_of_lt hp) (le_of_lt h1w), Real.rpow_neg (le_of_lt h1w) (k + 1),
      div_eq_mul_inv]
  rw [hw1]
  rwa [he] at h5

/-- For `L ≤ w` (with `L > 0`) and `0 ≤ k`:
`(L/w)^k / w ≤ L^k · (1+1/L)^{k+1} · (1+w)^{-(k+1)}` — the extra inverse power `1/w` of the
`w`-derivative is absorbed into the `(1+w)^{-(k+1)}`-weight at the cost of the factor
`(1+1/L)^{k+1}`. -/
lemma div_rpow_succ_le {w L k : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hw : L ≤ w) :
    (L / w) ^ k / w ≤ L ^ k * (1 + 1 / L) ^ (k + 1) * (1 + w) ^ (-(k + 1)) := by
  have hw0 : 0 < w := lt_of_lt_of_le hL hw
  have h1 : (L / w) ^ k / w = L ^ k * w ^ (-(k + 1)) := by
    have hsplit : w ^ (k + 1) = w ^ k * w := by
      rw [Real.rpow_add hw0 k 1, Real.rpow_one]
    rw [Real.div_rpow (le_of_lt hL) (le_of_lt hw0), div_div, ← hsplit,
      Real.rpow_neg (le_of_lt hw0) (k + 1), div_eq_mul_inv]
  rw [h1, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rpow_neg_succ_le hL hk hw)
    (Real.rpow_nonneg (le_of_lt hL) k)

/-! ## §2 The `oddPerS` glue -/

/-- On the open quadrant, `Φ w θ = psiP w θ` (for `w > 0`). -/
lemma Phi_eq_of_pos {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ ≤ Real.pi / 2) :
    (if 0 < w then oddPerS P w θ else 0) = P w θ := by
  rw [ite_eq_left hw]
  exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces P hP).2.1 w θ hθ hθ2

/-- On the axis, `Φ w 0 = 0`. -/
lemma Phi_zero_theta {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w : ℝ} :
    (if 0 < w then oddPerS P w 0 else 0) = 0 := by
  by_cases hw : 0 < w
  · rw [ite_eq_left hw]
    exact (Work.FTS_StreamBdry.SB25.oddPerS_pieces P hP).2.2.2.2 w
  · rw [ite_eq_right hw]

/-- At `w ≤ 0`, `Φ w θ = 0`. -/
lemma Phi_eq_zero_of_nonpos {P : ℝ → ℝ → ℝ} {w θ : ℝ} (hw : ¬ 0 < w) :
    (if 0 < w then oddPerS P w θ else 0) = 0 := ite_eq_right hw

/-- The `w`-derivative of `Φ` is that of `psiP` in the open quadrant. -/
lemma Phi_deriv_w {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    deriv (fun w' : ℝ => (if 0 < w' then oddPerS P w' θ else 0)) w
      = deriv (fun w' : ℝ => P w' θ) w := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
  exact Phi_eq_of_pos hP hw' hθ (le_of_lt hθ2)

/-- The `θ`-derivative of `Φ` is that of `psiP` in the open quadrant. -/
lemma Phi_deriv_theta {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w θ : ℝ}
    (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) θ
      = deriv (fun θ' : ℝ => P w θ') θ := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩] with θ' hθ'
  exact Phi_eq_of_pos hP hw hθ'.1 (le_of_lt hθ'.2)


/-- **Left-vanishing pins the derivative at `0` to `0`**: if `f` is differentiable at `0` and
`f` vanishes on `(-∞, 0)`, then `deriv f 0 = 0`. -/
lemma deriv_eq_zero_of_left_eq_zero {f : ℝ → ℝ} (hd : DifferentiableAt ℝ f 0)
    (h : ∀ y, y < 0 → f y = 0) (h0 : f 0 = 0) : deriv f 0 = 0 := by
  have h2 : Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) (𝓝[<] (0:ℝ))
      (𝓝 (deriv f 0)) := hd.hasDerivAt.tendsto_slope_zero_left
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] (0:ℝ)]
      (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hft : f (0 + t) = 0 := by simpa using h t ht
    show (0 : ℝ) = t⁻¹ * (f (0 + t) - f 0)
    rw [hft, h0, sub_self, mul_zero]
  have h3 : Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (0 + t) - f 0)) (𝓝[<] (0:ℝ)) (𝓝 0) :=
    Tendsto.congr' hev tendsto_const_nhds
  exact tendsto_nhds_unique h2 h3

/-- **The derivative of `Φ w ·` at `0`** is bounded by any bound on the difference quotient
`P w t / t` for `t → 0⁺`. -/
lemma deriv_theta_zero_le' {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w B : ℝ}
    (hw : 0 < w)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 → |P w t / t| ≤ B)
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0| ≤ B := by
  have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ *
      ((fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) (0 + t)
        - (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0)) :=
    hd.hasDerivAt.tendsto_slope_zero_right
  have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < Real.pi / 2 :=
    nhdsWithin_le_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
  have hev : (fun t : ℝ => t⁻¹ *
      ((fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) (0 + t)
        - (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun t : ℝ => P w t / t) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 htπ
    have ht0' : (0 : ℝ) < t := ht0
    have h1 : (if 0 < w then oddPerS P w (0 + t) else 0) = P w (0 + t) := by
      rw [zero_add]
      exact Phi_eq_of_pos hP hw ht0' (le_of_lt htπ)
    have h0 : (if 0 < w then oddPerS P w 0 else 0) = 0 := Phi_zero_theta hP
    rw [h1, h0, zero_add, sub_zero, div_eq_mul_inv]
    ring
  have hbd : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), |P w t / t| ≤ B := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 htπ
    have ht0' : (0 : ℝ) < t := ht0
    exact hb t ht0' htπ
  exact le_of_tendsto (hslope.congr' hev).abs hbd

/-- **The derivative of `Φ w ·` at `0`**: if it exists, it is the right difference quotient
`P w t / t` at `t → 0⁺`, hence bounded by `2M` when `|P w t| ≤ M sin 2t`. -/
lemma deriv_theta_zero_le {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0) {w M : ℝ}
    (hw : 0 < w) (hM : 0 ≤ M)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 → |P w t| ≤ M * Work.Construction.s2 t)
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0| ≤ 2 * M := by
  refine deriv_theta_zero_le' hP hw ?_ hd
  intro t ht0 htπ
  have ht0' : (0 : ℝ) < t := ht0
  have h2 : Work.Construction.s2 t / t ≤ 2 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul, div_le_iff₀ ht0']
    nlinarith [Real.sin_le (le_of_lt ht0'), Real.cos_le_one t,
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt ht0', by linarith [htπ, Real.pi_pos]⟩]
  calc |P w t / t| ≤ M * Work.Construction.s2 t / t := by
        rw [abs_div]
        simp only [abs_of_pos ht0']
        exact div_le_div_of_nonneg_right (hb t ht0 htπ) (le_of_lt ht0')
    _ = M * (Work.Construction.s2 t / t) := by ring
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left h2 hM
    _ = 2 * M := by ring

/-- The same with the far-field weight. -/
lemma deriv_theta_zero_le_far {P : ℝ → ℝ → ℝ} (hP : ∀ z, P z (Real.pi / 2) = 0)
    {αG L w Kf : ℝ} (hL : 0 < L) (hwL : L ≤ w) (hKf0 : 0 ≤ Kf)
    (hb : ∀ t, 0 < t → t < Real.pi / 2 →
      |P w t| ≤ Kf * Work.Construction.s2 t * (L / w) ^ (4 / αG))
    (hd : DifferentiableAt ℝ (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0) :
    |deriv (fun θ' : ℝ => (if 0 < w then oddPerS P w θ' else 0)) 0|
      ≤ 2 * Kf * (L / w) ^ (4 / αG) := by
  have hw : 0 < w := lt_of_lt_of_le hL hwL
  refine deriv_theta_zero_le' hP hw ?_ hd
  intro t ht0 htπ
  have ht0' : (0 : ℝ) < t := ht0
  have h2 : Work.Construction.s2 t / t ≤ 2 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul, div_le_iff₀ ht0']
    nlinarith [Real.sin_le (le_of_lt ht0'), Real.cos_le_one t,
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt ht0', by linarith [htπ, Real.pi_pos]⟩]
  calc |P w t / t| ≤ Kf * Work.Construction.s2 t * (L / w) ^ (4 / αG) / t := by
        rw [abs_div]
        simp only [abs_of_pos ht0']
        exact div_le_div_of_nonneg_right (hb t ht0 htπ) (le_of_lt ht0')
    _ = Kf * (L / w) ^ (4 / αG) * (Work.Construction.s2 t / t) := by ring
    _ ≤ Kf * (L / w) ^ (4 / αG) * 2 :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hKf0 (Real.rpow_nonneg (by positivity) _))
    _ = 2 * Kf * (L / w) ^ (4 / αG) := by ring

end Work.FTS_StreamBdry.SB6
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SBpsiP.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.Assembly` — `|D_z^j psiP| ≤ M·sin 2θ`, assembled

The target `Work.FTS_StreamBdry.PsiPDzLe αG M Ψ` says that the `U`-slot part of the stream
function satisfies `|D_z^j (psiP αG Ψ)| ≤ M·sin 2θ` on the open quadrant, for `j ≤ 2`, under
the slot bound `SlotBd αG Ψ M` (`|D_z^j U'(Ψ)| ≤ M`, `j ≤ 2`) and `Ψ ∈ C³`.

Since `psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` *definitionally* (`c = 3/αG - 1`, `J` the scaled
parameter integral of `SB3/DzJDefs`), everything follows from the chain

  `D_z^j (psiP αG Ψ) = -(s2 θ/αG)·J c (D_z^j U'(Ψ))`   (`j ≤ 2`),

obtained by applying the differentiation identity `SBpsiP.J_Dz_eq` first to `h = U'(Ψ)` and
then to `h = D_z U'(Ψ)` (each application gives both the identity and the differentiability
of the slice which the next one needs), and from the integral bound

  `|J c h z θ| ≤ M·(αG/3)`   whenever `|h| ≤ M` and `c + 1 = 3/αG`.

This file is stated *conditionally* on those two ingredients (`hsm`, `hbd`), so that the
crux analysis (`J_Dz_eq`, proved in `SBpsiP/DzJ_crux`) is separated from the finite-order
smoothness of the slot iterates and the elementary integral bound; the target file
`SB3/psiP_DzLe` discharges the two hypotheses.
-/

noncomputable section
open scoped Real Topology Interval
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `C¹` on the open quadrant implies differentiability of the `z`-slices. -/
lemma slice_diff_of_contDiffOn_one {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 1 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd'.mem_nhds hp))

/-- `C²` on the open quadrant implies differentiability of the `z`-slices. -/
lemma slice_diff_of_contDiffOn_two {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Work.Construction.Qd)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => F z' p.2) p.1 :=
  Work.Spaces.differentiableAt_curry_left
    ((h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd'.mem_nhds hp))

/-- The `θ`-only multiple rule for `D_z`. -/
lemma Dz_theta_mul {a : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    Work.Spaces.Dz (fun z θ => a θ * F z θ) z θ = a θ * Work.Spaces.Dz F z θ := by
  have hfun : (fun z' : ℝ => a θ * F z' θ)
      = (fun z' : ℝ => a θ * (fun z'' : ℝ => F z'' θ) z') := rfl
  show z * deriv (fun z' : ℝ => a θ * F z' θ) z = a θ * (z * deriv (fun z' => F z' θ) z)
  rw [hfun, deriv_const_mul _ hd]
  ring

/-- **`|D_z^j psiP| ≤ M·sin 2θ` from the two ingredients.**  `hsm` is the finite-order
smoothness of the slot iterates (`D_z^j U'(Ψ) ∈ C^{2-j}` on the quadrant) and `hbd` the
elementary scaled-integral bound. -/
theorem psiP_DzLe_of_pieces
    (hsm : ∀ (αG : ℝ), 0 < αG → ∀ (Ψ : ℝ → ℝ → ℝ),
      ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd →
      ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
        (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd)
    (hbd : ∀ (c B : ℝ), -1 < c → 0 ≤ B → ∀ (φ : ℝ → ℝ),
      ContinuousOn φ (Set.Ioc (0 : ℝ) 1) → (∀ v ∈ Set.Ioc (0 : ℝ) 1, |φ v| ≤ B) →
      |∫ v in (0 : ℝ)..1, v ^ c * φ v| ≤ B / (c + 1))
    {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPDzLe αG M Ψ := by
  intro z θ hmem j hj
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hs2nn : 0 ≤ Work.Construction.s2 θ :=
    le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hαGne : αG ≠ 0 := ne_of_gt hαG
  -- `M ≥ 0`
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot h1)
  have hc : (-1 : ℝ) < 3 / αG - 1 := by
    have h3pos : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  -- continuity and bounds for the iterates of the slot
  have hcont_all : ∀ i : ℕ, i ≤ 2 → ContinuousOn
      (Function.uncurry (Work.Spaces.DzIter i (Uprime αG Ψ))) Work.Construction.Qd :=
    fun i hi => (hsm αG hαG Ψ h3 i hi).continuousOn
  have hbnd_all : ∀ i : ℕ, i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter i (Uprime αG Ψ) z θ| ≤ M :=
    fun i hi z θ hzθ => SlotBd.Dz_le hslot hzθ hi
  -- the pointwise identity at level 0
  have hbase : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG)
        * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ := by
    intro z θ hzθ
    rw [Work.FTS_StreamBdry.psiP_eq_Iint, Work.FTS_StreamBdry.SB3.Iint_eq_J]
  -- the identity at level 1
  have h1pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := J_Dz_eq (c := 3 / αG - 1) hc
      (h := Uprime αG Ψ)
      (hcont_all 0 (by norm_num)) (hcont_all 1 (by norm_num))
      (fun z θ hzθ => slice_diff_of_contDiffOn_two hzθ
        (by simpa using hsm αG hαG Ψ h3 0 (by norm_num)))
      (fun z θ hzθ => hbnd_all 0 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hbnd_all 1 (by norm_num) z θ hzθ) z θ hzθ
    have hcongr : Work.Spaces.pz (psiP αG Ψ) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen isOpen_Qd'
        (fun q hq => by
          show Function.uncurry (psiP αG Ψ) q = Function.uncurry (fun z θ =>
            -(Work.Construction.s2 θ / αG)
              * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) q
          simpa only [Function.uncurry] using hbase q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (psiP αG Ψ) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ := by
      show z * Work.Spaces.pz (psiP αG Ψ) z θ = z * Work.Spaces.pz (fun z θ =>
        -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1) (Uprime αG Ψ) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ := by
      rw [Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 0 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ
    rw [Work.Spaces.DzIter_zero, hDz, hval]
  -- the identity at level 2
  have h2pt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
    intro z θ hzθ
    have hJ := J_Dz_eq (c := 3 / αG - 1) hc
      (h := Work.Spaces.DzIter 1 (Uprime αG Ψ))
      (hcont_all 1 (by norm_num)) (hcont_all 2 (by norm_num))
      (fun z θ hzθ => slice_diff_of_contDiffOn_one hzθ
        ((hsm αG hαG Ψ h3 1 (by norm_num)).of_le (by decide)))
      (fun z θ hzθ => hbnd_all 1 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hbnd_all 2 (by norm_num) z θ hzθ) z θ hzθ
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ :=
      Work.Spaces.pz_congr_of_isOpen isOpen_Qd'
        (fun q hq => by
          show Function.uncurry (Work.Spaces.DzIter 1 (psiP αG Ψ)) q
            = Function.uncurry (fun z θ => -(Work.Construction.s2 θ / αG)
                * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                    (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) q
          simpa only [Function.uncurry] using h1pt q.1 q.2 hq) hzθ
    have hDz : Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ := by
      show z * Work.Spaces.pz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
        = z * Work.Spaces.pz (fun z θ => -(Work.Construction.s2 θ / αG)
            * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
                (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
      rw [hcongr]
    have hval : Work.Spaces.Dz (fun z θ => -(Work.Construction.s2 θ / αG)
          * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
              (Work.Spaces.DzIter 1 (Uprime αG Ψ)) z θ) z θ
        = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
            (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ := by
      rw [Dz_theta_mul (a := fun θ => -(Work.Construction.s2 θ / αG)) hJ.1, hJ.2]
      rfl
    change Work.Spaces.Dz (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter 2 (Uprime αG Ψ)) z θ
    rw [hDz, hval]
  -- the identity at the given `j`
  have hident : Work.Spaces.DzIter j (psiP αG Ψ) z θ
      = -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
          (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simpa only [Work.Spaces.DzIter_zero] using hbase z θ hmem
    · exact h1pt z θ hmem
    · exact h2pt z θ hmem
  -- the integral bound
  have hJb : |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
      (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ| ≤ M * (αG / 3) := by
    have hφcont : ContinuousOn
        (fun v : ℝ => Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ)
        (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (z * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := (hcont_all j hj).comp hlin (fun v hv => ⟨mul_pos hz hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    have hφbd : ∀ v ∈ Set.Ioc (0 : ℝ) 1,
        |Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ| ≤ M :=
      fun v hv => hbnd_all j hj (z * v) θ ⟨mul_pos hz hv.1, hθ0, hθ1⟩
    have hmain := hbd (3 / αG - 1) M hc hM
      (fun v : ℝ => Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ) hφcont hφbd
    have hsimp : M / (3 / αG - 1 + 1) = M * (αG / 3) := by
      rw [show (3 / αG - 1 + 1 : ℝ) = 3 / αG by ring, div_eq_mul_inv, inv_div]
    simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hmain.trans_eq hsimp
  -- absolute values
  have hAa : |-(Work.Construction.s2 θ / αG)| = Work.Construction.s2 θ / αG := by
    rw [abs_neg, abs_of_nonneg (div_nonneg hs2nn (le_of_lt hαG))]
  rw [hident, abs_mul, hAa]
  have hstep : (Work.Construction.s2 θ / αG) * |Work.FTS_StreamBdry.SB3.J (3 / αG - 1)
        (Work.Spaces.DzIter j (Uprime αG Ψ)) z θ|
      ≤ (Work.Construction.s2 θ / αG) * (M * (αG / 3)) :=
    mul_le_mul_of_nonneg_left hJb (div_nonneg hs2nn (le_of_lt hαG))
  have hstep2 : (Work.Construction.s2 θ / αG) * (M * (αG / 3))
      = M * Work.Construction.s2 θ / 3 := by
    field_simp
  have hstep3 : M * Work.Construction.s2 θ / 3 ≤ M * Work.Construction.s2 θ := by
    nlinarith [hM, hs2nn]
  linarith [hstep, hstep2, hstep3]

end Work.FTS_StreamBdry.SBpsiP
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.sb1_gauge_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb1_gauge_proved` — the frozen SB1′ producer `StreamBdryIface.sb1_gauge`

Every `C³` stream function on the open quadrant whose `U`-slot is bounded (`SlotBd`) differs from
the particular solution `psiP` by a multiple of the gauge mode `gaugeMode αG = z^{-3/αG}/cos θ`.
No growth hypothesis is needed (FIX-A): the constant of integration is pinned by the boundedness of
`V(psiP)` at `z → 0⁺` (`SB1.psiP_Vop_bnd`), which is what makes the `θ`-ODE `c' = tan θ·c` hold.

Assembled in `SB1/Engine.lean` (`SB1.sb1_gauge_of_parts`) from the three engine lemmas
`SB1.psiP_ode`, `SB1.psiP_diff`, `SB1.psiP_Vop_bnd`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd gaugeMode psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB1′ proved** (frozen type `sb1_gauge`): the gauge decomposition, with no growth hypothesis. -/
theorem sb1_gauge_proved {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Ψ z θ = psiP αG Ψ z θ + κ * gaugeMode αG z θ :=
  SB1.sb1_gauge_of_parts hαG h3 hslot (SB1.psiP_ode hαG h3 hslot)
    (SB1.psiP_diff hαG h3 hslot) (SB1.psiP_Vop_bnd hαG h3 hslot)

end Work.FTS_StreamBdry
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.sb5_barrier_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb5_barrier_proved` — the frozen SB5 sub-leaf `StreamBdryIface.sb5_barrier`

The FIX-SB5 barrier exists: the explicit `phiB θ = 1/(4 sin θ) + 1/(16(1-sin θ)) + 3/(16(1+sin θ))
- (3/16)log(1-sin θ) - (9/16)log(1+sin θ) + 1` is `C²` on `(0,π/2)`, nonnegative there, blows up at
both ends, and satisfies `𝓐 phiB = -15/4` exactly, where `𝓐φ = -φ'' - (4cot 2θ - tan θ)φ'`.
Hence `SB5Barrier` holds with `Cφ = 15/4` (see `SB25/phiB_barrier`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SB5Barrier)

set_option autoImplicit false

/-- **SB5 sub-leaf, proved**: the barrier of FIX-SB5 exists (frozen type `SB5Barrier`). -/
theorem sb5_barrier_proved : SB5Barrier := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Work.FTS_StreamBdry.SB25.phiB_barrier
  exact ⟨Work.FTS_StreamBdry.SB25.phiB, 15 / 4, h1, h2, h3, h4,
    fun θ hθ => by rw [h5 θ hθ]⟩

end Work.FTS_StreamBdry
end
end
