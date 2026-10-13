import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.glue_line_C1

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
