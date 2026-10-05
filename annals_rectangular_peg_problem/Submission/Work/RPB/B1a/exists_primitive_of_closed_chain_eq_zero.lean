import Mathlib
import Submission.Work.RPB.B1a.SegChain
import Submission.Work.RPB.B1a.exists_chain_of_isOpen_of_isPreconnected

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

/-! ## Reversing a segment changes the sign of its integral -/

lemma segIntegral_antisymm (f : ℂ → ℂ) (a b : ℂ) :
    segIntegral f b a = -segIntegral f a b := by
  simp only [segIntegral]
  have hsub : (∫ t in (0 : ℝ)..1, f (b + (t : ℂ) * (a - b)) * (a - b))
      = ∫ t in (0 : ℝ)..1, f (b + ((1 : ℝ) - t : ℂ) * (a - b)) * (a - b) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun x : ℝ => f (b + ((1 : ℝ) - x : ℂ) * (a - b)) * (a - b)) (1 : ℝ)
    simpa using h
  rw [hsub]
  have hpoint : (fun t : ℝ => f (b + ((1 : ℝ) - t : ℂ) * (a - b)) * (a - b))
      = fun t : ℝ => -(f (a + (t : ℂ) * (b - a)) * (b - a)) := by
    funext t
    have harg : b + ((1 : ℝ) - t : ℂ) * (a - b) = a + (t : ℂ) * (b - a) := by
      push_cast; ring
    rw [harg]; ring
  rw [hpoint, intervalIntegral.integral_neg]

/-! ## The integral along a reversed chain is the negative integral -/

lemma chainIntegral_chainRev (f : ℂ → ℂ) (L : List (ℂ × ℂ)) :
    chainIntegral f (chainRev L) = -chainIntegral f L := by
  induction L with
  | nil => simp [chainRev, chainIntegral]
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    rw [chainRev_cons, chainIntegral_append, chainIntegral_singleton, ih, chainIntegral_cons,
      segIntegral_antisymm]
    ring

/-! ## Path-independence of the chain integral -/

/-- If the integral of `f` along every closed polygonal chain in `U` vanishes, then the integral
along a chain in `U` only depends on its endpoints. -/
lemma chainIntegral_eq_of_isChainFrom {U : Set ℂ} {f : ℂ → ℂ}
    (hclosed : ∀ (p : ℂ) (L : List (ℂ × ℂ)), IsChainFrom p p L → ChainIn U L →
      chainIntegral f L = 0)
    {p q : ℂ} {L₁ L₂ : List (ℂ × ℂ)} (h₁ : IsChainFrom p q L₁) (h₂ : IsChainFrom p q L₂)
    (c₁ : ChainIn U L₁) (c₂ : ChainIn U L₂) :
    chainIntegral f L₁ = chainIntegral f L₂ := by
  have hM : IsChainFrom p p (L₁ ++ chainRev L₂) :=
    IsChainFrom.append h₁ (IsChainFrom.reverse h₂)
  have cM : ChainIn U (L₁ ++ chainRev L₂) := ChainIn.append c₁ (ChainIn.reverse c₂)
  have h0 := hclosed p (L₁ ++ chainRev L₂) hM cM
  rw [chainIntegral_append, chainIntegral_chainRev] at h0
  have : chainIntegral f L₁ + -chainIntegral f L₂ = 0 := h0
  have := add_eq_zero_iff_eq_neg.mp this
  simpa using this

/-! ## Existence of a primitive -/

/-- **A holomorphic function on an open connected set whose integral along every closed polygonal
chain vanishes has a primitive.**  The pointwise construction is
`g z = ∫ f` along any polygonal chain from a fixed base point to `z`; closedness of the chain
integral makes it independent of the chosen chain, and the local Morera theorem
(`DifferentiableOn.isExactOn_ball`) supplies a local primitive on a ball inside `U`, which differs
from `g` by a constant. -/
theorem exists_primitive_of_closed_chain_eq_zero (U : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U)
    (hclosed : ∀ (p : ℂ) (L : List (ℂ × ℂ)), IsChainFrom p p L → ChainIn U L →
      chainIntegral f L = 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U := by
  classical
  obtain ⟨p₀, hp₀⟩ := hUc.nonempty
  have hchain : ∀ z ∈ U, ∃ L : List (ℂ × ℂ), IsChainFrom p₀ z L ∧ ChainIn U L :=
    fun z hz => exists_chain_of_isOpen_of_isPreconnected U hUo hUc hp₀ hz
  let LOf : ℂ → List (ℂ × ℂ) := fun z => if hz : z ∈ U then (hchain z hz).choose else []
  have hLOf : ∀ z (hz : z ∈ U), IsChainFrom p₀ z (LOf z) ∧ ChainIn U (LOf z) := by
    intro z hz
    have h : LOf z = (hchain z hz).choose := by
      simp only [LOf]
      exact dite_eq_left hz
    rw [h]
    exact (hchain z hz).choose_spec
  let g : ℂ → ℂ := fun z => chainIntegral f (LOf z)
  have hg_def : ∀ z, g z = chainIntegral f (LOf z) := fun z => rfl
  have hderiv : ∀ z₀ ∈ U, HasDerivAt g (f z₀) z₀ := by
    intro z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀
    obtain ⟨G, hG⟩ := DifferentiableOn.isExactOn_ball (c := z₀) (r := ε) (hfd.mono hball)
    have hGz₀ : HasDerivAt G (f z₀) z₀ := hG z₀ (Metric.mem_ball_self hε)
    have hEv : g =ᶠ[𝓝 z₀] fun z => G z + (g z₀ - G z₀) := by
      filter_upwards [Metric.ball_mem_nhds z₀ hε] with z hz
      have hzU : z ∈ U := hball hz
      have hsegball : segment ℝ z₀ z ⊆ Metric.ball z₀ ε :=
        Convex.segment_subset (convex_ball z₀ ε) (Metric.mem_ball_self hε) hz
      have hsegU : segment ℝ z₀ z ⊆ U := hsegball.trans hball
      have hc1' : IsChainFrom p₀ z (LOf z₀ ++ [(z₀, z)]) :=
        IsChainFrom.append (hLOf z₀ hz₀).1 (by simp [IsChainFrom])
      have hc2' : ChainIn U (LOf z₀ ++ [(z₀, z)]) :=
        ChainIn.append (hLOf z₀ hz₀).2 (by
          intro s hs
          obtain rfl := List.mem_singleton.mp hs
          exact ⟨hz₀, hzU, hsegU⟩)
      have e1 : chainIntegral f (LOf z) = chainIntegral f (LOf z₀ ++ [(z₀, z)]) :=
        chainIntegral_eq_of_isChainFrom hclosed (hLOf z hzU).1 hc1' (hLOf z hzU).2 hc2'
      have e2 : segIntegral f z₀ z = G z - G z₀ := by
        refine segIntegral_eq_sub_of_hasDerivAt (F := G) ?_ ?_
        · intro t ht
          exact hG _ (hsegball (mem_segment_param ht))
        · exact hfd.continuousOn.mono hsegU
      have e3 : g z - g z₀ = segIntegral f z₀ z := by
        change chainIntegral f (LOf z) - chainIntegral f (LOf z₀) = segIntegral f z₀ z
        rw [e1, chainIntegral_append, chainIntegral_singleton]
        ring
      have h1 : g z - g z₀ = G z - G z₀ := by rw [e3, e2]
      have h2 : G z + (g z₀ - G z₀) = (g z - g z₀) + g z₀ := by rw [h1]; ring
      rw [h2, sub_add_cancel]
    exact hEv.hasDerivAt_iff.mpr (hGz₀.add_const (g z₀ - G z₀))
  refine ⟨g, fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, ?_⟩
  intro z hz
  exact (hderiv z hz).deriv

end

end Work.RPB.B1a
