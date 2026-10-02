import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- If every point lies in a flow box of time `ε`, then the global flow `Φ` is jointly continuous on
the strip `Ioo (-ε) ε × M`: each point of the strip lies in a flow box, where `Φ` agrees with the box
map by uniqueness of integral curves. -/
theorem flow_continuous_strip {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)))
    {ε : ℝ} (hε : 0 < ε)
    (hbox : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ Ψ : ℝ → M → M, IsFlowBox v ε U Ψ)
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x) (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v) :
    ContinuousOn (Function.uncurry Φ) (Set.Ioo (-ε) ε ×ˢ Set.univ) := by
  intro p hp
  rcases p with ⟨t₀, x₀⟩
  rw [Set.mem_prod] at hp
  obtain ⟨ht₀, -⟩ := hp
  obtain ⟨U, hUopen, hx₀U, Ψ, hbox⟩ := hbox x₀
  -- the flow box `U` at `x₀`, with its box map `Ψ`
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  -- `Φ` and the box map `Ψ` agree on the strip for points of `U`, by uniqueness of integral curves
  have heq : ∀ (s : ℝ) (x : M), s ∈ Set.Ioo (-ε) ε → x ∈ U → Φ s x = Ψ s x := by
    intro s x hs hx
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht0 hv
      ((hΦ x).isMIntegralCurveOn _) ((hbox.2 x hx).2)
      ((h0 x).trans ((hbox.2 x hx).1).symm) hs
  have hnbd : Set.Ioo (-ε) ε ×ˢ U ∈ 𝓝 (t₀, x₀) :=
    (isOpen_Ioo.prod hUopen).mem_nhds ⟨ht₀, hx₀U⟩
  have hΨcont : ContinuousOn (Function.uncurry Ψ) (Set.Ioo (-ε) ε ×ˢ U) := hbox.1
  have hev : Function.uncurry Φ =ᶠ[𝓝 (t₀, x₀)] Function.uncurry Ψ := by
    filter_upwards [hnbd] with q hq
    rcases q with ⟨s, x⟩
    rw [Set.mem_prod] at hq
    exact heq s x hq.1 hq.2
  exact ((hΨcont.continuousAt hnbd).congr hev.symm).continuousWithinAt

end Work.Morse
