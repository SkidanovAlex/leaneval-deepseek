import Mathlib

namespace Work.NN.Core.TelTwoDF

/-- **Hölder continuity passes to the closure.**

If `f` is continuous and `K`-Hölder of exponent `α > 0` on a set `Ω`, then the same bound holds on
the closure of `Ω`: approximate `x, y ∈ closure Ω` by points of `Ω` and pass to the limit in
`‖f xₙ - f yₙ‖ ≤ K ‖xₙ - yₙ‖ ^ α`. -/
theorem holder_norm_sub_le_closure {X V : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup V] {f : X → V} {Ω : Set X} {K α : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hf : Continuous f)
    (h : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    {x y : X} (hx : x ∈ closure Ω) (hy : y ∈ closure Ω) :
    ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α := by
  have hfst : Continuous fun p : X × X => f p.1 := hf.comp continuous_fst
  have hsnd : Continuous fun p : X × X => f p.2 := hf.comp continuous_snd
  have hnorm : Continuous fun p : X × X => ‖f p.1 - f p.2‖ := (hfst.sub hsnd).norm
  have hnorm2 : Continuous fun p : X × X => ‖p.1 - p.2‖ :=
    (continuous_fst.sub continuous_snd).norm
  have hrpow : Continuous fun p : X × X => K * ‖p.1 - p.2‖ ^ α :=
    continuous_const.mul ((Real.continuous_rpow_const (le_of_lt hα)).comp hnorm2)
  have hclosed : IsClosed {p : X × X | ‖f p.1 - f p.2‖ ≤ K * ‖p.1 - p.2‖ ^ α} :=
    isClosed_le hnorm hrpow
  have hsub : Ω ×ˢ Ω ⊆ {p : X × X | ‖f p.1 - f p.2‖ ≤ K * ‖p.1 - p.2‖ ^ α} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact h a ha b hb
  have hxy : (x, y) ∈ closure (Ω ×ˢ Ω) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  exact closure_minimal hsub hclosed hxy

end Work.NN.Core.TelTwoDF
