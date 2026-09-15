import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Calculus

theorem contDiff_of_contDiffOn_compl_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {f : E → F}
    (h : ContDiffOn ℝ n f {x : E | x ≠ 0})
    (h0 : Filter.EventuallyEq (nhds (0 : E)) f (fun _ : E => 0)) : ContDiff ℝ n f := by
  -- `h0` says `f` vanishes on a neighbourhood of `0`; extract an open one.
  have hmem : {x : E | f x = 0} ∈ nhds (0 : E) := h0
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp hmem
  -- `f` agrees with the constant function `0` on `V`, hence is smooth there.
  have hV : ContDiffOn ℝ n f V :=
    (contDiff_const (c := (0 : F))).contDiffOn.congr (fun x hx => hVsub hx)
  -- `{0}ᶜ` and `V` are open and cover `E`, since `0 ∈ V`.
  have hcover : {x : E | x ≠ 0} ∪ V = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inr (hx ▸ hV0)
    · exact Or.inl hx
  exact contDiff_of_contDiffOn_union_of_isOpen h hV hcover isOpen_ne hVopen

end Commons.Analysis.Calculus