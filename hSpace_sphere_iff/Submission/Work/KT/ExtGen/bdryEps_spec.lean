import Mathlib
import Submission.Work.KT.ExtGen.TripleBdry

namespace Work.KT.ExtGen

noncomputable section

/-- Auxiliary to `bdryEps_spec`.

If the three chart slices of `F : tripleAlg V W Z` are the constant function `c` — i.e. `F` is an
element of `bdryKernel`, whose `bdryProj` is `algebraMap c` — then `F` takes the value `c` at every
point `y` of the boundary sphere `∂(D_{V×(W×Z)})`.

Since `∂(D_{V×(W×Z)})` is the set of points with `max ‖v‖ (max ‖w‖ ‖z‖) = 1`, at least one of the
three coordinates lies on its own sphere; the corresponding clause of `mem_tripleAlg_iff` moves
that coordinate to `v₀`/`w₀`/`z₀`, putting `y` on one of the three slices, where the value is `c`
by hypothesis. -/
lemma tripleAlg_slice_const_apply (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (F : tripleAlg V W Z) (c : ℂ)
    (hV : sliceV0 V W Z v0 hv0 F = algebraMap ℂ (prodAlg W Z) c)
    (hW : sliceW0 V W Z w0 hw0 F = algebraMap ℂ (prodAlg V Z) c)
    (hZ : sliceZ0 V W Z z0 hz0 F = algebraMap ℂ (prodAlg V W) c)
    (y : Ball (V × (W × Z))) (hy : y ∈ bdry (V × (W × Z))) :
    (F : C(Ball (V × (W × Z)), ℂ)) y = c := by
  have hy1 : ‖(y : V × (W × Z)).1‖ ≤ 1 := norm_fst_le' V W Z y
  have hy2 : ‖(y : V × (W × Z)).2.1‖ ≤ 1 := norm_w_le V W Z y
  have hy3 : ‖(y : V × (W × Z)).2.2‖ ≤ 1 := norm_zc_le V W Z y
  have hy2' : ‖(y : V × (W × Z)).2‖ ≤ 1 := by
    rw [Prod.norm_def]; exact max_le hy2 hy3
  have hmax : max ‖(y : V × (W × Z)).1‖
      (max ‖(y : V × (W × Z)).2.1‖ ‖(y : V × (W × Z)).2.2‖) = 1 := by
    rw [← Prod.norm_def, ← Prod.norm_def]; exact hy
  have hdisj : ‖(y : V × (W × Z)).1‖ = 1 ∨ ‖(y : V × (W × Z)).2.1‖ = 1 ∨
      ‖(y : V × (W × Z)).2.2‖ = 1 := by
    rcases max_eq_iff.mp hmax with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Or.inl h1
    · rcases max_eq_iff.mp h2 with ⟨hw, _⟩ | ⟨hz, _⟩
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr hz)
  rcases hdisj with h1 | h2 | h3
  · -- first coordinate on its sphere: `y` is on the `v = v₀` slice
    set p : Ball (W × Z) := ⟨(y : V × (W × Z)).2, mem_closedBall_zero_iff.mpr hy2'⟩ with hpdef
    have hconst := F.2.1 y (sliceMapV0 V W Z v0 hv0 p) h1 hv0 rfl rfl
    have hslice := sliceV0_apply V W Z v0 hv0 F p
    rw [hconst, ← hslice, hV]
    simp
  · -- second coordinate on its sphere: `y` is on the `w = w₀` slice
    have hp : ((y : V × (W × Z)).1, (y : V × (W × Z)).2.2) ∈ Metric.closedBall (0 : V × Z) 1 :=
      mem_closedBall_zero_iff.mpr (by rw [Prod.norm_def]; exact max_le hy1 hy3)
    set q : Ball (V × Z) := ⟨((y : V × (W × Z)).1, (y : V × (W × Z)).2.2), hp⟩ with hqdef
    have hconst := F.2.2.1 y (sliceMapW0 V W Z w0 hw0 q) h2 hw0 rfl rfl
    have hslice := sliceW0_apply V W Z w0 hw0 F q
    rw [hconst, ← hslice, hW]
    simp
  · -- third coordinate on its sphere: `y` is on the `z = z₀` slice
    have hp : ((y : V × (W × Z)).1, (y : V × (W × Z)).2.1) ∈ Metric.closedBall (0 : V × W) 1 :=
      mem_closedBall_zero_iff.mpr (by rw [Prod.norm_def]; exact max_le hy1 hy2)
    set r : Ball (V × W) := ⟨((y : V × (W × Z)).1, (y : V × (W × Z)).2.1), hp⟩ with hrdef
    have hconst := F.2.2.2 y (sliceMapZ0 V W Z z0 hz0 r) h3 hz0 rfl rfl
    have hslice := sliceZ0_apply V W Z z0 hz0 F r
    rw [hconst, ← hslice, hZ]
    simp

/-- `bdryEps V W Z v₀ hv₀ w₀ hw₀ z₀ hz₀ y₀ : bdryKernel ... →ₐ[ℂ] ℂ` (see
`Submission.Work.KT.ExtGen.TripleBdry`) is evaluation at the point `y₀`, restricted to the
subalgebra `bdryKernel = bdryProj⁻¹(ℂ·1)` of `tripleAlg`; its value on `u` is the (constant) value
of `u` on the boundary sphere, so `bdryProj u = algebraMap (bdryEps u)`. -/
theorem bdryEps_spec (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (y0 : Ball (V × (W × Z)))
    (hy0 : y0 ∈ bdry (V × (W × Z))) :
    ∀ u : bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0,
      bdryProj V W Z v0 hv0 w0 hw0 z0 hz0 u
        = algebraMap ℂ (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0)
            (bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0 u) := by
  intro u
  obtain ⟨c, hc⟩ := u.2
  have hcP := congrArg (fun x : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 =>
      (x : prodAlg W Z × prodAlg V Z × prodAlg V W)) hc
  have hV : sliceV0 V W Z v0 hv0 (u : tripleAlg V W Z) = algebraMap ℂ (prodAlg W Z) c := by
    have := congrArg (fun p : prodAlg W Z × prodAlg V Z × prodAlg V W => p.1) hcP
    simpa [bdryProj_apply, Subalgebra.coe_algebraMap, Prod.algebraMap_apply] using this
  have hW : sliceW0 V W Z w0 hw0 (u : tripleAlg V W Z) = algebraMap ℂ (prodAlg V Z) c := by
    have := congrArg (fun p : prodAlg W Z × prodAlg V Z × prodAlg V W => p.2.1) hcP
    simpa [bdryProj_apply, Subalgebra.coe_algebraMap, Prod.algebraMap_apply] using this
  have hZ : sliceZ0 V W Z z0 hz0 (u : tripleAlg V W Z) = algebraMap ℂ (prodAlg V W) c := by
    have := congrArg (fun p : prodAlg W Z × prodAlg V Z × prodAlg V W => p.2.2) hcP
    simpa [bdryProj_apply, Subalgebra.coe_algebraMap, Prod.algebraMap_apply] using this
  have hconst : ((u : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ)) y0 = c :=
    tripleAlg_slice_const_apply V W Z v0 hv0 w0 hw0 z0 hz0 (u : tripleAlg V W Z) c hV hW hZ y0 hy0
  have heps : bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0 u = c := by
    rw [bdryEps_apply]; exact hconst
  rw [hc, heps]

end

end Work.KT.ExtGen
