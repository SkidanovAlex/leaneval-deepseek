/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongLWP/Sobolev/Prelim.lean` — support and rectangle preliminaries of S3

Two elementary inputs of the interior Sobolev estimate `S3` (`sobolev_C4_bound`,
`Submission/Work/FTS/StrongLWP/Sobolev/Main.lean`):

* **support in `z`.**  The sup norms `supAbs (mixed c d f)` of the mixed derivatives are bounded by
  `Linf_H2`-type inequalities only when those derivatives decay at `z = ∞`
  (`Work.Spaces.Linf_H2_of_decay`).  The intended class of data of the strong route is the
  *compactly supported* one (the Galerkin profiles of `RegPkgGal` are compactly supported in `z`),
  for which the decay is automatic: a function vanishing for `z > Z` has every `z`- and
  `θ`-derivative vanishing for `z > Z`.  `mixed_decayInZ_of_supportsInZ` records this.

* **rectangles.**  The interior Sobolev bound is local: every compact `K ⊆ Q0` is contained in a
  product of intervals `[a,b] × [c,d]` with `a > 0`, `c > 0`, `d < π/2`, on which the weights
  `z` and `sin(2θ)` appearing in the inversion `mixed_inversion_bound` are bounded below.
  `exists_rect_of_compact_subset_Q0` supplies such a rectangle.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.StrongLWP.Library

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## The two smoothness classes -/

/-- `SmoothNbhd` implies `SmoothInt`: the neighbourhood class of `Work.Spaces` contains the open
strip `Ioi (-1) ×ˢ Ioo 0 (π/2)`, and the `z`-slices of a smooth function are smooth. -/
theorem smoothInt_of_smoothNbhd {f : Fn} (h : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothInt f := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-! ## Support in the radial variable, and the decay it forces -/

/-- `f` vanishes for `z > Z`, uniformly in the angle.  This is the form of "compact support in `z`"
that the strong route's data satisfy (the Galerkin profiles are supported in `z ≤ Z(τ)`), and it is
what makes the sup-norm bounds of `Linf_H2`-type available.  The strict inequality is what makes
every derivative vanish on a *two-sided* neighbourhood of each point of `Ioi Z`. -/
def SupportsInZ (f : Fn) (Z : ℝ) : Prop := ∀ z, Z < z → ∀ θ : ℝ, f z θ = 0

/-- `f` has compact support in the radial variable. -/
def CompactlySupportedInZ (f : Fn) : Prop := ∃ Z : ℝ, SupportsInZ f Z

/-- A function vanishing for `z > Z` is (at every fixed angle) eventually zero, hence has limit `0`
at `z = ∞`. -/
theorem SupportsInZ.tendsto {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (θ : ℝ) :
    Tendsto (fun z => f z θ) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨Z + 1, fun z hz =>
    (h z (by linarith : Z < z) θ).symm⟩)

/-- The pure `z`-derivative of a function vanishing for `z > Z` vanishes there as well. -/
theorem SupportsInZ.pz {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) :
    SupportsInZ (Work.Spaces.pz f) Z := by
  intro z hz θ
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ
  rw [Work.Spaces.pz, hev.deriv_eq]
  simp

/-- The pure `θ`-derivative of a function vanishing for `z > Z` vanishes there as well. -/
theorem SupportsInZ.pth {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) :
    SupportsInZ (Work.Spaces.pth f) Z := by
  intro z hz θ
  have hev : (fun θ' => f z θ') = fun _ => (0 : ℝ) := funext fun θ' => h z hz θ'
  rw [Work.Spaces.pth, hev]
  simp

/-- Every iterated mixed derivative `D_z^c D_θ^d f` of a function vanishing for `z > Z` vanishes
there as well. -/
theorem SupportsInZ.mixed {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (c d : ℕ) :
    SupportsInZ (Work.Spaces.mixed c d f) Z := by
  induction c with
  | zero =>
      induction d with
      | zero => simpa using h
      | succ d ih =>
          intro z hz θ
          have hthis : Work.Spaces.pth (Work.Spaces.DthIter d f) z θ = 0 := ih.pth z hz θ
          show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter d f) z θ = 0
          rw [hthis, mul_zero]
  | succ c ih =>
      intro z hz θ
      have hthis : Work.Spaces.pz (Work.Spaces.mixed c d f) z θ = 0 := ih.pz z hz θ
      show z * Work.Spaces.pz (Work.Spaces.mixed c d f) z θ = 0
      rw [hthis, mul_zero]

/-- Every pure partial derivative `∂_z^j ∂_θ^i f` of a function vanishing for `z > Z` vanishes
there as well. -/
theorem SupportsInZ.pzIter_pthIter {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (j i : ℕ) :
    SupportsInZ (Work.Spaces.pzIter j (Work.Spaces.pthIter i f)) Z := by
  induction j with
  | zero =>
      induction i with
      | zero => simpa using h
      | succ i ih =>
          change SupportsInZ (Work.Spaces.pth (Work.Spaces.pthIter i f)) Z
          exact ih.pth
  | succ j ih =>
      change SupportsInZ (Work.Spaces.pz (Work.Spaces.pzIter j (Work.Spaces.pthIter i f))) Z
      exact ih.pz

/-- **The radial decay of the mixed derivatives of a function with compact support in `z`.**  For
every `c d : ℕ` the mixed derivative `D_z^c D_θ^d f` satisfies the decay hypothesis
`DecayInZ 2` that `Work.Spaces.Linf_H2_of_decay` (and hence the sup-norm bound of `S3`) requires. -/
theorem mixed_decayInZ_of_supportsInZ {f : Fn} {Z : ℝ} (h : SupportsInZ f Z) (c d : ℕ) :
    Work.Spaces.DecayInZ 2 (Work.Spaces.mixed c d f) := by
  intro j i _ θ _
  exact (h.mixed c d).pzIter_pthIter j i |>.tendsto θ

theorem mixed_decayInZ_of_compactlySupportedInZ {f : Fn} (h : CompactlySupportedInZ f)
    (c d : ℕ) : Work.Spaces.DecayInZ 2 (Work.Spaces.mixed c d f) := by
  obtain ⟨Z, hZ⟩ := h
  exact mixed_decayInZ_of_supportsInZ hZ c d

/-! ## Rectangles inside the open quadrant -/

/-- **A compact subset of the open quadrant is contained in a product of intervals with positive
endpoints.**  This is the localisation used by `sobolev_C4_bound`: on such a rectangle the weights
`z` and `sin(2θ)` are bounded below, so the pointwise inversion of the mixed operators is bounded. -/
theorem exists_rect_of_compact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < π / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, 1, 1, one_pos, le_rfl, one_pos, le_rfl,
      by linarith [Real.pi_gt_three], by simp⟩
  · obtain ⟨p₁, hp₁, hmin₁⟩ := hK.exists_isMinOn hne (continuous_fst.continuousOn)
    obtain ⟨p₂, hp₂, hmax₁⟩ := hK.exists_isMaxOn hne (continuous_fst.continuousOn)
    obtain ⟨p₃, hp₃, hmin₂⟩ := hK.exists_isMinOn hne (continuous_snd.continuousOn)
    obtain ⟨p₄, hp₄, hmax₂⟩ := hK.exists_isMaxOn hne (continuous_snd.continuousOn)
    have hQ₁ : (0 : ℝ) < p₁.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₁)).1
    have hQ₃ : (0 : ℝ) < p₃.2 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₃)).2.1
    have hQ₄ : p₄.2 < π / 2 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp₄)).2.2
    exact ⟨p₁.1, p₂.1, p₃.2, p₄.2, hQ₁, hmin₁ hp₂, hQ₃, hmin₂ hp₄, hQ₄,
      fun p hp => ⟨⟨hmin₁ hp, hmax₁ hp⟩, ⟨hmin₂ hp, hmax₂ hp⟩⟩⟩

end Work.FTS.StrongLWP
