import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.FrameData
import Submission.Work.Diff.Evol.lcOf_second_congr_value
import Submission.Work.Diff.Evol.mvfderiv_inner_pair_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Skewness of the symmetrised second frame derivative `transHess`

`Work.Diff.Evol.transHess g x F v w p i` is the pairing, with `F p x`, of the symmetrisation in
`(v,w)` of the *field-form* second covariant derivative
`∇_v ∇_{smoothExt x w} (F i) = lcOf g (fun y => lcOf g (F i) y (smoothExt x w y)) x v`.

For a `C^∞` family `F` of fields which

* is `g`-orthonormal *near* `x` (`hON`), and
* is *parallel at `x`* to first order (`hfirst : ∀ i v, ∇_v (F i) = 0`),

the matrix `(p, i) ↦ transHess g x F v w p i` is skew:
`transHess v w p i + transHess v w i p = 0`.

## Proof

The function `Ψ y = ⟪F i y, F p y⟫` is constant near `x` (by `hON`), so its second covariant
derivative in the directions `(u, W)` — where `W` is any smooth field, say `smoothExt x w`, and `u`
any tangent vector at `x` — vanishes.  Expanding `∇_u ∇_W Ψ` with the product rule for the metric
pairing (`Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt`, applied twice) gives

  `0 = ⟪∇_u ∇_W (F i), F p x⟫ + ⟪∇_W (F i), ∇_u (F p)⟫ + ⟪∇_u (F i), ∇_W (F p)⟫
        + ⟪F i x, ∇_u ∇_W (F p)⟫`,

and the two middle terms vanish by `hfirst`.  This is `transHess_pairing_zero` below; the target
`transHess_skew` is its two-line consequence, summing the identities for `(u,W) = (v, smoothExt x w)`
and `(u,W) = (w, smoothExt x v)`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

/-- Congruence of `mvfderiv` under eventual equality, for an arbitrary target normed space.
(Mathlib does not provide this for a general codomain; the proof is the same as for the
`E`-valued version: `mvfderiv` is `mfderiv%` composed with `NormedSpace.fromTangentSpace`.) -/
theorem transHess_mvfderiv_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv I f₁ x = mvfderiv I f₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  rfl

/-- If `Ψ : M → ℝ` is constantly `c` near `x`, then the second derivative of `Ψ` in the
directions `(v, W)` (`W` any field) vanishes at `x`.

`Ψ` is constant on a *neighbourhood* of `x`; on that neighbourhood the function
`y ↦ (mvfderiv I Ψ y) (W y)` vanishes identically, whence so does its derivative at `x`. -/
theorem transHess_mvfderiv_second_const {Ψ : M → ℝ} {c : ℝ} {x : M}
    (h : ∀ᶠ y in 𝓝 x, Ψ y = c) (W : Π y : M, TangentSpace I y) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => mvfderiv I Ψ y (W y)) x v = 0 := by
  obtain ⟨s, hs, hsc⟩ := h.exists_mem
  have hxt : x ∈ interior s := mem_interior_iff_mem_nhds.mpr hs
  have ht : interior s ∈ 𝓝 x := isOpen_interior.mem_nhds hxt
  have hΦ : (fun y : M => mvfderiv I Ψ y (W y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [ht] with y hy
    have hy' : Ψ =ᶠ[𝓝 y] (fun _ => c) :=
      Filter.eventually_of_mem (isOpen_interior.mem_nhds hy)
        (fun z hz => hsc z (interior_subset hz))
    rw [transHess_mvfderiv_congr (I := I) hy', mvfderiv_const, zero_apply]
  rw [transHess_mvfderiv_congr (I := I) hΦ, mvfderiv_const, zero_apply]

/-- **The pairing identity behind the skewness of `transHess`.**

For a `g`-orthonormal-near-`x` smooth frame `F` which is parallel at `x` to first order, any smooth
field `W`, any `u ∈ T_xM` and any two frame indices `i`, `p`:

  `⟪∇_u ∇_W (F i), F p x⟫ + ⟪∇_u ∇_W (F p), F i x⟫ = 0`.

(Here `∇_u ∇_W (F i) = lcOf g (fun y => lcOf g (F i) y (W y)) x u`.)  This is the second derivative
of the locally constant function `⟪F i, F p⟫` in the directions `(u, W)`, expanded with the
Leibniz rule for the metric pairing; the "middle" terms `⟪∇_W (F i), ∇_u (F p)⟫` and
`⟪∇_u (F i), ∇_W (F p)⟫` vanish because `F` is parallel at `x`. -/
theorem transHess_pairing_zero
    (g : SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hF : ∀ i, Work.Diff.Evol.SmoothField I M (F i))
    (hON : Work.Diff.Evol.ONFrameNear I M g x F)
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
      Submission.Diff.lcOf g (F i) x v = 0)
    (W : Π y : M, TangentSpace I y) (hW : Work.Diff.Evol.SmoothField I M W)
    (p i : Fin (Module.finrank ℝ E)) (u : TangentSpace I x) :
    g.inner x (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F i) y (W y)) x u)
        (F p x)
      + g.inner x (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F p) y (W y)) x u)
        (F i x) = 0 := by
  -- Put the metric in the instance position, so that `g.inner` is `Inner.inner ℝ` and the
  -- metric-compatibility lemmas can be used.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet : IsMetricCompatible (Submission.Diff.lcOf g) :=
    (Work.EXT.lcSmooth_noBoundary (I := I) (M := M) (g := g)).2.2
  set U : Π y : M, TangentSpace I y := fun y => Submission.Diff.lcOf g (F i) y (W y) with hU
  set V : Π y : M, TangentSpace I y := fun y => Submission.Diff.lcOf g (F p) y (W y) with hV
  have hAsm : CMDiff ∞ (T% (F i)) := hF i
  have hBsm : CMDiff ∞ (T% (F p)) := hF p
  have hWsm : CMDiff ∞ (T% W) := hW
  have hUc : CMDiffAt ∞ (T% U) x := by
    rw [hU]; exact Work.EXT.lcOf_apply_contMDiffAt (I := I) g hAsm hWsm.contMDiffAt
  have hVc : CMDiffAt ∞ (T% V) x := by
    rw [hV]; exact Work.EXT.lcOf_apply_contMDiffAt (I := I) g hBsm hWsm.contMDiffAt
  have hUmd : MDiffAt (T% U) x := hUc.mdifferentiableAt (by simp)
  have hVmd : MDiffAt (T% V) x := hVc.mdifferentiableAt (by simp)
  have hAmd : MDiffAt (T% (F i)) x := hAsm.contMDiffAt.mdifferentiableAt (by simp)
  have hBmd : MDiffAt (T% (F p)) x := hBsm.contMDiffAt.mdifferentiableAt (by simp)
  -- ## The product rule for the pairing, pointwise
  have hpt : (fun y : M => mvfderiv I (fun z : M => g.inner z (F i z) (F p z)) y (W y))
      = fun y : M => g.inner y (U y) (F p y) + g.inner y (F i y) (V y) := by
    funext y
    rw [hU, hV]
    exact Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (cov := Submission.Diff.lcOf g)
      hmet (hAsm.contMDiffAt.mdifferentiableAt (by simp))
      (hBsm.contMDiffAt.mdifferentiableAt (by simp)) (W y)
  -- ## `⟪F i, F p⟫` is constant near `x`, so its second derivative in the directions `(u, W)` is `0`
  have hconst : (fun y : M => g.inner y (F i y) (F p y))
      =ᶠ[𝓝 x] (fun _ => (if i = p then (1 : ℝ) else 0)) := by
    filter_upwards [hON] with y hy
    exact hy i p
  have hsecond : mvfderiv I
      (fun y : M => mvfderiv I (fun z : M => g.inner z (F i z) (F p z)) y (W y)) x u = 0 :=
    transHess_mvfderiv_second_const hconst W u
  have hkey : mvfderiv I
      (fun y : M => g.inner y (U y) (F p y) + g.inner y (F i y) (V y)) x u = 0 := by
    rw [← hpt]; exact hsecond
  -- ## Expanding the derivative of the two summands with metric compatibility
  have hPmd : MDiffAt (fun y : M => g.inner y (U y) (F p y)) x :=
    (Work.EXT.pairing_contMDiffAt (I := I) g hUc hBsm.contMDiffAt).mdifferentiableAt (by simp)
  have hQmd : MDiffAt (fun y : M => g.inner y (F i y) (V y)) x :=
    (Work.EXT.pairing_contMDiffAt (I := I) g hAsm.contMDiffAt hVc).mdifferentiableAt (by simp)
  rw [mvfderiv_fun_add hPmd hQmd, add_apply] at hkey
  have h1 : mvfderiv I (fun y : M => g.inner y (U y) (F p y)) x u
      = g.inner x (Submission.Diff.lcOf g U x u) (F p x)
        + g.inner x (U x) (Submission.Diff.lcOf g (F p) x u) :=
    Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (cov := Submission.Diff.lcOf g)
      hmet hUmd hBmd u
  have h2 : mvfderiv I (fun y : M => g.inner y (F i y) (V y)) x u
      = g.inner x (Submission.Diff.lcOf g (F i) x u) (V x)
        + g.inner x (F i x) (Submission.Diff.lcOf g V x u) :=
    Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (cov := Submission.Diff.lcOf g)
      hmet hAmd hVmd u
  -- ## `F` is parallel at `x`: the two "middle" terms vanish
  rw [h1, h2, hfirst p u, hfirst i u] at hkey
  simp only [map_zero, add_zero, zero_add, zero_apply] at hkey
  rw [hU, hV] at hkey
  rw [g.symm x (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g (F p) y (W y)) x u)
    (F i x)]
  exact hkey

theorem transHess_skew
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hF : ∀ i, Work.Diff.Evol.SmoothField I M (F i))
    (hON : Work.Diff.Evol.ONFrameNear I M g x F)
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
      Submission.Diff.lcOf g (F i) x v = 0)
    (v w : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)) :
    Work.Diff.Evol.transHess g x F v w p i + Work.Diff.Evol.transHess g x F v w i p = 0 := by
  have h1 := transHess_pairing_zero (I := I) (M := M) g x F hF hON hfirst
    (Submission.Diff.smoothExt x w) (Work.Diff.GE.smoothExt_cmdiff x w) p i v
  have h2 := transHess_pairing_zero (I := I) (M := M) g x F hF hON hfirst
    (Submission.Diff.smoothExt x v) (Work.Diff.GE.smoothExt_cmdiff x v) p i w
  simp only [transHess]
  linear_combination (norm := ring) (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h2

end Work.Diff.Evol
