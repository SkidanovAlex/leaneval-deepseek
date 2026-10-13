import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.H2.DivQ

/-! ## Auxiliary one-variable facts for the substitution `x = sin(2θ)`

Everything is proved for points of the open interval `(-1,1)`, i.e. under the map `thetaOf` for
`θ ∈ (-π/4, π/4)`; the target statement only needs the sub-interval `(0, xNear)`. -/

/-- `thetaOf` is differentiable on `(-1,1)` with derivative `1/(2√(1-x²))`. -/
private lemma hasDerivAt_thetaOf {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * Real.sqrt (1 - x ^ 2))) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have heq : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * Real.sqrt (1 - x ^ 2)) := by
    have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr; nlinarith [hx.1, hx.2]
    field_simp
  rw [heq] at h2
  exact h2

/-- On the near interval, `thetaOf` lands in the angular interval `(0,π/2)` on which `h` is
smooth. -/
private lemma thetaOf_mem {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

/-- **The single transport step.**  For any function `U` differentiable at `thetaOf x`
(`x ∈ (-1,1)`), applying `D_θ = sin(2θ)∂_θ` to `U` at `thetaOf x` is the same as applying `Gop`
to the reparametrised function `sliceX U = U ∘ thetaOf` at `x`.  This is the chain rule
`deriv (U ∘ thetaOf) x = deriv U (thetaOf x) · deriv thetaOf x` combined with
`sin (2 thetaOf x) = x`, `cos (2 thetaOf x) = √(1-x²) = kappa x`. -/
private lemma Dth1_thetaOf_eq_Gop (U : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hU : DifferentiableAt ℝ U (thetaOf x)) :
    Work.Elliptic.Dth1 U (thetaOf x) = Gop (sliceX U) x := by
  have hs' : Real.sqrt (1 - x ^ 2) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; nlinarith [hx.1, hx.2]
  have hsin : Real.sin (2 * thetaOf x) = x := by
    have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
    rw [h2, Real.sin_arcsin (by linarith [hx.1]) (by linarith [hx.2])]
  have hcos : Real.cos (2 * thetaOf x) = Real.sqrt (1 - x ^ 2) := by
    have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
    rw [h2, Real.cos_arcsin]
  have htheta := hasDerivAt_thetaOf hx
  have hchain : deriv (sliceX U) x = deriv U (thetaOf x) * (1 / (2 * Real.sqrt (1 - x ^ 2))) :=
    (HasDerivAt.comp x (hU.hasDerivAt) htheta).deriv
  have key : Work.Elliptic.Dth1 U (thetaOf x) = x * deriv U (thetaOf x) := by
    simp only [Work.Elliptic.Dth1, hsin]
  have key2 : Gop (sliceX U) x = 2 * Real.sqrt (1 - x ^ 2) * (x * deriv (sliceX U) x) := by
    simp only [Gop, kappa, hcos]
  rw [key, key2, hchain]
  field_simp

/-- `Gop` only sees `u` through `deriv u x`, so it is insensitive to replacing `u` by a function
that agrees with it near `x`. -/
private lemma Gop_congr_deriv {u v : ℝ → ℝ} {x : ℝ} (h : u =ᶠ[𝓝 x] v) :
    Gop u x = Gop v x := by
  have hd : deriv u x = deriv v x := Filter.EventuallyEq.deriv_eq h
  simp only [Gop, hd]

/-- `Dth1Iter m` of a function of class `C^∞` on an open set is again of class `C^∞` there. -/
private lemma contDiffOn_Dth1Iter {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m f) s := by
  intro m
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [Work.Elliptic.Dth1Iter_succ]
    have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) s :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (Work.Elliptic.Dth1Iter m f)) s :=
      ih.deriv_of_isOpen hs (by simp)
    exact hsin.mul hder

/-- **Transport of the slice-level `D_θ`-iterates to the coordinate `x = sin(2θ)`.**  For `h` of
class `C^∞` on the open angular interval `(0,π/2)`,

  `Dth1Iter i h (thetaOf x) = (Gop^[i]) (sliceX h) x`  for all `x ∈ (0, xNear)`,

in the vocabulary of `Work.FTS.H2.DivQ.Defs` (`thetaOf x = arcsin(x)/2`, `sliceX h x = h (thetaOf x)`,
`Gop u x = 2 κ(x) · (x · deriv u x)`, `κ x = cos(2 thetaOf x) = √(1-x²)`, `xNear = sin(π/4) = 1/√2`)
and `Work.Elliptic.Dth1Iter`, the one-dimensional iterate of `D_θ = sin(2θ) ∂_θ` on slices.

ROUTE.  Prove `Set.EqOn … (Set.Ioo 0 xNear)` by induction on `i`.

* One-variable facts for `x ∈ (-1,1)`: `Real.sin (2 * thetaOf x) = x` (`Real.sin_arcsin`),
  `Real.cos (2 * thetaOf x) = Real.sqrt (1 - x^2) = kappa x` (`Real.cos_arcsin`), and
  `deriv thetaOf x = 1/(2 * Real.sqrt (1-x^2))` (`Real.deriv_arcsin`).
* Base `i = 0`: `rfl`.
* Step: `Dth1Iter (i+1) h = Dth1 (Dth1Iter i h)` with `Dth1 u = sin(2·) * deriv u`; for
  `U := Dth1Iter i h` (again `C^∞` on the open interval) the chain rule
  `deriv (U ∘ thetaOf) x = deriv U (thetaOf x) * deriv thetaOf x` and `sin (2 * thetaOf x) = x`
  give `Dth1 U (thetaOf x) = 2 * kappa x * (x * deriv (U ∘ thetaOf) x) = Gop (U ∘ thetaOf) x`.
  The induction hypothesis identifies `U ∘ thetaOf` with `Gop^[i] (sliceX h)` on `(0,xNear)`;
  since both are the restrictions of differentiable functions, replace them and use
  `Function.iterate_succ_apply'` (`Gop^[i+1] = Gop ∘ Gop^[i]`). -/
theorem DthIter_sliceX (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (fun x => Work.Elliptic.Dth1Iter i h (thetaOf x)) ((Gop^[i]) (sliceX h))
      (Set.Ioo 0 xNear) := by
  induction i with
  | zero => intro x hx; rfl
  | succ i ih =>
    intro x hx
    show Work.Elliptic.Dth1Iter (i + 1) h (thetaOf x) = (Gop^[i + 1]) (sliceX h) x
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      refine ⟨by linarith [hx.1], ?_⟩
      have hxN : xNear ≤ 1 := Real.sin_le_one _
      linarith [hx.2]
    have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem hx
    have hU : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter i h) (thetaOf x) :=
      ((contDiffOn_Dth1Iter isOpen_Ioo hsm i).contDiffAt
        (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)
    have hstep : Work.Elliptic.Dth1Iter (i + 1) h (thetaOf x)
        = Gop (sliceX (Work.Elliptic.Dth1Iter i h)) x := by
      rw [Work.Elliptic.Dth1Iter_succ]
      exact Dth1_thetaOf_eq_Gop _ hxI hU
    rw [hstep, Function.iterate_succ_apply']
    exact Gop_congr_deriv (by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      simpa only [sliceX] using ih hy)

end Work.FTS.H2.DivQ
