import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- **Leibniz expansion of `D_θ^i` applied to an angular multiple of a `D_z`-iterate.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/DthIter_angular_mul_expand.lean`,
namespace `Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand`.
For `a : ℝ → ℝ` smooth at `θ` (`∀ θ, ContDiffAt ℝ ⊤ a θ`), `f` smooth on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen f`, see `Submission/Work/FTS/EllipticEst/OpenQDefs.lean` —
note `SmoothOpen f` is `ContDiffOn ℝ ⊤ (uncurry f) Q0` with `Q0 = (0,∞) × (0,π/2)`), and
`(z,θ)` with `0 < z`, `θ ∈ (0,π/2)`,
`D_θ^i (a(θ) · D_z^j f (z,θ)) = ∑_{m ≤ i} C(i,m) · (LopIter m a θ) · D_θ^{i-m}(D_z^j f)(z,θ)`,
where `D_θ^k = Work.Spaces.DthIter k` (`D_θ = sin(2θ)∂_θ` is `Work.Spaces.Dth`) and
`LopIter m a θ = (L^m a)(θ)` is the `m`-th iterate of `L = Work.Spaces.Lop` on one-variable
functions (`Work.FTS.EllipticEst.LopIter`).
Proof route: this is `Work.FTS.EllipticEst.Lop_iter_mul` (the iterated Leibniz rule for `Lop`,
already proved in `Submission/Work/FTS/EllipticEst/Lop_iter_mul.lean`) combined with
`Work.Spaces.DthIter_eq_iterate_Lop` (`Submission/Work/Spaces/DthIter_mul.lean`); the
`C^∞`-at-`θ` hypothesis on the `θ`-slice of `D_z^j f` comes from `hf` via `SmoothOpen.DzIter`
and `SmoothOpen.curry_θ` (both in `Submission/Work/FTS/EllipticEst/OpenQDefs.lean`).

Note: the hypothesis available for the `θ`-slice of `D_z^j f` is the *genuine* smooth order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`, not the analytic order `⊤`; the packaged
`Lop_iter_mul` asks for `ContDiffAt ℝ ⊤`, so the smooth-order form
`Work.FTS.LocData.Lop_iter_mul_eqOn_smooth` (in
`Submission/Work/FTS/LocData/DthIter_mul_smoothQuad.lean`) is the one that applies here. -/
theorem DthIter_angular_mul_expand {a : ℝ → ℝ} (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z θ
      = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.DthIter (i - m) (Work.Spaces.DzIter j f) z θ := by
  -- `a` is analytic on `ℝ`, hence `C^∞` (order `smoothOrder`) on the angular interval
  have haCD : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
  have haOn : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (Real.pi / 2)) :=
    (haCD.contDiffOn (s := Set.Ioo 0 (Real.pi / 2))).of_le le_top
  -- the `θ`-slice of `D_z^j f` is `C^∞` on the angular interval
  have hgOn : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.DzIter j).curry_θ hz
  -- the iterated Leibniz rule for `Lop` at the genuine smooth order
  have hmain := Work.FTS.LocData.Lop_iter_mul_eqOn_smooth a
    (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo haOn hgOn i
  -- identify `D_θ^i` on the `θ`-slice with the `i`-th iterate of `Lop`
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop i
    (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z) θ]
  have hfun : (fun θ' : ℝ => a θ' * Work.Spaces.DzIter j f z θ')
      = a * (fun θ' : ℝ => Work.Spaces.DzIter j f z θ') := rfl
  rw [hfun, hmain hθ]
  apply Finset.sum_congr rfl
  intro m hm
  -- identify the remaining `Lop`-iterates: on `a` with `LopIter`, and on the slice with `D_θ^{i-m}`
  rw [← congrFun (Work.Spaces.DthIter_eq_iterate_Lop (i - m) (Work.Spaces.DzIter j f) z) θ]
  simp only [Work.FTS.EllipticEst.LopIter]
  ring

end Work.FTS.EllipticEst.Blocks
