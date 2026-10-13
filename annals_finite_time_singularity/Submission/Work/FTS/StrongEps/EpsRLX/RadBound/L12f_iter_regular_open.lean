import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Regularity of the `z∂_z`-iterates of `L₁₂ f` on `(0,∞)` (open-quadrant class)

For `0 < α ≤ 1`, a datum `f` which is `C^∞` on the *open* quadrant
(`Work.FTS.EllipticEst.SmoothOpen f`) with `HkMem α 4 f`, the radial profile
`L₁₂ f = Work.Coercivity.L12f f` is `C^4` on `(0,∞)`; consequently

* every `(z∂_z)`-iterate `D_z^c (L₁₂ f)`, `c ≤ 4`, is continuous on `(0,∞)`;
* every `D_z^b (L₁₂ f)`, `b ≤ 3`, is differentiable at every point of `(0,∞)`.

The two facts are the ones needed downstream to invoke the Leibniz rule
`D_z^q (ampA · L₁₂ f) = ∑ …` (`differentiableAt` of the iterates one order below).

## The proof

The operator of the elliptic chapter and that of the coercivity chapter agree:
`Work.Coercivity.L12f = Work.Elliptic.L12` (`FM.L12 Spaces.K` vs. `FM.L12 FM.Kpaper`,
and `Spaces.K` and `FM.Kpaper` are *the same* function `θ ↦ 3 sin θ cos²θ`, so this is `rfl`
after unfolding).

`Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k` (the open-quadrant version of the
`L₁₂`-regularity theorem: `L₁₂` gains one order over the density `-3 F_*/z`, which is
`C^{k-1}` for `HkMem α k f`) gives `ContDiffOn ℝ 4 (L₁₂ f) (0,∞)`.

From `ContDiffOn ℝ 4` on the *open* half-line, the iterate `D_z^c = Zop^[c]` loses exactly `c`
orders (`Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter'`, `c + (4-c) = 4`), so it
is `C^{4-c}` — in particular continuous; and for `b ≤ 3` it is `C^{b+1} ⊇ C^1`, hence
differentiable (`differentiableAt_Zop_iter_of_contDiffOn`).

The hypothesis `L₁₂ f 0 = 0` is not needed for regularity (it enters the consumer only to fix
the decay of `L₁₂ f` at the origin).
-/

namespace Work.FTS.StrongEps.EpsRLX.RadBound

theorem L12f_iter_regular_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (h0 : Work.Construction.L12 f 0 = 0) :
    (∀ c : ℕ, c ≤ 4 → ContinuousOn (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f))
        (Set.Ioi (0 : ℝ))) ∧
    (∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z) := by
  have _ := h0
  -- the coercivity operator and the elliptic operator are the same function
  have hL12 : Work.Coercivity.L12f f = Work.Elliptic.L12 f := by
    funext z
    show Work.FM.L12 Work.Spaces.K f z = Work.Elliptic.L12 f z
    rw [Work.Elliptic.L12_eq_FM]
    rfl
  -- `L₁₂ f` is `C^4` on the open half-line
  have hCd : ContDiffOn ℝ (4 : WithTop ℕ∞) (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
    rw [hL12]
    exact Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem (by norm_num)
  constructor
  · intro c hc
    -- `D_z^c = Zop^[c]` trades `c` orders of smoothness for `4 - c`
    have hcast : ((c + (4 - c) : ℕ) : WithTop ℕ∞) = (4 : WithTop ℕ∞) := by
      rw [Nat.add_sub_cancel' hc]; norm_num
    have hu : ContDiffOn ℝ ((c : WithTop ℕ∞) + ((4 - c : ℕ) : WithTop ℕ∞))
        (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
      rw [← Nat.cast_add, hcast]
      exact hCd
    have hcd := Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' c (4 - c) hu
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter c]
    exact hcd.continuousOn
  · intro b hb z hz
    have hle : ((b : WithTop ℕ∞) + 1) ≤ (4 : WithTop ℕ∞) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact_mod_cast (by omega : b + 1 ≤ 4)
    have hu : ContDiffOn ℝ ((b : WithTop ℕ∞) + 1) (Work.Coercivity.L12f f)
        (Set.Ioi (0 : ℝ)) :=
      hCd.of_le hle
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b]
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn hu hz

end Work.FTS.StrongEps.EpsRLX.RadBound
