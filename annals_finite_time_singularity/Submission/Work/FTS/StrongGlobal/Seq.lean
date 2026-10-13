/-
# `Work.FTS.StrongGlobal.Seq` — the continuation sequence of S5

This module builds the *stepping* of the global existence theorem `global_strong` (S5 of
`Submission/Work/FTS/FTS_STRONG_ROUTE.md` §3).

**The construction.**  Fix an exponent `α`, the canonical stream data `(Φs, EllSol)`, a datum `g₀`
and the two hypotheses of the route

* `hLWP : LWPStrong α Φs EllSol α₀ K δ` (**S1**): from any datum at any time `τ₀ ≥ 0` with
  `RegQ α 6` and `Xn₆ ≤ Kα²` there is a strong solution on `[τ₀, τ₀+δ]`;
* `hPersist : PersistStrong α Φs EllSol C₀ K` (**S2**): the `ℋ⁶`-bound `Kα²` is preserved as long
  as the `ℋ⁴`-bound `C₀α²` holds.

Starting from `g₀` (with `Xs` small enough: `Xn₄(g₀) ≤ α²` and `Xn₆(g₀) ≤ Kα²`) we build, by
recursion on `n`, an accumulated family `G n` that solves the dynamic modulated equation on the
*closed* fake-time interval `[0, stepEnd δ n] = [0, (n+1)δ]`, with

* `G n (·,·,0) = g₀`,
* `Xn₄(G n(τ)) ≤ C₀α²` for `τ ∈ [0, stepEnd δ n]` (by the a-priori bound **S4**,
  `Work.FTS.StrongGlobal.apriori_strong`),
* `Xn₆(G n(τ)) ≤ Kα²` (by **S2**),
* the nesting `G (n+1) = G n` on `[0, stepEnd δ n]`, so that all pieces are compatible.

The step is: at the junction `τ₀ = stepEnd δ n`, the datum `slice (G n) τ₀` has `RegQ α 6`
(`StrongSolOn.reg6`) and `Xn₆ ≤ Kα²` (the `ℋ⁶`-bound), so **S1** produces a strong solution `Q` on
`[τ₀, τ₀+δ]` with `Q(·,·,τ₀) = slice (G n) τ₀`, and `G (n+1)` is the concatenation of `G n` and
`Q` at `τ₀`.  The concatenation is a strong solution on `[0, τ₀+δ]` by the junction glue
`Work.FTS.StrongGlobal.isDynGSolOnIcc_concat`, and its joint `C¹`-field by the junction glue
`Work.FTS.StrongGlobal.contDiffOn_concat_1` (at the junction both pieces are `C¹` — their
`StrongSolOn.c1`-slabs have one unit of slack and `τ₀` is interior to both — and the two
hypotheses of that glue are `Q(·,·,τ₀) = slice (G n) τ₀` and the equality of the fake-time
derivatives there, which is the equation evaluated on the common slice).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongGlobal.Apriori
import Submission.Work.FTS.StrongGlobal.isDynGSolOnIcc_concat
import Submission.Work.FTS.StrongGlobal.dynRHS_congr
import Submission.Work.FTS.StrongGlobal.contDiffOn_concat_1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-! ## Auxiliary facts -/

/-- **A two-sided derivative equals a one-sided within-derivative.**  If `f` has the
within-`[a,b]`-derivative `V` at an interior-or-endpoint point `x ∈ [a,b]` (`a < b`) and is
differentiable at `x`, then `deriv f x = V`.  This is the bridge between the equation (which is a
*within*-derivative on the closed interval of fake time) and the two-sided derivative occurring in
the `C¹`-junction lemma. -/
theorem deriv_eq_of_hasDerivWithinAt_Icc {f : ℝ → ℝ} {V a b x : ℝ} (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hV : HasDerivWithinAt f V (Set.Icc a b) x)
    (hd : DifferentiableAt ℝ f x) : deriv f x = V := by
  have hsub1 : ∀ y ∈ Set.Ioc x b, y ∈ Set.Icc a b \ {x} := fun y hy =>
    ⟨⟨le_trans hx.1 hy.1.le, hy.2⟩, ne_of_gt hy.1⟩
  have hsub2 : ∀ y ∈ Set.Ico a x, y ∈ Set.Icc a b \ {x} := fun y hy =>
    ⟨⟨hy.1, le_trans hy.2.le hx.2⟩, ne_of_lt hy.2⟩
  have hmem : x ∈ closure (Set.Icc a b \ {x}) := by
    rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · refine closure_mono hsub1 ?_
      rw [closure_Ioc (a := x) (b := b) (ne_of_lt hxb)]
      exact ⟨le_rfl, hxb.le⟩
    · subst hxb
      refine closure_mono hsub2 ?_
      rw [closure_Ico (a := a) (b := x) (ne_of_lt hab)]
      exact ⟨hx.1, le_rfl⟩
  have hne : NeBot (𝓝[Set.Icc a b \ {x}] x) := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have h1 : Tendsto (slope f x) (𝓝[Set.Icc a b \ {x}] x) (𝓝 V) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hV
  have h2 : Tendsto (slope f x) (𝓝[Set.Icc a b \ {x}] x) (𝓝 (deriv f x)) :=
    hasDerivWithinAt_iff_tendsto_slope.mp
      (hd.hasDerivAt.hasDerivWithinAt : HasDerivWithinAt f (deriv f x) (Set.Icc a b) x)
  exact tendsto_nhds_unique h2 h1

theorem slab_min_left {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) : min (-1) (τ₀ - 1) = -1 :=
  min_eq_left (by linarith)

theorem slab_max_right {τ₀ δ : ℝ} (hδ : 0 < δ) : max (τ₀ + 1) (τ₀ + δ + 1) = τ₀ + δ + 1 :=
  max_eq_right (by linarith)

/-! ## The time steps -/

/-- The end of the `n`-th time step, `(n+1)δ`. -/
def stepEnd (δ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * δ

theorem stepEnd_succ (δ : ℝ) (n : ℕ) : stepEnd δ (n + 1) = stepEnd δ n + δ := by
  rw [stepEnd, stepEnd]
  push_cast
  ring

theorem stepEnd_nonneg {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 ≤ stepEnd δ n := by
  rw [stepEnd]; positivity

theorem stepEnd_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < stepEnd δ n := by
  rw [stepEnd]; positivity

theorem stepEnd_self (δ : ℝ) (n : ℕ) : stepEnd δ n = (n : ℝ) * δ + δ := by
  rw [stepEnd]; ring

theorem stepEnd_zero (δ : ℝ) : stepEnd δ 0 = δ := by
  rw [stepEnd]; norm_num

theorem stepEnd_mono {δ : ℝ} (hδ : 0 ≤ δ) {n m : ℕ} (h : n ≤ m) :
    stepEnd δ n ≤ stepEnd δ m := by
  rw [stepEnd, stepEnd]
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  nlinarith

/-! ## The accumulated pieces -/

/-- **The data carried by the `n`-th accumulated piece** of the continuation: it solves the dynamic
modulated problem on `[0, (n+1)δ]`, starts at `g₀`, and obeys the a-priori `ℋ⁴`-bound and the
persisted `ℋ⁶`-bound there. -/
structure PieceData (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) (δ C₀ K : ℝ) (n : ℕ)
    (g : Fam) : Prop where
  data : ∀ z θ, g z θ 0 = g₀ z θ
  sol : StrongSolOn α Φs EllSol 0 (stepEnd δ n) g
  bnd4 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n), Xn α (slice g τ) ≤ C₀ * α ^ 2
  bnd6 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n), Xn6 α (slice g τ) ≤ K * α ^ 2

/-- **The local piece produced by S1** at the junction time `stepEnd δ n`, from the datum
`slice g (stepEnd δ n)`. -/
noncomputable def lwpPiece {α₀ K δ : ℝ} (hLWP : LWPStrong α Φs EllSol α₀ K δ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (g : Fam) (n : ℕ) (hreg : RegQ α 6 (slice g (stepEnd δ n)))
    (hb : Xn6 α (slice g (stepEnd δ n)) ≤ K * α ^ 2) : Fam :=
  (hLWP.2.2.2 α hα hαα₀ (stepEnd δ n) (stepEnd_nonneg hLWP.1 n) (slice g (stepEnd δ n))
    hreg hb).choose

theorem lwpPiece_spec {α₀ K δ : ℝ} (hLWP : LWPStrong α Φs EllSol α₀ K δ) (hα : 0 < α)
    (hαα₀ : α ≤ α₀) (g : Fam) (n : ℕ) (hreg : RegQ α 6 (slice g (stepEnd δ n)))
    (hb : Xn6 α (slice g (stepEnd δ n)) ≤ K * α ^ 2) :
    (∀ z θ, lwpPiece hLWP hα hαα₀ g n hreg hb z θ (stepEnd δ n)
        = slice g (stepEnd δ n) z θ) ∧
      StrongSolOn α Φs EllSol (stepEnd δ n) (stepEnd δ n + δ)
        (lwpPiece hLWP hα hαα₀ g n hreg hb) :=
  (hLWP.2.2.2 α hα hαα₀ (stepEnd δ n) (stepEnd_nonneg hLWP.1 n) (slice g (stepEnd δ n))
    hreg hb).choose_spec

end Work.FTS.StrongGlobal
