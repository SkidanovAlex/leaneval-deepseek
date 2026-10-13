/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.H6Pair6Aux.assembly_core` — the assembly helpers of `H6Pair6`

`dynRHS = (-mubar·AK) + N₀ + N + N*` (`Construction.gRHS`), and `H6Pair.pair` bounds
`|IP6 1…1 α (dynRHS) (slice g τ)|`.  The route to `H6Pair6` is the decomposition of this pairing
over the four summands; the additivity of `IP6 1 … 1` in its first argument is the finite-order
theorem `IP6AddFin`, whose hypotheses are `ContDiffOn ℝ 6` **and** `HkMem α 6` of *both* summands
and of the second argument.  The four summands of `dynRHS` do not individually carry that data
in the interface (`L6Ctx` gives it only for the *sum*, as `hrhs : HQo α 6 (dynRHS …)`), so the
assembly needs

* the `HkMem`/`SmoothOpen` closure of the pieces under addition and subtraction
  (`HkMem_add_of_HkMem`, `HkMem_sub_of_HkMem`), from the open-class domination transfer
  `EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open` together with the pointwise
  additivity `EllipticEst.HkIntegrand_add_le_of_contDiffOn` of the weighted `ℋ^k`-integrand;
* the resulting four-fold splitting `IP6_split4`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.IP6AddFin
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open
import Submission.Work.FTS.EllipticEst.HkNorm_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `SmoothOpen`-closure of the elementary combinations -/

/-- The negation of an open-quadrant-smooth datum. -/
theorem smoothOpen_neg' {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) := by
  have hfun : Function.uncurry (fun z θ => -g z θ) = -(Function.uncurry g) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hg.neg

/-- The sum of two open-quadrant-smooth data. -/
theorem smoothOpen_add' {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.add hg

/-- The difference of two open-quadrant-smooth data. -/
theorem smoothOpen_sub' {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).sub (hg.forall n)

/-! ## The pointwise additivity of the weighted integrand -/

/-- **Pointwise additivity of `HkIntegrand`** on the closed domain, for data smooth on the open
quadrant: this is `EllipticEst.HkIntegrand_add_le_of_contDiffOn` (whose smoothness set is
`Q0`). -/
theorem HkIntegrand_add_le' (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
  Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α k hf hg

/-- **Pointwise subadditivity of `HkIntegrand`**: the integrand of a difference is dominated by
`2` (integrand of each factor).  Immediate from the additivity applied to `f` and `-g` and the
negation-invariance `EllipticEst.HkIntegrand_neg`. -/
theorem HkIntegrand_sub_le' (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ - g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  have hneg : Work.Spaces.HkIntegrand α k (fun z θ => -g z θ)
      = Work.Spaces.HkIntegrand α k g := by
    have h := Work.FTS.EllipticEst.HkIntegrand_neg α k g
    rwa [show (-g : Fn) = fun z θ => -g z θ from rfl] at h
  have he : (fun z θ => f z θ - g z θ) = fun z θ => f z θ + (fun z θ => -g z θ) z θ := by
    funext z θ
    exact sub_eq_add_neg (f z θ) (g z θ)
  rw [he]
  have h := HkIntegrand_add_le' α k hf (smoothOpen_neg' hg) z hz θ hθ
  rw [hneg] at h
  exact h

/-! ## The `HkMem`-closure of the elementary combinations -/

/-- **`HkMem` of a sum**: from the memberships of the two summands and their open-quadrant
smoothness. -/
theorem HkMem_add_of_HkMem (α : ℝ) (k : ℕ) {f g : Fn}
    (hf_sm : Work.FTS.EllipticEst.SmoothOpen f) (hg_sm : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) :=
  Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k
    (smoothOpen_add' hf_sm hg_sm) hf hg
    (fun z hz => ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_add_le' α k hf_sm hg_sm z hz θ hθ))

/-- **`HkMem` of a difference**: from the memberships of the two summands and their
open-quadrant smoothness. -/
theorem HkMem_sub_of_HkMem (α : ℝ) (k : ℕ) {f g : Fn}
    (hf_sm : Work.FTS.EllipticEst.SmoothOpen f) (hg_sm : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.Spaces.HkMem α k f) (hg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) :=
  Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_open α k
    (smoothOpen_sub' hf_sm hg_sm) hf hg
    (fun z hz => ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_sub_le' α k hf_sm hg_sm z hz θ hθ))

/-! ## The four-fold splitting of the pairing -/

/-- **`IP6 1 … 1` splits over a four-fold sum** (with the association
`((u₁+u₂)+u₃)+u₄` of `Construction.gRHS`), from the finite-order additivity `IP6AddFin` and the
`HkMem`/smoothness closure of the partial sums. -/
theorem IP6_split4 {α : ℝ} (hα : 0 < α) {u₁ u₂ u₃ u₄ v : Fn}
    (hs₁ : Work.FTS.EllipticEst.SmoothOpen u₁)
    (hs₂ : Work.FTS.EllipticEst.SmoothOpen u₂)
    (hs₃ : Work.FTS.EllipticEst.SmoothOpen u₃)
    (hs₄ : Work.FTS.EllipticEst.SmoothOpen u₄)
    (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hm₁ : Work.Spaces.HkMem α 6 u₁) (hm₂ : Work.Spaces.HkMem α 6 u₂)
    (hm₃ : Work.Spaces.HkMem α 6 u₃) (hm₄ : Work.Spaces.HkMem α 6 u₄)
    (hmv : Work.Spaces.HkMem α 6 v) :
    IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => u₁ z θ + u₂ z θ + u₃ z θ + u₄ z θ) v
      = IP6 1 1 1 1 1 1 1 1 1 1 α u₁ v + IP6 1 1 1 1 1 1 1 1 1 1 α u₂ v
        + IP6 1 1 1 1 1 1 1 1 1 1 α u₃ v + IP6 1 1 1 1 1 1 1 1 1 1 α u₄ v := by
  have hs₁₂ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => u₁ z θ + u₂ z θ) :=
    smoothOpen_add' hs₁ hs₂
  have hm₁₂ : Work.Spaces.HkMem α 6 (fun z θ => u₁ z θ + u₂ z θ) :=
    HkMem_add_of_HkMem α 6 hs₁ hs₂ hm₁ hm₂
  have hs₁₂₃ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) := smoothOpen_add' hs₁₂ hs₃
  have hm₁₂₃ : Work.Spaces.HkMem α 6 (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) :=
    HkMem_add_of_HkMem α 6 hs₁₂ hs₃ hm₁₂ hm₃
  have h₁ : ContDiffOn ℝ 6 (Function.uncurry u₁) Work.FTS.EllipticEst.Q0 := hs₁.forall 6
  have h₂ : ContDiffOn ℝ 6 (Function.uncurry u₂) Work.FTS.EllipticEst.Q0 := hs₂.forall 6
  have h₃ : ContDiffOn ℝ 6 (Function.uncurry u₃) Work.FTS.EllipticEst.Q0 := hs₃.forall 6
  have h₄ : ContDiffOn ℝ 6 (Function.uncurry u₄) Work.FTS.EllipticEst.Q0 := hs₄.forall 6
  have hv6 : ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0 := hv.forall 6
  have h₁₂ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => u₁ z θ + u₂ z θ))
      Work.FTS.EllipticEst.Q0 := hs₁₂.forall 6
  have h₁₂₃ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ))
      Work.FTS.EllipticEst.Q0 := hs₁₂₃.forall 6
  rw [IP6AddFin (u := fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) (v := u₄) (w := v)
      hα h₁₂₃ h₄ hv6 hm₁₂₃ hm₄ hmv,
    IP6AddFin (u := fun z θ => u₁ z θ + u₂ z θ) (v := u₃) (w := v) hα h₁₂ h₃ hv6 hm₁₂ hm₃ hmv,
    IP6AddFin (u := u₁) (v := u₂) (w := v) hα h₁ h₂ hv6 hm₁ hm₂ hmv]

end Work.FTS.StrongPersist.H6Pair6Aux
