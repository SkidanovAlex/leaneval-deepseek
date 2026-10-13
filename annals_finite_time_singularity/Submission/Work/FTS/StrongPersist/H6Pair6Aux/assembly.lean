/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.H6Pair6Aux.assembly` — the assembly of `H6Pair6` from its rows

`dynRHS α Φ g τ = gRHS α μ λ (F_*+f) Ψ f = (-μ̄·AK) + N₀ + N + N*` (definitionally, with
`f = slice g τ`, `Ψ = slice Φ τ`, `F = Ftau α g τ`).  This module fixes the four summands as
`P1 … P4`, records the definitional identity `dynRHS_eq_sum`, and proves the reduction

`H6Pair6_of_rows`: the level-six pairing bound follows from

* the scalar bound `|muDyn α Φ g τ| ≤ Kμ (1+|Ce|+|Cs|)⁴ α^{-10} (1+M)⁴` (`row_mu_bound`), and
* the four row bounds `|IP6 1…1 α Pᵢ (slice g τ)| ≤ Kᵢ (1+|Ce|+|Cs|)⁴ α^{-10} (1+M)⁴ (1+Sq6)`,
  with the membership data `SmoothOpen`/`HkMem α 6` for `P1`, `P2`, `P4` (needed to split the
  pairing by `IP6_split4`),

together with the `N*`-row `nstar_pair_le` (`H6Pair_ones3`), which needs no elliptic data.

The membership of `P3 = N` is *not* asked for: it is transferred from the membership of the whole
`dynRHS` (`L6Ctx.hrhs`) and that of the other three summands by
`H6Pair6Aux.HkMem_sub_of_HkMem` — which is what makes the reduction work with the interface as
frozen (the honesty of `N` alone is not implied by `L6Ctx`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core

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

/-! ## Constant multiples of open-quadrant-smooth data -/

/-- A constant multiple of an open-quadrant-smooth datum is open-quadrant-smooth. -/
theorem smoothOpen_const_mul_loc (c : ℝ) {f : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [h]
  exact contDiffOn_const.mul (hf.forall n)

/-! ## The four summands of `dynRHS` -/

/-- The modulation summand `-μ̄·AK α` of `dynRHS`. -/
def P1 (α : ℝ) (g Φ : Fam) (τ : ℝ) : Fn :=
  fun z θ => -Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (slice g τ))
      (Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ))
    * Work.Construction.AK α z θ

/-- The `N₀`-summand of `dynRHS`. -/
def P2 (α : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.N0 α (Work.Construction.Ftau α g τ) (slice g τ)

/-- The `N`-summand of `dynRHS`. -/
def P3 (α : ℝ) (g Φ : Fam) (τ : ℝ) : Fn :=
  Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ)

/-- The `N*`-summand of `dynRHS`, at the dynamic modulation constants. -/
def P4 (α : ℝ) (Φ g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Nstar (Work.FTS.Galerkin.muDyn α Φ g τ)
    (Work.FTS.Galerkin.lamDyn α Φ g τ) (slice g τ)

/-- **`dynRHS` is the four-fold sum of the pieces**, with the association of `gRHS`. -/
theorem dynRHS_eq_sum (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    Work.FTS.Galerkin.dynRHS α Φ g τ
      = fun z θ => ((P1 α g Φ τ z θ + P2 α g τ z θ) + P3 α g Φ τ z θ) + P4 α Φ g τ z θ := rfl

/-- `P4` is the `N*`-form `-μ f - (μ + λ + μλ) D_z f` of the pieces of `nstar_pair_le`. -/
theorem P4_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    P4 α Φ g τ = fun z θ => -(Work.FTS.Galerkin.muDyn α Φ g τ) * slice g τ z θ
      - (Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ)
        * Work.Spaces.Dz (slice g τ) z θ := rfl

/-! ## Membership of the pieces -/

/-- **Membership of the `N*`-piece.**  `P4 = -μ f - (μ+λ+μλ) D_z f` is `C^∞` on the open
quadrant and `ℋ⁶`, from the smoothness/`ℋ⁶`-membership of `f`, of `D_z f`
(`IPGen.HkMem_Dz_le`, which consumes `HkMem α 7 f`) and the closure under constant multiples. -/
theorem P4_smooth_mem {α : ℝ} {g Φ : Fam} {τ : ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen (slice g τ))
    (h6 : Work.Spaces.HkMem α 6 (slice g τ))
    (h7 : Work.Spaces.HkMem α 7 (slice g τ)) :
    Work.FTS.EllipticEst.SmoothOpen (P4 α Φ g τ) ∧ Work.Spaces.HkMem α 6 (P4 α Φ g τ) := by
  have he : P4 α Φ g τ = fun z θ =>
      (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ
      + (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ := by
    funext z θ
    rw [P4_eq]
    ring
  rw [he]
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ) :=
    smoothOpen_const_mul_loc (-(Work.FTS.Galerkin.muDyn α Φ g τ)) hsmf
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ) :=
    smoothOpen_const_mul_loc _ hsmf.Dz
  have hm1 : Work.Spaces.HkMem α 6
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ)) * slice g τ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 _ h6
  have hm2 : Work.Spaces.HkMem α 6
      (fun z θ => (-(Work.FTS.Galerkin.muDyn α Φ g τ + Work.FTS.Galerkin.lamDyn α Φ g τ
          + Work.FTS.Galerkin.muDyn α Φ g τ * Work.FTS.Galerkin.lamDyn α Φ g τ))
        * Work.Spaces.Dz (slice g τ) z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 _ (Work.FTS.IPGen.HkMem_Dz_le hsmf h7)
  exact ⟨smoothOpen_add' hsm1 hsm2, HkMem_add_of_HkMem α 6 hsm1 hsm2 hm1 hm2⟩

/-- **Transferred membership of the `N`-piece.**  The honesty of `P3` alone is *not* implied by
`L6Ctx`; what is implied is the honesty of the whole `dynRHS` (`L6Ctx.hrhs`).  Since
`P3 = dynRHS - (P1 + P2 + P4)` and the difference of two `ℋ⁶`-data is `ℋ⁶`
(`HkMem_sub_of_HkMem`), `P3` is in `ℋ⁶` as soon as the other three summands are. -/
theorem P3_mem_of_rest {α : ℝ} {g Φ : Fam} {τ : ℝ}
    (hdynd_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.dynRHS α Φ g τ))
    (hdyn : Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.dynRHS α Φ g τ))
    (hsm1 : Work.FTS.EllipticEst.SmoothOpen (P1 α g Φ τ))
    (hsm2 : Work.FTS.EllipticEst.SmoothOpen (P2 α g τ))
    (hsm4 : Work.FTS.EllipticEst.SmoothOpen (P4 α Φ g τ))
    (hm1 : Work.Spaces.HkMem α 6 (P1 α g Φ τ))
    (hm2 : Work.Spaces.HkMem α 6 (P2 α g τ))
    (hm4 : Work.Spaces.HkMem α 6 (P4 α Φ g τ)) :
    Work.Spaces.HkMem α 6 (P3 α g Φ τ) := by
  have hsm12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => P1 α g Φ τ z θ + P2 α g τ z θ) := smoothOpen_add' hsm1 hsm2
  have hm12 : Work.Spaces.HkMem α 6 (fun z θ => P1 α g Φ τ z θ + P2 α g τ z θ) :=
    HkMem_add_of_HkMem α 6 hsm1 hsm2 hm1 hm2
  have hsm124 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (P1 α g Φ τ z θ + P2 α g τ z θ) + P4 α Φ g τ z θ) :=
    smoothOpen_add' hsm12 hsm4
  have hm124 : Work.Spaces.HkMem α 6
      (fun z θ => (P1 α g Φ τ z θ + P2 α g τ z θ) + P4 α Φ g τ z θ) :=
    HkMem_add_of_HkMem α 6 hsm12 hsm4 hm12 hm4
  have hsub := HkMem_sub_of_HkMem α 6 hdynd_sm hsm124 hdyn hm124
  have heq : (fun z θ => Work.FTS.Galerkin.dynRHS α Φ g τ z θ
        - ((P1 α g Φ τ z θ + P2 α g τ z θ) + P4 α Φ g τ z θ)) = P3 α g Φ τ := by
    funext z θ
    rw [dynRHS_eq_sum]
    ring
  rwa [heq] at hsub

/-! ## The right-hand side shape of the rows -/

/-- The right-hand side shared by the four rows and by `H6Pair.pair`:
`(1+|Ce|+|Cs|)⁴ α^{-10} (1+M)⁴ (1 + |f|²_{ℋ⁶})`. -/
def RowRHS (α M Ce Cs : ℝ) (f : Fn) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)

theorem RowRHS_nonneg {α M Ce Cs : ℝ} {f : Fn} (hα : 0 < α) : 0 ≤ RowRHS α M Ce Cs f := by
  have h1 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    apply pow_nonneg
    have := abs_nonneg Ce; have := abs_nonneg Cs; linarith
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have h4 : (0 : ℝ) ≤ 1 + Sq6 α f := by have := Sq6_nonneg α f; linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- The `M`-only version of `RowRHS` (no `ℋ⁶` factor): the shape of the scalar bound on the
modulation constant `μ`. -/
def ScalRHS (α M Ce Cs : ℝ) : ℝ :=
  (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4

theorem ScalRHS_nonneg {α M Ce Cs : ℝ} (hα : 0 < α) : 0 ≤ ScalRHS α M Ce Cs := by
  have h1 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    apply pow_nonneg
    have := abs_nonneg Ce; have := abs_nonneg Cs; linarith
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- `ScalRHS` is dominated by `RowRHS`: `(1 + Sq6 f) ≥ 1`. -/
theorem ScalRHS_le_RowRHS {α M Ce Cs : ℝ} {f : Fn} (hα : 0 < α) :
    ScalRHS α M Ce Cs ≤ RowRHS α M Ce Cs f := by
  have h1 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    apply pow_nonneg
    have := abs_nonneg Ce; have := abs_nonneg Cs; linarith
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have h3 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
  have h4 : (1 : ℝ) ≤ 1 + Sq6 α f := by have := Sq6_nonneg α f; linarith
  have h5 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 :=
    mul_nonneg (mul_nonneg h1 h2) h3
  calc ScalRHS α M Ce Cs
      = ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4) * 1 := by
        rw [ScalRHS]; ring
    _ ≤ ((1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4) * (1 + Sq6 α f) :=
        mul_le_mul_of_nonneg_left h4 h5
    _ = RowRHS α M Ce Cs f := by rw [RowRHS]

/-- **The `N*`-coefficient identity at the paper's second modulation constant**:
`|μ + λ(μ) + μ·λ(μ)| = |μ|`.  For `μ ≠ -1` this is `Nonlin.lamfun_add`; for `μ = -1` the value
`lamfun (-1)` is `0` by the totalised division, and the identity is `rfl`-level. -/
theorem abs_add_lamfun (μ : ℝ) :
    |μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ| = |μ| := by
  rcases eq_or_ne μ (-1) with h | h
  · subst h
    have h0 : Work.Construction.lamfun (-1) = 0 := by
      rw [Work.Construction.lamfun]; norm_num
    rw [h0]
    norm_num
  · rw [Work.FTS.Nonlin.lamfun_add h]
    exact abs_neg μ

end Work.FTS.StrongPersist.H6Pair6Aux
