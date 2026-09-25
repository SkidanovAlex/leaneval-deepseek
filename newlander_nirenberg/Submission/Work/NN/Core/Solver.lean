import Mathlib
import Submission.Work.Core.Std
import Submission.Work.Core.Solvable
import Submission.Work.NN.Core.Defs
import Submission.Work.NN.Core.dbarPert_norm_le
import Submission.Work.NN.Core.proj_comp_norm_le
import Submission.Work.NN.Core.fderiv_zvec
import Submission.Work.NN.Core.tupleDeriv_comp
import Submission.Work.NN.Core.bijective_add_of_norm_comp_lt_one

/-!
# The honest analytic interface of the Newlander–Nirenberg core

This module replaces the (unsatisfiable, see below) sup-norm interfaces `FlatSolver`/`PertSolver`
of `Defs.lean` by the interface in which the classical small polydisc `∂̄`-estimates are actually
available: a solution operator for `∂̄_J` on *closed* data with a gain of one derivative, where the
data is measured in a **Hölder** (`C^{0,α}`) norm rather than a supremum norm, and the datum is
measured on a slightly larger set `P` than the set `P'` on which the solution is produced.

## Why the sup-norm form is wrong

A solution operator `T` for `∂̄` with a *sup-norm* gain — "data bounded by `δ` gives a solution
with `‖d(solve f)‖ ≤ C δ`" — does not exist, even for the flat operator on a disc in `ℂ`.  The
reason is that for `J = stdOf T` the equation `∂̄_{J} w = ∂̄_J u` determines `w` only modulo
`J`-holomorphic functions, and the *smallest* possible sup norm of the derivative is the distance
of `(∂̄_J)^{-1}(∂̄_Ju)` from the holomorphic functions; the resulting operator is a Calderón–Zygmund
transform of order `0`, which is bounded on `L^p` and on the Hölder spaces `C^{0,α}` with `α > 0`,
but *not* on `L^∞`.  (Equivalently: `∂Δ^{-1}∂` is not bounded on `L^∞`.)  Concretely,
`‖d w‖_∞ ≲ ‖f‖_∞` fails already on the unit disc with `f` a smoothed characteristic function.

What *is* true — the classical Kohn/Hörmander small polydisc estimate, and the content of the
structure below — is that `‖d(solve u)‖_{∞,P'} ≤ C₀ · δ` where `δ` bounds the `C^{0,α}`-norm of
the datum on `P` (supremum **and** Hölder seminorm).  On a polydisc of radius `r` this bound *does*
tend to `0` with `r`, because for a `C¹` function `g` vanishing at the centre one has
`[g]_{α,P} ≤ Lip(g) r^{1-α}`; that is exactly what makes the small polydisc contraction work.

## The interface and the reduction

`DbarSolverH n J α P P'` is the analytic input; `exists_frame_of_solver` below is the whole
remaining argument (solving `∂̄_J v_j = ∂̄_J z_j` for `v_j = solve (zvec T)` and using the Neumann
series `bijective_add_of_norm_comp_lt_one` for the invertibility of the differential of the frame).
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

namespace Work.NN.Core

variable {n : ℕ}

/-- The datum `∂̄_J u_j` of a `ℂⁿ`-valued tuple is bounded in `C^{0,α}` by `δ` on `P`: a supremum
bound and a Hölder bound. -/
def DbarDataBound (J : E n → E n →L[ℝ] E n) (u : E n → Fin n → ℂ) (α : ℝ) (P : Set (E n))
    (δ : ℝ) : Prop :=
  (∀ j y, y ∈ P → ‖dbar J (fun z => u z j) y‖ ≤ δ) ∧
  (∀ j y y', y ∈ P → y' ∈ P →
    ‖dbar J (fun z => u z j) y - dbar J (fun z => u z j) y'‖ ≤ δ * ‖y - y'‖ ^ α)

lemma DbarDataBound.sup {J : E n → E n →L[ℝ] E n} {u : E n → Fin n → ℂ} {α : ℝ} {P : Set (E n)}
    {δ : ℝ} (h : DbarDataBound J u α P δ) :
    ∀ j y, y ∈ P → ‖dbar J (fun z => u z j) y‖ ≤ δ := h.1

lemma DbarDataBound.holder {J : E n → E n →L[ℝ] E n} {u : E n → Fin n → ℂ} {α : ℝ} {P : Set (E n)}
    {δ : ℝ} (h : DbarDataBound J u α P δ) :
    ∀ j y y', y ∈ P → y' ∈ P →
      ‖dbar J (fun z => u z j) y - dbar J (fun z => u z j) y'‖ ≤ δ * ‖y - y'‖ ^ α := h.2

lemma dbarDataBound_mono {J : E n → E n →L[ℝ] E n} {u : E n → Fin n → ℂ} {α : ℝ}
    {P Q : Set (E n)} {δ : ℝ} (h : DbarDataBound J u α P δ) (hQP : Q ⊆ P) :
    DbarDataBound J u α Q δ :=
  ⟨fun j y hy => h.1 j y (hQP hy), fun j y y' hy hy' => h.2 j y y' (hQP hy) (hQP hy')⟩

/-- **The small polydisc `∂̄`-estimate for an almost complex structure `J` (the analytic input).**

`solve` turns a tuple `u` of functions which are smooth on `P` into a tuple solving the same
`∂̄_J`-equation on the slightly smaller set `P'`.  If the datum `∂̄_J u_j` has `C^{0,α}`-norm at most
`δ` on `P`, then the differential of the correction is bounded by `C₀ δ` on `P'`, and smooth data
give a smooth correction.

Classically this is obtained from the Bochner–Kodaira–Nakano estimate with a strictly
plurisubharmonic weight on a small polydisc (which uses `∂̄_J ∘ ∂̄_J = 0`, i.e. the vanishing of the
Nijenhuis tensor) together with interior Schauder estimates; the structure is the *correct*
formalisation of "the `∂̄`-equation with a gain of one derivative". -/
structure DbarSolverH (n : ℕ) (J : E n → E n →L[ℝ] E n) (α : ℝ) (P P' : Set (E n)) where
  /-- the constant in the gain-of-one-derivative estimate -/
  C₀ : ℝ
  /-- the constant is nonnegative -/
  hC₀ : 0 ≤ C₀
  /-- the correction operator -/
  solve : (E n → Fin n → ℂ) → (E n → Fin n → ℂ)
  /-- `solve u` solves the same `∂̄_J`-equation as `u`, on `P'` -/
  solves : ∀ u, (∀ j, ContDiffOn ℝ ∞ (fun y => u y j) P) → ∀ j y, y ∈ P' →
    dbar J (fun z => solve u z j) y = dbar J (fun z => u z j) y
  /-- gain of one derivative, from a `C^{0,α}` bound for the datum on `P` -/
  estimate : ∀ u, (∀ j, ContDiffOn ℝ ∞ (fun y => u y j) P) → ∀ δ : ℝ, 0 ≤ δ →
    DbarDataBound J u α P δ →
    ∀ j y, y ∈ P' → ‖fderiv ℝ (fun z => solve u z j) y‖ ≤ C₀ * δ
  /-- smooth data give a smooth correction -/
  smooth : ∀ u, (∀ j, ContDiffOn ℝ ∞ (fun y => u y j) P) →
    ContDiffOn ℝ ∞ (fun y => solve u y) P'

/-- **The analytic core, normalised form, from the honest solver.**

Let `P' ⊆ P` be open, `J` a field of endomorphisms, `T : E n ≃ F n`, and suppose the datum
`∂̄_J z_j` has `C^{0,α}`-norm at most `δ` on `P` and that the small polydisc solver
`S : DbarSolverH n J α P P'` is available (with `0 ≤ α < 1`).  If `C₀ δ ‖tupleDerivInv T‖ < 1`,
then `v_j = S.solve (zvec T)_j` solves `∂̄_J v_j = ∂̄_J z_j` and `u_j = z_j - v_j` is an independent
`J`-holomorphic frame on `P'` (with `∂̄_J u_j = 0` by linearity of `∂̄_J`, so that the Nijenhuis
hypothesis is not needed at this stage: it is what makes `S` available). -/
theorem exists_frame_of_solver {n : ℕ} {T : E n ≃L[ℝ] F n} {J : E n → E n →L[ℝ] E n}
    {P P' : Set (E n)} {α : ℝ} {δ : ℝ}
    (hP'open : IsOpen P') (_h0P' : (0 : E n) ∈ P')
    (hδ : 0 ≤ δ) (hdata : DbarDataBound J (zvec T) α P δ)
    (S : DbarSolverH n J α P P')
    (hsmall : S.C₀ * δ * ‖tupleDerivInv T‖ < 1) :
    ∃ v : E n → Fin n → ℂ,
      (∀ j y, y ∈ P' → dbar J (fun z => v z j) y = dbar J (zcoord T j) y) ∧
      IsHolomorphicFrame J P' (fun j y => zcoord T j y - v y j) := by
  have hvsmT : ∀ j, ContDiffOn ℝ ∞ (fun y => zvec T y j) P :=
    fun j => (contDiff_zcoord T j).contDiffOn
  set v : E n → Fin n → ℂ := S.solve (zvec T) with hvdef
  have hsol : ∀ j y, y ∈ P' → dbar J (fun z => v z j) y = dbar J (zcoord T j) y := by
    intro j y hy
    have h := S.solves (zvec T) hvsmT j y hy
    simpa [hvdef] using h
  have hvsm_all : ContDiffOn ℝ ∞ (fun y => v y) P' := S.smooth (zvec T) hvsmT
  have hvsm : ∀ j, ContDiffOn ℝ ∞ (fun y => v y j) P' := fun j =>
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ).contDiff.comp_contDiffOn hvsm_all)
  have hdb : ∀ j y, y ∈ P' → ‖fderiv ℝ (fun z => v z j) y‖ ≤ S.C₀ * δ :=
    fun j y hy => S.estimate (zvec T) hvsmT δ hδ hdata j y hy
  refine ⟨v, hsol, ?_, ?_, ?_⟩
  · -- smoothness of `u_j = z_j - v_j`
    intro j
    exact (contDiff_zcoord T j).contDiffOn.sub (hvsm j)
  · -- `J`-holomorphicity of `u_j = z_j - v_j`
    intro j y hy w
    have hz : DifferentiableAt ℝ (zcoord T j) y :=
      ((contDiff_zcoord T j).differentiable (by simp)).differentiableAt
    have hv : DifferentiableAt ℝ (fun z : E n => v z j) y :=
      ((hvsm j).contDiffAt (hP'open.mem_nhds hy)).differentiableAt (by simp)
    have hzero : dbar J (fun z : E n => zcoord T j z - v z j) y = 0 := by
      have h := dbar_sub J (zcoord T j) (fun z => v z j) y hz hv
      rw [h, (hsol j y hy).symm, sub_self]
    exact ((dbar_eq_zero_iff J (fun z : E n => zcoord T j z - v z j) y).mp hzero) w
  · -- invertibility of the differential of the tuple
    intro y hy
    have h1 : fderiv ℝ (fun y : E n => fun j => zcoord T j y) y = tupleDeriv T :=
      fderiv_zvec T y
    have h2 : fderiv ℝ (fun y : E n => fun j => v y j) y
        = ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y) :=
      fderiv_pi (fun j => ((hvsm j).contDiffAt (hP'open.mem_nhds hy)).differentiableAt (by simp))
    have hztup : DifferentiableAt ℝ (fun y : E n => fun j => zcoord T j y) y :=
      ((contDiff_zvec T).differentiable (by simp)).differentiableAt
    have hvtup : DifferentiableAt ℝ (fun y : E n => fun j => v y j) y :=
      ((hvsm_all.contDiffAt (hP'open.mem_nhds hy)).differentiableAt (by simp))
    have hfd : fderiv ℝ (fun y : E n => fun j => zcoord T j y - v y j) y
        = tupleDeriv T + (-(ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y))) := by
      rw [show (fun y : E n => fun j => zcoord T j y - v y j)
          = ((fun y : E n => fun j => zcoord T j y) - (fun y : E n => fun j => v y j)) from rfl,
        fderiv_sub hztup hvtup, h1, h2]
      abel
    rw [hfd]
    refine bijective_add_of_norm_comp_lt_one (tupleDeriv T) (tupleDerivInv T)
      (tupleDeriv_comp T).1 (tupleDeriv_comp T).2
      (-(ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y))) ?_
    rw [ContinuousLinearMap.comp_neg, norm_neg]
    have hpi : ‖ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y)‖
        ≤ S.C₀ * δ := by
      refine ContinuousLinearMap.norm_pi_le_of_le (fun j => hdb j y hy) ?_
      exact mul_nonneg S.hC₀ hδ
    have hmain : ‖(tupleDerivInv T).comp
        (ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y))‖
        ≤ S.C₀ * δ * ‖tupleDerivInv T‖ := by
      calc ‖(tupleDerivInv T).comp
            (ContinuousLinearMap.pi (fun j => fderiv ℝ (fun z => v z j) y))‖
          ≤ ‖tupleDerivInv T‖ * ‖ContinuousLinearMap.pi
              (fun j => fderiv ℝ (fun z => v z j) y)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖tupleDerivInv T‖ * (S.C₀ * δ) :=
            mul_le_mul_of_nonneg_left hpi (norm_nonneg _)
        _ = S.C₀ * δ * ‖tupleDerivInv T‖ := by ring
    exact lt_of_le_of_lt hmain hsmall

end Work.NN.Core
