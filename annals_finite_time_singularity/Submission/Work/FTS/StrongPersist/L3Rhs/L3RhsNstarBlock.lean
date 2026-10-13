/-
# `Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock` — the `ℋ³` block estimate for `N_*`

This is the `N_*`-block of the level-three right-hand side of the modulated `g`-equation
(`Work.FTS.StrongPersist.L3RhsPriced`).  The linear part of the right-hand side is

  `Nstar μ lam f = -μ f - (μ + lam + μλ) D_z f`     (`Work.Construction.Nstar`),

a *linear combination of the profile `f` and of `D_z f = z ∂_z f` with scalar coefficients*.
The block estimate is therefore the honest `ℋ³`-closure of the class `H6Adm α` under this
two-term combination, with coefficients controlled by the modulation parameters
(`|μ| ≤ 1/2`, `|lam| ≤ 1`):

  `SmoothOpen (N_*)`, `HkMem α 3 (N_*)`, `HkNorm α 3 (N_*) ≤ C (1 + |f|_{ℋ⁴})`.

Everything is uniform in `α ∈ (0,1]`, and the constant `C = 5√2/2` is absolute.

## The two mathematical contents

1. **The index shift `D_z` costs one `ℋ`-order.**  For `f ∈ C⁴` on the open quadrant and
   `f ∈ ℋ⁴`, the level-three integrand of `D_z f` is a sub-sum of the level-four integrand
   of `f` (the pure summands by the definitional shift `D_z^i (D_z f) = D_z^{i+1} f`, the
   mixed summands by the Clairaut identity `mixed b a (D_z f) = mixed (b+1) a f`), so

     `HkSq α 3 (D_z f) ≤ HkSq α 4 f`,   `HkMem α 3 (D_z f)`

   (`Transfer.HkSq_Dz_le_Q0Sm`, `Transfer.HkMem_descent_Q0Sm`).  This is the only place where
   the hypothesis `H6Adm` (hence `ℋ⁶` and `C^∞` on the open quadrant) is used beyond its
   `ℋ⁴`- and `ℋ³`-consequences.

2. **The triangle inequality of the weighted norm.**  Writing `N_* = A + B` with
   `A = -μ f` and `B = -(μ+λ+μλ) D_z f`, both summands are `SmoothOpen`, in `ℋ³`, and

     `|N_*|_{ℋ³} ≤ √2 (|A|_{ℋ³} + |B|_{ℋ³}) = √2 (|μ| |f|_{ℋ³} + |μ+λ+μλ| |D_z f|_{ℋ³})`

   (`EllipticEst.HkNorm_add_le`), with `|f|_{ℋ³}, |D_z f|_{ℋ³} ≤ |f|_{ℋ⁴} ≤ M` and
   `|μ| ≤ 1/2`, `|μ+λ+μλ| ≤ |μ| + |λ| + |μ||λ| ≤ 2`; hence `|N_*|_{ℋ³} ≤ (5√2/2) M`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.Uop_bound_reg
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option linter.unusedVariables false

theorem L3RhsNstarBlock : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (μ lam M : ℝ),
    Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
    |μ| ≤ 1 / 2 → |lam| ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar μ lam f) ∧
    Work.Spaces.HkMem α 3 (Work.Construction.Nstar μ lam f) ∧
    Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f) ≤ C * (1 + M) := by
  refine ⟨5 * Real.sqrt 2 / 2, ?_, ?_⟩
  · have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · intro α hα f μ lam M hf hM hμ hlam
    have hα0 : 0 < α := hα.1
    -- the regularity of the datum
    have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
    have hmem6 : Work.Spaces.HkMem α 6 f := hf.reg.2
    have hmem4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem6
    have hmem3 : Work.Spaces.HkMem α 3 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 3 (by norm_num) hmem6
    have hQ0Sm4 : Work.FTS.CoercivityFix.Transfer.Q0Sm 4 f := hsm.forall 4
    -- `D_z f` is in `ℋ³` (the index shift)
    have hmem3Dz : Work.Spaces.HkMem α 3 (Work.Spaces.Dz f) :=
      (Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα0 3 hQ0Sm4 hmem4).2.2
    have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hsm.Dz
    -- the two summands of `N_*`
    have hsmA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-μ) * f z θ) :=
      Work.FTS.EllipticEst.smoothOpen_const_mul' (-μ) hsm
    have hsmB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.EllipticEst.smoothOpen_const_mul' _ hsmDz
    have hmA : Work.Spaces.HkMem α 3 (fun z θ => (-μ) * f z θ) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of (-μ) hmem3
    have hmB : Work.Spaces.HkMem α 3
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of _ hmem3Dz
    -- the decomposition `N_* = A + B`
    have hsum : (fun z θ => (-μ) * f z θ
          + (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
        = Work.Construction.Nstar μ lam f := by
      funext z θ
      simp only [Work.Construction.Nstar]
      ring
    have hsmN : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar μ lam f) := by
      rw [← hsum]
      exact Work.FTS.EllipticEst.smoothOpen_add hsmA hsmB
    have hmN : Work.Spaces.HkMem α 3 (Work.Construction.Nstar μ lam f) := by
      rw [← hsum]
      exact Work.FTS.EllipticEst.HkMem_add_open hsmA hsmB hmA hmB
    refine ⟨hsmN, hmN, ?_⟩
    -- the norm bound
    have hXn : Work.Spaces.HkNorm α 4 f ≤ M := hM
    have hMnn : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn
    have hN01 : Work.Spaces.HkNorm α 3 f ≤ Work.Spaces.HkNorm α 4 f := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt
        (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem4)
    have hN0Dz : Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) ≤ Work.Spaces.HkNorm α 4 f := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt
        (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 3 hQ0Sm4 hmem4)
    have hnormA : Work.Spaces.HkNorm α 3 (fun z θ => (-μ) * f z θ)
        = |μ| * Work.Spaces.HkNorm α 3 f := by
      have heq : (fun z θ => (-μ) * f z θ) = (-μ) • f := by
        funext z θ; simp
      rw [heq, Work.FTS.EllipticEst.HkNorm_smul]
      simp
    have hnormB : Work.Spaces.HkNorm α 3
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
        = |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) := by
      have heq : (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
          = (-(μ + lam + μ * lam)) • Work.Spaces.Dz f := by
        funext z θ; simp
      rw [heq, Work.FTS.EllipticEst.HkNorm_smul, abs_neg]
    have hmain : Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
        ≤ Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
            + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)) := by
      rw [← hsum]
      have h := Work.FTS.EllipticEst.HkNorm_add_le α 3
        (fun n => hsmA.forall n) (fun n => hsmB.forall n) hmA hmB
      rw [hnormA, hnormB] at h
      exact h
    -- the coefficient bounds
    have hcoef : |μ + lam + μ * lam| ≤ 2 := by
      have h1 : |μ| ≤ 1 / 2 := hμ
      have h2 : |lam| ≤ 1 := hlam
      have h3 : |μ * lam| ≤ 1 / 2 := by
        rw [abs_mul]; nlinarith [abs_nonneg μ, abs_nonneg lam]
      calc |μ + lam + μ * lam| ≤ |μ + lam| + |μ * lam| := abs_add_le _ _
        _ ≤ (|μ| + |lam|) + |μ * lam| := by linarith [abs_add_le μ lam]
        _ ≤ 2 := by linarith
    have hfin : Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
        ≤ 5 * Real.sqrt 2 / 2 * (1 + M) := by
      have h1 : Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
            + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f))
          ≤ Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
            + 2 * Work.Spaces.HkNorm α 4 f) := by
        have hA : |μ| * Work.Spaces.HkNorm α 3 f ≤ (1 / 2) * Work.Spaces.HkNorm α 4 f := by
          have h0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 3 f := Work.Spaces.HkNorm_nonneg α 3 f
          nlinarith [hN01, hμ, Work.Spaces.HkNorm_nonneg α 4 f]
        have hB : |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)
            ≤ 2 * Work.Spaces.HkNorm α 4 f := by
          have h0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) :=
            Work.Spaces.HkNorm_nonneg α 3 (Work.Spaces.Dz f)
          nlinarith [hN0Dz, hcoef, Work.Spaces.HkNorm_nonneg α 4 f]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      have h2 : Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
            + 2 * Work.Spaces.HkNorm α 4 f)
          ≤ Real.sqrt 2 * ((5 / 2) * M) := by
        have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h3 : (1 / 2) * Work.Spaces.HkNorm α 4 f + 2 * Work.Spaces.HkNorm α 4 f
            = (5 / 2) * Work.Spaces.HkNorm α 4 f := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left (by linarith) hs2
      calc Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
          ≤ Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
              + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)) := hmain
        _ ≤ Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
              + 2 * Work.Spaces.HkNorm α 4 f) := h1
        _ ≤ Real.sqrt 2 * ((5 / 2) * M) := h2
        _ = 5 * Real.sqrt 2 / 2 * M := by ring
        _ ≤ 5 * Real.sqrt 2 / 2 * (1 + M) := by
            have h5 : (0 : ℝ) ≤ 5 * Real.sqrt 2 / 2 := by positivity
            nlinarith [hMnn, Real.sqrt_nonneg 2]
    exact hfin

end Work.FTS.StrongPersist.L3Rhs
