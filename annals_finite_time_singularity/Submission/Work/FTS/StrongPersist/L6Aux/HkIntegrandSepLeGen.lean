/-
Copyright: work module for the Elgindi finite-time singularity project.

# Separation of variables for the `ℋ^k`-integrand of a product `C(θ)·B(z)`

`Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen`: for **every** `k` and every `θ ∈ Iθ` the
`ℋ^k`-integrand of the separated function `(z,θ) ↦ C θ · B z` is dominated by the product of
the two one-dimensional blocks, with an *explicit* constant `1`:

  `HkIntegrand α k (C·B) z θ ≤ (C θ²·sin(2θ)^{-η} + Σ_{1≤i≤k} (D_θ^i C θ)²·sin(2θ)^{-γ})`
                              `· (Σ_{0≤q≤k} (D_z^q B z)²·w(z)²)`.

This is the `k`-general version of the `k = 3` sibling
`Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le`; the argument is identical, the sums simply
run up to `k` instead of `3` (every ingredient — `mixedSepDecomp`, `sep_sq1`, `sep_sq2`,
`sliceZ_DzIter` — is already stated for an arbitrary number of derivatives).

## The argument

Everything rests on the separation of variables `mixedSepDecomp`
(`Submission/Work/FTS/Nonlinear/Pieces/RNP/row15aux/mixedSepDecomp.lean`) for the mixed
`D`-operators: for a product of a `θ`-only and a `z`-only function,
`D_z^lD_θ^m (C·B) z θ = (dthU^[m] C) θ · (OpZ^[l] B) z`, together with the two "separated
square" `rpow` identities `Work.FTS.LocData.sep_sq1` / `sep_sq2`
(`Submission/Work/FTS/LocData/hLoc_hk.lean`): every summand of the integrand factorises into
its radial block `(D_z^q B z · w z)²` and its angular block
`(D_θ^i C θ)²·sin(2θ)^{-e}` (with `e = η` for the pure `D_z`-summands and `e = γ` for the
mixed ones).

Two elementary bookkeeping steps remain:

* the pure `D_z`-summands reproduce **exactly** the first term
  `C θ²·sin(2θ)^{-η} · Σ_q (D_z^q B z)²·w(z)²` of the right-hand side;
* the mixed summands are a *sub*-sum of `(Σ_i (D_θ^i C θ)²·sin(2θ)^{-γ}) · (Σ_q …)`: the
  index constraint `1 ≤ i ∧ i + j ≤ k` of the integrand only deletes nonnegative terms from
  the full product of the two sums (no term is bounded away), so the inequality holds with
  constant `1` — no Cauchy–Schwarz is needed.

The index `q` in `DzIter q (fun z' _ => B z') z 0` is the θ-independent radial operator
`OpZ^[q] B` (`Work.Spaces.sliceZ_DzIter`), so the `z 0`-evaluation is immaterial.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp
import Submission.Work.FTS.LocData.hLoc_hk
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem HkIntegrandSepLeGen {α : ℝ} {k : ℕ} {C : ℝ → ℝ} {B : ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z' θ' => C θ' * B z') z θ
      ≤ ((C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + ∑ i ∈ Finset.range (k + 1),
              (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- ### Separation of variables for the pure `D_z`- and the mixed derivatives
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z' θ' => C θ' * B z') z θ
      = C θ * (Work.Spaces.OpZ^[i] B) z := by
    intro i
    have h := Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp i 0 C B z θ
    rw [Work.Spaces.mixed_zero_right] at h
    simpa using h
  have hMx : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z' θ' => C θ' * B z') z θ
      = (Work.Spaces.dthU^[i] C) θ * (Work.Spaces.OpZ^[j] B) z := by
    intro j i
    simpa using Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp j i C B z θ
  -- the radial factor of the right-hand side is `OpZ^[q] B z`, independently of `θ`
  have hDzB : ∀ q : ℕ, Work.Spaces.DzIter q (fun z' _ => B z') z 0
      = (Work.Spaces.OpZ^[q] B) z := by
    intro q
    rw [← congrFun (Work.Spaces.sliceZ_DzIter q (fun z' _ => B z') 0) z]
  -- ### Unfold the integrand
  rw [Work.Spaces.HkIntegrand]
  simp only [hDz, hMx, hDzB]
  -- ### The angular variable and the two weight identities
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Work.FTS.LocData.sin_two_nonneg hθ
  have hWt : Work.Spaces.Wt α z θ = Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef]
  have hgamma : ∀ i : ℕ, 0 ≤ (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
      * s ^ (-(Work.Spaces.gam α)) else 0) := by
    intro i
    split_ifs with h
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · exact le_refl 0
  have hbq : ∀ q : ℕ, 0 ≤ ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### The pure `D_z`-summands reproduce the first term of the right-hand side exactly
  have hP : (∑ i ∈ Finset.range (k + 1),
        (C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        * (∑ q ∈ Finset.range (k + 1),
            ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show C θ * (Work.Spaces.OpZ^[i] B) z * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        = (Work.Spaces.OpZ^[i] B) z * C θ * (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2))
        by ring,
      Work.FTS.LocData.sep_sq1 ((Work.Spaces.OpZ^[i] B) z) (C θ) (Work.Spaces.w z) s
        (Work.Spaces.eta) hs0]
    ring
  rw [hP]
  -- ### The mixed summands are dominated by the product of the two sums
  have hQ : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
            * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
        * (∑ q ∈ Finset.range (k + 1),
            ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have hQ1 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                  * s ^ (-(Work.Spaces.gam α)) else 0)
                * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              else 0) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h.1, hWt]
        rw [show Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)))
            = (Work.Spaces.OpZ^[j] B) z * (Work.Spaces.dthU^[i] C θ)
              * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2))) by ring,
          Work.FTS.LocData.sep_sq2 ((Work.Spaces.OpZ^[j] B) z) (Work.Spaces.dthU^[i] C θ)
            (Work.Spaces.w z) s (Work.Spaces.gam α) hs0]
        ring
      · rw [ite_eq_right h, ite_eq_right h]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.dthU^[i] C θ * (Work.Spaces.OpZ^[j] B) z
              * Work.Spaces.Wt α z θ) ^ 2
            else 0))
        = _ := hQ1
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
                * s ^ (-(Work.Spaces.gam α)) else 0)
              * (((Work.Spaces.OpZ^[j] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          by_cases h : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left h]
          · rw [ite_eq_right h]
            exact mul_nonneg (hgamma i) (hbq j)
      _ = (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
              * s ^ (-(Work.Spaces.gam α)) else 0))
            * (∑ q ∈ Finset.range (k + 1),
                ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  -- ### Assemble
  have hR : (C θ ^ 2 * s ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
      * (∑ q ∈ Finset.range (k + 1), ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = C θ ^ 2 * s ^ (-(Work.Spaces.eta))
          * (∑ q ∈ Finset.range (k + 1),
              ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
          * (∑ q ∈ Finset.range (k + 1),
              ((Work.Spaces.OpZ^[q] B) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [add_mul]
  rw [hR]
  exact add_le_add (le_refl _) hQ

end Work.FTS.StrongPersist.L6Aux
