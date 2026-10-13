import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef_sum_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false

/-!
# The Stirling expansion of `D_z^n` from `DifferentiableOn`-hypotheses on an open set

The operators `D_z = z ∂_z` and `∂_z` satisfy the commutation relation
`∂_z ∘ D_z = D_z ∘ ∂_z + ∂_z`, so that

`D_z^n f = ∑_{k=0}^{n} S(n,k) z^k ∂_z^k f`

with `S(n,k) = Work.Spaces.scoef n k` the Stirling numbers of the second kind.  The
existing statements of this expansion (`Work.Spaces.DzIter_eq_sum_scoef`,
`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`, …) all require the `z`-slice to be
`C^∞` (or `C^∞` on a half-line).  This file proves the expansion in the minimal
form needed by the finite-order interior estimates: it suffices that the slices
`z ↦ pzIter k h z θ`, `k ≤ n`, are *differentiable on an open set* `U`, and the
identity then holds at every point of `U`.  The proof is the usual induction on
`n`: the induction hypothesis holds on a neighbourhood of the point (openness),
and the induction step differentiates the sum term by term with the product rule.
-/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step: the extra factor `z`
produced by `D_z` from the derivative of `z^k`. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- `deriv` of the `k`-th iterated `z`-derivative of the `z`-slice: this is the
definition of `pzIter`, so nothing has to be proved. -/
private theorem deriv_pzIter_slice (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` from `DifferentiableOn`-hypotheses on an open
set** (helper form, with `n` generalized so that the induction is clean). -/
private theorem DzIter_eq_sum_scoef_diffOn_aux {h : ℝ → ℝ → ℝ} {θ : ℝ} {U : Set ℝ}
    (hU : IsOpen U) :
    ∀ n : ℕ, (∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U) →
      ∀ z ∈ U, Work.Spaces.DzIter n h z θ
        = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
            * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro _ z _
    simp [Work.Spaces.DzIter, Work.Spaces.scoef]
  | succ n ih =>
    intro hd z hz
    -- the induction hypothesis applies with the hypotheses up to order `n`
    have hd' : ∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U :=
      fun k hk => hd k (Nat.le_succ_of_le hk)
    have hnhds : U ∈ 𝓝 z := hU.mem_nhds hz
    -- differentiability at the point `z`, which is interior to `U`
    have hdiff : ∀ k ≤ n + 1,
        DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z :=
      fun k hk => (hd k hk).differentiableAt hnhds
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ, k ≤ n →
        DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
      fun k hk => (hd1 k).mul (hdiff k (Nat.le_succ_of_le hk))
    -- the induction hypothesis, as an eventual equality near `z`
    have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
      filter_upwards [hnhds] with z' hz'
      exact ih hd' z' hz'
    -- the derivative of each summand
    have hterm : ∀ k : ℕ, k ≤ n →
        deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
            * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
        = (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
            + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      intro k hk
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
        (Work.Spaces.scoef n k : ℝ) (hd3 k hk)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k)
        (hdiff k (Nat.le_succ_of_le hk))
      have hmul' : deriv (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * Work.Spaces.pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow, deriv_pzIter_slice]
    -- differentiate the whole sum
    have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (Work.Spaces.scoef n k : ℝ)
                * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk =>
        (hd3 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul
          (Work.Spaces.scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk =>
        hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    calc Work.Spaces.DzIter (n + 1) h z θ
        = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
          simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
              + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : z * ((Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
              = (Work.Spaces.scoef n k : ℝ)
                * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term]
      _ = ∑ j ∈ Finset.range (n + 2),
            (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

theorem DzIter_eq_sum_scoef_diffOn {h : ℝ → ℝ → ℝ} {θ : ℝ} {U : Set ℝ} {n : ℕ}
    (hU : IsOpen U)
    (hd : ∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U) :
    ∀ z ∈ U, Work.Spaces.DzIter n h z θ
      = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k h z θ) :=
  DzIter_eq_sum_scoef_diffOn_aux hU n hd

end Work.FTS.EllipticEst.Cores.DiagEstEllT
