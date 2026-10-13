import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.scoef
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.FTS.GalBasis.GalDense.Xmb

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

open scoped Real Topology ContDiff
open Set Filter

noncomputable section

set_option autoImplicit false

/-!
# The Stirling expansion of `D_z^n` from `C^n` on an open set

`D_z = z ∂_z` and `∂_z` satisfy `∂_z ∘ D_z = D_z ∘ ∂_z + ∂_z`, so that

`D_z^n f = ∑_{k = 0}^{n} S(n,k) z^k ∂_z^k f`

with `S(n,k) = Work.Spaces.scoef n k` the Stirling numbers of the second kind.

The existing statements of this expansion ask for more differentiability than is needed:
`Work.Spaces.DzIter_eq_sum_scoef` wants the `z`-slice to be analytic, and
`Work.FTS.GalBasis.Xmb.DzIter_eq_sum_scoef_of_contDiffOn` wants `C^{n+1}` on the open set.
Here the hypothesis is exactly `C^n` on an open set `U ⊆ ℝ × ℝ`, which is what the
finite-order `C⁶`-interior machinery has available.

The induction is the usual one.  At level `n + 1` on the open set `U` we differentiate the
level-`n` expansion, which needs each `z ↦ ∂_z^k h(z,θ)`, `k ≤ n`, to be differentiable;
`C^{n+1}` supplies this (`k + 1 ≤ n + 1`), and `C^{n+1}` restricts to `C^n` for the
induction hypothesis.
-/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- `deriv` of the `k`-th iterated `z`-derivative of a `z`-slice is the `(k+1)`-st one. -/
private theorem deriv_pzIter_slice (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` in the genuine smooth order**: for `h` of class
`C^n` on an open set `U ⊆ ℝ × ℝ`,
`D_z^n h = ∑_{k ≤ n} S(n,k) z^k ∂_z^k h` on `U`. -/
theorem DzIter_eq_sum_scoef_of_contDiffOn_order {h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry h) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DzIter n h z θ
          = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
      intro _ z θ _
      rw [Finset.sum_range_one, show Work.Spaces.scoef 0 0 = 1 from rfl]
      norm_num
  | succ n ih =>
      intro hsm z θ hzθ
      -- the hypothesis of the induction hypothesis: `C^n ⊂ C^{n+1}`
      have hsm' : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry h) U :=
        hsm.of_le (Nat.cast_le.mpr (show n ≤ n + 1 by omega))
      -- differentiability of the `z`-slices of the iterated `z`-derivatives at `z`
      have hdiff : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k hk =>
        Work.FTS.GalBasis.Xmb.differentiableAt_slice_pzIter hU hsm (i := k) (by omega) hzθ
      have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
        differentiableAt_pow k
      have hd3 : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
        fun k hk => (hd1 k).mul (hdiff k hk)
      -- the induction hypothesis, as an eventual equality near `z`
      have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
        have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
          hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
        exact hopen.mem_nhds hzθ
      have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
          =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        filter_upwards [hsl] with z' hz'
        exact ih hsm' z' θ hz'
      -- the derivative of each summand
      have hterm : ∀ k : ℕ, k ≤ n →
          deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
              * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
            = (Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                    + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        intro k hk
        rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
          (Work.Spaces.scoef n k : ℝ) ((hd1 k).mul (hdiff k hk))]
        congr 1
        have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
          (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k) (hdiff k hk)
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
                fun z' => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
          funext z'
          simp [Finset.sum_apply]
        rw [hsumfun, deriv_sum (fun k hk => (hd3 k
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul (Work.Spaces.scoef n k : ℝ))]
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
            rw [show z * ((Work.Spaces.scoef n k : ℝ)
                  * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
                = (Work.Spaces.scoef n k : ℝ)
                  * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) from by ring,
              z_mul_term]
        _ = ∑ j ∈ Finset.range (n + 2),
              (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
            Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

end

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
