/-
# `Work.FTS.LocData.DzIter_oneSubChi_bound` — the iterated `D_z`-derivatives of `1 - χ(·/L)`

The complementary far factor of the localisation chapter is `1 - χ(z/L)`
(with `χ = Work.Stability.chi` the cut-off of `Submission/Work/Stability/Cutoff.lean`):
it is the profile of the *far part* of the constant function,
`Work.Stability.zfar L (fun _ _ => 1) = 1 - χ(z/L)`.

This file proves that its iterated `D_z = z ∂_z` derivatives are **uniformly bounded**
on the quadrant `z ≥ 0`, for all orders `c ≤ 4` and all scales `L ≥ 1`.

The argument has three layers.

* **Dilation.**  The dilation `z ↦ z/L` turns `z^k ∂_z^k` into `(z/L)^k ∂_x^k`:
  `iteratedDeriv k (fun x => m (x/L)) z = (L⁻¹)^k · iteratedDeriv k m (z/L)`
  (`IteratedDeriv_comp_div`, a corollary of Mathlib's `iteratedDeriv_comp_const_mul`).
  This is what makes the bound *uniform in `L`*.
* **Stirling expansion.**  `DzIterZ j m = ∑_{k≤j} S(j,k) z^k ∂_z^k m`
  (`DzIterZ_eq_sum_scoef`), with `S(j,k) = Work.Spaces.scoef j k` the Stirling numbers of
  the second kind.  (The sibling `Work.Spaces.DzIter_eq_sum_scoef` states this for
  two-variable functions but with the *analyticity* hypothesis `ContDiffOn ℝ ⊤`, which a
  cut-off does not satisfy; the version here needs only genuine `C^∞`-smoothness,
  `Work.Stability.smoothOrder`.)
* **The weighted derivatives of `1 - χ`.**  `x ↦ x^k ∂_x^k (1 - χ)` is continuous and, for
  `k ≥ 1`, supported in `|x| ≤ 2` (`χ = 1` on `[-1,1]` and `χ = 0` off `(-2,2)`), hence
  bounded (`OneSubChi_deriv_bound`).

Assembling: for `c ≤ 4` the `c`-th `D_z`-iterate of `1 - χ(·/L)` is the Stirling combination
of the bounded quantities `(z/L)^k ∂_x^k(1 - χ)(z/L)`, `k ≤ c ≤ 4`, and
`∑_{k≤c} S(c,k) = bell c ≤ 100`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.pz_aux
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option linter.unusedVariables false

/-! ## 1. The chain rule for a dilation -/

/-- **The iterated derivative of a dilation.**  For a smooth `m` and `L ≠ 0`,
`(∂^k (m(·/L)))(z) = (L⁻¹)^k (∂^k m)(z/L)`: differentiating `m (L⁻¹ ·)` `k` times pulls
out `k` factors of `L⁻¹`. -/
theorem IteratedDeriv_comp_div (m : ℝ → ℝ) (hm : ContDiff ℝ Work.Stability.smoothOrder m)
    {L : ℝ} (hL : L ≠ 0) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun x => m (x / L)) x = (L⁻¹) ^ k * iteratedDeriv k m (x / L) := by
  have h1 : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) m := hm.of_le (by simp)
  have h2 := iteratedDeriv_comp_const_mul (f := m) (c := L⁻¹) (n := k) h1
  have h3 : iteratedDeriv k (fun x => m (x / L))
      = fun x => (L⁻¹) ^ k * iteratedDeriv k m (x / L) := by
    simpa only [div_eq_mul_inv, mul_comm] using h2
  exact congrFun h3 x

/-! ## 2. The Stirling expansion of the iterated operator `D_z = z ∂_z`

The algebra of one step of the induction: multiplying by `z` converts `k z^{k-1} A + z^k B`
(the derivative of `z^k A`) into `k z^k A + z^{k+1} B`.  This is the identity underlying the
Pascal recursion of the Stirling numbers. -/

private theorem z_mul_weighted (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | n
  · ring
  · rw [pow_succ]; push_cast; ring

/-- `∂_z (z^k) = k z^{k-1}`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) :=
  (hasDerivAt_pow k z).deriv

/-- **The expansion of `D_z^j` in terms of the Stirling numbers of the second kind.**
For a smooth `m : ℝ → ℝ`, `DzIterZ j m = ∑_{k≤j} S(j,k) · z^k · ∂^k m`, with
`S(j,k) = Work.Spaces.scoef j k`.

This is the one-variable counterpart of `Work.Spaces.DzIter_eq_sum_scoef`, which is phrased
with the (unusable for a cut-off) analyticity hypothesis `ContDiffOn ℝ ⊤`; here
`Work.Stability.smoothOrder` — genuine `C^∞`-smoothness on all of `ℝ` — is enough. -/
theorem DzIterZ_eq_sum_scoef (m : ℝ → ℝ) (hm : ContDiff ℝ Work.Stability.smoothOrder m) :
    ∀ j : ℕ, Work.Coercivity.CommutZ.DzIterZ j m =
      fun z => ∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * iteratedDeriv k m z) := by
  intro j
  induction j with
  | zero =>
    funext z
    show m z = ∑ k ∈ Finset.range (0 + 1),
      (Work.Spaces.scoef 0 k : ℝ) * (z ^ k * iteratedDeriv k m z)
    simp [Work.Spaces.scoef]
  | succ j ih =>
    rw [Work.Coercivity.CommutZ.DzIterZ_succ, ih]
    funext z
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (iteratedDeriv k m) z := fun k => by
      have h₁ : ContDiff ℝ ((k + 1 : ℕ∞) : WithTop ℕ∞) m := hm.of_le (by simp)
      exact (h₁.differentiable_iteratedDeriv' k).differentiableAt
    -- the derivative of the `j`-th sum, term by term
    have hsumfun : (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z'))
        = (∑ k ∈ Finset.range (j + 1),
            fun z' : ℝ => (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) := by
      funext z'
      simp [Finset.sum_apply]
    have hderiv : deriv (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) z
        = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z) := by
      rw [hsumfun, deriv_sum (fun k hk => ?_)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [deriv_const_mul_field (Work.Spaces.scoef j k : ℝ)]
        congr 1
        have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
          (d := fun z' : ℝ => iteratedDeriv k m z') (differentiableAt_pow k) (hdiff k)
        have hmul' : deriv (fun z' : ℝ => z' ^ k * iteratedDeriv k m z') z
            = deriv (fun z' : ℝ => z' ^ k) z * iteratedDeriv k m z
              + z ^ k * deriv (fun z' : ℝ => iteratedDeriv k m z') z := hmul
        rw [hmul', deriv_zpow,
          show deriv (fun z' : ℝ => iteratedDeriv k m z') z = iteratedDeriv (k + 1) m z from
            (congrFun (iteratedDeriv_succ (n := k) (f := m)) z).symm]
        try ring
      · exact ((differentiableAt_pow k).mul (hdiff k)).const_mul (Work.Spaces.scoef j k : ℝ)
    -- multiply by `z` and collect the terms
    have hzeq : z * deriv (fun z' : ℝ => ∑ k ∈ Finset.range (j + 1),
          (Work.Spaces.scoef j k : ℝ) * (z' ^ k * iteratedDeriv k m z')) z
        = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ k * iteratedDeriv k m z + z ^ (k + 1) * iteratedDeriv (k + 1) m z) := by
      rw [hderiv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [show z * ((Work.Spaces.scoef j k : ℝ) *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z))
          = (Work.Spaces.scoef j k : ℝ) * (z *
            ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k m z + z ^ k * iteratedDeriv (k + 1) m z))
          from by ring, z_mul_weighted]
    rw [hzeq]
    have hshift := Work.Spaces.scoef_sum_shift j (fun k => iteratedDeriv k m z) z
    simpa only [] using hshift

/-! ## 3. The weighted derivatives of `1 - χ` are bounded -/

/-- **The weighted derivatives of `1 - χ` are bounded.**  There is a constant `M` dominating
`|x^k ∂_x^k (1 - χ)(x)|` for all `k ≤ 4` and all `x : ℝ`.

For `k = 0` this is `0 ≤ 1 - χ x ≤ 1`.  For `k ≥ 1` the function
`x ↦ x^k (1 - χ)^{(k)}(x) = -x^k χ^{(k)}(x)` is continuous (χ is `C^∞`) and supported in
`|x| ≤ 2` (χ is `1` on `[-1,1]` and `0` off `(-2,2)`), hence bounded. -/
theorem OneSubChi_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 4, ∀ x : ℝ,
      |x ^ k * iteratedDeriv k (fun x => (1 : ℝ) - Work.Stability.chi x) x| ≤ M := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have key : ∀ k ≤ 4, ∃ Mk : ℝ, 0 ≤ Mk ∧
      ∀ x : ℝ, |x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x| ≤ Mk := by
    intro k hk4
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · -- `k = 0`: the bound `|1 - χ x| ≤ 1`
      subst h0
      refine ⟨1, zero_le_one, fun x => ?_⟩
      have hxg : iteratedDeriv 0 (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
          = 1 - Work.Stability.chi x :=
        congrFun (iteratedDeriv_zero (f := fun x : ℝ => (1 : ℝ) - Work.Stability.chi x)) x
      rw [hxg]
      simp only [pow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Work.Stability.chi_le_one x]
      · linarith [Work.Stability.chi_nonneg x]
    · -- `k ≥ 1`: continuity on the compact set `[-2,2]` plus vanishing off `(-2,2)`
      have hcont : Continuous (fun x : ℝ =>
          x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x) :=
        (continuous_id.pow k).mul (hsm.continuous_iteratedDeriv k (by simp))
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := fun x : ℝ => x ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x)
        hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      by_cases hx : |x| ≤ 2
      · have hxmem : x ∈ Set.Icc (-2 : ℝ) 2 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx
        have hbound := hC x hxmem
        rw [Real.norm_eq_abs] at hbound
        exact le_trans hbound (le_max_left _ _)
      · -- `|x| > 2`: `χ ≡ 0` on a neighbourhood of `x`, so all its derivatives vanish there
        have hx2 : 2 < |x| := not_le.mp hx
        have hvan : iteratedDeriv k Work.Stability.chi x = 0 := by
          have hev : Work.Stability.chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
            have hmem : ∀ᶠ y in 𝓝 x, 2 < |y| :=
              (isOpen_lt continuous_const continuous_abs).mem_nhds (by simpa using hx2)
            filter_upwards [hmem] with y hy
            exact Work.Stability.chi_eq_zero (le_of_lt hy)
          rw [hev.iteratedDeriv_eq k, Work.Spaces.iteratedDeriv_zero_fun k x]
        have hgk : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) x
            = - iteratedDeriv k Work.Stability.chi x := by
          rw [iteratedDeriv_const_sub hpos (1 : ℝ)]
          simp
        rw [hgk, hvan]
        simp
  obtain ⟨M0, hM00, hM0⟩ := key 0 (by norm_num)
  obtain ⟨M1, hM10, hM1⟩ := key 1 (by norm_num)
  obtain ⟨M2, hM20, hM2⟩ := key 2 (by norm_num)
  obtain ⟨M3, hM30, hM3⟩ := key 3 (by norm_num)
  obtain ⟨M4, hM40, hM4⟩ := key 4 (by norm_num)
  refine ⟨M0 + M1 + M2 + M3 + M4, by linarith, fun k hk4 x => ?_⟩
  interval_cases k
  · exact le_trans (hM0 x) (by linarith)
  · exact le_trans (hM1 x) (by linarith)
  · exact le_trans (hM2 x) (by linarith)
  · exact le_trans (hM3 x) (by linarith)
  · exact le_trans (hM4 x) (by linarith)

/-! ## 4. The target estimate -/

theorem DzIter_oneSubChi_bound (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ C := by
  obtain ⟨M, hM0, hMb⟩ := OneSubChi_deriv_bound
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- smoothness of the two cut-off factors
  have hsmg : ContDiff ℝ Work.Stability.smoothOrder (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have hsmL : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) :=
    hsmg.comp (contDiff_id.div_const L)
  refine ⟨100 * M, fun c hc z hz θ => ?_⟩
  -- 1. the θ-independent function is a `z`-only multiplier
  have h1 : Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ
      = Work.Coercivity.CommutZ.DzIterZ c (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z := by
    have h := congrFun (congrFun (Work.Coercivity.CommutZ.DzIter_mulZ c
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))) z) θ
    have hfun : Work.Coercivity.CommutZ.mulZ (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L))
        = (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) := rfl
    rw [hfun] at h
    simpa only [Work.Coercivity.CommutZ.mulZ_apply] using h
  rw [h1]
  -- 2. the Stirling expansion
  have h2 : Work.Coercivity.CommutZ.DzIterZ c
        (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
      = ∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
          (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) := by
    simpa only [] using congrFun (DzIterZ_eq_sum_scoef
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) hsmL c) z
  rw [h2]
  -- 3. each summand is bounded by `M`
  have hb : ∀ k ≤ c, |z ^ k * iteratedDeriv k
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z| ≤ M := by
    intro k hk
    have hk4 : k ≤ 4 := le_trans hk hc
    have hrew : iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z
        = (L⁻¹) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) :=
      IteratedDeriv_comp_div (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) hsmg hLne k z
    have hzL : z ^ k * ((L⁻¹) ^ k *
          iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L))
        = (z / L) ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) (z / L) := by
      have hdiv : z / L = z * L⁻¹ := by rw [div_eq_mul_inv]
      rw [hdiv, mul_pow]
      ring
    rw [hrew, hzL]
    exact hMb k hk4 (z / L)
  have hsum := Work.Spaces.abs_sum_scoef_mul_le c M
    (fun k => z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z) hb
  have hbell : (Work.Spaces.bell c : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le c hc
  calc |∑ k ∈ Finset.range (c + 1), (Work.Spaces.scoef c k : ℝ) *
        (z ^ k * iteratedDeriv k (fun x : ℝ => (1 : ℝ) - Work.Stability.chi (x / L)) z)|
      ≤ (Work.Spaces.bell c : ℝ) * M := hsum
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right hbell hM0

end Work.FTS.LocData
