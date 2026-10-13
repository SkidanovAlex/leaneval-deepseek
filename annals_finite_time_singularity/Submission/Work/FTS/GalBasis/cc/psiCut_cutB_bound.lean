/-
# `Work.FTS.GalBasis.cc.psiCut_cutB_bound`

The *uniform in `N`* bound on the iterated angular derivatives of the angular step `cutB N`:

`∃ K > 0, ∀ N i ≤ 4, ∀ z θ, |D_θ^i (cutB N) z θ| ≤ K`,

where `D_θ = sin(2θ) ∂_θ` is the scale invariant angular operator of the paper and

`cutB N θ = st ((N+1) θ - 1) · st ((N+1) (π/2 - θ) - 1)`.

The point is that the mesh `1/(N+1)` of the step is *scale invariant*: the factor `(N+1)` produced
by the chain rule is compensated by the factor `sin(2θ) ≲ 1/(N+1)` valid on the transition layer,
so the constant does not depend on `N`.  This is what makes the cutoff `psiCut N` harmless in the
`ℋ⁴`-norm (see `PsiCutAux` and `psiCut_spec`).

## The argument

Both factors are compositions of the fixed profile `Real.smoothTransition` with an *affine* map,

`cutB N θ = st (a θ - 1) · st (a (π/2 - θ) - 1)`,  `a = N + 1 ≥ 1`,

so we substitute the rescaled variable `u = a θ - 1` (resp. `u = a (π/2 - θ) - 1`).  In that
variable `D_θ` becomes the operator `E_ρ = ρ ∂_u` with

`ρ (u) = a sin (2 (u+1)/a)`,  resp. `ρ (u) = - a sin (2 (u+1)/a)`,

and `ρ, ρ', ρ'', ρ'''` are bounded by `8` *uniformly for `a ≥ 1`* on `[0,1]` — the transition layer
of the profile.  Off that layer the profile is constant, so all the iterates of `E_ρ` applied to it
vanish there (`Eiter_eq_zero_of_open_const` of `PsiCutAux`); on the layer the abstract induction
`Eiter_deriv_bound` of `PsiCutAux` gives the bound `Cbnd M B i 0`, which uses only the (uniform,
compactness) bounds on the derivatives of `Real.smoothTransition` on `[0,1]` and the bounds on the
derivatives of `ρ` — hence it is *independent of `a` and of `N`*.

The two factors are recombined with the Leibniz rule for the iterated angular operator, which for
globally smooth factors `u, v` is the one dimensional statement

`Lop^[j] (u·v) = ∑_{a ≤ j} (j choose a) · (Lop^[a] u) · (Lop^[j-a] v)`,  `Lop φ = sin(2·) φ'`

(the `Lop` of `Work.Spaces`); this is `Lop_iter_mul` below.  The existence of the Leibniz rule in
this purely one dimensional form with *only* smoothness (rather than analyticity) hypotheses is
what makes the estimate apply to `Real.smoothTransition`, which is `C^∞` but not analytic.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.PsiCutAux
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The iterated angular operator on functions of `θ` alone

`Work.Spaces.Lop φ = sin(2·) · φ'` is the action of `D_θ` on the `θ`-slice, and
`DthIter n f z = Lop^[n] (fun θ => f z θ)`.  We need that the iterates of `Lop` preserve `C^∞`,
and the binomial expansion of `Lop^[j] (u · v)`. -/

/-- The iterates of `Lop` preserve smoothness. -/
theorem contDiff_Lop_iter {u : ℝ → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u) :
    ∀ k n : ℕ, ContDiff ℝ n (Work.Spaces.Lop^[k] u) := by
  intro k
  induction k with
  | zero => intro n; simpa using hu n
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply']
      have hsin : ContDiff ℝ n (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
      have h1 : ContDiff ℝ n (deriv (Work.Spaces.Lop^[k] u)) := (ih (n + 1)).deriv'
      exact hsin.mul h1

/-- **Leibniz rule for `Lop`.**  For globally smooth `u`, `v` the `j`-th iterate of
`Lop = sin(2·) ∂` applied to the pointwise product satisfies the binomial expansion. -/
theorem Lop_iter_mul {u v : ℝ → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u)
    (hv : ∀ n : ℕ, ContDiff ℝ n v) :
    ∀ j : ℕ, ∀ θ : ℝ, Work.Spaces.Lop^[j] (u * v) θ =
      ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
        ((Work.Spaces.Lop^[a] u) θ * (Work.Spaces.Lop^[j - a] v) θ) := by
  intro j
  induction j with
  | zero => intro θ; simp
  | succ j ih =>
      intro θ
      rw [Function.iterate_succ_apply']
      have hfun : Work.Spaces.Lop^[j] (u * v) = fun θ' => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ') := by
        funext θ'; exact ih θ'
      rw [hfun]
      have hdu : ∀ a, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ :=
        fun a => ((contDiff_Lop_iter hu a 1).differentiable (by norm_num)).differentiableAt
      have hdv : ∀ a, DifferentiableAt ℝ (Work.Spaces.Lop^[a] v) θ :=
        fun a => ((contDiff_Lop_iter hv a 1).differentiable (by norm_num)).differentiableAt
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ) *
            ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) θ :=
        fun a _ => ((hdu a).mul (hdv (j - a))).const_mul _
      have hfun2 : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ) *
              ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) := by
        funext θ'; rw [Finset.sum_apply]
      show Real.sin (2 * θ) * deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ' * (Work.Spaces.Lop^[j - a] v) θ')) θ = _
      rw [hfun2, deriv_sum hmem, Finset.mul_sum]
      rw [Finset.sum_congr rfl
        (fun a _ => Work.Spaces.sin_deriv_term u v θ j a (hdu a) (hdv (j - a)))]
      exact Work.Spaces.leibniz_step j (fun b => (Work.Spaces.Lop^[b] u) θ)
        (fun b => (Work.Spaces.Lop^[b] v) θ)

/-! ## 2. A bound on the iterates of `E_ρ` applied to the profile

`Eiter k ρ f = (ρ ∂)^k f` is the iterate of the operator `Eop ρ f = ρ · f'` (defined in
`PsiCutAux`).  If `f = Real.smoothTransition` is the step profile, if `M` bounds the first three
derivatives of `ρ` and `B` those of `f` on the transition layer `[0,1]`, then

`1 + ∑_{k ≤ 4} Cbnd M B k 0`

bounds `|Eiter k ρ f v|` for *all* `k ≤ 4` and *all* `v : ℝ`: on the layer this is the abstract
induction `Eiter_deriv_bound`, off the layer the profile is locally constant and all positive
iterates vanish.  Note that the constant only depends on `M` and `B`, not on `ρ` itself — this is
what makes it uniform in the mesh. -/
theorem Eiter_smoothTransition_bound {ρ : ℝ → ℝ} {M B : ℕ → ℝ}
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m) (hB0 : 1 ≤ B 0)
    (hM : ∀ m ≤ 3, ∀ u ∈ Set.Icc (0:ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m ≤ 4, ∀ u ∈ Set.Icc (0:ℝ) 1, |iteratedDeriv m Real.smoothTransition u| ≤ B m) :
    ∀ k : ℕ, k ≤ 4 → ∀ v : ℝ,
      |Eiter k ρ Real.smoothTransition v| ≤ 1 + ∑ k ∈ Finset.range 5, Cbnd M B k 0 := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range 5, Cbnd M B k 0 :=
    Finset.sum_nonneg (fun i _ => Cbnd_nonneg hMnn hBnn i 0)
  have hCb : ∀ k' ≤ 4, Cbnd M B k' 0 ≤ 1 + ∑ k ∈ Finset.range 5, Cbnd M B k 0 := by
    intro k' hk'
    have h1 : Cbnd M B k' 0 ≤ ∑ k ∈ Finset.range 5, Cbnd M B k 0 :=
      Finset.single_le_sum (fun i _ => Cbnd_nonneg hMnn hBnn i 0)
        (Finset.mem_range.mpr (by omega))
    linarith
  intro k hk v
  by_cases hv : v ∈ Set.Icc (0:ℝ) 1
  · have h := Eiter_deriv_bound hMnn hBnn hρ contDiff_smoothTransition hM hB k 0 (by omega) v hv
    simpa using le_trans h (hCb k hk)
  · rw [Set.mem_Icc, not_and_or] at hv
    rcases hv with hv | hv
    · -- `v < 0`: the profile vanishes identically on a neighbourhood of `v`
      have hv' : v < 0 := lt_of_not_ge hv
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [Eiter_zero]
        rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hv')]
        simp only [abs_zero]; linarith
      · rw [Eiter_eq_zero_of_open_const (ρ := ρ) (f := Real.smoothTransition) (U := Set.Iio 0)
          isOpen_Iio (Set.mem_Iio.mpr hv') ?_ k hkpos v (Set.mem_Iio.mpr hv')]
        · simp only [abs_zero]; linarith
        · intro w hw
          rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hw),
            Real.smoothTransition.zero_of_nonpos (le_of_lt hv')]
    · -- `1 < v`: the profile is identically `1` on a neighbourhood of `v`
      have hv' : 1 < v := lt_of_not_ge hv
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [Eiter_zero]
        rw [Real.smoothTransition.one_of_one_le (le_of_lt hv')]
        simp only [abs_one]; linarith
      · rw [Eiter_eq_zero_of_open_const (ρ := ρ) (f := Real.smoothTransition) (U := Set.Ioi 1)
          isOpen_Ioi (Set.mem_Ioi.mpr hv') ?_ k hkpos v (Set.mem_Ioi.mpr hv')]
        · simp only [abs_zero]; linarith
        · intro w hw
          rw [Real.smoothTransition.one_of_one_le (le_of_lt hw),
            Real.smoothTransition.one_of_one_le (le_of_lt hv')]

/-! ## 3. The rescaled angular coefficient `ρ (u) = a sin (2 (u+1)/a)`

`rhoM a` is the coefficient with which the operator `D_θ = sin(2θ) ∂_θ` acts in the rescaled
variable `u = a θ - 1` (`DthIter_affine` of `PsiCutAux`).  We compute its first three derivatives
and bound them by `8` on the transition layer `[0,1]`, uniformly in `a ≥ 1`. -/

/-- `deriv (rhoM a) u = 2 cos (2 (u+1)/a)`. -/
theorem rhoM_deriv_one (a : ℝ) (ha : a ≠ 0) :
    deriv (rhoM a) = fun u : ℝ => 2 * Real.cos (2 * (u + 1) / a) := by
  funext u
  have hinner : HasDerivAt (fun u : ℝ => 2 * (u + 1) / a) (2 / a) u := by
    have h1 : HasDerivAt (fun u : ℝ => u + 1) 1 u := by
      simpa using (hasDerivAt_id u).add_const 1
    have h2 : HasDerivAt (fun u : ℝ => 2 * (u + 1)) 2 u := by
      simpa using h1.const_mul 2
    exact h2.div_const a
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * (u + 1) / a))
      (Real.cos (2 * (u + 1) / a) * (2 / a)) u := hinner.sin
  have hfin : HasDerivAt (rhoM a) (a * (Real.cos (2 * (u + 1) / a) * (2 / a))) u := by
    show HasDerivAt (fun u : ℝ => a * Real.sin (2 * (u + 1) / a)) _ u
    exact hsin.const_mul a
  rw [hfin.deriv]
  field_simp

/-- `deriv (fun u => 2 cos (2 (u+1)/a)) u = -(4/a) sin (2 (u+1)/a)`. -/
theorem rhoM_deriv_two (a : ℝ) (ha : a ≠ 0) :
    deriv (fun u : ℝ => 2 * Real.cos (2 * (u + 1) / a)) =
      fun u : ℝ => -(4 / a) * Real.sin (2 * (u + 1) / a) := by
  funext u
  have hinner : HasDerivAt (fun u : ℝ => 2 * (u + 1) / a) (2 / a) u := by
    have h1 : HasDerivAt (fun u : ℝ => u + 1) 1 u := by
      simpa using (hasDerivAt_id u).add_const 1
    have h2 : HasDerivAt (fun u : ℝ => 2 * (u + 1)) 2 u := by
      simpa using h1.const_mul 2
    exact h2.div_const a
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (2 * (u + 1) / a))
      (-Real.sin (2 * (u + 1) / a) * (2 / a)) u := hinner.cos
  have hfin : HasDerivAt (fun u : ℝ => 2 * Real.cos (2 * (u + 1) / a))
      (2 * (-Real.sin (2 * (u + 1) / a) * (2 / a))) u := by
    show HasDerivAt (fun u : ℝ => 2 * Real.cos (2 * (u + 1) / a)) _ u
    exact hcos.const_mul 2
  rw [hfin.deriv]
  field_simp
  ring

/-- `deriv (fun u => -(4/a) sin (2 (u+1)/a)) u = -(8/a²) cos (2 (u+1)/a)`. -/
theorem rhoM_deriv_three (a : ℝ) (ha : a ≠ 0) :
    deriv (fun u : ℝ => -(4 / a) * Real.sin (2 * (u + 1) / a)) =
      fun u : ℝ => -(8 / a ^ 2) * Real.cos (2 * (u + 1) / a) := by
  funext u
  have hinner : HasDerivAt (fun u : ℝ => 2 * (u + 1) / a) (2 / a) u := by
    have h1 : HasDerivAt (fun u : ℝ => u + 1) 1 u := by
      simpa using (hasDerivAt_id u).add_const 1
    have h2 : HasDerivAt (fun u : ℝ => 2 * (u + 1)) 2 u := by
      simpa using h1.const_mul 2
    exact h2.div_const a
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * (u + 1) / a))
      (Real.cos (2 * (u + 1) / a) * (2 / a)) u := hinner.sin
  have hfin : HasDerivAt (fun u : ℝ => -(4 / a) * Real.sin (2 * (u + 1) / a))
      (-(4 / a) * (Real.cos (2 * (u + 1) / a) * (2 / a))) u := by
    show HasDerivAt (fun u : ℝ => -(4 / a) * Real.sin (2 * (u + 1) / a)) _ u
    exact hsin.const_mul (-(4 / a))
  rw [hfin.deriv]
  field_simp
  ring

/-- The derivatives of `rhoM a` up to order `3` are bounded by `8` on `[0,1]`, uniformly in
`a ≥ 1`. -/
theorem iteratedDeriv_rhoM_bound (a : ℝ) (ha : 1 ≤ a) (m : ℕ) (hm : m ≤ 3) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) : |iteratedDeriv m (rhoM a) u| ≤ 8 := by
  have hane : a ≠ 0 := by linarith
  have hapos : (0:ℝ) < a := by linarith
  interval_cases m
  · rw [iteratedDeriv_zero]
    have h2 : a * (2 * (u + 1) / a) = 2 * (u + 1) := by field_simp
    have hb : |Real.sin (2 * (u + 1) / a)| ≤ 2 * (u + 1) / a := by
      refine le_trans Real.abs_sin_le_abs ?_
      rw [abs_of_nonneg (div_nonneg (by linarith [hu.1]) (by linarith))]
    simp only [rhoM, abs_mul, abs_of_nonneg (le_of_lt hapos)]
    calc a * |Real.sin (2 * (u + 1) / a)| ≤ a * (2 * (u + 1) / a) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hapos)
      _ = 2 * (u + 1) := h2
      _ ≤ 8 := by linarith [hu.2]
  · rw [iteratedDeriv_one, rhoM_deriv_one a hane]
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * |Real.cos (2 * (u + 1) / a)| ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by norm_num)
      _ ≤ 8 := by norm_num
  · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ',
      iteratedDeriv_zero, rhoM_deriv_one a hane, rhoM_deriv_two a hane]
    have h4 : (0:ℝ) ≤ 4 / a := by positivity
    have hb : 4 / a ≤ 4 := by rw [div_le_iff₀ hapos]; linarith
    simp only [abs_mul, abs_neg, abs_of_nonneg h4]
    calc (4 / a) * |Real.sin (2 * (u + 1) / a)| ≤ (4 / a) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) h4
      _ = 4 / a := by ring
      _ ≤ 8 := by linarith
  · rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ',
      iteratedDeriv_succ', iteratedDeriv_zero, rhoM_deriv_one a hane, rhoM_deriv_two a hane,
      rhoM_deriv_three a hane]
    have h8nn : (0:ℝ) ≤ 8 / a ^ 2 := by positivity
    have h8 : 8 / a ^ 2 ≤ 8 := by rw [div_le_iff₀ (by positivity)]; nlinarith [ha]
    simp only [abs_mul, abs_neg, abs_of_nonneg h8nn]
    calc (8 / a ^ 2) * |Real.cos (2 * (u + 1) / a)| ≤ (8 / a ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h8nn
      _ = 8 / a ^ 2 := by ring
      _ ≤ 8 := h8

/-- The same bound for the negated coefficient `u ↦ -rhoM a u`, which is the coefficient of the
*upper* transition layer (`DthIter_affine` applied to `θ ↦ st (a (π/2 - θ) - 1)`). -/
theorem iteratedDeriv_neg_rhoM_bound (a : ℝ) (ha : 1 ≤ a) (m : ℕ) (hm : m ≤ 3) (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) : |iteratedDeriv m (fun u : ℝ => -(rhoM a u)) u| ≤ 8 := by
  have h : (fun u : ℝ => -(rhoM a u)) = -(rhoM a) := rfl
  rw [h, iteratedDeriv_neg, abs_neg]
  exact iteratedDeriv_rhoM_bound a ha m hm u hu

/-! ## 4. The two affine substitutions in the rescaled variable -/

/-- The rescaled coefficient of the angular substitution `u = a θ + c` for the *lower* layer
`c = -1` is `rhoM a`. -/
theorem coef_affine_eq_rhoM (a : ℝ) :
    (fun u : ℝ => a * Real.sin (2 * ((u - (-1)) / a))) = rhoM a := by
  funext u
  simp only [rhoM]
  rw [show 2 * ((u - (-1)) / a) = 2 * (u + 1) / a from by ring]

/-- The rescaled coefficient of the angular substitution `u = -a θ + (a π/2 - 1)` for the *upper*
layer `θ ↦ st (a (π/2 - θ) - 1)` is `-rhoM a`. -/
theorem coef_affine_eq_neg_rhoM (a : ℝ) (ha : a ≠ 0) :
    (fun u : ℝ => (-a) * Real.sin (2 * ((u - (a * (Real.pi / 2) - 1)) / (-a)))) =
      fun u : ℝ => -(rhoM a u) := by
  funext u
  simp only [rhoM]
  rw [show 2 * ((u - (a * (Real.pi / 2) - 1)) / (-a)) = Real.pi - 2 * (u + 1) / a from by
    field_simp
    ring]
  rw [Real.sin_pi_sub]
  ring

/-! ## 5. Recombining the two factors -/

/-- `DthIter i f z` for a function `f` that does not depend on `z` is the `i`-th iterate of `Lop`
applied to the `θ`-profile. -/
theorem DthIter_zindep (g : ℝ → ℝ) (z : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ => g θ) z = Work.Spaces.Lop^[i] g := by
  rw [Work.Spaces.DthIter_eq_iterate_Lop]

/-- The affine substitution `u = a θ + c` applied to `Lop`: the iterates of `Lop` on the rescaled
profile `θ ↦ st (a θ + c)` are the iterates of `E_ρ`, `ρ (u) = a sin (2 (u - c)/a)`, evaluated at
`u = a θ + c`. -/
theorem Lop_iter_affine_st (a c : ℝ) (ha : a ≠ 0) (i : ℕ) :
    ∀ θ : ℝ, Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.smoothTransition (a * θ' + c)) θ =
      Eiter i (fun u => a * Real.sin (2 * ((u - c) / a))) Real.smoothTransition (a * θ + c) := by
  intro θ
  rw [← DthIter_zindep (fun θ' : ℝ => Real.smoothTransition (a * θ' + c)) 0 i]
  exact DthIter_affine Real.smoothTransition a c ha i contDiff_smoothTransition 0 θ

/-- **The product bound.**  If the iterates of `Lop` on the two `θ`-profiles `u`, `v` are bounded
by `Ku` resp. `Kv` up to order `4`, then the iterates of `D_θ` on the pointwise product of the two
`z`-independent functions are bounded by `16 (Ku Kv) + 1`. -/
theorem DthIter_mul_zindep_bound {u v : ℝ → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u)
    (hv : ∀ n : ℕ, ContDiff ℝ n v) {Ku Kv : ℝ}
    (hKu : ∀ k : ℕ, k ≤ 4 → ∀ θ : ℝ, |Work.Spaces.Lop^[k] u θ| ≤ Ku)
    (hKv : ∀ k : ℕ, k ≤ 4 → ∀ θ : ℝ, |Work.Spaces.Lop^[k] v θ| ≤ Kv) :
    ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ,
      |Work.Spaces.DthIter i (fun (_ : ℝ) θ' => u θ' * v θ') z θ| ≤ 16 * (Ku * Kv) + 1 := by
  have hKunn : 0 ≤ Ku := le_trans (abs_nonneg _) (hKu 0 (by norm_num) 0)
  have hKvnn : 0 ≤ Kv := le_trans (abs_nonneg _) (hKv 0 (by norm_num) 0)
  intro i hi z θ
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (fun (_ : ℝ) θ' => u θ' * v θ') z) θ]
  rw [show (fun θ : ℝ => (fun (_ : ℝ) θ' => u θ' * v θ') z θ) = u * v from by funext θ'; rfl]
  rw [Lop_iter_mul hu hv i θ]
  have hsum : (∑ a ∈ Finset.range (i + 1),
      |(i.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ * (Work.Spaces.Lop^[i - a] v) θ)|)
      ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (Ku * Kv) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha' : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have h1 : |Work.Spaces.Lop^[a] u θ| ≤ Ku := hKu a (by omega) θ
    have h2 : |Work.Spaces.Lop^[i - a] v θ| ≤ Kv := hKv (i - a) (by omega) θ
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose a)), abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) hKunn)
      (Nat.cast_nonneg _)
  calc |∑ a ∈ Finset.range (i + 1),
        (i.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ * (Work.Spaces.Lop^[i - a] v) θ)|
      ≤ ∑ a ∈ Finset.range (i + 1),
          |(i.choose a : ℝ) * ((Work.Spaces.Lop^[a] u) θ * (Work.Spaces.Lop^[i - a] v) θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * (Ku * Kv) := hsum
    _ = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)) * (Ku * Kv) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ i * (Ku * Kv) := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 16 * (Ku * Kv) := by
        have h2i : (2:ℝ) ^ i ≤ 16 := by
          calc (2:ℝ)^i ≤ 2^4 := by
                apply pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 16 := by norm_num
        exact mul_le_mul_of_nonneg_right h2i (mul_nonneg hKunn hKvnn)
    _ ≤ 16 * (Ku * Kv) + 1 := by linarith

/-! ## 6. The uniform bound -/

theorem psiCut_cutB_bound : ∃ K : ℝ, 0 < K ∧ ∀ (N i : ℕ), i ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.DthIter i (fun (_ : ℝ) θ' => cutB N θ') z θ| ≤ K := by
  -- uniform bounds on the derivatives of the profile on the transition layer `[0,1]`
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ m ≤ 4, ∀ u ∈ Set.Icc (0:ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ Cb := by
    have hcont : Continuous (fun u : ℝ => ∑ m ∈ Finset.range 5,
        |iteratedDeriv m Real.smoothTransition u|) := by
      apply continuous_finsetSum
      intro m _
      exact ((contDiff_smoothTransition m).continuous_iteratedDeriv m le_rfl).abs
    obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Cb, fun m hm u hu => ?_⟩
    have hle : |iteratedDeriv m Real.smoothTransition u| ≤
        ∑ i ∈ Finset.range 5, |iteratedDeriv i Real.smoothTransition u| := by
      have := Finset.single_le_sum (s := Finset.range 5)
        (f := fun i => |iteratedDeriv i Real.smoothTransition u|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
      simpa using this
    have h2 := hCb u hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at h2
    linarith
  set B : ℕ → ℝ := fun _ => max Cb 1 with hBdef
  have hBnn : ∀ m, 0 ≤ B m := fun m => le_trans zero_le_one (le_max_right _ _)
  have hB0 : 1 ≤ B 0 := le_max_right _ _
  have hB : ∀ m ≤ 4, ∀ u ∈ Set.Icc (0:ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B m :=
    fun m hm u hu => le_trans (hCb m hm u hu) (le_max_left _ _)
  -- the derivative bounds `M` of the rescaled coefficient
  set M : ℕ → ℝ := fun _ => 8 with hMdef
  have hMnn : ∀ m, 0 ≤ M m := fun m => by rw [hMdef]; norm_num
  refine ⟨max 1 (16 * (1 + ∑ k ∈ Finset.range 5, Cbnd M B k 0) ^ 2 + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro N i hi z θ
    set Kc : ℝ := 1 + ∑ k ∈ Finset.range 5, Cbnd M B k 0 with hKcdef
    set a : ℝ := (N : ℝ) + 1 with hadef
    have ha1 : 1 ≤ a := by
      rw [hadef]
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hane : a ≠ 0 := by linarith
    have hM1 : ∀ m ≤ 3, ∀ u ∈ Set.Icc (0:ℝ) 1, |iteratedDeriv m (rhoM a) u| ≤ M m :=
      fun m hm u hu => by rw [hMdef]; exact iteratedDeriv_rhoM_bound a ha1 m hm u hu
    have hM2 : ∀ m ≤ 3, ∀ u ∈ Set.Icc (0:ℝ) 1,
        |iteratedDeriv m (fun u : ℝ => -(rhoM a u)) u| ≤ M m :=
      fun m hm u hu => by rw [hMdef]; exact iteratedDeriv_neg_rhoM_bound a ha1 m hm u hu
    have hKc1 : ∀ k : ℕ, k ≤ 4 → ∀ v : ℝ, |Eiter k (rhoM a) Real.smoothTransition v| ≤ Kc :=
      fun k hk v => by
        rw [hKcdef]
        exact Eiter_smoothTransition_bound (contDiff_rhoM a) hMnn hBnn hB0 hM1 hB k hk v
    have hKc2 : ∀ k : ℕ, k ≤ 4 → ∀ v : ℝ,
        |Eiter k (fun u : ℝ => -(rhoM a u)) Real.smoothTransition v| ≤ Kc :=
      fun k hk v => by
        rw [hKcdef]
        exact Eiter_smoothTransition_bound (fun n => (contDiff_rhoM a n).neg) hMnn hBnn hB0 hM2 hB
          k hk v
    have hsu : ∀ n : ℕ, ContDiff ℝ n (fun θ' : ℝ => Real.smoothTransition (a * θ' + (-1))) :=
      fun n => (contDiff_smoothTransition n).comp (contDiff_affine a (-1) n)
    have hsv : ∀ n : ℕ, ContDiff ℝ n
        (fun θ' : ℝ => Real.smoothTransition ((-a) * θ' + (a * (Real.pi / 2) - 1))) :=
      fun n => (contDiff_smoothTransition n).comp
        (contDiff_affine (-a) (a * (Real.pi / 2) - 1) n)
    -- the bounds on the iterated `D_θ`-derivatives of the two factors
    have hF1 : ∀ k : ℕ, k ≤ 4 → ∀ θ : ℝ,
        |Work.Spaces.Lop^[k] (fun θ' : ℝ => Real.smoothTransition (a * θ' + (-1))) θ| ≤ Kc := by
      intro k hk θ
      rw [Lop_iter_affine_st a (-1) hane k θ, coef_affine_eq_rhoM a]
      exact hKc1 k hk (a * θ + (-1))
    have hF2 : ∀ k : ℕ, k ≤ 4 → ∀ θ : ℝ,
        |Work.Spaces.Lop^[k] (fun θ' : ℝ =>
          Real.smoothTransition ((-a) * θ' + (a * (Real.pi / 2) - 1))) θ| ≤ Kc := by
      intro k hk θ
      rw [Lop_iter_affine_st (-a) (a * (Real.pi / 2) - 1) (by simpa using hane) k θ,
        coef_affine_eq_neg_rhoM a hane]
      exact hKc2 k hk ((-a) * θ + (a * (Real.pi / 2) - 1))
    -- `cutB N` as the product of the two rescaled factors
    have hcut : (fun (_ : ℝ) θ' => cutB N θ') =
        (fun (_ : ℝ) θ' => Real.smoothTransition (a * θ' + (-1)) *
          Real.smoothTransition ((-a) * θ' + (a * (Real.pi / 2) - 1))) := by
      funext z θ'
      have h1 : ((N:ℝ) + 1) * θ' - 1 = a * θ' + (-1) := by rw [← hadef]; ring
      have h2 : ((N:ℝ) + 1) * (Real.pi / 2 - θ') - 1 =
          (-a) * θ' + (a * (Real.pi / 2) - 1) := by rw [← hadef]; ring
      simp only [cutB, h1, h2]
    rw [hcut]
    refine le_trans (DthIter_mul_zindep_bound hsu hsv hF1 hF2 i hi z θ) ?_
    rw [← pow_two Kc, hKcdef]
    exact le_max_right _ _

end Work.FTS.GalBasis.cc
