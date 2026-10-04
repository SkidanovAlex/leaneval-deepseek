/-
# `Work.Diff.STE.flat.energy_differentiable`

The time regularity of the flat `Hᵏ` energy along a box-supported (Galerkin) trajectory.

The statement below is the "differentiate the energy" *prerequisite* of the a priori estimate
`Work.Diff.STE.flat.energy_apriori`: along any coefficient trajectory `c` which solves the
projected ODE `∂ₜ c t k' = fourierCoeff (Φ ∘ jet) k'` on the box `box n N`, vanishes outside the
box and keeps `seriesFunM (c t)` uniformly elliptic with constant `lam`, the map

  `σ ↦ ENormSqFull j (seriesFunM (c σ))`

is differentiable at every `t ∈ Ico 0 Tc`.

## Why this is elementary

The box support is the crucial hypothesis.  Because `c σ k' = 0` for `k' ∉ box n N`, the series
`seriesFunM (c σ)` is a *finite* trigonometric sum,

  `seriesFunM (c σ) x i i' = Σ_{k' ∈ box n N} c σ k' i i' · exp (2πi k'·x)`,

so by Parseval (`integral_normSq_seriesFun`) each of the finitely many terms of the energy is the
finite sum

  `∫_{unitCube} ‖∂^l (seriesFunM (c σ) · i i')‖² = Σ_{k' ∈ box n N} ‖dmulV l (c σ · i i') k'‖²`

(term by term differentiation `pdList_seriesFun`), and hence

  `ENormSqFull j (seriesFunM (c σ))
     = Σ_{i, i', l : Fin j → Fin n} Σ_{k' ∈ box} ‖dmulV l (c σ · i i') k'‖²
       + (same with j = 0)`.

This is an *explicit* function of the finitely many complex numbers `c σ k' i i'` (`k' ∈ box`),
each of which is differentiable at `t` by hypothesis; the value `‖μ · c σ k' i i'‖²` is
differentiable by `hasDerivAt_normsq_of_hasDerivAt`, and the finitely many sums are handled by
`HasDerivAt.fun_sum`.  In particular no differentiation under the integral sign, no domination
hypothesis and no neighbourhood in `σ` is needed: the whole argument is finite dimensional, which
is exactly what makes it work at the endpoint `t = 0` of `Ico 0 Tc` as well.

Main lemmas:
* `ENormSqM_seriesFunM_eq` — the explicit finite formula for the energy;
* `differentiableAt_sliceSum` — differentiability of that formula in `σ`;
* `energy_differentiable` — the requested statement.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.hasDerivAt_normsq_of_hasDerivAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators Filter

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

/-- An entry of a matrix which is equal to `0` vanishes. -/
lemma matC_apply_eq_zero {n : ℕ} {A : MatC n} (h : A = 0) (i j : Fin n) : A i j = 0 := by
  rw [h]; rfl

/-- A box-supported coefficient family has finite support, so all its weighted `ℓ¹` moments (and
in particular the moment sums entering `pdList_seriesFun`) are summable. -/
lemma summable_moment_box_ste {n : ℕ} (N : ℕ) (d : (Fin n → ℤ) → MatC n)
    (hbox : ∀ k : Fin n → ℤ, k ∉ box n N → d k = 0) (i j : Fin n) (M : ℕ) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖d k i j‖) := by
  refine summable_of_ne_finset_zero (s := box n N) ?_
  intro k hk
  rw [hbox k hk]
  simp

/-- **The energy of a box-supported coefficient family is an explicit finite sum.**

For a coefficient family `d` supported in `box n N`, the level-`m` `H^m` energy of the Fourier
series `seriesFunM d` (summed over the matrix entries) equals the finite sum

  `Σ_{i,i'} Σ_{l : Fin m → Fin n} Σ_{k' ∈ box n N} ‖dmulV l (d · i i') k'‖²`

of the (weighted) coefficient norms of the differentiated families.  This is just Parseval plus
term by term differentiation, made finite by the box support. -/
lemma ENormSqM_seriesFunM_eq {n : ℕ} (N m : ℕ) (d : (Fin n → ℤ) → MatC n)
    (hbox : ∀ k : Fin n → ℤ, k ∉ box n N → d k = 0) :
    ENormSqM m (seriesFunM d)
      = ∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin m → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => d k i i') k'‖ ^ 2 := by
  unfold ENormSqM ENormSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hfun : (fun x : Fin n → ℝ => seriesFunM d x i i')
      = seriesFun (fun k : Fin n → ℤ => d k i i') := by
    funext x; rw [seriesFunM_apply]
  rw [hfun]
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖d k i i'‖) :=
    fun M => summable_moment_box_ste N d hbox i i' M
  -- the differentiated family vanishes outside the box, so summability and `tsum` are finite
  have hz : ∀ k : Fin n → ℤ, k ∉ box n N →
      ‖dmulV (List.ofFn l) (fun k : Fin n → ℤ => d k i i') k‖ ^ 2 = 0 := by
    intro k hk
    have h0 : d k i i' = 0 := by simp only [hbox k hk, Pi.zero_apply]
    rw [dmulV, h0, mul_zero, norm_zero]
    norm_num
  have hz' : ∀ k : Fin n → ℤ, k ∉ box n N →
      ‖dmulV (List.ofFn l) (fun k : Fin n → ℤ => d k i i') k‖ = 0 := by
    intro k hk
    have h0 : d k i i' = 0 := by simp only [hbox k hk, Pi.zero_apply]
    rw [dmulV, h0, mul_zero, norm_zero]
  -- term by term differentiation of the series, then Parseval
  have hpd : pdVec m l (seriesFun (fun k : Fin n → ℤ => d k i i'))
      = seriesFun (dmulV (List.ofFn l) (fun k : Fin n → ℤ => d k i i')) :=
    funext (fun x => by
      rw [pdVec]
      exact pdList_seriesFun (List.ofFn l) (fun k : Fin n → ℤ => d k i i') hmom x)
  rw [hpd]
  rw [integral_normSq_seriesFun _
    (summable_of_ne_finset_zero (s := box n N) (fun k hk => hz' k hk))]
  exact tsum_eq_sum (fun k hk => hz k hk)

/-- **Differentiability of the explicit energy formula.**

If every coefficient function `σ ↦ c σ k' i i'` of the box `box n N` is differentiable at `t` with
derivative `G k' i i'`, then the finite sum

  `σ ↦ Σ_{i,i'} Σ_{l : Fin m → Fin n} Σ_{k' ∈ box n N} ‖dmulV l (c σ · i i') k'‖²`

is differentiable at `t`.  This is the derivative of the energy along a Galerkin trajectory: each
summand is `‖(∏_{j ∈ l} 2πi k'_j) · c σ k' i i'‖²`, a smooth function of the single coefficient
`c σ k' i i'`. -/
lemma differentiableAt_sliceSum {n : ℕ} (N : ℕ) (G : (Fin n → ℤ) → Fin n → Fin n → ℂ)
    (c : ℝ → (Fin n → ℤ) → MatC n) (t : ℝ)
    (hc : ∀ (k' : Fin n → ℤ), k' ∈ box n N → ∀ i i' : Fin n,
      HasDerivAt (fun σ => c σ k' i i') (G k' i i') t) (m : ℕ) :
    DifferentiableAt ℝ (fun σ => ∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin m → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c σ k i i') k'‖ ^ 2) t := by
  have hslice : ∀ (l : List (Fin n)) (i i' : Fin n),
      HasDerivAt (fun σ => ∑ k' ∈ box n N, ‖dmulV l (fun k => c σ k i i') k'‖ ^ 2)
        (∑ k' ∈ box n N, 2 * (((l.map (fun j => 2 * Real.pi * Complex.I * (k' j : ℂ))).prod
            * G k' i i')
          * star ((l.map (fun j => 2 * Real.pi * Complex.I * (k' j : ℂ))).prod
            * c t k' i i')).re) t := by
    intro l i i'
    refine HasDerivAt.fun_sum (fun k' hk' => ?_)
    have h1 : HasDerivAt
        (fun σ => (l.map (fun j => 2 * Real.pi * Complex.I * (k' j : ℂ))).prod * c σ k' i i')
        ((l.map (fun j => 2 * Real.pi * Complex.I * (k' j : ℂ))).prod * G k' i i') t :=
      (hc k' hk' i i').const_mul _
    have h2 := hasDerivAt_normsq_of_hasDerivAt h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall (fun σ => ?_))
    simp only [dmulV]
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun i' _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
        hslice (List.ofFn l) i i')))).differentiableAt

/-- **Time differentiability of the flat `Hᵏ` energy** along a box-supported Galerkin trajectory.

Under the equations `∂ₜ c t k' = fourierCoeff (Φ ∘ jetM (seriesFunM (c t))) k'` on the box
`box n N`, box support and uniform ellipticity of `seriesFunM (c t)`, the energy
`σ ↦ ENormSqFull j (seriesFunM (c σ))` is differentiable at every `t ∈ Ico 0 Tc`.

The ellipticity hypothesis is not needed: the box support makes the energy an explicit finite sum
of squares of the coefficients, so differentiability is purely algebraic. -/
theorem energy_differentiable {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (j : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∀ (Tc : ℝ) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
        HasDerivAt (fun σ => c σ k' i j)
          (Work.Diff.STE.fourierCoeff (fun x =>
            Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
      (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
      (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
      ∀ t ∈ Set.Ico (0 : ℝ) Tc,
        DifferentiableAt ℝ
          (fun σ => Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c σ))) t := by
  intro Tc N c hderiv hbox hell t ht
  classical
  -- the derivative of the box coefficients at `t`, as a function `G`
  have hc : ∀ (k' : Fin n → ℤ), k' ∈ box n N → ∀ i i' : Fin n,
      HasDerivAt (fun σ => c σ k' i i')
        (fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i i') k') t :=
    fun k' hk' i i' => hderiv t ht k' hk' i i'
  -- the two explicit slice sums (`j` and `0`) are differentiable …
  have h1 : DifferentiableAt ℝ
      (fun σ => ∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin j → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c σ k i i') k'‖ ^ 2) t :=
    differentiableAt_sliceSum N
      (fun k' i i' => fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i i') k')
      c t hc j
  have h2 : DifferentiableAt ℝ
      (fun σ => ∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin 0 → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c σ k i i') k'‖ ^ 2) t :=
    differentiableAt_sliceSum N
      (fun k' i i' => fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i i') k')
      c t hc 0
  -- … and they are the two halves of `ENormSqFull` for every `σ`
  have hpt : ∀ σ : ℝ, ENormSqFull j (seriesFunM (c σ))
      = (∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin j → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c σ k i i') k'‖ ^ 2)
        + (∑ i : Fin n, ∑ i' : Fin n, ∑ l : Fin 0 → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c σ k i i') k'‖ ^ 2) := by
    intro σ
    simp only [ENormSqFull, ENormSqM_seriesFunM_eq N j (c σ) (fun k' hk' => hbox σ k' hk'),
      ENormSqM_seriesFunM_eq N 0 (c σ) (fun k' hk' => hbox σ k' hk')]
  refine (h1.add h2).congr_of_eventuallyEq (Eventually.of_forall (fun σ => hpt σ))

end

end Work.Diff.STE.flat
