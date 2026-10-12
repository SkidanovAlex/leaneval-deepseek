import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Glaeser's inequality for the scaled corpus bump `chiScale ℓ`

`Work.BoseSWE.chiScaleGlaeser`: there is `N ≥ 0` such that for every `ℓ > 0` and every `x : ℝ³`

    ‖∇(chiScale ℓ) x‖² ≤ 2·(N/ℓ²)·chiScale ℓ x ,   chiScale ℓ = chi(ℓ⁻¹ • ·)

where `chi` is the cubic smooth bump of `Submission.CubicChi`
(`Submission.BoseGases.chi`).

The proof is the classical one, isolated here as reusable lemmas:

* `Work.BoseSWE.taylor_repr` — Taylor's formula at order `1` with integral remainder
  (`map_add_eq_sum_add_integral_iteratedFDeriv`) along the segment from `x` to `x - w`;
* `Work.BoseSWE.taylor_upper` — the resulting upper bound
  `f (x - w) ≤ f x - ⟨∇f x, w⟩ + N‖w‖²/2` whenever `‖D²f‖ ≤ N`;
* `Work.BoseSWE.glaeserPointwisePos` — the pointwise Glaeser inequality
  `‖∇f x‖² ≤ 2N·f x` for `f ≥ 0`, `C²`, `‖D²f‖ ≤ N`, `N > 0` (the `0 < N` form of the route's
  `Work.BoseSWE.glaeserPointwise`; the `N ≤ 0` case is vacuous, and only `N > 0` is used below);
* `Work.BoseSWE.chi_iteratedFDeriv_bound` — `‖D²chi‖` is bounded, by continuity of
  `iteratedFDeriv ℝ 2 chi` (`chi_contDiff`) together with its compact support
  (`chi_hasCompactSupport`).

The target then follows from the chain rule `Work.BlockBound4.fderiv_chiScale_apply`
(`fderiv ℝ (chiScale ℓ) x = ℓ⁻¹ • fderiv ℝ chi (ℓ⁻¹ • x)`) and `chiScale ℓ x = chi (ℓ⁻¹ • x)`.
-/

open MeasureTheory Finset
open scoped ContDiff

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Taylor's formula with integral remainder, order `1`, along a segment.** For a `C²` function
`f : ℝ³ → ℝ`, `f (x - w) = f x - ⟨f'(x), w⟩ + ∫₀¹ (1 - t)·(D²f(x - t•w))(w, w) dt`. -/
lemma taylor_repr {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (x w : E3) :
    f (x - w) = f x - fderiv ℝ f x w
      + ∫ t in (0:ℝ)..1, (1 - t) * (iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w) := by
  -- the second derivative applied to `(-w, -w)` equals the one applied to `(w, w)`
  have hsign : ∀ z : E3,
      (iteratedFDeriv ℝ 2 f z) (fun _ => -w) = (iteratedFDeriv ℝ 2 f z) (fun _ => w) := by
    intro z
    simp [iteratedFDeriv_two_apply]
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := -w) (n := 1) (by
    intro t ht
    exact hf.contDiffAt.of_le (by decide))
  simp only [Nat.reduceAdd] at h
  simp only [Finset.sum_range_succ, Nat.factorial_one, Nat.factorial_zero,
    Nat.cast_one, inv_one, pow_one, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply, smul_eq_mul, hsign] at h
  simp only [sub_eq_add_neg] at h ⊢
  rw [h]
  simp only [Finset.sum_range_zero, zero_add, one_mul, map_neg]
  rw [add_right_inj]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [show x + t • -w = x + -(t • w) by simp]

/-- **The Taylor upper bound.** If `‖D²f‖ ≤ N` pointwise then
`f (x - w) ≤ f x - ⟨f'(x), w⟩ + N‖w‖²/2`. -/
lemma taylor_upper {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) {N : ℝ}
    (hN : ∀ z : E3, ‖iteratedFDeriv ℝ 2 f z‖ ≤ N) (x w : E3) :
    f (x - w) ≤ f x - fderiv ℝ f x w + N * ‖w‖ ^ 2 / 2 := by
  rw [taylor_repr hf x w]
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (1 - t) * (iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w) ≤ (1 - t) * (N * ‖w‖ ^ 2) := by
    intro t ht
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [ht.2])
    calc (iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w)
        ≤ |(iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w)| := le_abs_self _
      _ = ‖(iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ 2 f (x - t • w)‖ * ∏ i : Fin 2, ‖(fun _ : Fin 2 => w) i‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ N * ‖w‖ ^ 2 := by
            have hprod : (∏ i : Fin 2, ‖(fun _ : Fin 2 => w) i‖) = ‖w‖ ^ 2 := by simp
            rw [hprod]
            exact mul_le_mul_of_nonneg_right (hN _) (sq_nonneg _)
  have hc : (∫ t in (0:ℝ)..1, (1 - t) * (N * ‖w‖ ^ 2)) = N * ‖w‖ ^ 2 / 2 := by
    rw [intervalIntegral.integral_mul_const]
    have h1 : (∫ t in (0:ℝ)..1, (1 - t)) = 1/2 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) 1]
      norm_num [integral_id]
    rw [h1]; ring
  have hle : (∫ t in (0:ℝ)..1, (1 - t) * (iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w))
      ≤ ∫ t in (0:ℝ)..1, (1 - t) * (N * ‖w‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        (1 - t) * (iteratedFDeriv ℝ 2 f (x - t • w)) (fun _ => w))).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous (fun t : ℝ => (1 - t) * (N * ‖w‖ ^ 2))).intervalIntegrable 0 1
    · exact hpt
  linarith [hle, hc]

/-- **Pointwise Glaeser inequality.** A nonnegative `C²` function `f : ℝ³ → ℝ` with
`‖D²f‖ ≤ N`, `N > 0`, satisfies `‖∇f x‖² ≤ 2 N f x` at every point.

(For `N ≤ 0` the hypothesis forces `D²f ≡ 0`, hence `∇f ≡ 0`; only the `N > 0` case is needed
below, where the bound on `‖D²chi‖` may be taken positive.) -/
lemma glaeserPointwisePos {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (hnn : ∀ x, 0 ≤ f x) {N : ℝ}
    (hNpos : 0 < N) (hN : ∀ y : E3, ‖iteratedFDeriv ℝ 2 f y‖ ≤ N) (x : E3) :
    ‖fderiv ℝ f x‖ ^ 2 ≤ 2 * N * f x := by
  set L := fderiv ℝ f x with hL
  have hfx : 0 ≤ f x := hnn x
  -- the one-dimensional inequality in each direction, for the descent direction `v`
  have hdir0 : ∀ v : E3, ‖v‖ = 1 → 0 ≤ L v → (L v) ^ 2 ≤ 2 * N * f x := by
    intro v hv hLv
    rcases eq_or_lt_of_le hLv with h0 | hpos
    · have hz : (L v) ^ 2 = 0 := by rw [← h0]; ring
      rw [hz]; nlinarith [hNpos, hfx]
    · set T := L v / N with hT
      have hTpos : 0 < T := by rw [hT]; exact div_pos hpos hNpos
      have hTnorm : ‖T • v‖ = T := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hTpos, hv, mul_one]
      have hupper := taylor_upper hf hN x (T • v)
      rw [hTnorm] at hupper
      have hLt : (fderiv ℝ f x) (T • v) = T * (L v) := by
        rw [hL, map_smul, smul_eq_mul]
      rw [hLt] at hupper
      have hlow : 0 ≤ f (x - T • v) := hnn _
      have hkey : T * L v ≤ f x + N * T ^ 2 / 2 := by linarith
      rw [hT] at hkey
      have hclear : (L v) ^ 2 ≤ 2 * N * f x := by
        field_simp at hkey
        nlinarith [hkey]
      exact hclear
  -- the downhill direction may be taken with either sign
  have hdir : ∀ v : E3, ‖v‖ = 1 → (L v) ^ 2 ≤ 2 * N * f x := by
    intro v hv
    rcases le_or_gt 0 (L v) with h | h
    · exact hdir0 v hv h
    · have h1 : L (-v) = -(L v) := by rw [map_neg]
      have h2 : 0 ≤ L (-v) := by rw [h1]; exact (neg_pos.mpr h).le
      have h3 := hdir0 (-v) (by simpa using hv) h2
      simpa [h1] using h3
  -- bound the operator norm by the value on the unit sphere
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * N * f x) := Real.sqrt_nonneg _
  have hbound : ‖L‖ ≤ Real.sqrt (2 * N * f x) := by
    refine ContinuousLinearMap.opNorm_le_bound _ hsqrt_nonneg ?_
    intro v
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have hunit : ‖(‖v‖⁻¹) • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv0)),
          inv_mul_cancel₀ hvn]
      have h1 := hdir ((‖v‖⁻¹) • v) hunit
      have hLu : L ((‖v‖⁻¹) • v) = ‖v‖⁻¹ * L v := by rw [map_smul, smul_eq_mul]
      rw [hLu] at h1
      have h4 : (L v) ^ 2 ≤ (Real.sqrt (2 * N * f x) * ‖v‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        calc (L v) ^ 2 = ‖v‖ ^ 2 * (‖v‖⁻¹ * L v) ^ 2 := by field_simp
          _ ≤ ‖v‖ ^ 2 * (2 * N * f x) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = (2 * N * f x) * ‖v‖ ^ 2 := by ring
      rw [Real.norm_eq_abs]
      simpa [abs_of_nonneg (mul_nonneg hsqrt_nonneg (norm_nonneg _))] using (sq_le_sq.mp h4)
  calc ‖L‖ ^ 2 ≤ (Real.sqrt (2 * N * f x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = 2 * N * f x := Real.sq_sqrt (by positivity)

/-- `‖D²chi‖` is bounded by a positive constant: `iteratedFDeriv ℝ 2 chi` is continuous
(`chi_contDiff`) with compact support (`chi_hasCompactSupport`). -/
lemma chi_iteratedFDeriv_bound :
    ∃ N : ℝ, 0 < N ∧
      ∀ y : E3, ‖iteratedFDeriv ℝ 2 Submission.BoseGases.chi y‖ ≤ N := by
  obtain ⟨C, hC⟩ :=
    (Submission.BoseGases.chi_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
      (Submission.BoseGases.chi_contDiff.continuous_iteratedFDeriv (m := 2)
        (WithTop.coe_le_coe.2 le_top))
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun y => le_trans (hC y) (le_max_left _ _)⟩

/-- **Glaeser at the `ℓ`-scale factor.** There is `N ≥ 0` such that for every `ℓ > 0` the scaled
corpus bump `chiScale ℓ = chi(ℓ⁻¹ • ·)` satisfies the pointwise Glaeser inequality
`‖∇(chiScale ℓ) x‖² ≤ 2(N/ℓ²)·chiScale ℓ x`.

Route: `Work.BoseSWE.glaeserPointwise` (the pointwise Glaeser for a nonnegative `C²` function with
`‖D²f‖ ≤ N`) applied to `Submission.BoseGases.chi` (`chi_contDiff`, `chi_nonneg`, and a bound
`‖D²chi‖ ≤ C` from `chi_hasCompactSupport` + `ContDiff ℝ 2 chi`), followed by the chain rule
`fderiv ℝ (chiScale ℓ) x = ℓ⁻¹ • fderiv ℝ chi (ℓ⁻¹ • x)`
(`Work.BlockBound4.fderiv_chiScale_apply`, `Submission.BoseGases.chiScale_apply_smul`). -/
theorem chiScaleGlaeser :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        ≤ 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x := by
  obtain ⟨N, hNpos, hN⟩ := chi_iteratedFDeriv_bound
  refine ⟨N, le_of_lt hNpos, ?_⟩
  intro ℓ hℓ x
  have hfderiv : fderiv ℝ (Submission.BoseGases.chiScale ℓ) x
      = ℓ⁻¹ • fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x) := by
    ext v
    rw [Work.BlockBound4.fderiv_chiScale_apply, smul_apply, smul_eq_mul]
  have hcd : ContDiff ℝ 2 Submission.BoseGases.chi :=
    Submission.BoseGases.chi_contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  have hgl := glaeserPointwisePos hcd Submission.BoseGases.chi_nonneg hNpos hN ((ℓ⁻¹) • x)
  calc ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
      = ‖ℓ⁻¹ • fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x)‖ ^ 2 := by rw [hfderiv]
    _ = (ℓ⁻¹) ^ 2 * ‖fderiv ℝ Submission.BoseGases.chi ((ℓ⁻¹) • x)‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]; ring
    _ ≤ (ℓ⁻¹) ^ 2 * (2 * N * Submission.BoseGases.chi ((ℓ⁻¹) • x)) :=
        mul_le_mul_of_nonneg_left hgl (sq_nonneg _)
    _ = 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x := by
        simp only [Submission.BoseGases.chiScale]
        field_simp

end Work.BoseSWE

#print axioms Work.BoseSWE.chiScaleGlaeser
