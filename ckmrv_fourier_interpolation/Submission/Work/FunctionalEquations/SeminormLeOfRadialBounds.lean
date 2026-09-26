import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.RadialSpace.RadialSeminormEquiv
import Submission.Work.RadialSpace.tail_seminorm_le_radialSeminorm
import Submission.Work.RadialSpace.RadialSeminorm
import Submission.Work.RadialSpace.iteratedDeriv_intervalIntegral_param

/-!
# The Schwartz seminorm is bounded by radial-derivative bounds

This file proves `Work.FunctionalEquations.SeminormLeOfRadialBounds`: for a radial Schwartz
function `f` on `R^n` whose iterated *radial* derivatives satisfy pointwise bounds
`‖x‖ ^ k * ‖D^j f x‖ ≤ B j` (`j ≤ l`) and `‖D^j f x‖ ≤ B j` (`j ≤ 2 * l`), the `(k, l)`
Schwartz seminorm of `f` is bounded by a universal multiple of the sum of the `B j`.

The analytic content is the passage from radial derivatives to full Fréchet derivatives:

* on the unit ball, `iteratedFDeriv` of `Ψ ∘ ‖·‖²` is controlled by the derivatives of `Ψ`
  (`taylorComp_bound`) and the iterated half-derivatives of the profile are controlled by the
  derivatives of the profile (`evenHalfDeriv_iterate_Icc_uniform`);
* outside the unit ball one rescales, `F z = f (‖x‖ • z)`, applies `taylorComp_bound` at the
  unit vector `y₀ = ‖x‖⁻¹ • x` and uses the weighted bound
  `Work.FunctionalEquations.evenHalfDeriv_pow_mul_le` for the half-derivatives at `1`.

## Main results

* `Work.FunctionalEquations.pow_mul_abs_iteratedDeriv_sqrt_eq`
* `Work.FunctionalEquations.evenHalfDeriv_pow_mul_le`
* `Work.FunctionalEquations.SeminormLeOfRadialBounds`
-/

open scoped FourierTransform SchwartzMap

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology

section Helpers

open Work.RadialSpace

/-- The exact value of `u ^ (2 * s - 1) * ‖(√·)^{(s)} (u ^ 2)‖`: multiplying the `s`-th
derivative of the square root by `u ^ (2 * s - 1)` removes the negative power of `u`. -/
theorem pow_mul_abs_iteratedDeriv_sqrt_eq {s : ℕ} (hs : 1 ≤ s) {u : ℝ} (hu : 0 < u) :
    u ^ (2 * s - 1) * |iteratedDeriv s (fun r : ℝ => Real.sqrt r) (u ^ 2)| = |sqrtCoeff s| := by
  have hu2 : (0:ℝ) < u ^ 2 := by positivity
  have hz : (0:ℝ) ≤ (u ^ 2) ^ ((1:ℝ)/2 - (s:ℝ)) := Real.rpow_nonneg (le_of_lt hu2) _
  rw [iteratedDeriv_sqrt_eq s hu2, abs_mul, abs_of_nonneg hz]
  have key : u ^ (2 * s - 1) * (u ^ 2) ^ ((1:ℝ)/2 - (s:ℝ)) = 1 := by
    rw [← Real.rpow_natCast_mul (le_of_lt hu) 2 ((1:ℝ)/2 - (s:ℝ))]
    rw [← Real.rpow_natCast u (2 * s - 1)]
    rw [← Real.rpow_add hu]
    have hsub : ((2 * s - 1 : ℕ) : ℝ) = 2 * (s:ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2*s)]
      ring
    have h2 : ((2:ℕ):ℝ) = 2 := by norm_num
    rw [hsub, h2]
    have hexp : (2*(s:ℝ) - 1) + 2*((1:ℝ)/2 - (s:ℝ)) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  calc u ^ (2 * s - 1) * (|sqrtCoeff s| * (u ^ 2) ^ ((1:ℝ)/2 - (s:ℝ)))
      = (u ^ (2 * s - 1) * (u ^ 2) ^ ((1:ℝ)/2 - (s:ℝ))) * |sqrtCoeff s| := by ring
    _ = |sqrtCoeff s| := by rw [key, one_mul]

/-- **Weighted bound for the iterated half-derivative.**  For `u ≥ 1` the factor `u ^ (2 * m)`
compensates the negative powers of `u` present in `evenHalfDeriv^[m] g`, so that
`u ^ (2 * m) * ‖evenHalfDeriv^[m] g u‖` is bounded by a universal multiple of the sum of
`u ^ c * ‖g ^ (c) u‖`, `c ≤ m`.  This is the `u ≥ 1` companion of
`Work.RadialSpace.evenHalfDeriv_iterate_le`. -/
theorem evenHalfDeriv_pow_mul_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℝ → ℂ), ContDiff ℝ Smooth g → Function.Even g →
      ∀ u : ℝ, 1 ≤ u → u ^ (2*m) * ‖(evenHalfDeriv^[m]) g u‖ ≤
        C * ∑ c ∈ Finset.range (m+1), u^c * ‖iteratedDeriv c g u‖ := by
  set B : ℝ := ∑ k ∈ Finset.range (m + 1), |sqrtCoeff k| with hB
  have hB0 : 0 ≤ B := by rw [hB]; exact Finset.sum_nonneg (fun k _ => abs_nonneg (sqrtCoeff k))
  have hB1 : 1 ≤ B := by
    have hmem : 0 ∈ Finset.range (m+1) := Finset.mem_range.mpr (Nat.succ_pos m)
    have hle := Finset.single_le_sum (f := fun k => |sqrtCoeff k|)
      (fun k _ => abs_nonneg (sqrtCoeff k)) hmem
    rw [hB]
    simpa [sqrtCoeff_zero] using hle
  refine ⟨(Fintype.card (OrderedFinpartition m) : ℝ) * B ^ m,
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB0 m), ?_⟩
  intro g hg he u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu2 : (0:ℝ) < u ^ 2 := by positivity
  have h1 : (evenHalfDeriv^[m]) g u = iteratedDeriv m (fun s => g (Real.sqrt s)) (u ^ 2) := by
    have h := (iteratedDeriv_comp_sqrt hg he hu2 m).symm
    rwa [Real.sqrt_sq (le_of_lt hu0)] at h
  rw [h1]
  have hfb := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := g)
    (f := fun s : ℝ => Real.sqrt s) (x := u ^ 2) (n := Smooth) (i := m)
    (hg.contDiffAt) (Real.contDiffAt_sqrt (ne_of_gt hu2)) (coe_nat_le_smooth m)
  rw [show iteratedDeriv m (fun s => g (Real.sqrt s)) (u^2)
      = ∑ c : OrderedFinpartition m, (∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2)) from hfb]
  have hterm : ∀ c : OrderedFinpartition m,
      u^(2*m) * ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖
        ≤ B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖ := by
    intro c
    have hcnorm : (∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖)
        = ∏ i, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)| := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [Real.norm_eq_abs]
    have hprod : u^(2*m) * (∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖)
        ≤ B^m * u^(c.length) := by
      rw [hcnorm]
      have hfac : ∀ i : Fin c.length,
          u ^ (2 * c.partSize i - 1) * |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|
            = |sqrtCoeff (c.partSize i)| :=
        fun i => pow_mul_abs_iteratedDeriv_sqrt_eq (c.partSize_pos i) hu0
      have hsum : ∑ i : Fin c.length, c.partSize i = m := by
        have h := Fintype.card_congr c.equivSigma
        simpa only [Fintype.card_sigma, Fintype.card_fin] using h
      have hadd : (∑ i : Fin c.length, (2 * c.partSize i - 1)) + c.length = 2 * m := by
        have hA : (∑ i : Fin c.length, (2 * c.partSize i - 1)) +
            (∑ _i : Fin c.length, (1:ℕ)) = 2 * m := by
          rw [← Finset.sum_add_distrib]
          trans ∑ i : Fin c.length, 2 * c.partSize i
          · exact Finset.sum_congr rfl (fun i _ => by have := c.partSize_pos i; omega)
          · rw [← Finset.mul_sum, hsum]
        have hlen : (∑ _i : Fin c.length, (1:ℕ)) = c.length := by simp
        rwa [hlen] at hA
      have hstep2 : u ^ (∑ i : Fin c.length, (2 * c.partSize i - 1)) *
            (∏ i : Fin c.length, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|)
          = ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)| := by
        rw [← Finset.prod_pow_eq_pow_sum Finset.univ
              (fun i : Fin c.length => 2 * c.partSize i - 1) u,
            ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun i _ => hfac i)
      have hkey : u ^ (2*m) * (∏ i : Fin c.length, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|)
          = u^(c.length) * ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)| := by
        calc u ^ (2*m) * (∏ i : Fin c.length, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|)
            = u ^ ((∑ i : Fin c.length, (2 * c.partSize i - 1)) + c.length) *
                (∏ i : Fin c.length, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|) := by
              rw [hadd]
          _ = u^(c.length) * (u ^ (∑ i : Fin c.length, (2 * c.partSize i - 1)) *
                (∏ i : Fin c.length, |iteratedDeriv (c.partSize i) (fun r : ℝ => Real.sqrt r) (u^2)|)) := by
              rw [pow_add]; ring
          _ = u^(c.length) * ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)| := by rw [hstep2]
      rw [hkey]
      have hBle : ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)| ≤ B^m := by
        have heach : ∀ i : Fin c.length, |sqrtCoeff (c.partSize i)| ≤ B := by
          intro i
          rw [hB]
          have hmem : c.partSize i ∈ Finset.range (m+1) :=
            Finset.mem_range.mpr (Nat.lt_succ_of_le (c.partSize_le i))
          exact Finset.single_le_sum (f := fun k => |sqrtCoeff k|)
            (fun k _ => abs_nonneg (sqrtCoeff k)) hmem
        calc ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)|
            ≤ ∏ _i : Fin c.length, B := Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => heach i)
          _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ B ^ m := pow_le_pow_right₀ hB1 c.length_le
      calc u ^ c.length * ∏ i : Fin c.length, |sqrtCoeff (c.partSize i)|
          ≤ u ^ c.length * B ^ m := mul_le_mul_of_nonneg_left hBle (by positivity)
        _ = B^m * u^(c.length) := by ring
    have hnorm : ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖
        = (∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖) *
          ‖iteratedDeriv c.length g (Real.sqrt (u^2))‖ := by
      rw [norm_smul, norm_prod]
    rw [hnorm, Real.sqrt_sq (le_of_lt hu0)]
    calc u ^ (2*m) * ((∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖) *
          ‖iteratedDeriv c.length g u‖)
        = (u ^ (2*m) * (∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖)) *
          ‖iteratedDeriv c.length g u‖ := by ring
      _ ≤ (B^m * u^(c.length)) * ‖iteratedDeriv c.length g u‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖ := by ring
  calc u ^ (2*m) * ‖∑ c : OrderedFinpartition m, (∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
        iteratedDeriv c.length g (Real.sqrt (u^2))‖
      ≤ u ^ (2*m) * ∑ c : OrderedFinpartition m, ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ c : OrderedFinpartition m, u ^ (2*m) * ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ c : OrderedFinpartition m, B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖ :=
        Finset.sum_le_sum (fun c _ => hterm c)
    _ ≤ ((Fintype.card (OrderedFinpartition m) : ℝ) * B^m) * ∑ c ∈ Finset.range (m+1), u^c * ‖iteratedDeriv c g u‖ := by
        have hunif : ∀ c : OrderedFinpartition m,
            B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖
              ≤ B^m * ∑ i ∈ Finset.range (m+1), u^i * ‖iteratedDeriv i g u‖ := by
          intro c
          have hsingle : u^(c.length) * ‖iteratedDeriv c.length g u‖
              ≤ ∑ i ∈ Finset.range (m+1), u^i * ‖iteratedDeriv i g u‖ :=
            Finset.single_le_sum (f := fun i => u^i * ‖iteratedDeriv i g u‖)
              (fun i _ => by positivity)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le))
          have := mul_le_mul_of_nonneg_left hsingle (pow_nonneg hB0 m)
          calc B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖
              = B^m * (u^(c.length) * ‖iteratedDeriv c.length g u‖) := by ring
            _ ≤ B^m * ∑ i ∈ Finset.range (m+1), u^i * ‖iteratedDeriv i g u‖ := this
        calc ∑ c : OrderedFinpartition m, B^m * u^(c.length) * ‖iteratedDeriv c.length g u‖
            ≤ ∑ _c : OrderedFinpartition m, B^m * ∑ i ∈ Finset.range (m+1), u^i * ‖iteratedDeriv i g u‖ :=
              Finset.sum_le_sum (fun c _ => hunif c)
          _ = (Fintype.card (OrderedFinpartition m) : ℝ) *
                (B^m * ∑ i ∈ Finset.range (m+1), u^i * ‖iteratedDeriv i g u‖) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ((Fintype.card (OrderedFinpartition m) : ℝ) * B^m) * ∑ c ∈ Finset.range (m+1), u^c * ‖iteratedDeriv c g u‖ := by
              ring

/-- `iteratedDeriv` is additive in its order. -/
lemma iteratedDeriv_iteratedDeriv_eq (f : ℝ → ℂ) (n m : ℕ) :
    iteratedDeriv n (iteratedDeriv m f) = iteratedDeriv (n + m) f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      rw [← iteratedDeriv_succ (n := n + m)]
      congr 1
      omega

/-- Iterated derivatives of a smooth function are smooth. -/
lemma contDiff_iteratedDeriv_of_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ Smooth f) (n : ℕ) :
    ContDiff ℝ Smooth (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact hf.iterate_deriv n

/-- On the unit interval the `j`-th derivative of the `m`-fold half-derivative of `g` is
bounded by the supremum of `g ^ (2 * m + j)` on `[0,1]`.  This is the "compact" bound
complementary to `evenHalfDeriv_pow_mul_le`. -/
theorem evenHalfDeriv_Icc_le (m j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℝ → ℂ), ContDiff ℝ Smooth g →
      ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ N : ℝ,
        (∀ s ∈ Set.Icc (0:ℝ) 1, ‖iteratedDeriv (2*m+j) g s‖ ≤ N) →
        ‖iteratedDeriv j ((evenHalfDeriv^[m]) g) u‖ ≤ C*N := by
  suffices h : ∀ m j : ℕ, ∀ (g : ℝ → ℂ), ContDiff ℝ Smooth g →
      ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ N : ℝ,
        (∀ s ∈ Set.Icc (0:ℝ) 1, ‖iteratedDeriv (2*m+j) g s‖ ≤ N) →
        ‖iteratedDeriv j ((evenHalfDeriv^[m]) g) u‖ ≤ (1/2:ℝ)^m * N by
    exact ⟨(1/2:ℝ)^m, by positivity, h m j⟩
  intro m
  induction m with
  | zero =>
    intro j g hg u hu N hN
    simpa using hN u hu
  | succ m ih =>
    intro j g hg u hu N hN
    have hT : ContDiff ℝ Smooth ((evenHalfDeriv^[m]) g) := contDiff_iterate_evenHalfDeriv hg m
    have hφ : ContDiff ℝ Smooth (iteratedDeriv 2 ((evenHalfDeriv^[m]) g)) :=
      contDiff_iteratedDeriv_of_smooth hT 2
    have hfun : iteratedDeriv j ((evenHalfDeriv^[m+1]) g) u
        = (1/2 : ℂ) * iteratedDeriv j
            (fun u : ℝ => ∫ t in (0:ℝ)..1, iteratedDeriv 2 ((evenHalfDeriv^[m]) g) (u * t)) u := by
      have heq : (evenHalfDeriv^[m+1]) g
          = fun u : ℝ => (1/2 : ℂ) * ∫ t in (0:ℝ)..1,
              iteratedDeriv 2 ((evenHalfDeriv^[m]) g) (u*t) := by
        rw [Function.iterate_succ_apply']
        funext v
        rw [evenHalfDeriv_apply]
      rw [heq, iteratedDeriv_const_mul]
      exact (Work.RadialSpace.contDiff_parametric_integral _ hφ).contDiffAt.of_le
        (Work.RadialSpace.coe_nat_le_smooth j)
    rw [hfun]
    have hP := Work.RadialSpace.iteratedDeriv_intervalIntegral_param
      (iteratedDeriv 2 ((evenHalfDeriv^[m]) g)) hφ j u
    rw [hP]
    have hPeq : (fun t : ℝ => t^j * iteratedDeriv j (iteratedDeriv 2 ((evenHalfDeriv^[m]) g)) (u*t))
        = fun t : ℝ => t^j * iteratedDeriv (j+2) ((evenHalfDeriv^[m]) g) (u*t) := by
      funext t
      rw [iteratedDeriv_iteratedDeriv_eq ((evenHalfDeriv^[m]) g) j 2]
    rw [hPeq]
    have hN' : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖iteratedDeriv (2*m + (j+2)) g s‖ ≤ N := by
      intro s hs
      have hs' := hN s hs
      rwa [← show 2 * m + (j + 2) = 2 * (m+1) + j from by omega] at hs'
    have hbnd : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖t^j * iteratedDeriv (j+2) ((evenHalfDeriv^[m]) g) (u*t)‖ ≤ (1/2)^m * N := by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      have hut : u * t ∈ Set.Icc (0:ℝ) 1 :=
        ⟨mul_nonneg hu.1 htI.1, mul_le_one₀ hu.2 htI.1 htI.2⟩
      have htn : ‖(↑t : ℂ) ^ j‖ = t^j := by
        rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg htI.1 j)]
      rw [norm_mul, htn]
      calc t^j * ‖iteratedDeriv (j+2) ((evenHalfDeriv^[m]) g) (u*t)‖
          ≤ 1 * ((1/2)^m * N) :=
            mul_le_mul (pow_le_one₀ htI.1 htI.2) (ih (j+2) g hg (u*t) hut N hN')
              (norm_nonneg _) (by norm_num)
        _ = (1/2)^m * N := one_mul _
    calc ‖(1/2 : ℂ) * ∫ t in (0:ℝ)..1, t^j * iteratedDeriv (j+2) ((evenHalfDeriv^[m]) g) (u*t)‖
        = (1/2) * ‖∫ t in (0:ℝ)..1, t^j * iteratedDeriv (j+2) ((evenHalfDeriv^[m]) g) (u*t)‖ := by
          rw [norm_mul]; norm_num
      _ ≤ (1/2) * ((1/2)^m * N) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) hbnd
          rwa [show |(1:ℝ) - 0| = 1 from by norm_num, mul_one] at h1
      _ = (1/2:ℝ)^(m+1) * N := by ring

end Helpers

open scoped FourierTransform SchwartzMap
open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology

theorem SeminormLeOfRadialBounds {n : ℕ} [NeZero n] (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(E n, ℂ)), Radial (⇑f) → ∀ (B : ℕ → ℝ),
      (∀ j : ℕ, j ≤ l → ∀ x : E n, ‖x‖ ^ k * ‖radialDeriv j (⇑f) x‖ ≤ B j) →
      (∀ j : ℕ, j ≤ 2 * l → ∀ x : E n, ‖radialDeriv j (⇑f) x‖ ≤ B j) →
      (SchwartzMap.seminorm ℂ k l) f ≤
        C * ((∑ j ∈ Finset.range (l + 1), B j) + (∑ j ∈ Finset.range (2 * l + 1), B j)) := by
  classical
  obtain ⟨CT, hCT0, hCT⟩ := Work.RadialSpace.taylorComp_bound n l
  choose CU hCU using fun m : ℕ => evenHalfDeriv_Icc_le m 0
  choose CW hCW using fun m : ℕ => evenHalfDeriv_pow_mul_le m
  set CUs : ℝ := ∑ m ∈ Finset.range (l+1), CU m with hCUsdef
  set CWs : ℝ := ∑ m ∈ Finset.range (l+1), CW m with hCWsdef
  have hCUs0 : 0 ≤ CUs := by rw [hCUsdef]; exact Finset.sum_nonneg (fun m _ => (hCU m).1)
  have hCWs0 : 0 ≤ CWs := by rw [hCWsdef]; exact Finset.sum_nonneg (fun m _ => (hCW m).1)
  refine ⟨2^l * CT * (l+1) * (CUs + CWs + 1), by positivity, ?_⟩
  intro f hf B hB1 hB2
  set g : ℝ → ℂ := Work.RadialSpace.profile (⇑f) with hgdef
  have hgc : ContDiff ℝ Work.RadialSpace.Smooth g := by
    rw [hgdef]; exact Work.RadialSpace.profile_contDiff (f.smooth ⊤)
  have hge : Function.Even g := by rw [hgdef]; exact Work.RadialSpace.profile_even hf
  have hfg : ∀ y : E n, (⇑f) y = g ‖y‖ := by
    intro y; rw [hgdef]; exact Work.RadialSpace.profile_eq_of_radial hf y
  have hg_us : ∀ u : ℝ, ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => g (u * r)) := fun u =>
    hgc.comp (contDiff_const.mul contDiff_id)
  have hg_ue : ∀ u : ℝ, Function.Even (fun r : ℝ => g (u * r)) := fun u v => by
    show g (u * -v) = g (u * v)
    rw [mul_neg]
    exact hge (u * v)
  have hB1' : ∀ j, j ≤ l → ∀ u : ℝ, 0 ≤ u → u^k * ‖iteratedDeriv j g u‖ ≤ B j := by
    intro j hj u hu
    have h := hB1 j hj (realIncl (n := n) u)
    rw [Work.Sampling.realIncl_norm, abs_of_nonneg hu] at h
    have h2 : radialDeriv j (⇑f) (realIncl (n:=n) u) = iteratedDeriv j g u := by
      have hfun : (fun r : ℝ => (⇑f) (realIncl (n:=n) r)) = g := by rw [hgdef]; rfl
      rw [radialDeriv, Work.Sampling.realIncl_norm, abs_of_nonneg hu, hfun]
    rwa [h2] at h
  have hB2' : ∀ j, j ≤ 2*l → ∀ u : ℝ, 0 ≤ u → ‖iteratedDeriv j g u‖ ≤ B j := by
    intro j hj u hu
    have h := hB2 j hj (realIncl (n := n) u)
    have h2 : radialDeriv j (⇑f) (realIncl (n:=n) u) = iteratedDeriv j g u := by
      have hfun : (fun r : ℝ => (⇑f) (realIncl (n:=n) r)) = g := by rw [hgdef]; rfl
      rw [radialDeriv, Work.Sampling.realIncl_norm, abs_of_nonneg hu, hfun]
    rwa [h2] at h
  have hBnn : ∀ j, j ≤ 2*l → 0 ≤ B j := fun j hj => le_trans (norm_nonneg _) (hB2 j hj 0)
  have hsum1nn : 0 ≤ ∑ j ∈ Finset.range (l+1), B j :=
    Finset.sum_nonneg (fun j hj => hBnn j (by have := Finset.mem_range.mp hj; omega))
  have hsum2nn : 0 ≤ ∑ j ∈ Finset.range (2*l+1), B j :=
    Finset.sum_nonneg (fun j hj => hBnn j (by have := Finset.mem_range.mp hj; omega))
  have hMnn : 0 ≤ 2^l * CT * (l+1) * (CUs + CWs + 1) *
      ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) :=
    mul_nonneg (by positivity) (add_nonneg hsum1nn hsum2nn)
  have hpoint_ne : ∀ x : E n, x ≠ 0 →
      ‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖ ≤
        2^l * CT * (l+1) * (CUs + CWs + 1) *
          ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) := by
    intro x hx
    have hu0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    by_cases hge1 : (1:ℝ) ≤ ‖x‖
    · -- outside the unit ball: rescale
      set y0 : E n := ‖x‖⁻¹ • x with hy0def
      set Ψ : ℝ → ℂ := fun s => g (‖x‖ * Real.sqrt s) with hΨdef
      have hy0norm : ‖y0‖ = 1 := by
        rw [hy0def, norm_smul]
        have h1 : ‖(‖x‖⁻¹ : ℝ)‖ = ‖x‖⁻¹ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        rw [h1, inv_mul_eq_div, div_self (ne_of_gt hu0)]
      have huy0 : ‖x‖ • y0 = x := by rw [hy0def, smul_inv_smul₀ (ne_of_gt hu0)]
      have hΨs : ContDiffAt ℝ Work.RadialSpace.Smooth Ψ (‖y0‖^2) := by
        rw [hΨdef, hy0norm]
        norm_num
        exact hgc.contDiffAt.comp ((1:ℝ))
          ((contDiffAt_const (c := ‖x‖)).mul (Real.contDiffAt_sqrt (by norm_num)))
      have h1 := hCT Ψ y0 hΨs
      have heqF : (fun y : E n => Ψ (‖y‖^2)) = fun z : E n => (⇑f) (‖x‖ • z) := by
        funext z
        rw [hΨdef]
        simp only []
        rw [hfg (‖x‖ • z), norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
          Real.sqrt_sq (norm_nonneg z)]
      rw [heqF, hy0norm] at h1
      norm_num at h1
      have hscale : iteratedFDeriv ℝ l (fun z : E n => (⇑f) (‖x‖ • z)) y0
          = ‖x‖^l • iteratedFDeriv ℝ l (⇑f) (‖x‖ • y0) :=
        congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (a := ‖x‖) (f := ⇑f) (i := l)
          (f.smooth (l : ℕ∞))) y0
      rw [hscale, huy0] at h1
      have hsl : ‖‖x‖^l • iteratedFDeriv ℝ l (⇑f) x‖
          = ‖x‖^l * ‖iteratedFDeriv ℝ l (⇑f) x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) l)]
      rw [hsl] at h1
      have hconv : ∀ j : ℕ, ‖iteratedDeriv j Ψ 1‖ ≤
          CW j * ∑ c ∈ Finset.range (j+1), ‖x‖^c * ‖iteratedDeriv c g ‖x‖‖ := by
        intro j
        have hs : iteratedDeriv j Ψ 1
            = (Work.RadialSpace.evenHalfDeriv^[j]) (fun r : ℝ => g (‖x‖ * r)) 1 := by
          rw [hΨdef]
          rw [show (fun s : ℝ => g (‖x‖ * Real.sqrt s))
              = (fun s => (fun r : ℝ => g (‖x‖ * r)) (Real.sqrt s)) from rfl]
          rw [Work.RadialSpace.iteratedDeriv_comp_sqrt (hg_us ‖x‖) (hg_ue ‖x‖)
            (by norm_num : (0:ℝ) < 1) j]
          norm_num
        rw [hs]
        have hW := (hCW j).2 (fun r : ℝ => g (‖x‖ * r)) (hg_us ‖x‖) (hg_ue ‖x‖) 1 le_rfl
        simp only [one_pow, one_mul] at hW
        have hterm : ∀ c : ℕ, ‖iteratedDeriv c (fun r : ℝ => g (‖x‖ * r)) 1‖
            = ‖x‖^c * ‖iteratedDeriv c g ‖x‖‖ := by
          intro c
          rw [congrFun (iteratedDeriv_comp_const_smul (f := g) (c := ‖x‖) (n := c)
            (hgc.of_le (Work.RadialSpace.coe_nat_le_smooth c))) 1]
          rw [mul_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) c)]
        rw [Finset.sum_congr rfl (fun c _ => hterm c)] at hW
        exact hW
      have hstep : ‖x‖^l * (‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖)
          ≤ ‖x‖^l * (CT * 2^l * (CWs * (∑ c ∈ Finset.range (l+1), B c))) := by
        have h2 : ‖x‖^l * (‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖)
            = ‖x‖^k * (‖x‖^l * ‖iteratedFDeriv ℝ l (⇑f) x‖) := by ring
        rw [h2]
        have hA : ‖x‖^k * (CT * 2^l * ∑ j ∈ Finset.range (l+1), ‖iteratedDeriv j Ψ 1‖)
            = CT * 2^l * ∑ j ∈ Finset.range (l+1),
                (‖x‖^k * ‖iteratedDeriv j Ψ 1‖) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        have hB : ∑ j ∈ Finset.range (l+1), (‖x‖^k * ‖iteratedDeriv j Ψ 1‖)
            ≤ ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                (‖x‖^k * (‖x‖^c * ‖iteratedDeriv c g ‖x‖‖)) := by
          apply Finset.sum_le_sum
          intro j _
          calc ‖x‖^k * ‖iteratedDeriv j Ψ 1‖
              ≤ ‖x‖^k * (CW j * ∑ c ∈ Finset.range (j+1),
                    ‖x‖^c * ‖iteratedDeriv c g ‖x‖‖) :=
                mul_le_mul_of_nonneg_left (hconv j) (pow_nonneg (norm_nonneg x) k)
            _ = CW j * ∑ c ∈ Finset.range (j+1),
                  (‖x‖^k * (‖x‖^c * ‖iteratedDeriv c g ‖x‖‖)) := by
                simp only [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro c _
                ring
        have hC : ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                (‖x‖^k * (‖x‖^c * ‖iteratedDeriv c g ‖x‖‖))
            = ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                ‖x‖^(k+c) * ‖iteratedDeriv c g ‖x‖‖ := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          rw [← mul_assoc, pow_add]
        have hD : ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                ‖x‖^(k+c) * ‖iteratedDeriv c g ‖x‖‖
            ≤ ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1), ‖x‖^l * B c := by
          apply Finset.sum_le_sum
          intro j hj
          apply mul_le_mul_of_nonneg_left _ (hCW j).1
          apply Finset.sum_le_sum
          intro c hc
          have hcl : c ≤ l := by
            have h1 := Finset.mem_range.mp hc; have h2 := Finset.mem_range.mp hj; omega
          by_cases hkc : l ≤ k+c
          · calc ‖x‖^(k+c) * ‖iteratedDeriv c g ‖x‖‖
                = ‖x‖^l * (‖x‖^(k+c-l) * ‖iteratedDeriv c g ‖x‖‖) := by
                  conv_lhs => rw [show k + c = (k + c - l) + l from (Nat.sub_add_cancel hkc).symm]
                  rw [pow_add]
                  ring
              _ ≤ ‖x‖^l * (‖x‖^k * ‖iteratedDeriv c g ‖x‖‖) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact mul_le_mul_of_nonneg_right
                    (pow_le_pow_right₀ hge1 (by omega)) (norm_nonneg _)
              _ ≤ ‖x‖^l * B c :=
                  mul_le_mul_of_nonneg_left (hB1' c hcl ‖x‖ (norm_nonneg x)) (by positivity)
          · calc ‖x‖^(k+c) * ‖iteratedDeriv c g ‖x‖‖
                ≤ ‖x‖^l * ‖iteratedDeriv c g ‖x‖‖ :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hge1 (by omega)) (norm_nonneg _)
              _ ≤ ‖x‖^l * B c :=
                  mul_le_mul_of_nonneg_left (hB2' c (by omega) ‖x‖ (norm_nonneg x)) (by positivity)
        have hE : ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1), ‖x‖^l * B c
            ≤ ‖x‖^l * (CWs * ∑ c ∈ Finset.range (l+1), B c) := by
          have hin : ∀ j ∈ Finset.range (l+1),
              CW j * ∑ c ∈ Finset.range (j+1), ‖x‖^l * B c
                ≤ CW j * (‖x‖^l * ∑ c ∈ Finset.range (l+1), B c) := by
            intro j hj
            have hjl : j + 1 ≤ l + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
            apply mul_le_mul_of_nonneg_left _ (hCW j).1
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [Finset.range_subset_range]
              exact hjl
            · intro i hi _
              exact mul_nonneg (by positivity)
                (hBnn i (by have := Finset.mem_range.mp hi; omega))
          calc ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1), ‖x‖^l * B c
              ≤ ∑ j ∈ Finset.range (l+1), CW j * (‖x‖^l * ∑ c ∈ Finset.range (l+1), B c) :=
                Finset.sum_le_sum hin
            _ = (∑ j ∈ Finset.range (l+1), CW j) *
                  (‖x‖^l * ∑ c ∈ Finset.range (l+1), B c) := by rw [Finset.sum_mul]
            _ = ‖x‖^l * (CWs * ∑ c ∈ Finset.range (l+1), B c) := by rw [hCWsdef]; ring
        calc ‖x‖^k * (‖x‖^l * ‖iteratedFDeriv ℝ l (⇑f) x‖)
            ≤ ‖x‖^k * (CT * 2^l * ∑ j ∈ Finset.range (l+1), ‖iteratedDeriv j Ψ 1‖) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg x) k)
          _ = CT * 2^l * ∑ j ∈ Finset.range (l+1), (‖x‖^k * ‖iteratedDeriv j Ψ 1‖) := hA
          _ ≤ CT * 2^l * ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                (‖x‖^k * (‖x‖^c * ‖iteratedDeriv c g ‖x‖‖)) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
          _ = CT * 2^l * ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                ‖x‖^(k+c) * ‖iteratedDeriv c g ‖x‖‖ := by rw [hC]
          _ ≤ CT * 2^l * ∑ j ∈ Finset.range (l+1), CW j * ∑ c ∈ Finset.range (j+1),
                ‖x‖^l * B c := mul_le_mul_of_nonneg_left hD (by positivity)
          _ ≤ CT * 2^l * (‖x‖^l * (CWs * ∑ c ∈ Finset.range (l+1), B c)) :=
              mul_le_mul_of_nonneg_left hE (by positivity)
          _ = ‖x‖^l * (CT * 2^l * (CWs * (∑ c ∈ Finset.range (l+1), B c))) := by ring
      have hfin : ‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖
          ≤ CT * 2^l * (CWs * (∑ c ∈ Finset.range (l+1), B c)) :=
        le_of_mul_le_mul_left hstep (pow_pos hu0 l)
      calc ‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖
          ≤ CT * 2^l * (CWs * (∑ c ∈ Finset.range (l+1), B c)) := hfin
        _ ≤ 2^l * CT * (l+1) * (CUs + CWs + 1) *
              ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) := by
            have hA : 0 ≤ CT * 2^l := by positivity
            have hCWsle : CWs ≤ (l+1 : ℝ) * (CUs + CWs + 1) := by
              have h1 : (1:ℝ) ≤ (l+1 : ℝ) := by push_cast [Nat.cast_add, Nat.cast_one]; linarith
              nlinarith [hCUs0, hCWs0, h1]
            have hCle : (∑ j ∈ Finset.range (l+1), B j) ≤
                (∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j) :=
              le_add_of_nonneg_right hsum2nn
            calc CT * 2^l * (CWs * (∑ j ∈ Finset.range (l+1), B j))
                ≤ CT * 2^l * (((l+1 : ℝ) * (CUs + CWs + 1)) *
                    (∑ j ∈ Finset.range (l+1), B j)) := by
                  apply mul_le_mul_of_nonneg_left _ hA
                  exact mul_le_mul_of_nonneg_right hCWsle hsum1nn
              _ = 2^l * CT * (l+1) * (CUs + CWs + 1) *
                    (∑ j ∈ Finset.range (l+1), B j) := by ring
              _ ≤ 2^l * CT * (l+1) * (CUs + CWs + 1) *
                    ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) :=
                  mul_le_mul_of_nonneg_left hCle (by positivity)
    · -- inside the unit ball
      have hlt : ‖x‖ < 1 := not_le.mp hge1
      set Ψ : ℝ → ℂ := fun s => g (Real.sqrt s) with hΨdef
      have hΨs : ContDiffAt ℝ Work.RadialSpace.Smooth Ψ (‖x‖^2) := by
        rw [hΨdef]
        exact hgc.contDiffAt.comp (‖x‖^2)
          (Real.contDiffAt_sqrt (pow_ne_zero 2 (ne_of_gt hu0)))
      have h1 := hCT Ψ x hΨs
      have heqF : (fun y : E n => Ψ (‖y‖^2)) = ⇑f := by
        funext y
        rw [hΨdef]
        simp only []
        rw [Real.sqrt_sq (norm_nonneg y), ← hfg y]
      rw [heqF] at h1
      have hconv : ∀ j ∈ Finset.range (l+1), ‖iteratedDeriv j Ψ (‖x‖^2)‖ ≤ CU j * B (2*j) := by
        intro j hj
        have hj' : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h2 : iteratedDeriv j Ψ (‖x‖^2) = (Work.RadialSpace.evenHalfDeriv^[j]) g ‖x‖ := by
          rw [hΨdef]
          rw [Work.RadialSpace.iteratedDeriv_comp_sqrt hgc hge (pow_pos hu0 2) j,
            Real.sqrt_sq (norm_nonneg x)]
        rw [h2]
        exact (hCU j).2 g hgc ‖x‖ ⟨norm_nonneg x, le_of_lt hlt⟩ (B (2*j))
          (fun s hs => by
            have := hB2' (2*j) (by omega) s hs.1
            simpa using this)
      have himg : (∑ j ∈ Finset.range (l+1), B (2*j)) ≤ ∑ i ∈ Finset.range (2*l+1), B i := by
        have himg' : (∑ j ∈ Finset.range (l+1), B (2*j))
            = ∑ i ∈ (Finset.range (l+1)).image (fun j => 2*j), B i := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          simp only [] at hab
          omega
        rw [himg']
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
        · intro i hi _
          exact hBnn i (by have := Finset.mem_range.mp hi; omega)
      have hsumCU : 0 ≤ ∑ j ∈ Finset.range (l+1), CU j * B (2*j) :=
        Finset.sum_nonneg (fun j hj => mul_nonneg (hCU j).1
          (hBnn (2*j) (by have := Finset.mem_range.mp hj; omega)))
      have hbnd : (∑ j ∈ Finset.range (l+1), CU j * B (2*j)) ≤
          CUs * (∑ i ∈ Finset.range (2*l+1), B i) := by
        have h1' : (∑ j ∈ Finset.range (l+1), CU j * B (2*j)) ≤
            CUs * (∑ j ∈ Finset.range (l+1), B (2*j)) := by
          rw [hCUsdef, Finset.sum_mul]
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hle : B (2*j) ≤ ∑ i ∈ Finset.range (l+1), B (2*i) :=
            Finset.single_le_sum (f := fun i => B (2*i))
              (fun i hi => hBnn (2*i) (by have := Finset.mem_range.mp hi; omega)) hj
          exact mul_le_mul_of_nonneg_left hle (hCU j).1
        exact h1'.trans (mul_le_mul_of_nonneg_left himg hCUs0)
      calc ‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖
          ≤ ‖x‖^k * (CT * (1 + ‖x‖)^l *
              ∑ j ∈ Finset.range (l+1), ‖iteratedDeriv j Ψ (‖x‖^2)‖) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg x) k)
        _ ≤ ‖x‖^k * (CT * (1 + ‖x‖)^l *
              ∑ j ∈ Finset.range (l+1), CU j * B (2*j)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg x) k)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum hconv
        _ ≤ 1 * (CT * 2^l * (CUs * (∑ i ∈ Finset.range (2*l+1), B i))) := by
            have hxk : ‖x‖^k ≤ 1 := pow_le_one₀ (norm_nonneg x) (le_of_lt hlt)
            have h2l : (1 + ‖x‖)^l ≤ 2^l :=
              pow_le_pow_left₀ (by positivity) (by linarith) l
            calc ‖x‖^k * (CT * (1 + ‖x‖)^l * ∑ j ∈ Finset.range (l+1), CU j * B (2*j))
                ≤ 1 * (CT * (1 + ‖x‖)^l * ∑ j ∈ Finset.range (l+1), CU j * B (2*j)) :=
                  mul_le_mul_of_nonneg_right hxk
                    (mul_nonneg (mul_nonneg hCT0 (by positivity)) hsumCU)
              _ ≤ 1 * (CT * 2^l * ∑ j ∈ Finset.range (l+1), CU j * B (2*j)) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left h2l hCT0) hsumCU
              _ ≤ 1 * (CT * 2^l * (CUs * (∑ i ∈ Finset.range (2*l+1), B i))) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ ≤ 2^l * CT * (l+1) * (CUs + CWs + 1) *
              ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) := by
            have hCUsle : CUs ≤ (l+1 : ℝ) * (CUs + CWs + 1) := by
              have h1 : (1:ℝ) ≤ (l+1 : ℝ) := by push_cast [Nat.cast_add, Nat.cast_one]; linarith
              nlinarith [hCUs0, hCWs0, h1]
            have hS2 : (∑ i ∈ Finset.range (2*l+1), B i) ≤
                (∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j) :=
              le_add_of_nonneg_left hsum1nn
            calc 1 * (CT * 2^l * (CUs * (∑ i ∈ Finset.range (2*l+1), B i)))
                ≤ 1 * (CT * 2^l * (((l+1:ℝ) * (CUs + CWs + 1)) *
                    (∑ i ∈ Finset.range (2*l+1), B i))) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact mul_le_mul_of_nonneg_right hCUsle hsum2nn
              _ = 2^l * CT * (l+1) * (CUs + CWs + 1) *
                    (∑ i ∈ Finset.range (2*l+1), B i) := by ring
              _ ≤ 2^l * CT * (l+1) * (CUs + CWs + 1) *
                    ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) :=
                  mul_le_mul_of_nonneg_left hS2 (by positivity)
  have hpoint : ∀ x : E n, ‖x‖^k * ‖iteratedFDeriv ℝ l (⇑f) x‖ ≤
      2^l * CT * (l+1) * (CUs + CWs + 1) *
        ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have hclosed : IsClosed {y : E n | ‖y‖^k * ‖iteratedFDeriv ℝ l (⇑f) y‖ ≤
          2^l * CT * (l+1) * (CUs + CWs + 1) *
            ((∑ j ∈ Finset.range (l+1), B j) + (∑ j ∈ Finset.range (2*l+1), B j))} := by
        refine isClosed_le ?_ continuous_const
        refine Continuous.mul (continuous_norm.pow k) ?_
        exact ((f.smooth l).continuous_iteratedFDeriv (m := l) le_rfl).norm
      have hv : realIncl (n := n) 1 ≠ 0 := by
        intro h0
        have h1 := congrArg norm h0
        rw [Work.Sampling.realIncl_norm_one, norm_zero] at h1
        norm_num at h1
      have htend : Tendsto (fun m : ℕ => ((m:ℝ)+1)⁻¹ • realIncl (n := n) 1) atTop (𝓝 (0 : E n)) := by
        have h1 : Tendsto (fun m : ℕ => ((m:ℝ)+1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        simpa using h1.smul_const (realIncl (n := n) 1)
      refine hclosed.mem_of_tendsto htend (Eventually.of_forall (fun m => ?_))
      refine hpoint_ne (((m:ℝ)+1)⁻¹ • realIncl (n := n) 1) ?_
      intro h0
      have h1 := congrArg norm h0
      rw [norm_smul, Work.Sampling.realIncl_norm_one, mul_one, norm_zero] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ (m:ℝ)+1))] at h1
      have h3 := inv_eq_zero.mp h1
      have h4 : (0:ℝ) < (m:ℝ)+1 := by positivity
      linarith
    · exact hpoint_ne x hx
  rw [SchwartzMap.seminorm_apply]
  refine csInf_le ⟨0, fun c hc => hc.1⟩ ⟨hMnn, hpoint⟩

end Work.FunctionalEquations
