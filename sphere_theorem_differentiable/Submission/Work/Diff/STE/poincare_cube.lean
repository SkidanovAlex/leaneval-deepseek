import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.norm_sq_Lp_eq_integral
import Submission.Work.Diff.STE.trigPoly_dense_L2
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.integral_mul_star_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Poincaré (Wirtinger) inequality on the unit torus cube

`Work.Diff.STE.poincare_cube`: there is a constant `C` such that every `C¹`, `1`-periodic
complex function `f` on `(0,1]^ι` with mean zero satisfies

  `∫_{cube} ‖f‖² ≤ C · Σᵢ ∫_{cube} ‖∂ᵢ f‖²`.

The proof is the Fourier proof, carried out with the tools of the STE Layer-A development; no
`L²` completeness/Parseval for arbitrary functions is used (only Bessel, which is proved in
`bessel_continuous`).  The constant obtained is the sharp one, `1/(2π)²`.

## Structure

* `tsum_fourierCoeff_sq_le`: the Fourier side inequality
  `Σ_k ‖û(k)‖² ≤ (1/4π²) Σᵢ ∫ ‖∂ᵢ f‖²` for a mean-zero `C¹` periodic `f`.  For `k ≠ 0` we have
  `1 ≤ Σᵢ kᵢ²`, so `‖û(k)‖² ≤ (1/4π²) Σᵢ (2π kᵢ)² ‖û(k)‖²`; summing and using
  `fourierCoeff (∂ᵢ f) k = 2πi kᵢ · û(k)` (`fourierCoeff_pd`) together with Bessel's inequality
  for the continuous functions `∂ᵢ f` gives the claim.  The mean-zero hypothesis is used exactly
  at `k = 0`: `û(0) = ∫_{cube} f = 0`.
* `pairing_bound` (+ `integral_mul_star_trigPoly`): approximating `f` in `L²` by a trigonometric
  polynomial `T` with `∫‖f − T‖² < ε²` (`trigPoly_dense_L2`), the pairing `‖∫ f · conj T‖` is
  bounded by `Σ_k ‖û(k)‖² + ε √(Σ_k ‖û(k)‖²)`: expand the pairing against the coefficients of
  `T`, insert `û`, and use Cauchy–Schwarz (finset form, `Real.sum_mul_le_sqrt_mul_sqrt`) plus
  Bessel's inequality for `f − T`.
* `poincare_cube`: Cauchy–Schwarz on the cube (`integral_mul_star_le`) applied to the
  decomposition `∫ f conj f = ∫ f conj (f − T) + ∫ f conj T` gives
  `X ≤ A + ε (√X + √A)` for every `ε > 0`, where `X = ∫‖f‖²` and `A = Σ_k ‖û(k)‖²`; letting
  `ε → 0` (via `le_of_forall_pos_le_add`) yields `X ≤ A`, and `A ≤ (1/4π²) Σᵢ ∫‖∂ᵢ f‖²` is
  `tsum_fourierCoeff_sq_le`.

The use of `T` in the *second* slot of the pairing (rather than Cauchy–Schwarz on `L²` norms) is
what avoids needing Parseval/completeness: only the upper bounds Bessel + density are needed.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE

/-! ## Fourier coefficients of trigonometric polynomials -/

theorem fourierCoeff_trigPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : (ι → ℤ) →₀ ℂ) (m : ι → ℤ) :
    fourierCoeff (fun x : ι → ℝ => ∑ k ∈ p.support, p k * fourierExp k x) m
      = if m ∈ p.support then p m else 0 := by
  rw [fourierCoeff]
  have hpt : ∀ x : ι → ℝ,
      fourierExp (-m) x * (∑ k ∈ p.support, p k * fourierExp k x)
        = ∑ k ∈ p.support, p k * fourierExp (k - m) x := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : fourierExp (-m) x * fourierExp k x = fourierExp (k - m) x := by
      rw [BesselCont.fourierExp_add_char (-m) k x]
      congr 1
      ring
    calc fourierExp (-m) x * (p k * fourierExp k x)
        = p k * (fourierExp (-m) x * fourierExp k x) := by ring
      _ = p k * fourierExp (k - m) x := by rw [h1]
  rw [funext hpt]
  rw [MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul]
    simp_rw [integral_fourierExp]
    rw [← Finset.sum_ite_eq' p.support m (fun k => p k)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k - m = 0
    · have hkm : k = m := sub_eq_zero.mp h
      simp [hkm]
    · have hkm : k ≠ m := fun hh => h (sub_eq_zero.mpr hh)
      simp [h, hkm]
  · intro k _
    exact integrableOn_unitCube_of_continuous
      (continuous_const.mul (contDiff_fourierExp (k - m)).continuous)

/-! ## Norms of the Fourier coefficients of `∂ᵢ f` -/

lemma norm_two_pi_I_int (k : ℤ) : ‖(2 * Real.pi * Complex.I * (k : ℂ))‖ ^ 2
    = (2 * Real.pi * (k : ℝ)) ^ 2 := by
  have hcast : (2 * Real.pi * Complex.I * ((k : ℤ) : ℂ))
      = (((2 * Real.pi * (k : ℝ) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [hcast, norm_mul, Complex.norm_I, mul_one, Complex.sq_norm, Complex.normSq_ofReal,
    pow_two]

lemma fourierCoeff_pd_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hf : ContDiff ℝ 1 f) (hper : Periodic1 f) :
    ‖fourierCoeff (pd i f) k‖ ^ 2
      = (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖fourierCoeff f k‖ ^ 2 := by
  rw [fourierCoeff_pd i f k hf (hper i), norm_mul, mul_pow]
  have hnorm : ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ ^ 2
      = (2 * Real.pi * (k i : ℝ)) ^ 2 := norm_two_pi_I_int (k i)
  rw [hnorm]

/-! ## The Fourier side Poincaré bound -/

theorem tsum_fourierCoeff_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ 1 f) (hper : Periodic1 f)
    (hmean : ∫ x in unitCube, f x = 0) :
    ∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2
      ≤ (1 / (4 * Real.pi ^ 2))
        * ∑ i, ∫ x in unitCube, ‖pd i f x‖ ^ 2 := by
  have hu0 : fourierCoeff f 0 = 0 := by
    rw [fourierCoeff]
    have h1 : ∀ x : ι → ℝ, fourierExp (-(0 : ι → ℤ)) x * f x = f x := by
      intro x; simp [fourierExp]
    rw [funext h1, hmean]
  have hHi : ∀ i : ι, Summable (fun k : ι → ℤ =>
      (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖fourierCoeff f k‖ ^ 2) := by
    intro i
    have hb := (bessel_continuous (pd i f) (continuous_pd hf i)).1
    refine hb.congr (fun k => fourierCoeff_pd_norm_sq i f k hf hper)
  set F : (ι → ℤ) → ℝ := fun k => ‖fourierCoeff f k‖ ^ 2 with hFdef
  set G : (ι → ℤ) → ℝ := fun k => (∑ i, ((k i : ℝ)) ^ 2) * F k with hGdef
  have hF : Summable F := (bessel_continuous f hf.continuous).1
  have hkey : ∀ k : ι → ℤ, G k
      = (1 / (4 * Real.pi ^ 2)) * ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k := by
    intro k
    show (∑ i, ((k i : ℝ)) ^ 2) * F k
      = (1 / (4 * Real.pi ^ 2)) * ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hG : Summable G := by
    have h1 : Summable (fun k : ι → ℤ =>
        (1 / (4 * Real.pi ^ 2)) * ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k) :=
      (summable_sum (fun i _ => hHi i)).mul_left (1 / (4 * Real.pi ^ 2))
    exact h1.congr (fun k => (hkey k).symm)
  have hpt : ∀ k : ι → ℤ, F k ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [hFdef, hGdef, hu0]
    · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
        by_contra h
        push Not at h
        exact hk (funext fun i => by simpa using h i)
      have h1 : (1 : ℝ) ≤ ((k i : ℝ)) ^ 2 := by
        have h2 : (1 : ℤ) ≤ (k i) ^ 2 := by
          rcases lt_or_gt_of_ne hi with h | h
          · have h3 : k i ≤ -1 := by omega
            nlinarith
          · have h3 : 1 ≤ k i := by omega
            nlinarith
        exact_mod_cast h2
      have h3 : (1 : ℝ) ≤ ∑ j, ((k j : ℝ)) ^ 2 :=
        le_trans h1 (Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      calc F k = 1 * F k := by ring
        _ ≤ (∑ j, ((k j : ℝ)) ^ 2) * F k :=
            mul_le_mul_of_nonneg_right h3 (by rw [hFdef]; positivity)
        _ = G k := by rw [hGdef]
  refine le_trans (Summable.tsum_le_tsum hpt hF hG) ?_
  have heq : ∑' k : ι → ℤ, G k
      = (1 / (4 * Real.pi ^ 2))
        * ∑ i, ∑' k : ι → ℤ, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k := by
    rw [show (∑' k : ι → ℤ, G k)
        = ∑' k : ι → ℤ, (1 / (4 * Real.pi ^ 2))
            * ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k from tsum_congr hkey]
    rw [tsum_mul_left,
      Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hHi i)]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  calc ∑' k : ι → ℤ, (2 * Real.pi * (k i : ℝ)) ^ 2 * F k
      = ∑' k : ι → ℤ, ‖fourierCoeff (pd i f) k‖ ^ 2 := by
        apply tsum_congr
        intro k
        show (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖fourierCoeff f k‖ ^ 2
          = ‖fourierCoeff (pd i f) k‖ ^ 2
        exact (fourierCoeff_pd_norm_sq i f k hf hper).symm
    _ ≤ ∫ x in unitCube, ‖pd i f x‖ ^ 2 :=
        (bessel_continuous (pd i f) (continuous_pd hf i)).2

/-! ## The `L²` pairing with a trigonometric polynomial -/

lemma integral_mul_star_trigPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f) (p : (ι → ℤ) →₀ ℂ) :
    (∫ x in unitCube, f x * star (∑ k ∈ p.support, p k * fourierExp k x))
      = ∑ k ∈ p.support, star (p k) * fourierCoeff f k := by
  have hpt : ∀ x : ι → ℝ,
      f x * star (∑ k ∈ p.support, p k * fourierExp k x)
        = ∑ k ∈ p.support, star (p k) * (f x * fourierExp (-k) x) := by
    intro x
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [star_mul, BesselCont.star_fourierExp_char k x]
    ring
  rw [funext hpt, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [fourierCoeff]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · intro k _
    exact integrableOn_unitCube_of_continuous
      (continuous_const.mul (hf.mul (contDiff_fourierExp (-k)).continuous))

lemma fourierCoeff_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (k : ι → ℤ) :
    fourierCoeff (fun x => f x - g x) k = fourierCoeff f k - fourierCoeff g k := by
  have h1 : Integrable (fun x : ι → ℝ => fourierExp (-k) x * f x)
      (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous ((contDiff_fourierExp (-k)).continuous.mul hf)
  have h2 : Integrable (fun x : ι → ℝ => fourierExp (-k) x * g x)
      (volume.restrict unitCube) :=
    integrableOn_unitCube_of_continuous ((contDiff_fourierExp (-k)).continuous.mul hg)
  simp only [fourierCoeff]
  rw [← MeasureTheory.integral_sub h1 h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The pairing of `f` with a trigonometric polynomial is bounded by the `ℓ²` norm of the
Fourier coefficients of `f` plus the approximation error. -/
lemma pairing_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f) (p : (ι → ℤ) →₀ ℂ) (ε : ℝ)
    (hε : 0 < ε)
    (hA : Summable (fun k : ι → ℤ => ‖fourierCoeff f k‖ ^ 2))
    (hE : ∫ x in unitCube, ‖f x - ∑ k ∈ p.support, p k * fourierExp k x‖ ^ 2 < ε ^ 2) :
    ‖∑ k ∈ p.support, star (p k) * fourierCoeff f k‖
      ≤ (∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2)
        + ε * Real.sqrt (∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2) := by
  set A : ℝ := ∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2 with hAdef
  set T : (ι → ℝ) → ℂ := fun x => ∑ k ∈ p.support, p k * fourierExp k x with hTdef
  have hTcont : Continuous T := continuous_finsetSum _ (fun k _ =>
    continuous_const.mul (contDiff_fourierExp k).continuous)
  have hA0 : 0 ≤ A := tsum_nonneg fun k => by positivity
  -- Step 1: triangle inequality
  have h1 : ‖∑ k ∈ p.support, star (p k) * fourierCoeff f k‖
      ≤ ∑ k ∈ p.support, ‖p k‖ * ‖fourierCoeff f k‖ := by
    calc ‖∑ k ∈ p.support, star (p k) * fourierCoeff f k‖
        ≤ ∑ k ∈ p.support, ‖star (p k) * fourierCoeff f k‖ := norm_sum_le _ _
      _ = ∑ k ∈ p.support, ‖p k‖ * ‖fourierCoeff f k‖ := by simp
  -- Step 2: insert the difference
  have h2 : ∑ k ∈ p.support, ‖p k‖ * ‖fourierCoeff f k‖
      ≤ ∑ k ∈ p.support, (‖p k - fourierCoeff f k‖ + ‖fourierCoeff f k‖)
          * ‖fourierCoeff f k‖ := by
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc ‖p k‖ = ‖(p k - fourierCoeff f k) + fourierCoeff f k‖ := by ring_nf
      _ ≤ ‖p k - fourierCoeff f k‖ + ‖fourierCoeff f k‖ := norm_add_le _ _
  -- Step 3: the error terms are bounded by the approximation error
  have hsub : ∀ k ∈ p.support, ‖p k - fourierCoeff f k‖
      = ‖fourierCoeff (fun x => f x - T x) k‖ := by
    intro k hk
    rw [fourierCoeff_sub f T hf hTcont k, hTdef, fourierCoeff_trigPoly p k]
    simp only [hk, ↓reduceIte]
    exact norm_sub_rev _ _
  have hEsum : ∑ k ∈ p.support, ‖fourierCoeff (fun x => f x - T x) k‖ ^ 2
      ≤ ∫ x in unitCube, ‖f x - T x‖ ^ 2 := by
    have hb := bessel_continuous (fun x => f x - T x) (hf.sub hTcont)
    calc ∑ k ∈ p.support, ‖fourierCoeff (fun x => f x - T x) k‖ ^ 2
        ≤ ∑' k : ι → ℤ, ‖fourierCoeff (fun x => f x - T x) k‖ ^ 2 :=
          Summable.sum_le_tsum _ (fun k _ => by positivity) hb.1
      _ ≤ ∫ x in unitCube, ‖f x - T x‖ ^ 2 := hb.2
  have hsqrtE : Real.sqrt (∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ ^ 2) ≤ ε := by
    have h3 : ∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ ^ 2 < ε ^ 2 := by
      calc ∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ ^ 2
          = ∑ k ∈ p.support, ‖fourierCoeff (fun x => f x - T x) k‖ ^ 2 := by
            apply Finset.sum_congr rfl
            exact fun k hk => by rw [hsub k hk]
        _ ≤ ∫ x in unitCube, ‖f x - T x‖ ^ 2 := hEsum
        _ < ε ^ 2 := hE
    calc Real.sqrt (∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ ^ 2)
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h3.le
      _ = ε := Real.sqrt_sq hε.le
  have hsqrtA : Real.sqrt (∑ k ∈ p.support, ‖fourierCoeff f k‖ ^ 2) ≤ Real.sqrt A := by
    apply Real.sqrt_le_sqrt
    rw [hAdef]
    exact Summable.sum_le_tsum _ (fun k _ => by positivity) hA
  have hsumA : ∑ k ∈ p.support, ‖fourierCoeff f k‖ ^ 2 ≤ A := by
    rw [hAdef]
    exact Summable.sum_le_tsum _ (fun k _ => by positivity) hA
  -- Step 4: expand and use Cauchy–Schwarz
  have h4 : ∑ k ∈ p.support, (‖p k - fourierCoeff f k‖ + ‖fourierCoeff f k‖)
        * ‖fourierCoeff f k‖
      ≤ ε * Real.sqrt A + A := by
    have hexp : ∑ k ∈ p.support, (‖p k - fourierCoeff f k‖ + ‖fourierCoeff f k‖)
          * ‖fourierCoeff f k‖
        = (∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ * ‖fourierCoeff f k‖)
          + ∑ k ∈ p.support, ‖fourierCoeff f k‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hexp]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt p.support
      (fun k => ‖p k - fourierCoeff f k‖) (fun k => ‖fourierCoeff f k‖)
    have h5 : ∑ k ∈ p.support, ‖p k - fourierCoeff f k‖ * ‖fourierCoeff f k‖
        ≤ ε * Real.sqrt A :=
      le_trans hcs (mul_le_mul hsqrtE hsqrtA (Real.sqrt_nonneg _) hε.le)
    linarith
  calc ‖∑ k ∈ p.support, star (p k) * fourierCoeff f k‖
      ≤ ∑ k ∈ p.support, ‖p k‖ * ‖fourierCoeff f k‖ := h1
    _ ≤ ∑ k ∈ p.support, (‖p k - fourierCoeff f k‖ + ‖fourierCoeff f k‖)
          * ‖fourierCoeff f k‖ := h2
    _ ≤ ε * Real.sqrt A + A := h4
    _ = A + ε * Real.sqrt A := by ring

/-! ## The Poincaré inequality on the unit cube -/

theorem poincare_cube {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (ι → ℝ) → ℂ, ContDiff ℝ 1 f → Periodic1 f →
      (∫ x in unitCube, f x = 0) →
      ∫ x in unitCube, ‖f x‖ ^ 2 ≤ C * ∑ i, ∫ x in unitCube, ‖pd i f x‖ ^ 2 := by
  refine ⟨1 / (4 * Real.pi ^ 2), by positivity, fun f hf hper hmean => ?_⟩
  set X : ℝ := ∫ x in unitCube, ‖f x‖ ^ 2 with hXdef
  set A : ℝ := ∑' k : ι → ℤ, ‖fourierCoeff f k‖ ^ 2 with hAdef
  set G : ℝ := ∑ i, ∫ x in unitCube, ‖pd i f x‖ ^ 2 with hGdef
  have hA : Summable (fun k : ι → ℤ => ‖fourierCoeff f k‖ ^ 2) :=
    (bessel_continuous f hf.continuous).1
  have hAG : A ≤ (1 / (4 * Real.pi ^ 2)) * G := by
    rw [hAdef, hGdef]
    exact tsum_fourierCoeff_sq_le f hf hper hmean
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; exact tsum_nonneg fun k => by positivity
  have hXA : X ≤ A := by
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    set ε : ℝ := η / (2 * (Real.sqrt X + Real.sqrt A + 1)) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    -- density of trigonometric polynomials
    have hInt : Integrable (fun x : ι → ℝ => ‖f x‖ ^ 2) (volume.restrict unitCube) := by
      have hMem : MemLp f 2 (volume.restrict unitCube) :=
        BesselCont.memLp_of_continuous f hf.continuous
      exact (memLp_two_iff_integrable_sq_norm hMem.aestronglyMeasurable).mp hMem
    obtain ⟨p, hp⟩ := trigPoly_dense_L2 f hInt hεpos
    set T : (ι → ℝ) → ℂ := fun x => ∑ k ∈ p.support, p k * fourierExp k x with hTdef
    have hTcont : Continuous T := continuous_finsetSum _ (fun k _ =>
      continuous_const.mul (contDiff_fourierExp k).continuous)
    have hE : ∫ x in unitCube, ‖f x - T x‖ ^ 2 < ε ^ 2 := hp
    -- Cauchy–Schwarz against `f - T`
    have hcs1 : ‖∫ x in unitCube, f x * star (f x - T x)‖ ≤ Real.sqrt X * ε := by
      have h := integral_mul_star_le f (fun x => f x - T x) hf.continuous
        (hf.continuous.sub hTcont)
      have hE' : Real.sqrt (∫ x in unitCube, ‖f x - T x‖ ^ 2) ≤ ε :=
        le_of_lt ((Real.sqrt_lt' hεpos).mpr hE)
      refine h.trans ?_
      rw [hXdef]
      exact mul_le_mul_of_nonneg_left hE' (Real.sqrt_nonneg _)
    -- the pairing with `T`
    have hpair : ‖∫ x in unitCube, f x * star (T x)‖ ≤ A + ε * Real.sqrt A := by
      have h1 : (∫ x in unitCube, f x * star (T x))
          = ∑ k ∈ p.support, star (p k) * fourierCoeff f k := by
        rw [hTdef]
        exact integral_mul_star_trigPoly f hf.continuous p
      rw [h1]
      exact pairing_bound f hf.continuous p ε hεpos hA hE
    -- the decomposition of `∫ f * star f`
    have hXc : (X : ℂ) = ∫ x in unitCube, f x * star (f x) := by
      have hpt : ∀ x : ι → ℝ, f x * star (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
        intro x
        rw [show ((‖f x‖ ^ 2 : ℝ) : ℂ) = ((‖f x‖ : ℝ) : ℂ) ^ 2 by push_cast; ring]
        exact RCLike.mul_conj (f x)
      rw [funext hpt]
      have h := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict unitCube)
        (f := fun x : ι → ℝ => ‖f x‖ ^ 2)
      exact h.symm
    have hsplit : ∫ x in unitCube, f x * star (f x)
        = (∫ x in unitCube, f x * star (f x - T x))
          + ∫ x in unitCube, f x * star (T x) := by
      rw [← MeasureTheory.integral_add]
      · exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun x => by
            show f x * star (f x) = f x * star (f x - T x) + f x * star (T x)
            rw [star_sub]; ring)
      · exact integrableOn_unitCube_of_continuous
          (hf.continuous.mul (hf.continuous.sub hTcont).star)
      · exact integrableOn_unitCube_of_continuous (hf.continuous.mul hTcont.star)
    have hfin : X ≤ A + ε * (Real.sqrt X + Real.sqrt A) := by
      calc X = ‖(X : ℂ)‖ := by
            have h1 : ‖((X : ℝ) : ℂ)‖ = |X| := RCLike.norm_ofReal X
            rw [h1, abs_of_nonneg hX0]
        _ = ‖∫ x in unitCube, f x * star (f x)‖ := by rw [hXc]
        _ = ‖(∫ x in unitCube, f x * star (f x - T x))
              + ∫ x in unitCube, f x * star (T x)‖ := by rw [hsplit]
        _ ≤ ‖∫ x in unitCube, f x * star (f x - T x)‖
              + ‖∫ x in unitCube, f x * star (T x)‖ := norm_add_le _ _
        _ ≤ Real.sqrt X * ε + (A + ε * Real.sqrt A) := add_le_add hcs1 hpair
        _ = A + ε * (Real.sqrt X + Real.sqrt A) := by ring
    have hεbound : ε * (Real.sqrt X + Real.sqrt A) ≤ η := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg X, Real.sqrt_nonneg A, hη]
    linarith
  exact le_trans hXA hAG

end Work.Diff.STE
