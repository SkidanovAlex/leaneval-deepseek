import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Core.Gaussian
import Submission.Work.RadialSpace.Basic
import Submission.Work.FunctionalEquations.DensityAux.composite_seminorm_smooth
import Submission.Work.FunctionalEquations.DensityAux.aliasing
import Submission.Work.FunctionalEquations.DensityAux.gaussianSeminormGrowth
import Submission.Work.FunctionalEquations.DensityAux.summableIntGaussian
import Submission.Work.FunctionalEquations.DensityAux.shiftSumTendsto
import Submission.Work.FunctionalEquations.DensityAux.shiftedProfileSeminorm
import Submission.Work.Summability.exists_schwartz_tsum
import Submission.Work.Radial.seminorm_bound

/-!
# Killing the de-Gaussed profile of a compactly supported profile

A continuous linear functional `Λ` on the Schwartz space on `ℝ^n` which vanishes on every
complex Gaussian `x ↦ exp (π i τ ‖x‖²)` with `Im τ = y` also vanishes on
`x ↦ exp (-π y ‖x‖²) h (‖x‖²)` for every compactly supported smooth profile `h`
(paper: CKMRV, proof of Lemma 3.3).

The proof is the one in the paper: writing `h(x) = ∫ ĝ(t) e^{2πi t x} dt`,
Poisson summation turns the Riemann sums `(1/N) ∑_n ĝ(n/N) e^{πi (n/N) |z|²}` of the
Gaussian integral into the periodisation `∑_m h (|z|² - 2 N m)` of `h`.  The Riemann
sums are linear combinations of complex Gaussians, hence are killed by `Λ`, and the
error is the sum over `m ≠ 0` of the translated profiles, whose Gaussian weight
`exp (-π y |z|²)` makes its Schwartz seminorms tend to `0` as `N → ∞`.
-/

open Filter
open scoped FourierTransform SchwartzMap Topology ContDiff

namespace Work.FunctionalEquations.DensityAux

variable {D : ℕ} [NeZero D]

/-! ### Elementary bounds -/

/-- The supremum of finitely many Schwartz seminorms is bounded by their sum. -/
lemma finset_sup_schwartz_le_sum (s : Finset (ℕ × ℕ))
    (g : 𝓢(EuclideanSpace ℝ (Fin D), ℂ)) :
    (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin D)) ℂ)) g
      ≤ ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert, Seminorm.sup_apply, Finset.sum_insert ha,
        SchwartzMap.schwartzSeminormFamily_apply]
      refine max_le (le_add_of_nonneg_right ?_) ?_
      · exact Finset.sum_nonneg fun i _ => apply_nonneg _ _
      · exact le_trans ih (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Schwartz decay in the form `(1 + |x|)^2 ‖g x‖ ≤ D`. -/
lemma one_add_sq_mul_norm_le (g : SchwartzMap ℝ ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, (1 + |x|) ^ 2 * ‖g x‖ ≤ D := by
  refine ⟨2 ^ 2 * ((Finset.Iic (2, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g,
    by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
    le_rfl le_rfl g x
  simpa [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using h

/-- The sampling of a Schwartz function along the arithmetic progression
`m ↦ c - d * m` is summable, for `d ≥ 1`. -/
lemma summable_int_shift (g : SchwartzMap ℝ ℂ) (c d : ℝ) (hd : 1 ≤ d) :
    Summable (fun m : ℤ => g (c - d * (m : ℝ))) := by
  obtain ⟨D, hD0, hD⟩ := one_add_sq_mul_norm_le g
  have hDb : ∀ x : ℝ, ‖g x‖ ≤ D / (1 + |x|) ^ 2 := by
    intro x
    rw [le_div_iff₀ (by positivity)]
    linarith [hD x]
  refine Summable.of_norm_bounded_eventually
    (g := fun m : ℤ => D * (1 + |c|) ^ 2 * |(m : ℝ)| ^ (-2 : ℝ)) ?_ ?_
  · exact (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)).mul_left _
  · rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
    intro m hm
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hm ⊢
    by_contra hne
    set M : ℝ := (m : ℝ) with hM
    set C : ℝ := c - d * M with hC
    have hM1 : (1 : ℝ) ≤ |M| := by
      have h1 : (1 : ℤ) ≤ |m| := by
        have := abs_pos.mpr hne
        omega
      rw [hM]
      exact_mod_cast h1
    have habs : |M| ≤ |c| + |C| := by
      have h2 : |M| ≤ |c| + |c - d * M| := by
        have h1 : |M| ≤ |d * M| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ d)]
          nlinarith [abs_nonneg M]
        have h3 : |d * M| ≤ |c| + |c - d * M| := by
          have h4 := abs_add_le c (d * M - c)
          rw [show c + (d * M - c) = d * M by ring, abs_sub_comm] at h4
          exact h4
        linarith
      rwa [hC]
    have key : (1 + |M|) ^ 2 ≤ (1 + |c|) ^ 2 * (1 + |C|) ^ 2 := by
      have h1 : 1 + |M| ≤ (1 + |c|) * (1 + |C|) := by
        have := abs_nonneg c
        have := abs_nonneg C
        have := abs_nonneg M
        nlinarith
      nlinarith [h1, abs_nonneg c, abs_nonneg C]
    have h3 : |M| ^ 2 ≤ (1 + |c|) ^ 2 * (1 + |C|) ^ 2 :=
      le_trans (by nlinarith [abs_nonneg M]) key
    have hstep : D / (1 + |C|) ^ 2 ≤ (D * (1 + |c|) ^ 2) / |M| ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h3, hD0]
    have hrw : D * (1 + |c|) ^ 2 * |M| ^ (-2 : ℝ) = (D * (1 + |c|) ^ 2) / |M| ^ 2 := by
      rw [Real.rpow_neg (abs_nonneg M), Real.rpow_two, div_eq_mul_inv]
    have hgoal : ‖g C‖ ≤ D * (1 + |c|) ^ 2 * |M| ^ (-2 : ℝ) := by
      rw [hrw]
      exact le_trans (hDb C) hstep
    rw [hC, hM] at hgoal
    exact hm hgoal

/-- Splitting a `ℤ`-indexed sum into the `m = 0` term and the sum over `m ≠ 0`. -/
lemma tsum_ne_eq_tsum_ite (f : ℤ → ℂ) :
    (∑' m : {m : ℤ // m ≠ 0}, f m) = ∑' m : ℤ, (if m = 0 then 0 else f m) := by
  change (∑' m : ↑({m : ℤ | m ≠ 0}), f ↑m) = _
  rw [tsum_subtype]
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · simp [Set.indicator_of_mem, hm]

/-- Splitting a summable `ℤ`-indexed sum into the `m = 0` term and the sum over `m ≠ 0`. -/
lemma tsum_eq_add_tsum_ne {f : ℤ → ℂ} (hf : Summable f) :
    ∑' m : ℤ, f m = f 0 + ∑' m : {m : ℤ // m ≠ 0}, f m := by
  rw [Summable.tsum_eq_add_tsum_ite hf 0]
  congr 1
  exact (tsum_ne_eq_tsum_ite f).symm

/-- A compactly supported function vanishes outside a ball, with the bound stated at
`R ≤ |t|`. -/
lemma exists_support_bound {h : ℝ → ℂ} (hs : HasCompactSupport h) :
    ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0 := by
  obtain ⟨C, hC⟩ := hs.isBounded.exists_norm_le
  refine ⟨|C| + 1, fun t ht => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have h1 := hC t hmem
  rw [Real.norm_eq_abs] at h1
  have h2 : C ≤ |C| := le_abs_self C
  linarith

/-! ### The Fourier pair producing the aliasing identity -/

/-- The continuous linear map given by composing a Schwartz function with `u ↦ -2 u`. -/
noncomputable def compNegTwoMul : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℂ (g := fun u : ℝ => -2 * u)
    (by
      have h : (fun u : ℝ => -2 * u) = ⇑((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) := by
        ext u; simp [smul_eq_mul]
      rw [h]; exact ContinuousLinearMap.hasTemperateGrowth _)
    (by
      refine ⟨1, 1, fun x => ?_⟩
      rw [pow_one, show ‖(-2 : ℝ) * x‖ = 2 * ‖x‖ by rw [norm_mul]; norm_num]
      linarith [norm_nonneg x])

lemma compNegTwoMul_apply (g : SchwartzMap ℝ ℂ) (u : ℝ) : compNegTwoMul g u = g (-2 * u) := by
  rw [compNegTwoMul, SchwartzMap.compCLM_apply]
  rfl

/-- For every Schwartz function `hS` there is a Schwartz function `ψ` whose Fourier
transform is `σ ↦ hS (-2 σ)`. -/
lemma exists_fourier_comp_neg_two (hS : SchwartzMap ℝ ℂ) :
    ∃ ψ : SchwartzMap ℝ ℂ, ∀ σ : ℝ, (FourierTransform.fourier ψ) σ = hS (-2 * σ) :=
  ⟨𝓕⁻ (compNegTwoMul hS), fun σ => by
    rw [FourierTransform.fourier_fourierInv_eq, compNegTwoMul_apply]⟩

/-- The factorisation of the complex Gaussian `exp (π i (u + iy) ‖x‖²)`. -/
lemma gaussianFun_factor (n : ℕ) (u y : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Work.Core.gaussianFun n ((u : ℂ) + (y : ℂ) * Complex.I) x
      = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ)))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  rw [Work.Core.gaussianFun, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The imaginary part of `u + i y` is `y`. -/
lemma im_gaussian (y u : ℝ) : (((u : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  simp [Complex.add_im, Complex.mul_im]

/-- **Aliasing (Poisson summation).** A continuous linear functional which vanishes on the
Riemann sums `∑_n ψ (n/N) exp (π i (n/N) t)` also vanishes on the periodisation
`∑_m hS (t - 2 N m)`.  This is the form used below (`aliasing` is the same identity with
the complex exponential written with a complex division). -/
lemma aliasingExpanded (ψ hS : SchwartzMap ℝ ℂ)
    (hψ : ∀ σ : ℝ, (FourierTransform.fourier ψ) σ = hS (-2 * σ))
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (1 / (N : ℂ)) * ∑' n : ℤ, ψ ((n : ℝ) / N) *
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          (((n : ℝ) / (N : ℝ) : ℝ) : ℂ) * ((t : ℝ) : ℂ))
      = ∑' m : ℤ, hS (t - 2 * (N : ℝ) * m) := by
  rw [show (∑' n : ℤ, ψ ((n : ℝ) / N) *
        Complex.exp ((Real.pi : ℂ) * Complex.I *
          (((n : ℝ) / (N : ℝ) : ℝ) : ℂ) * ((t : ℝ) : ℂ)))
      = (∑' n : ℤ, ψ ((n : ℝ) / N) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℝ) / N : ℂ) * t)) from by
    refine tsum_congr fun n => ?_
    congr 1
    push_cast
    ring]
  exact aliasing ψ hS hψ N hN t

theorem kills_compactProfile (D : ℕ) [NeZero D] {y : ℝ} (hy : 0 < y)
    (Λ : SchwartzMap (EuclideanSpace ℝ (Fin D)) ℂ →L[ℂ] ℂ)
    (hkills : ∀ (τ : ℂ), τ.im = y → ∀ F : SchwartzMap (EuclideanSpace ℝ (Fin D)) ℂ,
      (∀ x, F x = Work.Core.gaussianFun D τ x) → Λ F = 0)
    {h : ℝ → ℂ} (hh : ContDiff ℝ Work.RadialSpace.Smooth h) (hsupp : HasCompactSupport h)
    {F : SchwartzMap (EuclideanSpace ℝ (Fin D)) ℂ}
    (hF : ∀ x, F x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) * h (‖x‖ ^ 2)) :
    Λ F = 0 := by
  classical
  -- the profile as a Schwartz function and its support bound
  obtain ⟨R, hR⟩ := exists_support_bound hsupp
  let hS : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hh
  have hS_apply : ∀ t : ℝ, hS t = h t := fun t => rfl
  -- the Fourier pair giving the aliasing identity
  obtain ⟨ψ, hψ⟩ := exists_fourier_comp_neg_two hS
  -- Λ is bounded by finitely many seminorms
  obtain ⟨s, C₀, hC₀, hΛbnd⟩ := Work.Radial.exists_seminorm_bound D Λ
  -- BRICK (shiftedProfileSeminorm)
  have hshift : ∀ p : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (m : ℤ), 1 ≤ N → m ≠ 0 →
      ∃ T : 𝓢(EuclideanSpace ℝ (Fin D), ℂ),
        (∀ x, T x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
            hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ))) ∧
        (SchwartzMap.seminorm ℂ p.1 p.2) T
          ≤ C * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |(m : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |(m : ℝ)| + R) ^ (p.1 + 2 * p.2) := by
    intro p
    exact shiftedProfileSeminorm D (y := y) hy hS hR p.1 p.2
  choose Csh hCsh0 hCshBound using hshift
  -- BRICK (shiftSumTendsto)
  have hshiftSum : ∀ d : ℕ,
      (∀ N : ℕ, 1 ≤ N → Summable (fun m : {m : ℤ // m ≠ 0} =>
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d)) ∧
      Tendsto (fun N : ℕ => ∑' m : {m : ℤ // m ≠ 0},
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d) atTop (𝓝 0) := by
    intro d
    exact shiftSumTendsto y R hy d
  -- the main estimate for each `N`
  have key : ∀ N : ℕ, 1 ≤ N → ‖Λ F‖ ≤ C₀ * ∑ p ∈ s, Csh p *
      (∑' m : {m : ℤ // m ≠ 0},
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) := by
    intro N hN
    have hNpos : 0 < N := hN
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    -- the complex Gaussians
    let G : ℝ → 𝓢(EuclideanSpace ℝ (Fin D), ℂ) :=
      fun u => Work.Core.gaussianSchwartz D ((u : ℂ) + (y : ℂ) * Complex.I)
        (by rw [im_gaussian]; exact hy)
    have hG_val : ∀ (u : ℝ) (x : EuclideanSpace ℝ (Fin D)),
        G u x = Work.Core.gaussianFun D ((u : ℂ) + (y : ℂ) * Complex.I) x :=
      fun u x => Work.Core.gaussianSchwartz_apply D _ _ x
    -- the Riemann-sum approximant
    let v : ℤ → 𝓢(EuclideanSpace ℝ (Fin D), ℂ) :=
      fun n => (1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ))) • G ((n : ℝ) / (N : ℝ))
    have hvsumm : ∀ k l : ℕ, Summable (fun n : ℤ => (SchwartzMap.seminorm ℂ k l) (v n)) := by
      intro k l
      -- BRICK (gaussianSeminormGrowth)
      have hgauss : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ) (G' : 𝓢(EuclideanSpace ℝ (Fin D), ℂ)),
          (∀ x, G' x = Work.Core.gaussianFun D ((u : ℂ) + (y : ℂ) * Complex.I) x) →
          (SchwartzMap.seminorm ℂ k l) G' ≤ C * (1 + |u|) ^ (2 * l + 2) := by
        exact gaussianSeminormGrowth D (y := y) hy k l
      obtain ⟨Cg, hCg0, hCgb⟩ := hgauss
      -- BRICK (summableIntGaussian)
      have hpsi : Summable (fun n : ℤ =>
          ‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + |(n : ℝ)|) ^ (2 * l + 2)) := by
        exact summableIntGaussian ψ N hN (2 * l + 2)
      refine Summable.of_norm_bounded (hpsi.mul_left Cg) fun n => ?_
      rw [Real.norm_of_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ k l) (v n))]
      have hsmul : (SchwartzMap.seminorm ℂ k l) (v n)
          = ‖(1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ)))‖ *
            (SchwartzMap.seminorm ℂ k l) (G ((n : ℝ) / (N : ℝ))) := by
        rw [show v n = (1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ))) • G ((n : ℝ) / (N : ℝ))
          from rfl]
        exact Seminorm.smul' _ _ _
      rw [hsmul]
      have hgn := hCgb ((n : ℝ) / (N : ℝ)) (G ((n : ℝ) / (N : ℝ))) (hG_val _)
      have hc : ‖(1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ)))‖ ≤ ‖ψ ((n : ℝ) / (N : ℝ))‖ := by
        rw [norm_mul, show ‖(1 : ℂ) / (N : ℂ)‖ = 1 / (N : ℝ) by
          rw [norm_div, norm_one, Complex.norm_natCast], one_div]
        calc (N : ℝ)⁻¹ * ‖ψ ((n : ℝ) / (N : ℝ))‖ ≤ 1 * ‖ψ ((n : ℝ) / (N : ℝ))‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              rw [inv_le_one₀ (by linarith : (0 : ℝ) < (N : ℝ))]
              exact hNreal
          _ = ‖ψ ((n : ℝ) / (N : ℝ))‖ := one_mul _
      have hdiv : |(n : ℝ) / (N : ℝ)| ≤ |(n : ℝ)| := by
        rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ)),
          div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ))]
        nlinarith [abs_nonneg ((n : ℝ)), hNreal]
      have hpow : (1 + |(n : ℝ) / (N : ℝ)|) ^ (2 * l + 2) ≤ (1 + |(n : ℝ)|) ^ (2 * l + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith [hdiv, abs_nonneg ((n : ℝ))]) _
      calc ‖(1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ)))‖ *
              (SchwartzMap.seminorm ℂ k l) (G ((n : ℝ) / (N : ℝ)))
          ≤ ‖ψ ((n : ℝ) / (N : ℝ))‖ * (Cg * (1 + |(n : ℝ) / (N : ℝ)|) ^ (2 * l + 2)) := by
            refine mul_le_mul hc hgn (apply_nonneg _ _) (norm_nonneg _)
        _ ≤ ‖ψ ((n : ℝ) / (N : ℝ))‖ * (Cg * (1 + |(n : ℝ)|) ^ (2 * l + 2)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCg0) (norm_nonneg _)
        _ = Cg * (‖ψ ((n : ℝ) / (N : ℝ))‖ * (1 + |(n : ℝ)|) ^ (2 * l + 2)) := by ring
    let A : 𝓢(EuclideanSpace ℝ (Fin D), ℂ) := Work.Summability.schwartzSum v hvsumm
    have hHasA : HasSum v A := Work.Summability.hasSum_schwartzSum v hvsumm
    have hA_apply : ∀ x : EuclideanSpace ℝ (Fin D), A x = ∑' n : ℤ, v n x :=
      fun x => Work.Summability.schwartzSum_apply v hvsumm x
    -- `Λ` kills the approximant
    have hA_Λ : Λ A = 0 := by
      have hmap : Λ A = ∑' n : ℤ, Λ (v n) := by
        rw [← hHasA.tsum_eq]
        exact ContinuousLinearMap.map_tsum Λ hHasA.summable
      have hzero : ∀ n : ℤ, Λ (v n) = 0 := by
        intro n
        rw [show v n = (1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ))) • G ((n : ℝ) / (N : ℝ))
          from rfl, ContinuousLinearMap.map_smul]
        rw [hkills (((n : ℝ) / (N : ℝ) : ℝ) + (y : ℂ) * Complex.I)
          (im_gaussian y ((n : ℝ) / (N : ℝ))) (G ((n : ℝ) / (N : ℝ))) (hG_val _)]
        simp
      rw [hmap, tsum_congr hzero, tsum_zero]
    -- the pointwise values of the approximant
    have hA_val : ∀ x : EuclideanSpace ℝ (Fin D), A x =
        Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
          (∑' m : ℤ, hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ))) := by
      intro x
      rw [hA_apply]
      have hterm : ∀ n : ℤ, v n x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
          ((1 / (N : ℂ)) * (ψ ((n : ℝ) / (N : ℝ)) *
            Complex.exp ((Real.pi : ℂ) * Complex.I *
              (((n : ℝ) / (N : ℝ) : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ)))) := by
        intro n
        rw [show v n = (1 / (N : ℂ) * ψ ((n : ℝ) / (N : ℝ))) • G ((n : ℝ) / (N : ℝ))
          from rfl, smul_apply, hG_val, gaussianFun_factor D ((n : ℝ) / (N : ℝ)) y x]
        ring
      rw [tsum_congr hterm, tsum_mul_left, tsum_mul_left]
      rw [aliasingExpanded ψ hS hψ N hNpos (‖x‖ ^ 2)]
    -- the error series
    let T : (m : ℤ) → m ≠ 0 → 𝓢(EuclideanSpace ℝ (Fin D), ℂ) :=
      fun m hm => Classical.choose (hCshBound (0, 0) N m hN hm)
    have hTval : ∀ (m : ℤ) (hm : m ≠ 0) (x : EuclideanSpace ℝ (Fin D)),
        T m hm x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
          hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ)) :=
      fun m hm x => (Classical.choose_spec (hCshBound (0, 0) N m hN hm)).1 x
    have hTbound : ∀ (p : ℕ × ℕ) (m : ℤ) (hm : m ≠ 0),
        (SchwartzMap.seminorm ℂ p.1 p.2) (T m hm)
          ≤ Csh p * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |(m : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |(m : ℝ)| + R) ^ (p.1 + 2 * p.2) := by
      intro p m hm
      obtain ⟨T', hT'val, hT'bd⟩ := hCshBound p N m hN hm
      have hTeq : T' = T m hm := SchwartzMap.ext fun x => by rw [hT'val x, hTval m hm x]
      rw [hTeq] at hT'bd
      exact hT'bd
    let V : {m : ℤ // m ≠ 0} → 𝓢(EuclideanSpace ℝ (Fin D), ℂ) := fun m => T m.1 m.2
    have hVsumm : ∀ k l : ℕ,
        Summable (fun m : {m : ℤ // m ≠ 0} => (SchwartzMap.seminorm ℂ k l) (V m)) := by
      intro k l
      refine Summable.of_norm_bounded
        (((hshiftSum (k + 2 * l)).1 N hN).mul_left (Csh (k, l))) fun m => ?_
      rw [Real.norm_of_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ k l) (V m))]
      have hb := hTbound (k, l) m.1 m.2
      have hb' : (SchwartzMap.seminorm ℂ k l) (V m)
          ≤ Csh (k, l) * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (k + 2 * l) := hb
      calc (SchwartzMap.seminorm ℂ k l) (V m)
          ≤ Csh (k, l) * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (k + 2 * l) := hb'
        _ = Csh (k, l) * (Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (k + 2 * l)) := by ring
    let B : 𝓢(EuclideanSpace ℝ (Fin D), ℂ) := Work.Summability.schwartzSum V hVsumm
    have hB_apply : ∀ x : EuclideanSpace ℝ (Fin D),
        B x = ∑' m : {m : ℤ // m ≠ 0}, V m x :=
      fun x => Work.Summability.schwartzSum_apply V hVsumm x
    have hB_le : ∀ p : ℕ × ℕ, (SchwartzMap.seminorm ℝ p.1 p.2) B ≤ Csh p *
        (∑' m : {m : ℤ // m ≠ 0},
          Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
            * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) := by
      intro p
      have h1 : (SchwartzMap.seminorm ℂ p.1 p.2) B
          ≤ ∑' m : {m : ℤ // m ≠ 0}, (SchwartzMap.seminorm ℂ p.1 p.2) (V m) :=
        Work.Summability.seminorm_schwartzSum_le V hVsumm p.1 p.2
      rw [Work.Summability.schwartz_seminorm_complex_eq B] at h1
      have h2 : (∑' m : {m : ℤ // m ≠ 0}, (SchwartzMap.seminorm ℂ p.1 p.2) (V m))
          ≤ ∑' m : {m : ℤ // m ≠ 0},
              Csh p * (Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
                * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) := by
        refine Summable.tsum_le_tsum (fun m => ?_) (hVsumm p.1 p.2) ?_
        · calc (SchwartzMap.seminorm ℂ p.1 p.2) (V m)
              ≤ Csh p * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
                  * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2) :=
                hTbound p m.1 m.2
            _ = Csh p * (Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
                  * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) := by ring
        · exact ((hshiftSum (p.1 + 2 * p.2)).1 N hN).mul_left (Csh p)
      rw [tsum_mul_left] at h2
      exact le_trans h1 h2
    -- the pointwise identity `F - A = -B`
    have hFA : F - A = -B := by
      refine SchwartzMap.ext fun x => ?_
      have h1 : (F - A) x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) * hS (‖x‖ ^ 2)
          - Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
              (∑' m : ℤ, hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ))) := by
        rw [sub_apply, hF x, hA_val x, hS_apply]
      have h2 : (-B) x = -(∑' m : {m : ℤ // m ≠ 0},
            Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
              hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * ((m : ℤ) : ℝ))) := by
        rw [neg_apply, hB_apply]
        congr 1
        exact tsum_congr fun m => hTval m.1 m.2 x
      have hsplit := tsum_eq_add_tsum_ne
        (f := fun m : ℤ => hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ)))
        (summable_int_shift hS (‖x‖ ^ 2) (2 * (N : ℝ)) (by linarith))
      have hsplit' : (∑' m : ℤ, hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ))) =
          hS (‖x‖ ^ 2) + ∑' m : {m : ℤ // m ≠ 0},
            hS ((‖x‖ ^ 2) - 2 * (N : ℝ) * ((m : ℤ) : ℝ)) := by
        simpa using hsplit
      rw [h1, h2, hsplit', tsum_mul_left]
      ring
    -- conclusion
    have hsup : (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin D)) ℂ)) (F - A)
        ≤ ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) (F - A) :=
      finset_sup_schwartz_le_sum s (F - A)
    have hstep1 : ‖Λ F‖ ≤ C₀ * ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) (F - A) := by
      have h1 : Λ F = Λ (F - A) := by rw [map_sub, hA_Λ, sub_zero]
      calc ‖Λ F‖ = ‖Λ (F - A)‖ := by rw [h1]
        _ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin D)) ℂ)) (F - A) :=
            hΛbnd (F - A)
        _ ≤ C₀ * ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) (F - A) :=
            mul_le_mul_of_nonneg_left hsup hC₀
    have hstep2 : ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) (F - A)
        ≤ ∑ p ∈ s, Csh p * (∑' m : {m : ℤ // m ≠ 0},
            Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hsame : (SchwartzMap.seminorm ℝ p.1 p.2) (F - A)
          = (SchwartzMap.seminorm ℝ p.1 p.2) B := by
        rw [hFA, map_neg_eq_map]
      rw [hsame]
      exact hB_le p
    calc ‖Λ F‖ ≤ C₀ * ∑ p ∈ s, (SchwartzMap.seminorm ℝ p.1 p.2) (F - A) := hstep1
      _ ≤ C₀ * ∑ p ∈ s, Csh p * (∑' m : {m : ℤ // m ≠ 0},
            Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)) :=
          mul_le_mul_of_nonneg_left hstep2 hC₀
  -- let `N → ∞`
  have hlim : Tendsto (fun N : ℕ => ∑ p ∈ s, Csh p *
      (∑' m : {m : ℤ // m ≠ 0},
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum
      (f := fun p (N : ℕ) => Csh p *
        (∑' m : {m : ℤ // m ≠ 0},
          Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
            * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2)))
      (a := fun _ => (0 : ℝ)) s
      (fun p _ => by
        simpa using Tendsto.const_mul (Csh p) (hshiftSum (p.1 + 2 * p.2)).2)
    simpa using h
  have hfin : ‖Λ F‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := ε / (C₀ + 1) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨N, hNlt, hN1⟩ :=
      ((hlim.eventually (Iio_mem_nhds hδpos)).and (eventually_ge_atTop 1)).exists
    have hk := key N hN1
    have hCδ : C₀ * δ ≤ ε := by
      have h1 : C₀ / (C₀ + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      calc C₀ * δ = (C₀ / (C₀ + 1)) * ε := by rw [hδ]; ring
        _ ≤ 1 * ε := mul_le_mul_of_nonneg_right h1 hε.le
        _ = ε := one_mul ε
    have hmul : C₀ * (∑ p ∈ s, Csh p * (∑' m : {m : ℤ // m ≠ 0},
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ (p.1 + 2 * p.2))) ≤ C₀ * δ :=
      mul_le_mul_of_nonneg_left hNlt.le hC₀
    linarith [hk, hmul, hCδ]
  have hzero : ‖Λ F‖ = 0 := le_antisymm hfin (norm_nonneg _)
  exact norm_eq_zero.mp hzero

end Work.FunctionalEquations.DensityAux
