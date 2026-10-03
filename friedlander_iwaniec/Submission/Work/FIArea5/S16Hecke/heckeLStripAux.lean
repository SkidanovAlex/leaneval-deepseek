/-
# `Submission.Work.FIArea5.S16Hecke.heckeLStripAux`

Auxiliary development for `heckeLStripBound2` (*FI* (16.18), the convexity strip bound for the
continuation of the Hecke `L`-function of `ℚ(i)`):

* `stripX` (`X = 4d/π`), `stripKL` (the log-comparison constant) and `stripWeight`
  (`V s = (4d)^{1-s}Γ(2 - s/2)/Γ(1 + s/2)(log (s+2))²`, the Phragmén–Lindelöf weight);
* the agreement `Lcont = heckeLSeries` on `re s > 1` (identity theorem; uses the absolute
  convergence of the Hecke Dirichlet series, `abscissaOfAbsConv ≤ 1`);
* the boundary bounds of `Lcont` on the lines `re s = 1` and `re s = 0`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.primaryWeightDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea5.S16Hecke.LcontDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea5.S16Hecke.gammaLowerSharpVertical
import Submission.Work.FIArea5.S16Hecke.gammaVerticalLowerExp
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea5.S16Hecke

open scoped BigOperators Topology

noncomputable section

/-- The base `X = 4d/π` of the completion (`= √(|d_K|·N𝔣)/(2π)` for `K = ℚ(i)`, `𝔣` of norm
`16d²`). -/
def stripX (d : ℕ) : ℂ := (((4 * (d : ℝ)) / Real.pi) : ℂ)

/-- The logarithmic comparison constant `K = log(4d(m+4))/log 2 + 1`: for `y ≥ 0`
`log (4 d (y + m + 4)) ≤ K·log (2 + y)`. -/
def stripKL (d m : ℕ) : ℝ := Real.log (4 * (d : ℝ) * ((m : ℝ) + 4)) / Real.log 2 + 1

/-- The Phragmén–Lindelöf weight `V`: its modulus on the strip is `≍ (4d(2+|Im s|))^{1-re s}·log²`. -/
def stripWeight (d : ℕ) (s : ℂ) : ℂ :=
  ((4 * (d : ℝ) : ℝ) : ℂ) ^ (1 - s) *
    (Complex.Gamma (2 - s / 2) / Complex.Gamma (1 + s / 2)) * (Complex.log (s + 2)) ^ 2

lemma stripX_ne_zero {d : ℕ} (hd : 1 ≤ d) : stripX d ≠ 0 := by
  have h4 : (0 : ℝ) < 4 * (d : ℝ) / Real.pi := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  simpa [stripX] using (Complex.ofReal_ne_zero.mpr (ne_of_gt h4))

lemma stripKL_pos {d m : ℕ} (hd : 1 ≤ d) : 0 < stripKL d m := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have h4d : 0 < 4 * (d:ℝ) * ((m:ℝ)+4) := by positivity
  have h3 : 0 ≤ Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by nlinarith)) (Real.log_pos (by norm_num)).le
  simp only [stripKL]; linarith

lemma log_four_mul_le (d m : ℕ) (hd : 1 ≤ d) {y : ℝ} (hy : 0 ≤ y) :
    Real.log (4 * (d : ℝ) * (y + (m : ℝ) + 4)) ≤ stripKL d m * Real.log (2 + y) := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4d : 0 < 4 * (d:ℝ) * ((m:ℝ)+4) := by positivity
  have hK0 : 0 ≤ Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by nlinarith)) hlog2pos.le
  have h1 : 4 * (d:ℝ) * (y + (m:ℝ) + 4) ≤ 4 * (d:ℝ) * ((m:ℝ)+4) * (2+y) := by
    have h2 : y + (m:ℝ) + 4 ≤ ((m:ℝ)+4) * (2+y) := by nlinarith
    nlinarith [h2, hd1]
  have h2 : Real.log (4 * (d:ℝ) * (y + (m:ℝ) + 4))
      ≤ Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) + Real.log (2+y) := by
    rw [← Real.log_mul (ne_of_gt h4d) (by linarith)]
    exact Real.log_le_log (by positivity) h1
  have h3 : Real.log 2 ≤ Real.log (2+y) := Real.log_le_log (by norm_num) (by linarith)
  have h4 : (Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) / Real.log 2) * Real.log 2
      = Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) := by
    field_simp
  calc Real.log (4 * (d:ℝ) * (y + (m:ℝ) + 4))
      ≤ Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) + Real.log (2+y) := h2
    _ = (Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) / Real.log 2) * Real.log 2 + Real.log (2+y) := by rw [h4]
    _ ≤ (Real.log (4 * (d:ℝ) * ((m:ℝ)+4)) / Real.log 2) * Real.log (2+y) + Real.log (2+y) := by
        have := mul_le_mul_of_nonneg_left h3 hK0
        linarith
    _ = stripKL d m * Real.log (2+y) := by rw [stripKL]; ring

lemma Lcont_eq_mul (d : ℕ) (Lam : ℂ → ℂ) (m : ℕ) (s : ℂ) :
    Lcont d Lam m s = Lam s * (stripX d) ^ (-s) * (Complex.Gamma (s + (m : ℂ) / 2))⁻¹ := by
  have h : Lcont d Lam m s
      = Lam s * ((stripX d) ^ s)⁻¹ * (Complex.Gamma (s + (m : ℂ) / 2))⁻¹ := by
    unfold Lcont completeDenom stripX
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [h, Complex.cpow_neg]

lemma differentiable_Lcont {d : ℕ} (hd : 1 ≤ d) {Lam : ℂ → ℂ} (hLam : Differentiable ℂ Lam)
    (m : ℕ) : Differentiable ℂ (Lcont d Lam m) := by
  have hX : stripX d ≠ 0 := stripX_ne_zero hd
  have hpow : Differentiable ℂ fun s : ℂ => (stripX d) ^ (-s) :=
    Differentiable.const_cpow differentiable_neg (Or.inl hX)
  have hgam : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + (m : ℂ) / 2))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hfun : Lcont d Lam m
      = fun s : ℂ => Lam s * (stripX d) ^ (-s) * (Complex.Gamma (s + (m:ℂ)/2))⁻¹ :=
    funext (fun s => Lcont_eq_mul d Lam m s)
  rw [hfun]
  exact (hLam.mul hpow).mul hgam

lemma completeDenom_ne_zero {d m : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 0 < s.re + (m:ℝ)/2) :
    completeDenom d m s ≠ 0 := by
  have hre : 0 < (s + (m:ℂ)/2).re := by simpa using hs
  rw [completeDenom]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (stripX_ne_zero hd)))
    (Complex.Gamma_ne_zero_of_re_pos hre)

lemma Lcont_mul_completeDenom {d m : ℕ} (Lam : ℂ → ℂ) {s : ℂ}
    (hD : completeDenom d m s ≠ 0) : Lcont d Lam m s * completeDenom d m s = Lam s := by
  rw [Lcont, div_mul_cancel₀ _ hD]

lemma LSeriesSummable_heckeLam (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (heckeLam chi k) (y : ℂ) := by
  rw [LSeriesSummable]
  have hbd : ∀ n : ℕ,
      ‖LSeries.term (heckeLam chi k) (y : ℂ) n‖
        ≤ 4 * (((n.divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (-y)) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h1 : ‖heckeLam chi k n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
        heckeLam_bound chi k hchi (Nat.one_le_iff_ne_zero.mpr hn)
      have h2 : 4 * (((n.divisors.card : ℕ) : ℝ) * (n:ℝ) ^ (-y))
          = (4 * ((n.divisors.card : ℕ) : ℝ)) / (n:ℝ) ^ y := by
        rw [Real.rpow_neg hnpos.le]; ring
      calc ‖heckeLam chi k n‖ / (n:ℝ) ^ y
          ≤ (4 * ((n.divisors.card : ℕ) : ℝ)) / (n:ℝ) ^ y :=
            div_le_div_of_nonneg_right h1 (Real.rpow_pos_of_pos hnpos y).le
        _ = 4 * (((n.divisors.card : ℕ) : ℝ) * (n:ℝ) ^ (-y)) := h2.symm
  exact Summable.of_norm_bounded
    ((summable_card_divisors_mul_rpow_neg hy).mul_left 4) hbd

lemma heckeLSeries_absc_le_one (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (heckeLam chi k) ≤ (1 : EReal) := by
  have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := heckeLam chi k) (x := 1)
    (fun y hy => LSeriesSummable_heckeLam chi k hchi hy)
  rwa [EReal.coe_one] at h

/-- **The identity theorem.** `Lam` and `LambdaHecke` agree on the whole half-plane `re s > 1`:
they agree on the open half-plane `re s > 1 + m/2` in which `Lam` completes `heckeLSeries`, and both
are analytic on the (preconnected) half-plane `re s > 1` — `LambdaHecke` because `X^s` and
`Γ(s + m/2)` are analytic there and the Hecke Dirichlet series converges absolutely on `re s > 1`
(`heckeLSeries_absc_le_one`). -/
lemma Lam_eq_LambdaHecke_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℕ}
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s)
    {s : ℂ} (hs : 1 < s.re) : Lam s = LambdaHecke d chi m s := by
  set U : Set ℂ := {z : ℂ | 1 < z.re} with hU
  have hmem : ∀ {z : ℂ}, z ∈ U → 1 < z.re := fun {z} hz => by
    simpa only [hU, Set.mem_ofPred_eq] using hz
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    have h := (convex_Ioi (1 : ℝ)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    have h2 : (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Set.Ioi 1) = U := by
      ext z; simp [hU]
    rwa [h2] at h
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have hf : AnalyticOnNhd ℂ Lam U :=
    ((hAn.mono (Set.subset_univ U)).differentiableOn).analyticOnNhd hUopen
  have hg : AnalyticOnNhd ℂ (LambdaHecke d chi m) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    rw [show LambdaHecke d chi m
        = fun z => (stripX d) ^ z * Complex.Gamma (z + (m : ℂ) / 2) *
            heckeLSeries chi (m : ℤ) z from rfl]
    refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
    · exact (DifferentiableOn.const_cpow differentiable_id.differentiableOn
        (Or.inl (stripX_ne_zero hd)))
    · intro z hz
      refine ((Complex.differentiableAt_Gamma _ (fun k hk => ?_)).comp z
        (differentiableAt_id.add_const _)).differentiableWithinAt
      have hk' : z + (m : ℂ) / 2 = -(k : ℂ) := by simpa using hk
      have hre : (z + (m : ℂ) / 2).re = -(k : ℝ) := by
        have := congrArg Complex.re hk'
        simpa using this
      have hre2 : (z + (m : ℂ) / 2).re = z.re + (m:ℝ)/2 := by simp
      have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      have hzre : 1 < z.re := hmem hz
      linarith
    · intro z hz
      refine (LSeries_differentiableOn (heckeLam chi (m : ℤ)) z ?_).mono ?_
      · show LSeries.abscissaOfAbsConv (heckeLam chi (m : ℤ)) < (z.re : EReal)
        exact lt_of_le_of_lt (heckeLSeries_absc_le_one chi (m : ℤ) hb)
          (EReal.coe_lt_coe_iff.mpr (hmem hz))
      · intro w hw
        exact lt_of_le_of_lt (heckeLSeries_absc_le_one chi (m : ℤ) hb)
          (EReal.coe_lt_coe_iff.mpr (hmem hw))
  have hz₀ : (((2 + (m : ℝ) / 2 : ℝ)) : ℂ) ∈ U := by
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    simp only [hU, Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith
  have hev : Lam =ᶠ[𝓝 (((2 + (m : ℝ) / 2 : ℝ)) : ℂ)] (LambdaHecke d chi m) := by
    refine Filter.eventually_of_mem
      (show {z : ℂ | 1 + (m : ℝ) / 2 < z.re} ∈ 𝓝 _ from ?_) ?_
    · apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      exact hagree z hz
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hUpre hz₀ hev) hs

lemma Lcont_eq_heckeLSeries_of_one_lt_re {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℕ}
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s)
    {s : ℂ} (hs : 1 < s.re) : Lcont d Lam m s = heckeLSeries chi (m : ℤ) s := by
  have h1 := Lam_eq_LambdaHecke_of_one_lt_re hd hAn hb hagree hs
  have hD : completeDenom d m s ≠ 0 := by
    refine completeDenom_ne_zero hd ?_
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  rw [Lcont, h1, LambdaHecke, ← completeDenom]
  exact mul_div_cancel_left₀ _ hD

/-- **Bound on the line `re s = 1`.** -/
lemma Lcont_bound_re_one {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℕ} {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagree : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s)
    (hlim : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re →
      ‖heckeLSeries chi (m : ℤ) s‖ ≤ C * (Real.log (4 * (d : ℝ) * (‖s‖ + (m : ℝ) + 3))) ^ (2 : ℕ)) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ t : ℝ,
      ‖Lcont d Lam m ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C1 * (Real.log (2 + |t|)) ^ (2 : ℕ) := by
  obtain ⟨Clim, hClimpos, hClim⟩ := hlim
  have hdiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  have hkey : ∀ t : ℝ, ‖Lcont d Lam m ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Clim * (Real.log (4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m : ℝ) + 3))) ^ (2 : ℕ) := by
    intro t
    have hcont : ContinuousAt (Lcont d Lam m) ((1 : ℂ) + (t : ℂ) * Complex.I) :=
      (differentiable_Lcont hd hdiff m).continuous.continuousAt
    have hmap : Filter.Tendsto (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (𝓝[>] (1 : ℝ))
        (𝓝 ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      have h1 : ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) 1 := by fun_prop
      exact h1.tendsto.mono_left (inf_le_left : 𝓝[>] (1:ℝ) ≤ 𝓝 (1:ℝ))
    have htend : Filter.Tendsto (fun σ : ℝ => Lcont d Lam m ((σ : ℂ) + (t : ℂ) * Complex.I))
        (𝓝[>] (1 : ℝ)) (𝓝 (Lcont d Lam m ((1 : ℂ) + (t : ℂ) * Complex.I))) :=
      hcont.tendsto.comp hmap
    have hgt : ContinuousAt (fun w : ℂ => Clim *
        (Real.log (4 * (d : ℝ) * (‖w‖ + (m : ℝ) + 3))) ^ (2 : ℕ))
        ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.pow ?_ 2
      refine (Real.continuousAt_log ?_).comp ?_
      · have hpos : (0:ℝ) < 4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m : ℝ) + 3) := by
          have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
          positivity
        exact ne_of_gt hpos
      · exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.add (continuous_norm.continuousAt.add continuousAt_const) continuousAt_const)
    have hrt : Filter.Tendsto (fun σ : ℝ => Clim *
        (Real.log (4 * (d : ℝ) * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + (m : ℝ) + 3))) ^ (2 : ℕ))
        (𝓝[>] (1 : ℝ)) (𝓝 (Clim *
        (Real.log (4 * (d : ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m : ℝ) + 3))) ^ (2 : ℕ))) := by
      have hh := hgt.tendsto.comp hmap
      simpa [Function.comp_def] using hh
    have hev : Filter.Eventually (fun σ : ℝ =>
        ‖Lcont d Lam m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Clim * (Real.log (4 * (d : ℝ) * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + (m : ℝ) + 3))) ^ (2 : ℕ))
        (𝓝[>] (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simp; exact hσ
      rw [Lcont_eq_heckeLSeries_of_one_lt_re hd hAn hb hagree hσ1]
      exact hClim _ hσ1
    exact le_of_tendsto_of_tendsto htend.norm hrt hev
  refine ⟨Clim * (stripKL d m)^2, ?_, fun t => ?_⟩
  · exact mul_pos hClimpos (pow_pos (stripKL_pos hd) 2)
  · have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    refine (hkey t).trans ?_
    have hn1 : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
      calc ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1 + |t| := by simp [Complex.norm_I]
    have hm3 : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3 ≤ |t| + (m:ℝ) + 4 := by
      have := abs_nonneg t; linarith
    have hle4 : Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3))
        ≤ stripKL d m * Real.log (2 + |t|) := by
      refine (Real.log_le_log (by positivity) (by nlinarith)).trans
        (log_four_mul_le d m hd (abs_nonneg t))
    have hsq : (Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3)))^2
        ≤ (stripKL d m)^2 * (Real.log (2 + |t|))^2 := by
      have hpos : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
      have h1 : 0 ≤ stripKL d m * Real.log (2 + |t|) :=
        le_of_lt (mul_pos (stripKL_pos hd) hpos)
      calc (Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3)))^2
          ≤ (stripKL d m * Real.log (2 + |t|))^2 := by
            refine pow_le_pow_left₀ ?_ hle4 2
            exact Real.log_nonneg (by nlinarith [hd1, hm0, norm_nonneg ((1:ℂ) + (t:ℂ) * Complex.I)])
        _ = (stripKL d m)^2 * (Real.log (2 + |t|))^2 := by ring
    have hfin : Clim * ((Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3)))^2)
        ≤ Clim * ((stripKL d m)^2 * (Real.log (2 + |t|))^2) :=
      mul_le_mul_of_nonneg_left hsq hClimpos.le
    calc Clim * (Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3)))^2
        = Clim * ((Real.log (4 * (d:ℝ) * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + (m:ℝ) + 3)))^2) := rfl
      _ ≤ Clim * ((stripKL d m)^2 * (Real.log (2 + |t|))^2) := hfin
      _ = Clim * (stripKL d m)^2 * (Real.log (2 + |t|))^2 := by ring

end

end Work.FIArea5.S16Hecke
