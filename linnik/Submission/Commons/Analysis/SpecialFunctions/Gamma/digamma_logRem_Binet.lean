import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Commons.Analysis.SpecialFunctions.Frullani.complex_log
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_partialSum
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_exp_integrable
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_F_integrable
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_S_integrable
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_Gintegral_zero

open scoped Real BigOperators Topology
open Filter

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-! ###### basic complex-exponential machinery ###### -/

def expc (a : ℂ) (t : ℝ) : ℂ := Complex.exp (a * (t : ℂ))

@[simp] lemma expc_add (a b : ℂ) (t : ℝ) : expc (a + b) t = expc a t * expc b t := by
  unfold expc
  rw [← Complex.exp_add]
  congr 1
  ring

lemma expc_ofReal (a : ℝ) (t : ℝ) : expc (a : ℂ) t = ((Real.exp (a * t) : ℝ) : ℂ) := by
  unfold expc
  rw [← Complex.ofReal_mul]
  exact (Complex.ofReal_exp (a * t)).symm

@[simp] lemma expc_zero (t : ℝ) : expc 0 t = 1 := by simp [expc]

lemma expc_ne_zero (a : ℂ) (t : ℝ) : expc a t ≠ 0 := by
  unfold expc
  exact Complex.exp_ne_zero _

lemma norm_expc (a : ℂ) (t : ℝ) : ‖expc a t‖ = Real.exp (a.re * t) := by
  unfold expc
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp

lemma expc_pow (k : ℕ) (t : ℝ) : (expc (-(1 : ℂ)) t) ^ k = expc (-(k : ℂ)) t := by
  unfold expc
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma expc_neg_one_real (t : ℝ) : expc (-(1 : ℂ)) t = ((Real.exp (-t) : ℝ) : ℂ) := by
  simpa using expc_ofReal (-1) t

lemma expc_neg_one_ne_one {t : ℝ} (ht : 0 < t) : expc (-(1 : ℂ)) t ≠ 1 := by
  have hv := expc_neg_one_real t
  rw [hv]
  intro h
  have hre : Real.exp (-t) = 1 := (Complex.ofReal_eq_one.mp h)
  have hgt : Real.exp t > 1 := (Real.one_lt_exp_iff).2 ht
  have hprod : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmain : Real.exp t = 1 := by
    calc
      Real.exp t = Real.exp t * Real.exp (-t) := by rw [hre]; ring
      _ = 1 := hprod
  exact (ne_of_gt hgt) hmain

lemma geosum_eq_expc (m : ℕ) (t : ℝ) (ht : 0 < t) :
    ∑ k ∈ Finset.range (m + 1), expc (-(k : ℂ)) t =
      (1 - expc (-(1 : ℂ)) t ^ (m + 1)) / (1 - expc (-(1 : ℂ)) t) := by
  have hx : expc (-(1 : ℂ)) t ≠ 1 := expc_neg_one_ne_one ht
  calc
    ∑ k ∈ Finset.range (m + 1), expc (-(k : ℂ)) t
        = ∑ k ∈ Finset.range (m + 1), (expc (-(1 : ℂ)) t) ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (expc_pow k t).symm
    _ = (1 - expc (-(1 : ℂ)) t ^ (m + 1)) / (1 - expc (-(1 : ℂ)) t) := by
          have hg := geom_sum_eq hx (m + 1)
          rw [hg]
          field_simp [sub_ne_zero.mpr hx]
          ring

lemma expc_neg_mul (m : ℕ) (t : ℝ) : expc (-((m : ℕ) : ℂ)) t = ((Real.exp (-(m : ℝ) * t) : ℝ) : ℂ) := by
  simpa using expc_ofReal (-(m : ℝ)) t

/-! ###### kernel and its bounds ###### -/

def K (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t + 1 / 2

lemma exp_ge_add (t : ℝ) : 1 + t ≤ Real.exp t := by
  simpa [add_comm] using (Real.add_one_le_exp t : t + 1 ≤ Real.exp t)

lemma exp_neg_ge_sub_one (t : ℝ) : 1 - t ≤ Real.exp (-t) := by
  simpa [add_comm, sub_eq_add_neg] using (Real.add_one_le_exp (-t) : -t + 1 ≤ Real.exp (-t))

lemma exp_sub_one_le_mul_self (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := exp_neg_ge_sub_one t
  have hpos : 0 ≤ Real.exp t := (Real.exp_pos t).le
  have hmul : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h hpos
  have h1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 : (1 - t) * Real.exp t = Real.exp t - t * Real.exp t := by ring
  nlinarith

lemma exp_sub_one_ge (t : ℝ) (ht : 0 ≤ t) : t ≤ Real.exp t - 1 := by
  have h := exp_ge_add t
  linarith

lemma exp_sub_one_pos (t : ℝ) (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have hle := exp_ge_add t
  have hlt : 1 < 1 + t := by linarith
  exact sub_pos.mpr (lt_of_lt_of_le hlt hle)

lemma kernel_abs_le_half (t : ℝ) (ht : 0 < t) : |K t| ≤ 1 / 2 := by
  unfold K
  have hposE : 0 < Real.exp t - 1 := exp_sub_one_pos t ht
  have hA_nonpos : 1 / (Real.exp t - 1) - 1 / t ≤ 0 := by
    have hle : 1 / (Real.exp t - 1) ≤ 1 / t := by
      exact one_div_le_one_div_of_le ht (exp_sub_one_ge t ht.le)
    linarith
  have hA_ge : -(1 : ℝ) ≤ 1 / (Real.exp t - 1) - 1 / t := by
    have hdiv : 1 / t ≤ Real.exp t / (Real.exp t - 1) := by
      rw [div_le_div_iff₀ ht hposE]
      simpa [one_mul, mul_comm] using (exp_sub_one_le_mul_self t)
    have hrewrite : 1 / (Real.exp t - 1) - 1 / t + 1 =
        Real.exp t / (Real.exp t - 1) - 1 / t := by
      field_simp [(ne_of_gt hposE)]
      ring
    have : 0 ≤ Real.exp t / (Real.exp t - 1) - 1 / t := sub_nonneg.mpr hdiv
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- `K` extended by 0 at 0 for integrability -/
def kzero (t : ℝ) : ℝ := if t = 0 then 0 else K t

lemma kzero_eq_K {t : ℝ} (ht : t ≠ 0) : kzero t = K t := by
  simp [kzero, ht]

lemma kzero_abs_le_half {t : ℝ} (ht : 0 < t) : |kzero t| ≤ 1 / 2 := by
  rw [kzero_eq_K (ne_of_gt ht)]
  exact kernel_abs_le_half t ht

/-! ###### the integrands of the finite identity ###### -/

def kc (t : ℝ) : ℂ := (K t : ℂ)
def integrand (z : ℂ) (t : ℝ) : ℂ := kc t * expc (-z) t

def psumSeq (z : ℂ) (n : ℕ) : ℂ :=
  ((Real.log (n + 1 : ℝ) : ℂ)) - ∑ k ∈ Finset.range (n + 2), ((z + (k : ℂ))⁻¹)

def F (m : ℕ) (z : ℂ) (t : ℝ) : ℂ := (expc (-z) t - expc (-(m : ℂ)) t) / (t : ℂ)

def S (m : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  expc (-z) t * ∑ k ∈ Finset.range (m + 1), expc (-(k : ℂ)) t

def G (m : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  expc (-(m : ℂ)) t * (expc (-(z + 1 : ℂ)) t / (1 - expc (-(1 : ℂ)) t) - (t : ℂ)⁻¹)

/- pure algebraic identity: C-combination equals G -/
lemma comb_eq (m : ℕ) (A q t : ℂ) (hq : q ≠ 1) (ht : t ≠ 0) :
    (A - q ^ m) / t - A * (1 - q ^ (m + 1)) / (1 - q) + A / 2 +
        A * (q / (1 - q) - t⁻¹ + (1 / 2 : ℂ)) =
      q ^ m * (A * q / (1 - q) - t⁻¹) := by
  field_simp [hq, ht]
  ring

/- e^t equals (e^{-t})^{-1} as complex -/
lemma exp_t_eq_inv_exp_neg (t : ℝ) : (Real.exp t : ℂ) = (expc (-(1 : ℂ)) t)⁻¹ := by
  have hv := expc_neg_one_real t
  rw [hv]
  rw [← Complex.ofReal_inv]
  congr 1
  rw [Real.exp_neg, inv_inv]

/-- complex kernel equals `q/(1-q) - t⁻¹ + 1/2` where `q = e^{-t}` -/
lemma kc_eq (t : ℝ) (ht : 0 < t) :
    (K t : ℂ) = expc (-(1 : ℂ)) t / (1 - expc (-(1 : ℂ)) t) - (t : ℂ)⁻¹ + (1 / 2 : ℂ) := by
  have hq : expc (-(1 : ℂ)) t ≠ 1 := expc_neg_one_ne_one ht
  have hE : (Real.exp t : ℂ) = (expc (-(1 : ℂ)) t)⁻¹ := exp_t_eq_inv_exp_neg t
  have hq0 : expc (-(1 : ℂ)) t ≠ 0 := expc_ne_zero (-(1 : ℂ)) t
  unfold K
  -- (↑(1/(e^t-1)) - ↑(1/t) + ↑(1/2)) : ℂ
  have h1 : ((1 / (Real.exp t - 1) : ℝ) : ℂ) =
      expc (-(1 : ℂ)) t / (1 - expc (-(1 : ℂ)) t) := by
    have hsub : ((Real.exp t - 1 : ℝ) : ℂ) = (expc (-(1 : ℂ)) t)⁻¹ - 1 := by
      rw [← hE]
      norm_num
    rw [one_div]
    rw [Complex.ofReal_inv]
    rw [hsub]
    field_simp [hq0, hq]
  have h2 : ((1 / t : ℝ) : ℂ) = (t : ℂ)⁻¹ := by
    norm_num [one_div]
  calc
    (K t : ℂ) = ((1 / (Real.exp t - 1) : ℝ) : ℂ) - ((1 / t : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) := by
      unfold K
      rw [Complex.ofReal_add, Complex.ofReal_sub]
    _ = expc (-(1 : ℂ)) t / (1 - expc (-(1 : ℂ)) t) - (t : ℂ)⁻¹ + (1 / 2 : ℂ) := by
      rw [h1, h2]
      norm_num

/-- pointwise: F − S + half·e + integrand = G -/
lemma C_eq_G (m : ℕ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    F m z t - S m z t + ((1 / 2 : ℂ) * expc (-z) t) + integrand z t = G m z t := by
  have hq : expc (-(1 : ℂ)) t ≠ 1 := expc_neg_one_ne_one ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  let A : ℂ := expc (-z) t
  let q : ℂ := expc (-(1 : ℂ)) t
  have hA : A = expc (-z) t := rfl
  have hqdef : q = expc (-(1 : ℂ)) t := rfl
  have hq0 : q ≠ 1 := by simpa [q] using hq
  have hmain := comb_eq m A q (t : ℂ) hq0 ht0
  have hAq : A * q = expc (-(z + 1 : ℂ)) t := by
    dsimp [A, q]
    rw [← expc_add]
    congr 1
    ring
  have hqpm : q ^ m = expc (-(m : ℂ)) t := by
    dsimp [q]
    exact expc_pow m t
  unfold F S G integrand kc
  rw [kc_eq t ht]
  rw [geosum_eq_expc m t ht]
  rw [← hA]
  rw [← hqdef]
  rw [← hqpm]
  rw [← hAq]
  convert hmain using 1 <;> ring

/-! ###### log of positive reals, basic integrals ###### -/

lemma Complex_log_ofReal {x : ℝ} (hx : 0 < x) : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
  exact (Complex.ofReal_log (le_of_lt hx)).symm

lemma log_nat_complex (m : ℕ) (hm : 0 < m) : Complex.log (m : ℂ) = ((Real.log (m : ℝ)) : ℂ) := by
  simpa using Complex_log_ofReal (by exact_mod_cast hm : 0 < (m : ℝ))

/-- ∫ over Ioi of e^{-w t} = w⁻¹ -/
lemma integral_expc_neg (w : ℂ) (hw : 0 < w.re) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), expc (-w) t) = w⁻¹ := by
  have hfun : (fun t : ℝ => expc (-w) t) = fun x : ℝ => Complex.exp ((-w) * (x : ℂ)) := by
    funext x
    rfl
  have hI := integral_exp_mul_complex_Ioi (a := -w) (by simpa [hw] : (-w).re < 0) (0 : ℝ)
  rw [hfun, hI]
  simp

/-- e^{-w t} integrable on (0, ∞) for 0 < re w -/
lemma integrable_expc_neg (w : ℂ) (hw : 0 < w.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ => expc (-w) t) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -w) (by simpa [hw] : (-w).re < 0) (0 : ℝ)
  simpa [expc] using h

lemma kc_eq_target (t : ℝ) :
    (K t : ℂ) = ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) := by
  apply congrArg Complex.ofReal
  unfold K
  ring

lemma expc_neg_z_eq (z : ℂ) (t : ℝ) : expc (-z) t = Complex.exp (-(z * (t : ℂ))) := by
  unfold expc
  congr 1
  ring

/-- kernel·e^{-zt} integrable on (0,∞) -/
lemma integrable_kernel_expc (z : ℂ) (hz : 0 < z.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (K t : ℂ) * expc (-z) t) (Set.Ioi (0 : ℝ)) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_exp_integrable z hz
  have hfun : (fun t : ℝ => ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-(z * (t : ℂ)))) = fun t : ℝ => (K t : ℂ) * expc (-z) t := by
    funext t
    rw [kc_eq_target, expc_neg_z_eq]
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro t ht
  exact congr_fun hfun t

/-- S_m integrable on (0,∞) -/
lemma integrable_S (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => S m z t) (Set.Ioi (0 : ℝ)) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_S_integrable z hz m
  have hfun : (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ∑ k ∈ Finset.range (m + 1),
        Complex.exp (-((k : ℂ) * (t : ℂ)))) = fun t : ℝ => S m z t := by
    funext t
    unfold S
    congr 1
    · unfold expc
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      unfold expc
      congr 1
      ring
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro t ht
  exact congr_fun hfun t

/-- F_m integrable on (0,∞) -/
lemma integrable_F (z : ℂ) (hz : 0 < z.re) (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn (fun t : ℝ => F m z t) (Set.Ioi (0 : ℝ)) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_F_integrable z hz m hm
  have hfun : (fun t : ℝ =>
      (Complex.exp (-(z * (t : ℂ))) - Complex.exp (-(((m : ℝ) : ℂ) * (t : ℂ)))) / (t : ℂ)) =
      fun t : ℝ => F m z t := by
    funext t
    unfold F
    congr 2
    · unfold expc
      congr 1
      ring
    · unfold expc
      congr 1
      rw [Complex.ofReal_natCast]
      ring
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro t ht
  exact congr_fun hfun t

/-- helper: expc(−(z+k))t is integrable on (0,∞) -/
lemma integrable_expc_neg_add (z : ℂ) (hz : 0 < z.re) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => expc (-(z + (k : ℂ))) t) (Set.Ioi (0 : ℝ)) := by
  apply integrable_expc_neg (z + (k : ℂ))
  rw [Complex.add_re]
  have hkre : ((k : ℂ).re) = (k : ℝ) := by simp
  have hk : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  rw [hkre]
  linarith

/-- pointwise: expc(−z)·expc(−k) = expc(−(z+k)) -/
lemma expc_mul_neg_nat (z : ℂ) (k : ℕ) (t : ℝ) :
    expc (-z) t * expc (-(k : ℂ)) t = expc (-(z + (k : ℂ))) t := by
  rw [← expc_add]
  congr 1
  ring

/-- piece: geometric-sum integral = partial fraction sum -/
lemma integral_S_eq (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), S m z t) =
      ∑ k ∈ Finset.range (m + 1), (z + (k : ℂ))⁻¹ := by
  -- S = Σ_k expc(−(z+k))t on all t; then sum of integrals.
  have hSfun : (fun t : ℝ => S m z t) =
      fun t : ℝ => ∑ k ∈ Finset.range (m + 1), expc (-(z + (k : ℂ))) t := by
    funext t
    unfold S
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact expc_mul_neg_nat z k t
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), S m z t)
        = ∫ t : ℝ, (S m z t) ∂μ := by rfl
    _ = ∫ t : ℝ, (∑ k ∈ Finset.range (m + 1), expc (-(z + (k : ℂ))) t) ∂μ := by
          rw [hSfun]
    _ = ∑ k ∈ Finset.range (m + 1), (∫ t : ℝ, expc (-(z + (k : ℂ))) t ∂μ) := by
          rw [MeasureTheory.integral_finset_sum]
          intro k hk
          exact integrable_expc_neg_add z hz k
    _ = ∑ k ∈ Finset.range (m + 1), (z + (k : ℂ))⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_expc_neg (z + (k : ℂ)) (by
            rw [Complex.add_re]
            have hkre : ((k : ℂ).re) = (k : ℝ) := by simp
            rw [hkre]
            have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
            linarith)]

/-- piece: ∫ F_m = log m − log z (via complex Frullani) -/
lemma integral_F_eq (z : ℂ) (hz : 0 < z.re) (m : ℕ) (hm : 0 < m) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), F m z t) = Complex.log (m : ℂ) - Complex.log z := by
  let H : ℝ → ℂ := fun t : ℝ => (Complex.exp (-(z * (t : ℂ))) - Complex.exp (-(((m : ℝ) : ℂ) * (t : ℂ)))) / (t : ℂ)
  have hcl : (∫ t : ℝ in Set.Ioi (0 : ℝ), H t) = Complex.log ((m : ℝ) : ℂ) - Complex.log z := by
    simpa [H] using (Commons.Analysis.SpecialFunctions.Frullani.complex_log z hz (m : ℝ) (by exact_mod_cast hm))
  have hfun : (fun t : ℝ => F m z t) = H := by
    funext t
    unfold F H
    congr 2
    · unfold expc
      congr 1
      ring
    · unfold expc
      congr 1
      rw [Complex.ofReal_natCast]
      ring
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), F m z t) = ∫ t : ℝ in Set.Ioi (0 : ℝ), H t := by
      rw [hfun]
    _ = Complex.log ((m : ℝ) : ℂ) - Complex.log z := hcl
    _ = Complex.log (m : ℂ) - Complex.log z := by
      rw [Complex.ofReal_natCast]

/-- piece: ∫ (1/2) e^{-zt} = (2)⁻¹ z⁻¹ -/
lemma integral_half_expc (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), ((1 / 2 : ℂ) * expc (-z) t)) = ((2 : ℂ)⁻¹) * z⁻¹ := by
  rw [MeasureTheory.integral_const_mul]
  rw [integral_expc_neg z hz]
  norm_num

/-- combined integrand of the finite identity -/
def C (m : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  F m z t - S m z t + ((1 / 2 : ℂ) * expc (-z) t) + integrand z t

/-- integrability of the combined integrand -/
lemma integrable_C (z : ℂ) (hz : 0 < z.re) (m : ℕ) (hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn (fun t : ℝ => C m z t) (Set.Ioi (0 : ℝ)) := by
  have hFS : MeasureTheory.IntegrableOn (fun t : ℝ => F m z t - S m z t) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.sub (integrable_F z hz m hm) (integrable_S z hz m)
  have hhalf : MeasureTheory.IntegrableOn (fun t : ℝ => ((1 / 2 : ℂ) * expc (-z) t)) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Integrable.const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (integrable_expc_neg z hz) (1 / 2 : ℂ)
  have hker : MeasureTheory.IntegrableOn (fun t : ℝ => integrand z t) (Set.Ioi (0 : ℝ)) := by
    unfold integrand kc
    exact integrable_kernel_expc z hz
  have hSum2 : MeasureTheory.IntegrableOn (fun t : ℝ => ((1 / 2 : ℂ) * expc (-z) t) + integrand z t)
      (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.add hhalf hker
  have hSum : MeasureTheory.IntegrableOn (fun t : ℝ => (F m z t - S m z t) +
      (((1 / 2 : ℂ) * expc (-z) t) + integrand z t)) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.add hFS hSum2
  convert hSum using 1
  ext t
  unfold C
  ring

/-- (∫F − ∫S) + (∫half + ∫integrand) = ∫C -/
lemma integral_C_comb (z : ℂ) (hz : 0 < z.re) (m : ℕ) (hm : 1 ≤ m) :
    ((∫ t : ℝ in Set.Ioi (0 : ℝ), F m z t) - (∫ t : ℝ in Set.Ioi (0 : ℝ), S m z t)) +
        ((∫ t : ℝ in Set.Ioi (0 : ℝ), ((1 / 2 : ℂ) * expc (-z) t)) +
          (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t)) =
      (∫ t : ℝ in Set.Ioi (0 : ℝ), C m z t) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hF : MeasureTheory.Integrable (fun t : ℝ => F m z t) μ := integrable_F z hz m hm
  have hS : MeasureTheory.Integrable (fun t : ℝ => S m z t) μ := integrable_S z hz m
  have hhalf : MeasureTheory.Integrable (fun t : ℝ => ((1 / 2 : ℂ) * expc (-z) t)) μ := by
    simpa [μ] using (MeasureTheory.Integrable.const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (integrable_expc_neg z hz) (1 / 2 : ℂ))
  have hker : MeasureTheory.Integrable (fun t : ℝ => integrand z t) μ := by
    dsimp [μ]
    unfold integrand kc
    exact integrable_kernel_expc z hz
  have hFS : MeasureTheory.Integrable (fun t : ℝ => F m z t - S m z t) μ := MeasureTheory.Integrable.sub hF hS
  have hSum2 : MeasureTheory.Integrable (fun t : ℝ => ((1 / 2 : ℂ) * expc (-z) t) + integrand z t) μ :=
    MeasureTheory.Integrable.add hhalf hker
  calc
    ((∫ t : ℝ, F m z t ∂μ) - (∫ t : ℝ, S m z t ∂μ)) + ((∫ t : ℝ, ((1 / 2 : ℂ) * expc (-z) t) ∂μ) +
          (∫ t : ℝ, integrand z t ∂μ))
        = (∫ t : ℝ, F m z t - S m z t ∂μ) + ((∫ t : ℝ, ((1 / 2 : ℂ) * expc (-z) t) ∂μ) +
            (∫ t : ℝ, integrand z t ∂μ)) := by
          rw [← MeasureTheory.integral_sub hF hS]
    _ = (∫ t : ℝ, F m z t - S m z t ∂μ) + ∫ t : ℝ, ((1 / 2 : ℂ) * expc (-z) t) + integrand z t ∂μ := by
          rw [← MeasureTheory.integral_add hhalf hker]
    _ = ∫ t : ℝ, (F m z t - S m z t) + (((1 / 2 : ℂ) * expc (-z) t) + integrand z t) ∂μ := by
          rw [← MeasureTheory.integral_add hFS hSum2]
    _ = ∫ t : ℝ, C m z t ∂μ := by
          apply MeasureTheory.integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro t
          unfold C
          ring
    _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), C m z t := by
          rfl
/-- finite identity: psum − log z + inv2z + E = ∫ G -/
lemma finite_identity (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    psumSeq z n - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ +
        (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t) =
      (∫ t : ℝ in Set.Ioi (0 : ℝ), G (n + 1) z t) := by
  have hpos : 0 < n + 1 := by omega
  have hF := integral_F_eq z hz (n + 1) hpos
  have hS := integral_S_eq z hz (n + 1)
  have hH := integral_half_expc z hz
  calc
    psumSeq z n - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ +
        (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t)
      = (Complex.log ((n + 1 : ℕ) : ℂ) - Complex.log z) -
          (∑ k ∈ Finset.range (n + 2), (z + (k : ℂ))⁻¹) +
          ((2 : ℂ)⁻¹) * z⁻¹ + (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t) := by
          rw [show psumSeq z n =
            (Real.log (n + 1 : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 2), (z + (k : ℂ))⁻¹ by rfl]
          have hlog : (Real.log (n + 1 : ℝ) : ℂ) = (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) := by
            congr 1
            norm_num
          rw [hlog]
          rw [← log_nat_complex (n + 1) hpos]
          ring
    _ = (∫ t : ℝ in Set.Ioi (0 : ℝ), F (n + 1) z t) - (∫ t : ℝ in Set.Ioi (0 : ℝ), S (n + 1) z t) +
        ((∫ t : ℝ in Set.Ioi (0 : ℝ), ((1 / 2 : ℂ) * expc (-z) t)) +
          (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t)) := by
          rw [← hF]
          rw [← hS]
          rw [← hH]
          ring
    _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), C (n + 1) z t := integral_C_comb z hz (n + 1) (by omega)
    _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), G (n + 1) z t := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact C_eq_G (n + 1) z ht

/-- dominated convergence: ∫_0^∞ G_{n+1} → 0 -/
lemma G_integral_tendsto_zero (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => (∫ t : ℝ in Set.Ioi (0 : ℝ), G (n + 1) z t)) atTop (𝓝 (0 : ℂ)) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_Gintegral_zero z hz
  refine h.congr' ?_
  filter_upwards with n
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold G
  have hE1 : expc (-((n + 1 : ℕ) : ℂ)) t = Complex.exp (-(((n + 1 : ℕ) : ℂ) * (t : ℂ))) := by
    unfold expc
    congr 1
    ring
  have hE2 : expc (-(z + 1 : ℂ)) t = Complex.exp (-((z + 1 : ℂ) * (t : ℂ))) := by
    unfold expc
    congr 1
    ring
  have hE3 : expc (-(1 : ℂ)) t = Complex.exp (-(t : ℂ)) := by
    unfold expc
    congr 1
    ring
  rw [hE1, hE2, hE3]
  rfl

/-- final theorem -/
theorem digamma_logRem_Binet (z : ℂ) (hz : 0 < z.re) :
    Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ =
      -∫ t in Set.Ioi (0 : ℝ),
        ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))) := by
  let sSeq : ℕ → ℂ := fun n => psumSeq z n - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹
  have hD := Commons.Analysis.SpecialFunctions.Gamma.digamma_partialSum z hz
  have hA : Tendsto sSeq atTop (𝓝 (Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹)) := by
    dsimp [sSeq]
    exact (hD.sub tendsto_const_nhds).add tendsto_const_nhds
  have hlimG := G_integral_tendsto_zero z hz
  have hB' : Tendsto (fun n : ℕ =>
      (∫ t : ℝ in Set.Ioi (0 : ℝ), G (n + 1) z t) - (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t))
      atTop (𝓝 (-(∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t))) := by
    simpa using (hlimG.sub tendsto_const_nhds)
  have hB : Tendsto sSeq atTop (𝓝 (-(∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t))) := by
    refine hB'.congr' ?_
    filter_upwards with n
    dsimp [sSeq]
    have h := finite_identity z hz n
    calc
      (∫ t : ℝ in Set.Ioi (0 : ℝ), G (n + 1) z t) - (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t)
          = (psumSeq z n - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ +
              (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t)) -
            (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t) := by rw [← h]
      _ = psumSeq z n - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ := by ring
  have hConv : (∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t) =
      ∫ t in Set.Ioi (0 : ℝ),
        ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold integrand kc
    rw [kc_eq_target t, expc_neg_z_eq]
  have hEq := tendsto_nhds_unique hA hB
  calc
    Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹
        = -(∫ t : ℝ in Set.Ioi (0 : ℝ), integrand z t) := hEq
    _ = -∫ t in Set.Ioi (0 : ℝ),
        ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))) := by rw [hConv]

end Commons.Analysis.SpecialFunctions.Gamma
