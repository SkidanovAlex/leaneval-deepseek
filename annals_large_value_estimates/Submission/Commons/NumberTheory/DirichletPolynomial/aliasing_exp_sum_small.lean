import Mathlib
import Submission.Commons.Analysis.ExponentialSums.kusmin_landau
import Submission.Commons.Analysis.Summation.abel_prefix_bound
import Submission.Commons.Analysis.Integral.integral_integral_Icc_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletPolynomial

open MeasureTheory intervalIntegral Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-!
# Aliasing estimate: the sum and the integral of `n^{iδ}` differ by `O(1)`

We prove that for `N ≥ 1` and real `δ` with `|δ| ≤ N`,
`|∑_{n=N}^{2N} n^{iδ} − ∫_N^{2N} x^{iδ} dx| ≤ C` for an absolute constant `C`,
which is a strengthening of the requested statement (whose right-hand side is
`C(1 + |δ|/N) ≥ C`).

The argument is a first-order "midpoint/Taylor" comparison.  Writing
`F(x) = exp (i δ log x)`, one has the exact identity
`F(x) − F(n) = ∫_n^x F'(t) dt` and hence
`∫_n^{n+1} (F(x) − F(n)) dx = ∫_0^1 (1−u) F'(n+u) du`.
Summing over `n` and swapping sum and integral,
`∑_{n=N}^{2N} F(n) − ∫_N^{2N} F = F(2N) − iδ ∫_0^1 (1−u) Σ(u) du`,
where `Σ(u) = ∑_{n=N}^{2N−1} F(n+u)/(n+u)` is a weighted exponential sum.  The
Kusmin–Landau inequality bounds its partial sums by `4πN/|δ|`, and Abel
summation then bounds `Σ` by `4π/|δ|`.
-/

/-- The basic oscillating function `x ↦ exp (i δ log x)`, which equals `x ^ (iδ)`
for `x > 0`. -/
def Fw (δ : ℝ) : ℝ → ℂ := fun x => Complex.exp ((Complex.I * (δ : ℂ)) * ((Real.log x : ℝ) : ℂ))

/-- Its formal derivative, `F'(x) = F(x) · iδ / x`. -/
def FwD (δ : ℝ) : ℝ → ℂ := fun x => Fw δ x * ((Complex.I * (δ : ℂ)) * (x : ℂ)⁻¹)

lemma Fw_eq_exp (δ x : ℝ) : Fw δ x = Complex.exp (((δ * Real.log x : ℝ) : ℂ) * Complex.I) := by
  simp only [Fw]; congr 1; push_cast; ring

lemma Fw_eq_cpow {δ x : ℝ} (hx : 0 < x) : Fw δ x = (x : ℂ) ^ (Complex.I * (δ : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  simp only [Fw]; ring_nf

lemma norm_ofReal_complex (r : ℝ) : ‖((r:ℂ))‖ = |r| := RCLike.norm_ofReal _

lemma norm_Fw {δ x : ℝ} (_hx : 0 < x) : ‖Fw δ x‖ = 1 := by
  rw [Fw_eq_exp, Complex.norm_exp_ofReal_mul_I]

lemma Fw_neg_eq_conj (δ x : ℝ) : Fw (-δ) x = conj (Fw δ x) := by
  rw [Fw, Fw, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma hasDerivAt_Fw (δ x : ℝ) (hx : 0 < x) : HasDerivAt (Fw δ) (FwD δ x) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Complex.I * (δ : ℂ)) * ((Real.log y : ℝ) : ℂ))
      ((Complex.I * (δ : ℂ)) * ((x:ℝ)⁻¹ : ℝ)) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.log y) (x⁻¹) x := Real.hasDerivAt_log hx.ne'
    exact (h1.ofReal_comp).const_mul (Complex.I * (δ : ℂ))
  have hexp := hlog.cexp
  have hFF : Fw δ = fun y => Complex.exp ((Complex.I * (δ : ℂ)) * ((Real.log y : ℝ) : ℂ)) := rfl
  rw [hFF, FwD, hFF]
  convert hexp using 1
  · push_cast; ring

lemma continuousOn_Fw (δ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (Fw δ) (Set.Icc a b) := by
  refine ContinuousOn.cexp ?_
  apply ContinuousOn.mul continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  refine Real.continuousOn_log.mono ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

lemma continuousOn_FwD (δ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (FwD δ) (Set.Icc a b) := by
  unfold FwD
  refine ContinuousOn.mul (continuousOn_Fw δ ha) ?_
  refine ContinuousOn.mul continuousOn_const ?_
  refine ContinuousOn.inv₀ ?_ ?_
  · exact Complex.continuous_ofReal.continuousOn
  · intro x hx
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le ha hx.1))

lemma intervalIntegrable_FwD (δ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (FwD δ) volume (n:ℝ) ((n:ℝ)+1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    (continuousOn_FwD δ hn0)

lemma intervalIntegrable_Fw (δ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (Fw δ) volume (n:ℝ) ((n:ℝ)+1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith) (continuousOn_Fw δ hn0)

lemma integral_eq_sub_Fw (δ : ℝ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : (n:ℝ) ≤ x) :
    ∫ t in (n:ℝ)..x, FwD δ t = Fw δ x - Fw δ (n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hderiv : ∀ t ∈ Set.uIcc (n:ℝ) x, HasDerivAt (Fw δ) (FwD δ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact hasDerivAt_Fw δ t (lt_of_lt_of_le hn0 ht.1)
  have hint : IntervalIntegrable (FwD δ) volume (n:ℝ) x :=
    ContinuousOn.intervalIntegrable_of_Icc hx (continuousOn_FwD δ hn0)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The inner identity: `∫_n^{n+1} (F x − F n) = ∫_0^1 (1−u) F'(n+u) du`. -/
lemma inside_id (δ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (n:ℝ)..((n:ℝ)+1), (Fw δ x - Fw δ n)
      = ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * FwD δ (n+u) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnn : (n:ℝ) ≤ (n:ℝ)+1 := by linarith
  have hstep1 : ∀ x ∈ Set.uIcc (n:ℝ) ((n:ℝ)+1),
      Fw δ x - Fw δ n = ∫ t in (n:ℝ)..x, FwD δ t := by
    intro x hx
    rw [Set.uIcc_of_le hnn] at hx
    exact (integral_eq_sub_Fw δ hn hx.1).symm
  rw [intervalIntegral.integral_congr hstep1]
  rw [Commons.Analysis.Integral.integral_integral_Icc_eq (FwD δ) hnn (continuousOn_FwD δ hn0)]
  have hsub : (∫ x in (0:ℝ)..1, (((n:ℝ)+1 - (x + (n:ℝ)) : ℝ)) * FwD δ (x + (n:ℝ)))
      = ∫ t in (n:ℝ)..((n:ℝ)+1), (((n:ℝ)+1 - t : ℝ)) * FwD δ t := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1)
      (f := fun t : ℝ => (((n:ℝ)+1 - t : ℝ)) * FwD δ t) (n:ℝ)
    rw [zero_add] at h
    rw [show (1:ℝ) + (n:ℝ) = (n:ℝ) + 1 from by ring] at h
    exact h
  rw [← hsub]
  refine intervalIntegral.integral_congr ?_
  intro u _
  ring_nf

/-! ## Kusmin–Landau helpers -/

/-- Integer distance lower bound: a point in the band `[η, 1−η]` has integer
distance at least `η`. -/
lemma intDist_ge_of_mem {x η : ℝ} (hη : 0 < η) (hx0 : η ≤ x) (hx1 : x ≤ 1 - η) :
    η ≤ Submission.VanDerCorput.intDist x := by
  by_contra h
  rw [not_le] at h
  obtain ⟨k, hk⟩ := (Submission.IntDistRegion.intDist_lt_iff_exists_int (x := x) hη.le).mp h
  have hk0 : k = 0 := by
    rw [← Int.abs_lt_one_iff]
    have h1 : |(k:ℝ)| < 1 := by
      calc |(k:ℝ)| = |((k:ℝ) - x) + x| := by ring_nf
        _ ≤ |(k:ℝ) - x| + |x| := abs_add_le _ _
        _ = |x - (k:ℝ)| + |x| := by rw [abs_sub_comm]
        _ < η + (1 - η) := by
            have : |x| ≤ x := le_of_eq (abs_of_nonneg (by linarith : 0 ≤ x))
            linarith
        _ = 1 := by ring
    rw [← Int.cast_abs] at h1
    exact_mod_cast h1
  rw [hk0] at hk
  simp only [Int.cast_zero, sub_zero] at hk
  have hxabs : |x| = x := abs_of_nonneg (by linarith : 0 ≤ x)
  rw [hxabs] at hk
  linarith

/-- The log phase `v ↦ δ log (v + u) / (2π)`. -/
def phi (δ u : ℝ) : ℝ → ℝ := fun v => δ * Real.log (v + u) / (2 * Real.pi)

lemma hasDerivAt_log_add {u v : ℝ} (hv : 0 < v + u) :
    HasDerivAt (fun v : ℝ => Real.log (v + u)) ((v+u)⁻¹) v := by
  have h := (Real.hasDerivAt_log (ne_of_gt hv)).comp v (hasDerivAt_id v |>.add_const u)
  simpa [Function.comp_def] using h

lemma deriv_phi {δ u v : ℝ} (hv : 0 < v + u) :
    deriv (phi δ u) v = (δ / (2 * Real.pi)) * (v + u)⁻¹ := by
  have h1 := hasDerivAt_log_add (u := u) hv
  have h2 : HasDerivAt (fun v : ℝ => δ / (2*Real.pi) * Real.log (v + u))
      (δ/(2*Real.pi) * (v+u)⁻¹) v := h1.const_mul _
  have hcong : phi δ u = fun v => δ/(2*Real.pi) * Real.log (v + u) := by
    funext w; unfold phi; ring
  rw [hcong, h2.deriv]

lemma deriv_phi' {δ u v : ℝ} (hv : 0 < v + u) :
    deriv (phi δ u) v = δ / (2 * Real.pi * (v + u)) := by
  rw [deriv_phi hv]; field_simp

lemma abs_deriv_phi {δ u v : ℝ} (hv : 0 < v + u) :
    |deriv (phi δ u) v| = |δ| / (2 * Real.pi * (v + u)) := by
  rw [deriv_phi' hv, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * (v + u))]

lemma contDiffOn_phi (δ u : ℝ) {a b : ℝ} (ha : 0 < a + u) :
    ContDiffOn ℝ 1 (phi δ u) (Set.Icc a b) := by
  unfold phi
  have h1 : ContDiffOn ℝ 1 (fun v : ℝ => Real.log (v + u)) (Set.Icc a b) := by
    refine (contDiffOn_id.add contDiffOn_const).log (fun v hv => ?_)
    have hav : a ≤ v := hv.1
    have hpos : 0 < v + u := by linarith
    exact ne_of_gt hpos
  have h2 : ContDiffOn ℝ 1 (fun v : ℝ => δ * Real.log (v + u)) (Set.Icc a b) :=
    contDiffOn_const.mul h1
  exact h2.div_const _

lemma deriv_phi_mono {δ u a b : ℝ} (ha : 0 < a + u) :
    MonotoneOn (deriv (phi δ u)) (Set.Icc a b) ∨
      AntitoneOn (deriv (phi δ u)) (Set.Icc a b) := by
  rcases lt_trichotomy δ 0 with hδ | hδ | hδ
  · left
    intro v1 h1 v2 h2 hv12
    have hp1 : 0 < v1 + u := by linarith [ha, h1.1]
    have hp2 : 0 < v2 + u := by linarith [ha, h2.1]
    rw [deriv_phi hp1, deriv_phi hp2]
    have hinv : (v2 + u)⁻¹ ≤ (v1 + u)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (b := v2 + u) hp1 (by linarith)
    have hc : δ / (2*Real.pi) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ.le (by positivity)
    exact mul_le_mul_of_nonpos_left hinv hc
  · subst hδ
    left
    intro v1 h1 v2 h2 hv12
    have hp1 : 0 < v1 + u := by linarith [ha, h1.1]
    have hp2 : 0 < v2 + u := by linarith [ha, h2.1]
    rw [deriv_phi hp1, deriv_phi hp2]; simp
  · right
    intro v1 h1 v2 h2 hv12
    have hp1 : 0 < v1 + u := by linarith [ha, h1.1]
    have hp2 : 0 < v2 + u := by linarith [ha, h2.1]
    rw [deriv_phi hp1, deriv_phi hp2]
    have hinv : (v2 + u)⁻¹ ≤ (v1 + u)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (b := v2 + u) hp1 (by linarith)
    have hc : 0 ≤ δ / (2*Real.pi) := div_nonneg hδ.le (by positivity)
    exact mul_le_mul_of_nonneg_left hinv hc

/-- Cast an `ℤ`-interval sum to a `ℕ`-interval sum. -/
lemma sum_Icc_int_eq (g : ℕ → ℂ) {a b : ℕ} (_hab : a ≤ b) :
    ∑ k ∈ Finset.Icc (a:ℤ) (b:ℤ), g k.toNat = ∑ k ∈ Finset.Icc a b, g k := by
  refine Finset.sum_bij (fun (k:ℤ) _ => k.toNat) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨by omega, by omega⟩
  · intro k1 hk1 k2 hk2 h
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    refine ⟨(k:ℤ), ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩, ?_⟩
    omega
  · intro k hk
    rfl

lemma kl_term_eq (δ u x : ℝ) (_hx : 0 < x + u) :
    Complex.exp (((2 * Real.pi * phi δ u x : ℝ):ℂ) * Complex.I) = Fw δ (x + u) := by
  have h2 : 2 * Real.pi * phi δ u x = δ * Real.log (x + u) := by
    unfold phi; field_simp
  rw [h2, Fw]
  congr 1
  push_cast; ring

/-- Kusmin–Landau bound for the partial exponential sums. -/
lemma partial_sum_bound (N m : ℕ) (hN : 2 ≤ N) (hm1 : N ≤ m) (hm2 : m ≤ 2*N - 1)
    {δ : ℝ} (hδ : 0 < δ) (hδN : δ ≤ N) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ k ∈ Finset.Icc N m, Fw δ ((k:ℝ) + u)‖ ≤ 4 * Real.pi * N / δ := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hmR : (m:ℝ) ≤ 2*(N:ℝ) - 1 := by
    have : (m:ℝ) ≤ ((2*N - 1 : ℕ) : ℝ) := by exact_mod_cast hm2
    rw [Nat.cast_sub (by omega : 1 ≤ 2*N)] at this
    push_cast at this ⊢
    linarith
  set A : ℤ := (N:ℤ) - 1 with hA
  set B : ℤ := (m:ℤ) with hB
  have hAB : A ≤ B := by simp only [hA, hB]; omega
  have hη : 0 < δ / (4 * Real.pi * N) := by positivity
  have hA1 : A + 1 = (N:ℤ) := by simp only [hA]; ring
  have hAval : (A:ℝ) = (N:ℝ) - 1 := by simp only [hA]; push_cast; ring
  have hBval : (B:ℝ) = (m:ℝ) := by simp [hB]
  have hAa : 0 < (A:ℝ) + u := by rw [hAval]; linarith
  have hcont : ContDiffOn ℝ 1 (phi δ u) (Set.Icc (A:ℝ) (B:ℝ)) := contDiffOn_phi δ u hAa
  have hmono := deriv_phi_mono (δ := δ) (u := u) (a := (A:ℝ)) (b := (B:ℝ)) hAa
  have hdist : ∀ x ∈ Set.Icc (A:ℝ) (B:ℝ),
      δ / (4 * Real.pi * N) ≤ Submission.VanDerCorput.intDist (deriv (phi δ u) x) := by
    intro x hx
    have hxle : x ≤ (m:ℝ) := by rw [← hBval]; exact hx.2
    have hxge : (N:ℝ) - 1 ≤ x := by rw [← hAval]; exact hx.1
    have hxpos : 0 < x + u := by linarith
    refine intDist_ge_of_mem hη ?_ ?_
    · rw [deriv_phi' hxpos]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi * ↑N)
            (by positivity : (0:ℝ) < 2 * Real.pi * (x + u))]
      have hkey : x + u ≤ 2 * (N:ℝ) := by linarith [hxle, hmR, hu1]
      have hkey2 : 2 * Real.pi * (x + u) ≤ 2 * Real.pi * (2 * (N:ℝ)) := by
        nlinarith [Real.pi_pos, hkey]
      have hmul := mul_le_mul_of_nonneg_left hkey2 (le_of_lt hδ)
      ring_nf at hmul ⊢
      linarith [hmul]
    · rw [deriv_phi' hxpos]
      have hlt : δ / (2 * Real.pi * (x + u)) ≤ 1 / Real.pi := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * (x + u)) (by positivity : (0:ℝ) < Real.pi)]
        have hkey : δ ≤ 2 * (x + u) := by nlinarith [hδN, hxge, hu0, hN2]
        nlinarith [Real.pi_pos, hkey]
      have h2 : (1:ℝ) - δ / (4 * Real.pi * N) ≥ 1 - 1/(4*Real.pi) := by
        have : δ / (4 * Real.pi * N) ≤ 1/(4*Real.pi) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4*Real.pi*↑N) (by positivity : (0:ℝ) < 4*Real.pi)]
          nlinarith [Real.pi_pos, hδ, hδN, hNpos]
        linarith
      have h3 : (1:ℝ)/Real.pi ≤ 1 - 1/(4*Real.pi) := by
        have hpi : (1 - 1/(4*Real.pi)) * Real.pi = Real.pi - 1/4 := by
          field_simp
        rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi), hpi]
        linarith [Real.pi_gt_three]
      linarith [hlt, h3, h2]
  have hKL := Commons.Analysis.ExponentialSums.kusmin_landau (A := A) (B := B) hAB hη hcont hmono hdist
  have hcast : (∑ n ∈ Finset.Icc (N:ℤ) (m:ℤ), Fw δ ((n:ℝ) + u))
      = ∑ k ∈ Finset.Icc N m, Fw δ ((k:ℝ) + u) := by
    rw [← sum_Icc_int_eq (fun k => Fw δ ((k:ℝ)+u)) hm1]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0:ℤ) ≤ n := by omega
    have hnat : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    have hreal : ((n.toNat : ℕ) : ℝ) = (n:ℝ) := by exact_mod_cast hnat
    rw [hreal]
  have hsum_eq : (∑ n ∈ Finset.Icc (A+1) B, Complex.exp (((2 * Real.pi * phi δ u (n:ℝ) : ℝ):ℂ) * Complex.I))
      = ∑ k ∈ Finset.Icc N m, Fw δ ((k:ℝ) + u) := by
    rw [hA1]
    have hterm : ∀ n ∈ Finset.Icc (N:ℤ) (m:ℤ),
        Complex.exp (((2 * Real.pi * phi δ u (n:ℝ) : ℝ):ℂ) * Complex.I) = Fw δ ((n:ℝ) + u) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn0 : 0 < (n:ℝ) + u := by
        have : (2:ℤ) ≤ n := by omega
        have h2r : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast this
        linarith
      exact kl_term_eq δ u (n:ℝ) hn0
    rw [Finset.sum_congr rfl hterm]
    exact hcast
  rw [← hsum_eq]
  have hres := hKL
  have hone : (1:ℝ) / (δ / (4 * Real.pi * N)) = 4 * Real.pi * N / δ := by rw [one_div_div]
  rw [hone] at hres
  exact hres

/-- Kusmin–Landau partial-sum bound with `|δ|`. -/
lemma partial_sum_bound_abs (N m : ℕ) (hN : 2 ≤ N) (hm1 : N ≤ m) (hm2 : m ≤ 2*N - 1)
    {δ : ℝ} (hδ : δ ≠ 0) (hδN : |δ| ≤ N) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ k ∈ Finset.Icc N m, Fw δ ((k:ℝ) + u)‖ ≤ 4 * Real.pi * N / |δ| := by
  rcases lt_trichotomy δ 0 with hlt | heq | hgt
  · have hpos : 0 < -δ := by linarith
    have hle : -δ ≤ (N:ℝ) := by
      rw [abs_of_neg hlt] at hδN; linarith
    have h1 := partial_sum_bound N m hN hm1 hm2 hpos hle u hu0 hu1
    have hconj : (∑ k ∈ Finset.Icc N m, Fw δ ((k:ℝ) + u))
        = conj (∑ k ∈ Finset.Icc N m, Fw (-δ) ((k:ℝ) + u)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Fw_neg_eq_conj]; simp
    rw [hconj, Complex.norm_conj, abs_of_neg hlt]
    exact h1
  · exact absurd heq hδ
  · have hle : δ ≤ (N:ℝ) := by
      rw [abs_of_pos hgt] at hδN; exact hδN
    have h1 := partial_sum_bound N m hN hm1 hm2 hgt hle u hu0 hu1
    rwa [abs_of_pos hgt]

/-- Telescoping sum over an `Icc` window. -/
lemma sum_Icc_telescope_aes {G : Type*} [AddCommGroup G] (f : ℕ → G) {N K : ℕ} (hNK : N ≤ K) :
    ∑ j ∈ Finset.Icc N K, (f j - f (j + 1)) = f N - f (K + 1) := by
  induction K, hNK using Nat.le_induction with
  | base => rw [Finset.Icc_self]; simp
  | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega : N ≤ k + 1), ih]
      abel

/-- Bound on the weighted exponential sum `Σ(u) = ∑_{n=N}^{2N−1} F(n+u)/(n+u)`. -/
lemma Sigma_bound {N : ℕ} (hN : 2 ≤ N) {δ : ℝ} (hδ : δ ≠ 0) (hδN : |δ| ≤ N)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ n ∈ Finset.Icc N (2*N-1), Fw δ ((n:ℝ)+u) * ((((n:ℝ)+u)⁻¹ : ℝ) : ℂ)‖
      ≤ 4 * Real.pi / |δ| := by
  have hpos : 0 < |δ| := abs_pos.mpr hδ
  have hN1 : 1 ≤ N := by omega
  have hM : N ≤ 2*N - 1 := by omega
  have hB : ∀ n, N ≤ n → n ≤ 2*N-1 →
      ‖∑ k ∈ Finset.Icc N n, Fw δ ((k:ℝ) + u)‖ ≤ 4 * Real.pi * N / |δ| :=
    fun n h1 h2 => partial_sum_bound_abs N n hN h1 h2 hδ hδN u hu0 hu1
  have hab := Commons.Analysis.Summation.abel_prefix_bound
    (fun n => Fw δ ((n:ℝ)+u)) (fun n => ((((n:ℝ)+u)⁻¹ : ℝ) : ℂ))
    (4 * Real.pi * N / |δ|) hM hN1 hB
  refine le_trans hab ?_
  have hbM : ‖(((((2*N-1:ℕ):ℝ)+u)⁻¹ : ℝ) : ℂ)‖ = (((2*N-1:ℕ):ℝ)+u)⁻¹ := by
    rw [norm_ofReal_complex, abs_of_nonneg (by positivity)]
  have hvar : (∑ n ∈ Finset.Icc N ((2*N-1) - 1),
      ‖((((n:ℝ)+u)⁻¹ : ℝ) : ℂ) - (((((n+1:ℕ):ℝ)+u)⁻¹ : ℝ) : ℂ)‖)
      = ((N:ℝ)+u)⁻¹ - ((((2*N-1:ℕ):ℝ)+u)⁻¹) := by
    have hterm : ∀ n ∈ Finset.Icc N ((2*N-1)-1),
        ‖((((n:ℝ)+u)⁻¹ : ℝ) : ℂ) - (((((n+1:ℕ):ℝ)+u)⁻¹ : ℝ) : ℂ)‖
          = ((n:ℝ)+u)⁻¹ - (((n+1:ℕ):ℝ)+u)⁻¹ := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have h1 : (0:ℝ) < (n:ℝ) + u := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        linarith
      have hle : (n:ℝ) + u ≤ ((n+1:ℕ):ℝ) + u := by push_cast; linarith
      rw [← Complex.ofReal_sub, norm_ofReal_complex,
          abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ h1 hle))]
    rw [Finset.sum_congr rfl hterm]
    have htel := sum_Icc_telescope_aes (fun j : ℕ => (((j:ℝ)+u)⁻¹)) (by omega : N ≤ (2*N-1) - 1)
    rw [htel]
    have hK : ((2*N-1) - 1) + 1 = 2*N-1 := by omega
    rw [hK]
  rw [hbM, hvar]
  have hcomb : (4 * Real.pi * N / |δ|) * (((2*N-1:ℕ):ℝ)+u)⁻¹
      + (4 * Real.pi * N / |δ|) * (((N:ℝ)+u)⁻¹ - ((((2*N-1:ℕ):ℝ)+u)⁻¹))
      = (4 * Real.pi * N / |δ|) * ((N:ℝ)+u)⁻¹ := by ring
  rw [hcomb]
  have hfin : (4 * Real.pi * N / |δ|) * ((N:ℝ)+u)⁻¹ ≤ 4 * Real.pi / |δ| := by
    have hNu : ((N:ℝ)+u)⁻¹ ≤ (N:ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith [hu0])
    have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    calc (4 * Real.pi * N / |δ|) * ((N:ℝ)+u)⁻¹
        ≤ (4 * Real.pi * N / |δ|) * (N:ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hNu; positivity
      _ = 4 * Real.pi / |δ| := by
          field_simp
  exact hfin

/-- The weighted exponential sum `Σ(u) = ∑_{n=N}^{2N−1} F(n+u)/(n+u)`. -/
def Sig (δ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2*N-1), Fw δ ((n:ℝ)+u) * ((((n:ℝ)+u)⁻¹ : ℝ) : ℂ)

/-- `|δ| · ‖Σ(u)‖ ≤ 4π` for all `u ∈ [0,1]`, `N ≥ 1`, `|δ| ≤ N`. -/
lemma abs_delta_mul_Sig_le {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδN : |δ| ≤ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |δ| * ‖Sig δ N u‖ ≤ 4 * Real.pi := by
  rcases eq_or_ne δ 0 with h0 | hδ0
  · rw [h0, abs_zero, zero_mul]; linarith [Real.pi_pos]
  · rcases eq_or_lt_of_le hN with h1 | h2
    · subst h1
      have hterm : Sig δ 1 u = Fw δ ((1:ℝ) + u) * ((((1:ℝ)+u)⁻¹ : ℝ) : ℂ) := by
        have h2' : (2*1-1 : ℕ) = 1 := by norm_num
        unfold Sig
        rw [h2', Finset.Icc_self, Finset.sum_singleton]
        norm_num
      have hd : |δ| ≤ 1 := by simpa using hδN
      have h1' : ((1:ℝ) + u)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by linarith)]
        linarith
      have hpos : (0:ℝ) ≤ ((1:ℝ)+u)⁻¹ := by positivity
      rw [hterm, norm_mul, norm_ofReal_complex, abs_of_nonneg hpos,
          norm_Fw (show (0:ℝ) < (1:ℝ) + u by linarith), one_mul]
      calc |δ| * ((1:ℝ) + u)⁻¹ ≤ 1 * 1 :=
            mul_le_mul hd h1' hpos (by norm_num)
        _ ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    · have hSig := Sigma_bound h2 hδ0 hδN u hu0 hu1
      have h2' : ‖Sig δ N u‖ * |δ| ≤ 4 * Real.pi := by
        rw [le_div_iff₀ (abs_pos.mpr hδ0)] at hSig; exact hSig
      rw [mul_comm]; exact h2'

/-- The main decomposition: sum minus integral equals a boundary term minus a
weighted integral of the exponential sum `Σ`. -/
lemma main_decomp (δ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc N (2*N), Fw δ (n:ℝ)) - (∫ x in (N:ℝ)..(2*(N:ℝ)), Fw δ x)
      = Fw δ ((2*N:ℕ):ℝ)
        - (Complex.I * (δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u := by
  have h2NR : 2*N = (2*N-1)+1 := by omega
  have hInt : (∫ x in (N:ℝ)..(2*(N:ℝ)), Fw δ x)
      = ∑ n ∈ Finset.Icc N (2*N-1), ∫ x in (n:ℝ)..((n:ℝ)+1), Fw δ x := by
    have hintg : ∀ k ∈ Set.Ico N (2*N),
        IntervalIntegrable (Fw δ) volume (((k:ℕ):ℝ)) ((((k+1):ℕ):ℝ)) := by
      intro k hk
      rw [Set.mem_Ico] at hk
      simpa [Nat.cast_add, Nat.cast_one] using intervalIntegrable_Fw δ (by omega)
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
      (a := fun k : ℕ => ((k:ℕ):ℝ)) (m := N) (n := 2*N) (f := Fw δ) (by omega) hintg
    have hIco : Finset.Ico N (2*N) = Finset.Icc N (2*N-1) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hIco] at h
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using h.symm
  rw [hInt]
  have hsplit : (∑ n ∈ Finset.Icc N (2*N), Fw δ (n:ℝ))
      = Fw δ ((2*N:ℕ):ℝ) + ∑ n ∈ Finset.Icc N (2*N-1), Fw δ (n:ℝ) := by
    rw [h2NR, Finset.sum_Icc_succ_top (by omega : N ≤ (2*N-1)+1)]
    push_cast
    ring
  rw [hsplit, add_sub_assoc, ← Finset.sum_sub_distrib]
  have hdiff : (∑ n ∈ Finset.Icc N (2*N-1), (Fw δ (n:ℝ) - ∫ x in (n:ℝ)..((n:ℝ)+1), Fw δ x))
      = - ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * (∑ n ∈ Finset.Icc N (2*N-1), FwD δ ((n:ℝ)+u)) := by
    have hterm : ∀ n ∈ Finset.Icc N (2*N-1),
        Fw δ (n:ℝ) - ∫ x in (n:ℝ)..((n:ℝ)+1), Fw δ x
          = - ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * FwD δ ((n:ℝ)+u) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := by omega
      have hi := inside_id δ n hn1
      have hsub : (∫ x in (n:ℝ)..((n:ℝ)+1), (Fw δ x - Fw δ n))
          = (∫ x in (n:ℝ)..((n:ℝ)+1), Fw δ x) - Fw δ (n:ℝ) := by
        rw [intervalIntegral.integral_sub (intervalIntegrable_Fw δ hn1) intervalIntegrable_const,
            intervalIntegral.integral_const]
        simp
      rw [hsub] at hi
      rw [← hi]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← intervalIntegral.integral_finsetSum]
    · congr 1
      apply intervalIntegral.integral_congr
      intro u _
      exact (Finset.mul_sum _ _ _).symm
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := by omega
      have hcont : ContinuousOn (fun u : ℝ => ((1-u:ℝ):ℂ) * FwD δ ((n:ℝ)+u)) (Set.Icc 0 1) := by
        refine ContinuousOn.mul ?_ ?_
        · exact ((Complex.continuous_ofReal.comp
            (continuous_const.sub continuous_id))).continuousOn
        · refine ContinuousOn.comp
            (continuousOn_FwD δ (a := (1:ℝ)) (b := ((n:ℝ)+1)) (by norm_num : (0:ℝ) < 1)) ?_ ?_
          · exact (continuous_const.add continuous_id).continuousOn
          · intro u hu
            simp only [Set.mem_Icc] at hu ⊢
            constructor
            · have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
              linarith [hu.1, hn1']
            · linarith [hu.2]
      exact hcont.intervalIntegrable_of_Icc (by norm_num)
  rw [hdiff]
  have hswap_pt : ∀ u : ℝ, (∑ n ∈ Finset.Icc N (2*N-1), FwD δ ((n:ℝ)+u))
      = (Complex.I*(δ:ℂ)) * Sig δ N u := by
    intro u
    rw [Sig, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [FwD, Complex.ofReal_inv]
    ring
  have hswap : (∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * (∑ n ∈ Finset.Icc N (2*N-1), FwD δ ((n:ℝ)+u)))
      = (Complex.I*(δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u := by
    rw [show (∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * (∑ n ∈ Finset.Icc N (2*N-1), FwD δ ((n:ℝ)+u)))
        = ∫ u in (0:ℝ)..1, (Complex.I*(δ:ℂ)) * (((1-u:ℝ):ℂ) * Sig δ N u) from
        intervalIntegral.integral_congr (fun u _ => by rw [hswap_pt u]; ring)]
    exact intervalIntegral.integral_const_mul _ _
  rw [hswap]
  ring

/-- Absolute bound `‖D‖ ≤ 1 + 4π`. -/
lemma main_bound (δ : ℝ) {N : ℕ} (hN : 1 ≤ N) (hδN : |δ| ≤ (N:ℝ)) :
    ‖(∑ n ∈ Finset.Icc N (2*N), Fw δ (n:ℝ)) - (∫ x in (N:ℝ)..(2*(N:ℝ)), Fw δ x)‖
      ≤ 1 + 4 * Real.pi := by
  have hFw : ‖Fw δ ((2*N:ℕ):ℝ)‖ = 1 := norm_Fw (by positivity)
  have hmain : ‖(Complex.I*(δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u‖
      ≤ 4 * Real.pi := by
    rcases eq_or_ne δ 0 with h0 | hδ0
    · subst h0
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
      linarith [Real.pi_pos]
    · have hbound : ∀ u ∈ Set.uIoc (0:ℝ) 1, ‖((1-u:ℝ):ℂ) * Sig δ N u‖ ≤ 4*Real.pi/|δ| := by
        intro u hu
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
        have hle1 : (0:ℝ) ≤ 1 - u := by linarith [hu.2]
        have hle2 : (1:ℝ) - u ≤ 1 := by linarith [hu.1]
        rw [norm_mul, norm_ofReal_complex, abs_of_nonneg hle1]
        have hS : ‖Sig δ N u‖ ≤ 4*Real.pi/|δ| := by
          have h := abs_delta_mul_Sig_le hN hδN (le_of_lt hu.1) hu.2
          rw [le_div_iff₀ (abs_pos.mpr hδ0), mul_comm ‖Sig δ N u‖ |δ|]
          exact h
        calc (1-u) * ‖Sig δ N u‖ ≤ 1 * (4*Real.pi/|δ|) :=
              mul_le_mul hle2 hS (norm_nonneg _) (by norm_num)
          _ = 4*Real.pi/|δ| := by ring
      have hInorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
      rw [sub_zero, abs_one, mul_one] at hInorm
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_ofReal_complex]
      have hkey : |δ| * (4*Real.pi/|δ|) = 4*Real.pi := by
        field_simp
      calc |δ| * ‖∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u‖
          ≤ |δ| * (4*Real.pi/|δ|) := mul_le_mul_of_nonneg_left hInorm (abs_nonneg δ)
        _ = 4*Real.pi := hkey
  rw [main_decomp δ hN]
  calc ‖Fw δ ((2*N:ℕ):ℝ) - (Complex.I*(δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u‖
      ≤ ‖Fw δ ((2*N:ℕ):ℝ)‖ +
          ‖(Complex.I*(δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u‖ := norm_sub_le _ _
    _ = 1 + ‖(Complex.I*(δ:ℂ)) * ∫ u in (0:ℝ)..1, ((1-u:ℝ):ℂ) * Sig δ N u‖ := by rw [hFw]
    _ ≤ 1 + 4 * Real.pi := by linarith [hmain]

/-- **Main theorem:** the sum and the integral of `n^{iδ}` over `[N, 2N]` differ
by a bounded amount. -/
theorem aliasing_exp_sum_small :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, |δ| ≤ (N : ℝ) →
      ‖(∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))) -
        (∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖ ≤
      C * (1 + |δ| / (N : ℝ)) := by
  refine ⟨16, by norm_num, ?_⟩
  intro N hN δ hδN
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (∑ n ∈ Finset.Icc N (2*N), (n:ℂ)^(Complex.I*(δ:ℂ)))
      = ∑ n ∈ Finset.Icc N (2*N), Fw δ (n:ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact (Fw_eq_cpow hn0).symm
  have hint : (∫ x in (N:ℝ)..(2*(N:ℝ)), (x:ℂ)^(Complex.I*(δ:ℂ)))
      = ∫ x in (N:ℝ)..(2*(N:ℝ)), Fw δ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le (by linarith : (N:ℝ) ≤ 2*(N:ℝ))] at hx
      linarith [hx.1, hN0]
    exact (Fw_eq_cpow hx0).symm
  rw [hsum, hint]
  have hbound := main_bound δ hN hδN
  have hpos : (0:ℝ) ≤ |δ| / (N:ℝ) := div_nonneg (abs_nonneg δ) hN0.le
  have hpi : (1:ℝ) + 4 * Real.pi ≤ 16 := by nlinarith [Real.pi_lt_d4]
  calc ‖(∑ n ∈ Finset.Icc N (2*N), Fw δ (n:ℝ)) - (∫ x in (N:ℝ)..(2*(N:ℝ)), Fw δ x)‖
      ≤ 1 + 4 * Real.pi := hbound
    _ ≤ 16 * (1 + |δ| / (N:ℝ)) := by nlinarith [hpos, hpi]

end

end Commons.NumberTheory.DirichletPolynomial
