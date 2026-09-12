import Submission.MarkovSHelper
import Submission.MarkovSValue
import Submission.MarkovSCos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.MarkovSBern

open MarkovSHelper
open MarkovSValue

/-- Trigonometric Bernstein inequality: degree-≤ n trig polynomial bounded by M has derivative
bounded by nM.  Derived from the strict value form by scaling with (1−ε)/M. -/
lemma trigBern {n : ℕ} (hn : 1 ≤ n) {a b : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ θ : ℝ, |TPoly n a b θ| ≤ M) (θ0 : ℝ) :
    |deriv (TPoly n a b) θ0| ≤ (n : ℝ) * M := by
  by_cases hM0 : M = 0
  · have hT : TPoly n a b = (fun _ : ℝ => 0) := by
      funext φ
      have h : |TPoly n a b φ| ≤ 0 := by simpa [hM0] using hbd φ
      have hz : |TPoly n a b φ| = 0 := le_antisymm h (abs_nonneg _)
      exact (abs_eq_zero.mp hz)
    rw [hT, hM0]
    simp
  · have hMpos : 0 < M := by exact lt_of_le_of_ne hM (Ne.symm hM0)
    let A : ℝ := |deriv (TPoly n a b) θ0|
    by_contra hgt
    have hnm : 0 ≤ (n : ℝ) * M := mul_nonneg (by positivity) hM
    have hnm' : (n : ℝ) * M < A := lt_of_not_ge hgt
    have hApos : 0 < A := lt_of_le_of_lt hnm hnm'
    have hnMpos : 0 < (n : ℝ) * M := by positivity
    let ε : ℝ := (A - (n : ℝ) * M) / (2 * A)
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    have hεlt : ε < 1 := by
      dsimp [ε]
      field_simp [ne_of_gt hApos]
      linarith
    let γ : ℝ := (1 - ε) / M
    have hγ : 0 < γ := by
      dsimp [γ]
      positivity
    have hstrict : ∀ θ : ℝ, |TPoly n (fun k => γ * a k) (fun k => γ * b k) θ| < 1 := by
      intro θ
      have hv := TPoly_smul n γ a b θ
      rw [hv]
      have habs : |γ * TPoly n a b θ| = γ * |TPoly n a b θ| := by
        rw [abs_mul, abs_of_pos hγ]
      rw [habs]
      have hle : γ * |TPoly n a b θ| ≤ γ * M := mul_le_mul_of_nonneg_left (hbd θ) (le_of_lt hγ)
      have hγM : γ * M = 1 - ε := by
        dsimp [γ]
        field_simp [hM0]
      rw [hγM] at hle
      exact lt_of_le_of_lt hle (by linarith)
    have hvf := strict_value_form hn (fun k => γ * a k) (fun k => γ * b k) hstrict θ0
    have hsin : (n : ℝ) * Real.sin (Real.arccos (TPoly n (fun k => γ * a k)
        (fun k => γ * b k) θ0)) ≤ (n : ℝ) := by
      have h01 : 0 ≤ (n : ℝ) := by positivity
      calc
        (n : ℝ) * Real.sin (Real.arccos (TPoly n (fun k => γ * a k) (fun k => γ * b k) θ0))
            ≤ (n : ℝ) * 1 := by
              exact mul_le_mul_of_nonneg_left (Real.sin_le_one _) h01
        _ = (n : ℝ) := by ring
    have hvf' : |deriv (TPoly n (fun k => γ * a k) (fun k => γ * b k)) θ0| ≤ (n : ℝ) :=
      le_trans hvf hsin
    have hpoint : TPoly n (fun k => γ * a k) (fun k => γ * b k) =
        (fun φ : ℝ => γ * TPoly n a b φ) := by
      funext φ
      exact TPoly_smul n γ a b φ
    have hder : deriv (TPoly n (fun k => γ * a k) (fun k => γ * b k)) θ0 =
        γ * deriv (TPoly n a b) θ0 := by
      rw [hpoint]
      exact deriv_const_mul γ (differentiable_TPoly n a b θ0)
    have hmain : γ * A ≤ (n : ℝ) := by
      rw [hder] at hvf'
      rw [abs_mul, abs_of_pos hγ] at hvf'
      simpa [A] using hvf'
    have hmul : (1 - ε) * A ≤ (n : ℝ) * M := by
      have hm : γ * A * M ≤ (n : ℝ) * M := mul_le_mul_of_nonneg_right hmain (le_of_lt hMpos)
      have hcancel : γ * A * M = (1 - ε) * A := by
        dsimp [γ]
        field_simp [hM0]
      rwa [hcancel] at hm
    have hcalc : (1 - ε) * A = (A + (n : ℝ) * M) / 2 := by
      dsimp [ε]
      field_simp [ne_of_gt hApos]
      ring
    rw [hcalc] at hmul
    linarith
/-! ## Algebraic Bernstein inequality for real polynomials -/

/-- chain rule: d/dθ P(cos θ) = -P'(cos θ)·sin θ -/
lemma deriv_poly_cos (P : Polynomial ℝ) (θ : ℝ) :
    deriv (fun x : ℝ => P.eval (Real.cos x)) θ =
      - (P.derivative.eval (Real.cos θ)) * Real.sin θ := by
  have hPol : ∀ y : ℝ, HasDerivAt (fun z : ℝ => P.eval z) (P.derivative.eval y) y :=
    Polynomial.hasDerivAt P
  have hc : HasDerivAt Real.cos (- Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hcomp := hPol (Real.cos θ) |>.comp θ hc
  exact hcomp.deriv.trans (by ring)

/-- Bernstein inequality in trigonometric form: |P'(cos θ)·sin θ| ≤ n·M for θ ∈ (0,π). -/
theorem bernstein_cos {P : Polynomial ℝ} {n : ℕ} (hdeg : P.natDegree ≤ n)
    {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |P.eval x| ≤ M)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 π) :
    |P.derivative.eval (Real.cos θ)| * Real.sin θ ≤ (n : ℝ) * M := by
  by_cases hn0 : n = 0
  · have hdeg0 : P.natDegree ≤ 0 := by simpa [hn0] using hdeg
    have hP : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg0
    have hder : P.derivative = 0 := by
      rw [hP]
      simp
    simp [hder, hn0]
  · have hn : 1 ≤ n := by omega
    obtain ⟨a, ha⟩ := MarkovSCos.poly_eval_cos_is_TPoly (n := n) P hdeg
    have hφbd : ∀ φ : ℝ, |TPoly n a (fun _ => 0) φ| ≤ M := by
      intro φ
      have he := ha φ
      rw [← he]
      exact hbd (Real.cos φ) (⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩)
    have htb := trigBern hn (a := a) (b := fun _ => 0) (M := M) hM hφbd θ
    have hφ : (fun x : ℝ => P.eval (Real.cos x)) = TPoly n a (fun _ => 0) := by
      funext φ
      exact ha φ
    have hder' : |deriv (fun x : ℝ => P.eval (Real.cos x)) θ| ≤ (n : ℝ) * M := by
      rw [hφ]
      exact htb
    have hd := deriv_poly_cos P θ
    rw [hd] at hder'
    have hsin : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_mem_Ioo hθ)
    have habs : |-(P.derivative.eval (Real.cos θ)) * Real.sin θ| =
        |P.derivative.eval (Real.cos θ)| * Real.sin θ := by
      calc
        |-(P.derivative.eval (Real.cos θ)) * Real.sin θ|
            = |-(P.derivative.eval (Real.cos θ))| * |Real.sin θ| := by rw [abs_mul]
        _ = |P.derivative.eval (Real.cos θ)| * Real.sin θ := by
              rw [abs_neg, abs_of_nonneg hsin]
    rwa [habs] at hder'


/-- 0 ≤ cos(π/(2n)) for n ≥ 1 -/
lemma pi_div_two_n_le_pi_div_two (n : ℕ) (hn : 1 ≤ n) : π / (2 * (n : ℝ)) ≤ π / 2 := by
  field_simp
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [Real.pi_pos]

lemma cos_pi_div_two_n_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Real.cos (π / (2 * (n : ℝ))) := by
  have h : π / (2 * (n : ℝ)) ≤ π / 2 := pi_div_two_n_le_pi_div_two n hn
  have h1 : 0 ≤ π / (2 * (n : ℝ)) := by positivity
  have hmem1 : π / (2 * (n : ℝ)) ∈ Set.Icc (0:ℝ) π := ⟨h1, le_trans h (by linarith [Real.pi_pos])⟩
  have hmem2 : π / 2 ∈ Set.Icc (0:ℝ) π := by constructor <;> linarith [Real.pi_pos]
  have hc := Real.antitoneOn_cos hmem1 hmem2 h
  simpa using hc

lemma cos_pi_div_two_n_lt_one (n : ℕ) (hn : 1 ≤ n) : Real.cos (π / (2 * (n : ℝ))) < 1 := by
  have hpos : 0 < π / (2 * (n : ℝ)) := by positivity
  have hltπ : π / (2 * (n : ℝ)) < π := by
    have h : π / (2 * (n : ℝ)) ≤ π / 2 := pi_div_two_n_le_pi_div_two n hn
    linarith [Real.pi_pos]
  have hm1 : (0:ℝ) ∈ Set.Icc (0:ℝ) π := by constructor <;> linarith [Real.pi_pos]
  have hm2 : π / (2 * (n : ℝ)) ∈ Set.Icc (0:ℝ) π := ⟨le_of_lt hpos, le_of_lt hltπ⟩
  have hc := Real.strictAntiOn_cos hm1 hm2 hpos
  simpa using hc

lemma sin_pi_div_two_mul_ge_inv (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ Real.sin (π / (2 * (n : ℝ))) := by
  have hx0 : 0 ≤ π / (2 * (n : ℝ)) := by positivity
  have hx1 : π / (2 * (n : ℝ)) ≤ π / 2 := pi_div_two_n_le_pi_div_two n hn
  have hm := Real.mul_le_sin hx0 hx1
  calc
    (1 : ℝ) / (n : ℝ) = (2 / π) * (π / (2 * (n : ℝ))) := by
      field_simp
    _ ≤ Real.sin (π / (2 * (n : ℝ))) := hm

lemma sq_le_sq_of_abs_le {x c : ℝ} (hc : 0 ≤ c) (h : |x| ≤ c) : x ^ 2 ≤ c ^ 2 := by
  exact (sq_le_sq.mpr (by rwa [abs_of_nonneg hc]))

lemma inv_n_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ (1 : ℝ) / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  exact div_nonneg (by norm_num) (le_of_lt hnpos)

lemma sin_pi_div_two_n_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Real.sin (π / (2 * (n : ℝ))) := by
  have harg1 : 0 < π / (2 * (n : ℝ)) := by positivity
  have harg2 : π / (2 * (n : ℝ)) < π := by
    have h : π / (2 * (n : ℝ)) ≤ π / 2 := pi_div_two_n_le_pi_div_two n hn
    linarith [Real.pi_pos]
  exact le_of_lt (Real.sin_pos_of_mem_Ioo ⟨harg1, harg2⟩)

/-- Bernstein inequality on the central region |x| ≤ cos(π/(2n)). -/
theorem bernstein_central {P : Polynomial ℝ} {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM : 0 ≤ M)
    (hdeg : P.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |P.eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hcentral : |x| ≤ Real.cos (π / (2 * (n : ℝ)))) :
    |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  let θ : ℝ := Real.arccos x
  have hc0 : 0 ≤ Real.cos (π / (2 * (n : ℝ))) := cos_pi_div_two_n_nonneg n hn
  have hc1 : Real.cos (π / (2 * (n : ℝ))) < 1 := cos_pi_div_two_n_lt_one n hn
  have hx1 : x < 1 := by
    have hx1a : x ≤ Real.cos (π / (2 * (n : ℝ))) := le_trans (le_abs_self x) hcentral
    linarith
  have hx0 : -1 < x := by
    have hx0a : -Real.cos (π / (2 * (n : ℝ))) ≤ x := by
      have h : -x ≤ |x| := by simpa [abs_neg] using (le_abs_self (-x) : -x ≤ |-(x:ℝ)|)
      have h2 : -x ≤ Real.cos (π / (2 * (n : ℝ))) := le_trans h hcentral
      linarith
    linarith
  have hθ : θ ∈ Set.Ioo 0 π := by
    dsimp [θ]
    exact ⟨(Real.arccos_pos (x := x)).mpr hx1, (Real.arccos_lt_pi (x := x)).mpr hx0⟩
  have hb := bernstein_cos hdeg hM hbd θ hθ
  have hc : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos (le_of_lt hx0) (le_of_lt hx1)
  have hsin : Real.sin θ = Real.sqrt (1 - x ^ 2) := by
    dsimp [θ]
    exact Real.sin_arccos x
  have hx2 : x ^ 2 ≤ 1 := by
    simpa using (sq_le_sq_of_abs_le (by norm_num : (0 : ℝ) ≤ 1) (abs_le.mpr hx))
  have hs0 : 0 ≤ 1 - x ^ 2 := by linarith
  have hsin_ge : (1 : ℝ) / (n : ℝ) ≤ Real.sin θ := by
    rw [hsin]
    rw [Real.le_sqrt (inv_n_nonneg n hn) hs0]
    have hc0sq : (Real.cos (π / (2 * (n : ℝ)))) ^ 2 = 1 - (Real.sin (π / (2 * (n : ℝ)))) ^ 2 := by
      have := Real.cos_sq_add_sin_sq (π / (2 * (n : ℝ)))
      nlinarith
    have hx2c : x ^ 2 ≤ (Real.cos (π / (2 * (n : ℝ)))) ^ 2 := sq_le_sq_of_abs_le hc0 hcentral
    have hs : ((1 : ℝ) / (n : ℝ)) ^ 2 ≤ (Real.sin (π / (2 * (n : ℝ)))) ^ 2 := by
      have hsp := sin_pi_div_two_mul_ge_inv n hn
      have h1n0 : 0 ≤ (1 : ℝ) / (n : ℝ) := inv_n_nonneg n hn
      have hs0' : 0 ≤ Real.sin (π / (2 * (n : ℝ))) := sin_pi_div_two_n_nonneg n hn
      exact sq_le_sq.mpr (by rwa [abs_of_nonneg h1n0, abs_of_nonneg hs0'])
    have hs2 : (Real.sin (π / (2 * (n : ℝ)))) ^ 2 ≤ 1 - x ^ 2 := by
      nlinarith [hc0sq, hx2c]
    exact le_trans hs hs2
  have hmain : |P.derivative.eval x| * Real.sin θ ≤ (n : ℝ) * M := by
    rw [← hc]
    simpa using hb
  have hsinpos : 0 < Real.sin θ := by
    have h1n : 0 < (1 : ℝ) / (n : ℝ) := by
      exact div_pos (by norm_num) (by exact_mod_cast hn)
    exact lt_of_lt_of_le h1n hsin_ge
  -- final: A·s ≤ b, s ≥ 1/n: A ≤ n²·M via multiplication chain
  let A : ℝ := |P.derivative.eval x|
  have h2 : 1 ≤ (n : ℝ) * Real.sin θ := by
    calc
      1 = (n : ℝ) * ((1 : ℝ) / (n : ℝ)) := by field_simp
      _ ≤ (n : ℝ) * Real.sin θ := mul_le_mul_of_nonneg_left hsin_ge (by positivity)
  have haA : 0 ≤ A := abs_nonneg _
  have hstep1 : A ≤ A * ((n : ℝ) * Real.sin θ) := by
    calc
      A = A * 1 := by rw [mul_one]
      _ ≤ A * ((n : ℝ) * Real.sin θ) := mul_le_mul_of_nonneg_left h2 haA
  have hstep2 : A * ((n : ℝ) * Real.sin θ) ≤ ((n : ℝ) * M) * (n : ℝ) := by
    calc
      A * ((n : ℝ) * Real.sin θ) = (A * Real.sin θ) * (n : ℝ) := by ring
      _ ≤ ((n : ℝ) * M) * (n : ℝ) := mul_le_mul_of_nonneg_right hmain (by positivity)
  have hstep3 : ((n : ℝ) * M) * (n : ℝ) = (n : ℝ) ^ 2 * M := by ring
  calc
    |P.derivative.eval x| = A := rfl
    _ ≤ A * ((n : ℝ) * Real.sin θ) := hstep1
    _ ≤ ((n : ℝ) * M) * (n : ℝ) := hstep2
    _ = (n : ℝ) ^ 2 * M := hstep3

end Submission.MarkovSBern
