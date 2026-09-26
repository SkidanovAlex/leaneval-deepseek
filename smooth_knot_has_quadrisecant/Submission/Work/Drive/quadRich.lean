import Mathlib
import Submission.Work.Drive.quadFamilyDefs

/-!
# Richness of the trigonometric family

The scalar perturbation family `Work.Drive.scFun` of degree `4` can realise *arbitrary* values of
the value, the first and the second derivative at any three pairwise distinct parameters.  This is
the "richness" of the family used to transfer the rank computations for the badness patches from
the data space to the coefficient space.

The proof is the classical Hermite-interpolation argument, transported through the substitution
`z = exp (I t)`: a scalar trigonometric sum of degree at most `4` corresponds to a complex
polynomial of degree at most `8` (via `z ↦ z^4 · f̂ z`), and the vanishing of the value, first and
second derivative at a point `t` is equivalent to a zero of order three of that polynomial at
`z = exp (I t)`.  Since the three points are distinct modulo `2π`, the corresponding `z` are
distinct, so the polynomial is divisible by `∏ⱼ (X - zⱼ)^3`, of degree `9 > 8`, hence vanishes;
the map from coefficients to jets is therefore injective, and since the source and target both
have dimension `9`, it is bijective — in particular surjective.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## Euler's formula and the powers of `zcirc t = exp (I t)` -/

/-- The parametrisation `t ↦ exp (I t)` of the unit circle. -/
def zcirc (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

@[simp] lemma zcirc_def (t : ℝ) : zcirc t = Complex.exp ((t : ℂ) * Complex.I) := rfl

lemma zcirc_ne_zero (t : ℝ) : zcirc t ≠ 0 := Complex.exp_ne_zero _

lemma zcirc_pow (t : ℝ) (k : Fin 4) :
    zcirc t ^ ((k : ℕ) + 1) = Complex.cos (((scFreq 4 k * t : ℝ)) : ℂ) +
      Complex.sin (((scFreq 4 k * t : ℝ)) : ℂ) * Complex.I := by
  rw [zcirc, ← Complex.exp_nat_mul]
  have harg : ((↑((k : ℕ) + 1) : ℂ) * ((t : ℂ) * Complex.I)) =
      (((scFreq 4 k * t : ℝ)) : ℂ) * Complex.I := by
    simp only [scFreq]
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]

lemma zcirc_pow_inv (t : ℝ) (k : Fin 4) :
    (zcirc t ^ ((k : ℕ) + 1))⁻¹ = Complex.cos (((scFreq 4 k * t : ℝ)) : ℂ) -
      Complex.sin (((scFreq 4 k * t : ℝ)) : ℂ) * Complex.I := by
  have hpow : zcirc t ^ ((k : ℕ) + 1) =
      Complex.exp ((((scFreq 4 k * t : ℝ)) : ℂ) * Complex.I) := by
    rw [zcirc, ← Complex.exp_nat_mul]
    congr 1
    simp only [scFreq]
    push_cast
    ring
  rw [hpow, ← Complex.exp_neg]
  have hneg : -((((scFreq 4 k * t : ℝ)) : ℂ) * Complex.I) =
      (((-(scFreq 4 k * t) : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hneg, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  ring

lemma zcirc_pow_add_inv (t : ℝ) (k : Fin 4) :
    zcirc t ^ ((k : ℕ) + 1) + (zcirc t ^ ((k : ℕ) + 1))⁻¹ =
      2 * Complex.cos (((scFreq 4 k * t : ℝ)) : ℂ) := by
  rw [zcirc_pow_inv, zcirc_pow]
  ring

lemma zcirc_pow_sub_inv (t : ℝ) (k : Fin 4) :
    zcirc t ^ ((k : ℕ) + 1) - (zcirc t ^ ((k : ℕ) + 1))⁻¹ =
      2 * Complex.I * Complex.sin (((scFreq 4 k * t : ℝ)) : ℂ) := by
  rw [zcirc_pow_inv, zcirc_pow]
  ring_nf

/-! ## The associated complex polynomial -/

/-- The complex polynomial associated with a scalar trigonometric sum of degree at most `4`:
`c = a₀ + Σ_{k=1}^{4} (a_k cos (k t) + b_k sin (k t))` corresponds to

    a₀ X⁴ + Σ_{k=1}^{4} [ (a_k - i b_k)/2 · X^{4+k} + (a_k + i b_k)/2 · X^{4-k} ] ,

so that `a₀ + Σ_k (a_k cos kt + b_k sin kt) = (exp (-4 i t)) · P (exp (i t))`. -/
def scPoly (c : ScCoeff 4) : Polynomial ℂ :=
  Polynomial.C ((c none : ℝ) : ℂ) * Polynomial.X ^ 4 +
    ∑ k : Fin 4,
      (Polynomial.C ((((c (some (k, false)) : ℝ) : ℂ) -
            Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) *
          Polynomial.X ^ (4 + ((k : ℕ) + 1)) +
        Polynomial.C ((((c (some (k, false)) : ℝ) : ℂ) +
            Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) *
          Polynomial.X ^ (4 - ((k : ℕ) + 1)))

lemma eval_scPoly (c : ScCoeff 4) (z : ℂ) :
    (scPoly c).eval z = ((c none : ℝ) : ℂ) * z ^ 4 +
      ∑ k : Fin 4,
        (((((c (some (k, false)) : ℝ) : ℂ) - Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) *
              z ^ (4 + ((k : ℕ) + 1)) +
          ((((c (some (k, false)) : ℝ) : ℂ) + Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) *
              z ^ (4 - ((k : ℕ) + 1))) := by
  simp only [scPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]

/-! ## The polynomial identity -/

/-- The per-frequency identity expressing `a cos (k t) + b sin (k t)` through the powers of
`zcirc t`. -/
lemma term_identity (t : ℝ) (k : Fin 4) (a b : ℝ) :
    ((a : ℂ) * (((Real.cos (scFreq 4 k * t) : ℝ)) : ℂ) +
        (b : ℂ) * (((Real.sin (scFreq 4 k * t) : ℝ)) : ℂ)) * zcirc t ^ 4 =
      ((a : ℂ) - Complex.I * (b : ℂ)) / 2 * zcirc t ^ (4 + ((k : ℕ) + 1)) +
        ((a : ℂ) + Complex.I * (b : ℂ)) / 2 * zcirc t ^ (4 - ((k : ℕ) + 1)) := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  have hbr : ((a : ℂ) - Complex.I * (b : ℂ)) / 2 * zcirc t ^ ((k : ℕ) + 1) +
      ((a : ℂ) + Complex.I * (b : ℂ)) / 2 * (zcirc t ^ ((k : ℕ) + 1))⁻¹ =
      (a : ℂ) * Complex.cos (((scFreq 4 k * t : ℝ)) : ℂ) +
        (b : ℂ) * Complex.sin (((scFreq 4 k * t : ℝ)) : ℂ) := by
    rw [zcirc_pow_inv, zcirc_pow]
    ring_nf
    simp only [pow_two, Complex.I_mul_I]
    ring
  have hzpow : zcirc t ^ (4 - ((k : ℕ) + 1)) =
      (zcirc t ^ ((k : ℕ) + 1))⁻¹ * zcirc t ^ 4 := by
    have hk : ((k : ℕ) + 1) ≤ 4 := Nat.succ_le_of_lt k.isLt
    have h : zcirc t ^ ((k : ℕ) + 1) * zcirc t ^ (4 - ((k : ℕ) + 1)) = zcirc t ^ 4 := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
    calc zcirc t ^ (4 - ((k : ℕ) + 1))
        = (zcirc t ^ ((k : ℕ) + 1))⁻¹ *
            (zcirc t ^ ((k : ℕ) + 1) * zcirc t ^ (4 - ((k : ℕ) + 1))) := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (zcirc_ne_zero t)), one_mul]
      _ = (zcirc t ^ ((k : ℕ) + 1))⁻¹ * zcirc t ^ 4 := by rw [h]
  rw [pow_add, hzpow,
    show ((a : ℂ) - Complex.I * (b : ℂ)) / 2 *
          (zcirc t ^ 4 * zcirc t ^ ((k : ℕ) + 1)) +
        ((a : ℂ) + Complex.I * (b : ℂ)) / 2 *
          ((zcirc t ^ ((k : ℕ) + 1))⁻¹ * zcirc t ^ 4)
      = zcirc t ^ 4 *
        (((a : ℂ) - Complex.I * (b : ℂ)) / 2 * zcirc t ^ ((k : ℕ) + 1) +
          ((a : ℂ) + Complex.I * (b : ℂ)) / 2 * (zcirc t ^ ((k : ℕ) + 1))⁻¹) by ring,
    hbr]
  ring

/-- The coercion of `scFun` to `ℂ`, with the sum distributed over the basis terms. -/
lemma scFun_cast (c : ScCoeff 4) (t : ℝ) :
    (scFun 4 c t : ℂ) = (c none : ℂ) + ∑ k : Fin 4,
      ((((c (some (k, false)) : ℝ)) : ℂ) * (((Real.cos (scFreq 4 k * t) : ℝ)) : ℂ) +
        (((c (some (k, true)) : ℝ)) : ℂ) * (((Real.sin (scFreq 4 k * t) : ℝ)) : ℂ)) := by
  rw [scFun_expand]
  push_cast
  ring

/-- **The polynomial identity**: evaluating the associated polynomial at `zcirc t` recovers
the trigonometric sum multiplied by `zcirc t ^ 4`. -/
lemma scFun_mul_pow (c : ScCoeff 4) (t : ℝ) :
    (scFun 4 c t : ℂ) * zcirc t ^ 4 = (scPoly c).eval (zcirc t) := by
  rw [eval_scPoly, scFun_cast]
  rw [add_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun k _ => term_identity t k _ _)]


/-! ## The vanishing order transfer -/

/-- The complexification of `scFun`. -/
def scFunC (c : ScCoeff 4) (t : ℝ) : ℂ := (scFun 4 c t : ℂ)

@[simp] lemma scFunC_apply (c : ScCoeff 4) (t : ℝ) : scFunC c t = (scFun 4 c t : ℂ) := rfl

lemma scFunC_eq (c : ScCoeff 4) (t : ℝ) :
    scFunC c t = (zcirc t ^ 4)⁻¹ * (scPoly c).eval (zcirc t) := by
  rw [scFunC_apply, ← scFun_mul_pow c t]
  field_simp

lemma hasDerivAt_zcirc (t : ℝ) : HasDerivAt zcirc (Complex.I * zcirc t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t :=
    h1.mul_const Complex.I
  have h3 := (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h2
  exact h3.congr_deriv (by rw [zcirc]; ring)

lemma differentiableAt_zcirc (t : ℝ) : DifferentiableAt ℝ zcirc t :=
  (hasDerivAt_zcirc t).differentiableAt

lemma differentiableAt_eval_real (p : Polynomial ℂ) (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => p.eval w) z :=
  ((Polynomial.hasDerivAt p z).differentiableAt).restrictScalars ℝ

/-- `A t = (zcirc t ^ 4)⁻¹` has derivative `-4 i A`. -/
lemma hasDerivAt_A (t : ℝ) :
    HasDerivAt (fun s : ℝ => (zcirc s ^ 4)⁻¹) (-(4 : ℂ) * Complex.I * (zcirc t ^ 4)⁻¹) t := by
  have hz := hasDerivAt_zcirc t
  have hz0 : zcirc t ≠ 0 := zcirc_ne_zero t
  have hw0 : zcirc t ^ 4 ≠ 0 := pow_ne_zero _ hz0
  have hw : HasDerivAt (fun s : ℝ => zcirc s ^ 4)
      (4 * zcirc t ^ 3 * (Complex.I * zcirc t)) t := hz.pow 4
  have hderiv : -(4 * zcirc t ^ 3 * (Complex.I * zcirc t)) / (zcirc t ^ 4) ^ 2 =
      -(4 : ℂ) * Complex.I * (zcirc t ^ 4)⁻¹ := by
    field_simp <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  have h := hw.inv hw0
  rw [show (fun s : ℝ => zcirc s ^ 4)⁻¹ = (fun s : ℝ => (zcirc s ^ 4)⁻¹) from rfl] at h
  exact h.congr_deriv hderiv

/-- `A'' = -16 A`. -/
lemma hasDerivAt_A2 (t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (fun u : ℝ => (zcirc u ^ 4)⁻¹) s)
      (-(16 : ℂ) * (zcirc t ^ 4)⁻¹) t := by
  have h1 : (fun s : ℝ => deriv (fun u : ℝ => (zcirc u ^ 4)⁻¹) s) =
      fun s : ℝ => -(4 : ℂ) * Complex.I * (zcirc s ^ 4)⁻¹ := by
    funext s; exact (hasDerivAt_A s).deriv
  rw [h1]
  refine (((hasDerivAt_const t (-(4 : ℂ) * Complex.I)).mul (hasDerivAt_A t)).congr_deriv ?_)
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `B t = P (zcirc t)`. -/
lemma hasDerivAt_B (c : ScCoeff 4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (scPoly c).eval (zcirc s))
      ((scPoly c).derivative.eval (zcirc t) * (Complex.I * zcirc t)) t := by
  have h := (Polynomial.hasDerivAt (scPoly c) (zcirc t)).comp t (hasDerivAt_zcirc t)
  rw [show ((fun z : ℂ => (scPoly c).eval z) ∘ zcirc) =
      (fun s : ℝ => (scPoly c).eval (zcirc s)) from rfl] at h
  exact h

/-- `B' t = P' (zcirc t)`. -/
lemma hasDerivAt_B' (c : ScCoeff 4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (scPoly c).derivative.eval (zcirc s))
      ((scPoly c).derivative.derivative.eval (zcirc t) * (Complex.I * zcirc t)) t := by
  have h := (Polynomial.hasDerivAt ((scPoly c).derivative) (zcirc t)).comp t (hasDerivAt_zcirc t)
  rw [show ((fun z : ℂ => (scPoly c).derivative.eval z) ∘ zcirc) =
      (fun s : ℝ => (scPoly c).derivative.eval (zcirc s)) from rfl] at h
  exact h

lemma hasDerivAt_zI (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.I * zcirc s) (Complex.I * (Complex.I * zcirc t)) t := by
  have h := (hasDerivAt_const t Complex.I).mul (hasDerivAt_zcirc t)
  rw [show ((fun _ : ℝ => Complex.I) * zcirc) = (fun s : ℝ => Complex.I * zcirc s) from rfl] at h
  exact h.congr_deriv (by ring)

/-- The bracket `t ↦ -4 i P (z) + i z P' (z)`. -/
lemma hasDerivAt_U (c : ScCoeff 4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s) +
        Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s))
      (-(4 : ℂ) * Complex.I *
          ((scPoly c).derivative.eval (zcirc t) * (Complex.I * zcirc t)) +
        (Complex.I * (Complex.I * zcirc t) * (scPoly c).derivative.eval (zcirc t) +
          Complex.I * zcirc t *
            ((scPoly c).derivative.derivative.eval (zcirc t) * (Complex.I * zcirc t)))) t := by
  have hA : HasDerivAt (fun s : ℝ => -(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s))
      (-(4 : ℂ) * Complex.I *
        ((scPoly c).derivative.eval (zcirc t) * (Complex.I * zcirc t))) t := by
    have h := (hasDerivAt_const t (-(4 : ℂ) * Complex.I)).mul (hasDerivAt_B c t)
    rw [show ((fun _ : ℝ => -(4 : ℂ) * Complex.I) * fun s : ℝ => (scPoly c).eval (zcirc s)) =
        (fun s : ℝ => -(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s)) from by
          funext s; simp [Pi.mul_apply]] at h
    exact h.congr_deriv (by ring)
  have hB : HasDerivAt (fun s : ℝ => Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s))
      (Complex.I * (Complex.I * zcirc t) * (scPoly c).derivative.eval (zcirc t) +
        Complex.I * zcirc t *
          ((scPoly c).derivative.derivative.eval (zcirc t) * (Complex.I * zcirc t))) t := by
    have h := (hasDerivAt_zI t).mul (hasDerivAt_B' c t)
    rw [show ((fun s : ℝ => Complex.I * zcirc s) *
        fun s : ℝ => (scPoly c).derivative.eval (zcirc s)) =
        (fun s : ℝ => Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s)) from by
          funext s; simp [Pi.mul_apply]] at h
    exact h.congr_deriv (by ring)
  have h := hA.add hB
  rw [show ((fun s : ℝ => -(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s)) +
      fun s : ℝ => Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s)) =
      (fun s : ℝ => -(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s) +
        Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s)) from by
        funext s; simp [Pi.add_apply]] at h
  exact h

/-- The derivative of `t ↦ (zcirc t ^ 4)⁻¹ * P (zcirc t)`. -/
lemma deriv_wP (c : ScCoeff 4) :
    deriv (fun t : ℝ => (zcirc t ^ 4)⁻¹ * (scPoly c).eval (zcirc t)) =
      fun t : ℝ => (zcirc t ^ 4)⁻¹ *
        (-(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc t) +
          Complex.I * zcirc t * (scPoly c).derivative.eval (zcirc t)) := by
  funext t
  have h := (hasDerivAt_A t).mul (hasDerivAt_B c t)
  rw [show ((fun s : ℝ => (zcirc s ^ 4)⁻¹) * fun s : ℝ => (scPoly c).eval (zcirc s)) =
      (fun t : ℝ => (zcirc t ^ 4)⁻¹ * (scPoly c).eval (zcirc t)) from by
        funext s; simp [Pi.mul_apply]] at h
  rw [h.deriv]
  ring

/-- The second derivative of `t ↦ (zcirc t ^ 4)⁻¹ * P (zcirc t)`. -/
lemma deriv2_wP (c : ScCoeff 4) :
    deriv (deriv (fun t : ℝ => (zcirc t ^ 4)⁻¹ * (scPoly c).eval (zcirc t))) =
      fun t : ℝ => (zcirc t ^ 4)⁻¹ *
        (-(16 : ℂ) * (scPoly c).eval (zcirc t) +
          7 * zcirc t * (scPoly c).derivative.eval (zcirc t) -
          zcirc t ^ 2 * (scPoly c).derivative.derivative.eval (zcirc t)) := by
  rw [deriv_wP]
  funext t
  have h := (hasDerivAt_A t).mul (hasDerivAt_U c t)
  rw [show ((fun s : ℝ => (zcirc s ^ 4)⁻¹) * fun s : ℝ =>
        (-(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc s) +
          Complex.I * zcirc s * (scPoly c).derivative.eval (zcirc s))) =
      (fun t : ℝ => (zcirc t ^ 4)⁻¹ *
        (-(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc t) +
          Complex.I * zcirc t * (scPoly c).derivative.eval (zcirc t))) from by
        funext s; simp [Pi.mul_apply]] at h
  rw [h.deriv]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **The vanishing-order transfer**: if the value, first and second derivative of the scalar
trigonometric sum vanish at `t`, then the associated polynomial has a zero of order three at
`zcirc t`. -/
lemma scPoly_deriv_zero {c : ScCoeff 4} {t : ℝ}
    (h0 : scFun 4 c t = 0) (h1 : scFunD 4 c t = 0) (h2 : scFunD2 4 c t = 0) :
    (scPoly c).eval (zcirc t) = 0 ∧ (scPoly c).derivative.eval (zcirc t) = 0 ∧
      (scPoly c).derivative.derivative.eval (zcirc t) = 0 := by
  have hz0 : zcirc t ≠ 0 := zcirc_ne_zero t
  have hw : zcirc t ^ 4 ≠ 0 := pow_ne_zero _ hz0
  have hF : (fun s : ℝ => (zcirc s ^ 4)⁻¹ * (scPoly c).eval (zcirc s)) = scFunC c := by
    funext s
    exact (scFunC_eq c s).symm
  have hd1 : deriv (fun u : ℝ => scFunC c u) = fun s : ℝ => ((scFunD 4 c s : ℝ) : ℂ) := by
    funext s
    exact ((hasDerivAt_scFun 4 c s).ofReal_comp).deriv
  have hF0 : (zcirc t ^ 4)⁻¹ * (scPoly c).eval (zcirc t) = 0 := by
    have := congrFun hF t
    rw [this, scFunC_apply, h0]
    simp
  have hF1 : deriv (fun s : ℝ => (zcirc s ^ 4)⁻¹ * (scPoly c).eval (zcirc s)) t = 0 := by
    rw [hF]
    show deriv (fun u : ℝ => ((scFun 4 c u : ℝ) : ℂ)) t = 0
    rw [((hasDerivAt_scFun 4 c t).ofReal_comp).deriv]
    exact_mod_cast h1
  have hF2 : deriv (deriv (fun s : ℝ => (zcirc s ^ 4)⁻¹ * (scPoly c).eval (zcirc s))) t = 0 := by
    rw [hF, hd1]
    show deriv (fun u : ℝ => ((scFunD 4 c u : ℝ) : ℂ)) t = 0
    rw [((hasDerivAt_scFunD 4 c t).ofReal_comp).deriv]
    exact_mod_cast h2
  have hp0 : (scPoly c).eval (zcirc t) = 0 := by
    rcases mul_eq_zero.mp hF0 with h | h
    · exact absurd h (inv_ne_zero hw)
    · exact h
  have hp1 : (scPoly c).derivative.eval (zcirc t) = 0 := by
    have h := hF1
    rw [deriv_wP] at h
    have hm : (zcirc t ^ 4)⁻¹ * (-(4 : ℂ) * Complex.I * (scPoly c).eval (zcirc t) +
        Complex.I * zcirc t * (scPoly c).derivative.eval (zcirc t)) = 0 := h
    rcases mul_eq_zero.mp hm with h3 | h3
    · exact absurd h3 (inv_ne_zero hw)
    · rw [hp0] at h3
      have h4 : Complex.I * zcirc t * (scPoly c).derivative.eval (zcirc t) = 0 := by
        simpa using h3
      rcases mul_eq_zero.mp h4 with h5 | h5
      · rcases mul_eq_zero.mp h5 with h6 | h6
        · exact absurd h6 Complex.I_ne_zero
        · exact absurd h6 hz0
      · exact h5
  have hp2 : (scPoly c).derivative.derivative.eval (zcirc t) = 0 := by
    have h := hF2
    rw [deriv2_wP] at h
    have hm : (zcirc t ^ 4)⁻¹ * (-(16 : ℂ) * (scPoly c).eval (zcirc t) +
        7 * zcirc t * (scPoly c).derivative.eval (zcirc t) -
        zcirc t ^ 2 * (scPoly c).derivative.derivative.eval (zcirc t)) = 0 := h
    rcases mul_eq_zero.mp hm with h3 | h3
    · exact absurd h3 (inv_ne_zero hw)
    · rw [hp0, hp1] at h3
      have h4 : -(zcirc t ^ 2 * (scPoly c).derivative.derivative.eval (zcirc t)) = 0 := by
        simpa using h3
      have h5 : zcirc t ^ 2 * (scPoly c).derivative.derivative.eval (zcirc t) = 0 := by
        simpa using h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 (pow_ne_zero 2 hz0)
      · exact h6
  exact ⟨hp0, hp1, hp2⟩


/-! ## Divisibility at a triple zero -/

/-- If `(X - z)` divides `P`, the derivative of `P` at `z` is the value of the quotient at
`z`. -/
lemma eval_derivative_of_factor {P Q : Polynomial ℂ} {z : ℂ}
    (h : P = (Polynomial.X - Polynomial.C z) * Q) : P.derivative.eval z = Q.eval z := by
  rw [h, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, sub_zero, one_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  ring

/-- If `(X - z)` divides `P`, the second derivative of `P` at `z` is twice the derivative of
the quotient at `z`. -/
lemma deriv2_eval_of_factor {P Q : Polynomial ℂ} {z : ℂ}
    (h : P = (Polynomial.X - Polynomial.C z) * Q) :
    P.derivative.derivative.eval z = 2 * Q.derivative.eval z := by
  have h1 : P.derivative = Q + (Polynomial.X - Polynomial.C z) * Q.derivative := by
    rw [h, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul]
  rw [h1, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  ring

/-- **A triple zero is a cubic factor.**  If a complex polynomial and its first two derivatives
vanish at `z`, then `(X - z)^3` divides it. -/
theorem dvd_cube_of_deriv_zero (P : Polynomial ℂ) (z : ℂ)
    (h0 : P.eval z = 0) (h1 : P.derivative.eval z = 0)
    (h2 : P.derivative.derivative.eval z = 0) :
    (Polynomial.X - Polynomial.C z) ^ 3 ∣ P := by
  obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr h0
  have hQ0 : Q.eval z = 0 := by rw [← eval_derivative_of_factor hQ]; exact h1
  obtain ⟨S, hS⟩ := Polynomial.dvd_iff_isRoot.mpr hQ0
  have hQd : Q.derivative.eval z = 0 := by
    rw [deriv2_eval_of_factor hQ] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hS0 : S.eval z = 0 := by rw [← eval_derivative_of_factor hS]; exact hQd
  obtain ⟨T, hT⟩ := Polynomial.dvd_iff_isRoot.mpr hS0
  exact ⟨T, by rw [hQ, hS, hT]; ring⟩

/-! ## The coefficients of the associated polynomial -/

lemma coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (N : ℕ) :
    (s.sum f).coeff N = s.sum (fun i => (f i).coeff N) := by
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp

/-- The coefficients of `scPoly c` in closed form. -/
lemma coeff_scPoly (c : ScCoeff 4) (N : ℕ) :
    (scPoly c).coeff N = (if N = 4 then ((c none : ℝ) : ℂ) else 0) +
      ∑ k : Fin 4,
        ((if N = 4 + ((k : ℕ) + 1) then
            ((((c (some (k, false)) : ℝ) : ℂ) -
              Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) else 0) +
         (if N = 4 - ((k : ℕ) + 1) then
            ((((c (some (k, false)) : ℝ) : ℂ) +
              Complex.I * ((c (some (k, true)) : ℝ) : ℂ)) / 2) else 0)) := by
  rw [scPoly, Polynomial.coeff_add, coeff_finset_sum]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]

/-- The upper-half coefficient attached to the frequency `m + 1`. -/
def scCoeffHi (c : ScCoeff 4) (m : Fin 4) : ℂ :=
  ((((c (some (m, false)) : ℝ) : ℂ) - Complex.I * ((c (some (m, true)) : ℝ) : ℂ)) / 2)

/-- The lower-half coefficient attached to the frequency `m + 1`. -/
def scCoeffLo (c : ScCoeff 4) (m : Fin 4) : ℂ :=
  ((((c (some (m, false)) : ℝ) : ℂ) + Complex.I * ((c (some (m, true)) : ℝ) : ℂ)) / 2)

lemma coeff_scPoly_four (c : ScCoeff 4) : (scPoly c).coeff 4 = ((c none : ℝ) : ℂ) := by
  rw [coeff_scPoly, if_pos rfl, add_eq_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : (k : ℕ) < 4 := k.isLt
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

lemma coeff_scPoly_hi (c : ScCoeff 4) (m : Fin 4) :
    (scPoly c).coeff (4 + ((m : ℕ) + 1)) = scCoeffHi c m := by
  rw [coeff_scPoly, if_neg (by omega)]
  rw [zero_add, Finset.sum_eq_single m]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
    rfl
  · intro b _ hbm
    have hb : (b : ℕ) ≠ (m : ℕ) := fun h => hbm (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega)]
    norm_num
  · intro hm; exact absurd (Finset.mem_univ m) hm

lemma coeff_scPoly_lo (c : ScCoeff 4) (m : Fin 4) :
    (scPoly c).coeff (4 - ((m : ℕ) + 1)) = scCoeffLo c m := by
  rw [coeff_scPoly, if_neg (by omega)]
  rw [zero_add, Finset.sum_eq_single m]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
    rfl
  · intro b _ hbm
    have hb : (b : ℕ) ≠ (m : ℕ) := fun h => hbm (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega)]
    norm_num
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-- The associated polynomial of degree-four trigonometric data has degree at most eight. -/
lemma natDegree_scPoly_le (c : ScCoeff 4) : (scPoly c).natDegree ≤ 8 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_scPoly, if_neg (by omega : ¬ (N = 4)), zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : (k : ℕ) < 4 := k.isLt
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

/-- **The vanishing-order transfer for three distinct parameters.**  If the value, the first and
the second derivative of `scFun 4 c` vanish at three parameters with distinct `zcirc`-images,
then the associated polynomial is zero. -/
lemma scPoly_eq_zero_of_jets {c : ScCoeff 4} {t : Fin 3 → ℝ}
    (ht : Function.Injective (fun i : Fin 3 => zcirc (t i)))
    (h0 : ∀ i, scFun 4 c (t i) = 0) (h1 : ∀ i, scFunD 4 c (t i) = 0)
    (h2 : ∀ i, scFunD2 4 c (t i) = 0) : scPoly c = 0 := by
  by_contra hP
  have hdvd : ∀ i : Fin 3,
      (Polynomial.X - Polynomial.C (zcirc (t i))) ^ 3 ∣ scPoly c := fun i =>
    dvd_cube_of_deriv_zero _ _ (scPoly_deriv_zero (h0 i) (h1 i) (h2 i)).1
      (scPoly_deriv_zero (h0 i) (h1 i) (h2 i)).2.1
      (scPoly_deriv_zero (h0 i) (h1 i) (h2 i)).2.2
  have hcop : Pairwise (fun i j : Fin 3 =>
      IsCoprime ((Polynomial.X - Polynomial.C (zcirc (t i))) ^ 3)
        ((Polynomial.X - Polynomial.C (zcirc (t j))) ^ 3)) :=
    fun i j hij => (Polynomial.pairwise_coprime_X_sub_C ht hij).pow (m := 3) (n := 3)
  have h01 : ((Polynomial.X - Polynomial.C (zcirc (t 0))) ^ 3 *
      (Polynomial.X - Polynomial.C (zcirc (t 1))) ^ 3) ∣ scPoly c :=
    (hcop (by decide)).mul_dvd (hdvd 0) (hdvd 1)
  have h012 : ((Polynomial.X - Polynomial.C (zcirc (t 0))) ^ 3 *
      (Polynomial.X - Polynomial.C (zcirc (t 1))) ^ 3 *
      (Polynomial.X - Polynomial.C (zcirc (t 2))) ^ 3) ∣ scPoly c :=
    ((hcop (by decide : (0 : Fin 3) ≠ 2)).mul_left (hcop (by decide : (1 : Fin 3) ≠ 2))).mul_dvd
      h01 (hdvd 2)
  have hA : (Polynomial.X - Polynomial.C (zcirc (t 0))) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hB : (Polynomial.X - Polynomial.C (zcirc (t 1))) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hC : (Polynomial.X - Polynomial.C (zcirc (t 2))) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hdeg : ((Polynomial.X - Polynomial.C (zcirc (t 0))) ^ 3 *
      (Polynomial.X - Polynomial.C (zcirc (t 1))) ^ 3 *
      (Polynomial.X - Polynomial.C (zcirc (t 2))) ^ 3).natDegree = 9 := by
    rw [Polynomial.natDegree_mul (mul_ne_zero hA hB) hC,
      Polynomial.natDegree_mul hA hB, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    norm_num
  have h9 : 9 ≤ (scPoly c).natDegree := by
    rw [← hdeg]
    exact Polynomial.natDegree_le_of_dvd h012 hP
  have h8 := natDegree_scPoly_le c
  omega

/-- **The associated polynomial determines the coefficient vector.** -/
lemma scPoly_eq_zero_iff (c : ScCoeff 4) : scPoly c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h4 : (c none : ℝ) = 0 := by
      have hh := coeff_scPoly_four c
      rw [h, Polynomial.coeff_zero] at hh
      exact Complex.ofReal_eq_zero.mp hh.symm
    have hhl : ∀ m : Fin 4,
        (c (some (m, false)) : ℝ) = 0 ∧ (c (some (m, true)) : ℝ) = 0 := by
      intro m
      have hi := coeff_scPoly_hi c m
      have hl := coeff_scPoly_lo c m
      rw [h, Polynomial.coeff_zero] at hi hl
      simp only [scCoeffHi] at hi
      simp only [scCoeffLo] at hl
      have hi' : (((c (some (m, false)) : ℝ) : ℂ) -
          Complex.I * ((c (some (m, true)) : ℝ) : ℂ)) = 0 := by
        rcases div_eq_zero_iff.mp hi.symm with h' | h'
        · exact h'
        · exact absurd h' (by norm_num)
      have hl' : (((c (some (m, false)) : ℝ) : ℂ) +
          Complex.I * ((c (some (m, true)) : ℝ) : ℂ)) = 0 := by
        rcases div_eq_zero_iff.mp hl.symm with h' | h'
        · exact h'
        · exact absurd h' (by norm_num)
      constructor
      · have hre := congrArg Complex.re hi'
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.zero_re, mul_zero, zero_mul, sub_zero] at hre
        exact hre
      · have him := congrArg Complex.im hl'
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.zero_im, mul_zero, one_mul, zero_add,
          add_zero] at him
        exact him
    ext n
    rcases n with _ | ⟨m, b⟩
    · exact h4
    · cases b
      · exact (hhl m).1
      · exact (hhl m).2
  · intro h
    rw [h]
    simp [scPoly]

/-! ## The jet map and its surjectivity -/

/-- The `ℝ`-linear jet map `c ↦ (value, first derivative, second derivative)` at three
parameters. -/
def scJet (t : Fin 3 → ℝ) :
    ScCoeff 4 →ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) where
  toFun c := (fun i => scFun 4 c (t i), fun i => scFunD 4 c (t i),
    fun i => scFunD2 4 c (t i))
  map_add' c c' := by
    ext i <;> simp [scFun_add, scFunD_add, scFunD2_add]
  map_smul' r c := by
    ext i <;> simp [scFun_smul, scFunD_smul, scFunD2_smul]

@[simp] lemma scJet_apply (t : Fin 3 → ℝ) (c : ScCoeff 4) :
    scJet t c = (fun i => scFun 4 c (t i), fun i => scFunD 4 c (t i),
      fun i => scFunD2 4 c (t i)) := rfl

/-- **Injectivity of the jet map**: the jets of the value, the first and the second derivative at
three parameters with distinct `zcirc`-images determine the coefficient vector. -/
lemma scJet_injective {t : Fin 3 → ℝ} (ht : Function.Injective (fun i : Fin 3 => zcirc (t i))) :
    Function.Injective (scJet t) := by
  intro c c' h
  have hsub : scJet t (c - c') = 0 := by rw [map_sub, h, sub_self]
  have hfst : (fun i => scFun 4 (c - c') (t i)) = 0 := congrArg Prod.fst hsub
  have hsnd : (fun i => scFunD 4 (c - c') (t i)) = 0 :=
    congrArg (fun z => z.2.1) hsub
  have hthd : (fun i => scFunD2 4 (c - c') (t i)) = 0 :=
    congrArg (fun z => z.2.2) hsub
  have hz := scPoly_eq_zero_of_jets ht (fun i => congrFun hfst i)
    (fun i => congrFun hsnd i) (fun i => congrFun hthd i)
  have hzero : c - c' = 0 := (scPoly_eq_zero_iff (c - c')).mp hz
  exact sub_eq_zero.mp hzero

/-- **The dimensions match**: both the coefficient space of degree-four trigonometric sums and
the space of value/first/second derivative data at three parameters are nine-dimensional. -/
lemma finrank_scJet :
    Module.finrank ℝ (ScCoeff 4) =
      Module.finrank ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) := by
  have h1 : Module.finrank ℝ (ScCoeff 4) = 9 := by
    show Module.finrank ℝ (EuclideanSpace ℝ (ScIdx 4)) = 9
    rw [finrank_euclideanSpace]
    simp [ScIdx, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
  have h2 : Module.finrank ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) = 9 := by
    simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [h1, h2]

/-- **Richness at three parameters**: the jet map (value, first and second derivative at three
parameters with distinct `zcirc`-images) is surjective. -/
theorem scJet_surjective {t : Fin 3 → ℝ}
    (ht : Function.Injective (fun i : Fin 3 => zcirc (t i))) :
    Function.Surjective (scJet t) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_scJet).mp
    (scJet_injective ht)

/-- **Richness for the value-and-first-derivative data at three parameters**: the map
`c ↦ (value, first derivative)` is surjective. -/
theorem scValueDeriv_surjective {t : Fin 3 → ℝ}
    (ht : Function.Injective (fun i : Fin 3 => zcirc (t i))) :
    Function.Surjective (fun c : ScCoeff 4 =>
      ((fun i => scFun 4 c (t i)), (fun i => scFunD 4 c (t i)))) := by
  rintro ⟨y₁, y₂⟩
  obtain ⟨c, hc⟩ := scJet_surjective ht (y₁, y₂, 0)
  refine ⟨c, ?_⟩
  change ((fun i => scFun 4 c (t i)), (fun i => scFunD 4 c (t i))) = (y₁, y₂)
  simp only [scJet_apply, Prod.mk.injEq] at hc
  rw [hc.1, hc.2.1]

/-- Some basis function of degree at most four has a nonzero second derivative at every
parameter. -/
lemma scBaseD2_exists_ne_zero (t : ℝ) : ∃ j : ScIdx 4, scBaseD2 4 j t ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 := h (some (0, false))
  have h2 := h (some (0, true))
  have hc : Real.cos t = 0 := by
    have h1' : -(scFreq 4 0) ^ 2 * Real.cos (scFreq 4 0 * t) = 0 := by simpa [scBaseD2] using h1
    have hf : scFreq 4 0 = 1 := by simp [scFreq]
    rw [hf] at h1'
    have : (1 : ℝ) ^ 2 * Real.cos (1 * t) = 0 := by linarith [h1']
    simpa using this
  have hs : Real.sin t = 0 := by
    have h2' : -(scFreq 4 0) ^ 2 * Real.sin (scFreq 4 0 * t) = 0 := by simpa [scBaseD2] using h2
    have hf : scFreq 4 0 = 1 := by simp [scFreq]
    rw [hf] at h2'
    have : (1 : ℝ) ^ 2 * Real.sin (1 * t) = 0 := by linarith [h2']
    simpa using this
  have hsum := Real.cos_sq_add_sin_sq t
  rw [hc, hs] at hsum
  norm_num at hsum

/-- **Richness of the second derivative at one parameter**: every real number is the second
derivative of a degree-four trigonometric sum at `t`. -/
theorem scFunD2_surjective (t : ℝ) :
    Function.Surjective (fun c : ScCoeff 4 => scFunD2 4 c t) := by
  obtain ⟨j, hj⟩ := scBaseD2_exists_ne_zero t
  intro y
  refine ⟨WithLp.toLp 2 (fun j' : ScIdx 4 => if j' = j then y / scBaseD2 4 j t else 0), ?_⟩
  simp only [scFunD2]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro b _ hb
    simp [hb]
  · intro hj'; exact absurd (Finset.mem_univ j) hj'

/-! ## Comparing `zcirc` at fundamental-domain parameters -/

/-- Two distinct parameters of the fundamental domain `[0, 2π)` have distinct `zcirc`-images. -/
lemma zcirc_ne_of {s t : ℝ} (hs : s ∈ Set.Ico 0 (2 * Real.pi))
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (h : s ≠ t) : zcirc s ≠ zcirc t := by
  intro hEq
  rw [zcirc, zcirc, Complex.exp_eq_exp_iff_exists_int] at hEq
  obtain ⟨n, hn⟩ := hEq
  have him : s = t + (n : ℝ) * (2 * Real.pi) := by
    have h1 := congrArg Complex.im hn
    simpa using h1
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hst : s - t = (n : ℝ) * (2 * Real.pi) := by linarith
  have hlt : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    rw [← hst]; linarith [hs.2, ht.1]
  have hgt : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by
    rw [← hst]; linarith [hs.1, ht.2]
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have hn0 : n = 0 := by
    have h3 : n < 1 := by exact_mod_cast hn1
    have h4 : -1 < n := by exact_mod_cast hn2
    omega
  rw [hn0] at him
  simp at him
  exact h him

/-! ## Assembling a coefficient vector from its scalar components -/

/-- The coefficient vector of `QCoeff 4` whose `i`-th coordinate is the scalar coefficient vector
`f i`. -/
def coeffOf (f : Fin 3 → ScCoeff 4) : QCoeff 4 :=
  WithLp.toLp 2 (fun k : Fin (3 * (2 * 4 + 1)) =>
    f ((cIdxEquiv 4).symm k).1 ((cIdxEquiv 4).symm k).2)

lemma coefC_coeffOf (f : Fin 3 → ScCoeff 4) (i : Fin 3) :
    coefC 4 (coeffOf f) i = f i := by
  ext j
  simp [coefC, coefAt, coeffOf, Equiv.symm_apply_apply]

/-- **Surjectivity of the data map**: the value and the derivative of the correction at three
pairwise distinct fundamental-domain parameters can be prescribed arbitrarily. -/
theorem dataJet_surjective {a b m : ℝ}
    (ha : a ∈ Set.Ico 0 (2 * Real.pi)) (hb : b ∈ Set.Ico 0 (2 * Real.pi))
    (hm : m ∈ Set.Ico 0 (2 * Real.pi)) (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) :
    Function.Surjective (fun c : QCoeff 4 =>
      (corr 4 c a, corr 4 c b, corr 4 c m, corrD 4 c a, corrD 4 c b, corrD 4 c m)) := by
  rintro ⟨P, Q, M, A, B, C⟩
  have ht : Function.Injective (fun j : Fin 3 => zcirc (![a, b, m] j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact absurd hij (zcirc_ne_of ha hb hab)
    · exact absurd hij (zcirc_ne_of ha hm ham)
    · exact absurd hij (zcirc_ne_of hb ha (Ne.symm hab))
    · exact absurd hij (zcirc_ne_of hb hm hbm)
    · exact absurd hij (zcirc_ne_of hm ha (Ne.symm ham))
    · exact absurd hij (zcirc_ne_of hm hb (Ne.symm hbm))
  have key : ∀ i : Fin 3, ∃ f : ScCoeff 4, scFun 4 f a = P i ∧
      scFun 4 f b = Q i ∧ scFun 4 f m = M i ∧ scFunD 4 f a = A i ∧
      scFunD 4 f b = B i ∧ scFunD 4 f m = C i := by
    intro i
    obtain ⟨f, hf⟩ := scValueDeriv_surjective ht
      ((fun j => ![P i, Q i, M i] j), (fun j => ![A i, B i, C i] j))
    refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrFun (congrArg Prod.fst hf) 0
    · simpa using congrFun (congrArg Prod.fst hf) 1
    · simpa using congrFun (congrArg Prod.fst hf) 2
    · simpa using congrFun (congrArg (fun z => z.2) hf) 0
    · simpa using congrFun (congrArg (fun z => z.2) hf) 1
    · simpa using congrFun (congrArg (fun z => z.2) hf) 2
  choose f hf using key
  refine ⟨coeffOf f, ?_⟩
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; rw [corr_apply, coefC_coeffOf]; exact (hf i).1
  · ext i; rw [corr_apply, coefC_coeffOf]; exact (hf i).2.1
  · ext i; rw [corr_apply, coefC_coeffOf]; exact (hf i).2.2.1
  · ext i; rw [corrD_apply, coefC_coeffOf]; exact (hf i).2.2.2.1
  · ext i; rw [corrD_apply, coefC_coeffOf]; exact (hf i).2.2.2.2.1
  · ext i; rw [corrD_apply, coefC_coeffOf]; exact (hf i).2.2.2.2.2


/-- **Surjectivity of the acceleration of the correction**: every vector of `Space` is realised as
`corrD2 4 c t` for a suitable coefficient vector. -/
theorem corrD2_surjective (t : ℝ) :
    Function.Surjective (fun c : QCoeff 4 => corrD2 4 c t) := by
  intro w
  have key : ∀ i : Fin 3, ∃ f : ScCoeff 4, scFunD2 4 f t = w i := fun i =>
    scFunD2_surjective t (w i)
  choose f hf using key
  refine ⟨coeffOf f, ?_⟩
  ext i
  rw [corrD2_apply, coefC_coeffOf]
  exact hf i

end

end Work.Drive
