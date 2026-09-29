import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.discRootsReal

/-!
# TMC14Core: the derivative/gap estimate for the rational discriminant

This file proves `Work.TMC14Core.derivDivGapLe`, the elementary polynomial lemma underlying
ROUTE_LEAD §4 C14 14f:

Let `Δ = disc p q lam` be the discriminant of the rational approximant `p/q`, `c` a real
number with `|c| ≤ 2 + 2 λ^q`, and `a < b` two real points with `Δ(a) = Δ(b) = c`.  Then for
every `η > 0` and every `C` with `‖Δ(a + iη) - c‖ ≤ C` one has

  `‖Δ'(a)‖ / (b - a) ≤ C / η²`.

The proof is the standard one.  Write `f = Δ - c ∈ ℂ[X]`; then `f(a) = f(b) = 0`, so
`f = (X - a)(X - b) · Q` with `Q ∈ ℂ[X]` monic of degree `q - 2`.  Two facts combine:

* **every root of `f` is real** (and hence every root of `Q` is real): this is the input of
  Avila–Jitomirskaya, formalised as `discRootsReal` — the level set `{Δ = c}` for
  `|c| ≤ 2 + 2λ^q` lies in `ℝ`.  Consequently `‖Q(a)‖ ≤ ‖Q(a + iη)‖`, since moving off the
  real axis moves away from every real root;

* **the identity** `Δ'(a) = (a - b) Q(a)` and
  `f(a + iη) = (iη)·((a - b) + iη)·Q(a + iη)`, so that

  `η² ‖Q(a)‖ ≤ η·‖(a - b) + iη‖·‖Q(a + iη)‖ = ‖f(a + iη)‖ ≤ C`.

Dividing by `η² > 0` and using `‖Δ'(a)‖ = (b - a)‖Q(a)‖` gives the claim.  Note that the
sharper factor `η` (rather than `b - a`) in the second factor of `f(a + iη)` is exactly what
produces `η²` in the denominator.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. Elementary norm facts -/

/-- Moving off the real axis increases the distance to the origin: for real `t, η`,
`|t| ≤ ‖t + iη‖`. -/
lemma abs_le_norm_add_I (t η : ℝ) : |t| ≤ ‖((t : ℝ) : ℂ) + (η : ℂ) * Complex.I‖ := by
  calc |t| = |(((t : ℝ) : ℂ) + (η : ℂ) * Complex.I).re| := by simp
    _ ≤ ‖(((t : ℝ) : ℂ) + (η : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _

/-! ## 2. A polynomial all of whose roots are real does not decrease off the real axis -/

/-- If every root of `Q ∈ ℂ[X]` is real, then `‖Q(a)‖ ≤ ‖Q(a + iη)‖` for real `a` and `η ≥ 0`:
each factor `|a - r|` of the product over the (real) roots is increased to `|a + iη - r|`. -/
theorem norm_eval_le_of_roots_real {Q : Polynomial ℂ}
    (hQ : ∀ z : ℂ, Q.eval z = 0 → z.im = 0) (a : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    ‖Q.eval (a : ℂ)‖ ≤ ‖Q.eval ((a : ℂ) + (η : ℂ) * Complex.I)‖ := by
  have key : ∀ n, ∀ Q : Polynomial ℂ, Q.natDegree ≤ n →
      (∀ z : ℂ, Q.eval z = 0 → z.im = 0) →
      ‖Q.eval (a : ℂ)‖ ≤ ‖Q.eval ((a : ℂ) + (η : ℂ) * Complex.I)‖ := by
    intro n
    induction n with
    | zero =>
      intro Q hdeg _
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp hdeg)
      rw [← hc]
      simp
    | succ n ih =>
      intro Q hdeg hQr
      by_cases h0 : Q.natDegree = 0
      · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [← hc]
        simp
      · have hQ0 : Q ≠ 0 := by rintro rfl; simp at h0
        have hdegpos : 0 < Q.degree := by
          rw [Polynomial.degree_eq_natDegree hQ0]
          exact_mod_cast Nat.pos_of_ne_zero h0
        obtain ⟨r, hr⟩ := Complex.exists_root (f := Q) hdegpos
        have hrreal : r.im = 0 := hQr r hr
        obtain ⟨Q₁, hQ₁⟩ := (Polynomial.dvd_iff_isRoot (p := Q) (a := r)).mpr hr
        have hQ₁0 : Q₁ ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hQ₁
          exact hQ0 hQ₁
        have hnat : Q₁.natDegree ≤ n := by
          have h1 : Q.natDegree = 1 + Q₁.natDegree := by
            rw [hQ₁, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hQ₁0,
              Polynomial.natDegree_X_sub_C]
          omega
        have ih' := ih Q₁ hnat (fun z hz =>
          hQr z (by rw [hQ₁, Polynomial.eval_mul, hz, mul_zero]))
        rw [hQ₁]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [norm_mul, norm_mul]
        refine mul_le_mul ?_ ih' (norm_nonneg _) (norm_nonneg _)
        have hr' : r = ((r.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hrreal]
        rw [hr']
        have e1 : (a : ℂ) - ((r.re : ℝ) : ℂ) = ((a - r.re : ℝ) : ℂ) := by push_cast; ring
        have e2 : (a : ℂ) + (η : ℂ) * Complex.I - ((r.re : ℝ) : ℂ)
            = ((a - r.re : ℝ) : ℂ) + (η : ℂ) * Complex.I := by push_cast; ring
        rw [e1, e2]
        have hL : ‖((a - r.re : ℝ) : ℂ)‖ = |a - r.re| := RCLike.norm_ofReal _
        rw [hL]
        exact abs_le_norm_add_I _ _
  exact key Q.natDegree Q le_rfl hQ

/-! ## 3. Factoring out two distinct roots -/

/-- Over `ℂ`, a polynomial vanishing at two distinct points `u ≠ v` is divisible by
`(X - u)(X - v)`. -/
theorem dvd_quadratic_of_eval_eq_zero {f : Polynomial ℂ} {u v : ℂ} (huv : u ≠ v)
    (hu : f.eval u = 0) (hv : f.eval v = 0) :
    ∃ Q : Polynomial ℂ, f = (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) * Q := by
  obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot (p := f) (a := v)).mpr hv
  have hgu : g.eval u = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval u) hg
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      hu] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr huv)
  obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot (p := g) (a := u)).mpr hgu
  exact ⟨Q, by rw [hg, hQ]; ring⟩

/-- The derivative of `(X - u)(X - v)Q` at the root `u` is `(u - v)Q(u)`. -/
theorem derivative_eval_quad_factor (Q : Polynomial ℂ) (u v : ℂ) :
    (((Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) * Q).derivative).eval u
      = (u - v) * Q.eval u := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, sub_zero, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  ring

/-! ## 4. The estimate -/

theorem derivDivGapLe (p : ℤ) (q : ℕ) (lam : ℝ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 1 ≤ q) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (c : ℝ) (hc : |c| ≤ 2 + 2 * lam ^ q)
    {a b : ℝ} (ha : (disc p q lam).eval (a : ℂ) = (c : ℂ))
    (hb : (disc p q lam).eval (b : ℂ) = (c : ℂ)) (hab : a < b) {eta C : ℝ} (heta : 0 < eta)
    (hC : ‖(disc p q lam).eval ((a : ℂ) + eta * Complex.I) - (c : ℂ)‖ ≤ C) :
    ‖(disc p q lam).derivative.eval (a : ℂ)‖ / (b - a) ≤ C / eta ^ 2 := by
  set f : Polynomial ℂ := disc p q lam - Polynomial.C (c : ℂ) with hf
  have hfa : f.eval (a : ℂ) = 0 := by
    rw [hf, Polynomial.eval_sub, Polynomial.eval_C, ha, sub_self]
  have hfb : f.eval (b : ℂ) = 0 := by
    rw [hf, Polynomial.eval_sub, Polynomial.eval_C, hb, sub_self]
  have habne : (a : ℂ) ≠ (b : ℂ) := by
    rw [ne_eq, Complex.ofReal_inj]
    exact ne_of_lt hab
  obtain ⟨Q, hQ⟩ := dvd_quadratic_of_eval_eq_zero habne hfa hfb
  -- every root of `Q` is real, being a root of `f = disc - c`
  have hQroot : ∀ z : ℂ, Q.eval z = 0 → z.im = 0 := by
    intro z hz
    have hfz : f.eval z = 0 := by
      rw [hQ]
      simp only [Polynomial.eval_mul, hz, mul_zero]
    have hdisc : (disc p q lam).eval z = (c : ℂ) := by
      rw [hf, Polynomial.eval_sub, Polynomial.eval_C] at hfz
      exact sub_eq_zero.mp hfz
    obtain ⟨x, hx⟩ := discRootsReal p q lam hpq hq hlam c hc hdisc
    rw [hx]
    simp
  have hkey := norm_eval_le_of_roots_real hQroot a (le_of_lt heta)
  have hfeval : ‖f.eval ((a : ℂ) + eta * Complex.I)‖ ≤ C := by
    simpa only [hf, Polynomial.eval_sub, Polynomial.eval_C] using hC
  -- the value of `f` at `a + iη` factors through `Q(a + iη)`
  have hsplit : f.eval ((a : ℂ) + eta * Complex.I)
      = ((eta : ℂ) * Complex.I) * (((a : ℂ) + eta * Complex.I) - (b : ℂ))
        * Q.eval ((a : ℂ) + eta * Complex.I) := by
    rw [hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hnorm : ‖f.eval ((a : ℂ) + eta * Complex.I)‖
      = eta * ‖((a : ℂ) + eta * Complex.I) - (b : ℂ)‖
        * ‖Q.eval ((a : ℂ) + eta * Complex.I)‖ := by
    rw [hsplit, norm_mul, norm_mul, norm_mul]
    have he : ‖(((eta : ℝ)) : ℂ)‖ = eta := by
      calc ‖(((eta : ℝ)) : ℂ)‖ = |eta| := RCLike.norm_ofReal eta
        _ = eta := abs_of_pos heta
    rw [he, Complex.norm_I, mul_one]
  have hz0 : eta ≤ ‖((a : ℂ) + eta * Complex.I) - (b : ℂ)‖ := by
    have hrw : ((a : ℂ) + eta * Complex.I) - (b : ℂ)
        = ((a - b : ℝ) : ℂ) + (eta : ℂ) * Complex.I := by push_cast; ring
    rw [hrw]
    calc eta = |(((a - b : ℝ) : ℂ) + (eta : ℂ) * Complex.I).im| := by
          simp [abs_of_pos heta]
      _ ≤ ‖((a - b : ℝ) : ℂ) + (eta : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
  have hbound : eta ^ 2 * ‖Q.eval (a : ℂ)‖ ≤ C :=
    calc eta ^ 2 * ‖Q.eval (a : ℂ)‖
        ≤ eta ^ 2 * ‖Q.eval ((a : ℂ) + eta * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = eta * (eta * ‖Q.eval ((a : ℂ) + eta * Complex.I)‖) := by ring
      _ ≤ eta * (‖((a : ℂ) + eta * Complex.I) - (b : ℂ)‖
            * ‖Q.eval ((a : ℂ) + eta * Complex.I)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz0 (norm_nonneg _))
            (le_of_lt heta)
      _ = ‖f.eval ((a : ℂ) + eta * Complex.I)‖ := by rw [hnorm]; ring
      _ ≤ C := hfeval
  have hderiv : f.derivative.eval (a : ℂ) = ((a : ℂ) - (b : ℂ)) * Q.eval (a : ℂ) := by
    rw [hQ]
    exact derivative_eval_quad_factor Q (a : ℂ) (b : ℂ)
  have hdisc_deriv : (disc p q lam).derivative = f.derivative := by
    rw [hf, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero]
  have hnorm_deriv : ‖(disc p q lam).derivative.eval (a : ℂ)‖ = (b - a) * ‖Q.eval (a : ℂ)‖ := by
    rw [hdisc_deriv, hderiv, norm_mul]
    have h1 : ‖((a : ℂ) - (b : ℂ))‖ = b - a := by
      have e : (a : ℂ) - (b : ℂ) = ((a - b : ℝ) : ℂ) := by push_cast; ring
      rw [e]
      calc ‖((a - b : ℝ) : ℂ)‖ = |a - b| := RCLike.norm_ofReal _
        _ = b - a := by rw [abs_of_neg (by linarith)]; ring
    rw [h1]
  rw [hnorm_deriv, mul_div_cancel_left₀ _ (by linarith : b - a ≠ 0)]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < eta ^ 2)]
  calc ‖Q.eval (a : ℂ)‖ * eta ^ 2 = eta ^ 2 * ‖Q.eval (a : ℂ)‖ := mul_comm _ _
    _ ≤ C := hbound

end Work.TMC14Core
