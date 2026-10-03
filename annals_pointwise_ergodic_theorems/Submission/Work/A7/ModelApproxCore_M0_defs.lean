/-
# Vocabulary for the sharp `‖M₀‖` estimate of the §6 model approximation (Area A7)

This module collects the *definitions* and the elementary (periodicity/normalisation) lemmas
needed by the sharp single-scale estimate of the symbol difference `M₀` of Proposition
`mod-approx` of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Ann. of Math. 195 (3) 2022 (see `NOTES_A7_ModelApproxCore.md`).

The objects are

* `momFun P ξ₁ ξ₂ t = e(ξ₁t + ξ₂P(t))`, the oscillatory phase (the integrand of `mTilde`);
* `arithW P α₁ α₂ n = fourier n α₁ · fourier (P n) α₂`, the arithmetic character, which is
  `q`-periodic on `ℤ` as soon as `q • α₁ = q • α₂ = 0` (`arithW_period`, `arithW_period_mul`);
* `Sval P k₁ k₂ = 2^{k₁} + 2^{d k₂}` (`d = P.natDegree`), the frequency scale of the estimate;
* `mFirst`/`mLast`, the enumeration of the residue class `a (mod q)` inside an interval of
  integers: `{a + q m : mFirst ≤ m ≤ mLast}` is exactly the set of `n ≡ a (mod q)` in `(K, N]`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

/-- **The oscillatory phase of the model approximation**,
`momFun P ξ₁ ξ₂ t = e(ξ₁ t + ξ₂ P(t))` with `e(x) = exp(2πix)`; this is the integrand of the
oscillatory integral `mTilde P N ξ₁ ξ₂`. -/
noncomputable def momFun (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => Work.KMTAreas.A7.ee (ξ₁ * t + ξ₂ * Work.KMTAreas.A7.PevalR P t)

/-- **The arithmetic character** `n ↦ e(α₁n + α₂P(n))` of the discrete average, in the
`fourier` convention of the Ionescu--Wainger framework. -/
noncomputable def arithW (P : ℤ[X]) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (n : ℤ) : ℂ :=
  fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂

/-- **The frequency scale** `S = 2^{k₁} + 2^{d k₂}` (`d = P.natDegree`) appearing in the sharp
estimate: the discrete average resolves the continuous frequencies up to this scale. -/
noncomputable def Sval (P : ℤ[X]) (k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)

/-- The least `m : ℤ` with `K < a + q m` (for `0 ≤ a < q` this is the first index of the class
`a (mod q)` above `K`). -/
def mFirst (q K a : ℕ) : ℤ :=
  if a ≤ K then (((K - a) / q : ℕ) : ℤ) + 1 else 0

/-- The greatest `m : ℤ` with `a + q m ≤ N`; `-1` if there is none. -/
def mLast (q N a : ℕ) : ℤ :=
  if a ≤ N then (((N - a) / q : ℕ) : ℤ) else -1

/-! ## Elementary facts -/

/-- The oscillatory phase has modulus one. -/
lemma momFun_norm_eq_one (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) (t : ℝ) : ‖momFun P ξ₁ ξ₂ t‖ = 1 := by
  simp [momFun, Work.KMTAreas.A7.ee, Complex.norm_exp]

/-- The summand of the discrete average is the arithmetic character times the phase. -/
lemma momPhase_eq (P : ℤ[X]) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (ξ₁ ξ₂ : ℝ) (n : ℤ) :
    Work.KMTAreas.A7.momPhase P N α₁ α₂ ξ₁ ξ₂ n
      = arithW P α₁ α₂ n * momFun P ξ₁ ξ₂ (n : ℝ) := by
  rw [Work.KMTAreas.A7.momPhase, arithW, momFun]

/-- The Fourier character `fourier (T:=1) · α` is `q`-periodic when `q • α = 0`. -/
lemma fourier_period (q : ℕ) (α : Work.Analysis.IonescuWainger.Circle) (h : q • α = 0) (n : ℤ) :
    fourier (T := 1) (n + q) α = fourier (T := 1) n α := by
  rw [fourier_add]
  rw [show fourier (T := 1) (q : ℤ) α = 1 from by
    rw [fourier_apply]
    have h2 : (q : ℤ) • α = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h
    rw [h2, AddCircle.toCircle_zero, Circle.coe_one]]
  ring

/-- `q` divides `P (n + q) - P n` (the difference is `(P(X+q) - P(X))` evaluated at `n`, and
`P(X+q) - P(X)` has all coefficients divisible by `q`). -/
lemma dvd_eval_add (P : ℤ[X]) (q : ℕ) (n : ℤ) : (q : ℤ) ∣ P.eval (n + q) - P.eval n := by
  have h1'' : ∀ m : ℤ, ((P.eval m : ℤ) : ZMod q)
      = Polynomial.eval (m : ZMod q) (P.map (Int.castRingHom (ZMod q))) := by
    intro m; rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply (p := P) (Int.castRingHom (ZMod q)) m).symm
  have key : ((P.eval (n + q) - P.eval n : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_sub, h1'' (n + q), h1'' n]
    have hq0 : ((n + q : ℤ) : ZMod q) = (n : ZMod q) := by
      push_cast
      rw [CharP.cast_eq_zero]
      ring
    rw [hq0, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at key

/-- **The arithmetic character is `q`-periodic in `n`** when `q • α₁ = q • α₂ = 0`. -/
lemma arithW_period (P : ℤ[X]) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (n : ℤ) :
    arithW P α₁ α₂ (n + q) = arithW P α₁ α₂ n := by
  have h2' : (q : ℤ) • α₂ = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h₂
  have hf2 : fourier (T := 1) (P.eval (n + q)) α₂ = fourier (T := 1) (P.eval n) α₂ := by
    obtain ⟨c, hc⟩ := dvd_eval_add P q n
    have heq : P.eval (n + q) = P.eval n + q * c := by linarith [hc]
    rw [heq, fourier_add, show fourier (T := 1) (q * c) α₂ = 1 from by
      rw [fourier_apply]
      have h3 : ((q : ℤ) * c) • α₂ = 0 := by rw [mul_zsmul, smul_comm, h2', smul_zero]
      rw [h3, AddCircle.toCircle_zero, Circle.coe_one]]
    ring
  rw [arithW, arithW, fourier_period q α₁ h₁ n, hf2]

/-- **The full periodicity**: `arithW P α₁ α₂ (n + q m) = arithW P α₁ α₂ n` for every `m : ℤ`. -/
lemma arithW_period_mul (P : ℤ[X]) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (n : ℤ) (m : ℤ) :
    arithW P α₁ α₂ (n + q * m) = arithW P α₁ α₂ n := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have h : n + (q : ℤ) * (k + 1) = (n + (q : ℤ) * k) + q := by ring
      rw [h, arithW_period P q α₁ α₂ h₁ h₂ (n + (q : ℤ) * k), ih]
  | pred k ih =>
      have h : n + (q : ℤ) * (-(k : ℤ) - 1) = (n + (q : ℤ) * (-(k : ℤ))) - q := by ring
      rw [h]
      have hh := arithW_period P q α₁ α₂ h₁ h₂ (n + (q : ℤ) * (-(k : ℤ)) - q)
      rw [show n + (q : ℤ) * (-(k : ℤ)) - q + q = n + (q : ℤ) * (-(k : ℤ)) from by ring] at hh
      rw [← hh, ih]

/-- The oscillatory phase is of class `C²`. -/
lemma momFun_contDiff (P : ℤ[X]) (ξ₁ ξ₂ : ℝ) : ContDiff ℝ 2 (momFun P ξ₁ ξ₂) := by
  have hpol : ContDiff ℝ 2 (fun t : ℝ => Work.KMTAreas.A7.PevalR P t) := by
    have h2 : (fun t : ℝ => Work.KMTAreas.A7.PevalR P t)
        = fun t : ℝ => ∑ i ∈ Finset.range ((P.map (Int.castRingHom ℝ)).natDegree + 1),
            (P.map (Int.castRingHom ℝ)).coeff i * t ^ i := by
      funext t; rw [Work.KMTAreas.A7.PevalR, Polynomial.eval_eq_sum_range]
    rw [h2]
    exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_id.pow i))
  have hfun : momFun P ξ₁ ξ₂
      = fun t : ℝ => Complex.exp (2 * ↑Real.pi * Complex.I * ↑(ξ₁ * t + ξ₂ * Work.KMTAreas.A7.PevalR P t)) :=
    rfl
  rw [hfun]
  apply ContDiff.cexp
  have harg : ContDiff ℝ 2 (fun x : ℝ => ξ₁ * x + ξ₂ * Work.KMTAreas.A7.PevalR P x) := by
    fun_prop
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp harg)

end

end Work.A7
