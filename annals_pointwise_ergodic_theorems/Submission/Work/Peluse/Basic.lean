/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib

/-!
# Peluse's inverse theorem for the progression `(x, x + n, x + P(n))`: notation

This module fixes the notation of

* S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Mathematics, Pi **8**
  (2020), e16 (arXiv:1909.00309),

the inverse theorem (Theorem 3.3 there) for the bilinear averages along the polynomial
progression `(x, x + y, x + P(y))` that Krause–Mirek–Tao use as the deep input of their §5
(`improv`, their Theorem `pp`).  We follow Peluse's notation literally:

* `shift`, `Delta`, `DeltaP` : the operators `T_h f`, `Δ_h f = conj (f(·+h)) · f`,
  `Δ'_{(h,h')} f = conj (f(·+h)) · f(·+h')` of §2;
* `muL` : the weight `μ_L(h) = #{h₁,h₂ ∈ [L] : h₁ - h₂ = h}/L²` of §2, used in van der Corput's
  inequality;
* `cubeTerm`, `boxSumPow`, `boxNormPow`, `boxNorm` : the Gowers *box* norm
  `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` of Definition 2.1, together with the *uniformity* norm
  `‖f‖_{U^t_Q(S)}` obtained by taking all the sets `Q_i` equal;
* `prodCubeSum` : the general "cube average with `2^t` different functions" whose bound by the
  product of box norms is Peluse's Lemma 2.3;
* `LambdaZ` / `LambdaHalfZ` / `dualFn` / `progAvg` : the multilinear average
  `Λ^{N,M}` of §3, its upper-half variant matching `AhalfZ` of the workspace, the dual function
  `F_2` of Corollary 3.8 and the progression average `E_{y ∈ [N']} f (x + qy)`;
* `FinSuppZ` : "finitely supported", the standing hypothesis on all the functions below.

## Conventions

All functions live on `ℤ` with complex values, as in Peluse.  The box norms use Peluse's
normalisation `(1/|S|) ∑_{x ∈ ℤ}` where `S` is the support of `f`; the sum over `x` is a `tsum`,
which is a genuine finite sum exactly when `f` is finitely supported (`FinSuppZ`), the standing
hypothesis of the whole area.  The conjugation `C^{|ω|}` of the paper is rendered by iterating
`star`, see `star_iterate_even` / `star_iterate_odd`.

## Reference

`Submission/Work/KMTPlan/ROUTE_LEAD.md` §1.3 (Area A2) and `Submission/Work/Peluse/PLAN.md`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-! ## Shifts, differences and the van der Corput weight -/

/-- The shift `T_h f (x) = f (x + h)`. -/
def shift (h : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => f (x + h)

/-- The operator `Δ_h f (x) = conj (f (x + h)) · f x`. -/
def Delta (h : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => star (f (x + h)) * f x

/-- The operator `Δ'_{(h,h')} f (x) = conj (f (x + h)) · f (x + h')`. -/
def DeltaP (h h' : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => star (f (x + h)) * f (x + h')

/-- The weight `μ_L(h) = #{h₁,h₂ ∈ [L] : h₁ - h₂ = h}/L²` of Peluse §2: finitely supported in
`(-L,L)`, with `∑_h μ_L(h) = 1` and `∑_h μ_L(h)² ≤ 1/L`. -/
def muL (L : ℕ) (h : ℤ) : ℝ :=
  ((L : ℝ) ^ 2)⁻¹ * (((Finset.Icc 1 L).product (Finset.Icc 1 L)).filter
    (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = h)).card

/-- The paper's `‖x‖`: the distance from the real number `x` to the nearest integer.  (The paper
writes `‖·‖` for this, and uses it for all the major-arc conditions.) -/
def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

lemma distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := by
  simpa [distInt] using abs_sub_round x

lemma distInt_add_int (x : ℝ) (n : ℤ) : distInt (x + (n : ℝ)) = distInt x := by
  have h : round (x + (n : ℝ)) = round x + n := by
    rw [round_eq, round_eq]
    push_cast
    rw [show x + (n:ℝ) + 1/2 = (x + 1/2) + (n:ℝ) by ring, Int.floor_add_intCast]
  simp [distInt, h]

/-- `f` is supported in `[-N,N]` (Peluse's "supported on the interval"): the standing hypothesis on
all the functions of this area. -/
def SupportIn (f : ℤ → ℂ) (N : ℕ) : Prop := ∀ x : ℤ, N < x.natAbs → f x = 0

/-- `f` has finite support. -/
def FinSuppZ (f : ℤ → ℂ) : Prop := ∃ N : ℕ, SupportIn f N

lemma FinSuppZ.zero : FinSuppZ (0 : ℤ → ℂ) := ⟨0, fun _ _ => rfl⟩

lemma SupportIn.mono {f : ℤ → ℂ} {N N' : ℕ} (h : SupportIn f N) (hNN' : N ≤ N') :
    SupportIn f N' := fun x hx => h x (lt_of_le_of_lt hNN' hx)

lemma FinSuppZ.of_supportIn {f : ℤ → ℂ} {N : ℕ} (h : SupportIn f N) : FinSuppZ f := ⟨N, h⟩

/-! ## The cube term of the box norm -/

/-- The `ω`-corner of the cube with lower corner `h'` and increment `h - h'`, i.e.
`ω · h + (1 - ω) · h'`. -/
def cornerShift {t : ℕ} (h h' : Fin t → ℤ) (ω : Fin t → Bool) : ℤ :=
  ∑ i : Fin t, if ω i then h i else h' i

/-- The number of `1`'s in `ω`, i.e. `|ω|` of the paper. -/
def weight {t : ℕ} (ω : Fin t → Bool) : ℕ := (Finset.univ.filter fun i => ω i).card

/-- The cube term `∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')` of the paper (with
`C` the conjugation, rendered by iterating `star`). -/
def cubeTerm {t : ℕ} (h h' : Fin t → ℤ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + cornerShift h h' ω))

/-- The general cube average with `2^t` possibly different functions `f ω`:
`(1/|S|) ∑_x E_{h,h'} ∏_{ω} C^{|ω|} f_ω (x + ω·h + (1-ω)·h')`.  This is the quantity bounded by
`∏_ω ‖f_ω‖_{□^t}` in Peluse's Lemma 2.3. -/
def prodCubeSum (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : (Fin t → Bool) → ℤ → ℂ) : ℂ :=
  ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
    ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f ω (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))

lemma prodCubeSum_eq (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : (Fin t → Bool) → ℤ → ℂ) :
    prodCubeSum t Q S f = ((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f ω (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) :=
  rfl

/-- The `2^t`-th power of the Gowers box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` of Peluse's
Definition 2.1, as a complex number:

`(1/|S|) ∑_x E_{h_i,h_i' ∈ Q_i} Δ'_{(h₁,h₁'),…,(h_t,h_t')} f (x)`.

For finitely supported `f` this complex number is a nonnegative real, see
`prodCubeSum_single_re_nonneg`; `boxNormPow` is its modulus. -/
def boxSumPow (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℂ :=
  prodCubeSum t Q S (fun _ => f)

/-- The `2^t`-th power of the Gowers box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` of Peluse's
Definition 2.1, as a *nonnegative real*.  It agrees with the real number defined by the paper (see
`boxSumPow_eq`), but taking the modulus makes it automatically nonnegative. -/
def boxNormPow (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ‖boxSumPow t Q S f‖

/-- The Gowers box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}`. -/
def boxNorm (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  (boxNormPow t Q S f) ^ (1 / ((2 : ℝ) ^ t))

/-- The the `2^t`-th power of the Gowers *uniformity* norm `‖f‖_{U^t_Q(S)}` (all the sets equal). -/
def uNormPow (t : ℕ) (Q : Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  boxNormPow t (fun _ : Fin t => Q) S f

/-- The Gowers uniformity norm `‖f‖_{U^t_Q(S)}`. -/
def uNorm (t : ℕ) (Q : Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  (uNormPow t Q S f) ^ (1 / ((2 : ℝ) ^ t))

/-! ## Cubes with a constant step: the sets `Q = c[L]` -/

/-- The interval `[L] = {1, 2, …, L}` of the paper, as a set of integers. -/
def intIcc (L : ℕ) : Finset ℤ := (Finset.Icc 1 L).image (fun n : ℕ => (n : ℤ))

/-- The arithmetic-progression set `c[L] = {c, 2c, …, Lc}` of the paper. -/
def arithIcc (c : ℤ) (L : ℕ) : Finset ℤ := (Finset.Icc 1 L).image (fun n : ℕ => c * (n : ℤ))

/-- The symmetric interval `[-L, L]` as a set of integers. -/
def symIcc (L : ℕ) : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ)

/-! ## The multilinear averages of §3 -/

/-- The paper's multilinear average for the progression `(x, x+y, x+P(y))`:

`Λ^{N,M}_{y,P}(f₀,f₁,f₂) = (1/(N M)) ∑_x f₀(x) ∑_{y ∈ [M]} f₁ (x+y) f₂ (x + P(y))`.

This is the specialisation `m = 2`, `P₁ = X`, `P₂ = P` of Peluse's
`Λ^{N,M}_{P₁,…,P_m}(f₀,…,f_m)` to the case of two polynomials, with all the characters
`ψ_i` trivial. -/
def LambdaZ (N M : ℕ) (P : ℤ[X]) (f₀ f₁ f₂ : ℤ → ℂ) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f₀ x *
    ∑ y ∈ Finset.Icc 1 M, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))

/-- The *upper-half* variant of `LambdaZ` matching the workspace's `AhalfZ`: the average over
`y ∈ (M/2, M]`. -/
def LambdaHalfZ (N M : ℕ) (P : ℤ[X]) (f₀ f₁ f₂ : ℤ → ℂ) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f₀ x *
    ∑ y ∈ Finset.Ioc (M / 2) M, f₁ (x + (y : ℤ)) * f₂ (x + P.eval (y : ℤ))

/-- The dual function of Peluse's Corollary 3.8 in the case `ℓ = 2`, `m = 2`, `P₁ = X`:

`F₂(x) = E_{y ∈ [M]} f₀ (x - P(y)) f₁ (x + y - P(y))`. -/
def dualFn (M : ℕ) (P : ℤ[X]) (f₀ f₁ : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ((M : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 M,
    f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))

/-- The progression average `E_{y ∈ [N']} f (x + q y) = (1/N') ∑_{y ∈ [N']} f (x + qy)`. -/
def progAvg (N' : ℕ) (q : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ((N' : ℂ))⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))

/-- The quantity met in the conclusion (ii) of Peluse's Theorem 3.3:
`∑_x |E_{y ∈ [N']} f (x + qy)|`. -/
def progAvgSum (N' : ℕ) (q : ℤ) (f : ℤ → ℂ) : ℝ :=
  ∑' x : ℤ, ‖progAvg N' q f x‖

/-! ## Iterated conjugation -/

lemma star_iterate_two_mul (k : ℕ) (z : ℂ) : ((starRingEnd ℂ)^[2 * k]) z = z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, Function.iterate_add_apply]
      rw [show ((starRingEnd ℂ)^[2]) z = z by simp [Function.iterate_succ_apply']]
      exact ih

lemma star_iterate_two_mul_add_one (k : ℕ) (z : ℂ) : ((starRingEnd ℂ)^[2 * k + 1]) z = star z := by
  rw [show 2 * k + 1 = 2 * k + 1 by ring, Function.iterate_succ_apply']
  rw [star_iterate_two_mul k z]
  rfl

/-- Iterated conjugation only depends on the parity of the exponent. -/
lemma star_iterate_eq (n : ℕ) (z : ℂ) :
    ((starRingEnd ℂ)^[n]) z = if n % 2 = 0 then z else star z := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show (k + k) % 2 = 0 by omega, if_pos rfl]
    rw [show k + k = 2 * k by omega]
    exact star_iterate_two_mul k z
  · rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
    exact star_iterate_two_mul_add_one k z

end

end Work.Peluse
