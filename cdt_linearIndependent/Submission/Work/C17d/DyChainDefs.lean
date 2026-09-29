import Mathlib
import Submission.Work.C17.seventeen_defs

/-!
# The polynomial chain attached to the order-2 operator `M` (area C17)

`M = P₂·∂² + P₁·∂ + P₀` (over `ℚ[X]`, `Pᵢ = Work.C17.Pᵢx a b`) is the order-two operator of the
unlikely series `P`.  In the `P`-branch module `WQ = ℚ(X)² × (Fin 6 → ℚ(X))` of
`Work.C17.seventeen_indep` the class of `∂_y^k` is `cls a b k`, obtained from the derivation `dW`.

This file supplies the *cleared* form of that chain: polynomials `Dc a b k`, `Ac a b k`, `Bc a b k`
with
  `algebraMap (Ac k) = algebraMap (Dc k) * (cls a b k).1`,  `algebraMap (Bc k) = algebraMap (Dc k) * (cls a b k).2`
(proved in `Work.C17d.RatChain`) and, for any holomorphic solution `y₁` of `M y₁ = 0` on a disc,
  `Dc k z * DyIter k y₁ z = Ac k z * y₁ z + Bc k z * ((deriv y₁) z)`
(proved in `Work.C17d.AnaChain`).

The recursion is the one obtained by clearing the denominators in
`(u,v) ↦ (ρ(u' - v·P₀/P₂), ρ(u + v' - v·P₁/P₂))` with `ρ = (X-1)²/(X²-2X)`.
-/

namespace Work.C17d

open Polynomial
open Work.C17

noncomputable section

/-- `X - 1`: the numerator of `rhoQ` (up to the square) and the factor appearing in the clearing. -/
def rX : Polynomial ℚ := X - 1

/-- `X ^ 2 - 2 * X = X(X-2)`: the denominator of `rhoQ`. -/
def wX : Polynomial ℚ := X ^ 2 - 2 * X

lemma rX_ne_zero : rX ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial ℚ => p.eval 0) h
  simp [rX] at h2

lemma wX_ne_zero : wX ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial ℚ => p.eval 1) h
  norm_num [wX] at h2

/-- One step of the cleared chain: `(D,A,B) ↦ (D²P₂W, r²[...], r²[...])`. -/
def chainStep (a b : ℚ) (D A B : Polynomial ℚ) :
    Polynomial ℚ × Polynomial ℚ × Polynomial ℚ :=
  (D ^ 2 * P2x a b * wX,
   rX ^ 2 * (D * P2x a b * A.derivative - P2x a b * D.derivative * A - D * B * P0x a b),
   rX ^ 2 * (D * P2x a b * (A + B.derivative) - D * B * P1x a b - P2x a b * D.derivative * B))

/-- The cleared chain `(D_k, A_k, B_k)` of the class of `∂_y^k`. -/
def chain (a b : ℚ) : ℕ → Polynomial ℚ × Polynomial ℚ × Polynomial ℚ
  | 0 => (1, 1, 0)
  | k + 1 => chainStep a b (chain a b k).1 (chain a b k).2.1 (chain a b k).2.2

/-- The common denominator `D_k`. -/
def Dc (a b : ℚ) (k : ℕ) : Polynomial ℚ := (chain a b k).1

/-- The `y₁`-coefficient `A_k`. -/
def Ac (a b : ℚ) (k : ℕ) : Polynomial ℚ := (chain a b k).2.1

/-- The `y₁'`-coefficient `B_k`. -/
def Bc (a b : ℚ) (k : ℕ) : Polynomial ℚ := (chain a b k).2.2

@[simp] lemma chain_zero (a b : ℚ) : chain a b 0 = (1, 1, 0) := rfl

@[simp] lemma chain_succ (a b : ℚ) (k : ℕ) :
    chain a b (k + 1) = chainStep a b (Dc a b k) (Ac a b k) (Bc a b k) := rfl

@[simp] lemma Dc_zero (a b : ℚ) : Dc a b 0 = 1 := rfl
@[simp] lemma Ac_zero (a b : ℚ) : Ac a b 0 = 1 := rfl
@[simp] lemma Bc_zero (a b : ℚ) : Bc a b 0 = 0 := rfl

@[simp] lemma Dc_succ (a b : ℚ) (k : ℕ) :
    Dc a b (k + 1) = Dc a b k ^ 2 * P2x a b * wX := by
  simp [Dc, Ac, Bc, chainStep]

@[simp] lemma Ac_succ (a b : ℚ) (k : ℕ) :
    Ac a b (k + 1) = rX ^ 2 * (Dc a b k * P2x a b * (Ac a b k).derivative
      - P2x a b * (Dc a b k).derivative * Ac a b k - Dc a b k * Bc a b k * P0x a b) := by
  simp [Dc, Ac, Bc, chainStep]

@[simp] lemma Bc_succ (a b : ℚ) (k : ℕ) :
    Bc a b (k + 1) = rX ^ 2 * (Dc a b k * P2x a b * (Ac a b k + (Bc a b k).derivative)
      - Dc a b k * Bc a b k * P1x a b - P2x a b * (Dc a b k).derivative * Bc a b k) := by
  simp [Dc, Ac, Bc, chainStep]

/-- `D_k` is the `(P₂·W)`-power predicted by the recursion; in particular it never vanishes. -/
lemma Dc_eq (a b : ℚ) (k : ℕ) : Dc a b k = (P2x a b * wX) ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Dc_succ, ih, show 2 ^ (k + 1) - 1 = (2 ^ k - 1) * 2 + 1 from by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega]
      ring

lemma Q4x_ne_zero (a b : ℚ) : Q4x a b ≠ 0 := by
  intro h
  have h2 : (1 : ℚ) = 0 := by
    simpa [Q4x] using congrArg (fun p : Polynomial ℚ => p.eval 0) h
  exact one_ne_zero h2

lemma X_sub_one_ne_zero : (X - 1 : Polynomial ℚ) ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial ℚ => p.eval 0) h
  norm_num at h2

lemma X_add_one_ne_zero : (X + 1 : Polynomial ℚ) ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial ℚ => p.eval 0) h
  norm_num at h2

lemma P2x_ne_zero (a b : ℚ) : P2x a b ≠ 0 := by
  rw [P2x]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero X_sub_one_ne_zero Polynomial.X_ne_zero)
    X_add_one_ne_zero) (Q4x_ne_zero a b)

lemma Dc_ne_zero (a b : ℚ) (k : ℕ) : Dc a b k ≠ 0 := by
  rw [Dc_eq]
  exact pow_ne_zero _ (mul_ne_zero (P2x_ne_zero a b) wX_ne_zero)

/-- The restricted pair-chain of `dW` (the `P`-branch coordinates, integrals dropped). -/
def pairStep (a b : ℚ) (uv : RatFunc ℚ × RatFunc ℚ) : RatFunc ℚ × RatFunc ℚ :=
  (rhoQ * (Submission.CDT.dRat uv.1 - uv.2 * P0Q a b / P2Q a b),
   rhoQ * (uv.1 + Submission.CDT.dRat uv.2 - uv.2 * P1Q a b / P2Q a b))

@[simp] lemma pairStep_fst (a b : ℚ) (uv : RatFunc ℚ × RatFunc ℚ) :
    (pairStep a b uv).1
      = rhoQ * (Submission.CDT.dRat uv.1 - uv.2 * P0Q a b / P2Q a b) := rfl

@[simp] lemma pairStep_snd (a b : ℚ) (uv : RatFunc ℚ × RatFunc ℚ) :
    (pairStep a b uv).2
      = rhoQ * (uv.1 + Submission.CDT.dRat uv.2 - uv.2 * P1Q a b / P2Q a b) := rfl

/-- `xQ - 1` is the image of `rX`. -/
lemma xQ_sub_one : xQ - 1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) rX := by
  rw [rX, map_sub, map_one, xQ, RatFunc.algebraMap_X]

/-- `xQ ^ 2 - 2 * xQ` is the image of `wX`. -/
lemma xQ_sq_sub : xQ ^ 2 - 2 * xQ = algebraMap (Polynomial ℚ) (RatFunc ℚ) wX := by
  simp only [wX, map_sub, map_mul, map_pow, map_ofNat, xQ, RatFunc.algebraMap_X]

/-- `rhoQ` is `rX² / wX` read in `ℚ(X)`. -/
lemma rhoQ_eq : rhoQ = (algebraMap (Polynomial ℚ) (RatFunc ℚ) rX) ^ 2
    / algebraMap (Polynomial ℚ) (RatFunc ℚ) wX := by
  rw [rhoQ, ← xQ_sub_one, ← xQ_sq_sub]

end

end Work.C17d
