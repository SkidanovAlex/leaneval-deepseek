import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.LacNatExt.rank_one_add_polyT
import Submission.Work.ORHughesFree.NaturalExtension.rank_ge_const_coeff
import Submission.Work.ORHughesFree.NaturalExtension.rank_le_one_sub_const_ann
import Submission.Work.ORHughesFree.NaturalExtension.sup_const_mul_add_sup_const_ann
import Submission.Work.ORHughesFree.NaturalExtension.exists_mul_t_pow_nonneg
import Submission.Work.ORHughesFree.NaturalExtension.isUnit_skewLaurentT
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.NaturalExtension.ampDefs
import Submission.Work.ORHughesFree.NaturalExtension.sylvesterRank_exists_transport
import Submission.Work.ORHughesFree.NaturalExtension.exists_isNaturalExtension_amplified
import Submission.Work.ORHughesFree.NaturalExtension.amplifiedRank_tauCompatible
import Submission.Work.ORHughesFree.NaturalExtension.coeffElt_skewMatrixEquiv_symm
import Submission.Work.ORHughesFree.NaturalExtension.padToSquare_spec

universe u

/-!
# Uniqueness of the natural extension of a Sylvester rank function

Blueprint of the proof (following [JZLA20, Proposition 3.5 / Proposition 7.7] as proved in
Jaikin-Zapirain's *base change* paper and in D. López-Álvarez's thesis
"Sylvester rank functions, epic division rings and the strong Atiyah conjecture for locally
indicable groups" (UAM 2021), §1.5).

Let `R` be von Neumann regular, `τ` the automorphism encoded by the `Multiplicative ℤ`-action,
`rk` a `τ`-compatible Sylvester rank function on `R`, and `S = R[t^{±1};τ]`.  Let `rkE` be a
Sylvester rank function on `S` which is a natural extension of `rk`, i.e. (a) it restricts to
`rk` on the constants and (b) `rkE (I_n + A t) = n` for every `n × n` matrix `A` over `R`.

1. *Extension of (b) to polynomial matrices.*  From (b) one deduces, by induction on the degree
   and using only the rank axioms (the unit `t^{-1}` and the axiom (SMat4) on block upper
   triangular matrices), that `rkE (I_n + A_1 t + ⋯ + A_k t^k) = n` for all matrices `A_i` over
   `R` (`lacrank_one_add_polyT`, in the module `Work.ORHughesFree.LacNatExt.rank_one_add_polyT`;
   the variant `rank_one_add_polyT` in `Work.ORHughesFree.NaturalExtension.rank_one_add_polyT`
   has the same statement but its auxiliary declarations clash with those of the duality
   development, so the namespace-clean copy is the one imported here).

2. *The squeeze on `1 × 1` matrices.*  Let `p ∈ S`.  For `q ∈ S·p` whose entries are
   polynomials with constant term `c_0` one has `rkE (c_0) ≤ rkE (q) ≤ rkE (p)`: multiply
   `c_0 x q = c_0 (1 + D t)` (`x` a von Neumann inverse of `c_0`, `D ∈ R[t]`) by the full-rank
   matrix `1 + D t` of step 1 and use that multiplying by a square matrix of maximal rank does
   not change the rank (`rank_ge_const_coeff`).  Dually, if `q' p = 0` then
   `rkE (p) ≤ 1 − rkE (c'_0)` by Sylvester's law of nullity (`rank_le_one_sub_const_ann`).

3. *The crucial duality.*  For `p ∈ S` put
   `σ(p) = sup {rk (c_0) : c_0 is the constant term of some polynomial in S·p}` and
   `τ(p) = sup {rk (c_0) : c_0 is the constant term of some polynomial annihilating p}`.
   Then `σ(p) + τ(p) ≥ 1`.  This is the assertion (for the two left ideals `S·p` and `Ann_l(p)`)
   that `lim_i dim(Q_{i-1} ∩ I)/i = sup {rk (a_0) : Σ a_i t^i ∈ I}` of [JZLA20, Proposition 7.2],
   proved by a Fekete/positivity argument on the filtration by degree, and it involves only `rk`,
   not `rkE` (`sup_const_mul_add_sup_const_ann`).

4. Steps 2 and 3 sandwich `rkE (p)` between `σ(p)` and `1 − τ(p)`, which differ by at most `ε`
   for every `ε > 0`; the same holds for `rkE'`, so `rkE (p) = rkE' (p)` (this is
   `oneByOne_eq_of_isNaturalExtension` below).

The general matrix case is reduced to the `1 × 1` case by **amplification**.  The ring `Mat_N(R)`
is again von Neumann regular and carries the entrywise twist, the isomorphism
`skewMatrixEquiv : Mat_N(R)[t^{±1};τ] ⟶ Mat_N(R[t^{±1};τ])` identifies the amplified skew Laurent
ring with the matrix ring, and the amplified rank functions
`A ↦ rk (flattenBlocks A)/N` on `Mat_N(R)` and `rkE` transported through `skewMatrixEquiv` on
`Mat_N(R)[t^{±1};τ]` are again related by `IsNaturalExtension`
(`exists_isNaturalExtension_amplified`).  Hence Step 4 applied over the ring `Mat_N(R)` gives
uniqueness for `N × N` matrices over `R` (an element of `Mat_N(R)[t^{±1};τ]` is exactly an
`N × N` matrix over `R[t^{±1};τ]`), and a general `n × m` matrix is `rank`-preservingly padded to
an `(n+m) × (n+m)` matrix (`padToSquare_spec`).  An arbitrary matrix over `S` is first multiplied
by a power of the unit `t` so that all its coefficients become non-negative
(`exists_mul_t_pow_nonneg`, `isUnit_skewLaurentT`).
-/

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## The `1 × 1` case -/

/-- The product of two `1 × 1` matrices is the `1 × 1` matrix of the product of the entries. -/
lemma oneByOne_mul {R : Type u} [Ring R] (a b : R) :
    oneByOne a * oneByOne b = oneByOne (a * b) := by
  ext i j
  simp [Matrix.mul_apply, oneByOne]

/-- The constant matrix `skewLaurentConst 1 1 (oneByOne a)` is the `1 × 1` matrix with the
constant entry `a`. -/
lemma skewLaurentConst_oneByOne {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (a : R) :
    skewLaurentConst 1 1 (oneByOne a)
      = oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) := by
  ext i j
  simp [skewLaurentConst, oneByOne]

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- **The `1 × 1` case of the uniqueness of the natural extension.**  Two Sylvester rank
functions on `R[t^{±1};τ]` which are natural extensions of the same `τ`-compatible rank
function `rk` agree on every element of `R[t^{±1};τ]` with non-negative powers of `t`. -/
theorem oneByOne_eq_of_isNaturalExtension [VonNeumannRegularRing R] (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {rkE rkE' : SylvesterRank (SkewL R)} (h : IsNaturalExtension rk rkE)
    (h' : IsNaturalExtension rk rkE') (p : SkewL R)
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) :
    rkE.rk 1 1 (oneByOne p) = rkE'.rk 1 1 (oneByOne p) := by
  classical
  -- Step 1: the polynomial version of the `I + A t` condition, for both rank functions.
  have hbE : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)),
      (∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) →
      rkE.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) +
        B * Matrix.diagonal (fun _ => skewLaurentT)) = (n : ℝ) :=
    fun n B hB => lacrank_one_add_polyT rkE h.2 B hB
  have hbE' : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)),
      (∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) →
      rkE'.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) +
        B * Matrix.diagonal (fun _ => skewLaurentT)) = (n : ℝ) :=
    fun n B hB => lacrank_one_add_polyT rkE' h'.2 B hB
  -- The two halves of the squeeze, for the pair `(rkE, rkE')`.
  have key : ∀ ε : ℝ, 0 < ε → rkE.rk 1 1 (oneByOne p) ≤ rkE'.rk 1 1 (oneByOne p) + ε := by
    intro ε hε
    obtain ⟨c₀, c₁, ⟨q, q', hq, hqnn, hqc⟩, ⟨q'', hq'', hq''nn, hq''c⟩, hsum⟩ :=
      sup_const_mul_add_sup_const_ann rk hτ p hp (ε / 2) (by linarith)
    have h1 : rk.rk 1 1 (oneByOne c₀) ≤ rkE'.rk 1 1 (oneByOne p) := by
      have hH1 := rank_ge_const_coeff rkE' hbE' q hqnn
      have hqeq : oneByOne q = oneByOne q' * oneByOne p := by
        rw [hq]
        ext i j
        simp [Matrix.mul_apply, oneByOne]
      calc rk.rk 1 1 (oneByOne c₀)
          = rkE'.rk 1 1 (skewLaurentConst 1 1 (oneByOne c₀)) :=
            (h'.1 1 1 (oneByOne c₀)).symm
        _ = rkE'.rk 1 1 (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c₀)) := by
            congr 1
        _ = rkE'.rk 1 1
              (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (coeffElt q 0))) := by
            rw [hqc]
        _ ≤ rkE'.rk 1 1 (oneByOne q) := hH1
        _ = rkE'.rk 1 1 (oneByOne q' * oneByOne p) := by rw [hqeq]
        _ ≤ rkE'.rk 1 1 (oneByOne p) := rkE'.rk_mul_le_right (oneByOne q') (oneByOne p)
    have h2 : rkE.rk 1 1 (oneByOne p) ≤ 1 - rk.rk 1 1 (oneByOne c₁) := by
      have hH2 := rank_le_one_sub_const_ann rkE hbE hq''nn hq''
      calc rkE.rk 1 1 (oneByOne p)
          ≤ 1 - rkE.rk 1 1
              (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (coeffElt q'' 0))) :=
            hH2
        _ = 1 - rkE.rk 1 1 (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c₁)) := by
            rw [hq''c]
        _ = 1 - rkE.rk 1 1 (skewLaurentConst 1 1 (oneByOne c₁)) := by
            congr 1
        _ = 1 - rk.rk 1 1 (oneByOne c₁) := by rw [h.1 1 1 (oneByOne c₁)]
    linarith
  have key' : ∀ ε : ℝ, 0 < ε → rkE'.rk 1 1 (oneByOne p) ≤ rkE.rk 1 1 (oneByOne p) + ε := by
    intro ε hε
    obtain ⟨c₀, c₁, ⟨q, q', hq, hqnn, hqc⟩, ⟨q'', hq'', hq''nn, hq''c⟩, hsum⟩ :=
      sup_const_mul_add_sup_const_ann rk hτ p hp (ε / 2) (by linarith)
    have h1 : rk.rk 1 1 (oneByOne c₀) ≤ rkE.rk 1 1 (oneByOne p) := by
      have hH1 := rank_ge_const_coeff rkE hbE q hqnn
      have hqeq : oneByOne q = oneByOne q' * oneByOne p := by
        rw [hq]
        ext i j
        simp [Matrix.mul_apply, oneByOne]
      calc rk.rk 1 1 (oneByOne c₀)
          = rkE.rk 1 1 (skewLaurentConst 1 1 (oneByOne c₀)) := (h.1 1 1 (oneByOne c₀)).symm
        _ = rkE.rk 1 1 (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c₀)) := by
            congr 1
        _ = rkE.rk 1 1
              (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (coeffElt q 0))) := by
            rw [hqc]
        _ ≤ rkE.rk 1 1 (oneByOne q) := hH1
        _ = rkE.rk 1 1 (oneByOne q' * oneByOne p) := by rw [hqeq]
        _ ≤ rkE.rk 1 1 (oneByOne p) := rkE.rk_mul_le_right (oneByOne q') (oneByOne p)
    have h2 : rkE'.rk 1 1 (oneByOne p) ≤ 1 - rk.rk 1 1 (oneByOne c₁) := by
      have hH2 := rank_le_one_sub_const_ann rkE' hbE' hq''nn hq''
      calc rkE'.rk 1 1 (oneByOne p)
          ≤ 1 - rkE'.rk 1 1
              (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (coeffElt q'' 0))) :=
            hH2
        _ = 1 - rkE'.rk 1 1 (oneByOne (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c₁)) := by
            rw [hq''c]
        _ = 1 - rkE'.rk 1 1 (skewLaurentConst 1 1 (oneByOne c₁)) := by
            congr 1
        _ = 1 - rk.rk 1 1 (oneByOne c₁) := by rw [h'.1 1 1 (oneByOne c₁)]
    linarith
  refine le_antisymm ?_ ?_
  · by_contra hcon
    push_neg at hcon
    have hkey := key ((rkE.rk 1 1 (oneByOne p) - rkE'.rk 1 1 (oneByOne p)) / 2) (by linarith)
    linarith
  · by_contra hcon
    push_neg at hcon
    have hkey := key' ((rkE'.rk 1 1 (oneByOne p) - rkE.rk 1 1 (oneByOne p)) / 2) (by linarith)
    linarith

/-! ## The matrix case, by amplification -/

/-- **The uniqueness of the natural extension for matrices with non-negative powers of `t`.**

The `n × m` matrix `A` over `R[t^{±1};τ]` is padded to the square `(n+m) × (n+m)` matrix
`padToSquare A` (rank-preservingly), and the `1 × 1` case is applied to the corresponding element
of `Mat_{n+m}(R)[t^{±1};τ]`. -/
theorem matrix_eq_of_isNaturalExtension [VonNeumannRegularRing R] (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {rkE rkE' : SylvesterRank (SkewL R)} (h : IsNaturalExtension rk rkE)
    (h' : IsNaturalExtension rk rkE') {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL R))
    (hA : ∀ i j, ∀ k : ℤ, k < 0 → coeffElt (A i j) k = 0) :
    rkE.rk n m A = rkE'.rk n m A := by
  classical
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hN
  · -- `n = m = 0`: the only matrix is `0`.
    have hn0 : n = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hn0
    subst hm0
    have hA0 : A = 0 := by
      ext i j
      exact Fin.elim0 i
    rw [hA0, rkE.rk_zero, rkE'.rk_zero]
  · -- The main case: `N := n + m > 0`.
    obtain ⟨hpadpoly, hpadrk⟩ := padToSquare_spec rkE A hA
    obtain ⟨-, hpadrk'⟩ := padToSquare_spec rkE' A hA
    -- The amplification is a rank function on the (von Neumann regular) matrix ring.
    haveI : VonNeumannRegularRing (Matrix (Fin (n + m)) (Fin (n + m)) R) :=
      StarRegular.vonNeumannRegularRing_matrix (n + m)
    obtain ⟨rkEN, hENformula, hENnat⟩ := exists_isNaturalExtension_amplified h (n + m) hN
    obtain ⟨rkEN', hEN'formula, hEN'nat⟩ := exists_isNaturalExtension_amplified h' (n + m) hN
    have hτN := amplifiedRank_tauCompatible (R := R) hτ (n + m) hN
    -- The element of `Mat_{n+m}(R)[t^{±1};τ]` corresponding to the padded matrix.
    set X : SkewL (Matrix (Fin (n + m)) (Fin (n + m)) R) :=
      (skewMatrixEquiv R (n + m)).symm (padToSquare A) with hX
    have hXpoly : ∀ k : ℤ, k < 0 → coeffElt X k = 0 := by
      intro k hk
      rw [hX, coeffElt_skewMatrixEquiv_symm]
      ext i j
      simp only [coeffMat_apply, Matrix.zero_apply]
      exact hpadpoly i j k hk
    have hmapX : (oneByOne X).map (skewMatrixEquiv R (n + m)) = oneByOne (padToSquare A) := by
      rw [hX]
      apply Matrix.ext
      intro i j
      simp only [Matrix.map_apply, oneByOne]
      exact RingEquiv.apply_symm_apply (skewMatrixEquiv R (n + m)) (padToSquare A)
    have hkey := oneByOne_eq_of_isNaturalExtension (R := Matrix (Fin (n + m)) (Fin (n + m)) R)
      (amplifiedRank rk (n + m) hN) hτN hENnat hEN'nat X hXpoly
    have h1 : rkEN.rk 1 1 (oneByOne X)
        = rkE.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ) := by
      rw [hENformula 1 1 (oneByOne X), hmapX, MatrixBlocks.flattenBlocks_oneByOne,
        RankAPI.rk_reindex rkE ((finCongr (Nat.one_mul (n + m))).symm)
          ((finCongr (Nat.one_mul (n + m))).symm) (padToSquare A)]
    have h1' : rkEN'.rk 1 1 (oneByOne X)
        = rkE'.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ) := by
      rw [hEN'formula 1 1 (oneByOne X), hmapX, MatrixBlocks.flattenBlocks_oneByOne,
        RankAPI.rk_reindex rkE' ((finCongr (Nat.one_mul (n + m))).symm)
          ((finCongr (Nat.one_mul (n + m))).symm) (padToSquare A)]
    have hNne : ((n + m : ℕ) : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast hN
      exact ne_of_gt hpos
    have hfin : rkE.rk (n + m) (n + m) (padToSquare A)
        = rkE'.rk (n + m) (n + m) (padToSquare A) := by
      have h2 : rkE.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ)
          = rkE'.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ) := by
        rw [← h1, ← h1', hkey]
      have h4 : (rkE.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ))
            * ((n + m : ℕ) : ℝ)
          = (rkE'.rk (n + m) (n + m) (padToSquare A) / ((n + m : ℕ) : ℝ))
            * ((n + m : ℕ) : ℝ) := by
        rw [h2]
      simpa only [div_mul_cancel₀ _ hNne] using h4
    rw [← hpadrk, ← hpadrk', hfin]

theorem naturalExtension_unique {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R) (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A) {rkE rkE' : SylvesterRank (SkewMonoidAlgebra R (Multiplicative ℤ))} (h : IsNaturalExtension rk rkE) (h' : IsNaturalExtension rk rkE') : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra R (Multiplicative ℤ))), rkE.rk n m A = rkE'.rk n m A := by
  intro n m A
  classical
  -- Multiply by a large power of the unit `t` to make all coefficients non-negative.
  obtain ⟨k, hk⟩ := exists_mul_t_pow_nonneg A
  obtain ⟨u, hu⟩ := isUnit_skewLaurentT (R := R)
  set D : Matrix (Fin m) (Fin m) (SkewL R) := Matrix.diagonal (fun _ : Fin m => ↑(u ^ k)) with hD
  set D' : Matrix (Fin m) (Fin m) (SkewL R) :=
    Matrix.diagonal (fun _ : Fin m => ↑((u ^ k)⁻¹)) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal]
    have hfun : (fun i : Fin m => (↑(u ^ k) : SkewL R) * ↑((u ^ k)⁻¹)) = fun _ => 1 := by
      funext i
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hfun, Matrix.diagonal_one]
  have hDval : D = Matrix.diagonal (fun _ : Fin m => (skewLaurentT (R := R)) ^ k) := by
    rw [hD]
    congr 1
    funext i
    rw [Units.val_pow_eq_pow_val, hu]
  have hA' : ∀ i j, ∀ l : ℤ, l < 0 → coeffElt ((A * D) i j) l = 0 := by
    rw [hDval]
    exact hk
  have hpresE : rkE.rk n m (A * D) = rkE.rk n m A :=
    SylvesterRank.rk_eq_of_mul_right_inverse rkE A D D' hDD'
  have hpresE' : rkE'.rk n m (A * D) = rkE'.rk n m A :=
    SylvesterRank.rk_eq_of_mul_right_inverse rkE' A D D' hDD'
  have hmain := matrix_eq_of_isNaturalExtension rk hτ h h' (A * D) hA'
  rw [hpresE, hpresE'] at hmain
  exact hmain

end Work.ORHughesFree.NaturalExtension
