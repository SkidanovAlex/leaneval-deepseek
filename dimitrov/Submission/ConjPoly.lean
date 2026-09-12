import Mathlib
import Submission.Minpoly
import Submission.Dictionary
import Submission.Conjugates
import Submission.Powers
import Submission.RootProd
import Submission.RootCorr

/-!
# Complex factorization of the minimal polynomial over the conjugate set

Let `S := conjugateValues α ⊆ ℂ` be the (distinct) complex conjugates of an
algebraic integer `α` (the values `σ α` over all `σ : K →+* ℂ`).  This module
proves:

* `pow2`/`pow4` commute with change of rings (`pow2_map`, `pow4_map`);
* over `ℂ`, the minimal polynomial equals `∏ z ∈ S (X - z)`
  (`minpoly_complex_eq_prod`), and hence
* `natDegree (minpoly ℤ α) = |S|` (`minpoly_natDegree_eq_card`);
* the product identities `pow2 (∏ z∈S (X - z²)) = ∏ z∈S (X - z⁴)` and
  `pow4 (∏ z∈S (X - z)) = ∏ z∈S (X - z⁴)` over `ℂ` for any finite `S`.

These identities are the bridge between the algebraic polynomials `pow2 P`,
`pow4 P` and the conjugates `σ α` (their roots are the squares / fourth powers
of the conjugates).

## IMPORTANT CORRECTION to `pow2_map` / `pow4_map` (module author's attention)

The statements below carry the extra hypothesis `P.Monic`.  The fully general
statements without it are **false**: take `P := 3X + 1 ∈ ℤ[X]` and
`f : ℤ →+* ZMod 3` (reduction mod 3).  Then `natDegree P = 1` while
`natDegree (P.map f) = natDegree 1 = 0`, and a direct computation gives
`(pow2 P).map f = C (-1)` while `pow2 (P.map f) = C 1` in `(ZMod 3)[X]`,
which are unequal (as `-1 ≠ 1` in `ZMod 3`).  The obstruction is exactly that
`pow2` scales by `(-1) ^ natDegree`, which is only preserved by `map f` when
the degree is preserved; for a **monic** `P` (so the leading coefficient `1`
maps to `1 ≠ 0`) the degree is preserved and the commutation holds.  Every use
of these lemmas in this project (`minpoly ℤ α` and its `pow2`/`pow4`
iterates, all monic) is covered by the monic hypothesis.

## Proof plans

`pow2_map` / `pow4_map`: use `ext n`, `rw [coeff_map, evenPart_coeff]`, and the
definition of `pow2`/`pow4` (which is built from `evenPart`, scalar multiplication
by `(-1)^d`, multiplication and `comp (-X)`); all of these commute with `map f`
(`map_mul`, `map_comp`, `map_smul`, `coeff_map`, `evenPart_coeff`).
Alternatively prove it by induction on the support, or directly via the map
version of `pow2_expand` and `expand_injective`.

`minpoly_complex_eq_prod`:  Let `p := minpoly ℤ α` and `p̅ := p.map (algebraMap ℤ ℂ)`.
Facts available:
* the *roots* of `p̅` in `ℂ` are exactly `S`:
  `rootSet_int_minpoly_eq_conjugateValues` (Submission.Minpoly) gives
  `p.rootSet ℂ = (conjugateValues α : Set ℂ)`, and roots are unchanged by the map
  `ℤ → ℂ` (`rootSet_int_eq_rootSet_rat` + `aroots_map` as in that module; or
  directly: `(p.map (algebraMap ℤ ℂ)).rootSet ℂ = p.rootSet ℂ` — a roots-preservation
  lemma you may need to state/prove using `rootSet_def` and `aroots_map`).
* `p̅` is monic (`Polynomial.Monic.map`).
* `p̅` is separable and splits over `ℂ` (the minimal polynomial of an algebraic
  number over a characteristic-zero field is squarefree/separable; over the
  algebraically closed field `ℂ` every polynomial splits).  For splitting:
  `minpoly ℚ α` splits over `ℂ` (`IsAlgClosed.splits`), and `p̅` is its image
  under `ℚ → ℂ` (`minpoly_rat_eq_map_int`, `map_map`).
* Hence (this is the key step) a monic polynomial over `ℂ` that splits with
  exactly its root set as simple roots equals `∏ z ∈ S (X - z)`.
  Standard route: `p̅.Splits` gives `p̅.natDegree = p̅.roots.card`
  (`Polynomial.Splits.natDegree_eq_card_roots`), separability gives
  `p̅.roots.Nodup` (`Polynomial.nodup_roots`), the root set of `p̅` is `S`, so
  `p̅.roots.toFinset = S` as `Finset`s (use `Finset.coe_inj`), and finally use
  the splitting-factorization `p̅ = ∏ r ∈ p̅.roots, (X - C r)` — search for
  `Splits.prod_roots_eq_self` / `eq_prod_roots_of_monic` (as used e.g. in
  `FieldTheory/AbelRuffini.lean`, `FieldTheory/KummerExtension.lean`).

`minpoly_natDegree_eq_card`: combine `minpoly_complex_eq_prod` with the degree of
`∏ z∈S (X - z)` being `|S|` (as in `natDegree_prod_X_sub_C` /
`natDegree_prod_of_monic` in `Submission.RootProd` / mathlib) and
`Polynomial.natDegree_map`.

`pow2_prod_sq`: prove directly with `expand 2` on both sides and
`pow2_expand`.  LHS: `expand 2 (pow2 F) = (-1)^d • (F * F.comp (-X))` with
`F := ∏ z∈S (X - C (z^2))`, `d := F.natDegree`; compute `F.comp (-X)` via
`prod_comp`, `sub_comp`, `X_comp`, `C_comp`, and show the RHS expands to
`expand 2 (∏ z∈S (X - C (z^4)))`; conclude with `expand_injective`
(`Polynomial.expand_injective (by norm_num : 0 < 2)`), as in the proofs inside
`Submission.RootProd`.  Alternatively: apply `pow2_eq_prod_sub_sq`
(Submission.RootProd) to the polynomial `F` whose roots are the *squares* — but
note the product `∏ z∈S (X - C (z^2))` is over the same index set `S` with
arguments `z^2`, so the direct expand-argument is cleaner.

`pow4_prod`: `pow4 F = pow2 (pow2 F)`; use `pow2_eq_prod_sub_sq` (RootProd)
once and `pow2_prod_sq` once.

You may add helper lemmas. Do NOT change the statements. No sorries may remain.
-/

noncomputable section

open Polynomial
open scoped Complex Polynomial

namespace Submission.ConjPoly

open Submission.Powers
open Submission.Conjugates
open Submission.RootProd
open Submission.RootCorr

variable {K : Type*} [Field K] [NumberField K]

/-- The degree of `∏_{z∈S}(X - C (a z))` is `|S|`, for any values `a z`. -/
lemma natDegree_prod_X_sub_C_of (S : Finset ℂ) (a : ℂ → ℂ) :
    (S.prod fun z : ℂ => X - C (a z)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod S (fun z : ℂ => X - C (a z))]
  · simp
  · intro z hz
    exact (Polynomial.monic_X_sub_C (a z)).ne_zero

/-- Applying `pow2` to the product of the linear factors of the values
`(a z)` yields the product of the linear factors of the *squares* `(a z)²`
(this is a purely formal identity: the `a z` need not be distinct). -/
lemma pow2_prod_X_sub_C_sq (S : Finset ℂ) (a : ℂ → ℂ) :
    pow2 (S.prod (fun z : ℂ => X - C (a z))) = S.prod (fun z : ℂ => X - C ((a z) ^ 2)) := by
  classical
  let Q : ℂ[X] := S.prod fun z : ℂ => X - C (a z)
  let B : ℂ[X] := S.prod fun z : ℂ => X + C (a z)
  let W : ℂ[X] := S.prod fun z : ℂ => X - C ((a z) ^ 2)
  have hdeg : Q.natDegree = S.card := by
    dsimp [Q]
    exact natDegree_prod_X_sub_C_of S a
  have hfac : ∀ z : ℂ, (X - C (a z)).comp (-X) = (-1 : ℂ[X]) * (X + C (a z)) := by
    intro z
    have h1 : (X - C (a z)).comp (-X) = -X - C (a z) := by simp
    rw [h1]
    ring
  have hcompB : Q.comp (-X) = (-1 : ℂ[X]) ^ S.card * B := by
    dsimp [Q, B]
    calc
      (S.prod fun z : ℂ => X - C (a z)).comp (-X)
          = S.prod fun z : ℂ => (X - C (a z)).comp (-X) := by rw [prod_comp]
      _ = S.prod fun z : ℂ => (-1 : ℂ[X]) * (X + C (a z)) := by
              apply Finset.prod_congr rfl
              intro z hz
              exact hfac z
      _ = (S.prod fun _ : ℂ => (-1 : ℂ[X])) * S.prod (fun z : ℂ => X + C (a z)) := by
              rw [Finset.prod_mul_distrib]
      _ = (-1 : ℂ[X]) ^ S.card * S.prod (fun z : ℂ => X + C (a z)) := by
              simp
  have hsq : (-1 : ℂ[X]) ^ S.card * (-1 : ℂ[X]) ^ S.card = 1 := by
    rw [← pow_add]
    have : S.card + S.card = 2 * S.card := by omega
    rw [this, pow_mul]
    simp
  have hCpow : C ((-1 : ℂ) ^ S.card) = (-1 : ℂ[X]) ^ S.card := by
    rw [C_pow]
    congr 1
    simp
  have hsmulconv : (-1 : ℂ) ^ S.card • (Q * Q.comp (-X)) =
        (-1 : ℂ[X]) ^ S.card * (Q * Q.comp (-X)) := by
    rw [smul_eq_C_mul]
    rw [hCpow]
  have hL : expand ℂ 2 (pow2 Q) = Q * B := by
    rw [pow2_expand]
    rw [hdeg]
    rw [hsmulconv]
    rw [hcompB]
    have hre : (-1 : ℂ[X]) ^ S.card * (Q * ((-1 : ℂ[X]) ^ S.card * B)) = Q * B := by
      calc
        (-1 : ℂ[X]) ^ S.card * (Q * ((-1 : ℂ[X]) ^ S.card * B))
            = Q * ((-1 : ℂ[X]) ^ S.card * ((-1 : ℂ[X]) ^ S.card * B)) := by ring
        _ = Q * (((-1 : ℂ[X]) ^ S.card * (-1 : ℂ[X]) ^ S.card) * B) := by ring
        _ = Q * B := by
              rw [hsq]
              simp
    exact hre
  have hG : expand ℂ 2 W = Q * B := by
    calc
      expand ℂ 2 W = W.comp (X ^ 2) := by rw [Polynomial.expand_eq_comp_X_pow 2]
      _ = (S.prod fun z : ℂ => X - C ((a z) ^ 2)).comp (X ^ 2) := by rfl
      _ = S.prod fun z : ℂ => (X - C ((a z) ^ 2)).comp (X ^ 2) := by rw [prod_comp]
      _ = S.prod fun z : ℂ => X ^ 2 - C ((a z) ^ 2) := by
              apply Finset.prod_congr rfl
              intro z hz
              simp
      _ = S.prod fun z : ℂ => (X - C (a z)) * (X + C (a z)) := by
              apply Finset.prod_congr rfl
              intro z hz
              have hC : C ((a z) ^ 2) = (C (a z)) ^ 2 := by rw [map_pow]
              rw [hC]
              ring
      _ = (S.prod fun z : ℂ => X - C (a z)) * S.prod (fun z : ℂ => X + C (a z)) := by
              rw [Finset.prod_mul_distrib]
      _ = Q * B := by
              rfl
  have hE : expand ℂ 2 (pow2 Q) = expand ℂ 2 W := by
    rw [hL, hG]
  have hE2 : pow2 Q = W := (expand_inj (R := ℂ) (p := 2) (by norm_num : 0 < 2)).1 hE
  dsimp [Q, W] at hE2
  exact hE2

/-- `pow2` commutes with extending scalars, for a monic polynomial `P`.

The statement without `P.Monic` is false in general (see module header); for
monic `P` the degree is preserved by `map f` and everything commutes. -/
theorem pow2_map {R S : Type*} [CommRing R] [CommRing S] (P : R[X]) (f : R →+* S)
    (hP : P.Monic) :
    (pow2 P).map f = pow2 (P.map f) := by
  classical
  by_cases hS : Nontrivial S
  · let d : ℕ := P.natDegree
    have hnd : (P.map f).natDegree = d := by
      dsimp [d]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · exact Polynomial.natDegree_map_le
      · rw [coeff_map]
        have hl : P.coeff P.natDegree = 1 := by
          change P.leadingCoeff = 1
          exact hP.leadingCoeff
        rw [hl]
        exact (map_one f).symm ▸ one_ne_zero
    have he1 : expand S 2 ((pow2 P).map f) = expand S 2 (pow2 (P.map f)) := by
      calc
        expand S 2 ((pow2 P).map f)
            = (expand R 2 (pow2 P)).map f := by rw [Polynomial.map_expand]
        _ = ((-1 : R) ^ P.natDegree • (P * P.comp (-X))).map f := by
            rw [pow2_expand]
        _ = (-1 : S) ^ P.natDegree • ((P.map f) * (P.comp (-X)).map f) := by
            have hfpow : f ((-1 : R) ^ P.natDegree) = (-1 : S) ^ P.natDegree := by
              rw [map_pow]
              rw [map_neg]
              simp
            rw [Polynomial.map_smul, Polynomial.map_mul, hfpow]
        _ = (-1 : S) ^ P.natDegree • ((P.map f) * (P.map f).comp (-X)) := by
            rw [Polynomial.map_comp]
            simp
        _ = expand S 2 (pow2 (P.map f)) := by
            rw [pow2_expand]
            rw [hnd]
    exact (expand_injective (R := S) (n := 2) (by norm_num : 0 < 2)) he1
  · have hsub : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    ext n
    exact hsub.elim _ _

/-- `pow4` commutes with extending scalars, for a monic polynomial `P`
(same caveat as `pow2_map`). -/
theorem pow4_map {R S : Type*} [CommRing R] [CommRing S] (P : R[X]) (f : R →+* S)
    (hP : P.Monic) :
    (pow4 P).map f = pow4 (P.map f) := by
  rw [pow4, pow4]
  rw [pow2_map (pow2 P) f (pow2_monic P hP)]
  rw [pow2_map P f hP]

/-- Over `ℂ`, the minimal polynomial of `α` splits into the product of the
linear factors `X - z` over its distinct conjugates `z`. -/
theorem minpoly_complex_eq_prod (α : K) (hα : IsIntegral ℤ α) :
    (minpoly ℤ α).map (algebraMap ℤ ℂ) =
      (conjugateValues α).prod (fun z : ℂ => X - C z) := by
  classical
  let P : ℂ[X] := (minpoly ℤ α).map (algebraMap ℤ ℂ)
  let S : Finset ℂ := conjugateValues α
  have hαℚ : IsIntegral ℚ α := IsIntegral.tower_top hα
  have hRat : (minpoly ℚ α).map (algebraMap ℚ ℂ) = P := by
    dsimp [P]
    calc
      (minpoly ℚ α).map (algebraMap ℚ ℂ)
          = ((minpoly ℤ α).map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) := by
              rw [Submission.Minpoly.minpoly_rat_eq_map_int α hα]
      _ = (minpoly ℤ α).map (algebraMap ℤ ℂ) := by
              rw [Polynomial.map_map]
              congr 1
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hmonic : P.Monic := by
    dsimp [P]
    exact (minpoly.monic hα).map (algebraMap ℤ ℂ)
  have hsep : P.Separable := by
    have hIr : Irreducible (minpoly ℚ α) := minpoly.irreducible hαℚ
    have hsepℚ : (minpoly ℚ α).Separable := hIr.separable
    have hsepℂ : ((minpoly ℚ α).map (algebraMap ℚ ℂ)).Separable :=
      Polynomial.Separable.map hsepℚ
    simpa [hRat] using hsepℂ
  have hnod : P.roots.Nodup := Polynomial.nodup_roots hsep
  have hset : (P.roots.toFinset : Set ℂ) = (S : Set ℂ) := by
    calc
      (P.roots.toFinset : Set ℂ) = (minpoly ℤ α).rootSet ℂ := by
        dsimp [P]
        simp [rootSet_def, aroots_def]
      _ = (conjugateValues α : Set ℂ) := by
        exact Submission.Minpoly.rootSet_int_minpoly_eq_conjugateValues α hα
      _ = (S : Set ℂ) := rfl
  have hfinset : P.roots.toFinset = S := Finset.coe_inj.mp hset
  have hms : P.roots = S.1 := by
    apply Multiset.Nodup.toFinset_inj hnod S.2
    simpa [Multiset.toFinset_eq S.2] using hfinset
  calc
    (minpoly ℤ α).map (algebraMap ℤ ℂ) = P := rfl
    _ = (P.roots.map (fun z : ℂ => X - C z)).prod :=
        Splits.eq_prod_roots_of_monic hsplit hmonic
    _ = (S.1.map (fun z : ℂ => X - C z)).prod := by rw [hms]
    _ = S.prod (fun z : ℂ => X - C z) := rfl
    _ = (conjugateValues α).prod (fun z : ℂ => X - C z) := rfl

/-- The degree of the minimal polynomial equals the number of distinct
conjugates. -/
theorem minpoly_natDegree_eq_card (α : K) (hα : IsIntegral ℤ α) :
    (minpoly ℤ α).natDegree = (conjugateValues α).card := by
  classical
  let P : ℂ[X] := (minpoly ℤ α).map (algebraMap ℤ ℂ)
  let S : Finset ℂ := conjugateValues α
  have hnd_le : P.natDegree ≤ (minpoly ℤ α).natDegree := by
    dsimp [P]
    exact Polynomial.natDegree_map_le
  have hcoeff : P.coeff ((minpoly ℤ α).natDegree) ≠ 0 := by
    dsimp [P]
    rw [coeff_map]
    rw [← Polynomial.leadingCoeff]
    rw [(minpoly.monic hα).leadingCoeff]
    norm_num
  have hdeg : (minpoly ℤ α).natDegree = P.natDegree := by
    exact (Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnd_le hcoeff).symm
  have hcard : P.natDegree = S.card := by
    calc
      P.natDegree = ((minpoly ℤ α).map (algebraMap ℤ ℂ)).natDegree := rfl
      _ = (S.prod fun z : ℂ => X - C z).natDegree := by
        rw [minpoly_complex_eq_prod α hα]
      _ = S.card := by
        dsimp [S]
        exact Submission.RootProd.natDegree_prod_X_sub_C (conjugateValues α)
  calc
    (minpoly ℤ α).natDegree = P.natDegree := hdeg
    _ = S.card := hcard
    _ = (conjugateValues α).card := rfl

/-- Squaring the roots again squares the factors once more:
`pow2 (∏ z∈S (X - z²)) = ∏ z∈S (X - z⁴)` over `ℂ`. -/
theorem pow2_prod_sq (S : Finset ℂ) :
    pow2 (S.prod (fun z : ℂ => X - C (z ^ 2))) = S.prod (fun z : ℂ => X - C (z ^ 4)) := by
  have h := pow2_prod_X_sub_C_sq S (fun z : ℂ => z ^ 2)
  convert h using 1
  apply Finset.prod_congr rfl
  intro z hz
  congr 1
  ring_nf

/-- Fourth powers of the roots: `pow4 (∏ z∈S (X - z)) = ∏ z∈S (X - z⁴)`. -/
theorem pow4_prod (S : Finset ℂ) :
    pow4 (S.prod (fun z : ℂ => X - C z)) = S.prod (fun z : ℂ => X - C (z ^ 4)) := by
  rw [pow4]
  rw [pow2_prod_X_sub_C_sq S (fun z : ℂ => z)]
  have h := pow2_prod_X_sub_C_sq S (fun z : ℂ => z ^ 2)
  convert h using 1
  apply Finset.prod_congr rfl
  intro z hz
  congr 1
  ring_nf

end Submission.ConjPoly

end
