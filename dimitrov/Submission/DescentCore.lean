import Mathlib
import Submission.Minpoly
import Submission.Dictionary
import Submission.Conjugates
import Submission.Powers
import Submission.ConjPoly
import Submission.RootProd

/-!
# The master-structure case split (core)

Let `P := minpoly ℤ α` (monic irreducible) and `P₂ := pow2 P`.  The engine of
the proof of Dimitrov's theorem can run only when `P₂` is irreducible (the
algebraic dichotomy `pow4 P = pow2 P` requires it).  This module proves the
case split that covers everything else:

> **`pow2_irreducible_or_negclosed`**: either `pow2 (minpoly ℤ α)` is
> irreducible, or the set `S := conjugateValues α` of conjugates of `α` is
> closed under negation (`-z ∈ S` for all `z ∈ S`).

In the second case one descends to `β := α²` (degree and phase count halve:
see `Submission.DescentCount`), which is why the case split closes the
induction.

## Mathematical proof of the core lemma (¬ irreducible ⟹ neg-closed)

Set `S := conjugateValues α` (so `P̅ = ∏ z∈S (X - C z)` over `ℂ`,
`Submission.ConjPoly.minpoly_complex_eq_prod`), `β := α²`,
`Q := minpoly ℤ β`, `S₂ := conjugateValues β`, and `P₂ := pow2 P`.

1. **Products.**  From `minpoly_complex_eq_prod` for `α` and the map-commutation
   `pow2_map`, plus `pow2_eq_prod_sub_sq` (Submission.RootProd):
   `P̅₂ := (pow2 P).map (algebraMap ℤ ℂ) = ∏ z∈S (X - C (z ^ 2))`.
   From `minpoly_complex_eq_prod` for `β` (needs `hβ : IsIntegral ℤ (α^2)`,
   obtainable as `hα.pow`):
   `Q̅ := Q.map (algebraMap ℤ ℂ) = ∏ w∈S₂ (X - C w)`.
   Finally `S₂ = S.image (fun z => z ^ 2)` (`Submission.Descent.conjugateValues_sq`),
   so every `w ∈ S₂` has at least one preimage `z ∈ S` with `w = z²`.

2. **`Q` divides `P₂` over `ℚ`.**  Show `aeval β P₂ = 0` in `K`: from
   `aeval α (minpoly ℤ α) = 0` (`minpoly_int_aeval`) and the square-evaluation
   identity `pow2_eval_sq` (in `Submission.Powers`; you may need to map `P₂` to
   `K[X]` first via `(pow2 P).map (algebraMap ℤ K)` and `pow2_map`):
   `P₂` vanishes at `β`.  Hence the minimal polynomial of `β` over `ℚ` divides
   `P₂` in `ℚ[X]` (standard: a polynomial over a field vanishing at `β` is a
   multiple of the minimal polynomial — search for `minpoly.dvd`, or prove it
   from the fact that `minpoly ℚ β` is the monic generator of the kernel of the
   evaluation homomorphism `ℚ[X] → K`, `X ↦ β`).  So there is
   `R : ℚ[X]` with `P₂ = Q' * R` where `Q' := Q.map (algebraMap ℤ ℚ)`.

3. **`P₂` is `Q` or `Q²`.**  Map the factorization of step 2 to `ℂ` and cancel
   `Q̅` in the product identities of step 1 (they are equal polynomials, and
   `Q̅ ≠ 0`).  Each value `w ∈ S₂` occurs as `w = z²` for at most two elements
   `z ∈ S` (the preimages of `w` under squaring in `ℂ` are `±√w`), so the
   multiplicity of the factor `(X - w)` in `P̅₂` is `1` or `2`.  Consequently
   `R̅ = ∏ w∈T (X - C w)` for `T := {w ∈ S₂ | multiplicity is 2} ⊆ S₂`, i.e.
   `R̅` is a monic polynomial with *simple roots all contained in the root set
   of the irreducible polynomial* `Q̅`.  Because `R : ℚ[X]` (equivalently every
   irreducible factor of `R` over `ℚ` equals `Q`), and
   `natDegree R ≤ natDegree Q` (since `natDegree P₂ = natDegree Q * (1 or 2)`:
   `natDegree P₂ = natDegree P` by `pow2_natDegree`, `natDegree Q = |S₂|`, and
   `|S| ≤ 2 |S₂|` as each value has at most two preimages), conclude `R = 1` or
   `R = Q'`; hence `P₂ = Q'` or `P₂ = Q' ^ 2` in `ℚ[X]` (equivalently in
   `ℤ[X]` for the monic polynomials `P₂` and `Q`).

4. **Conclude.**  If `P₂ = Q` then `P₂` is irreducible (it is the minimal
   polynomial of `β`), contradicting the hypothesis; hence `P₂ = Q²`.  Then
   for any `z₀ ∈ S`, the factor `(X - C (z₀²))` divides `P̅₂`; but `P̅₂ = Q̅²`
   and `z₀² ∈ S₂` is a root of `Q̅`, so `(X - C (z₀²))²` divides `P̅₂`; from
   `P̅₂ = (X - C (z₀²)) · F` with `F := ∏ z ∈ S.erase z₀ (X - C (z ^ 2))` and
   `(X - C (z₀²)) ∣ F` (divisibility in `ℂ[X]`) we get `F(z₀²) = 0`, so some
   factor of `F` vanishes: `∃ z₁ ≠ z₀, z₁² = z₀²`, and `z₁ = -z₀`
   (over `ℂ`: `z₁² = z₀²` with `z₁ ≠ z₀` forces `z₁ = -z₀`).  Hence
   `-z₀ ∈ S`.

You may add helper lemmas.  Do NOT change the statement.  No sorries may
remain in this file.
-/

noncomputable section

open Polynomial
open scoped Complex Polynomial
open Submission.ConjPoly
open Submission.RootProd
open Submission.Minpoly

namespace Submission.Descent

open Submission.Conjugates
open Submission.Powers

variable {K : Type*} [Field K] [NumberField K]

/-- `aeval (α^2) (pow2 (minpoly ℤ α)) = 0` in `K`. -/
lemma pow2_aeval_sq_zero (α : K) (hα : IsIntegral ℤ α) :
    aeval (α ^ 2) (pow2 (minpoly ℤ α)) = 0 := by
  classical
  let PK : K[X] := (minpoly ℤ α).map (algebraMap ℤ K)
  have hPKpow2 : (pow2 (minpoly ℤ α)).map (algebraMap ℤ K) = pow2 PK := by
    simpa [PK] using pow2_map (minpoly ℤ α) (algebraMap ℤ K) (minpoly_int_monic α hα)
  have heval0 : eval α PK = 0 := by
    dsimp [PK]
    rw [Polynomial.eval_map]
    exact minpoly_int_aeval α
  have hsmul : eval (α ^ 2) (pow2 PK) =
      (-1 : K) ^ PK.natDegree • (eval α PK * eval (-α) PK) := pow2_eval_sq PK α
  have hsmul0 : eval (α ^ 2) (pow2 PK) = 0 := by
    rw [hsmul, heval0]
    simp
  have hmain : eval (α ^ 2) ((pow2 (minpoly ℤ α)).map (algebraMap ℤ K)) = 0 := by
    rw [hPKpow2]
    exact hsmul0
  calc
    aeval (α ^ 2) (pow2 (minpoly ℤ α))
        = eval₂ (algebraMap ℤ K) (α ^ 2) (pow2 (minpoly ℤ α)) := by
          exact Polynomial.aeval_def (α ^ 2) (pow2 (minpoly ℤ α))
    _ = eval (α ^ 2) ((pow2 (minpoly ℤ α)).map (algebraMap ℤ K)) := by
          exact (Polynomial.eval_map (algebraMap ℤ K) (α ^ 2)).symm
    _ = 0 := hmain

/-- `α²` is a root of `pow2 (minpoly ℤ α)` viewed over `ℚ`. -/
lemma pow2_aeval_rat_sq_zero (α : K) (hα : IsIntegral ℤ α) :
    Polynomial.aeval (α ^ 2) ((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap ℚ (α ^ 2) (pow2 (minpoly ℤ α))]
  exact pow2_aeval_sq_zero α hα

/-- `minpoly ℚ (α^2)` divides `pow2 (minpoly ℤ α)` over `ℚ`. -/
lemma pow2_rat_dvd_factor (α : K) (hα : IsIntegral ℤ α) :
    ∃ R : ℚ[X], (pow2 (minpoly ℤ α)).map (algebraMap ℤ ℚ) = minpoly ℚ (α ^ 2) * R := by
  rcases minpoly.dvd ℚ (α ^ 2) (pow2_aeval_rat_sq_zero α hα) with ⟨R, hR⟩
  exact ⟨R, hR⟩

/-- Over `ℂ`, `pow2 (minpoly ℤ α)` is the product of the `X - z²` over the
conjugates `z` of `α`. -/
lemma pow2_complex_prod_sq (α : K) (hα : IsIntegral ℤ α) :
    (pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ) =
      (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
  calc
    (pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)
        = pow2 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := by
          exact pow2_map (minpoly ℤ α) (algebraMap ℤ ℂ) (minpoly_int_monic α hα)
    _ = (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
          exact pow2_eq_prod_sub_sq (conjugateValues α) ((minpoly ℤ α).map (algebraMap ℤ ℂ))
            (minpoly_complex_eq_prod α hα)

/-- Over `ℂ`, the minimal polynomial of `α²` splits into linear factors at the
conjugates of `α²`. -/
lemma minpoly_sq_complex_prod (α : K) (hα : IsIntegral ℤ α) :
    (minpoly ℤ (α ^ 2)).map (algebraMap ℤ ℂ) =
      (conjugateValues (α ^ 2)).prod (fun z : ℂ => X - C z) := by
  exact minpoly_complex_eq_prod (α ^ 2) (IsIntegral.pow hα 2)

/-- The conjugates of `α²` are exactly the squares of the conjugates of `α`. -/
lemma conjugateValues_sq_image (α : K) :
    conjugateValues (α ^ 2) = (conjugateValues α).image (fun z : ℂ => z ^ 2) := by
  classical
  unfold conjugateValues
  rw [Finset.image_image]
  congr 1
  ext σ
  exact map_pow σ α 2

/-- Squaring maps a finite set of complex numbers onto an image whose double
cardinality dominates the original: each value `w` has at most two preimages. -/
lemma sq_image_card_le_two_mul (S : Finset ℂ) :
    S.card ≤ 2 * (S.image (fun z : ℂ => z ^ 2)).card := by
  classical
  let T : Finset ℂ := S.image (fun z : ℂ => z ^ 2)
  have hfib : ∀ b ∈ T, (S.filter (fun z : ℂ => z ^ 2 = b)).card ≤ 2 := by
    intro b hb
    let Fb : Finset ℂ := S.filter (fun z : ℂ => z ^ 2 = b)
    by_cases hne : Fb.Nonempty
    · rcases hne with ⟨z₀, hz₀⟩
      have hz₀sq : z₀ ^ 2 = b := (Finset.mem_filter.mp hz₀).2
      let U : Finset ℂ := ({z₀, -z₀} : Finset ℂ)
      have hsub : Fb ⊆ U := by
        intro z hz
        have hzsq : z ^ 2 = b := (Finset.mem_filter.mp hz).2
        have heq : z ^ 2 = z₀ ^ 2 := by rw [hzsq, hz₀sq]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h1 | h2
        · simp [U, h1]
        · simp [U, h2]
      have hU : U.card ≤ 2 := by
        calc
          U.card = (insert z₀ ({-z₀} : Finset ℂ)).card := by rfl
          _ ≤ ({-z₀} : Finset ℂ).card + 1 := Finset.card_insert_le z₀ ({-z₀} : Finset ℂ)
          _ = 2 := by simp
      simpa [Fb] using le_trans (Finset.card_le_card hsub) hU
    · have hE : Fb = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [Fb, hE]
  have hsum_eq : S.card = ∑ b ∈ T, (S.filter (fun z : ℂ => z ^ 2 = b)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise (f := fun z : ℂ => z ^ 2) (s := S) (t := T) (by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hsum_le : (∑ b ∈ T, (S.filter (fun z : ℂ => z ^ 2 = b)).card) ≤ ∑ b ∈ T, (2 : ℕ) := by
    exact Finset.sum_le_sum (fun b hb => hfib b hb)
  have hsum2 : (∑ b ∈ T, (2 : ℕ)) = T.card * 2 := by
    exact Finset.sum_const_nat (fun b hb => rfl)
  calc
    S.card = ∑ b ∈ T, (S.filter (fun z : ℂ => z ^ 2 = b)).card := hsum_eq
    _ ≤ ∑ b ∈ T, (2 : ℕ) := hsum_le
    _ = T.card * 2 := hsum2
    _ = 2 * T.card := by rw [Nat.mul_comm]
    _ ≤ 2 * (S.image (fun z : ℂ => z ^ 2)).card := by
      dsimp [T]
      rfl

/-- Classical lemma: a monic rational polynomial whose complex roots are all
roots of a monic irreducible rational polynomial `g`, and whose degree is at
most `deg g`, is `1` or `g`. -/
lemma monic_eq_one_or_of_root_subset (f g : ℚ[X])
    (hgmon : g.Monic) (hgirr : Irreducible g) (hfmon : f.Monic)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hroot : ∀ w : ℂ, (f.map (algebraMap ℚ ℂ)).IsRoot w → (g.map (algebraMap ℚ ℂ)).IsRoot w) :
    f = 1 ∨ f = g := by
  classical
  by_cases hf : f = 1
  · exact Or.inl hf
  · right
    have hfpos : 0 < f.natDegree := by
      by_contra h
      have hnd : f.natDegree = 0 := by omega
      have hf0 : f ≠ 0 := hfmon.ne_zero
      have hdeg0 : f.degree = 0 := by
        rw [Polynomial.degree_eq_natDegree hf0, hnd]
        norm_num
      have hunit : IsUnit f := (Polynomial.isUnit_iff_degree_eq_zero).mpr hdeg0
      exact hf ((Polynomial.Monic.isUnit_iff hfmon).mp hunit)
    let fℂ : ℂ[X] := f.map (algebraMap ℚ ℂ)
    have hfℂ0 : fℂ ≠ 0 := by
      dsimp [fℂ]
      exact (Polynomial.Monic.map (algebraMap ℚ ℂ) hfmon).ne_zero
    have hfdeg : fℂ.degree ≠ 0 := by
      dsimp [fℂ]
      have hnd : (f.map (algebraMap ℚ ℂ)).natDegree = f.natDegree :=
        Polynomial.natDegree_map_eq_of_injective (by
          intro a b h
          exact_mod_cast h) f
      rw [Polynomial.degree_eq_natDegree hfℂ0, hnd]
      exact_mod_cast (ne_of_gt hfpos)
    rcases IsAlgClosed.exists_root fℂ hfdeg with ⟨w, hw⟩
    have hgwm : (g.map (algebraMap ℚ ℂ)).IsRoot w := hroot w hw
    have haeval_f : Polynomial.aeval w f = 0 := by
      calc
        Polynomial.aeval w f = eval₂ (algebraMap ℚ ℂ) w f := Polynomial.aeval_def w f
        _ = eval w (f.map (algebraMap ℚ ℂ)) := (Polynomial.eval_map (algebraMap ℚ ℂ) w).symm
        _ = 0 := by simpa [fℂ] using hw
    have haeval_g : Polynomial.aeval w g = 0 := by
      calc
        Polynomial.aeval w g = eval₂ (algebraMap ℚ ℂ) w g := Polynomial.aeval_def w g
        _ = eval w (g.map (algebraMap ℚ ℂ)) := (Polynomial.eval_map (algebraMap ℚ ℂ) w).symm
        _ = 0 := by simpa using hgwm
    have hgmin : g = minpoly ℚ w := by
      exact minpoly.eq_of_irreducible_of_monic hgirr haeval_g hgmon
    have hgf : g ∣ f := by
      simpa [hgmin] using (minpoly.dvd ℚ w haeval_f)
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hgmon hfmon hgf hdeg)

/-- The structure theorem: `pow2 (minpoly ℤ α)` is either the minimal
polynomial of `α²` or its square. -/
lemma pow2_eq_minpoly_sq_or_sq (α : K) (hα : IsIntegral ℤ α) :
    pow2 (minpoly ℤ α) = minpoly ℤ (α ^ 2) ∨
      pow2 (minpoly ℤ α) = (minpoly ℤ (α ^ 2)) ^ 2 := by
  classical
  let P : ℤ[X] := minpoly ℤ α
  let P₂ : ℤ[X] := pow2 P
  let β : K := α ^ 2
  let Q : ℤ[X] := minpoly ℤ β
  let Qℚ : ℚ[X] := minpoly ℚ β
  let P₂ℚ : ℚ[X] := P₂.map (algebraMap ℤ ℚ)
  let S : Finset ℂ := conjugateValues α
  let S₂ : Finset ℂ := conjugateValues β
  have hβint : IsIntegral ℤ β := by simpa [β] using (IsIntegral.pow hα 2)
  have hβ : IsIntegral ℚ β := IsIntegral.tower_top hβint
  have hℤℚinj : Function.Injective (algebraMap ℤ ℚ) := by
    intro a b h
    exact_mod_cast h
  have hmapℤℂℚ : ∀ (F : ℤ[X]), (F.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) =
      F.map (algebraMap ℤ ℂ) := by
    intro F
    rw [Polynomial.map_map]
    congr
  have hPmonic : P.Monic := by simpa [P] using minpoly_int_monic α hα
  have hP₂monic : P₂.Monic := by
    dsimp [P₂]
    exact pow2_monic P hPmonic
  have hP₂ℚmonic : P₂ℚ.Monic := by
    dsimp [P₂ℚ]
    exact Polynomial.Monic.map (algebraMap ℤ ℚ) hP₂monic
  have hQℚmonic : Qℚ.Monic := by
    dsimp [Qℚ]
    exact minpoly.monic hβ
  have hQℚ_map : Qℚ = Q.map (algebraMap ℤ ℚ) := by
    dsimp [Qℚ, Q, β]
    exact minpoly_rat_eq_map_int (α ^ 2) hβint
  have hQℚirr : Irreducible Qℚ := by
    dsimp [Qℚ]
    exact minpoly.irreducible hβ
  -- rational factorization
  rcases pow2_rat_dvd_factor α hα with ⟨R, hR⟩
  have hRat : P₂ℚ = Qℚ * R := by
    simpa [P₂, Qℚ, β, P₂ℚ] using hR
  have hRmonic : R.Monic := by
    apply Polynomial.Monic.of_mul_monic_left hQℚmonic
    simpa [hRat] using hP₂ℚmonic
  -- complex products
  have hP2ℂ : P₂.map (algebraMap ℤ ℂ) = S.prod (fun z : ℂ => X - C (z ^ 2)) := by
    simpa [P₂, P, S] using pow2_complex_prod_sq α hα
  have hQℂ : Q.map (algebraMap ℤ ℂ) = S₂.prod (fun u : ℂ => X - C u) := by
    simpa [Q, β, S₂] using minpoly_sq_complex_prod α hα
  have hQℚℂ : Qℚ.map (algebraMap ℚ ℂ) = Q.map (algebraMap ℤ ℂ) := by
    rw [hQℚ_map]
    exact hmapℤℂℚ Q
  have hRℂ : P₂.map (algebraMap ℤ ℂ) =
      Q.map (algebraMap ℤ ℂ) * R.map (algebraMap ℚ ℂ) := by
    calc
      P₂.map (algebraMap ℤ ℂ) = P₂ℚ.map (algebraMap ℚ ℂ) := by
        dsimp [P₂ℚ]
        exact (hmapℤℂℚ P₂).symm
      _ = (Qℚ * R).map (algebraMap ℚ ℂ) := by rw [hRat]
      _ = Qℚ.map (algebraMap ℚ ℂ) * R.map (algebraMap ℚ ℂ) := by
        rw [Polynomial.map_mul]
      _ = Q.map (algebraMap ℤ ℂ) * R.map (algebraMap ℚ ℂ) := by
        rw [hQℚℂ]
  -- root inclusion: every root of R (in ℂ) is a root of Q
  have hrootincl : ∀ w : ℂ, (R.map (algebraMap ℚ ℂ)).IsRoot w →
      (Q.map (algebraMap ℤ ℂ)).IsRoot w := by
    intro w hw
    change eval w (R.map (algebraMap ℚ ℂ)) = 0 at hw
    have hP2w : eval w (P₂.map (algebraMap ℤ ℂ)) = 0 := by
      rw [hRℂ]
      rw [Polynomial.eval_mul]
      rw [hw]
      simp
    have hwprod : S.prod (fun z : ℂ => w - z ^ 2) = 0 := by
      rw [hP2ℂ] at hP2w
      rw [Polynomial.eval_prod] at hP2w
      simpa using hP2w
    have hz : ∃ z ∈ S, w - z ^ 2 = 0 := by
      exact (Finset.prod_eq_zero_iff.mp (by simpa using hwprod))
    rcases hz with ⟨z, hzS, hz0⟩
    have hwz : w = z ^ 2 := sub_eq_zero.mp hz0
    have hwS2 : w ∈ S₂ := by
      dsimp [S₂, β, S]
      rw [conjugateValues_sq_image α]
      exact Finset.mem_image.mpr ⟨z, hzS, hwz.symm⟩
    rw [hQℂ]
    change eval w (S₂.prod (fun u : ℂ => X - C u)) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hwS2 (by simp)
  -- degree bounds
  have hdegP2ℚ : P₂ℚ.natDegree = S.card := by
    calc
      P₂ℚ.natDegree = P₂.natDegree := by
        dsimp [P₂ℚ]
        exact Polynomial.natDegree_map_eq_of_injective hℤℚinj P₂
      _ = P.natDegree := by
        dsimp [P₂]
        exact Submission.RootCorr.pow2_natDegree P hPmonic
      _ = S.card := by
        simpa [P, S] using minpoly_natDegree_eq_card α hα
  have hdegQℚ : Qℚ.natDegree = S₂.card := by
    calc
      Qℚ.natDegree = (Q.map (algebraMap ℤ ℚ)).natDegree := by rw [hQℚ_map]
      _ = Q.natDegree := Polynomial.natDegree_map_eq_of_injective hℤℚinj Q
      _ = S₂.card := by
        simpa [Q, β, S₂] using minpoly_natDegree_eq_card (α ^ 2) hβint
  have hcard : S.card ≤ 2 * S₂.card := by
    dsimp [S, S₂, β]
    rw [conjugateValues_sq_image α]
    exact sq_image_card_le_two_mul (conjugateValues α)
  have hnatmul : P₂ℚ.natDegree = Qℚ.natDegree + R.natDegree := by
    have hP₂ℚ0 : P₂ℚ ≠ 0 := hP₂ℚmonic.ne_zero
    have hQℚ0 : Qℚ ≠ 0 := hQℚmonic.ne_zero
    have hR0 : R ≠ 0 := hRmonic.ne_zero
    calc
      P₂ℚ.natDegree = (Qℚ * R).natDegree := by rw [hRat]
      _ = Qℚ.natDegree + R.natDegree := Polynomial.natDegree_mul hQℚ0 hR0
  have hdegR : R.natDegree ≤ Qℚ.natDegree := by
    have hineq : Qℚ.natDegree + R.natDegree ≤ 2 * Qℚ.natDegree := by
      calc
        Qℚ.natDegree + R.natDegree = P₂ℚ.natDegree := hnatmul.symm
        _ = S.card := hdegP2ℚ
        _ ≤ 2 * S₂.card := hcard
        _ = 2 * Qℚ.natDegree := by rw [← hdegQℚ]
    omega
  -- apply the classical lemma to the rational quotient R
  have hRcases : R = 1 ∨ R = Qℚ := by
    exact monic_eq_one_or_of_root_subset R Qℚ hQℚmonic hQℚirr hRmonic hdegR (by
      intro w hw
      rw [hQℚℂ]
      exact hrootincl w hw)
  rcases hRcases with hR1 | hRQQ
  · left
    have hP2Qℚ : P₂ℚ = Qℚ := by simpa [hR1] using hRat
    have hP2Q_int : P₂ = Q := by
      apply Polynomial.map_injective (algebraMap ℤ ℚ) hℤℚinj
      calc
        P₂.map (algebraMap ℤ ℚ) = P₂ℚ := rfl
        _ = Qℚ := hP2Qℚ
        _ = Q.map (algebraMap ℤ ℚ) := hQℚ_map
    simpa [P₂, Q, P, β] using hP2Q_int
  · right
    have hP2Q2ℚ : P₂ℚ = Qℚ * Qℚ := by simpa [hRQQ] using hRat
    have hP2Q2_int : P₂ = Q ^ 2 := by
      apply Polynomial.map_injective (algebraMap ℤ ℚ) hℤℚinj
      calc
        P₂.map (algebraMap ℤ ℚ) = P₂ℚ := rfl
        _ = Qℚ * Qℚ := hP2Q2ℚ
        _ = (Q.map (algebraMap ℤ ℚ)) * (Q.map (algebraMap ℤ ℚ)) := by rw [hQℚ_map]
        _ = (Q * Q).map (algebraMap ℤ ℚ) := by rw [← Polynomial.map_mul]
        _ = (Q ^ 2).map (algebraMap ℤ ℚ) := by rw [pow_two]
    simpa [P₂, Q, P, β] using hP2Q2_int

/-- If `pow2 (minpoly ℤ α) = (minpoly ℤ (α^2))^2` then the conjugates of `α`
are closed under negation. -/
lemma negclosed_of_pow2_eq_minpoly_sq_sq (α : K) (hα : IsIntegral ℤ α)
    (h : pow2 (minpoly ℤ α) = (minpoly ℤ (α ^ 2)) ^ 2) :
    ∀ z : ℂ, z ∈ conjugateValues α → -z ∈ conjugateValues α := by
  classical
  let P₂ : ℤ[X] := pow2 (minpoly ℤ α)
  let Q : ℤ[X] := minpoly ℤ (α ^ 2)
  let S : Finset ℂ := conjugateValues α
  let S₂ : Finset ℂ := conjugateValues (α ^ 2)
  have hPQ : P₂ = Q ^ 2 := by simpa [P₂, Q] using h
  have hP2Q : P₂.map (algebraMap ℤ ℂ) = (Q.map (algebraMap ℤ ℂ)) ^ 2 := by
    calc
      P₂.map (algebraMap ℤ ℂ) = (Q ^ 2).map (algebraMap ℤ ℂ) := by rw [hPQ]
      _ = (Q.map (algebraMap ℤ ℂ)) ^ 2 := by rw [Polynomial.map_pow]
  have hP2ℂ : P₂.map (algebraMap ℤ ℂ) = S.prod (fun z : ℂ => X - C (z ^ 2)) := by
    simpa [P₂, S] using pow2_complex_prod_sq α hα
  have hQℂ : Q.map (algebraMap ℤ ℂ) = S₂.prod (fun u : ℂ => X - C u) := by
    simpa [Q, S₂] using minpoly_sq_complex_prod α hα
  have hP2Qprod : S.prod (fun z : ℂ => X - C (z ^ 2)) =
      (S₂.prod (fun u : ℂ => X - C u)) ^ 2 := by
    calc
      S.prod (fun z : ℂ => X - C (z ^ 2)) = P₂.map (algebraMap ℤ ℂ) := hP2ℂ.symm
      _ = (Q.map (algebraMap ℤ ℂ)) ^ 2 := hP2Q
      _ = (S₂.prod (fun u : ℂ => X - C u)) ^ 2 := by rw [hQℂ]
  intro z₀ hz₀
  let a : ℂ := z₀ ^ 2
  have haS₂ : a ∈ S₂ := by
    dsimp [a, S₂, S]
    rw [conjugateValues_sq_image α]
    exact Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩
  let F : ℂ[X] := (S.erase z₀).prod (fun z : ℂ => X - C (z ^ 2))
  have hF : S.prod (fun z : ℂ => X - C (z ^ 2)) = (X - C a) * F := by
    dsimp [F]
    dsimp [a]
    exact (Finset.mul_prod_erase S (fun z : ℂ => X - C (z ^ 2)) hz₀).symm
  let G : ℂ[X] := (S₂.erase a).prod (fun u : ℂ => X - C u)
  have hG : S₂.prod (fun u : ℂ => X - C u) = (X - C a) * G := by
    dsimp [G]
    dsimp [a]
    exact (Finset.mul_prod_erase S₂ (fun u : ℂ => X - C u) haS₂).symm
  have hF_eq : F = (X - C a) * G ^ 2 := by
    have htmp : (X - C a) * F = (X - C a) * ((X - C a) * G ^ 2) := by
      calc
        (X - C a) * F = S.prod (fun z : ℂ => X - C (z ^ 2)) := hF.symm
        _ = (S₂.prod (fun u : ℂ => X - C u)) ^ 2 := hP2Qprod
        _ = ((X - C a) * G) ^ 2 := by rw [hG]
        _ = (X - C a) ^ 2 * G ^ 2 := by ring
        _ = (X - C a) * ((X - C a) * G ^ 2) := by ring
    exact mul_left_cancel₀ (monic_X_sub_C a).ne_zero htmp
  have hdiv : (X - C a) ∣ F := ⟨G ^ 2, hF_eq⟩
  have hFr : F.IsRoot a := (Polynomial.dvd_iff_isRoot).mp hdiv
  have hzero : eval a F = 0 := by simpa [IsRoot] using hFr
  have hzeroprod : (S.erase z₀).prod (fun z : ℂ => a - z ^ 2) = 0 := by
    dsimp [F] at hzero
    rw [Polynomial.eval_prod] at hzero
    simpa using hzero
  have hz1 : ∃ z ∈ S.erase z₀, a - z ^ 2 = 0 := by
    exact (Finset.prod_eq_zero_iff.mp (by simpa using hzeroprod))
  rcases hz1 with ⟨z₁, hz₁mem, hz₁0⟩
  have hz₁neq : z₁ ≠ z₀ := (Finset.mem_erase.mp hz₁mem).1
  have hz₁S : z₁ ∈ S := (Finset.mem_erase.mp hz₁mem).2
  have hsq : z₁ ^ 2 = a := (sub_eq_zero.mp hz₁0).symm
  have hsq0 : z₁ ^ 2 = z₀ ^ 2 := by rw [hsq]
  have hz₁eq : z₁ = z₀ ∨ z₁ = -z₀ := sq_eq_sq_iff_eq_or_eq_neg.mp hsq0
  have hneg : -z₀ ∈ S := by
    rcases hz₁eq with h1 | h2
    · exact False.elim (hz₁neq h1)
    · exact h2 ▸ hz₁S
  simpa [S] using hneg

/-- **Master case split.** Either `pow2 (minpoly ℤ α)` is irreducible, or the
conjugates of `α` are closed under negation. -/
theorem pow2_irreducible_or_negclosed (α : K) (hα : IsIntegral ℤ α) :
    Irreducible (pow2 (minpoly ℤ α)) ∨
      ∀ z : ℂ, z ∈ conjugateValues α → -z ∈ conjugateValues α := by
  rcases pow2_eq_minpoly_sq_or_sq α hα with h | h
  · left
    rw [h]
    exact minpoly_int_irreducible (α ^ 2) (IsIntegral.pow hα 2)
  · right
    exact negclosed_of_pow2_eq_minpoly_sq_sq α hα h

end Submission.Descent

end
