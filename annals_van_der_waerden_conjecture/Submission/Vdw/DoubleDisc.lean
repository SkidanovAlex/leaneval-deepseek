import Mathlib
import Submission.Commons.FieldTheory.Polynomial.discr_constCoeff_lead_natDegree_coeff
import Submission.Commons.FieldTheory.Polynomial.discr_X_pow_add_X_add_T
import Submission.Commons.FieldTheory.Polynomial.discr_C_mul_X_pow_add_C_ne_zero
import Submission.Commons.RingTheory.Polynomial.discr_map_of_natDegree
import Submission.Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero
import Submission.Commons.Algebra.MvPolynomial.zeroSet_ncard_le_box
import Submission.Commons.Algebra.MvPolynomial.doubleDiscr_totalDegree_le

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 2000000

/-!
# The Case-III "double discriminant" DD(a₁,…,a_{n−1})

For the monic family `f(X) = X^n + a_{n-1} X^{n-1} + … + a_1 X + a_0` (a_i = coefficient
of X^i), Case III of Bhargava's proof of van der Waerden's Conjecture (Section 5)
introduces `DD(a_1,…,a_{n-1}) := Disc_{a_0}( Disc_X(f(X)) )`.  This module builds DD as
an explicit polynomial in the n−1 non-constant coefficients over ℚ (variable
`j : Fin (n-1)` ↔ coefficient of `X^(j+1)`) and proves:

- `ddPoly_ne_zero (n ≥ 3)`, `ddPoly_totalDegree_le` (bound `(4n−3)(2n−1)`),
- the box zero-set bound `ddPoly_zero_box_ncard_le` (O(H^(n−2)), Case III),
- the evaluation identity `(eval u)(ddPoly n) = concDD n u` (value of DD at coefficient
  vector `u` = `Disc_t(Disc_X(f with upper coefficients u))`).

Structure: `P := MvPolynomial (Fin (n−1)) ℚ` (parameters), `C := Polynomial P` with
variable the formal constant coefficient `t`; `fam : C[X]` is `X^n + Σ_j X_j·X^(j+1) + t`;
`DD := Disc_t(Disc_X(fam)) ∈ P`.  The generic family is written in the same form as the
fleet lemma `discr_constCoeff_lead_natDegree_coeff` (t-degree n−1, leading coeff ± n^n).
-/

namespace Submission.Vdw

noncomputable section

/-- Parameters: the `n−1` non-constant coefficients; variable `j` ↔ coefficient of `X^(j+1)`. -/
abbrev ddParam (n : ℕ) := MvPolynomial (Fin (n - 1)) ℚ

/-- The generic monic degree-`n` family `X^n + Σ_j X_j·X^(j+1) + t` in `C[X]`
(`C = (ddParam n)[X]`, whose variable is the formal constant coefficient `t`). -/
def ddFamily (n : ℕ) : (Polynomial (ddParam n))[X] :=
  X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)) +
    Polynomial.C (Polynomial.X : Polynomial (ddParam n))

/-- `Disc_X` of the family: a polynomial in `t` with parameter coefficients. -/
abbrev ddInner (n : ℕ) : Polynomial (ddParam n) := Polynomial.discr (ddFamily n)

/-- `DD := Disc_t(Disc_X family)`, an element of the parameter ring. -/
abbrev ddPoly (n : ℕ) : ddParam n := Polynomial.discr (ddInner n)

/-- The concrete monic degree-`n` family over `ℚ[t]` with upper coefficients `u`. -/
def concFamily (n : ℕ) (u : Fin (n - 1) → ℚ) : (Polynomial ℚ)[X] :=
  X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1)) +
    Polynomial.C (Polynomial.X : Polynomial ℚ)

/-- `Disc_X` of the concrete family: an element of `ℚ[t]`. -/
abbrev concInner (n : ℕ) (u : Fin (n - 1) → ℚ) : Polynomial ℚ :=
  Polynomial.discr (concFamily n u)

/-- The value `DD(u) = Disc_t(Disc_X(f))` for concrete upper coefficients `u`. -/
def concDD (n : ℕ) (u : Fin (n - 1) → ℚ) : ℚ := Polynomial.discr (concInner n u)

/-- The specialization vector with `X^1`-coefficient 1 (all other upper coefficients 0). -/
def ddU0 (n : ℕ) : Fin (n - 1) → ℚ := fun j => if (j : ℕ) = 0 then 1 else 0

-- ---------------------------------------------------------------
-- 1. basic structural facts

/-- Coefficients distribute over finite sums. -/
lemma coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι) (f : ι → R[X]) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' has' ih
    rw [Finset.sum_insert has', Finset.sum_insert has', Polynomial.coeff_add, ih]

/-- Substituting the parameters in the generic family yields the concrete family. -/
lemma ddFamily_map_conc (n : ℕ) (u : Fin (n - 1) → ℚ) :
    Polynomial.map (Polynomial.mapRingHom (MvPolynomial.eval u)) (ddFamily n) = concFamily n u := by
  classical
  let f : Polynomial (ddParam n) →+* Polynomial ℚ := Polynomial.mapRingHom (MvPolynomial.eval u)
  have hterm (j : Fin (n - 1)) :
      Polynomial.map f (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)
          : (Polynomial (ddParam n))[X]) = Polynomial.C (Polynomial.C (u j)) * X ^ ((j : ℕ) + 1) := by
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    congr 1
    rw [Polynomial.map_C]
    congr 1
    change Polynomial.map (MvPolynomial.eval u) (Polynomial.C (MvPolynomial.X j)) = Polynomial.C (u j)
    rw [Polynomial.map_C]
    congr 1
    simpa using (MvPolynomial.eval_X u j)
  unfold ddFamily concFamily
  rw [Polynomial.map_add, Polynomial.map_add]
  rw [Polynomial.map_pow, Polynomial.map_X]
  rw [Polynomial.map_sum]
  rw [Polynomial.map_C]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j
  · congr 1
    change Polynomial.map (MvPolynomial.eval u) (Polynomial.X : Polynomial (ddParam n)) = Polynomial.X
    rw [Polynomial.map_X]

/-- Coefficient of the family at index `k ≥ n`. -/
lemma ddFamily_coeff_ge (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : n ≤ k) :
    (ddFamily n).coeff k = if k = n then 1 else 0 := by
  classical
  unfold ddFamily
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  have hX : (X ^ n : (Polynomial (ddParam n))[X]).coeff k = if k = n then 1 else 0 := by
    rw [Polynomial.coeff_X_pow]
  have hC : (Polynomial.C (Polynomial.X : Polynomial (ddParam n)) : (Polynomial (ddParam n))[X]).coeff k = 0 := by
    rw [Polynomial.coeff_C]
    simp [show k ≠ 0 by omega]
  rw [coeff_finset_sum]
  have hsum : (∑ j : Fin (n - 1), (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)
        : (Polynomial (ddParam n))[X]).coeff k) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hnat : (Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)
        : (Polynomial (ddParam n))[X]).natDegree ≤ (j : ℕ) + 1 := by
      rw [Polynomial.natDegree_le_iff_degree_le]
      exact Polynomial.degree_C_mul_X_pow_le ((j : ℕ) + 1) (Polynomial.C (MvPolynomial.X j))
    omega
  rw [hX, hC, hsum]
  simp

/-- The family is monic of degree `n` in `X` (for `1 ≤ n`). -/
lemma ddFamily_monic_natDegree (n : ℕ) (hn : 1 ≤ n) : (ddFamily n).Monic ∧ (ddFamily n).natDegree = n := by
  have hnd : (ddFamily n).natDegree = n := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [ddFamily_coeff_ge n hn m (le_of_lt hm)]
      simp [ne_of_gt hm]
    · by_contra hlt
      have hc0 : (ddFamily n).coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hlt)
      have hc : (ddFamily n).coeff n = 1 := by
        rw [ddFamily_coeff_ge n hn n (le_rfl)]
        simp
      rw [hc] at hc0
      norm_num at hc0
  constructor
  · show (ddFamily n).leadingCoeff = 1
    rw [Polynomial.leadingCoeff, hnd, ddFamily_coeff_ge n hn n (le_rfl)]
    simp
  · exact hnd

-- 2. leading coefficient of ddInner in t  (fleet discr_constCoeff_lead_natDegree_coeff)
-- ---------------------------------------------------------------

/-- The t-degree of `Disc_X(family)` is `n−1` with t-leading coefficient `± n^n`. -/
lemma ddInner_natDegree_lc (n : ℕ) (hn : 2 ≤ n) :
    (ddInner n).natDegree = n - 1 ∧
      (ddInner n).coeff (n - 1) = MvPolynomial.C ((-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n) := by
  exact Commons.FieldTheory.Polynomial.discr_constCoeff_lead_natDegree_coeff (F := ℚ) n hn (by
    exact_mod_cast (Nat.ne_of_gt (by omega) : n ≠ 0))

-- ---------------------------------------------------------------
-- 3. evaluation identity: eval u (ddPoly n) = concDD n u
-- ---------------------------------------------------------------

/-- Inner commutation: substituting parameters into `Disc_X(family)` gives `Disc_X` of the
concrete family (fleet `discr_map_of_natDegree`, the family being monic). -/
lemma ddInner_map_conc (n : ℕ) (hn : 1 ≤ n) (u : Fin (n - 1) → ℚ) :
    Polynomial.map (MvPolynomial.eval u) (ddInner n) = concInner n u := by
  classical
  have hdeg : (Polynomial.map (Polynomial.mapRingHom (MvPolynomial.eval u)) (ddFamily n)).natDegree
      = (ddFamily n).natDegree := by
    have hm := (ddFamily_monic_natDegree n hn).1
    have hlc : (ddFamily n).leadingCoeff = 1 := hm
    exact Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero
      (Polynomial.mapRingHom (MvPolynomial.eval u)) (p := ddFamily n) (by simp [hlc])
  have hR5 := Commons.RingTheory.Polynomial.discr_map_of_natDegree
    (R := Polynomial (ddParam n)) (S := Polynomial ℚ)
    (Polynomial.mapRingHom (MvPolynomial.eval u)) (p := ddFamily n) hdeg
  change (Polynomial.mapRingHom (MvPolynomial.eval u)) (ddInner n) = concInner n u
  change (Polynomial.mapRingHom (MvPolynomial.eval u)) (Polynomial.discr (ddFamily n))
      = Polynomial.discr (concFamily n u)
  rw [hR5]
  congr 1
  rw [ddFamily_map_conc n u]

/-- The evaluation identity: substituting the upper coefficients `u` into `DD` recovers
`Disc_t(Disc_X(f_u))`. -/
lemma ddPoly_eval_concDD (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℚ) :
    (MvPolynomial.eval u) (ddPoly n) = concDD n u := by
  classical
  have hnz : n ≠ 0 := by omega
  have hlcne : (MvPolynomial.eval u) ((ddInner n).leadingCoeff) ≠ 0 := by
    have hnd := (ddInner_natDegree_lc n hn).1
    have hlc := (ddInner_natDegree_lc n hn).2
    rw [Polynomial.leadingCoeff, hnd, hlc, MvPolynomial.eval_C]
    exact mul_ne_zero
      (pow_ne_zero (n * (n - 1) / 2) (by norm_num))
      (pow_ne_zero n (by exact_mod_cast hnz))
  have hdeg : (Polynomial.map (MvPolynomial.eval u) (ddInner n)).natDegree = (ddInner n).natDegree :=
    Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero (MvPolynomial.eval u) (p := ddInner n) hlcne
  have hR5 := Commons.RingTheory.Polynomial.discr_map_of_natDegree
    (R := ddParam n) (S := ℚ) (MvPolynomial.eval u) (p := ddInner n) hdeg
  change (MvPolynomial.eval u) (Polynomial.discr (ddInner n)) = Polynomial.discr (concInner n u)
  rw [hR5]
  congr 1
  exact ddInner_map_conc n (by omega : 1 ≤ n) u


-- ---------------------------------------------------------------
-- 4. total degree bound and nonzeroness of DD
-- ---------------------------------------------------------------

/-- Explicit total-degree bound for DD (fleet `doubleDiscr_totalDegree_le`). -/
lemma ddPoly_totalDegree_le (n : ℕ) (hn : 1 ≤ n) : (ddPoly n).totalDegree ≤ (4 * n - 3) * (2 * n - 1) := by
  simpa [ddPoly, ddInner, ddFamily]
    using (Commons.Algebra.MvPolynomial.doubleDiscr_totalDegree_le (F := ℚ) n hn)

/-- The concrete family at the specialization `ddU0` is the two-term family `X^n + X + t`
(coefficients of all `X^(j+1)`, j ≥ 1, vanish). -/
lemma concFamily_ddU0_two (n : ℕ) (hn : 2 ≤ n) :
    concFamily n (ddU0 n) = X ^ n + X + Polynomial.C (Polynomial.X : Polynomial ℚ) := by
  classical
  unfold concFamily ddU0
  -- separate the j = 0 term from the rest
  have hne : (0 : ℕ) < n - 1 := by omega
  let j0 : Fin (n - 1) := ⟨0, hne⟩
  have hsplit : ∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (if (j : ℕ) = 0 then 1 else 0)) * X ^ ((j : ℕ) + 1)
      = Polynomial.C (Polynomial.C (1 : ℚ)) * X + 0 := by
    rw [Finset.sum_eq_single j0]
    · simp [j0]
    · intro b hb hb0
      have hb1 : (b : ℕ) ≠ 0 := by
        intro hb0'
        apply hb0
        ext
        simpa [j0] using hb0' 
      simp [hb1]
    · intro hmem
      simp [j0] at hmem
  rw [hsplit]
  simp [add_assoc]

/-- The t-discriminant of the specialized family `X^n + X + t` is a nonzero rational
(explicit two-term form from fleet `discr_X_pow_add_X_add_T`; nonzero by
`discr_C_mul_X_pow_add_C_ne_zero`). -/
lemma ddU0_value_ne_zero (n : ℕ) (hn : 3 ≤ n) : concDD n (ddU0 n) ≠ 0 := by
  classical
  have hfam := concFamily_ddU0_two n (by omega : 2 ≤ n)
  change Polynomial.discr (Polynomial.discr (concFamily n (ddU0 n))) ≠ 0
  rw [hfam]
  rw [Commons.FieldTheory.Polynomial.discr_X_pow_add_X_add_T (F := ℚ) n (by omega : 2 ≤ n)]
  let e1 : ℚ := (-1 : ℚ) ^ (n * (n - 1) / 2) * (n : ℚ) ^ n
  let e2 : ℚ := (-1 : ℚ) ^ (n * (n - 1) / 2) * (-1 : ℚ) ^ (n - 1) * ((n : ℚ) - 1) ^ (n - 1)
  have hmq : ((n - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : (n - 1 : ℕ) ≠ 0)
  have hne1 : e1 ≠ 0 := by
    dsimp [e1]
    exact mul_ne_zero (pow_ne_zero (n * (n - 1) / 2) (by norm_num))
      (pow_ne_zero n (by exact_mod_cast (by omega : n ≠ 0)))
  have hne2 : e2 ≠ 0 := by
    dsimp [e2]
    have h1 : ((-1 : ℚ) ^ (n * (n - 1) / 2) * (-1 : ℚ) ^ (n - 1)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero (n * (n - 1) / 2) (by norm_num)) (pow_ne_zero (n - 1) (by norm_num))
    have hnc : ((n : ℚ) - 1) ≠ 0 := by
      have h2n : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 2 ≤ n)
      linarith
    exact mul_ne_zero h1 (pow_ne_zero (n - 1) hnc)
  exact Commons.FieldTheory.Polynomial.discr_C_mul_X_pow_add_C_ne_zero (F := ℚ) (n - 1) e1 e2 hmq hne1 hne2

/-- `DD ≠ 0` for `n ≥ 3`. -/
lemma ddPoly_ne_zero (n : ℕ) (hn : 3 ≤ n) : ddPoly n ≠ 0 := by
  intro hz
  have hval : (MvPolynomial.eval (ddU0 n)) (ddPoly n) = concDD n (ddU0 n) :=
    ddPoly_eval_concDD n (by omega : 2 ≤ n) (ddU0 n)
  have hz0 : concDD n (ddU0 n) = 0 := by
    rw [← hval]
    simp [hz]
  exact ddU0_value_ne_zero n hn hz0

-- ---------------------------------------------------------------
-- 5. integer-box zero-set bound  O(H^(n-2))
-- ---------------------------------------------------------------

/-- Evaluating DD at integer coefficients (embedded in ℚ). -/
def ddEvalInt (n : ℕ) (u : Fin (n - 1) → ℤ) : ℚ := (ddPoly n).eval (fun i => (u i : ℚ))

/-- The set of rational box-points `{-H,…,H}`. -/
def ratBox (H : ℕ) : Finset ℚ := (Finset.Icc (-(H : ℤ)) (H : ℤ)).image (fun z : ℤ => (z : ℚ))

/-- Cardinality of the rational box: `2H+1`. -/
lemma ratBox_card (H : ℕ) : (ratBox H).card = 2 * H + 1 := by
  classical
  unfold ratBox
  rw [Finset.card_image_of_injective]
  · rw [Int.card_Icc]
    have hz : (H : ℤ) + 1 - (-(H : ℤ)) = (2 * (H : ℤ) + 1) := by ring
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg (a := 2 * (H : ℤ) + 1) (by omega))
  · intro a b hab
    exact_mod_cast (Int.cast_injective hab)

lemma ddPoly_zero_box_ncard_le (n H : ℕ) (hn : 3 ≤ n) :
    ({u : Fin (n - 1) → ℤ | (∀ i, |u i| ≤ (H : ℤ)) ∧ ddEvalInt n u = 0} : Set (Fin (n - 1) → ℤ)).ncard ≤
      (n - 1) * ((4 * n - 3) * (2 * n - 1)) * (2 * H + 1) ^ (n - 2) := by
  classical
  let S : Finset ℚ := ratBox H
  let d : ℕ := (4 * n - 3) * (2 * n - 1)
  have hdeg : ∀ i : Fin (n - 1), (ddPoly n).degreeOf i ≤ d := by
    intro i
    exact le_trans (MvPolynomial.degreeOf_le_totalDegree (ddPoly n) i) (ddPoly_totalDegree_le n (by omega : 1 ≤ n))
  have hSZ := Commons.Algebra.MvPolynomial.zeroSet_ncard_le_box (F := ℚ) (m := n - 1)
      (ddPoly n) (ddPoly_ne_zero n hn) S d hdeg
  let B : Set (Fin (n - 1) → ℚ) := {x | (∀ i, x i ∈ S) ∧ MvPolynomial.eval x (ddPoly n) = 0}
  let A : Set (Fin (n - 1) → ℤ) := {u | (∀ i, |u i| ≤ (H : ℤ)) ∧ ddEvalInt n u = 0}
  let f : (Fin (n - 1) → ℤ) → (Fin (n - 1) → ℚ) := fun u i => (u i : ℚ)
  have hBleB : B.ncard ≤ (n - 1) * d * (2 * H + 1) ^ (n - 2) := by
    have h1 : B.ncard ≤ (n - 1) * d * S.card ^ ((n - 1) - 1) := by
      simpa [B, S, d] using hSZ
    have hScard : S.card = 2 * H + 1 := ratBox_card H
    have hsub : (n - 1) - 1 = n - 2 := by omega
    simpa [hScard, hsub] using h1
  have hBfinite : B.Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Fintype.piFinset (fun _ : Fin (n - 1) => S))) ?_
    intro x hx
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    exact hx.1 i
  have hfinj : Function.Injective f := by
    intro u v huv
    funext i
    have hc : (u i : ℚ) = (v i : ℚ) := by simpa [f] using congrFun huv i
    exact_mod_cast hc
  have himg : f '' A ⊆ B := by
    rintro x ⟨u, hu, rfl⟩
    constructor
    · intro i
      change (f u i) ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).image (fun z : ℤ => (z : ℚ))
      rw [Finset.mem_image]
      refine ⟨u i, ?_, rfl⟩
      rw [Finset.mem_Icc]
      exact abs_le.mp (hu.1 i)
    · simpa [A, ddEvalInt] using hu.2
  have hAleB : A.ncard ≤ B.ncard := by
    rw [← Set.ncard_image_of_injective A hfinj]
    exact Set.ncard_le_ncard himg hBfinite
  simpa [A] using (hAleB.trans hBleB)
end
