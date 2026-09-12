import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_C_mul
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_neg
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_eval_ne_zero_of_transcendental
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finite_int_polys_bounded_supNorm
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_factor_supNorm_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.poly_det_facile
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.exists_pos_small_eval_of_transcendental
import Submission.Commons.Analysis.Polynomial.supNorm_X_pow_mul
import Submission.Commons.Measure.FinFunction.affineCylinder_volume
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.one_le_int_norm_cast
import Submission.Commons.LinearAlgebra.Independence.li_real_of_li_int
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper_measure
import Submission.Commons.LinearAlgebra.Independence.linearIndependent_sub_smul_pivot
import Submission.Commons.Combinatorics.Reindex.monotone_perm
import Submission.Commons.Analysis.ContinuousMin.finset_min_continuous
import Submission.Commons.LinearAlgebra.Independence.li_pair_drop_some
import Submission.Commons.LinearAlgebra.Independence.linearIndependent_of_ambient

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree
open Polynomial
open scoped BigOperators
noncomputable section



open Polynomial
open scoped BigOperators


/-- Sup-norm of an integer polynomial mapped to ℝ. -/
def supN (P : Polynomial ℤ) : ℝ := (P.map (Int.castRingHom ℝ)).supNorm
/-- Evaluation at ξ of the real map. -/
def pv (ξ : ℝ) (P : Polynomial ℤ) : ℝ := Polynomial.eval ξ (P.map (Int.castRingHom ℝ))

lemma supN_nonneg (P : Polynomial ℤ) : 0 ≤ supN P := by
  dsimp [supN]
  exact Polynomial.supNorm_nonneg (p := P.map (Int.castRingHom ℝ))

lemma supN_one_le {P : Polynomial ℤ} (h : P ≠ 0) : 1 ≤ supN P := by
  dsimp [supN]
  exact int_poly_supNorm_one_le P h

lemma supN_pos_of_ne_zero {P : Polynomial ℤ} (h : P ≠ 0) : 0 < supN P :=
  lt_of_lt_of_le zero_lt_one (supN_one_le h)

lemma supN_eq_zero_iff {P : Polynomial ℤ} : supN P = 0 ↔ P = 0 := by
  dsimp [supN]
  rw [Polynomial.supNorm_eq_zero_iff]
  exact Polynomial.map_eq_zero_iff (Int.cast_injective (α := ℝ))

lemma pv_ne_zero_of_transcendental {ξ : ℝ} (hξ : Transcendental ℚ ξ) {P : Polynomial ℤ}
    (hP : P ≠ 0) : pv ξ P ≠ 0 := by
  dsimp [pv]
  exact int_poly_eval_ne_zero_of_transcendental ξ hξ P hP

/-- supNorm triangle inequality for the sup norm on polynomial coefficients. -/
lemma supNorm_add_le {A : Type*} [SeminormedRing A] (p q : Polynomial A) :
    (p + q).supNorm ≤ p.supNorm + q.supNorm := by
  classical
  rcases Polynomial.exists_eq_supNorm (p := p + q) with ⟨i, hi⟩
  calc
    (p + q).supNorm = ‖(p + q).coeff i‖ := hi
    _ = ‖p.coeff i + q.coeff i‖ := by simp
    _ ≤ ‖p.coeff i‖ + ‖q.coeff i‖ := norm_add_le _ _
    _ ≤ p.supNorm + q.supNorm := add_le_add (Polynomial.le_supNorm p i) (Polynomial.le_supNorm q i)

lemma supN_add_le (P Q : Polynomial ℤ) : supN (P + Q) ≤ supN P + supN Q := by
  dsimp [supN]
  rw [Polynomial.map_add]
  exact supNorm_add_le (P.map (Int.castRingHom ℝ)) (Q.map (Int.castRingHom ℝ))


lemma pv_add (ξ : ℝ) (P Q : Polynomial ℤ) : pv ξ (P + Q) = pv ξ P + pv ξ Q := by
  dsimp [pv]
  rw [Polynomial.map_add, Polynomial.eval_add]


lemma pv_neg (ξ : ℝ) (P : Polynomial ℤ) : pv ξ (-P) = -pv ξ P := by
  dsimp [pv]
  rw [Polynomial.map_neg, Polynomial.eval_neg]

lemma pv_sub (ξ : ℝ) (P Q : Polynomial ℤ) : pv ξ (P - Q) = pv ξ P - pv ξ Q := by
  dsimp [pv]
  rw [Polynomial.map_sub, Polynomial.eval_sub]

lemma pv_C_mul (ξ : ℝ) (c : ℤ) (P : Polynomial ℤ) : pv ξ (Polynomial.C c * P) = (c : ℝ) * pv ξ P := by
  dsimp [pv]
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
  have hc : Int.castRingHom ℝ c = (c : ℝ) := rfl
  rw [hc]

lemma supN_C_mul (c : ℤ) (P : Polynomial ℤ) : supN (Polynomial.C c * P) = ‖(c : ℝ)‖ * supN P := by
  dsimp [supN]
  exact int_poly_supNorm_C_mul c P

lemma supN_neg (P : Polynomial ℤ) : supN (-P) = supN P := by
  dsimp [supN]
  exact int_poly_supNorm_neg P

/-- Triangle in reverse: ‖P + Q‖ ≥ ‖Q‖ − ‖P‖ (also ‖P + Q‖ ≥ ‖P‖ − ‖Q‖). -/
lemma supN_ge_sub (P Q : Polynomial ℤ) : supN Q - supN P ≤ supN (P + Q) := by
  have h1 : supN Q ≤ supN (P + Q) + supN P := by
    calc
      supN Q = supN (P + Q + -P) := by
        congr 1
        ext i
        simp [add_assoc]
      _ ≤ supN (P + Q) + supN (-P) := supN_add_le (P + Q) (-P)
      _ = supN (P + Q) + supN P := by rw [supN_neg]
  linarith

/-- Evaluation bound: |P(ξ)| ≤ (n+1)·max(1,|ξ|)^n · ‖P‖ for deg P ≤ n. -/
lemma abs_pv_le {n : ℕ} {ξ : ℝ} (P : Polynomial ℤ) (hdeg : P.natDegree ≤ n) :
    |pv ξ P| ≤ (n + 1 : ℝ) * (max 1 |ξ|) ^ n * supN P := by
  classical
  dsimp [pv, supN]
  let B : ℝ := max 1 |ξ|
  have hB1 : 1 ≤ B := by dsimp [B]; exact le_max_left 1 |ξ|
  have hB0 : 0 ≤ B := by dsimp [B]; exact le_trans zero_le_one (le_max_left _ _)
  have hxiB : |ξ| ≤ B := by dsimp [B]; exact le_max_right 1 |ξ|
  let p : ℝ[X] := P.map (Int.castRingHom ℝ)
  have hpdeg : p.natDegree ≤ n := by
    dsimp [p]
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hdeg
  have hnlt : p.natDegree < n + 1 := Nat.lt_succ_of_le hpdeg
  rw [Polynomial.eval_eq_sum_range' hnlt ξ]
  calc
    |∑ i ∈ Finset.range (n + 1), p.coeff i * ξ ^ i|
        ≤ ∑ i ∈ Finset.range (n + 1), |p.coeff i * ξ ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (n + 1), |p.coeff i| * |ξ| ^ i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (n + 1), p.supNorm * B ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        calc
          |p.coeff i| * |ξ| ^ i ≤ p.supNorm * |ξ| ^ i := by
            exact mul_le_mul_of_nonneg_right (Polynomial.le_supNorm p i) (pow_nonneg (abs_nonneg _) i)
          _ ≤ p.supNorm * B ^ i := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxiB i) p.supNorm_nonneg
          _ ≤ p.supNorm * B ^ n := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hi_le) p.supNorm_nonneg
    _ = (↑(Finset.range (n + 1)).card) * (p.supNorm * B ^ n) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ = (n + 1 : ℝ) * (p.supNorm * B ^ n) := by
        rw [Finset.card_range]
        norm_num
    _ = (n + 1 : ℝ) * B ^ n * p.supNorm := by ring

theorem pv_lower_uniform {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) (B : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ n → supN P ≤ B →
      m ≤ |pv ξ P| := by
  classical
  rcases exists_pos_small_eval_of_transcendental n B ξ hξ with ⟨m, hm0, hm1, hmain⟩
  refine ⟨m, hm0, ?_⟩
  intro P hPne hdeg hsup
  have hb : (P.map (Int.castRingHom ℝ)).supNorm ≤ B := by simpa [supN] using hsup
  have hval : m ≤ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ := hmain P hPne hdeg hb
  simpa [pv, Real.norm_eq_abs] using hval





open Polynomial
open scoped BigOperators


/-- The q-height functional in multiplicative form:  Tq(q,P) = max(‖P‖, e^q·|P(ξ)|).
(We work multiplicatively; additive exponents are logs of these.) -/
def Tq (ξ : ℝ) (q : ℝ) (P : Polynomial ℤ) : ℝ := max (supN P) (Real.exp q * |pv ξ P|)

lemma Tq_nonneg (ξ : ℝ) (q : ℝ) (P : Polynomial ℤ) : 0 ≤ Tq ξ q P := by
  dsimp [Tq]
  exact le_max_of_le_left (supN_nonneg P)

lemma supN_le_Tq (ξ : ℝ) (q : ℝ) (P : Polynomial ℤ) : supN P ≤ Tq ξ q P := by
  dsimp [Tq]
  exact le_max_left _ _

lemma Tq_exp_le (ξ : ℝ) (q : ℝ) (P : Polynomial ℤ) :
    Real.exp q * |pv ξ P| ≤ Tq ξ q P := by
  dsimp [Tq]
  exact le_max_right _ _

lemma Tq_zero (ξ : ℝ) (q : ℝ) : Tq ξ q 0 = 0 := by
  dsimp [Tq, supN, pv]
  simp

/-- `Tq ≥ 1` for nonzero polynomials. -/
lemma one_le_Tq {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ} (hP : P ≠ 0) : 1 ≤ Tq ξ q P :=
  le_trans (supN_one_le hP) (supN_le_Tq ξ q P)

/-- monotone in q. -/
lemma Tq_mono_q {ξ : ℝ} {q q' : ℝ} (hqq : q ≤ q') (P : Polynomial ℤ) : Tq ξ q P ≤ Tq ξ q' P := by
  dsimp [Tq]
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hqq) (abs_nonneg _))

/-- `Tq` factorizes the max for nonzero P: lower bound on the value term when norm term is
smaller.  If Tq(Q) = e^q·|Q(ξ)| then we say the value constraint is active at q. -/
lemma Tq_eq_value_iff {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ} :
    Tq ξ q P = Real.exp q * |pv ξ P| ↔ supN P ≤ Real.exp q * |pv ξ P| := by
  dsimp [Tq]
  exact max_eq_right_iff

/-- universal scale bound: monomials have Tq ≤ R0. -/
def R0 (n : ℕ) (ξ : ℝ) (q : ℝ) : ℝ := max 1 (Real.exp q * (max 1 |ξ|) ^ n)

lemma monomial_Tq_le_R0 (n : ℕ) (ξ : ℝ) (q : ℝ) (i : ℕ) (hi : i ≤ n) :
    Tq ξ q (Polynomial.X ^ i) ≤ R0 n ξ q := by
  have hsupN : supN (Polynomial.X ^ i) = 1 := by
    have h1 := Commons.Analysis.Polynomial.supNorm_X_pow_mul (A := ℝ) (Q := (1 : Polynomial ℝ)) i
    have hone : (1 : Polynomial ℝ).supNorm = 1 := by
      rw [← Polynomial.C_1, Polynomial.supNorm_C]
      norm_num
    calc
      supN (Polynomial.X ^ i)
          = ((Polynomial.X ^ i : Polynomial ℝ) * (1 : Polynomial ℝ)).supNorm := by
            dsimp [supN]
            rw [Polynomial.map_pow, Polynomial.map_X]
            simp
      _ = (1 : Polynomial ℝ).supNorm := h1
      _ = 1 := hone
  have hev : pv ξ (Polynomial.X ^ i) = ξ ^ i := by
    dsimp [pv]
    rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X]
  have hle1 : (1 : ℝ) ≤ R0 n ξ q := by dsimp [R0]; exact le_max_left _ _
  have hle2 : Real.exp q * |ξ ^ i| ≤ R0 n ξ q := by
    have hq : Real.exp q * |ξ ^ i| ≤ Real.exp q * (max 1 |ξ|) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos q).le
      calc
        |ξ ^ i| ≤ (max 1 |ξ|) ^ i := by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right 1 |ξ|) i
        _ ≤ (max 1 |ξ|) ^ n := pow_le_pow_right₀ (le_max_left 1 |ξ|) hi
    exact le_trans hq (le_max_right _ _)
  have h1 : supN (Polynomial.X ^ i) ≤ R0 n ξ q := le_trans (le_of_eq hsupN) hle1
  have h2 : Real.exp q * |pv ξ (Polynomial.X ^ i)| ≤ R0 n ξ q := by
    rw [hev]
    simpa using hle2
  change max (supN (Polynomial.X ^ i)) (Real.exp q * |pv ξ (Polynomial.X ^ i)|) ≤ R0 n ξ q
  exact max_le h1 h2

/-- The monomials X^0,…,X^{j-1} are ℝ-linearly independent as real polynomials. -/
lemma linearIndependent_X_pow_fin (j : ℕ) :
    LinearIndependent ℝ (fun i : Fin j => (Polynomial.X ^ (i.val : ℕ) : Polynomial ℝ)) := by
  have hb : LinearIndependent ℝ (fun s : ℕ => (Polynomial.X ^ s : Polynomial ℝ)) := by
    simpa [Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials ℝ).linearIndependent
  exact hb.comp (fun i : Fin j => (i.val : ℕ)) (by intro a b h; exact Fin.ext (by simpa using h))

/-! ## Successive minima (multiplicative) of the body `{P : Tq(q,P) ≤ R}` over the lattice
of integer polynomials of degree ≤ n. -/

/-- Defining set of the j-th successive minimum at level q. -/
def smSet (n : ℕ) (ξ : ℝ) (q : ℝ) (j : ℕ) : Set ℝ :=
  {R : ℝ | 0 ≤ R ∧ ∃ S : Fin j → Polynomial ℤ,
    (∀ i : Fin j, S i ≠ 0 ∧ (S i).natDegree ≤ n ∧ Tq ξ q (S i) ≤ R) ∧
    LinearIndependent ℝ (fun i : Fin j => (S i).map (Int.castRingHom ℝ))}

/-- The j-th successive minimum: infimum of the levels whose ball contains j independent
integer polynomials of degree ≤ n. -/
def sm (n : ℕ) (ξ : ℝ) (q : ℝ) (j : ℕ) : ℝ := sInf (smSet n ξ q j)

lemma bddBelow_smSet (n : ℕ) (ξ : ℝ) (q : ℝ) (j : ℕ) : BddBelow (smSet n ξ q j) := by
  refine ⟨0, ?_⟩
  rintro R ⟨hR0, _⟩
  exact hR0

/-- smSet is nonempty when j ≤ n+1 (monomials realize level R0). -/
lemma nonempty_smSet {n : ℕ} {ξ : ℝ} {q : ℝ} {j : ℕ} (hj : j ≤ n + 1) :
    (smSet n ξ q j).Nonempty := by
  let S : Fin j → Polynomial ℤ := fun i => Polynomial.X ^ (i.val : ℕ)
  refine ⟨R0 n ξ q, ?_⟩
  constructor
  · exact le_max_of_le_left (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one
  · refine ⟨S, ?_, ?_⟩
    · intro i
      have hdeg : (Polynomial.X ^ (i.val : ℕ) : Polynomial ℤ).natDegree = i.val := Polynomial.natDegree_X_pow i.val
      constructor
      · exact pow_ne_zero _ (by simp : (Polynomial.X : Polynomial ℤ) ≠ 0)
      · constructor
        · rw [hdeg]
          exact (by omega : (i.val : ℕ) ≤ n)
        · exact monomial_Tq_le_R0 n ξ q i.val (by omega : (i.val : ℕ) ≤ n)
    · change LinearIndependent ℝ (fun i : Fin j => ((Polynomial.X ^ (i.val : ℕ) : Polynomial ℤ).map (Int.castRingHom ℝ)))
      have h := linearIndependent_X_pow_fin j
      simpa [Polynomial.map_pow, Polynomial.map_X] using h

/-- successive minima are nonnegative. -/
lemma sm_nonneg {n : ℕ} {ξ : ℝ} {q : ℝ} {j : ℕ} (hj : j ≤ n + 1) :
    0 ≤ sm n ξ q j := by
  unfold sm
  exact le_csInf (nonempty_smSet (n := n) (ξ := ξ) (q := q) (j := j) hj)
    (by rintro R ⟨hR0, _⟩; exact hR0)

/-- If a level R contains j independent points, then λ_j ≤ R. -/
lemma sm_le_of_exists {n : ℕ} {ξ : ℝ} {q : ℝ} {j : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (S : Fin j → Polynomial ℤ)
    (hS : ∀ i : Fin j, S i ≠ 0 ∧ (S i).natDegree ≤ n ∧ Tq ξ q (S i) ≤ R)
    (hlin : LinearIndependent ℝ (fun i : Fin j => (S i).map (Int.castRingHom ℝ))) :
    sm n ξ q j ≤ R := by
  unfold sm
  exact csInf_le (bddBelow_smSet n ξ q j) ⟨hR, S, hS, hlin⟩

/-- λ_1 is at most the q-height of every nonzero polynomial of degree ≤ n. -/
lemma sm1_le_Tq {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ n) : sm n ξ q 1 ≤ Tq ξ q P := by
  have hnon : 0 ≤ Tq ξ q P := Tq_nonneg ξ q P
  refine sm_le_of_exists (n := n) (ξ := ξ) (q := q) (j := 1) hnon (fun _ => P) ?_ ?_
  · intro i
    exact ⟨hP, hdeg, le_rfl⟩
  · rw [linearIndependent_subsingleton_index_iff]
    intro i hp
    -- P ≠ 0 implies its real map ≠ 0
    apply hP
    apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
    simpa using hp

/-- Realization: any level strictly above λ_j contains j independent lattice points. -/
lemma exists_linearIndependent_of_sm_lt {n : ℕ} {ξ : ℝ} {q : ℝ} {j : ℕ}
    (hj : j ≤ n + 1) {R : ℝ} (hR : sm n ξ q j < R) :
    ∃ S : Fin j → Polynomial ℤ,
      (∀ i : Fin j, S i ≠ 0 ∧ (S i).natDegree ≤ n ∧ Tq ξ q (S i) ≤ R) ∧
      LinearIndependent ℝ (fun i : Fin j => (S i).map (Int.castRingHom ℝ)) := by
  have hS : (smSet n ξ q j).Nonempty := nonempty_smSet (n := n) (ξ := ξ) (q := q) hj
  have hmem : R ∈ smSet n ξ q j := by
    by_contra hRset
    have hlb : ∀ s ∈ smSet n ξ q j, R ≤ s := by
      intro s hs
      by_contra hlt
      exact hRset (by
        rcases hs with ⟨hs0, S, hS1, hlin⟩
        exact ⟨le_trans hs0 (le_of_lt (lt_of_not_ge hlt)), S, fun i => ⟨(hS1 i).1, (hS1 i).2.1,
          le_trans (hS1 i).2.2 (le_of_lt (lt_of_not_ge hlt))⟩, hlin⟩)
    have hinf : R ≤ sInf (smSet n ξ q j) := le_csInf hS hlb
    exact (not_lt_of_ge hinf) hR
  exact hmem.2

/-- monotonicity in j. -/
lemma sm_mono {n : ℕ} {ξ : ℝ} {q : ℝ} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n + 1) :
    sm n ξ q i ≤ sm n ξ q j := by
  unfold sm
  apply le_csInf (nonempty_smSet (n := n) (ξ := ξ) (q := q) (j := j) hj)
  rintro R ⟨hR0, S, hS, hlin⟩
  let e : Fin i ↪ Fin j := Fin.castLEEmb hij
  refine sm_le_of_exists (n := n) (ξ := ξ) (q := q) (j := i) hR0 (fun a => S (e a)) ?_ ?_
  · intro a
    exact hS (e a)
  · exact hlin.comp (fun a : Fin i => e a) (Function.Embedding.injective e)

/-- upper bound for all successive minima by R0. -/
lemma sm_le_R0 {n : ℕ} {ξ : ℝ} {q : ℝ} {j : ℕ} (hj : j ≤ n + 1) :
    sm n ξ q j ≤ R0 n ξ q := by
  let S : Fin j → Polynomial ℤ := fun i => Polynomial.X ^ (i.val : ℕ)
  refine sm_le_of_exists (n := n) (ξ := ξ) (q := q) (j := j)
    (le_max_of_le_left (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one) S ?_ ?_
  · intro i
    have hdeg : (Polynomial.X ^ (i.val : ℕ) : Polynomial ℤ).natDegree = i.val := Polynomial.natDegree_X_pow i.val
    constructor
    · exact pow_ne_zero _ (by simp : (Polynomial.X : Polynomial ℤ) ≠ 0)
    · constructor
      · rw [hdeg]
        exact (by omega : (i.val : ℕ) ≤ n)
      · exact monomial_Tq_le_R0 n ξ q i.val (by omega : (i.val : ℕ) ≤ n)
  · change LinearIndependent ℝ (fun i : Fin j => ((Polynomial.X ^ (i.val : ℕ) : Polynomial ℤ).map (Int.castRingHom ℝ)))
    have h := linearIndependent_X_pow_fin j
    simpa [Polynomial.map_pow, Polynomial.map_X] using h

/-- λ_1 is also bounded BELOW: any level below λ_1 contains no nonzero point, so every
nonzero P has λ_1 ≤ Tq(P) (that is the min-characterisation) — this is sm1_le_Tq above.
The converse: if some level r < λ_1 then no nonzero P has Tq ≤ r; contrapositive of
realization at j=1. -/
lemma sm1_eq_infi_Tq {n : ℕ} {ξ : ℝ} {q : ℝ} :
    sm n ξ q 1 = sInf {t : ℝ | 0 ≤ t ∧ ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ Tq ξ q P ≤ t} := by
  unfold sm smSet
  congr 1
  ext t
  constructor
  · rintro ⟨ht0, S, hS, hlin⟩
    refine ⟨ht0, ⟨S 0, (hS ⟨0, by omega⟩).1, (hS ⟨0, by omega⟩).2.1, (hS ⟨0, by omega⟩).2.2⟩⟩
  · rintro ⟨ht0, P, hP, hdeg, hPt⟩
    refine ⟨ht0, fun _ => P, ?_, ?_⟩
    · intro i
      exact ⟨hP, hdeg, hPt⟩
    · rw [linearIndependent_subsingleton_index_iff]
      intro i hp
      apply hP
      apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
      simpa using hp

/-- A polynomial realizing the first minimum (when Tq equals λ_1) gives slope/value structure. -/
lemma Tq_eq_sm1_of_le {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ n) (hle : Tq ξ q P ≤ sm n ξ q 1) : Tq ξ q P = sm n ξ q 1 := by
  exact le_antisymm hle (sm1_le_Tq hP hdeg)


/-- The first minimum is at least 1 (every nonzero integer polynomial has height ≥ 1). -/
lemma sm_one_le {n : ℕ} {ξ : ℝ} {q : ℝ} : (1 : ℝ) ≤ sm n ξ q 1 := by
  unfold sm
  apply le_csInf (nonempty_smSet (n := n) (ξ := ξ) (q := q) (j := 1) (by omega))
  rintro r ⟨hr0, S, hS, hlin⟩
  let i0 : Fin 1 := ⟨0, by omega⟩
  have h1 : (1 : ℝ) ≤ Tq ξ q (S i0) := one_le_Tq (hS i0).1
  have h2 : Tq ξ q (S i0) ≤ r := (hS i0).2.2
  exact le_trans h1 h2


/-- Successive minima are monotone in the level `q`: `q ≤ q'` gives `sm(q) ≤ sm(q')`
(the body shrinks as `q` grows). -/
lemma sm_mono_q {n : ℕ} {ξ : ℝ} {q q' : ℝ} (hqq : q ≤ q') {j : ℕ}
    (hj : j ≤ n + 1) : sm n ξ q j ≤ sm n ξ q' j := by
  unfold sm
  apply le_csInf (nonempty_smSet (n := n) (ξ := ξ) (q := q') (j := j) hj)
  rintro r ⟨hr0, S, hS, hlin⟩
  -- r ∈ smSet(q') gives the family also in smSet(q) (Tq monotone in q), hence sm(q) ≤ r
  have hSq : ∀ i : Fin j, S i ≠ 0 ∧ (S i).natDegree ≤ n ∧ Tq ξ q (S i) ≤ r := by
    intro i
    exact ⟨(hS i).1, (hS i).2.1, le_trans (Tq_mono_q hqq (S i)) (hS i).2.2⟩
  exact csInf_le (bddBelow_smSet n ξ q j) ⟨hr0, S, hSq, hlin⟩





open Polynomial
open scoped BigOperators


/-! ## M1 first slice: extension outside a span

A linearly independent family indexed by `Fin (k+1)` cannot be contained in the
ℝ-span of `k` vectors.  Generic linear algebra over any ℝ-vector space. -/

lemma exists_not_mem_span_of_linearIndependent {k : ℕ} {E : Type*} [AddCommGroup E]
    [Module ℝ E] {S : Fin (k + 1) → E} (hS : LinearIndependent ℝ S) {f : Fin k → E} :
    ∃ i : Fin (k + 1), S i ∉ Submodule.span ℝ (Set.range f) := by
  classical
  by_contra h
  push_neg at h
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range f)
  have hSW : ∀ i : Fin (k + 1), S i ∈ W := by
    intro i
    exact h i
  -- W is finitely generated by the finite family f, hence a finite module
  have hWfg : W.FG := Submodule.fg_span (Set.finite_range f)
  haveI : Module.Finite ℝ ↥W := (Module.Finite.iff_fg (R := ℝ) (M := E) (N := W)).mpr hWfg
  -- span of the S family is contained in W
  have hspan_le : Submodule.span ℝ (Set.range S) ≤ W := by
    exact Submodule.span_le.mpr (by intro x hx; rcases hx with ⟨i, rfl⟩; exact hSW i)
  -- independence of S gives (k+1) ≤ finrank(span(range S)) ≤ finrank W ≤ k
  have hcard : (k + 1) ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range S)) := by
    have hcard0 := (linearIndependent_iff_card_le_finrank_span (R := ℝ) (M := E) (b := S)).mp hS
    -- hcard0 : Fintype.card (Fin (k+1)) ≤ Set.finrank ℝ (range S)
    simpa [Set.finrank] using hcard0
  have hmono : Module.finrank ℝ (Submodule.span ℝ (Set.range S)) ≤ Module.finrank ℝ ↥W := by
    exact Submodule.finrank_mono (R := ℝ) hspan_le
  have hWupper : Module.finrank ℝ ↥W ≤ k := by
    have h := finrank_range_le_card (R := ℝ) (M := E) (b := f)
    -- h : Set.finrank ℝ (range f) ≤ Fintype.card (Fin k)
    simpa [W, Set.finrank] using h
  omega





open Polynomial
open scoped BigOperators


/- helper: pointwise behaviour of Fin.snoc on a constant type -/
lemma snoc_apply_castSucc {m : ℕ} {α : Type*} (v : Fin m → α) (x : α) (i : Fin m) :
    (@Fin.snoc m (fun _ : Fin (m + 1) => α) v x) (Fin.castSucc i) = v i := by
  exact @Fin.snoc_castSucc m (fun _ : Fin (m + 1) => α) x v i

lemma snoc_apply_last {m : ℕ} {α : Type*} (v : Fin m → α) (x : α) :
    (@Fin.snoc m (fun _ : Fin (m + 1) => α) v x) (Fin.last m) = x := by
  exact @Fin.snoc_last m (fun _ : Fin (m + 1) => α) x v

/-! ## M1: nested realizers for the successive minima of `Tq`

For every j = 1..n+1 there are j linearly independent integer polynomials
Q_1..Q_j of degree ≤ n with Tq(Q_i) ≤ sm(n,ξ,q,i) + 1.  One-step extension first. -/

lemma extend_family (n : ℕ) (ξ : ℝ) (q : ℝ) {m : ℕ} (hmlt : m < n + 1)
    {Q : Fin m → Polynomial ℤ}
    (hQb : ∀ i : Fin m, Q i ≠ 0 ∧ (Q i).natDegree ≤ n ∧
      Tq ξ q (Q i) ≤ sm n ξ q (i.val + 1) + 1)
    (hQli : LinearIndependent ℝ (fun i : Fin m => (Q i).map (Int.castRingHom ℝ))) :
    ∃ Q' : Fin (m + 1) → Polynomial ℤ,
      (∀ j : Fin m, Q' (Fin.castSucc j) = Q j) ∧
      (∀ j : Fin (m + 1), Q' j ≠ 0 ∧ (Q' j).natDegree ≤ n ∧
        Tq ξ q (Q' j) ≤ sm n ξ q (j.val + 1) + 1) ∧
      LinearIndependent ℝ (fun j : Fin (m + 1) => (Q' j).map (Int.castRingHom ℝ)) := by
  classical
  have hm1 : m + 1 ≤ n + 1 := by omega
  have hlt : sm n ξ q (m + 1) < sm n ξ q (m + 1) + 1 := lt_add_of_pos_right _ zero_lt_one
  rcases exists_linearIndependent_of_sm_lt (n := n) (ξ := ξ) (q := q) (j := m + 1) hm1 hlt
    with ⟨S, hS, hSli⟩
  rcases exists_not_mem_span_of_linearIndependent (E := Polynomial ℝ)
    (S := fun i : Fin (m + 1) => (S i).map (Int.castRingHom ℝ)) hSli
    (f := fun j : Fin m => (Q j).map (Int.castRingHom ℝ)) with ⟨idx, hidx⟩
  let Q' : Fin (m + 1) → Polynomial ℤ := Fin.snoc Q (S idx)
  refine ⟨Q', ?_, ?_, ?_⟩
  · intro j
    exact snoc_apply_castSucc Q (S idx) j
  · intro j
    by_cases hjm : (j : ℕ) < m
    · let i : Fin m := ⟨(j : ℕ), hjm⟩
      have hjc : j = Fin.castSucc i := by
        apply Fin.ext
        simp [i]
      have hxj : Q' j = Q i := by
        rw [hjc]
        exact snoc_apply_castSucc Q (S idx) i
      have hiv : i.val + 1 = j.val + 1 := by simp [i]
      rw [hxj, hiv]
      exact hQb i
    · have hjv : (j : ℕ) = m := by omega
      have hjc : j = Fin.last m := by
        apply Fin.ext
        exact hjv
      have hxj : Q' j = S idx := by
        rw [hjc]
        exact snoc_apply_last Q (S idx)
      have hjv1 : j.val + 1 = m + 1 := by omega
      rw [hxj, hjv1]
      exact hS idx
  · have hmap : (fun j : Fin (m + 1) => (Q' j).map (Int.castRingHom ℝ)) =
        (@Fin.snoc m (fun _ : Fin (m + 1) => Polynomial ℝ)
          (fun j : Fin m => (Q j).map (Int.castRingHom ℝ))
          ((S idx).map (Int.castRingHom ℝ)) : Fin (m + 1) → Polynomial ℝ) := by
      funext j
      by_cases hjm : (j : ℕ) < m
      · let i : Fin m := ⟨(j : ℕ), hjm⟩
        have hjc : j = Fin.castSucc i := by
          apply Fin.ext
          simp [i]
        have hqj : (Q' j).map (Int.castRingHom ℝ) = (Q i).map (Int.castRingHom ℝ) := by
          rw [hjc]
          change ((@Fin.snoc m (fun _ : Fin (m + 1) => Polynomial ℤ) Q (S idx))
            (Fin.castSucc i)).map (Int.castRingHom ℝ) = (Q i).map (Int.castRingHom ℝ)
          rw [snoc_apply_castSucc Q (S idx) i]
        have hsj : (@Fin.snoc m (fun _ : Fin (m + 1) => Polynomial ℝ)
            (fun k : Fin m => (Q k).map (Int.castRingHom ℝ))
            ((S idx).map (Int.castRingHom ℝ))) j = (Q i).map (Int.castRingHom ℝ) := by
          rw [hjc]
          exact snoc_apply_castSucc (fun k : Fin m => (Q k).map (Int.castRingHom ℝ))
            ((S idx).map (Int.castRingHom ℝ)) i
        rw [hqj, hsj]
      · have hjv : (j : ℕ) = m := by omega
        have hjc : j = Fin.last m := by
          apply Fin.ext
          exact hjv
        have hqj : (Q' j).map (Int.castRingHom ℝ) = (S idx).map (Int.castRingHom ℝ) := by
          rw [hjc]
          change ((@Fin.snoc m (fun _ : Fin (m + 1) => Polynomial ℤ) Q (S idx))
            (Fin.last m)).map (Int.castRingHom ℝ) = (S idx).map (Int.castRingHom ℝ)
          rw [snoc_apply_last Q (S idx)]
        have hsj : (@Fin.snoc m (fun _ : Fin (m + 1) => Polynomial ℝ)
            (fun k : Fin m => (Q k).map (Int.castRingHom ℝ))
            ((S idx).map (Int.castRingHom ℝ))) j = (S idx).map (Int.castRingHom ℝ) := by
          rw [hjc]
          exact snoc_apply_last (fun k : Fin m => (Q k).map (Int.castRingHom ℝ))
            ((S idx).map (Int.castRingHom ℝ))
        rw [hqj, hsj]
    have hfin : LinearIndependent ℝ
        (Fin.snoc (fun j : Fin m => (Q j).map (Int.castRingHom ℝ))
          ((S idx).map (Int.castRingHom ℝ))) := by
      exact LinearIndependent.finSnoc (K := ℝ)
        (v := fun j : Fin m => (Q j).map (Int.castRingHom ℝ)) hQli hidx
    simpa [hmap] using hfin

/-- Nested realizers: n+1 independent polynomials of degree ≤ n with `Tq ≤ sm_i + 1`. -/
lemma realizer_family {n : ℕ} {ξ : ℝ} {q : ℝ} :
    ∃ Q : Fin (n + 1) → Polynomial ℤ,
      (∀ i : Fin (n + 1), Q i ≠ 0 ∧ (Q i).natDegree ≤ n ∧
        Tq ξ q (Q i) ≤ sm n ξ q (i.val + 1) + 1) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Q i).map (Int.castRingHom ℝ)) := by
  classical
  let P : ℕ → Prop := fun m => ∀ (hm : m ≤ n + 1), ∃ Q : Fin m → Polynomial ℤ,
      (∀ i : Fin m, Q i ≠ 0 ∧ (Q i).natDegree ≤ n ∧
        Tq ξ q (Q i) ≤ sm n ξ q (i.val + 1) + 1) ∧
      LinearIndependent ℝ (fun i : Fin m => (Q i).map (Int.castRingHom ℝ))
  have hP0 : P 0 := by
    intro hm
    refine ⟨fun _ : Fin 0 => 0, ?_, ?_⟩
    · intro i
      exact False.elim (Fin.elim0 i)
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      exact False.elim (Fin.elim0 i)
  have hPstep : ∀ m, P m → P (m + 1) := by
    intro m hPm hm1
    have hm : m ≤ n + 1 := by omega
    rcases hPm hm with ⟨Q, hQb, hQli⟩
    have hmlt : m < n + 1 := by omega
    rcases extend_family (n := n) (ξ := ξ) (q := q) hmlt hQb hQli with ⟨Q', hQ'ext, hQ'b, hQ'li⟩
    exact ⟨Q', hQ'b, hQ'li⟩
  have hall : ∀ m, P m := by
    intro m
    induction m with
    | zero => exact hP0
    | succ m ih => exact hPstep m ih
  exact hall (n + 1) le_rfl





open Polynomial
open scoped BigOperators


/-! ## Lemma 3.3, step 1: the value-correction R_i := Q_i − ⌊Q_i(ξ)/Q_1(ξ)⌋·Q_1 -/

/-- The correcting integer: floor(a/b). -/
def corrInt (a b : ℝ) (hb : b ≠ 0) : ℤ := Int.floor (a / b)

/-- |x − floor x| < 1 for every real x. -/
lemma abs_sub_floor_lt_one (x : ℝ) : |x - (Int.floor x : ℝ)| < 1 := by
  have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

/-- |floor x| ≤ |x| + 1. -/
lemma abs_floor_le_abs_add_one (x : ℝ) : |(Int.floor x : ℝ)| ≤ |x| + 1 := by
  have hsub := abs_sub_floor_lt_one x
  calc
    |(Int.floor x : ℝ)| = |x + ((Int.floor x : ℝ) - x)| := by ring_nf
    _ ≤ |x| + |(Int.floor x : ℝ) - x| := abs_add_le _ _
    _ ≤ |x| + 1 := by
      have h1 : |(Int.floor x : ℝ) - x| < 1 := by
        simpa [abs_sub_comm] using hsub
      linarith

/-- The corrected polynomial keeps the value strictly smaller than |Q_1(ξ)|. -/
lemma corr_value_lt {ξ : ℝ} {Q1 Q2 : Polynomial ℤ} (hξ : pv ξ Q1 ≠ 0) :
    let k : ℤ := corrInt (pv ξ Q2) (pv ξ Q1) hξ
    |pv ξ (Q2 - Polynomial.C k * Q1)| < |pv ξ Q1| := by
  intro k
  dsimp [k, corrInt]
  have hmain : |pv ξ Q2 / pv ξ Q1 - (Int.floor (pv ξ Q2 / pv ξ Q1) : ℝ)| < 1 :=
    abs_sub_floor_lt_one (pv ξ Q2 / pv ξ Q1)
  have hcorr : pv ξ (Q2 - Polynomial.C (Int.floor (pv ξ Q2 / pv ξ Q1)) * Q1) =
      pv ξ Q2 - (Int.floor (pv ξ Q2 / pv ξ Q1) : ℝ) * pv ξ Q1 := by
    rw [pv_sub, pv_C_mul]
  have hid : pv ξ Q2 - (Int.floor (pv ξ Q2 / pv ξ Q1) : ℝ) * pv ξ Q1 =
      pv ξ Q1 * (pv ξ Q2 / pv ξ Q1 - (Int.floor (pv ξ Q2 / pv ξ Q1) : ℝ)) := by
    field_simp [hξ]
  rw [hcorr, hid, abs_mul]
  exact (mul_lt_mul_of_pos_left hmain (abs_pos.mpr hξ)).trans_eq (by simp)

/-- Norm of the correction:
supN(Q2 − C k Q1) ≤ supN Q2 + (|Q2(ξ)|/|Q1(ξ)|)·supN Q1 + supN Q1. -/
lemma corr_supN_bound {ξ : ℝ} {Q1 Q2 : Polynomial ℤ} (hξ : pv ξ Q1 ≠ 0) :
    let k : ℤ := corrInt (pv ξ Q2) (pv ξ Q1) hξ
    supN (Q2 - Polynomial.C k * Q1) ≤
      supN Q2 + (|pv ξ Q2| / |pv ξ Q1|) * supN Q1 + supN Q1 := by
  intro k
  dsimp [k, corrInt]
  let fl : ℤ := Int.floor (pv ξ Q2 / pv ξ Q1)
  have hk : ‖(fl : ℝ)‖ ≤ |pv ξ Q2 / pv ξ Q1| + 1 := by
    simpa [fl] using abs_floor_le_abs_add_one (pv ξ Q2 / pv ξ Q1)
  have hab : |pv ξ Q2 / pv ξ Q1| = |pv ξ Q2| / |pv ξ Q1| := by
    rw [abs_div]
  have h1 : supN (Q2 - Polynomial.C fl * Q1) ≤ supN Q2 + ‖(fl : ℝ)‖ * supN Q1 := by
    calc
      supN (Q2 - Polynomial.C fl * Q1)
          ≤ supN Q2 + supN (Polynomial.C fl * Q1) := by
            have htri' : supN (Q2 + (-(Polynomial.C fl * Q1))) ≤ supN Q2 + supN (-(Polynomial.C fl * Q1)) :=
              supN_add_le Q2 (-(Polynomial.C fl * Q1))
            simpa [sub_eq_add_neg, supN_neg] using htri'
      _ = supN Q2 + ‖(fl : ℝ)‖ * supN Q1 := by rw [supN_C_mul]
  change supN (Q2 - Polynomial.C (Int.floor (pv ξ Q2 / pv ξ Q1)) * Q1) ≤
      supN Q2 + (|pv ξ Q2| / |pv ξ Q1|) * supN Q1 + supN Q1
  dsimp [fl] at hk hab h1
  calc
    supN (Q2 - Polynomial.C fl * Q1) ≤ supN Q2 + ‖(fl : ℝ)‖ * supN Q1 := h1
    _ ≤ supN Q2 + (|pv ξ Q2 / pv ξ Q1| + 1) * supN Q1 := by
      have hmul : ‖(fl : ℝ)‖ * supN Q1 ≤ (|pv ξ Q2 / pv ξ Q1| + 1) * supN Q1 :=
        mul_le_mul_of_nonneg_right hk (supN_nonneg Q1)
      linarith
    _ ≤ supN Q2 + (|pv ξ Q2| / |pv ξ Q1|) * supN Q1 + supN Q1 := by
      have hle : (|pv ξ Q2 / pv ξ Q1| + 1) * supN Q1 ≤
          (|pv ξ Q2| / |pv ξ Q1|) * supN Q1 + supN Q1 := by
        rw [hab, add_mul, one_mul]
      linarith





open Polynomial
open scoped BigOperators


/-! ## Coefficient-space glue (Sec2a)

`ℤ[X]_{≤n}` embeds isometrically into the finite-dimensional space `Fin (n+1) → ℝ` by
coefficients (basis `1, X, …, Xⁿ`): the sup-norm of the ℝ-map equals the maximum
`|coefficient|` over the first `n+1` entries (`cmax`), and evaluation at ξ is the linear
functional `ell`. -/

/-- Coefficient vector of an integer polynomial (first n+1 coefficients). -/
def cvec {n : ℕ} (P : Polynomial ℤ) : Fin (n + 1) → ℝ :=
  fun i => ((P.coeff (i.val : ℕ) : ℤ) : ℝ)

/-- The evaluation linear functional on coefficient vectors. -/
def ell (n : ℕ) (ξ : ℝ) (v : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ξ ^ (i.val : ℕ) * v i

/-- `ell` is ℝ-linear in the vector: additivity. -/
lemma ell_add {n : ℕ} (ξ : ℝ) (u v : Fin (n + 1) → ℝ) :
    ell n ξ (u + v) = ell n ξ u + ell n ξ v := by
  dsimp [ell]
  have hsplit : (∑ i : Fin (n + 1), ξ ^ (i.val : ℕ) * (u i + v i)) =
      ∑ i : Fin (n + 1), (ξ ^ (i.val : ℕ) * u i + ξ ^ (i.val : ℕ) * v i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [hsplit]
  exact Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin (n + 1))))
    (f := fun i : Fin (n + 1) => ξ ^ (i.val : ℕ) * u i)
    (g := fun i : Fin (n + 1) => ξ ^ (i.val : ℕ) * v i)

/-- `ell` is ℝ-linear in the vector: homogeneity. -/
lemma ell_smul {n : ℕ} (ξ : ℝ) (c : ℝ) (v : Fin (n + 1) → ℝ) :
    ell n ξ (c • v) = c * ell n ξ v := by
  dsimp [ell]
  calc
    (∑ i : Fin (n + 1), ξ ^ (i.val : ℕ) * (c • v) i)
        = ∑ i : Fin (n + 1), c * (ξ ^ (i.val : ℕ) * v i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Pi.smul_apply]
          ring
    _ = c * (∑ i : Fin (n + 1), ξ ^ (i.val : ℕ) * v i) := by
          rw [Finset.mul_sum]

/-- max |v i| over the finite index type. -/
def cmax {n : ℕ} (v : Fin (n + 1) → ℝ) : ℝ :=
  (Finset.univ.image (fun i : Fin (n + 1) => |v i|)).max' (by
    refine ⟨|v 0|, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩)

/-- Members of the finite set are ≤ cmax. -/
lemma abs_le_cmax {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : |v i| ≤ cmax v := by
  dsimp [cmax]
  refine Finset.le_max' (Finset.univ.image (fun i : Fin (n + 1) => |v i|)) (|v i|) ?_
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- cmax ≤ a provided every member is ≤ a. -/
lemma cmax_le {n : ℕ} {v : Fin (n + 1) → ℝ} {a : ℝ} (h : ∀ i : Fin (n + 1), |v i| ≤ a) :
    cmax v ≤ a := by
  dsimp [cmax]
  exact Finset.max'_le (Finset.univ.image (fun i : Fin (n + 1) => |v i|))
    (by exact ⟨|v 0|, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩) a
    (by intro y hy
        rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
        exact h i)

/-- `cmax` is nonnegative (it dominates |v 0|). -/
lemma cmax_nonneg {n : ℕ} (v : Fin (n + 1) → ℝ) : 0 ≤ cmax v := by
  have h0 : 0 ≤ |v 0| := abs_nonneg _
  have h : |v 0| ≤ cmax v := abs_le_cmax v 0
  linarith

/-- The sup-norm on `Fin (n + 1) → ℝ` equals `cmax` (both are the maximum |v i|). -/
lemma norm_eq_cmax {n : ℕ} (v : Fin (n + 1) → ℝ) : ‖v‖ = cmax v := by
  classical
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (cmax_nonneg v)).mpr (by
      intro i
      rw [Real.norm_eq_abs]
      exact abs_le_cmax v i)
  · apply cmax_le
    intro i
    have h := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at h

/-- sup-norm of the ℝ-map equals the maximum of |coefficients| over indices ≤ n. -/
lemma supN_eq_cmax_cvec {n : ℕ} {P : Polynomial ℤ} (hdeg : P.natDegree ≤ n) :
    supN P = cmax (cvec (n := n) P) := by
  classical
  by_cases hP0 : P = 0
  · subst hP0
    simp [supN, cmax, cvec, Polynomial.map_zero, Finset.image_const]
  · let p : Polynomial ℝ := P.map (Int.castRingHom ℝ)
    have hdegp : p.natDegree ≤ n := by
      dsimp [p]
      rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
      exact hdeg
    rcases Polynomial.exists_eq_supNorm p with ⟨j, hj⟩
    have hsupN : supN P = ‖p.coeff j‖ := by
      dsimp [supN, p]
      exact hj
    have hjle : j ≤ n := by
      by_contra hgtn
      have hnlt : n < j := Nat.lt_of_not_ge hgtn
      have hc : p.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegp hnlt)
      have h0 : supN P = 0 := by
        rw [hsupN, hc]
        simp
      have hpos : 0 < supN P := supN_pos_of_ne_zero hP0
      linarith
    apply le_antisymm
    · calc
        supN P = ‖p.coeff j‖ := hsupN
        _ = |((P.coeff j : ℤ) : ℝ)| := by
              dsimp [p]
              rw [Polynomial.coeff_map]
              rfl
        _ = |cvec (n := n) P ⟨j, Nat.lt_succ_of_le hjle⟩| := by rfl
        _ ≤ cmax (cvec (n := n) P) := abs_le_cmax (cvec (n := n) P) ⟨j, Nat.lt_succ_of_le hjle⟩
    · apply cmax_le
      intro i
      calc
        |cvec (n := n) P i| = ‖((P.map (Int.castRingHom ℝ)).coeff i.val)‖ := by
              dsimp [cvec]
              rw [Polynomial.coeff_map]
              rfl
        _ ≤ (P.map (Int.castRingHom ℝ)).supNorm := Polynomial.le_supNorm _ _
        _ = supN P := rfl

/-- Evaluation at ξ equals the linear functional of the coefficient vector. -/
lemma pv_eq_ell_cvec {n : ℕ} (ξ : ℝ) {P : Polynomial ℤ} (hdeg : P.natDegree ≤ n) :
    pv ξ P = ell n ξ (cvec (n := n) P) := by
  dsimp [pv, ell, cvec]
  have hdegp : (P.map (Int.castRingHom ℝ)).natDegree ≤ n := by
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hdeg
  have hnlt : (P.map (Int.castRingHom ℝ)).natDegree < n + 1 := Nat.lt_succ_of_le hdegp
  rw [Polynomial.eval_eq_sum_range' hnlt ξ]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Polynomial.coeff_map]
  change ((P.coeff (i.val : ℕ) : ℤ) : ℝ) * ξ ^ (i.val : ℕ) =
    ξ ^ (i.val : ℕ) * ((P.coeff (i.val : ℕ) : ℤ) : ℝ)
  rw [mul_comm]

/-- cvec is a right inverse to evaluation-based reconstruction for degree-≤ n polys:
the coefficients of `P` equal the coefficients of the polynomial built from `cvec P`. -/
lemma poly_ext_cvec {n : ℕ} {P Q : Polynomial ℤ} (hdegP : P.natDegree ≤ n)
    (hdegQ : Q.natDegree ≤ n) (h : cvec (n := n) P = cvec (n := n) Q) : P = Q := by
  classical
  apply Polynomial.ext
  intro m
  by_cases hm : m ≤ n
  · have hc := congrFun h ⟨m, Nat.lt_succ_of_le hm⟩
    have hc' : ((P.coeff m : ℤ) : ℝ) = ((Q.coeff m : ℤ) : ℝ) := by
      simpa [cvec] using hc
    exact Int.cast_injective hc'
  · have hP : P.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegP (Nat.lt_of_not_ge hm))
    have hQ : Q.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegQ (Nat.lt_of_not_ge hm))
    rw [hP, hQ]





open Polynomial
open scoped BigOperators


/-! ## Sec2b: the M2 volume estimate over the coefficient space

Body at level q (coefficient form):  C(q) = {v : ‖coeffs‖∞ ≤ 1 ∧ |ell n ξ v| ≤ e^{-q}}.
First: the ell-decomposition splitting off the constant-coefficient coordinate 0, and the
cylinder scale constants. -/

/-- The evaluation functional splits into the constant-coefficient term and the linear part
in coordinates 1..n. -/
lemma ell_decomposition {n : ℕ} (ξ : ℝ) (v : Fin (n + 1) → ℝ) :
    ell n ξ v = v 0 + ∑ i : Fin n, ξ ^ (i.val + 1) * v (Fin.succ i) := by
  unfold ell
  rw [Fin.sum_univ_succ]
  simp

/-- The sum of |ξ|^{i+1} over the coordinates 1..n; nonnegative always. -/
def ellCoeffSum (n : ℕ) (ξ : ℝ) : ℝ := ∑ i : Fin n, |ξ| ^ (i.val + 1)

lemma ellCoeffSum_nonneg (n : ℕ) (ξ : ℝ) : 0 ≤ ellCoeffSum n ξ := by
  dsimp [ellCoeffSum]
  exact Finset.sum_nonneg (by intro i hi; exact pow_nonneg (abs_nonneg ξ) _)

/-- positive whenever ξ ≠ 0 (n ≥ 1 is automatic here only for n ≥ 1; take the i = 0 term). -/
lemma ellCoeffSum_pos {n : ℕ} {ξ : ℝ} (hn : 1 ≤ n) (hξ : ξ ≠ 0) :
    0 < ellCoeffSum n ξ := by
  dsimp [ellCoeffSum]
  let i0 : Fin n := ⟨0, by omega⟩
  have hmem : i0 ∈ Finset.univ := Finset.mem_univ _
  have hnon : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |ξ| ^ (i.val + 1) := by
    intro i hi
    exact pow_nonneg (abs_nonneg ξ) _
  have hle : |ξ| ^ (i0.val + 1) ≤ ∑ i : Fin n, |ξ| ^ (i.val + 1) := by
    simpa [i0] using (Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin n => |ξ| ^ (i.val + 1)) hnon hmem)
  have hz : 0 < |ξ| ^ (i0.val + 1) := by
    dsimp [i0]
    simpa [pow_one] using (abs_pos.mpr hξ)
  exact lt_of_lt_of_le hz hle

/-- Coordinate bound used for the cylinder: s = 1/(2(A+1)) gives 0 < s, s ≤ 1 and
s·A ≤ 1/2. -/
def cylHalf (n : ℕ) (ξ : ℝ) : ℝ := (2 * (ellCoeffSum n ξ + 1))⁻¹

lemma cylHalf_pos (n : ℕ) (ξ : ℝ) : 0 < cylHalf n ξ := by
  dsimp [cylHalf]
  have hA : 0 ≤ ellCoeffSum n ξ := ellCoeffSum_nonneg n ξ
  have hpos : 0 < 2 * (ellCoeffSum n ξ + 1) := by nlinarith
  exact inv_pos.mpr hpos

lemma cylHalf_le_one (n : ℕ) (ξ : ℝ) : cylHalf n ξ ≤ 1 := by
  dsimp [cylHalf]
  have hA : 0 ≤ ellCoeffSum n ξ := ellCoeffSum_nonneg n ξ
  have hpos : 0 < 2 * (ellCoeffSum n ξ + 1) := by nlinarith
  exact (inv_le_one₀ hpos).mpr (by nlinarith)

lemma cylHalf_mul_le_half (n : ℕ) (ξ : ℝ) : cylHalf n ξ * ellCoeffSum n ξ ≤ 1 / 2 := by
  dsimp [cylHalf]
  have hA : 0 ≤ ellCoeffSum n ξ := ellCoeffSum_nonneg n ξ
  have hpos : 0 < 2 * (ellCoeffSum n ξ + 1) := by nlinarith
  rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [hA]


/-! ### The body C(q) over the coefficient space and its cylinder, with the volume bound -/

/-- Coefficient body at level q: {v : ‖coeffs‖∞ ≤ 1 ∧ |ell v| ≤ e^{-q}}. -/
def bodyC (n : ℕ) (ξ : ℝ) (q : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {v | (∀ i : Fin (n + 1), |v i| ≤ 1) ∧ |ell n ξ v| ≤ Real.exp (-q)}

/-- The cylinder inside C(q): coordinates 1..n in [−s,s] and |ell v| ≤ e^{-q}. -/
def cylinder (n : ℕ) (ξ : ℝ) (q : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {v | (∀ i : Fin n, |v (Fin.succ i)| ≤ cylHalf n ξ) ∧ |ell n ξ v| ≤ Real.exp (-q)}

/-- The cylinder is contained in the body for q ≥ log 2 (so e^{-q} ≤ 1/2). -/
lemma cylinder_subset_body {n : ℕ} {ξ : ℝ} {q : ℝ} (hq : Real.log 2 ≤ q) :
    cylinder n ξ q ⊆ bodyC n ξ q := by
  intro v hv
  rcases hv with ⟨hvb, hell⟩
  have hε12 : Real.exp (-q) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : 2 ≤ Real.exp q := by
      have hlog : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num : (0 : ℝ) < 2)
      rw [← hlog]
      exact Real.exp_le_exp.mpr hq
    have hqpos : 0 < Real.exp q := Real.exp_pos q
    exact (by
      simpa using ((inv_le_inv₀ hqpos (by norm_num : (0 : ℝ) < 2)).mpr h2))
  constructor
  · intro i
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = (0 : Fin (n + 1)) := by
        apply Fin.ext
        exact hi0
      rw [hi]
      let S : ℝ := ∑ j : Fin n, ξ ^ (j.val + 1) * v (Fin.succ j)
      have hell' : |v 0 + S| ≤ Real.exp (-q) := by
        have he := ell_decomposition ξ v
        simpa [S] using (by rw [he] at hell; exact hell)
      have htri : |v 0| ≤ |v 0 + S| + |S| := by
        have hv0 : v 0 = (v 0 + S) + (-S) := by ring
        rw [hv0]
        have h := abs_add_le (v 0 + S) (-S)
        simpa using h
      have hS1 : |S| ≤ ∑ i : Fin n, |ξ ^ (i.val + 1) * v (Fin.succ i)| := by
        dsimp [S]
        exact Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => ξ ^ (i.val + 1) * v (Fin.succ i))
      have hS2 : (∑ i : Fin n, |ξ ^ (i.val + 1) * v (Fin.succ i)|) ≤
          cylHalf n ξ * ellCoeffSum n ξ := by
        have hstep : ∀ i : Fin n, |ξ ^ (i.val + 1) * v (Fin.succ i)| ≤
            |ξ| ^ (i.val + 1) * cylHalf n ξ := by
          intro i
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (hvb i) (pow_nonneg (abs_nonneg ξ) _)
        have hsum : (∑ i : Fin n, |ξ ^ (i.val + 1) * v (Fin.succ i)|) ≤
            (∑ i : Fin n, |ξ| ^ (i.val + 1) * cylHalf n ξ) := by
          exact Finset.sum_le_sum (fun i hi => hstep i)
        have hsum2 : (∑ i : Fin n, |ξ| ^ (i.val + 1) * cylHalf n ξ) =
            cylHalf n ξ * ellCoeffSum n ξ := by
          dsimp [ellCoeffSum]
          rw [← Finset.sum_mul]
          rw [mul_comm]
        exact le_trans hsum (le_of_eq hsum2)
      have hbound : |v 0| ≤ Real.exp (-q) + cylHalf n ξ * ellCoeffSum n ξ := by
        have hSle : |S| ≤ cylHalf n ξ * ellCoeffSum n ξ := le_trans hS1 hS2
        linarith [htri, hell', hSle]
      have hhalf : cylHalf n ξ * ellCoeffSum n ξ ≤ 1 / 2 := cylHalf_mul_le_half n ξ
      linarith
    · -- coordinate i ≥ 1: i = succ of its predecessor
      let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
      have hji : i = Fin.succ j := by
        apply Fin.ext
        have hj : (j : Fin n).val = i.val - 1 := rfl
        dsimp [j]
        omega
      rw [hji]
      have hle : |v (Fin.succ j)| ≤ cylHalf n ξ := hvb j
      exact le_trans hle (cylHalf_le_one n ξ)
  · exact hell



/-- The cylinder (ell-form) equals the affine cylinder of `affineCylinder_volume`
(with coefficients a i = −ξ^{i+1}). -/
lemma cylinder_eq_affine {n : ℕ} (ξ : ℝ) (q : ℝ) :
    cylinder n ξ q =
      {v : Fin (n + 1) → ℝ |
        (∀ i : Fin n, |v (Fin.succ i)| ≤ cylHalf n ξ) ∧
        |v 0 - ∑ i : Fin n, (-ξ ^ (i.val + 1)) * v (Fin.succ i)| ≤ Real.exp (-q)} := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨hvb, hell⟩
    constructor
    · exact hvb
    · have he := ell_decomposition ξ v
      rw [he] at hell
      -- |v0 + Σ ξ^{i+1} v_i| ≤ ε  ⟹ |v0 − Σ (−ξ^{i+1}) v_i| ≤ ε
      convert hell using 1
      · ring_nf
        rw [Finset.sum_neg_distrib]
        ring
  · intro hv
    rcases hv with ⟨hvb, hell⟩
    constructor
    · exact hvb
    · have he := ell_decomposition ξ v
      rw [he]
      -- convert the affine-cylinder bound to the ell-form bound
      convert hell using 1
      ring_nf
      rw [Finset.sum_neg_distrib]
      ring

/-- **M2 volume estimate**: for q ≥ log 2 the coefficient body C(q) has Lebesgue volume
at least `c · e^{-q}` with a constant c > 0 depending only on n and ξ. -/
lemma body_volume_lower {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, Real.log 2 ≤ q →
      ENNReal.ofReal (c * Real.exp (-q)) ≤
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)) (bodyC n ξ q) := by
  classical
  let s : ℝ := cylHalf n ξ
  let c : ℝ := (2 * s) ^ n * 2
  refine ⟨c, ?_, ?_⟩
  · have hs : 0 < s := cylHalf_pos n ξ
    have hpow : 0 < (2 * s) ^ n := pow_pos (by nlinarith) n
    dsimp [c]
    nlinarith
  · intro q hq
    have hs0 : 0 ≤ s := le_of_lt (cylHalf_pos n ξ)
    have hε0 : 0 ≤ Real.exp (-q) := (Real.exp_pos (-q)).le
    have hvolA := Commons.Measure.FinFunction.affineCylinder_volume
      (n := n) (a := fun i : Fin n => -ξ ^ (i.val + 1)) (s := s) (ε := Real.exp (-q)) hs0 hε0
    have hcylEq := cylinder_eq_affine (n := n) ξ q
    have hvolcyl : (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
        (cylinder n ξ q) = ENNReal.ofReal ((2 * s) ^ n * (2 * Real.exp (-q))) := by
      rw [hcylEq]
      exact hvolA
    have hmono : (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
        (cylinder n ξ q) ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ))
          (bodyC n ξ q) := by
      exact MeasureTheory.measure_mono (cylinder_subset_body (n := n) (ξ := ξ) hq)
    have hc : c * Real.exp (-q) = (2 * s) ^ n * (2 * Real.exp (-q)) := by
      dsimp [c]
      ring
    rw [hc]
    rw [← hvolcyl]
    exact hmono





open Polynomial
open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Sec3a (M2b, IN PROGRESS — compiles)

`Coeff ξ q n` wraps a coefficient vector `v : Fin (n+1) → ℝ` and carries the norm
`Nq(v) = max(‖v.vec‖∞, e^q·|ell n ξ v.vec|)` as its `NormedAddCommGroup`/`NormedSpace`
structure.  The M2b instantiation will attach the Haar measure of the underlying function
space and the integer lattice, then apply
`Commons.Lattice.Minkowski.minkowski_second_upper_measure` to conclude
`∏ⱼ sm ≤ C(n,ξ)·e^q` for q ≥ log 2. -/

/-- Wrapper type: a coefficient vector with the q-height norm attached. -/
structure Coeff (ξ : ℝ) (q : ℝ) (n : ℕ) where
  vec : Fin (n + 1) → ℝ

namespace Coeff

variable {ξ : ℝ} {q : ℝ} {n : ℕ}

/-- Pointwise zero/add/neg/sub/nat/ℤ-smul from the underlying function space. -/
instance : Zero (Coeff ξ q n) := ⟨⟨0⟩⟩
instance : Add (Coeff ξ q n) := ⟨fun a b => ⟨a.vec + b.vec⟩⟩
instance : Neg (Coeff ξ q n) := ⟨fun a => ⟨-a.vec⟩⟩
instance : Sub (Coeff ξ q n) := ⟨fun a b => ⟨a.vec - b.vec⟩⟩
instance : SMul ℕ (Coeff ξ q n) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℤ (Coeff ξ q n) := ⟨fun k a => ⟨k • a.vec⟩⟩
instance : SMul ℝ (Coeff ξ q n) := ⟨fun c a => ⟨c • a.vec⟩⟩

@[ext] theorem ext {a b : Coeff ξ q n} (h : a.vec = b.vec) : a = b := by
  cases a; cases b; congr

@[simp] theorem vec_zero : (0 : Coeff ξ q n).vec = 0 := rfl
@[simp] theorem vec_add (a b : Coeff ξ q n) : (a + b).vec = a.vec + b.vec := rfl
@[simp] theorem vec_neg (a : Coeff ξ q n) : (-a).vec = -a.vec := rfl
@[simp] theorem vec_sub (a b : Coeff ξ q n) : (a - b).vec = a.vec - b.vec := rfl
@[simp] theorem vec_nsmul (k : ℕ) (a : Coeff ξ q n) : (k • a).vec = k • a.vec := rfl
@[simp] theorem vec_zsmul (k : ℤ) (a : Coeff ξ q n) : (k • a).vec = k • a.vec := rfl
@[simp] theorem vec_smul (c : ℝ) (a : Coeff ξ q n) : (c • a).vec = c • a.vec := rfl

/-- The additive group structure (pointwise). -/
instance : AddCommGroup (Coeff ξ q n) where
  add := (· + ·)
  add_assoc := by intro a b c; ext; simp [vec_add, add_assoc]
  zero := 0
  zero_add := by intro a; ext; simp [vec_zero, vec_add]
  add_zero := by intro a; ext; simp [vec_zero, vec_add]
  nsmul := (· • ·)
  nsmul_zero := by intro a; ext; simp [vec_nsmul, vec_zero]
  nsmul_succ := by intro n a; ext i; simp [vec_nsmul, vec_add]; ring_nf
  neg := fun a => ⟨-a.vec⟩
  sub := (· - ·)
  sub_eq_add_neg := by intro a b; ext; simp [vec_sub, vec_add, sub_eq_add_neg]
  zsmul := (· • ·)
  zsmul_zero' := by intro a; ext; simp [vec_zsmul, vec_zero]
  zsmul_succ' := by intro n a; ext i; simp [vec_zsmul, vec_add]; ring_nf
  zsmul_neg' := by intro n a; ext i; simp [vec_zsmul, vec_neg]; ring_nf
  neg_add_cancel := by intro a; ext; simp [vec_neg, vec_add, vec_zero, neg_add_cancel]
  add_comm := by intro a b; ext; simp [vec_add, add_comm]

/-- The ℝ-module structure (pointwise). -/
instance : Module ℝ (Coeff ξ q n) where
  smul := (· • ·)
  smul_zero := by intro c; apply Coeff.ext; funext i; simp [vec_smul, vec_zero]
  smul_add := by intro c a b; apply Coeff.ext; funext i; simp [vec_smul, vec_add, mul_add]
  add_smul := by intro c d a; apply Coeff.ext; funext i; simp [vec_smul, vec_add, add_mul]
  zero_smul := by intro a; apply Coeff.ext; funext i; simp [vec_smul, vec_zero]
  one_smul := by intro a; apply Coeff.ext; funext i; simp [vec_smul]
  mul_smul := by intro c d a; apply Coeff.ext; funext i; simp [vec_smul, mul_assoc]

/-- The q-height of a coefficient vector (multiplicative form, matching `Tq` on
polynomials through `cvec`). -/
noncomputable def Nq (v : Coeff ξ q n) : ℝ :=
  max ‖v.vec‖ (Real.exp q * |ell n ξ v.vec|)

/-- Raw bound: the value term is ≤ the q-height. -/
lemma value_le_Nq (v : Coeff ξ q n) : Real.exp q * |ell n ξ v.vec| ≤ Nq v := by
  dsimp [Nq]
  exact le_max_right _ _

/-- Raw bound: the coefficient sup-norm is ≤ the q-height. -/
lemma coeff_le_Nq (v : Coeff ξ q n) : ‖v.vec‖ ≤ Nq v := by
  dsimp [Nq]
  exact le_max_left _ _

/-- The q-height is nonnegative. -/
lemma Nq_nonneg (v : Coeff ξ q n) : 0 ≤ Nq v := by
  dsimp [Nq]
  exact le_max_of_le_left (norm_nonneg v.vec)

/-- On coefficient vectors of integer polynomials the q-height coincides with `Tq`:
`Tq ξ q P = Nq ⟨cvec P⟩` (via Sec2a: supN = cmax = ‖·‖∞-of-cvec, pv = ell∘cvec). -/
lemma Nq_eq_Tq {P : Polynomial ℤ} (hdeg : P.natDegree ≤ n) :
    Tq ξ q P = Nq (⟨cvec (n := n) P⟩ : Coeff ξ q n) := by
  dsimp [Tq, Nq]
  rw [supN_eq_cmax_cvec hdeg]
  rw [pv_eq_ell_cvec ξ hdeg]
  rw [norm_eq_cmax (cvec (n := n) P)]

/-- The norm instance: the q-height. -/
noncomputable instance : Norm (Coeff ξ q n) := ⟨Nq⟩

/-- c·max a b = max (c·a) (c·b) for c ≥ 0. -/
lemma mul_max_of_nonneg {a b c : ℝ} (hc : 0 ≤ c) : c * max a b = max (c * a) (c * b) := by
  apply le_antisymm
  · by_cases hab : a ≤ b
    · rw [max_eq_right hab]
      exact le_max_right _ _
    · have hba : b ≤ a := le_of_not_ge hab
      rw [max_eq_left hba]
      exact le_max_left _ _
  · exact max_le (mul_le_mul_of_nonneg_left (le_max_left a b) hc)
      (mul_le_mul_of_nonneg_left (le_max_right a b) hc)

/-- The norm core: `Nq` satisfies the norm axioms. -/
noncomputable def normCore (ξ : ℝ) (q : ℝ) (n : ℕ) : NormedSpace.Core ℝ (Coeff ξ q n) := {
  norm_nonneg := by
    intro a
    exact Nq_nonneg a
  norm_smul := by
    intro c a
    change Nq (c • a) = |c| * Nq a
    dsimp [Nq]
    rw [norm_smul c a.vec]
    have h2 : Real.exp q * |ell n ξ (c • a.vec)| = |c| * (Real.exp q * |ell n ξ a.vec|) := by
      rw [ell_smul, abs_mul]
      ring
    rw [h2]
    rw [Real.norm_eq_abs c]
    rw [← mul_max_of_nonneg (abs_nonneg c)]
  norm_triangle := by
    intro a b
    change Nq (a + b) ≤ Nq a + Nq b
    dsimp [Nq]
    have h1 : ‖a.vec + b.vec‖ ≤ ‖a.vec‖ + ‖b.vec‖ := norm_add_le _ _
    have h2 : Real.exp q * |ell n ξ (a.vec + b.vec)| ≤ Real.exp q * |ell n ξ a.vec| +
        Real.exp q * |ell n ξ b.vec| := by
      rw [ell_add]
      have htri : |ell n ξ a.vec + ell n ξ b.vec| ≤ |ell n ξ a.vec| + |ell n ξ b.vec| := abs_add_le _ _
      have hnon : 0 ≤ Real.exp q := (Real.exp_pos q).le
      calc
        Real.exp q * |ell n ξ a.vec + ell n ξ b.vec|
            ≤ Real.exp q * (|ell n ξ a.vec| + |ell n ξ b.vec|) :=
              mul_le_mul_of_nonneg_left htri hnon
        _ = Real.exp q * |ell n ξ a.vec| + Real.exp q * |ell n ξ b.vec| := by ring
    have h3 : ‖a.vec‖ + ‖b.vec‖ ≤ Nq a + Nq b := by
      exact add_le_add (coeff_le_Nq a) (coeff_le_Nq b)
    have h4 : Real.exp q * |ell n ξ a.vec| + Real.exp q * |ell n ξ b.vec| ≤ Nq a + Nq b := by
      exact add_le_add (value_le_Nq a) (value_le_Nq b)
    exact max_le (le_trans h1 h3) (le_trans h2 h4)
  norm_eq_zero_iff := by
    intro a
    constructor
    · intro ha
      have hnorm : ‖a‖ = Nq a := rfl
      rw [hnorm] at ha
      have hle : ‖a.vec‖ ≤ Nq a := coeff_le_Nq a
      have hle0 : ‖a.vec‖ ≤ (0 : ℝ) := by
        rw [ha] at hle
        exact hle
      have hvec : ‖a.vec‖ = 0 := le_antisymm hle0 (norm_nonneg a.vec)
      have hvec0 : a.vec = 0 := norm_eq_zero.mp hvec
      apply Coeff.ext
      simpa using hvec0
    · intro ha
      subst a
      change Nq (0 : Coeff ξ q n) = 0
      dsimp [Nq]
      simp [ell]
}

/-- `Coeff` is a normed additive commutative group with the q-height norm. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Coeff ξ q n) :=
  NormedAddCommGroup.ofCore (normCore ξ q n)

/-- `Coeff` is a normed real vector space with the q-height norm. -/
noncomputable instance instNormedSpace : NormedSpace ℝ (Coeff ξ q n) :=
  NormedSpace.ofCore (normCore ξ q n)

/-- `Coeff` is linearly equivalent to the plain coefficient function space. -/
noncomputable def linEquivPi (ξ : ℝ) (q : ℝ) (n : ℕ) : Coeff ξ q n ≃ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := Coeff.vec
  invFun := fun v => ⟨v⟩
  left_inv := by intro x; rfl
  right_inv := by intro v; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- `Coeff` is nontrivial. -/
instance : Nontrivial (Coeff ξ q n) := by
  refine ⟨⟨(fun _ : Fin (n + 1) => (0 : ℝ))⟩, ⟨(fun _ : Fin (n + 1) => (1 : ℝ))⟩, ?_⟩
  intro h
  have hc := congrArg Coeff.vec h
  have h0 := congrFun hc (0 : Fin (n + 1))
  norm_num at h0

/-- `Coeff` is finite-dimensional (via `linEquivPi`). -/
instance instFiniteDimensional : FiniteDimensional ℝ (Coeff ξ q n) :=
  LinearEquiv.finiteDimensional (K := ℝ) (V := Fin (n + 1) → ℝ) (V₂ := Coeff ξ q n)
    (linEquivPi ξ q n).symm





/-- Measurable space on `Coeff`: the Borel sets of the norm topology.  (No separate
topology instance is declared: the topology is the one bundled with `instNormedAddCommGroup`,
i.e. the topology induced by the q-height norm `Nq`.) -/
noncomputable instance instMeasurableSpace : MeasurableSpace (Coeff ξ q n) := borel (Coeff ξ q n)

/-- `Coeff` is a Borel space. -/
noncomputable instance instBorelSpace : BorelSpace (Coeff ξ q n) := ⟨rfl⟩

/-- `vec` is continuous (automatic continuity of linear equivalences between finite-dimensional
normed spaces). -/
lemma continuous_vec : Continuous (Coeff.vec : Coeff ξ q n → Fin (n + 1) → ℝ) := by
  change Continuous (linEquivPi ξ q n)
  exact (linEquivPi ξ q n).toContinuousLinearEquiv.continuous

/-- The inverse `v ↦ ⟨v⟩` is continuous (automatic continuity of linear equivalences). -/
lemma continuous_inv (ξ : ℝ) (q : ℝ) (n : ℕ) :
    Continuous (fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n)) := by
  change Continuous (linEquivPi ξ q n).symm
  exact (linEquivPi ξ q n).symm.toContinuousLinearEquiv.continuous


/-- `Coeff` is a measure space: volume is the pushforward of Lebesgue on the coefficient
function space along the wrapping map `v ↦ ⟨v⟩` (= `(linEquivPi ξ q n).symm`). -/
noncomputable instance instMeasureSpace (ξ : ℝ) (q : ℝ) (n : ℕ) :
    MeasureSpace (Coeff ξ q n) where
  volume := Measure.map (fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n))
    (MeasureTheory.volume : Measure (Fin (n + 1) → ℝ))

/-- The wrapped Lebesgue measure is an additive Haar measure on `Coeff` (the wrapping map is
a ℝ-linear equivalence, hence a homeomorphism, between the ambient function space and the
coefficient space). -/
noncomputable instance instIsAddHaarMeasure (ξ : ℝ) (q : ℝ) (n : ℕ) :
    MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure (Coeff ξ q n)) := by
  let ν : Measure (Fin (n + 1) → ℝ) := MeasureTheory.volume
  let e : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] Coeff ξ q n := (linEquivPi ξ q n).symm
  have hvol : (MeasureTheory.volume : Measure (Coeff ξ q n)) = ν.map (⇑e) := by
    change (MeasureTheory.volume : Measure (Coeff ξ q n)) = ν.map (⇑e)
    dsimp [ν]
    unfold instMeasureSpace
    congr 1
  have hhaar : MeasureTheory.Measure.IsAddHaarMeasure (ν.map (⇑e)) := by
    dsimp [ν]
    exact (MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure
      (μ := MeasureTheory.volume) (e := e) :
      MeasureTheory.Measure.IsAddHaarMeasure (ν.map (⇑e)))
  simpa [hvol] using hhaar

end Coeff



open Module
open scoped BigOperators ENNReal

/-! ## Sec3b (M2b slice 5, IN PROGRESS — compiles)

The integer lattice inside `Coeff ξ q n` (coefficient vectors with integer entries):
`intLattice ξ q n : Submodule ℤ (Coeff ξ q n)`.  Done and compiling:
  • `intLattice` (carrier = integer-valued vecs; zero/add/smul closure)
  • `one_le_norm_of_mem_intLattice_ne_zero` (nonzero lattice points have norm ≥ 1)
  • `discreteTopology_intLattice` (instance: unit ball contains no other lattice point)

TODO (next session, roughly in order):
  1. `span_intLattice_top : span ℝ (intLattice ξ q n : Set (Coeff ξ q n)) = ⊤`
     — prove `span_ej_top` first: with `ej ξ q n j := ⟨fun i => if i = j then 1 else 0⟩`,
     `Set.range (fun j => (ej ξ q n j).vec)` equals `Set.range (Pi.basisFun ℝ (Fin(n+1)))`
     (use `simp [ej]` + `rw [Pi.single_apply]` per coordinate; Pi.basisFun j reduces via
     theorem `Pi.basisFun_apply : Pi.basisFun R η i = Pi.single i 1` — simp does not
     reduce basisFun itself, add `Pi.basisFun_apply` to simp), then map through
     `linEquivPi ξ q n` (note `linEquivPi ξ q n x = x.vec` is rfl) with
     `Submodule.map_span`, `Set.image_range`, injectivity of `Submodule.map` of an
     equivalence, `Submodule.map_top`, `LinearMap.range_eq_top` (equivalence is
     surjective).  Alternatively prove by sum-representation in Coeff directly.
  2. `isZLattice_intLattice : IsZLattice ℝ (intLattice ξ q n)` (span_top field).
  3. `finrank_intLattice : Module.finrank ℤ (intLattice ξ q n) = n + 1`
     via `ZLattice.rank` + `LinearEquiv.finrank_eq (linEquivPi ξ q n)` + simp.
  4. covolume: `ZLattice.covolume (μ := (volume : Measure (Coeff ξ q n))) (intLattice ξ q n) = 1`
     — route: transport to Pi via the ℝ-linear equivalence e := (linEquivPi ξ q n).symm;
     standard ℤ-lattice in (Fin (n+1) → ℝ) has covolume 1 w.r.t. Lebesgue
     (e.g. `ZLattice.covolume_eq_det` with b = Pi.basisFun as ℤ-basis, det = 1);
     use `ZLattice.covolume_comap`-style or `covolume_eq_measure_fundamentalDomain`
     with the fundamental domain mapping to the unit cube via `map_fundamentalDomain`.
  5. then slice 6: connect `successiveMinimum (intLattice ξ q n) j` to `sm n ξ q j`
     (see ROADMAP). -/

namespace Coeff

/-- The integer lattice inside `Coeff ξ q n`: coefficient vectors with integer entries. -/
noncomputable def intLattice (ξ : ℝ) (q : ℝ) (n : ℕ) : Submodule ℤ (Coeff ξ q n) where
  carrier := {x | ∀ i : Fin (n + 1), ∃ z : ℤ, x.vec i = (z : ℝ)}
  zero_mem' := by
    intro i
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro x y hx hy i
    rcases hx i with ⟨zx, hx'⟩
    rcases hy i with ⟨zy, hy'⟩
    refine ⟨zx + zy, ?_⟩
    change (x + y).vec i = ((zx + zy : ℤ) : ℝ)
    simp [hx', hy']
  smul_mem' := by
    intro z x hx i
    rcases hx i with ⟨zx, hx'⟩
    refine ⟨z * zx, ?_⟩
    change (z • x).vec i = (((z * zx : ℤ)) : ℝ)
    simp [hx']

/-- Nonzero lattice points have norm at least 1 (their sup-norm is an integer ≥ 1). -/
lemma one_le_norm_of_mem_intLattice_ne_zero {ξ : ℝ} {q : ℝ} {n : ℕ} {x : intLattice ξ q n}
    (hx : (x : Coeff ξ q n) ≠ 0) : (1 : ℝ) ≤ ‖(x : Coeff ξ q n)‖ := by
  have hz : ∃ i : Fin (n + 1), (x : Coeff ξ q n).vec i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hx
    apply Coeff.ext
    funext i
    exact hzero i
  rcases hz with ⟨i, hvi⟩
  have hxint : ∃ z : ℤ, (x : Coeff ξ q n).vec i = (z : ℝ) := x.2 i
  rcases hxint with ⟨z, hzi⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hvi
    rw [hzi, hz0]
    norm_num
  have hone : (1 : ℝ) ≤ ‖(x : Coeff ξ q n).vec i‖ := by
    rw [hzi]
    simpa using (one_le_int_norm_cast z hz0)
  calc
    (1 : ℝ) ≤ ‖(x : Coeff ξ q n).vec i‖ := hone
    _ ≤ ‖(x : Coeff ξ q n).vec‖ := by
      simpa using (norm_le_pi_norm (fun k : Fin (n + 1) => (x : Coeff ξ q n).vec k) i)
    _ ≤ ‖(x : Coeff ξ q n)‖ := coeff_le_Nq (x : Coeff ξ q n)

/-- The integer lattice is discrete in `Coeff` (the open unit ball of `Nq` contains no
other lattice point). -/
instance discreteTopology_intLattice (ξ : ℝ) (q : ℝ) (n : ℕ) :
    DiscreteTopology (intLattice ξ q n) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hset : ({0} : Set (intLattice ξ q n)) =
      (fun x : intLattice ξ q n => (x : Coeff ξ q n)) ⁻¹' (Metric.ball (0 : Coeff ξ q n) 1) := by
    ext x
    constructor
    · intro hx0
      subst x
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
      simp
    · intro hx
      apply Subtype.ext
      by_contra hne
      have hone : (1 : ℝ) ≤ ‖(x : Coeff ξ q n)‖ :=
        one_le_norm_of_mem_intLattice_ne_zero (x := x) hne
      have hlt : ‖(x : Coeff ξ q n)‖ < 1 := by
        simpa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] using hx
      linarith
  rw [hset]
  exact (IsOpen.preimage (continuous_subtype_val : Continuous (fun x : intLattice ξ q n => (x : Coeff ξ q n)))
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Coeff ξ q n) 1)))


/-- The `j`-th standard unit vector of the coefficient space (all coordinates 0 except a 1
at coordinate `j`). -/
def ej (ξ : ℝ) (q : ℝ) (n : ℕ) (j : Fin (n + 1)) : Coeff ξ q n :=
  ⟨fun i => if i = j then (1 : ℝ) else 0⟩

/-- Each unit vector lies in the integer lattice. -/
lemma mem_intLattice_ej (ξ : ℝ) (q : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ej ξ q n j ∈ intLattice ξ q n := by
  intro i
  refine ⟨(if i = j then 1 else 0 : ℤ), ?_⟩
  by_cases h : i = j
  · simp [ej, h]
  · simp [ej, h]

@[simp] theorem vec_sum {ξ : ℝ} {q : ℝ} {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Coeff ξ q n) :
    (∑ i ∈ s, f i).vec = ∑ i ∈ s, (f i).vec := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    simp [Finset.sum_insert has, ih]

/-- Every coefficient vector is the (unique) linear combination of the unit vectors with its
own coordinates as coefficients. -/
lemma coeff_eq_sum_ej {ξ : ℝ} {q : ℝ} {n : ℕ} (x : Coeff ξ q n) :
    x = ∑ j : Fin (n + 1), (x.vec j) • ej ξ q n j := by
  apply Coeff.ext
  funext i
  simp [ej, vec_smul, Finset.sum_apply, Finset.sum_ite_eq']

/-- The integer lattice spans the whole coefficient space over ℝ. -/
lemma span_intLattice_top (ξ : ℝ) (q : ℝ) (n : ℕ) :
    Submodule.span ℝ ((intLattice ξ q n : Set (Coeff ξ q n))) = ⊤ := by
  apply eq_top_iff.mpr
  intro x hx
  rw [coeff_eq_sum_ej x]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ (x.vec j)
    (Submodule.subset_span (mem_intLattice_ej ξ q n j)))

/-- The integer lattice is a full ℤ-lattice in the real coefficient space. -/
instance instIsZLattice_intLattice (ξ : ℝ) (q : ℝ) (n : ℕ) :
    IsZLattice ℝ (intLattice ξ q n) where
  span_top := span_intLattice_top ξ q n

/-- The ℤ-rank of the integer lattice is `n + 1` (equal to the real dimension). -/
lemma finrank_intLattice (ξ : ℝ) (q : ℝ) (n : ℕ) :
    Module.finrank ℤ (intLattice ξ q n) = n + 1 := by
  have hrank := ZLattice.rank ℝ (intLattice ξ q n)
  rw [hrank]
  have h := LinearEquiv.finrank_eq (linEquivPi ξ q n)
  rw [h]
  simp
end Coeff



open Module MeasureTheory MeasureTheory.Measure Polynomial
open scoped BigOperators ENNReal

/-! ## Sec3c (M2b slices 5–6, IN PROGRESS)

* covolume of the integer lattice `Coeff.intLattice ξ q n` (w.r.t. the wrapped Lebesgue
  measure on `Coeff ξ q n`) is 1 — by transport to the standard integer lattice in the plain
  coefficient space (`Pi.basisFun`), whose covolume is 1 (unit cube);
* the volume of the unit `Nq`-ball equals the volume of the coefficient body `bodyC n ξ q`
  of Sec2b;
* connection between the lattice successive minima (`Commons.Lattice.SuccessiveMinima.
  successiveMinimum (Coeff.intLattice ξ q n) j`) and the polynomial successive minima
  `sm n ξ q j`: `sm j ≤ successiveMinimum (intLattice) j` for `j ≤ n+1`
  (needs `Commons.LinearAlgebra.Independence.li_real_of_li_int`);
* instantiate `Commons.Lattice.Minkowski.minkowski_second_upper_measure` and Sec2b's
  `body_volume_lower` to get the **M2** product bound
  `∏_{i : Fin (n+1)} sm n ξ q (i+1) ≤ C(n,ξ) · e^q` for all `q ≥ log 2`. -/

namespace Coeff
/-- Volume on `Coeff` is the pushforward of Lebesgue under the wrapping map. -/
lemma volume_eq_map (ξ : ℝ) (q : ℝ) (n : ℕ) :
    (MeasureTheory.volume : Measure (Coeff ξ q n)) =
      (MeasureTheory.volume : Measure (Fin (n + 1) → ℝ)).map
        (fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n)) := by
  rfl

/-- The integer lattice in the plain coefficient space: ℤ-span of the standard unit vectors. -/
def intLatticePi (n : ℕ) : Submodule ℤ (Fin (n + 1) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))

instance discreteTopology_intLatticePi (n : ℕ) : DiscreteTopology (intLatticePi n) := by
  unfold intLatticePi
  exact ZSpan.discreteTopology_pi_basisFun

instance instIsZLattice_intLatticePi (n : ℕ) : IsZLattice ℝ (intLatticePi n) where
  span_top := by
    change (Submodule.span ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))
      : Set (Fin (n + 1) → ℝ))) = ⊤
    exact ZSpan.span_top (Pi.basisFun ℝ (Fin (n + 1)))

/-- Covolume of the standard integer lattice in the plain coefficient space (Lebesgue) is 1. -/
lemma covolume_stdLattice (n : ℕ) :
    ZLattice.covolume (μ := (volume : Measure (Fin (n + 1) → ℝ)))
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) = 1 := by
  classical
  letI : DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) :=
    ZSpan.discreteTopology_pi_basisFun
  letI : IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) :=
    ⟨ZSpan.span_top (Pi.basisFun ℝ (Fin (n + 1)))⟩
  let b : Basis (Fin (n + 1)) ℤ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) :=
    (Pi.basisFun ℝ (Fin (n + 1))).restrictScalars ℤ
  have hc : ZLattice.covolume (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) =
      (volume : Measure (Fin (n + 1) → ℝ)).real
        (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1))))) volume
      (ZLattice.isAddFundamentalDomain b volume)
  rw [hc]
  have hvol := ZSpan.volume_real_fundamentalDomain (b.ofZLatticeBasis ℝ)
  rw [hvol]
  have hvec : ∀ i : Fin (n + 1), (⇑(b.ofZLatticeBasis ℝ) i) = Pi.basisFun ℝ (Fin (n + 1)) i := by
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply]
    rw [Module.Basis.restrictScalars_apply ℤ]
  have hid : (Matrix.of (b.ofZLatticeBasis ℝ)) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    change (⇑(b.ofZLatticeBasis ℝ) i) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j
    rw [hvec i]
    change (⇑(Pi.basisFun ℝ (Fin (n + 1))) i) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j
    rw [Pi.basisFun_apply]
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply, Pi.single_eq_same]
    · simp [Matrix.one_apply, Pi.single_eq_of_ne, h]
  rw [hid, Matrix.det_one, abs_one]

/-- The covolume of the integer coefficient lattice (w.r.t. the wrapped Lebesgue measure) is 1. -/
lemma covolume_intLattice_coeff (ξ : ℝ) (q : ℝ) (n : ℕ) :
    ZLattice.covolume (μ := (volume : Measure (Coeff ξ q n))) (intLattice ξ q n) = 1 := by
  classical
  let ν : Measure (Fin (n + 1) → ℝ) := MeasureTheory.volume
  let μ : Measure (Coeff ξ q n) := MeasureTheory.volume
  let e : (Fin (n + 1) → ℝ) ≃L[ℝ] Coeff ξ q n := (linEquivPi ξ q n).symm.toContinuousLinearEquiv
  have hvolμ : μ = ν.map (fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n)) := by
    dsimp [μ, ν]
    exact volume_eq_map ξ q n
  have hwrap : (⇑e) = fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n) := by
    rfl
  have hmeas : Measurable (⇑e) := e.continuous.measurable
  have hmap : (MeasureTheory.Measure.map (⇑e) ν) = μ := by
    rw [hwrap]
    exact hvolμ
  have hpres : MeasureTheory.MeasurePreserving (⇑e) ν μ := ⟨hmeas, hmap⟩
  have hcov := ZLattice.covolume_comap (E := Coeff ξ q n) (F := Fin (n + 1) → ℝ)
    (L := intLattice ξ q n) (μ := μ) (ν := ν) (e := e) hpres
  have hgoal : ZLattice.covolume (μ := μ) (intLattice ξ q n) = 1 := by
    rw [← hcov]
    let f : (Fin (n + 1) → ℝ) →ₗ[ℝ] Coeff ξ q n := (linEquivPi ξ q n).symm
    change ZLattice.covolume (ZLattice.comap ℝ (intLattice ξ q n) f) ν = 1
    have hcomap : ZLattice.comap ℝ (intLattice ξ q n) f =
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (n + 1)))) := by
      ext v
      constructor
      · intro hv
        rw [(Pi.basisFun ℝ (Fin (n + 1))).mem_span_iff_repr_mem ℤ v]
        change v ∈ (ZLattice.comap ℝ (intLattice ξ q n) f : Set (Fin (n + 1) → ℝ)) at hv
        rw [ZLattice.coe_comap] at hv
        change (⟨v⟩ : Coeff ξ q n) ∈ intLattice ξ q n at hv
        intro i
        rw [Pi.basisFun_repr]
        rcases hv i with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        change (z : ℝ) = v i
        exact hz.symm
      · intro hv
        rw [(Pi.basisFun ℝ (Fin (n + 1))).mem_span_iff_repr_mem ℤ v] at hv
        change v ∈ (ZLattice.comap ℝ (intLattice ξ q n) f : Set (Fin (n + 1) → ℝ))
        rw [ZLattice.coe_comap]
        change (⟨v⟩ : Coeff ξ q n) ∈ intLattice ξ q n
        change ∀ i : Fin (n + 1), ∃ z : ℤ, (⟨v⟩ : Coeff ξ q n).vec i = (z : ℝ)
        intro i
        rcases hv i with ⟨z, hz⟩
        rw [Pi.basisFun_repr] at hz
        refine ⟨z, ?_⟩
        change v i = (z : ℝ)
        exact hz.symm
    rw [hcomap]
    dsimp [ν]
    exact covolume_stdLattice n
  simpa [μ] using hgoal

/-- `e^q · x ≤ 1` iff `x ≤ e^{-q}`. -/
lemma exp_mul_le_one_iff {q x : ℝ} : Real.exp q * x ≤ 1 ↔ x ≤ Real.exp (-q) := by
  have hqneg0 : 0 ≤ Real.exp (-q) := (Real.exp_pos (-q)).le
  have hprod : Real.exp (-q) * Real.exp q = 1 := by
    rw [← Real.exp_add]
    norm_num
  constructor
  · intro h
    calc
      x = (Real.exp (-q) * Real.exp q) * x := by
        rw [hprod]
        ring
      _ = Real.exp (-q) * (Real.exp q * x) := by ring
      _ ≤ Real.exp (-q) * 1 := mul_le_mul_of_nonneg_left h hqneg0
      _ = Real.exp (-q) := by ring
  · intro h
    have hq0 : 0 < Real.exp q := Real.exp_pos q
    calc
      Real.exp q * x ≤ Real.exp q * Real.exp (-q) := mul_le_mul_of_nonneg_left h hq0.le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num

/-- Coefficient of a finite sum of polynomials. -/
@[simp] lemma coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    simp [Finset.sum_insert has, ih]

/-- The norm of a wrapped coefficient vector is the q-height. -/
lemma norm_coeff_eq (ξ : ℝ) (q : ℝ) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    ‖(⟨v⟩ : Coeff ξ q n)‖ = max ‖v‖ (Real.exp q * |ell n ξ v|) := by
  rfl

/-- The unit `Nq`-ball preimage in the coefficient space is the Sec2b body. -/
lemma preball_eq_bodyC (ξ : ℝ) (q : ℝ) (n : ℕ) :
    {v : Fin (n + 1) → ℝ | ‖(⟨v⟩ : Coeff ξ q n)‖ ≤ 1} = bodyC n ξ q := by
  ext v
  change (‖(⟨v⟩ : Coeff ξ q n)‖ ≤ 1) ↔ v ∈ bodyC n ξ q
  rw [bodyC, Set.mem_setOf_eq]
  rw [norm_coeff_eq ξ q n v, max_le_iff]
  constructor
  · intro h
    rcases h with ⟨hball, hval⟩
    constructor
    · intro i
      have hp := (pi_norm_le_iff_of_nonneg (x := v) (r := 1) (by norm_num : (0 : ℝ) ≤ 1)).mp hball
      have hi : ‖v i‖ ≤ 1 := hp i
      simpa [Real.norm_eq_abs] using hi
    · exact (exp_mul_le_one_iff.mp hval)
  · intro h
    constructor
    · apply (pi_norm_le_iff_of_nonneg (x := v) (r := 1) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      simpa [Real.norm_eq_abs] using h.1 i
    · exact exp_mul_le_one_iff.mpr h.2

/-- The Lebesgue-volume of the unit ball in `Coeff` equals the volume of the body. -/
lemma volume_closedBall_eq_bodyC (ξ : ℝ) (q : ℝ) (n : ℕ) :
    (MeasureTheory.volume : Measure (Coeff ξ q n)) (Metric.closedBall (0 : Coeff ξ q n) 1)
      = (MeasureTheory.volume : Measure (Fin (n + 1) → ℝ)) (bodyC n ξ q) := by
  change (Measure.map (fun v : Fin (n + 1) → ℝ => (⟨v⟩ : Coeff ξ q n))
    (MeasureTheory.volume : Measure (Fin (n + 1) → ℝ)))
      (Metric.closedBall (0 : Coeff ξ q n) 1)
      = (MeasureTheory.volume : Measure (Fin (n + 1) → ℝ)) (bodyC n ξ q)
  rw [MeasureTheory.Measure.map_apply]
  · congr 1
    ext v
    constructor
    · intro hv
      have hle : ‖(⟨v⟩ : Coeff ξ q n)‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hv
      rw [← preball_eq_bodyC ξ q n]
      simpa using hle
    · intro hv
      rw [← preball_eq_bodyC ξ q n] at hv
      change (⟨v⟩ : Coeff ξ q n) ∈ Metric.closedBall (0 : Coeff ξ q n) 1
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      simpa using hv
  · exact continuous_inv ξ q n |>.measurable
  · exact Metric.isClosed_closedBall.measurableSet

/-- The integer coefficient of a lattice point at coordinate `i`. -/
noncomputable def intCoeff {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) (i : Fin (n + 1)) :
    ℤ := Classical.choose (x.2 i)

lemma intCoeff_spec {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) (i : Fin (n + 1)) :
    (x : Coeff ξ q n).vec i = ((intCoeff x i : ℤ) : ℝ) :=
  Classical.choose_spec (x.2 i)

/-- The integer polynomial whose coefficients are the entries of a lattice point. -/
noncomputable def polyOfLattice {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    Polynomial ℤ :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i.val : ℕ) (intCoeff x i)

/-- The real polynomial whose coefficients are the entries of a function. -/
def realPoly {n : ℕ} (v : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (n + 1), Polynomial.monomial (k.val : ℕ) (v k)

lemma realPoly_coeff {n : ℕ} (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (realPoly v).coeff (k.val : ℕ) = v k := by
  classical
  dsimp [realPoly]
  rw [coeff_finset_sum]
  rw [Fintype.sum_eq_single k]
  · rw [Polynomial.coeff_monomial]
    simp
  · intro b hb
    rw [Polynomial.coeff_monomial]
    have hb' : b.val ≠ k.val := by
      intro h
      exact hb (Fin.ext h)
    simp [hb']

/-- `realPoly` is injective (coefficient extraction). -/
lemma realPoly_injective {n : ℕ} :
    Function.Injective (realPoly : (Fin (n + 1) → ℝ) → Polynomial ℝ) := by
  intro u v huv
  funext k
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (k.val : ℕ)) huv
  simpa [realPoly_coeff] using hc

/-- The real map of the polynomial of a lattice point is `realPoly` of its coefficient
vector. -/
lemma map_polyOfLattice {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    (polyOfLattice x).map (Int.castRingHom ℝ) = realPoly (x : Coeff ξ q n).vec := by
  dsimp [polyOfLattice, realPoly]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_monomial]
  simp [intCoeff_spec]

/-- The coefficient vector of the polynomial of a lattice point is its own vector. -/
lemma cvec_polyOfLattice {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    cvec (n := n) (polyOfLattice x) = (x : Coeff ξ q n).vec := by
  funext i
  classical
  have hc : (polyOfLattice x).coeff (i.val : ℕ) = intCoeff x i := by
    dsimp [polyOfLattice]
    rw [coeff_finset_sum]
    rw [Fintype.sum_eq_single i]
    · rw [Polynomial.coeff_monomial]
      simp
    · intro b hb
      rw [Polynomial.coeff_monomial]
      have hb' : b.val ≠ i.val := by
        intro h
        exact hb (Fin.ext h)
      simp [hb']
  simp [cvec, hc, intCoeff_spec]

/-- `natDegree` of the lattice polynomial is at most `n`. -/
lemma polyOfLattice_natDegree_le {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    (polyOfLattice x).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  dsimp [polyOfLattice]
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial]
  have hmn : (i.val : ℕ) ≠ m := by
    intro h
    omega
  simp [hmn]

/-- The `Tq`-height of the polynomial built from a lattice point equals its norm. -/
lemma Tq_polyOfLattice {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    Tq ξ q (polyOfLattice x) = ‖(x : Coeff ξ q n)‖ := by
  have hdeg : (polyOfLattice x).natDegree ≤ n := polyOfLattice_natDegree_le x
  have h := Nq_eq_Tq (ξ := ξ) (q := q) (n := n) (P := polyOfLattice x) hdeg
  rw [h]
  congr 1
  apply Coeff.ext
  exact cvec_polyOfLattice x

/-- The polynomial of a nonzero lattice point is nonzero. -/
lemma polyOfLattice_ne_zero {ξ : ℝ} {q : ℝ} {n : ℕ} {x : intLattice ξ q n}
    (hx : (x : Coeff ξ q n) ≠ 0) : polyOfLattice x ≠ 0 := by
  intro hp
  apply hx
  apply Coeff.ext
  have hcv : cvec (n := n) (polyOfLattice x) = (x : Coeff ξ q n).vec := cvec_polyOfLattice x
  rw [← hcv]
  funext i
  simp [cvec, hp]

/-- The real map of the polynomial of a nonzero lattice point is nonzero. -/
lemma realMap_polyOfLattice_ne_zero {ξ : ℝ} {q : ℝ} {n : ℕ} {x : intLattice ξ q n}
    (hx : (x : Coeff ξ q n) ≠ 0) :
    (polyOfLattice x).map (Int.castRingHom ℝ) ≠ 0 := by
  intro hp
  exact (polyOfLattice_ne_zero (x := x) hx)
    (Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using hp))

/-- Degree of the real map of the lattice polynomial is at most `n`. -/
lemma realMap_natDegree_le {ξ : ℝ} {q : ℝ} {n : ℕ} (x : intLattice ξ q n) :
    ((polyOfLattice x).map (Int.castRingHom ℝ)).natDegree ≤ n := by
  rw [int_poly_natDegree_map_eq (polyOfLattice x)]
  exact polyOfLattice_natDegree_le x


/-- Coefficient of `realPoly` at an arbitrary exponent. -/
lemma realPoly_coeff' {n : ℕ} (v : Fin (n + 1) → ℝ) (m : ℕ) :
    (realPoly v).coeff m = if h : m < n + 1 then v ⟨m, h⟩ else 0 := by
  classical
  by_cases hm : m < n + 1
  · let k : Fin (n + 1) := ⟨m, hm⟩
    have hstep : ∀ b : Fin (n + 1), b ≠ k → (Polynomial.monomial (b.val : ℕ) (v b)).coeff m = 0 := by
      intro b hb
      rw [Polynomial.coeff_monomial]
      have hb' : ¬ b.val = m := by
        intro hval
        apply hb
        apply Fin.ext
        calc
          b.val = m := hval
          _ = k.val := rfl
      simp [hb']
    calc
      (realPoly v).coeff m
          = ∑ i : Fin (n + 1), (Polynomial.monomial (i.val : ℕ) (v i)).coeff m := by
              dsimp [realPoly]
              rw [coeff_finset_sum]
      _ = (Polynomial.monomial (k.val : ℕ) (v k)).coeff m := by
              rw [Fintype.sum_eq_single k (fun b hb => hstep b hb)]
      _ = v k := by
              rw [Polynomial.coeff_monomial]
              simp [k]
      _ = if h : m < n + 1 then v ⟨m, h⟩ else 0 := by
              rw [dif_pos hm]
  · have hstep0 : ∀ i : Fin (n + 1), (Polynomial.monomial (i.val : ℕ) (v i)).coeff m = 0 := by
      intro i
      rw [Polynomial.coeff_monomial]
      have hi : (i.val : ℕ) ≠ m := by
        intro h
        omega
      simp [hi]
    calc
      (realPoly v).coeff m
          = ∑ i : Fin (n + 1), (Polynomial.monomial (i.val : ℕ) (v i)).coeff m := by
              dsimp [realPoly]
              rw [coeff_finset_sum]
      _ = 0 := by
              simp [hstep0]
      _ = if h : m < n + 1 then v ⟨m, h⟩ else 0 := by
              rw [dif_neg hm]

/-- The real-coefficient polynomial linear map (coefficient vector ↦ polynomial). -/
def realPolyMap {n : ℕ} : (Fin (n + 1) → ℝ) →ₗ[ℝ] Polynomial ℝ where
  toFun := realPoly
  map_add' := by
    intro u v
    apply Polynomial.ext
    intro m
    by_cases hm : m < n + 1
    · rw [Polynomial.coeff_add, realPoly_coeff', realPoly_coeff', realPoly_coeff']
      rw [dif_pos hm, dif_pos hm, dif_pos hm]
      simp
    · rw [Polynomial.coeff_add, realPoly_coeff', realPoly_coeff', realPoly_coeff']
      rw [dif_neg hm, dif_neg hm, dif_neg hm]
      simp
  map_smul' := by
    intro c u
    apply Polynomial.ext
    intro m
    by_cases hm : m < n + 1
    · rw [Polynomial.coeff_smul, realPoly_coeff', realPoly_coeff']
      rw [dif_pos hm, dif_pos hm]
      simp
    · rw [Polynomial.coeff_smul, realPoly_coeff', realPoly_coeff']
      rw [dif_neg hm, dif_neg hm]
      simp

/-- `realPolyMap` is injective. -/
lemma realPolyMap_ker {n : ℕ} : (realPolyMap (n := n)).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hzero : realPoly x = 0 := by
    simpa [realPolyMap] using hx
  have hz0 : realPoly (0 : (Fin (n + 1) → ℝ)) = 0 := by
    simp [realPoly]
  exact realPoly_injective (by rw [hz0]; exact hzero)

/-- (Hard direction) A radius `r` realized by `j` `ℤ`-independent lattice points is an
`sm`-level: `sm n ξ q j ≤ r`.  (ℤ-independence of integer-coefficient lattice vectors forces
ℝ-independence of the corresponding real polynomials, via the classical
`li_real_of_li_int`.) -/
lemma sm_le_of_successiveMinimum {ξ : ℝ} {q : ℝ} {n : ℕ} {j : ℕ} (hj : j ≤ n + 1) {r : ℝ}
    (hr : 0 ≤ r) (f : Fin j → intLattice ξ q n)
    (hlin : LinearIndependent ℤ (fun a : Fin j => (f a : Coeff ξ q n)))
    (hnorm : ∀ a : Fin j, ‖(f a : Coeff ξ q n)‖ ≤ r) :
    sm n ξ q j ≤ r := by
  letI : DiscreteTopology (intLattice ξ q n) := discreteTopology_intLattice ξ q n
  letI : IsZLattice ℝ (intLattice ξ q n) := instIsZLattice_intLattice ξ q n
  have hR0 : LinearIndependent ℝ (fun a : Fin j => (f a : Coeff ξ q n)) := by
    exact Commons.Lattice.SuccessiveMinima.linearIndependent_real_of_linearIndependent_int
      (E := Coeff ξ q n) (L := intLattice ξ q n) (f := f) hlin
  have hvec_ker : ((linEquivPi ξ q n).toLinearMap.ker = ⊥) := by
    rw [LinearMap.ker_eq_bot]
    exact (linEquivPi ξ q n).injective
  have hRpi : LinearIndependent ℝ (fun a : Fin j => (f a : Coeff ξ q n).vec) := by
    exact (hR0.map' (linEquivPi ξ q n).toLinearMap hvec_ker)
  have hR1 : LinearIndependent ℝ (fun a : Fin j => (realPolyMap (n := n)) ((f a : Coeff ξ q n).vec)) := by
    exact (hRpi.map' (realPolyMap (n := n)) realPolyMap_ker)
  have hRmaps : LinearIndependent ℝ
      (fun a : Fin j => ((polyOfLattice (f a)).map (Int.castRingHom ℝ))) := by
    have heq : (fun a : Fin j => ((polyOfLattice (f a)).map (Int.castRingHom ℝ))) =
        (fun a : Fin j => (realPolyMap (n := n)) ((f a : Coeff ξ q n).vec)) := by
      funext a
      rw [map_polyOfLattice (f a)]
      rfl
    simpa [heq] using hR1
  refine sm_le_of_exists (n := n) (ξ := ξ) (q := q) (j := j) hr
    (fun a => polyOfLattice (f a)) ?_ hRmaps
  intro a
  have hz : (f a : Coeff ξ q n) ≠ 0 := hlin.ne_zero a
  constructor
  · exact polyOfLattice_ne_zero (x := f a) hz
  · constructor
    · exact polyOfLattice_natDegree_le (f a)
    · change Tq ξ q (polyOfLattice (f a)) ≤ r
      rw [Tq_polyOfLattice (f a)]
      exact hnorm a

/-- The polynomial successive minima bound the lattice successive minima from below:
`sm n ξ q j ≤ λⱼ(intLattice ξ q n)` for `j ≤ n + 1`. -/
lemma sm_le_succ (ξ : ℝ) (q : ℝ) (n : ℕ) (j : ℕ) (hj : j ≤ n + 1) :
    sm n ξ q j ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) j := by
  classical
  letI : DiscreteTopology (intLattice ξ q n) := discreteTopology_intLattice ξ q n
  letI : IsZLattice ℝ (intLattice ξ q n) := instIsZLattice_intLattice ξ q n
  unfold Commons.Lattice.SuccessiveMinima.successiveMinimum
  apply le_csInf
  · exact Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet
      (intLattice ξ q n) j (by rw [finrank_intLattice ξ q n]; omega)
  · rintro r ⟨hr0, f, hlin, hnorm⟩
    exact sm_le_of_successiveMinimum (n := n) (ξ := ξ) (q := q) hj hr0 f hlin hnorm

/-- The unit-ball volume of `Coeff` is at least `c·e^{-q}` (from Sec2b's body estimate). -/
lemma ball_volume_lower {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, Real.log 2 ≤ q →
      c * Real.exp (-q) ≤
        ENNReal.toReal ((volume : Measure (Coeff ξ q n))
          (Metric.closedBall (0 : Coeff ξ q n) 1)) := by
  classical
  rcases body_volume_lower (n := n) hn ξ with ⟨c, hc0, hcvol⟩
  refine ⟨c, hc0, ?_⟩
  intro q hq
  have hvolENN : ENNReal.ofReal (c * Real.exp (-q)) ≤
      (volume : Measure (Coeff ξ q n)) (Metric.closedBall (0 : Coeff ξ q n) 1) := by
    rw [volume_closedBall_eq_bodyC ξ q n]
    exact hcvol q hq
  have hfin : (volume : Measure (Coeff ξ q n)) (Metric.closedBall (0 : Coeff ξ q n) 1) ≠ ∞ := by
    exact (ne_of_lt ((ProperSpace.isCompact_closedBall (0 : Coeff ξ q n) 1 :
      IsCompact (Metric.closedBall (0 : Coeff ξ q n) 1)).measure_lt_top))
  have hto : (ENNReal.ofReal (c * Real.exp (-q))).toReal ≤
      ((volume : Measure (Coeff ξ q n)) (Metric.closedBall (0 : Coeff ξ q n) 1)).toReal := by
    exact ENNReal.toReal_mono hfin hvolENN
  rwa [ENNReal.toReal_ofReal (mul_nonneg hc0.le (Real.exp_pos (-q)).le)] at hto

/-- **M2**: product of the polynomial successive minima at level `q` is `≤ C(n,ξ)·e^q` for all
`q ≥ log 2`.  (Minkowski's second theorem in measure form, applied to the integer coefficient
lattice, whose successive minima dominate the polynomial ones, with covolume 1 and the Sec2b
volume lower bound.) -/
theorem minkowski_sm_product_bound {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, Real.log 2 ≤ q →
      (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) ≤ C * Real.exp q := by
  classical
  rcases ball_volume_lower (n := n) hn ξ with ⟨c, hc0, hcvol⟩
  let C : ℝ := (2 : ℝ) ^ (2 * (n + 1)) * c⁻¹
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * (n + 1))) (inv_pos.mpr hc0)
  · intro q hq
    letI : DiscreteTopology (intLattice ξ q n) := discreteTopology_intLattice ξ q n
    letI : IsZLattice ℝ (intLattice ξ q n) := instIsZLattice_intLattice ξ q n
    letI : MeasureSpace (Coeff ξ q n) := instMeasureSpace ξ q n
    letI : BorelSpace (Coeff ξ q n) := instBorelSpace
    letI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure (Coeff ξ q n)) :=
      instIsAddHaarMeasure ξ q n
    have hvol := hcvol q hq
    have hlam : ∀ i : Fin (n + 1),
        0 ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1) := by
      intro i
      exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg (intLattice ξ q n) (i.val + 1)
        (by rw [finrank_intLattice ξ q n]; omega)
    have hsm_le : ∀ i : Fin (n + 1),
        sm n ξ q (i.val + 1) ≤
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1) := by
      intro i
      exact sm_le_succ ξ q n (i.val + 1) (by omega)
    have hprod : (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) ≤
        (∏ i : Fin (n + 1),
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) := by
      refine Finset.prod_le_prod (s := Finset.univ)
        (f := fun i : Fin (n + 1) => sm n ξ q (i.val + 1))
        (g := fun i : Fin (n + 1) =>
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) ?_ ?_
      · intro i hi
        exact sm_nonneg (by omega)
      · intro i hi
        exact hsm_le i
    have hM := Commons.Lattice.Minkowski.minkowski_second_upper_measure
      (d := n + 1) (by omega : 0 < n + 1) (E := Coeff ξ q n) (L := intLattice ξ q n)
      (hfin := finrank_intLattice ξ q n)
    have hcov : ZLattice.covolume (μ := (volume : Measure (Coeff ξ q n))) (intLattice ξ q n) = 1 :=
      covolume_intLattice_coeff ξ q n
    have hM1 : (∏ i : Fin (n + 1),
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) *
          ENNReal.toReal ((volume : Measure (Coeff ξ q n))
            (Metric.closedBall (0 : Coeff ξ q n) 1)) ≤
        (2 : ℝ) ^ (2 * (n + 1)) := by
      calc
        (∏ i : Fin (n + 1),
            Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) *
            ENNReal.toReal ((volume : Measure (Coeff ξ q n))
              (Metric.closedBall (0 : Coeff ξ q n) 1))
            ≤ (2 : ℝ) ^ (2 * (n + 1)) * 1 := by simpa [hcov] using hM
        _ = (2 : ℝ) ^ (2 * (n + 1)) := by ring
    have hlamc : (∏ i : Fin (n + 1),
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) *
          (c * Real.exp (-q)) ≤ (2 : ℝ) ^ (2 * (n + 1)) := by
      calc
        (∏ i : Fin (n + 1),
            Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) *
            (c * Real.exp (-q))
            ≤ (∏ i : Fin (n + 1),
                Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) *
                ENNReal.toReal ((volume : Measure (Coeff ξ q n))
                  (Metric.closedBall (0 : Coeff ξ q n) 1)) :=
              mul_le_mul_of_nonneg_left hvol (Finset.prod_nonneg (by intro i hi; exact hlam i))
        _ ≤ (2 : ℝ) ^ (2 * (n + 1)) := hM1
    have hlamle : (∏ i : Fin (n + 1),
          Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) ≤
        (2 : ℝ) ^ (2 * (n + 1)) * c⁻¹ * Real.exp q := by
      have hdiv := (le_div_iff₀ (mul_pos hc0 (Real.exp_pos (-q)))).mpr hlamc
      calc
        (∏ i : Fin (n + 1),
            Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1))
            ≤ (2 : ℝ) ^ (2 * (n + 1)) / (c * Real.exp (-q)) := hdiv
        _ = (2 : ℝ) ^ (2 * (n + 1)) * c⁻¹ * Real.exp q := by
          rw [Real.exp_neg]
          field_simp [Real.exp_ne_zero, hc0.ne']
    calc
      (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) ≤
          (∏ i : Fin (n + 1),
            Commons.Lattice.SuccessiveMinima.successiveMinimum (intLattice ξ q n) (i.val + 1)) :=
        hprod
      _ ≤ (2 : ℝ) ^ (2 * (n + 1)) * c⁻¹ * Real.exp q := hlamle
      _ = C * Real.exp q := by
        dsimp [C]

end Coeff



open Polynomial
open scoped BigOperators

/-! ## Sec4 (M3, IN PROGRESS): the base construction (paper Lemma 3.3)

Given a polynomial `Q` realizing the first successive minimum at level `q` with active
value-slope, one builds `n+1` independent integer polynomials `P₁ = Q, P₂, …, P_{n+1}`
of degree ≤ n with small values `|pv Pᵢ| < |pv Q|`, monotone heights and a product
`|pv Q|·∏_{i≥2} supN(Pᵢ) ≍ 1`.  This file starts with the analytic input: the upper
product bound derived from the Minkowski bound `minkowski_sm_product_bound` (M2),
together with the slope/value bookkeeping. -/

/-- `sm n ξ q (i.val+1)` over `Fin (n+1)` splits as `sm 1` times the tail
`j = 2..n+1` (`sm (j.val+2)`). -/
lemma prod_sm_succ_eq (n : ℕ) (ξ : ℝ) (q : ℝ) :
    (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) =
      sm n ξ q 1 * (∏ j : Fin n, sm n ξ q (j.val + 2)) := by
  rw [Fin.prod_univ_succ (f := fun i : Fin (n + 1) => sm n ξ q (i.val + 1))]
  congr 1

/-- If the value term realizes the first minimum (`e^q·|pv Q| = sm 1`), then
`|pv Q| = e^{-q}·sm 1`. -/
lemma realizer_value_eq {n : ℕ} {ξ : ℝ} {q : ℝ} {Q : Polynomial ℤ}
    (hval : Real.exp q * |pv ξ Q| = sm n ξ q 1) :
    |pv ξ Q| = Real.exp (-q) * sm n ξ q 1 := by
  calc
    |pv ξ Q| = Real.exp (-q) * (Real.exp q * |pv ξ Q|) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ = Real.exp (-q) * sm n ξ q 1 := by rw [hval]

/-- Product bound for the values at level `q`: if `Q` realizes `sm 1` with the value term
active, then `|pv Q| · ∏_{j=2}^{n+1} sm_j ≤ C(n,ξ)`.  (The analytic engine behind
Lemma 3.3's product estimate `|P₁(ξ)|·‖P₂‖···‖P_{n+1}‖ ≪ 1`.) -/
theorem realizer_value_product_bound {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, Real.log 2 ≤ q → ∀ Q : Polynomial ℤ,
      Real.exp q * |pv ξ Q| = sm n ξ q 1 →
      |pv ξ Q| * (∏ j : Fin n, sm n ξ q (j.val + 2)) ≤ C := by
  classical
  rcases Coeff.minkowski_sm_product_bound (n := n) hn ξ with ⟨CM2, hCM2pos, hM2⟩
  refine ⟨CM2, hCM2pos, ?_⟩
  intro q hq Q hval
  have hle : (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) ≤ CM2 * Real.exp q := hM2 q hq
  have hpq : |pv ξ Q| = Real.exp (-q) * sm n ξ q 1 := realizer_value_eq (Q := Q) hval
  calc
    |pv ξ Q| * (∏ j : Fin n, sm n ξ q (j.val + 2))
        = (Real.exp (-q) * sm n ξ q 1) * (∏ j : Fin n, sm n ξ q (j.val + 2)) := by rw [hpq]
    _ = Real.exp (-q) * (sm n ξ q 1 * (∏ j : Fin n, sm n ξ q (j.val + 2))) := by ring
    _ = Real.exp (-q) * (∏ i : Fin (n + 1), sm n ξ q (i.val + 1)) := by
            rw [prod_sm_succ_eq n ξ q]
    _ ≤ Real.exp (-q) * (CM2 * Real.exp q) :=
            mul_le_mul_of_nonneg_left hle (Real.exp_pos (-q)).le
    _ = CM2 := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
/-- If a nonzero polynomial's value term at level `q` is strictly below the first minimum,
then its height is realized by the sup-norm, which is at least `sm 1`:
`Tq(P) = supN P` and `sm 1 ≤ supN P`.  (Minimality of the first minimum.) -/
lemma norm_active_of_value_lt_sm1 {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ}
    (hdeg : P.natDegree ≤ n) (hP : P ≠ 0)
    (hval : Real.exp q * |pv ξ P| < sm n ξ q 1) :
    Tq ξ q P = supN P ∧ sm n ξ q 1 ≤ supN P := by
  have htq : sm n ξ q 1 ≤ Tq ξ q P := sm1_le_Tq (n := n) (ξ := ξ) (q := q) hP hdeg
  have hTq_ge_sm1 : sm n ξ q 1 ≤ max (supN P) (Real.exp q * |pv ξ P|) := by
    simpa [Tq] using htq
  have hba : Real.exp q * |pv ξ P| ≤ supN P := by
    by_contra hnot
    have hlt : supN P < Real.exp q * |pv ξ P| := lt_of_not_ge hnot
    have hmax : max (supN P) (Real.exp q * |pv ξ P|) = Real.exp q * |pv ξ P| :=
      max_eq_right (le_of_lt hlt)
    have hsm : sm n ξ q 1 ≤ Real.exp q * |pv ξ P| := by
      rw [← hmax]
      exact hTq_ge_sm1
    exact (not_lt_of_ge hsm) hval
  have hmax : max (supN P) (Real.exp q * |pv ξ P|) = supN P := max_eq_left hba
  constructor
  · simpa [Tq] using hmax
  · rw [← hmax]
    exact hTq_ge_sm1
/-- Slope (value term active) + first-minimum realization ⇒ the value term equals `sm 1`. -/
lemma value_active_eq {n : ℕ} {ξ : ℝ} {q : ℝ} {Q : Polynomial ℤ}
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hreal : Tq ξ q Q = sm n ξ q 1) :
    Real.exp q * |pv ξ Q| = sm n ξ q 1 := by
  have hmax : max (supN Q) (Real.exp q * |pv ξ Q|) = Real.exp q * |pv ξ Q| := max_eq_right hslope
  have hTq : Tq ξ q Q = Real.exp q * |pv ξ Q| := by simpa [Tq] using hmax
  rw [hTq] at hreal
  exact hreal

/-- **M3(a)**: extension of the given first-realizer `Q` to a full linearly independent
family `R : Fin (n+1) → ℤ[X]` with `R 0 = Q` and `Tq(R i) ≤ sm (i.val+1) + 1`. -/
lemma extend_family_from_Q {n : ℕ} {ξ : ℝ} {q : ℝ} (Q : Polynomial ℤ)
    (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ n) (hTq : Tq ξ q Q ≤ sm n ξ q 1 + 1) :
    ∃ R : Fin (n + 1) → Polynomial ℤ,
      R 0 = Q ∧
      (∀ i : Fin (n + 1), R i ≠ 0 ∧ (R i).natDegree ≤ n ∧
        Tq ξ q (R i) ≤ sm n ξ q (i.val + 1) + 1) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (R i).map (Int.castRingHom ℝ)) := by
  classical
  -- P m: a family indexed by Fin (m+1) starting at Q
  let P : ℕ → Prop := fun m => ∃ R : Fin (m + 1) → Polynomial ℤ,
      R 0 = Q ∧
      (∀ i : Fin (m + 1), R i ≠ 0 ∧ (R i).natDegree ≤ n ∧
        Tq ξ q (R i) ≤ sm n ξ q (i.val + 1) + 1) ∧
      LinearIndependent ℝ (fun i : Fin (m + 1) => (R i).map (Int.castRingHom ℝ))
  have hP0 : P 0 := by
    refine ⟨fun _ : Fin 1 => Q, ?_, ?_, ?_⟩
    · rfl
    · intro i
      have hi : (i.val : ℕ) = 0 := by omega
      constructor
      · exact hQ
      · constructor
        · exact hdeg
        · have hsm : sm n ξ q (i.val + 1) + 1 = sm n ξ q 1 + 1 := by rw [hi]
          rw [hsm]
          exact hTq
    · have hmap0 : (Q.map (Int.castRingHom ℝ)) ≠ 0 := by
        intro hz
        apply hQ
        exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using hz)
      exact (linearIndependent_subsingleton_index_iff
        (f := fun i : Fin 1 => (Q.map (Int.castRingHom ℝ)))).2 (by intro i; exact hmap0)
  have hstep : ∀ m : ℕ, m < n → P m → P (m + 1) := by
    intro m hmlt hPm
    rcases hPm with ⟨R, hR0, hRb, hRli⟩
    rcases extend_family (n := n) (ξ := ξ) (q := q) (by omega : m + 1 < n + 1) hRb hRli
      with ⟨R', hR'ext, hR'b, hR'li⟩
    refine ⟨R', ?_, hR'b, hR'li⟩
    have hzero : (0 : Fin (m + 2)) = Fin.castSucc (0 : Fin (m + 1)) := by
      apply Fin.ext
      simp
    rw [hzero]
    have hcast : R' (Fin.castSucc (0 : Fin (m + 1))) = R (0 : Fin (m + 1)) := hR'ext 0
    rw [hcast]
    exact hR0
  have hall : ∀ m : ℕ, m ≤ n → P m := by
    intro m
    induction m with
    | zero => intro hm; exact hP0
    | succ m ih =>
        intro hmn
        have hm : m ≤ n := by omega
        exact hstep m (by omega) (ih hm)
  exact hall n (by rfl)


/-- A value-active first-realizer has nonzero value at ξ. -/
lemma realizer_pv_ne_zero {n : ℕ} {ξ : ℝ} {q : ℝ} {Q : Polynomial ℤ}
    (hval : Real.exp q * |pv ξ Q| = sm n ξ q 1) :
    pv ξ Q ≠ 0 := by
  have hsm : 0 < sm n ξ q 1 :=
    lt_of_lt_of_le zero_lt_one (sm_one_le (n := n) (ξ := ξ) (q := q))
  have hpos : 0 < Real.exp q * |pv ξ Q| := by
    rw [hval]
    exact hsm
  intro hpv
  have hz : Real.exp q * |pv ξ Q| = 0 := by
    rw [hpv]
    simp
  rw [hz] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- Value strictly below the realizer's and height at most `3·B`: the M3(b) correction
`A ↦ A − C(⌊pv A / pv Q⌋)·Q` keeps the value tiny and the height controlled by the
`Tq`-level `B` (for `Q` a value-active realizer and `sm 1 ≤ B`). -/
lemma corr_value_norm_bound {n : ℕ} {ξ : ℝ} {q : ℝ} {Q A : Polynomial ℤ} (B : ℝ)
    (hpv : pv ξ Q ≠ 0)
    (hval : Real.exp q * |pv ξ Q| = sm n ξ q 1)
    (hslopeQ : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hBge : sm n ξ q 1 ≤ B)
    (hATq : Tq ξ q A ≤ B) :
    let k : ℤ := corrInt (pv ξ A) (pv ξ Q) hpv
    |pv ξ (A - Polynomial.C k * Q)| < |pv ξ Q| ∧
    supN (A - Polynomial.C k * Q) ≤ 3 * B := by
  intro k
  dsimp [k]
  have hsmpos : 0 < sm n ξ q 1 :=
    lt_of_lt_of_le zero_lt_one (sm_one_le (n := n) (ξ := ξ) (q := q))
  have hQabs : 0 < |pv ξ Q| := by
    have hpos : 0 < Real.exp q * |pv ξ Q| := by
      rw [hval]
      exact hsmpos
    exact (mul_pos_iff_of_pos_left (Real.exp_pos q)).mp hpos
  constructor
  · have hcv := corr_value_lt (ξ := ξ) (Q1 := Q) (Q2 := A) hpv
    -- hcv : let k := corrInt (pv A) (pv Q) hpv; |pv (A − C k Q)| < |pv Q|
    simpa [corrInt] using hcv
  · have h1e : supN A ≤ B := le_trans (supN_le_Tq ξ q A) hATq
    have hQ_sm : supN Q ≤ sm n ξ q 1 := hslopeQ.trans_eq hval
    have hQ_le_B : supN Q ≤ B := le_trans hQ_sm hBge
    have hsm_div : sm n ξ q 1 / |pv ξ Q| = Real.exp q := by
      have hpq := realizer_value_eq (Q := Q) hval
      -- hpq : |pv Q| = e^{-q} sm 1
      rw [hpq]
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero, ne_of_gt hsmpos]
    have hratio_sm : (|pv ξ A| / |pv ξ Q|) * sm n ξ q 1 ≤ B := by
      calc
        (|pv ξ A| / |pv ξ Q|) * sm n ξ q 1 = |pv ξ A| * (sm n ξ q 1 / |pv ξ Q|) := by ring
        _ = |pv ξ A| * Real.exp q := by rw [hsm_div]
        _ = Real.exp q * |pv ξ A| := by ring
        _ ≤ B := le_trans (Tq_exp_le ξ q A) hATq
    have hratio_le : (|pv ξ A| / |pv ξ Q|) * supN Q ≤ B := by
      calc
        (|pv ξ A| / |pv ξ Q|) * supN Q
            ≤ (|pv ξ A| / |pv ξ Q|) * sm n ξ q 1 := by
              exact mul_le_mul_of_nonneg_left hQ_sm
                (div_nonneg (abs_nonneg _) (le_of_lt hQabs))
        _ ≤ B := hratio_sm
    have hnorm_raw := corr_supN_bound (ξ := ξ) (Q1 := Q) (Q2 := A) hpv
    -- hnorm_raw : let k := corrInt (pv A) (pv Q) hpv;
    --             supN (A − C k Q) ≤ supN A + (|pv A|/|pv Q|)·supN Q + supN Q
    have hnorm : supN (A - Polynomial.C (corrInt (pv ξ A) (pv ξ Q) hpv) * Q) ≤
        supN A + (|pv ξ A| / |pv ξ Q|) * supN Q + supN Q := by
      simpa [corrInt] using hnorm_raw
    linarith [hnorm, h1e, hratio_le, hQ_le_B]


/-- **M3(b)**: the extension family `R` from `extend_family_from_Q`, corrected at every
index `i ≠ 0` by `R i ↦ R i − ⌊pv(R i)/pv Q⌋·Q`.  Keeps `Q` as the first element, forces
values below `|pv Q|`, and bounds the heights by `3·(sm (i.val+1) + 1)`. -/
lemma corrected_family {n : ℕ} {ξ : ℝ} {q : ℝ} (Q : Polynomial ℤ)
    (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|) :
    ∃ C : Fin (n + 1) → Polynomial ℤ,
      C 0 = Q ∧
      (∀ i : Fin (n + 1), i ≠ 0 →
        (C i).natDegree ≤ n ∧ |pv ξ (C i)| < |pv ξ Q| ∧
        supN (C i) ≤ 3 * (sm n ξ q (i.val + 1) + 1)) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)) := by
  classical
  have hval : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
  have hpv : pv ξ Q ≠ 0 := realizer_pv_ne_zero (Q := Q) hval
  have hTq : Tq ξ q Q ≤ sm n ξ q 1 + 1 := by
    rw [hreal]
    linarith
  rcases extend_family_from_Q (n := n) (ξ := ξ) (q := q) Q hQ hdeg hTq with ⟨R, hR0, hRb, hRli⟩
  let C : Fin (n + 1) → Polynomial ℤ := fun i =>
    if h : i = 0 then Q else R i - Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C]
  · intro i hi
    have hiLt : (i.val : ℕ) < n + 1 := i.isLt
    have hile : (i.val : ℕ) ≤ n := by omega
    have hsm1 : sm n ξ q 1 ≤ sm n ξ q (i.val + 1) := by
      exact sm_mono (n := n) (ξ := ξ) (q := q) (by omega : (1 : ℕ) ≤ i.val + 1)
        (by omega)
    have hBge : sm n ξ q 1 ≤ sm n ξ q (i.val + 1) + 1 := le_trans hsm1 (by linarith)
    have hbnd := corr_value_norm_bound (n := n) (ξ := ξ) (q := q) (Q := Q) (A := R i)
      (sm n ξ q (i.val + 1) + 1) hpv hval hslope hBge (hRb i).2.2
    have hsub : C i = R i - Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q := by
      dsimp [C]
      rw [if_neg hi]
    have hmain : |pv ξ (R i - Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q)| < |pv ξ Q| ∧
        supN (R i - Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q) ≤
          3 * (sm n ξ q (i.val + 1) + 1) := by
      simpa using hbnd
    constructor
    · -- natDegree (C i) ≤ n
      rw [hsub]
      have h1 : ((Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q).natDegree) ≤ n :=
        le_trans (Polynomial.natDegree_C_mul_le (corrInt (pv ξ (R i)) (pv ξ Q) hpv) Q) hdeg
      have hs := Polynomial.natDegree_sub_le (R i)
        (Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q)
      exact le_trans hs (max_le (hRb i).2.1 h1)
    · simpa [hsub] using hmain
  · -- linear independence of the corrected family: a shear of the independent R-family
    have hQ_R0 : Q = R (0 : Fin (n + 1)) := hR0.symm
    have hcv : (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)) =
        (fun i : Fin (n + 1) =>
          (R i).map (Int.castRingHom ℝ) - (if i = 0 then 0 else
            ((corrInt (pv ξ (R i)) (pv ξ Q) hpv : ℤ) : ℝ) •
              (R (0 : Fin (n + 1))).map (Int.castRingHom ℝ))) := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [C, hQ_R0]
      · dsimp [C]
        rw [if_neg hi]
        -- map of the correction: map(R i − C k Q) = map(R i) − (k:ℝ) • map(R 0)
        have hmap_corr : ((R i - Polynomial.C (corrInt (pv ξ (R i)) (pv ξ Q) hpv) * Q).map
            (Int.castRingHom ℝ)) =
            (R i).map (Int.castRingHom ℝ) -
              ((corrInt (pv ξ (R i)) (pv ξ Q) hpv : ℤ) : ℝ) •
                (Q.map (Int.castRingHom ℝ)) := by
          rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C]
          simp [Algebra.smul_def]
        rw [hmap_corr]
        have hq : ((corrInt (pv ξ (R i)) (pv ξ Q) hpv : ℤ) : ℝ) •
              (Q.map (Int.castRingHom ℝ)) =
            ((corrInt (pv ξ (R i)) (pv ξ Q) hpv : ℤ) : ℝ) •
              (R (0 : Fin (n + 1))).map (Int.castRingHom ℝ) := by
          congr 1
          exact congrArg (fun P : Polynomial ℤ => P.map (Int.castRingHom ℝ)) hQ_R0
        rw [if_neg hi]
        simp [hq]
    have hli := Commons.LinearAlgebra.Independence.linearIndependent_sub_smul_pivot
      (a := (0 : Fin (n + 1)))
      (v := fun i : Fin (n + 1) => (R i).map (Int.castRingHom ℝ))
      (m := fun i : Fin (n + 1) => ((corrInt (pv ξ (R i)) (pv ξ Q) hpv : ℤ) : ℝ)) hRli
    simpa [hcv] using hli



/-- A corrected polynomial with value strictly below `|pv Q|` (for a value-active
first-realizer `Q`) is norm-active and has height at least `sm 1`. -/
lemma corr_active {n : ℕ} {ξ : ℝ} {q : ℝ} {Q C : Polynomial ℤ}
    (hdeg : C.natDegree ≤ n) (hC : C ≠ 0)
    (hval : Real.exp q * |pv ξ Q| = sm n ξ q 1)
    (hlt : |pv ξ C| < |pv ξ Q|) :
    sm n ξ q 1 ≤ supN C ∧ Tq ξ q C = supN C := by
  have hval2 : Real.exp q * |pv ξ C| < sm n ξ q 1 := by
    have hqq : 0 < Real.exp q := Real.exp_pos q
    calc
      Real.exp q * |pv ξ C| < Real.exp q * |pv ξ Q| := mul_lt_mul_of_pos_left hlt hqq
      _ = sm n ξ q 1 := hval
  have hmain := norm_active_of_value_lt_sm1 (n := n) (ξ := ξ) (q := q) (P := C) hdeg hC hval2
  exact ⟨hmain.2, hmain.1⟩

/-- Members of a linearly independent family of polynomial maps are nonzero. -/
lemma li_poly_ne_zero {n : ℕ} {C : Fin (n + 1) → Polynomial ℤ}
    (hli : LinearIndependent ℝ (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)))
    (i : Fin (n + 1)) : C i ≠ 0 := by
  have hnz : ((C i).map (Int.castRingHom ℝ)) ≠ 0 := hli.ne_zero i
  intro hz
  apply hnz
  rw [hz]
  simp


/-- Constant product over `Fin n`: `∏ a = a^n`. -/
lemma prod_const_pow {n : ℕ} (a : ℝ) : (∏ j : Fin n, a) = a ^ n := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Pulling a constant out of a product over `Fin n`. -/
lemma prod_mul_const {n : ℕ} (a : ℝ) (f : Fin n → ℝ) :
    (∏ j : Fin n, a * f j) = a ^ n * (∏ j : Fin n, f j) := by
  calc
    (∏ j : Fin n, a * f j) = (∏ j : Fin n, a) * (∏ j : Fin n, f j) := by
      rw [Finset.prod_mul_distrib]
    _ = a ^ n * (∏ j : Fin n, f j) := by rw [prod_const_pow a]

/-- **M3(b3) upper**: for a value-active first-realizer `Q` at level `q ≥ log 2`, any
family `C₀` starting at `Q` whose other members meet the M3(b) height bounds satisfies
`|pv Q| · ∏_{j:Fin n} supN (C₀ (Fin.succ j)) ≤ C(n,ξ)` (assertion (3) of Lemma 3.3,
upper side). -/
theorem corrected_product_upper {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, Real.log 2 ≤ q → ∀ Q : Polynomial ℤ,
      Q ≠ 0 → Q.natDegree ≤ n → Tq ξ q Q = sm n ξ q 1 →
      supN Q ≤ Real.exp q * |pv ξ Q| →
      ∀ C₀ : Fin (n + 1) → Polynomial ℤ,
        C₀ 0 = Q →
        (∀ i : Fin (n + 1), i ≠ 0 →
          supN (C₀ i) ≤ 3 * (sm n ξ q (i.val + 1) + 1)) →
        |pv ξ Q| * (∏ j : Fin n, supN (C₀ (Fin.succ j))) ≤ C := by
  classical
  rcases realizer_value_product_bound (n := n) hn ξ with ⟨C1, hC1pos, hC1⟩
  let C : ℝ := (6 : ℝ) ^ n * C1
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro q hq Q hQ hdeg hreal hslope C₀ hC0 hbounds
    have hvalQ : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
    have hQabs0 : 0 ≤ |pv ξ Q| := abs_nonneg _
    have hsmge : ∀ j : Fin n, (1 : ℝ) ≤ sm n ξ q (j.val + 2) := by
      intro j
      have hj1 : (1 : ℕ) ≤ j.val + 2 := by omega
      have hjl : j.val + 2 ≤ n + 1 := by omega
      exact le_trans (sm_one_le (n := n) (ξ := ξ) (q := q))
        (sm_mono (n := n) (ξ := ξ) (q := q) hj1 hjl)
    have hjl : ∀ j : Fin n, (j.val : ℕ) + 2 ≤ n + 1 := by
      intro j
      have hjlt : j.val < n := j.isLt
      omega
    have hidx : ∀ j : Fin n, (Fin.succ j).val + 1 = j.val + 2 := by
      intro j
      rw [Fin.val_succ]
    have hfac0 : ∀ j : Fin n, supN (C₀ (Fin.succ j)) ≤ 3 * (sm n ξ q (j.val + 2) + 1) := by
      intro j
      have hnz : Fin.succ j ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
      have hb := hbounds (Fin.succ j) hnz
      -- supN(C₀(succ j)) ≤ 3(sm_{succ j.val+1} + 1); reindex (succ j).val + 1 = j.val + 2
      simpa [hidx j] using hb
    have hfac : ∀ j : Fin n,
        3 * (sm n ξ q (j.val + 2) + 1) ≤ 6 * sm n ξ q (j.val + 2) := by
      intro j
      nlinarith [hsmge j]
    have htotal1 : (∏ j : Fin n, supN (C₀ (Fin.succ j))) ≤
        (6 : ℝ) ^ n * (∏ j : Fin n, sm n ξ q (j.val + 2)) := by
      calc
        (∏ j : Fin n, supN (C₀ (Fin.succ j)))
            ≤ ∏ j : Fin n, 3 * (sm n ξ q (j.val + 2) + 1) := by
              refine Finset.prod_le_prod (s := Finset.univ)
                (f := fun j : Fin n => supN (C₀ (Fin.succ j)))
                (g := fun j : Fin n => 3 * (sm n ξ q (j.val + 2) + 1)) ?_ ?_
              · intro j hj
                exact supN_nonneg (C₀ (Fin.succ j))
              · intro j hj
                exact hfac0 j
        _ ≤ ∏ j : Fin n, 6 * sm n ξ q (j.val + 2) := by
              refine Finset.prod_le_prod (s := Finset.univ)
                (f := fun j : Fin n => 3 * (sm n ξ q (j.val + 2) + 1))
                (g := fun j : Fin n => 6 * sm n ξ q (j.val + 2)) ?_ ?_
              · intro j hj
                exact mul_nonneg (by norm_num)
                  (by linarith [sm_nonneg (n := n) (ξ := ξ) (q := q) (hjl j)])
              · intro j hj
                exact hfac j
        _ = (6 : ℝ) ^ n * (∏ j : Fin n, sm n ξ q (j.val + 2)) := by
              exact prod_mul_const (6 : ℝ) (fun j : Fin n => sm n ξ q (j.val + 2))
    have hvalBound : |pv ξ Q| * (∏ j : Fin n, sm n ξ q (j.val + 2)) ≤ C1 := hC1 q hq Q hvalQ
    calc
      |pv ξ Q| * (∏ j : Fin n, supN (C₀ (Fin.succ j)))
          ≤ |pv ξ Q| * ((6 : ℝ) ^ n * (∏ j : Fin n, sm n ξ q (j.val + 2))) :=
              mul_le_mul_of_nonneg_left htotal1 hQabs0
      _ = (6 : ℝ) ^ n * (|pv ξ Q| * (∏ j : Fin n, sm n ξ q (j.val + 2))) := by ring
      _ ≤ (6 : ℝ) ^ n * C1 :=
              mul_le_mul_of_nonneg_left hvalBound (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) n)
      _ = C := by
              dsimp [C]


/-- Splitting a `Fin (n+1)`-product at the zero index. -/
lemma prod_succ_split {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∏ i : Fin (n + 1), f i) = f 0 * (∏ j : Fin n, f (Fin.succ j)) := by
  rw [Fin.prod_univ_succ (f := f)]

/-- **M3(b3) lower**: for a value-active first-realizer `Q` (deg ≤ n, `Tq = sm 1`,
norm-slope) and a linearly independent family `C₀ : Fin (n+1) → ℤ[X]` starting at `Q`
with `deg ≤ n` and values `|pv(C₀ i)| < |pv Q|` for `i ≠ 0`, one has
`1 ≤ C · (|pv Q| · ∏_{j:Fin n} supN (C₀ (Fin.succ j)))` (det_facile + the ratio bound
`|pv(C₀ i)|/supN(C₀ i) ≤ |pv Q|/supN Q`). -/
theorem corrected_product_lower {n : ℕ} (hn : 1 ≤ n) (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, ∀ Q : Polynomial ℤ,
      Q ≠ 0 → Q.natDegree ≤ n → Tq ξ q Q = sm n ξ q 1 →
      supN Q ≤ Real.exp q * |pv ξ Q| →
      ∀ C₀ : Fin (n + 1) → Polynomial ℤ,
        C₀ 0 = Q →
        (∀ i : Fin (n + 1), (C₀ i).natDegree ≤ n) →
        LinearIndependent ℝ (fun i : Fin (n + 1) => (C₀ i).map (Int.castRingHom ℝ)) →
        (∀ i : Fin (n + 1), i ≠ 0 → |pv ξ (C₀ i)| < |pv ξ Q|) →
        1 ≤ C * (|pv ξ Q| * (∏ j : Fin n, supN (C₀ (Fin.succ j)))) := by
  classical
  rcases poly_det_facile n hn ξ with ⟨c, hc0, hdet⟩
  let C : ℝ := c * (n + 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos hc0 (by positivity : 0 < (n + 1 : ℝ))
  · intro q Q hQ hdegQ hreal hslope C₀ hC0 hdeg hli hval0
    have hvalQ : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
    have hpv : pv ξ Q ≠ 0 := realizer_pv_ne_zero (Q := Q) hvalQ
    have hQabs0 : 0 < |pv ξ Q| := abs_pos.mpr hpv
    have hQsup0 : 0 < supN Q := supN_pos_of_ne_zero hQ
    have hdetC : 1 ≤ c * (∏ i : Fin (n + 1), supN (C₀ i)) *
        (∑ i : Fin (n + 1), |pv ξ (C₀ i)| / supN (C₀ i)) := by
      simpa [supN, pv, Real.norm_eq_abs] using hdet C₀ hdeg hli
    have hsupQ : ∀ i : Fin (n + 1), i ≠ 0 → supN Q ≤ supN (C₀ i) := by
      intro i hi
      have hC0nz : C₀ i ≠ 0 := li_poly_ne_zero (C := C₀) hli i
      have hdegI : (C₀ i).natDegree ≤ n := hdeg i
      have hcorr := corr_active (Q := Q) (C := C₀ i) hdegI hC0nz hvalQ (hval0 i hi)
      have hQsup : supN Q ≤ sm n ξ q 1 := by
        have ht := supN_le_Tq ξ q Q
        rwa [hreal] at ht
      exact le_trans hQsup hcorr.1
    have hratio : ∀ i : Fin (n + 1),
        |pv ξ (C₀ i)| / supN (C₀ i) ≤ |pv ξ Q| / supN Q := by
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [hC0]
      · exact div_le_div₀ (abs_nonneg _) (le_of_lt (hval0 i hi)) hQsup0 (hsupQ i hi)
    have hsum : (∑ i : Fin (n + 1), |pv ξ (C₀ i)| / supN (C₀ i)) ≤
        (n + 1) * (|pv ξ Q| / supN Q) := by
      calc
        (∑ i : Fin (n + 1), |pv ξ (C₀ i)| / supN (C₀ i))
            ≤ ∑ i : Fin (n + 1), (|pv ξ Q| / supN Q) := by
              exact Finset.sum_le_sum (fun i hi => hratio i)
        _ = (n + 1) * (|pv ξ Q| / supN Q) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              ring
    have hprod : (∏ i : Fin (n + 1), supN (C₀ i)) =
        supN Q * (∏ j : Fin n, supN (C₀ (Fin.succ j))) := by
      rw [prod_succ_split (f := fun i : Fin (n + 1) => supN (C₀ i))]
      congr 1
      rw [hC0]
    have hmain0 : 1 ≤ c * (∏ i : Fin (n + 1), supN (C₀ i)) *
        ((n + 1) * (|pv ξ Q| / supN Q)) := by
      calc
        1 ≤ c * (∏ i : Fin (n + 1), supN (C₀ i)) *
            (∑ i : Fin (n + 1), |pv ξ (C₀ i)| / supN (C₀ i)) := hdetC
        _ ≤ c * (∏ i : Fin (n + 1), supN (C₀ i)) * ((n + 1) * (|pv ξ Q| / supN Q)) := by
              exact mul_le_mul_of_nonneg_left hsum
                (mul_nonneg hc0.le (Finset.prod_nonneg (fun i hi => supN_nonneg (C₀ i))))
    have hfin : c * (∏ i : Fin (n + 1), supN (C₀ i)) * ((n + 1) * (|pv ξ Q| / supN Q)) =
        (c * (n + 1)) * (|pv ξ Q| * (∏ j : Fin n, supN (C₀ (Fin.succ j)))) := by
      rw [hprod]
      field_simp [ne_of_gt hQsup0]
    have hgoal : 1 ≤ (c * (n + 1)) * (|pv ξ Q| * (∏ j : Fin n, supN (C₀ (Fin.succ j)))) := by
      rw [← hfin]
      exact hmain0
    simpa [C] using hgoal


/-- **M3(c)**: norm-sorting of a family.  Any `Fin n`-indexed family of integer polynomials
can be reindexed by a permutation so that its sup-norms are nondecreasing, with the product
of the sup-norms preserved (the sorting step used when the base construction's tail is
ordered by increasing height). -/
lemma exists_norm_sorted {n : ℕ} (w : Fin n → Polynomial ℤ) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ i j : Fin n, i.val ≤ j.val → supN (w (σ i)) ≤ supN (w (σ j))) ∧
      ((∏ i : Fin n, supN (w (σ i))) = (∏ i : Fin n, supN (w i))) := by
  classical
  rcases Commons.Combinatorics.Reindex.monotone_perm (f := fun i : Fin n => supN (w i))
    with ⟨σ, hσ⟩
  refine ⟨σ, ?_, ?_⟩
  · intro i j hij
    exact hσ i j hij
  · calc
      (∏ i : Fin n, supN (w (σ i))) = ∏ j : Fin n, supN (w j) := by
        refine Finset.prod_bij (s := Finset.univ) (t := Finset.univ)
          (fun a ha => σ a) (fun a ha => by simp)
          (fun a ha b hb h => by exact σ.injective h)
          (fun b hb => ⟨σ.symm b, by simp, σ.apply_symm_apply b⟩)
          (fun a ha => rfl)

/-- Linear independence is invariant under reindexing a family by a permutation. -/
lemma li_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : Fin n → Polynomial ℤ)
    (hli : LinearIndependent ℝ (fun i : Fin n => (w i).map (Int.castRingHom ℝ))) :
    LinearIndependent ℝ (fun i : Fin n => (w (σ i)).map (Int.castRingHom ℝ)) := by
  exact hli.comp σ σ.injective




open Polynomial
open scoped BigOperators

/-! ## Sec5 (M4, IN PROGRESS): the hA slope lemma
(paper "estimation Q(xi) qui réalise L1")

Fix a lower exponent `wbar` for which hA holds: for every `H ≥ H0` there is a nonzero
integer polynomial of degree ≤ n with `supN ≤ H` and `|pv| ≤ H^(-wbar)`.  If `Q` is a
value-active first-realizer at level `q` (with `sm 1` large enough that `sm 1 / 2 ≥ H0`),
then `|pv Q| ≤ (sm 1 / 2)^(-wbar)`.  The three steps:
(1) `hA_solution_lt_sm1`: apply hA at `H := sm 1 / 2` to get a solution with strict
    `supN < sm 1`;
(2) `value_active_of_supN_lt_sm1`: such a polynomial is value-active (`sm 1 ≤ e^q·|pv|`)
    by minimality of the first minimum;
(3) `realizer_value_le_oracle`: the realizer's value is below that of any value-active
    solution, so `|pv Q| ≤ (sm 1 / 2)^(-wbar)`. -/

/-- hA-oracle: for every `H ≥ H0` a nonzero degree-≤-n integer polynomial with height
`≤ H` and value `≤ H^(-wbar)`. -/
def WbarOracle (n : ℕ) (ξ : ℝ) (wbar : ℝ) (H0 : ℝ) : Prop :=
  ∀ H : ℝ, H0 ≤ H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧
    supN P ≤ H ∧ |pv ξ P| ≤ H ^ (-wbar)

/-- **M4 (1)**: applying the oracle at `H := sm 1 / 2` (legal once `sm 1 / 2 ≥ H0`)
gives a strict-height solution `supN P < sm 1` with the oracle value bound. -/
lemma hA_solution_lt_sm1 {n : ℕ} {ξ : ℝ} {q : ℝ} {wbar : ℝ} {H0 : ℝ}
    (hA : WbarOracle n ξ wbar H0) (hsm0 : H0 ≤ sm n ξ q 1 / 2) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ supN P < sm n ξ q 1 ∧
      |pv ξ P| ≤ (sm n ξ q 1 / 2) ^ (-wbar) := by
  rcases hA (sm n ξ q 1 / 2) hsm0 with ⟨P, hPnz, hdeg, hsup, hval⟩
  refine ⟨P, hPnz, hdeg, ?_, hval⟩
  have hsm1 : 1 ≤ sm n ξ q 1 := sm_one_le (n := n) (ξ := ξ) (q := q)
  have hsm0' : 0 < sm n ξ q 1 := lt_of_lt_of_le zero_lt_one hsm1
  calc
    supN P ≤ sm n ξ q 1 / 2 := hsup
    _ < sm n ξ q 1 := by nlinarith

/-- **M4 (2)**: a polynomial of degree ≤ n with `supN P < sm 1` is value-active:
`sm 1 ≤ e^q·|pv P|` and `Tq(P) = e^q·|pv P|` (minimality of the first minimum). -/
lemma value_active_of_supN_lt_sm1 {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ}
    (hdeg : P.natDegree ≤ n) (hP : P ≠ 0) (hlt : supN P < sm n ξ q 1) :
    sm n ξ q 1 ≤ Real.exp q * |pv ξ P| ∧ Tq ξ q P = Real.exp q * |pv ξ P| := by
  have htq : sm n ξ q 1 ≤ Tq ξ q P := sm1_le_Tq (n := n) (ξ := ξ) (q := q) hP hdeg
  have hba : supN P < Real.exp q * |pv ξ P| := by
    by_contra hnot
    have hle : Real.exp q * |pv ξ P| ≤ supN P := le_of_not_gt hnot
    have hmax : Tq ξ q P = supN P := by
      rw [Tq]
      exact max_eq_left hle
    have hsmP : sm n ξ q 1 ≤ supN P := by
      rwa [hmax] at htq
    exact (not_lt_of_ge hsmP) hlt
  have hval : Tq ξ q P = Real.exp q * |pv ξ P| := by
    rw [Tq]
    exact max_eq_right (le_of_lt hba)
  constructor
  · rwa [hval] at htq
  · exact hval

/-- **M4 (3)**: the realizer's value is at most that of any value-active solution `P`
(`supN P < sm 1`, value bound `A`): from `e^q·|pv Q| = sm 1 ≤ e^q·|pv P|`. -/
lemma realizer_value_le_oracle {n : ℕ} {ξ : ℝ} {q : ℝ} {Q P : Polynomial ℤ} {A : ℝ}
    (hdeg : P.natDegree ≤ n) (hP : P ≠ 0) (hlt : supN P < sm n ξ q 1)
    (hvalA : |pv ξ P| ≤ A)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|) :
    |pv ξ Q| ≤ A := by
  have hvalQ : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
  have hPact := value_active_of_supN_lt_sm1 (P := P) hdeg hP hlt
  have hcomp : Real.exp q * |pv ξ Q| ≤ Real.exp q * |pv ξ P| := by
    calc
      Real.exp q * |pv ξ Q| = sm n ξ q 1 := hvalQ
      _ ≤ Real.exp q * |pv ξ P| := hPact.1
  have hleabs : |pv ξ Q| ≤ |pv ξ P| := by
    exact le_of_mul_le_mul_left hcomp (Real.exp_pos q)
  exact le_trans hleabs hvalA

/-- **M4**: the slope-realizer bound.  If the hA-oracle holds for `wbar` and `Q` is a
value-active first-realizer at `q` with `sm 1 / 2 ≥ H0`, then `|pv Q| ≤ (sm 1 / 2)^(-wbar)`. -/
theorem m4_slope_realizer {n : ℕ} {ξ : ℝ} {q : ℝ} {wbar : ℝ} {H0 : ℝ} (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ n) (hQ : Q ≠ 0)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hA : WbarOracle n ξ wbar H0)
    (hbig : H0 ≤ sm n ξ q 1 / 2) :
    |pv ξ Q| ≤ (sm n ξ q 1 / 2) ^ (-wbar) := by
  rcases hA_solution_lt_sm1 (n := n) (ξ := ξ) (q := q) (wbar := wbar) (H0 := H0) hA hbig
    with ⟨P, hPnz, hdegP, hsupP, hvalP⟩
  exact realizer_value_le_oracle (Q := Q) (P := P) (A := (sm n ξ q 1 / 2) ^ (-wbar))
    hdegP hPnz hsupP hvalP hreal hslope




open Polynomial
open scoped BigOperators

/-! ## Sec6 (M5, IN PROGRESS): the q-choice and the "‖P‖ → ∞" limit facts

For M5 we pick a level `q` at which `sm 1(q) = e^{-n}·supN P` (the maximal such level in the
paper).  This file records analytic support facts: `sm1_unbounded` (`sm 1(q)` exceeds any
level for some `q`, for transcendental ξ), the threshold consequence
`H0 ≤ sm 1(q)/2` once `‖P‖` is large, and the decay of the M4-bound as `‖P‖ → ∞`
(`(sm 1(q)/2)^{-wbar} ≤ ε` once `sm 1(q)/2` is large). -/

/-- The first minimum is unbounded: for transcendental ξ, every level `B0` is exceeded by
`sm 1(q)` for a suitable `q`. -/
lemma sm1_unbounded {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) (B0 : ℝ) :
    ∃ q : ℝ, B0 < sm n ξ q 1 := by
  classical
  let B : ℝ := max 1 (B0 + 1)
  have hB0pos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (B0 + 1))
  have hB0leB : B0 + 1 ≤ B := by
    dsimp [B]
    exact le_max_right 1 (B0 + 1)
  rcases pv_lower_uniform (n := n) (ξ := ξ) hξ B with ⟨m, hm0, hmall⟩
  by_contra hno
  push_neg at hno
  let q0 : ℝ := Real.log (2 * B / m)
  have hpos_arg : 0 < 2 * B / m := div_pos (mul_pos (by norm_num) hB0pos) hm0
  have hq0 : Real.exp q0 = 2 * B / m := Real.exp_log hpos_arg
  have hsmle : sm n ξ q0 1 ≤ B0 := hno q0
  have hlt : sm n ξ q0 1 < sm n ξ q0 1 + 1 := lt_add_of_pos_right _ zero_lt_one
  have h1le : (1 : ℕ) ≤ n + 1 := by omega
  rcases exists_linearIndependent_of_sm_lt (n := n) (ξ := ξ) (q := q0) (j := 1) h1le hlt
    with ⟨S, hS, hSli⟩
  let P : Polynomial ℤ := S ⟨0, by omega⟩
  have hPnz : P ≠ 0 := (hS ⟨0, by omega⟩).1
  have hdeg : P.natDegree ≤ n := (hS ⟨0, by omega⟩).2.1
  have hTq : Tq ξ q0 P ≤ sm n ξ q0 1 + 1 := (hS ⟨0, by omega⟩).2.2
  have hTqB : Tq ξ q0 P ≤ B0 + 1 := le_trans hTq (by linarith)
  have hsupB : supN P ≤ B := by
    calc
      supN P ≤ Tq ξ q0 P := supN_le_Tq ξ q0 P
      _ ≤ B0 + 1 := hTqB
      _ ≤ B := hB0leB
  have hmP : m ≤ |pv ξ P| := hmall P hPnz hdeg hsupB
  have hval_le : |pv ξ P| ≤ Real.exp (-q0) * (B0 + 1) := by
    have ht := Tq_exp_le ξ q0 P
    have h1 : Real.exp q0 * |pv ξ P| ≤ B0 + 1 := le_trans ht hTqB
    calc
      |pv ξ P| = Real.exp (-q0) * (Real.exp q0 * |pv ξ P|) := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ ≤ Real.exp (-q0) * (B0 + 1) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-q0)).le
  have hinv : Real.exp (-q0) = m / (2 * B) := by
    rw [Real.exp_neg, hq0]
    field_simp [Real.exp_ne_zero, hm0.ne', ne_of_gt hB0pos]
  have hsmall : Real.exp (-q0) * (B0 + 1) < m := by
    calc
      Real.exp (-q0) * (B0 + 1) ≤ Real.exp (-q0) * B := by
        exact mul_le_mul_of_nonneg_left hB0leB (Real.exp_pos (-q0)).le
      _ = (m / (2 * B)) * B := by rw [hinv]
      _ = m / 2 := by
        field_simp [ne_of_gt hB0pos]
      _ < m := by linarith [hm0]
  have hbad : m ≤ Real.exp (-q0) * (B0 + 1) := le_trans hmP hval_le
  linarith

/-- q-choice "eventually as ‖P‖ → ∞" half: if `sm 1(q) = e^{-n}·supN P`, then the M4
threshold `H0 ≤ sm 1(q)/2` holds once `‖P‖ ≥ 2·e^n·H0`. -/
lemma sm1_choice_threshold {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ} (H0 : ℝ)
    (hq : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hbig : 2 * Real.exp (n : ℝ) * H0 ≤ supN P) :
    H0 ≤ sm n ξ q 1 / 2 := by
  have he_n : 0 < Real.exp (n : ℝ) := Real.exp_pos (n : ℝ)
  have hle : H0 ≤ supN P / (2 * Real.exp (n : ℝ)) := by
    exact (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) he_n)).mpr (by
      calc
        H0 * (2 * Real.exp (n : ℝ)) = 2 * Real.exp (n : ℝ) * H0 := by ring
        _ ≤ supN P := hbig)
  calc
    H0 ≤ supN P / (2 * Real.exp (n : ℝ)) := hle
    _ = sm n ξ q 1 / 2 := by
      rw [hq]
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- Decay of the M4-bound: `A^{-wbar} ≤ ε` once `ε^{-1/wbar} ≤ A` (`wbar > 0`, `ε > 0`,
`A > 0`).  All exponents are `Real.rpow`. -/
lemma rpow_neg_decay {wbar : ℝ} (hwbar : 0 < wbar) {ε A : ℝ} (hε : 0 < ε)
    (hA0 : 0 < A) (hAbig : ε ^ (-1 / wbar) ≤ A) :
    A ^ (-wbar) ≤ ε := by
  let B : ℝ := ε ^ (-1 / wbar)
  have hB0 : 0 < B := Real.rpow_pos_of_pos hε _
  have hBleA : B ≤ A := hAbig
  have hpowA : B ^ wbar ≤ A ^ wbar := Real.rpow_le_rpow hB0.le hBleA hwbar.le
  have hAneg : A ^ (-wbar) = (A ^ wbar)⁻¹ := Real.rpow_neg (le_of_lt hA0) wbar
  have hBneg : B ^ (-wbar) = (B ^ wbar)⁻¹ := Real.rpow_neg (le_of_lt hB0) wbar
  have hcomp : (A ^ wbar)⁻¹ ≤ (B ^ wbar)⁻¹ := by
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hA0 wbar) (Real.rpow_pos_of_pos hB0 wbar)).mpr hpowA
  have hBval : B ^ (-wbar) = ε := by
    have hmul1 : (-1 / wbar) * (-wbar) = (1 : ℝ) := by
      field_simp [ne_of_gt hwbar]
    calc
      B ^ (-wbar) = ε ^ ((-1 / wbar) * (-wbar)) := by
        dsimp [B]
        rw [← Real.rpow_mul hε.le]
      _ = ε ^ (1 : ℝ) := by rw [hmul1]
      _ = ε := Real.rpow_one ε
  calc
    A ^ (-wbar) ≤ B ^ (-wbar) := by
      rw [hAneg, hBneg]
      exact hcomp
    _ = ε := hBval




open Polynomial Filter Metric
open scoped BigOperators Topology

/-! ## Sec7 (M5 support, IN PROGRESS): continuity of q ↦ sm 1(q)

The first successive minimum as a function of `q` is continuous.  Strategy at a point
`q0`:
* pick a realizer level polynomial `P0` (`Tq(q0,P0) ≤ sm1(q0)+1`);
* on a neighbourhood of `q0`, `sm1(q)` stays `≤ sm1(q0)+2`, so every near-minimizer has
  `supN ≤ sm1(q0)+4`; hence `sm1(q) = min` over the *fixed finite* set
  `F = {P ≠ 0, deg ≤ n, supN ≤ sm1(q0)+4}` of the continuous functions `q ↦ Tq(q,P)`;
* a min of finitely many continuous functions is continuous. -/

/-- `Tq` is continuous in the level `q`. -/
lemma continuous_Tq_q (ξ : ℝ) (P : Polynomial ℤ) :
    Continuous (fun q : ℝ => Tq ξ q P) := by
  dsimp [Tq]
  refine Continuous.max continuous_const ?_
  have h := (Real.continuous_exp.mul continuous_const : Continuous (fun q : ℝ => Real.exp q * |pv ξ P|))
  exact h

/-- Approximating the first minimum from above: if `R > sm 1(q)` there is a nonzero
degree-≤-n polynomial with `Tq < R`. -/
lemma exists_Tq_lt {n : ℕ} {ξ : ℝ} {q : ℝ} {R : ℝ} (hR : sm n ξ q 1 < R) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ Tq ξ q P < R := by
  classical
  let S : Set ℝ := {t | 0 ≤ t ∧ ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧ Tq ξ q P ≤ t}
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro t ⟨ht0, _⟩
    exact ht0
  have hSne : S.Nonempty := by
    refine ⟨Tq ξ q (1 : Polynomial ℤ), ?_⟩
    constructor
    · exact Tq_nonneg ξ q (1 : Polynomial ℤ)
    · refine ⟨(1 : Polynomial ℤ), ?_, ?_, le_rfl⟩
      · norm_num
      · simp
  have hsm : sm n ξ q 1 = sInf S := sm1_eq_infi_Tq (n := n) (ξ := ξ) (q := q)
  have hslt : sInf S < R := by
    rwa [hsm] at hR
  rcases (csInf_lt_iff hbdd hSne).mp hslt with ⟨t, htS, htR⟩
  rcases htS with ⟨ht0, P, hPnz, hdeg, hTq⟩
  exact ⟨P, hPnz, hdeg, lt_of_le_of_lt hTq htR⟩


/-- A polynomial realizing the first minimum up to `+1` at level `q0`. -/
lemma sm1_realizer_add_one {n : ℕ} {ξ : ℝ} {q0 : ℝ} :
    ∃ P0 : Polynomial ℤ, P0 ≠ 0 ∧ P0.natDegree ≤ n ∧ Tq ξ q0 P0 ≤ sm n ξ q0 1 + 1 := by
  have hlt : sm n ξ q0 1 < sm n ξ q0 1 + 1 := lt_add_of_pos_right _ zero_lt_one
  rcases exists_linearIndependent_of_sm_lt (n := n) (ξ := ξ) (q := q0) (j := 1)
    (by omega : (1 : ℕ) ≤ n + 1) hlt with ⟨S, hS, hSli⟩
  let P0 : Polynomial ℤ := S ⟨0, by omega⟩
  refine ⟨P0, ?_⟩
  exact (hS ⟨0, by omega⟩)

/-- Level-set of the first minimum: on the neighbourhood `U` (so that
`Tq(q,P0) < sm 1(q0)+2`) the value `sm 1(q)` is the minimum over the fixed finite family
`{P ≠ 0, deg ≤ n, supN ≤ sm 1(q0)+3}` of the continuous functions `Tq(·,P)`. -/
lemma sm1_eq_sInf_finite {n : ℕ} {ξ : ℝ} {q0 q : ℝ} {P0 : Polynomial ℤ}
    (hP0 : P0 ≠ 0) (hdegP0 : P0.natDegree ≤ n)
    (hP0Tq : Tq ξ q0 P0 ≤ sm n ξ q0 1 + 1)
    (hU : Tq ξ q P0 < sm n ξ q0 1 + 2) :
    sm n ξ q 1 =
      sInf ((fun P : Polynomial ℤ => Tq ξ q P) ''
        {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧ supN P ≤ sm n ξ q0 1 + 3}) := by
  classical
  let F : Set (Polynomial ℤ) := {P | P ≠ 0 ∧ P.natDegree ≤ n ∧ supN P ≤ sm n ξ q0 1 + 3}
  have hFin : F.Finite := by
    have hset : F ⊆ {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
        (P.map (Int.castRingHom ℝ)).supNorm ≤ sm n ξ q0 1 + 3} := by
      intro P hP
      exact ⟨hP.1, hP.2.1, by simpa [supN] using hP.2.2⟩
    exact (finite_int_polys_bounded_supNorm n (sm n ξ q0 1 + 3)).subset hset
  have hP0F : P0 ∈ F := by
    have hsup : supN P0 ≤ sm n ξ q0 1 + 3 := by
      calc
        supN P0 ≤ Tq ξ q0 P0 := supN_le_Tq ξ q0 P0
        _ ≤ sm n ξ q0 1 + 1 := hP0Tq
        _ ≤ sm n ξ q0 1 + 3 := by linarith
    exact ⟨hP0, hdegP0, hsup⟩
  have hsmU : sm n ξ q 1 < sm n ξ q0 1 + 2 := by
    have hle : sm n ξ q 1 ≤ Tq ξ q P0 := sm1_le_Tq (n := n) (ξ := ξ) (q := q) hP0 hdegP0
    exact lt_of_le_of_lt hle hU
  let I : Set ℝ := (fun P : Polynomial ℤ => Tq ξ q P) '' F
  have hbddI : BddBelow I := ⟨0, by rintro t ⟨P, hP, rfl⟩; exact Tq_nonneg ξ q P⟩
  have hneI : I.Nonempty := ⟨Tq ξ q P0, ⟨P0, hP0F, rfl⟩⟩
  have hle1 : sm n ξ q 1 ≤ sInf I := by
    refine le_csInf hneI ?_
    rintro t ⟨P, hPF, rfl⟩
    exact sm1_le_Tq (n := n) (ξ := ξ) (q := q) hPF.1 hPF.2.1
  have hle2 : sInf I ≤ sm n ξ q 1 := by
    by_contra hnot
    have hlt : sm n ξ q 1 < sInf I := lt_of_not_ge hnot
    let eps : ℝ := min ((sInf I - sm n ξ q 1) / 2) (1 / 2)
    have heps0 : 0 < eps := by
      have hd : 0 < sInf I - sm n ξ q 1 := sub_pos.mpr hlt
      dsimp [eps]
      exact lt_min (by linarith) (by norm_num)
    have heps1 : eps < 1 := by
      dsimp [eps]
      have h : min ((sInf I - sm n ξ q 1) / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      linarith
    have hR : sm n ξ q 1 < sm n ξ q 1 + eps := by linarith
    rcases exists_Tq_lt (n := n) (ξ := ξ) (q := q) hR with ⟨P, hPnz, hdeg, hTq⟩
    have hPF : P ∈ F := by
      have hsup : supN P ≤ sm n ξ q0 1 + 3 := by
        have h1 : supN P ≤ Tq ξ q P := supN_le_Tq ξ q P
        have h2 : Tq ξ q P < sm n ξ q 1 + eps := hTq
        have h3 : sm n ξ q 1 + eps < sm n ξ q0 1 + 3 := by linarith
        exact le_of_lt (lt_of_le_of_lt h1 (lt_trans h2 h3))
      exact ⟨hPnz, hdeg, hsup⟩
    have hinf : sInf I ≤ Tq ξ q P := csInf_le hbddI ⟨P, hPF, rfl⟩
    have hsmall : Tq ξ q P < sInf I := by
      calc
        Tq ξ q P < sm n ξ q 1 + eps := hTq
        _ ≤ sm n ξ q 1 + (sInf I - sm n ξ q 1) / 2 := by
          have hle : eps ≤ (sInf I - sm n ξ q 1) / 2 := by
            dsimp [eps]
            exact min_le_left _ _
          linarith
        _ < sInf I := by linarith
    exact (not_le_of_gt hsmall) hinf
  have heq : sInf I = sm n ξ q 1 := le_antisymm hle2 hle1
  -- target = sInf of image over F (definitional after unfolding F)
  change sm n ξ q 1 =
      sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' F)
  exact heq.symm

/-- sInf over the set-image of a finite set equals the Finset-minimum. -/
lemma sInf_image_finset_min' {ι : Type*} [DecidableEq ι] (A : Finset ι) (hA : A.Nonempty)
    (f : ι → ℝ) : sInf (f '' (A : Set ι)) =
      (A.image f).min' (Finset.image_nonempty.mpr hA) := by
  classical
  have himg : f '' (A : Set ι) = ((A.image f) : Set ℝ) := by
    ext y
    simp
  rw [himg]
  exact Finset.Nonempty.csInf_eq_min' (s := A.image f) (Finset.image_nonempty.mpr hA)

/-- The first successive minimum is continuous as a function of the level `q`. -/
theorem sm1_continuous {n : ℕ} {ξ : ℝ} : Continuous (fun q : ℝ => sm n ξ q 1) := by
  rw [continuous_iff_continuousAt]
  intro q0
  rcases sm1_realizer_add_one (n := n) (ξ := ξ) (q0 := q0) with ⟨P0, hP0, hdegP0, hP0Tq⟩
  let U : Set ℝ := {q : ℝ | Tq ξ q P0 < sm n ξ q0 1 + 2}
  have hUopen : IsOpen U := by
    dsimp [U]
    change IsOpen ((fun q : ℝ => Tq ξ q P0) ⁻¹' Set.Iio (sm n ξ q0 1 + 2))
    exact IsOpen.preimage (continuous_Tq_q ξ P0) isOpen_Iio
  have hmemU : q0 ∈ U := by
    dsimp [U]
    linarith
  have hUmem : U ∈ 𝓝 q0 := hUopen.mem_nhds hmemU
  let Fset : Set (Polynomial ℤ) := {P | P ≠ 0 ∧ P.natDegree ≤ n ∧ supN P ≤ sm n ξ q0 1 + 3}
  have hFin : Fset.Finite := by
    have hsub : Fset ⊆ {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
        (P.map (Int.castRingHom ℝ)).supNorm ≤ sm n ξ q0 1 + 3} := by
      intro P hP
      exact ⟨hP.1, hP.2.1, by simpa [supN] using hP.2.2⟩
    exact (finite_int_polys_bounded_supNorm n (sm n ξ q0 1 + 3)).subset hsub
  have hP0F : P0 ∈ Fset := by
    have hsup : supN P0 ≤ sm n ξ q0 1 + 3 := by
      calc
        supN P0 ≤ Tq ξ q0 P0 := supN_le_Tq ξ q0 P0
        _ ≤ sm n ξ q0 1 + 1 := hP0Tq
        _ ≤ sm n ξ q0 1 + 3 := by linarith
    exact ⟨hP0, hdegP0, hsup⟩
  let Fs : Finset (Polynomial ℤ) := hFin.toFinset
  have hFsne : Fs.Nonempty := by
    refine ⟨P0, ?_⟩
    dsimp [Fs]
    rw [hFin.mem_toFinset]
    exact hP0F
  let g : ℝ → ℝ := fun q => (Fs.image (fun P : Polynomial ℤ => Tq ξ q P)).min'
    (Finset.image_nonempty.mpr hFsne)
  have hagree : (fun q : ℝ => sm n ξ q 1) =ᶠ[𝓝 q0] g := by
    refine Filter.mem_of_superset hUmem ?_
    intro q hq
    have hqU : Tq ξ q P0 < sm n ξ q0 1 + 2 := by
      dsimp [U] at hq
      exact hq
    have hsmfin := sm1_eq_sInf_finite (n := n) (ξ := ξ) (q0 := q0) (q := q) (P0 := P0)
      hP0 hdegP0 hP0Tq hqU
    change sm n ξ q 1 = sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset) at hsmfin
    have hbridge : sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset) = g q := by
      dsimp [g, Fs]
      have hsets : Fset = (↑(hFin.toFinset) : Set (Polynomial ℤ)) := hFin.coe_toFinset.symm
      have hb' := sInf_image_finset_min' (hFin.toFinset) hFsne (fun P : Polynomial ℤ => Tq ξ q P)
      calc
        sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset)
            = sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' (↑(hFin.toFinset) : Set (Polynomial ℤ))) := by
                exact congrArg (fun A : Set (Polynomial ℤ) =>
                  sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' A)) hsets
        _ = ((hFin.toFinset).image (fun P : Polynomial ℤ => Tq ξ q P)).min'
              (Finset.image_nonempty.mpr hFsne) := hb'
    -- goal: membership in {q | sm1(q) = g(q)}
    exact hsmfin.trans hbridge
  have hgcont : Continuous g := by
    dsimp [g]
    exact Commons.Analysis.ContinuousMin.finset_min_continuous (s := Fs) hFsne
      (f := fun P : Polynomial ℤ => fun q : ℝ => Tq ξ q P)
      (by intro P hP; exact continuous_Tq_q ξ P)
  exact hgcont.continuousAt.congr_of_eventuallyEq hagree




open Polynomial Set Metric Filter
open scoped BigOperators Topology

/-! ## Sec8 (M5, IN PROGRESS): the level-set equality

`sm 1` is continuous (`sm1_continuous`), monotone (`sm_mono_q`) and unbounded
(`sm1_unbounded`).  Hence for every level `c ≥ sm 1(0)` there is `q ≥ 0` with
`sm 1(q) = c` (intermediate value).  In M5 the level is `c = e^{-n}·supN P`, which is
`≥ sm 1(0)` once `‖P‖ ≥ e^n·sm 1(0)`. -/

/-- Every level `c ≥ sm 1(0)` is attained: `∃ q ≥ 0, sm 1(q) = c` (IVT). -/
lemma sm1_attains {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) (c : ℝ)
    (hc0 : sm n ξ 0 1 ≤ c) : ∃ q : ℝ, 0 ≤ q ∧ sm n ξ q 1 = c := by
  rcases sm1_unbounded (n := n) (ξ := ξ) hξ c with ⟨q0, hc_lt⟩
  let q1 : ℝ := max q0 0
  have hq1ge0 : 0 ≤ q1 := le_max_right q0 0
  have hq0_le_q1 : q0 ≤ q1 := le_max_left q0 0
  have hc_le1 : c ≤ sm n ξ q1 1 := by
    have hmono : sm n ξ q0 1 ≤ sm n ξ q1 1 :=
      sm_mono_q (n := n) (ξ := ξ) hq0_le_q1 (by omega : (1 : ℕ) ≤ n + 1)
    linarith
  let f : ℝ → ℝ := fun q => sm n ξ q 1
  have hfcont : Continuous f := sm1_continuous (n := n) (ξ := ξ)
  have hmem : c ∈ Set.Icc (f 0) (f q1) := by
    dsimp [f]
    exact ⟨hc0, hc_le1⟩
  have him := intermediate_value_Icc (a := 0) (b := q1) (f := f) hq1ge0 hfcont.continuousOn
  rcases him hmem with ⟨q, hqi, hq⟩
  exact ⟨q, hqi.1, hq⟩

/-- The M5 level: for `‖P‖ ≥ e^n·sm 1(0)` there is `q ≥ 0` with
`sm 1(q) = e^{-n}·supN P`. -/
lemma sm1_level_exists {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) {P : Polynomial ℤ}
    (hbig : Real.exp (n : ℝ) * sm n ξ 0 1 ≤ supN P) :
    ∃ q : ℝ, 0 ≤ q ∧ sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P := by
  have hc0 : sm n ξ 0 1 ≤ Real.exp (-(n : ℝ)) * supN P := by
    have hle : sm n ξ 0 1 ≤ supN P / Real.exp (n : ℝ) := by
      exact (le_div_iff₀ (Real.exp_pos (n : ℝ))).mpr (by simpa [mul_comm] using hbig)
    calc
      sm n ξ 0 1 ≤ supN P / Real.exp (n : ℝ) := hle
      _ = Real.exp (-(n : ℝ)) * supN P := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  exact sm1_attains (n := n) (ξ := ξ) hξ (Real.exp (-(n : ℝ)) * supN P) hc0


/-- **Exact realizer of the first minimum**: for every level `q` there is a nonzero integer
polynomial of degree ≤ n with `Tq(ξ,q,Q) = sm 1(q)` (the infimum is attained, as it is the
minimum over a fixed finite family). -/
lemma sm1_realizer {n : ℕ} {ξ : ℝ} {q : ℝ} :
    ∃ Q : Polynomial ℤ, Q ≠ 0 ∧ Q.natDegree ≤ n ∧ Tq ξ q Q = sm n ξ q 1 := by
  classical
  rcases sm1_realizer_add_one (n := n) (ξ := ξ) (q0 := q) with ⟨P0, hP0, hdegP0, hP0Tq⟩
  have hU : Tq ξ q P0 < sm n ξ q 1 + 2 := by linarith
  have hsm := sm1_eq_sInf_finite (n := n) (ξ := ξ) (q0 := q) (q := q) (P0 := P0)
    hP0 hdegP0 hP0Tq hU
  let Fset : Set (Polynomial ℤ) := {P | P ≠ 0 ∧ P.natDegree ≤ n ∧ supN P ≤ sm n ξ q 1 + 3}
  have hFin : Fset.Finite := by
    have hsub : Fset ⊆ {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
        (P.map (Int.castRingHom ℝ)).supNorm ≤ sm n ξ q 1 + 3} := by
      intro P hP
      exact ⟨hP.1, hP.2.1, by simpa [supN] using hP.2.2⟩
    exact (finite_int_polys_bounded_supNorm n (sm n ξ q 1 + 3)).subset hsub
  have hP0F : P0 ∈ Fset := by
    have hsup : supN P0 ≤ sm n ξ q 1 + 3 := by
      calc
        supN P0 ≤ Tq ξ q P0 := supN_le_Tq ξ q P0
        _ ≤ sm n ξ q 1 + 1 := hP0Tq
        _ ≤ sm n ξ q 1 + 3 := by linarith
    exact ⟨hP0, hdegP0, hsup⟩
  let Fs : Finset (Polynomial ℤ) := hFin.toFinset
  have hFsne : Fs.Nonempty := by
    refine ⟨P0, ?_⟩
    dsimp [Fs]
    rw [hFin.mem_toFinset]
    exact hP0F
  let t : Finset ℝ := Fs.image (fun P : Polynomial ℤ => Tq ξ q P)
  have htn : t.Nonempty := Finset.image_nonempty.mpr hFsne
  have hsmmin : sm n ξ q 1 = t.min' htn := by
    have hbridge : sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset) = t.min' htn := by
      dsimp [t]
      have hsets : Fset = (↑(hFin.toFinset) : Set (Polynomial ℤ)) := hFin.coe_toFinset.symm
      have hb' := sInf_image_finset_min' (hFin.toFinset) hFsne (fun P : Polynomial ℤ => Tq ξ q P)
      calc
        sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset)
            = sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' (↑(hFin.toFinset) : Set (Polynomial ℤ))) := by
                exact congrArg (fun A : Set (Polynomial ℤ) =>
                  sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' A)) hsets
        _ = ((hFin.toFinset).image (fun P : Polynomial ℤ => Tq ξ q P)).min'
              (Finset.image_nonempty.mpr hFsne) := hb'
    calc
      sm n ξ q 1 = sInf ((fun P : Polynomial ℤ => Tq ξ q P) '' Fset) := hsm
      _ = t.min' htn := hbridge
  have hmems : t.min' htn ∈ t := Finset.min'_mem t htn
  rcases (Finset.mem_image.mp hmems) with ⟨Q, hQF, hQt⟩
  have hQFs : Q ∈ Fs := hQF
  have hQFset : Q ∈ Fset := by
    dsimp [Fs] at hQFs
    exact hFin.mem_toFinset.mp hQFs
  have hQeq : Tq ξ q Q = sm n ξ q 1 := by
    rw [hQt]
    exact hsmmin.symm
  exact ⟨Q, hQFset.1, hQFset.2.1, hQeq⟩


/-- **Slope to the right of a maximal level**: if `q` is maximal among the levels where
`sm 1 = c`, then any realizer `Q` of `sm 1(q)` is value-active at `q`
(`supN Q ≤ e^q·|pv Q|`): otherwise `L(Q,·)` stays flat at `c` for small increments,
forcing `sm 1(q+δ) = c` against maximality. -/
lemma sm1_realizer_slope_right {n : ℕ} {ξ : ℝ} {q : ℝ} (c : ℝ) (Q : Polynomial ℤ)
    (hQnz : Q ≠ 0) (hdeg : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1) (hc : sm n ξ q 1 = c)
    (hmax : ∀ q' : ℝ, q < q' → sm n ξ q' 1 ≠ c) :
    supN Q ≤ Real.exp q * |pv ξ Q| := by
  classical
  by_contra hnot
  have hstrict : Real.exp q * |pv ξ Q| < supN Q := lt_of_not_ge hnot
  -- the value term stays below the norm for a small increment δ > 0
  have hgcont : Continuous (fun t : ℝ => Real.exp t * |pv ξ Q|) :=
    (Real.continuous_exp.mul continuous_const : Continuous (fun t : ℝ => Real.exp t * |pv ξ Q|))
  have hO : IsOpen {t : ℝ | Real.exp t * |pv ξ Q| < supN Q} := by
    exact IsOpen.preimage hgcont isOpen_Iio
  have hmemO : q ∈ {t : ℝ | Real.exp t * |pv ξ Q| < supN Q} := hstrict
  rcases Metric.mem_nhds_iff.mp (hO.mem_nhds hmemO) with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hqδmem : q + δ ∈ {t : ℝ | Real.exp t * |pv ξ Q| < supN Q} := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
    have hδ : |q + δ - q| = δ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ q + δ - q)]
      ring
    rw [hδ]
    dsimp [δ]
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  have hle : Real.exp (q + δ) * |pv ξ Q| ≤ supN Q := le_of_lt hqδmem
  have hnormQ : Tq ξ q Q = supN Q := by
    rw [Tq]
    exact max_eq_left (le_of_lt hstrict)
  have hflat : Tq ξ (q + δ) Q = supN Q := by
    rw [Tq]
    exact max_eq_left hle
  have hsm_le : sm n ξ (q + δ) 1 ≤ c := by
    calc
      sm n ξ (q + δ) 1 ≤ Tq ξ (q + δ) Q := sm1_le_Tq (n := n) (ξ := ξ) (q := q + δ) hQnz hdeg
      _ = supN Q := hflat
      _ = c := by
        rw [← hnormQ, hreal, hc]
  have hmono : c ≤ sm n ξ (q + δ) 1 := by
    have hqle : q ≤ q + δ := by linarith
    have hm := sm_mono_q (n := n) (ξ := ξ) hqle (by omega : (1 : ℕ) ≤ n + 1)
    -- hm : sm1(q) ≤ sm1(q+δ)
    rwa [hc] at hm
  have hEq : sm n ξ (q + δ) 1 = c := le_antisymm hsm_le hmono
  have hqδ : q < q + δ := by linarith
  exact (hmax (q + δ) hqδ) hEq


/-- **Maximal level with `sm 1 = c`**: for every `c ≥ sm 1(0)`, the set of levels where
`sm 1(q) = c` has a greatest element `q ≥ 0` (nonempty bounded interval; its supremum is
attained by continuity). -/
lemma sm1_maximal_level {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) (c : ℝ)
    (hc0 : sm n ξ 0 1 ≤ c) :
    ∃ q : ℝ, 0 ≤ q ∧ sm n ξ q 1 = c ∧ ∀ q' : ℝ, q < q' → sm n ξ q' 1 ≠ c := by
  classical
  let A : Set ℝ := {q : ℝ | 0 ≤ q ∧ sm n ξ q 1 = c}
  have hAn : A.Nonempty := by
    rcases sm1_attains (n := n) (ξ := ξ) hξ c hc0 with ⟨q, hq0, hq⟩
    exact ⟨q, hq0, hq⟩
  have hAbdd : BddAbove A := by
    rcases sm1_unbounded (n := n) (ξ := ξ) hξ c with ⟨q1, hq1⟩
    refine ⟨q1, ?_⟩
    intro a ha
    by_contra hlt
    have hq1a : q1 < a := lt_of_not_ge hlt
    have hm := sm_mono_q (n := n) (ξ := ξ) (le_of_lt hq1a) (by omega : (1 : ℕ) ≤ n + 1)
    have h_le : sm n ξ q1 1 ≤ c := by
      rwa [ha.2] at hm
    exact (not_lt_of_ge h_le) hq1
  let qstar : ℝ := sSup A
  have hqstar0 : 0 ≤ qstar := by
    rcases hAn with ⟨a0, ha0A⟩
    exact le_trans ha0A.1 (le_csSup hAbdd ha0A)
  have hleft : ∀ q : ℝ, 0 ≤ q → q < qstar → sm n ξ q 1 ≤ c := by
    intro q hq0 hql
    rcases (lt_csSup_iff hAbdd hAn).mp hql with ⟨a, haA, hqa⟩
    have hmon := sm_mono_q (n := n) (ξ := ξ) (le_of_lt hqa) (by omega : (1 : ℕ) ≤ n + 1)
    rwa [haA.2] at hmon
  have hge : c ≤ sm n ξ qstar 1 := by
    rcases hAn with ⟨a0, ha0A⟩
    have hmon := sm_mono_q (n := n) (ξ := ξ) (le_csSup hAbdd ha0A) (by omega : (1 : ℕ) ≤ n + 1)
    rwa [ha0A.2] at hmon
  have hsmval : sm n ξ qstar 1 = c := by
    by_cases hz : qstar = 0
    · rcases hAn with ⟨a0, ha0A⟩
      have ha0le : a0 ≤ 0 := by rw [← hz]; exact le_csSup hAbdd ha0A
      have ha00 : a0 = 0 := le_antisymm ha0le ha0A.1
      have hc0' : sm n ξ 0 1 = c := by simpa [ha00] using ha0A.2
      simpa [hz] using hc0'
    · have hpos : 0 < qstar := lt_of_le_of_ne hqstar0 (Ne.symm hz)
      apply le_antisymm
      · by_contra hnot
        have hgt : c < sm n ξ qstar 1 := lt_of_not_ge hnot
        have hO : IsOpen {t : ℝ | c < sm n ξ t 1} := by
          exact IsOpen.preimage (sm1_continuous (n := n) (ξ := ξ)) isOpen_Ioi
        have hmemO : qstar ∈ {t : ℝ | c < sm n ξ t 1} := hgt
        rcases Metric.mem_nhds_iff.mp (hO.mem_nhds hmemO) with ⟨δ, hδ, hball⟩
        let eps : ℝ := min δ qstar
        have heps0 : 0 < eps := by
          dsimp [eps]
          exact lt_min hδ hpos
        let q : ℝ := qstar - eps / 2
        have hq0 : 0 ≤ q := by
          dsimp [q, eps]
          have hqle : qstar - min δ qstar / 2 ≥ 0 := by
            have hmin : min δ qstar ≤ qstar := min_le_right δ qstar
            nlinarith
          exact hqle
        have hql : q < qstar := by
          dsimp [q, eps]
          have hmin : min δ qstar ≤ qstar := min_le_right δ qstar
          nlinarith [heps0]
        have hmem : q ∈ Metric.ball qstar δ := by
          rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
          have hd : |q - qstar| = eps / 2 := by
            dsimp [q]
            have h1 : |(qstar - eps / 2) - qstar| = |-(eps / 2)| := by congr 1; ring
            rw [h1, abs_neg]
            rw [abs_of_nonneg (by dsimp [eps]; positivity : 0 ≤ eps / 2)]
          rw [hd]
          have hminle : eps ≤ δ := by dsimp [eps]; exact min_le_left δ qstar
          have hlt2 : eps / 2 < δ := by
            have hh : eps ≤ δ := hminle
            nlinarith
          exact hlt2
        have hqO : c < sm n ξ q 1 := hball hmem
        have hqle_c : sm n ξ q 1 ≤ c := hleft q hq0 hql
        linarith
      · exact hge
  have hmax : ∀ q' : ℝ, qstar < q' → sm n ξ q' 1 ≠ c := by
    intro q' hqq' hq'
    have hq'0 : 0 ≤ q' := le_trans hqstar0 (le_of_lt hqq')
    have hq'A : q' ∈ A := ⟨hq'0, hq'⟩
    have hq'le : q' ≤ qstar := le_csSup hAbdd hq'A
    linarith
  exact ⟨qstar, hqstar0, hsmval, hmax⟩

/-- The M5 choice: a maximal level with `sm 1(q) = e^{-n}·‖P‖` for large `‖P‖`. -/
lemma sm1_maximal_level_P {n : ℕ} {ξ : ℝ} (hξ : Transcendental ℚ ξ) {P : Polynomial ℤ}
    (hbig : Real.exp (n : ℝ) * sm n ξ 0 1 ≤ supN P) :
    ∃ q : ℝ, 0 ≤ q ∧ sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P ∧
      ∀ q' : ℝ, q < q' → sm n ξ q' 1 ≠ Real.exp (-(n : ℝ)) * supN P := by
  have hc0 : sm n ξ 0 1 ≤ Real.exp (-(n : ℝ)) * supN P := by
    have hle : sm n ξ 0 1 ≤ supN P / Real.exp (n : ℝ) := by
      exact (le_div_iff₀ (Real.exp_pos (n : ℝ))).mpr (by simpa [mul_comm] using hbig)
    calc
      sm n ξ 0 1 ≤ supN P / Real.exp (n : ℝ) := hle
      _ = Real.exp (-(n : ℝ)) * supN P := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  exact sm1_maximal_level (n := n) (ξ := ξ) hξ (Real.exp (-(n : ℝ)) * supN P) hc0




open Polynomial
open scoped BigOperators

/-! ## Sec9 (M5(a), IN PROGRESS): level/threshold glue for the assembly

Given `P` (irreducible, degree ≤ n, tiny value at ξ) of very large sup-norm, the M5
level is `cL := e^{-n}·supN P` and `q` is the *maximal* level with `sm 1(q) = cL`.
This file records the threshold consequences used by the assembly:
  • `q ≥ log 2` once `‖P‖ > e^n · sm 1(log 2)` (so the M2/M3 product bounds apply);
  • any realizer `Q` of `sm 1(q)` has `‖Q‖ ≤ e^{-n}·‖P‖`;
  • the M4 bound in terms of `‖P‖` and the hA threshold. -/

/-- If the level `sm 1(q) = e^{-n}·‖P‖` is above `sm 1(log 2)`, then `log 2 < q`
(successive minima are monotone in `q`). -/
lemma sm1_q_gt_log2_of_level_big {n : ℕ} {ξ : ℝ} {q : ℝ} {P : Polynomial ℤ}
    (hq : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hbig : Real.exp (n : ℝ) * sm n ξ (Real.log 2) 1 < supN P) :
    Real.log 2 < q := by
  by_contra hnot
  have hqle : q ≤ Real.log 2 := le_of_not_gt hnot
  have hmono : sm n ξ q 1 ≤ sm n ξ (Real.log 2) 1 := by
    exact sm_mono_q (n := n) (ξ := ξ) hqle (by omega : (1 : ℕ) ≤ n + 1)
  have hle : Real.exp (-(n : ℝ)) * supN P ≤ sm n ξ (Real.log 2) 1 := by
    rwa [hq] at hmono
  have hsup : supN P ≤ Real.exp (n : ℝ) * sm n ξ (Real.log 2) 1 := by
    have hcancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
      rw [← Real.exp_add]
      norm_num
    calc
      supN P = Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * supN P) := by
        rw [← mul_assoc, hcancel]
        ring
      _ ≤ Real.exp (n : ℝ) * sm n ξ (Real.log 2) 1 := by
        exact mul_le_mul_of_nonneg_left hle (Real.exp_pos (n : ℝ)).le
  exact (not_lt_of_ge hsup) hbig

/-- A realizer `Q` of `sm 1(q)` has height at most `sm 1(q)`. -/
lemma realizer_supN_le_sm1 {n : ℕ} {ξ : ℝ} {q : ℝ} {Q : Polynomial ℤ}
    (hreal : Tq ξ q Q = sm n ξ q 1) : supN Q ≤ sm n ξ q 1 := by
  calc
    supN Q ≤ Tq ξ q Q := supN_le_Tq ξ q Q
    _ = sm n ξ q 1 := hreal

/-- At the M5 level `sm 1(q) = e^{-n}·‖P‖`, a realizer has `‖Q‖ ≤ e^{-n}·‖P‖`. -/
lemma realizer_norm_le_e_neg_n_supN {n : ℕ} {ξ : ℝ} {q : ℝ} {P Q : Polynomial ℤ}
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P) :
    supN Q ≤ Real.exp (-(n : ℝ)) * supN P := by
  calc
    supN Q ≤ sm n ξ q 1 := realizer_supN_le_sm1 (Q := Q) hreal
    _ = Real.exp (-(n : ℝ)) * supN P := hlevel

/-- At the M5 level, the M4 bound holds once `‖P‖ ≥ 2·e^n·H0`
(`|pv Q| ≤ (e^{-n}‖P‖/2)^{-wbar}` for the value-active realizer `Q`). -/
lemma m4_bound_of_level_big {n : ℕ} {ξ : ℝ} {q : ℝ} {wbar H0 : ℝ} (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ n) (hQ : Q ≠ 0)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hA : WbarOracle n ξ wbar H0)
    {P : Polynomial ℤ}
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hbig : 2 * Real.exp (n : ℝ) * H0 ≤ supN P) :
    |pv ξ Q| ≤ (Real.exp (-(n : ℝ)) * supN P / 2) ^ (-wbar) := by
  have hthr : H0 ≤ sm n ξ q 1 / 2 := by
    exact sm1_choice_threshold (n := n) (ξ := ξ) (q := q) (P := P) H0 hlevel hbig
  have hbound := m4_slope_realizer (n := n) (ξ := ξ) (q := q) (wbar := wbar) (H0 := H0) Q
    hdeg hQ hreal hslope hA hthr
  convert hbound using 1
  congr 1
  rw [hlevel]




open Polynomial
open scoped BigOperators

/-! ## Sec10 (M5(b), IN PROGRESS): the λ-corrections P̃ᵢ = Cᵢ + λᵢ·P

Given a base-family member `C` (value < |pv Q|, height ≥ e^{-n}·‖P‖) and the polynomial
`P` (with `‖P‖ ≤ e^n·‖C‖`), the corrected polynomial
`P̃ := C + (if ‖C‖ ≤ ‖P‖ then 3 else 0)·P` satisfies:
  • `‖P‖ < ‖P̃‖`  (so `P` can be placed second in the sorted final family),
  • `‖P̃‖ ≤ (1 + 3e^n)·‖C‖`  (so products over the `P̃`'s are controlled by products
    over the `C`'s — the engine of the |pv Q|·‖P‖^x ≤ B bound),
  • `|pv P̃| ≤ |pv C| + 3|pv P|` (so values are controlled by max(|pv Q|, |pv P|)). -/

/-- The correction `P̃ = C + λ·P` with `λ = 3` when `‖C‖ ≤ ‖P‖` and `λ = 0` otherwise. -/
noncomputable def tailCorr (P : Polynomial ℤ) (C : Polynomial ℤ) : Polynomial ℤ :=
  C + Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P

/-- `|pv P̃| ≤ |pv C| + 3·|pv P|`. -/
lemma tailCorr_value_le {ξ : ℝ} (P C : Polynomial ℤ) :
    |pv ξ (tailCorr P C)| ≤ |pv ξ C| + 3 * |pv ξ P| := by
  classical
  have hk : ‖(((if supN C ≤ supN P then (3 : ℤ) else 0) : ℤ) : ℝ)‖ ≤ 3 := by
    by_cases h : supN C ≤ supN P
    · simp [h]
    · simp [h]
  have hmul : |pv ξ (Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P)| ≤
      3 * |pv ξ P| := by
    rw [pv_C_mul]
    calc
      |(((if supN C ≤ supN P then (3 : ℤ) else 0) : ℤ) : ℝ) * pv ξ P|
          = ‖(((if supN C ≤ supN P then (3 : ℤ) else 0) : ℤ) : ℝ)‖ * |pv ξ P| := by
            rw [abs_mul, Real.norm_eq_abs]
      _ ≤ 3 * |pv ξ P| := mul_le_mul_of_nonneg_right hk (abs_nonneg (pv ξ P))
  have htri := abs_add_le (pv ξ C)
    (pv ξ (Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P))
  dsimp [tailCorr]
  rw [pv_add]
  linarith

/-- `‖P‖ < ‖P̃‖` when `e^{-n}·‖P‖ ≤ ‖C‖` and `0 < ‖P‖`. -/
lemma tailCorr_supN_gt {n : ℕ} {P C : Polynomial ℤ}
    (hCge : Real.exp (-(n : ℝ)) * supN P ≤ supN C) (hPpos : 0 < supN P) :
    supN P < supN (tailCorr P C) := by
  classical
  by_cases hle : supN C ≤ supN P
  · have h3 : supN (Polynomial.C (3 : ℤ) * P) = 3 * supN P := by
      rw [supN_C_mul]
      norm_num
    have h := supN_ge_sub C (Polynomial.C (3 : ℤ) * P)
    -- h : supN(3P) − supN C ≤ supN (C + 3P)
    rw [h3] at h
    have htwo : 2 * supN P ≤ 3 * supN P - supN C := by linarith
    have hgoal : supN P < supN (C + Polynomial.C (3 : ℤ) * P) := by
      calc
        supN P < 2 * supN P := by nlinarith
        _ ≤ 3 * supN P - supN C := htwo
        _ ≤ supN (C + Polynomial.C (3 : ℤ) * P) := h
    have hC3 : supN (tailCorr P C) = supN (C + Polynomial.C (3 : ℤ) * P) := by
      dsimp [tailCorr]
      simp [hle]
    rwa [hC3]
  · have hgt : supN P < supN C := lt_of_not_ge hle
    have hC0 : supN (tailCorr P C) = supN C := by
      dsimp [tailCorr]
      simp [hle]
    rwa [hC0]

/-- `‖P̃‖ ≤ (1 + 3e^n)·‖C‖` when `e^{-n}·‖P‖ ≤ ‖C‖`. -/
lemma tailCorr_supN_le {n : ℕ} {P C : Polynomial ℤ}
    (hCge : Real.exp (-(n : ℝ)) * supN P ≤ supN C) :
    supN (tailCorr P C) ≤ (1 + 3 * Real.exp (n : ℝ)) * supN C := by
  classical
  have hPle : supN P ≤ Real.exp (n : ℝ) * supN C := by
    have hcancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
      rw [← Real.exp_add]
      norm_num
    calc
      supN P = Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * supN P) := by
        rw [← mul_assoc, hcancel]
        ring
      _ ≤ Real.exp (n : ℝ) * supN C :=
        mul_le_mul_of_nonneg_left hCge (Real.exp_pos (n : ℝ)).le
  have h3 : supN (Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P) ≤
      3 * supN P := by
    by_cases h : supN C ≤ supN P
    · have heq : supN (Polynomial.C (3 : ℤ) * P) = 3 * supN P := by
        rw [supN_C_mul]
        norm_num
      rw [if_pos h]
      exact le_of_eq heq
    · have heq0 : supN (Polynomial.C (0 : ℤ) * P) = 0 := by
        rw [supN_C_mul]
        norm_num
      rw [if_neg h]
      calc
        supN (Polynomial.C (0 : ℤ) * P) = 0 := heq0
        _ ≤ 3 * supN P := by exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (supN_nonneg P)
  have h1 : supN (tailCorr P C) ≤ supN C + 3 * supN P := by
    dsimp [tailCorr]
    exact le_trans (supN_add_le C (Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P))
      (by linarith)
  have hm := mul_le_mul_of_nonneg_left hPle (by norm_num : (0 : ℝ) ≤ 3)
  have h2 : supN C + 3 * supN P ≤ supN C + 3 * (Real.exp (n : ℝ) * supN C) := by
    nlinarith
  have hfin : supN C + 3 * (Real.exp (n : ℝ) * supN C) = (1 + 3 * Real.exp (n : ℝ)) * supN C := by
    ring
  exact le_trans (le_trans h1 h2) (le_of_eq hfin)

/-- Degree of the correction is at most `n` when both inputs are. -/
lemma tailCorr_natDegree_le {n : ℕ} {P C : Polynomial ℤ}
    (hdegC : C.natDegree ≤ n) (hdegP : P.natDegree ≤ n) :
    (tailCorr P C).natDegree ≤ n := by
  classical
  dsimp [tailCorr]
  exact le_trans (Polynomial.natDegree_add_le C
    (Polynomial.C (if supN C ≤ supN P then (3 : ℤ) else 0) * P))
    (by
      rw [max_le_iff]
      constructor
      · exact hdegC
      · exact le_trans (Polynomial.natDegree_C_mul_le
          (if supN C ≤ supN P then (3 : ℤ) else 0) P) hdegP)




open Polynomial
open scoped BigOperators

/-! ## Sec11 (M5(c), IN PROGRESS): the corrected family P̃ⱼ = tailCorr P (C(succ j))

Starting from the corrected base family `C` (`C 0 = Q`, values `|pv(C i)| < |pv Q|`,
heights `≤ 3·(sm_{i.val+1}+1)`, heights `≥ sm 1 = e^{-n}‖P‖`) built by Sec4, we form
`P̃ⱼ := tailCorr P (C (Fin.succ j))` for `j : Fin n`.  Each `P̃ⱼ` has
  • degree ≤ n,  • `‖P‖ < ‖P̃ⱼ‖`,  • `‖P̃ⱼ‖ ≤ (1+3e^n)·3·(sm_{...}+1)`,
  • `|pv(P̃ⱼ)| < |pv Q| + 3|pv P|`. -/

/-- The level relation `sm 1(q) = e^{-n}·‖P‖` gives a lower bound on the corrected
tail heights: `e^{-n}·‖P‖ ≤ ‖C‖` for any member `C` with value `< |pv Q|`. -/
lemma tail_norm_ge_level {n : ℕ} {ξ : ℝ} {q : ℝ} {Q C : Polynomial ℤ} {P : Polynomial ℤ}
    (hval : Real.exp q * |pv ξ Q| = sm n ξ q 1)
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hdegC : C.natDegree ≤ n) (hC : C ≠ 0) (hlt : |pv ξ C| < |pv ξ Q|) :
    Real.exp (-(n : ℝ)) * supN P ≤ supN C := by
  have hcorr := corr_active (n := n) (ξ := ξ) (q := q) (Q := Q) (C := C) hdegC hC hval hlt
  -- hcorr : sm 1 ≤ supN C ∧ Tq(C) = supN C
  calc
    Real.exp (-(n : ℝ)) * supN P = sm n ξ q 1 := hlevel.symm
    _ ≤ supN C := hcorr.1

/-- The corrected family of tails: `Ptilde_j := tailCorr P (C (Fin.succ j))`. -/
theorem m5_corrected_tails {n : ℕ} (ξ : ℝ) (q : ℝ) (Q P : Polynomial ℤ)
    (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hP : P ≠ 0) (hdegP : P.natDegree ≤ n)
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P) :
    ∃ Ct : Fin n → Polynomial ℤ,
      (∀ j : Fin n,
        (Ct j).natDegree ≤ n ∧
        supN P < supN (Ct j) ∧
        supN (Ct j) ≤ (1 + 3 * Real.exp (n : ℝ)) *
          (3 * (sm n ξ q ((Fin.succ j).val + 1) + 1)) ∧
        |pv ξ (Ct j)| < |pv ξ Q| + 3 * |pv ξ P|) := by
  classical
  have hval : Real.exp q * |pv ξ Q| = sm n ξ q 1 :=
    value_active_eq (Q := Q) hslope hreal
  rcases corrected_family (n := n) (ξ := ξ) (q := q) Q hQ hdegQ hreal hslope
    with ⟨C, hC0, hCb, hCli⟩
  refine ⟨fun j => tailCorr P (C (Fin.succ j)), ?_⟩
  intro j
  change (tailCorr P (C (Fin.succ j))).natDegree ≤ n ∧
    supN P < supN (tailCorr P (C (Fin.succ j))) ∧
    supN (tailCorr P (C (Fin.succ j))) ≤
      (1 + 3 * Real.exp (n : ℝ)) * (3 * (sm n ξ q ((Fin.succ j).val + 1) + 1)) ∧
    |pv ξ (tailCorr P (C (Fin.succ j)))| < |pv ξ Q| + 3 * |pv ξ P|
  have hsne : Fin.succ j ≠ 0 := Fin.succ_ne_zero j
  have hCnb := hCb (Fin.succ j) hsne
  have hdegC : (C (Fin.succ j)).natDegree ≤ n := hCnb.1
  have hvalC : |pv ξ (C (Fin.succ j))| < |pv ξ Q| := hCnb.2.1
  have hsupC : supN (C (Fin.succ j)) ≤ 3 * (sm n ξ q ((Fin.succ j).val + 1) + 1) := hCnb.2.2
  have hCne : C (Fin.succ j) ≠ 0 := li_poly_ne_zero (C := C) hCli (Fin.succ j)
  have hge : Real.exp (-(n : ℝ)) * supN P ≤ supN (C (Fin.succ j)) :=
    tail_norm_ge_level (n := n) (ξ := ξ) (q := q) (Q := Q) (C := C (Fin.succ j)) (P := P)
      hval hlevel hdegC hCne hvalC
  have hPpos : 0 < supN P := supN_pos_of_ne_zero hP
  have hgt := tailCorr_supN_gt (n := n) (P := P) (C := C (Fin.succ j)) hge hPpos
  have hle := tailCorr_supN_le (n := n) (P := P) (C := C (Fin.succ j)) hge
  have hdeg := tailCorr_natDegree_le (n := n) (P := P) (C := C (Fin.succ j)) hdegC hdegP
  have hvalle := tailCorr_value_le (ξ := ξ) (P := P) (C := C (Fin.succ j))
  have hvallt : |pv ξ (tailCorr P (C (Fin.succ j)))| < |pv ξ Q| + 3 * |pv ξ P| := by
    have h3 : 0 ≤ 3 * |pv ξ P| := by positivity
    calc
      |pv ξ (tailCorr P (C (Fin.succ j)))| ≤ |pv ξ (C (Fin.succ j))| + 3 * |pv ξ P| := hvalle
      _ < |pv ξ Q| + 3 * |pv ξ P| := by linarith
  have hK : 0 ≤ 1 + 3 * Real.exp (n : ℝ) := by nlinarith [Real.exp_pos (n : ℝ)]
  have hle2 : supN (tailCorr P (C (Fin.succ j))) ≤
      (1 + 3 * Real.exp (n : ℝ)) * (3 * (sm n ξ q ((Fin.succ j).val + 1) + 1)) := by
    exact le_trans hle (mul_le_mul_of_nonneg_left hsupC hK)
  exact ⟨hdeg, hgt, hle2, hvallt⟩



open Polynomial
open scoped BigOperators

/-! ## Sec12 (M6 glue support, IN PROGRESS): real-rpow product bookkeeping

Lemmas relating the product identity `H^x = ∏ H_i` with the lower bound
`x ≥ n` when every factor is `≥ H > 1`, plus the recovery `H^(log x/log H) = x`. -/

/-- If every member of a `Fin n`-family is `≥ H ≥ 0` then `H^n ≤ ∏`. -/
lemma prod_le_prod_const_pow {n : ℕ} {H : ℝ} {hs : Fin n → ℝ} (hH0 : 0 ≤ H)
    (hhs : ∀ j : Fin n, H ≤ hs j) : H ^ n ≤ ∏ j : Fin n, hs j := by
  calc
    H ^ n = ∏ j : Fin n, H := (prod_const_pow H).symm
    _ ≤ ∏ j : Fin n, hs j := by
      exact Finset.prod_le_prod (s := Finset.univ)
        (f := fun _ : Fin n => H) (g := hs)
        (by intro i hi; exact hH0)
        (by intro i hi; exact hhs i)

/-- The product of `H` over `Icc 2 (n+1)` is `H^n` (the interval has `n` elements). -/
lemma prod_const_Icc_two_succ {n : ℕ} (H : ℝ) :
    (∏ i ∈ Finset.Icc 2 (n + 1), H) = H ^ n := by
  rw [Finset.prod_const]
  congr 1
  rw [Nat.card_Icc]
  omega

/-- `H^y = ∏ hs` over `Icc 2 (n+1)`, with every factor `≥ H > 1`, forces `(n : ℝ) ≤ y`. -/
lemma x_ge_n_of_rpow_prod_Icc {n : ℕ} {H : ℝ} (hH : 1 < H) {hs : ℕ → ℝ}
    (hhs : ∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → H ≤ hs i)
    {y : ℝ} (hy : (∏ i ∈ Finset.Icc 2 (n + 1), hs i) = H ^ y) :
    (n : ℝ) ≤ y := by
  have hH0 : 0 ≤ H := le_of_lt (lt_trans zero_lt_one hH)
  have hle : H ^ n ≤ ∏ i ∈ Finset.Icc 2 (n + 1), hs i := by
    calc
      H ^ n = ∏ i ∈ Finset.Icc 2 (n + 1), H := (prod_const_Icc_two_succ (n := n) H).symm
      _ ≤ ∏ i ∈ Finset.Icc 2 (n + 1), hs i := by
        exact Finset.prod_le_prod (s := Finset.Icc 2 (n + 1))
          (f := fun _ : ℕ => H) (g := hs)
          (by intro i hi; exact hH0)
          (by intro i hi; exact hhs i hi)
  have hle2 : (H : ℝ) ^ (n : ℝ) ≤ H ^ y := by
    calc
      (H : ℝ) ^ (n : ℝ) = H ^ n := by rw [Real.rpow_natCast]
      _ ≤ ∏ i ∈ Finset.Icc 2 (n + 1), hs i := hle
      _ = H ^ y := hy
  exact (Real.rpow_le_rpow_left_iff hH).mp hle2

/-- `H ^ (log x / log H) = x` for `1 < H` and `0 < x`. -/
lemma rpow_log_div_log {H x : ℝ} (hH : 1 < H) (hx : 0 < x) :
    H ^ (Real.log x / Real.log H) = x := by
  have hH0 : 0 < H := lt_trans zero_lt_one hH
  have hlogH : Real.log H ≠ 0 := ne_of_gt (Real.log_pos hH)
  calc
    H ^ (Real.log x / Real.log H) = Real.exp (Real.log H * (Real.log x / Real.log H)) := by
      rw [Real.rpow_def_of_pos hH0]
    _ = Real.exp (Real.log x) := by
      congr 1
      field_simp [hlogH]
    _ = x := Real.exp_log hx




open Polynomial
open scoped BigOperators

/-! ## Sec13 (M5(d), IN PROGRESS): Q',P' are ℝ-linearly independent as real maps

Given the realizer `Q` (‖Q‖ ≤ e^{-n}‖P‖ < ‖P‖) and the input irreducible `P` with
tiny value at ξ (so `P` is nonconstant, hence primitive, `content(P) = 1`), we show
that the real polynomial maps of `Q` and `P` are ℝ-linearly independent:
ℝ-proportionality would force `q·Q = p·P` for nonzero integers, and comparing
contents gives `|p| = |q|·|content(Q)| ≥ |q|`, while the norm identity
`|q|·‖Q‖ = |p|·‖P‖` then forces `‖Q‖ ≥ ‖P‖`, contradicting `‖Q‖ < ‖P‖`. -/

/-- `content (C k * P) = |k| * content P` over ℤ. -/
lemma content_C_mul (k : ℤ) (P : Polynomial ℤ) :
    (Polynomial.C k * P).content = |k| * P.content := by
  rw [Polynomial.content_mul, Polynomial.content_C]
  rw [Int.abs_eq_normalize k]

/-- absolute content of a `C k`-multiple. -/
lemma abs_content_C_mul (k : ℤ) (P : Polynomial ℤ) :
    |((Polynomial.C k * P).content)| = |k * P.content| := by
  calc
    |((Polynomial.C k * P).content)| = |(|k| : ℤ) * P.content| := by rw [content_C_mul]
    _ = |(|k| : ℤ)| * |P.content| := abs_mul (|k| : ℤ) P.content
    _ = |k| * |P.content| := by congr 1; exact abs_of_nonneg (abs_nonneg (k : ℤ))
    _ = |k * P.content| := (abs_mul (k : ℤ) P.content).symm

/-- If `q•Q = p•P` with `P` primitive, then `|p| = |q|·|content Q|`. -/
lemma abs_int_mul_of_scalar_eq {p q : ℤ} {Q P : Polynomial ℤ}
    (hprim : P.IsPrimitive) (h : ((q : ℤ) • Q) = ((p : ℤ) • P)) :
    |p| = |q| * |Q.content| := by
  have hc : (((q : ℤ) • Q).content) = (((p : ℤ) • P).content) := by rw [h]
  have hq : ((q : ℤ) • Q) = Polynomial.C q * Q := Polynomial.smul_eq_C_mul q
  have hp : ((p : ℤ) • P) = Polynomial.C p * P := Polynomial.smul_eq_C_mul p
  have hprim' : P.content = 1 := (Polynomial.isPrimitive_iff_content_eq_one).mp hprim
  have hP1 : |P.content| = 1 := by rw [hprim']; simp
  calc
    |p| = |p| * |P.content| := by rw [hP1, mul_one]
    _ = |p * P.content| := (abs_mul (p : ℤ) P.content).symm
    _ = |(Polynomial.C p * P).content| := (abs_content_C_mul p P).symm
    _ = |(((p : ℤ) • P).content)| := by rw [hp]
    _ = |(((q : ℤ) • Q).content)| := by rw [← hc]
    _ = |(Polynomial.C q * Q).content| := by rw [hq]
    _ = |q * Q.content| := abs_content_C_mul q Q
    _ = |q| * |Q.content| := abs_mul (q : ℤ) Q.content

/-- Sup-norm of an integer scalar multiple. -/
lemma supN_int_mul (k : ℤ) (P : Polynomial ℤ) :
    supN (((k : ℤ) • P)) = |(k : ℝ)| * supN P := by
  rw [Polynomial.smul_eq_C_mul]
  exact supN_C_mul k P

/-- If `q•Q = p•P` with `Q ≠ 0` and `P` primitive, then `|p| ≥ |q|`. -/
lemma abs_ge_of_scalar_eq {p q : ℤ} {Q P : Polynomial ℤ}
    (hQ : Q ≠ 0) (hprim : P.IsPrimitive) (h : ((q : ℤ) • Q) = ((p : ℤ) • P)) :
    |q| ≤ |p| := by
  have hcq : Q.content ≠ 0 := by
    intro hc0
    exact hQ ((Polynomial.content_eq_zero_iff).mp hc0)
  have habs : |p| = |q| * |Q.content| := abs_int_mul_of_scalar_eq hprim h
  have hone : 1 ≤ |Q.content| := Int.one_le_abs hcq
  have hmul : |q| * 1 ≤ |q| * |Q.content| :=
    mul_le_mul_of_nonneg_left hone (abs_nonneg (q : ℤ))
  calc
    |q| = |q| * (1 : ℤ) := by ring
    _ ≤ |q| * |Q.content| := hmul
    _ = |p| := habs.symm

/-- Sup-norm identity from `q•Q = p•P`: `|q|·‖Q‖ = |p|·‖P‖`. -/
lemma supN_eq_of_scalar_eq {p q : ℤ} {Q P : Polynomial ℤ}
    (h : ((q : ℤ) • Q) = ((p : ℤ) • P)) :
    |(q : ℝ)| * supN Q = |(p : ℝ)| * supN P := by
  have hsup : supN (((q : ℤ) • Q)) = supN (((p : ℤ) • P)) := by rw [h]
  rwa [supN_int_mul, supN_int_mul] at hsup

/-- Coefficient-wise integer proportionality from real proportionality of the maps. -/
lemma int_mul_eq_of_map_smul {Q P : Polynomial ℤ} (hP : P ≠ 0) {lam : ℝ}
    (hQm : (Q.map (Int.castRingHom ℝ)) = lam • (P.map (Int.castRingHom ℝ))) :
    ∃ p q : ℤ, q ≠ 0 ∧ ((q : ℤ) • Q) = ((p : ℤ) • P) := by
  classical
  have hcoeff : ∃ i : ℕ, P.coeff i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hP
    apply Polynomial.ext
    intro i
    exact h i
  rcases hcoeff with ⟨i0, hPi0⟩
  refine ⟨Q.coeff i0, P.coeff i0, hPi0, ?_⟩
  apply Polynomial.ext
  intro j
  have hQm_i0 : ((Q.map (Int.castRingHom ℝ)).coeff i0) =
      ((lam • (P.map (Int.castRingHom ℝ))).coeff i0) := by rw [hQm]
  have hQm_j : ((Q.map (Int.castRingHom ℝ)).coeff j) =
      ((lam • (P.map (Int.castRingHom ℝ))).coeff j) := by rw [hQm]
  have h1 : (Q.coeff i0 : ℝ) = lam * (P.coeff i0 : ℝ) := by
    simpa [Polynomial.coeff_map] using hQm_i0
  have h2 : (Q.coeff j : ℝ) = lam * (P.coeff j : ℝ) := by
    simpa [Polynomial.coeff_map] using hQm_j
  have hcross : (P.coeff i0 : ℝ) * (Q.coeff j : ℝ) =
      (Q.coeff i0 : ℝ) * (P.coeff j : ℝ) := by
    rw [h2, h1]
    ring
  have hcross_int : P.coeff i0 * Q.coeff j = Q.coeff i0 * P.coeff j := by
    exact_mod_cast hcross
  rw [Polynomial.coeff_smul, Polynomial.coeff_smul, zsmul_eq_mul, zsmul_eq_mul]
  exact hcross_int

/-- **M5(d)(1)**: the real maps of `Q` and `P` are ℝ-linearly independent, provided
`P` is primitive (automatic for irreducible nonconstant inputs) and `‖Q‖ < ‖P‖`. -/
theorem li_pair_maps_of_supN_lt {Q P : Polynomial ℤ} (hQ : Q ≠ 0)
    (hprim : P.IsPrimitive) (hPQ : supN Q < supN P) :
    LinearIndependent ℝ (fun i : Fin 2 => ![Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)] i) := by
  classical
  by_contra hlin
  rw [Fintype.linearIndependent_iff] at hlin
  push_neg at hlin
  rcases hlin with ⟨g, hsum, hg⟩
  have hsum2 : g 0 • (Q.map (Int.castRingHom ℝ)) + g 1 • (P.map (Int.castRingHom ℝ)) = 0 := by
    simpa [Fin.sum_univ_two] using hsum
  have hg0 : g 0 ≠ 0 := by
    intro hg0z
    have h : g 1 • (P.map (Int.castRingHom ℝ)) = 0 := by
      simpa [hg0z] using hsum2
    have hg1 : g 1 ≠ 0 := by
      intro hg1z
      rcases hg with ⟨i, hi⟩
      fin_cases i <;> simp [hg0z, hg1z] at hi
    have hPm0 : P.map (Int.castRingHom ℝ) = 0 := (smul_eq_zero.mp h).resolve_left hg1
    have hP0 : P = 0 := by
      exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using hPm0)
    exact hprim.ne_zero hP0
  let lam : ℝ := -(g 1 / g 0)
  have hQm : Q.map (Int.castRingHom ℝ) = lam • (P.map (Int.castRingHom ℝ)) := by
    dsimp [lam]
    have h1 : g 0 • (Q.map (Int.castRingHom ℝ)) = -(g 1 • (P.map (Int.castRingHom ℝ))) := by
      calc
        g 0 • (Q.map (Int.castRingHom ℝ)) =
            (g 0 • (Q.map (Int.castRingHom ℝ)) + g 1 • (P.map (Int.castRingHom ℝ))) - g 1 • (P.map (Int.castRingHom ℝ)) := by abel
        _ = 0 - g 1 • (P.map (Int.castRingHom ℝ)) := by rw [hsum2]
        _ = -(g 1 • (P.map (Int.castRingHom ℝ))) := by abel
    calc
      Q.map (Int.castRingHom ℝ) = (g 0)⁻¹ • (g 0 • (Q.map (Int.castRingHom ℝ))) := by
        rw [smul_smul]
        simp [hg0]
      _ = (g 0)⁻¹ • (-(g 1 • (P.map (Int.castRingHom ℝ)))) := by rw [h1]
      _ = lam • (P.map (Int.castRingHom ℝ)) := by
        dsimp [lam]
        rw [smul_neg, smul_smul, ← neg_smul]
        congr 1
        field_simp [hg0]
  rcases int_mul_eq_of_map_smul (Q := Q) (P := P) hprim.ne_zero hQm with ⟨p, q, hq0, hpq⟩
  have hge : |q| ≤ |p| := abs_ge_of_scalar_eq (Q := Q) (P := P) hQ hprim hpq
  have hnorm : |(q : ℝ)| * supN Q = |(p : ℝ)| * supN P := supN_eq_of_scalar_eq hpq
  have hPpos : 0 < supN P := supN_pos_of_ne_zero hprim.ne_zero
  have hqpos : 0 < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast hq0)
  have hpge : |(q : ℝ)| * supN P ≤ |(p : ℝ)| * supN P := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hge) (le_of_lt hPpos)
  have hQge : supN P ≤ supN Q := by
    have hnorm' : |(q : ℝ)| * supN P ≤ |(q : ℝ)| * supN Q := by
      calc
        |(q : ℝ)| * supN P ≤ |(p : ℝ)| * supN P := hpge
        _ = |(q : ℝ)| * supN Q := hnorm.symm
    exact le_of_mul_le_mul_left hnorm' hqpos
  exact (not_lt_of_ge hQge) hPQ


/-! ### (1b) inputs `P` are nonconstant hence primitive -/

/-- A nonzero polynomial of degree 0 is a nonunit exactly when its constant
coefficient is not a unit. -/
lemma irreducible_ne_zero {P : Polynomial ℤ} (hP : Irreducible P) : P ≠ 0 := by
  intro hP0
  exact (hP.isUnit_or_isUnit (a := (0 : Polynomial ℤ)) (b := (0 : Polynomial ℤ))
    (by rw [hP0]; ring)).elim (fun hu => not_isUnit_zero hu) (fun hu => not_isUnit_zero hu)

/-- From irreducibility and the tiny-value hypothesis, `P` is primitive (nonconstant). -/
lemma isPrimitive_of_irreducible_tiny_value {n : ℕ} {ξ : ℝ} {eps w2 : ℝ} (hw2 : eps < w2)
    {P : Polynomial ℤ} (hdeg : P.natDegree ≤ n) (hP : Irreducible P)
    (hval : |pv ξ P| ≤ supN P ^ (-(w2 - eps))) : P.IsPrimitive := by
  refine Irreducible.isPrimitive hP ?_
  intro hdeg0
  have hPnz : P ≠ 0 := irreducible_ne_zero hP
  have heq : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  set c : ℤ := P.coeff 0 with hcdef
  have hc0 : c ≠ 0 := by
    intro hc0z
    apply hPnz
    rw [heq]
    simp [hc0z]
  have hcnu : ¬ IsUnit (c : ℤ) := by
    intro hcu
    apply hP.not_isUnit
    rw [heq]
    exact (Polynomial.isUnit_C).2 hcu
  have hc2 : (2 : ℤ) ≤ |c| := by
    by_contra h2
    set a : ℤ := |c| with ha
    have h2a : ¬ (2 : ℤ) ≤ a := by simpa [ha] using h2
    have hla : a < 2 := lt_of_not_ge h2a
    have hle1 : a ≤ (1 : ℤ) := by omega
    have hle1c : |c| ≤ (1 : ℤ) := by simpa [ha] using hle1
    have hcne1 : c ≠ (1 : ℤ) := by intro hc1; apply hcnu; rw [hc1]; simp
    have hcnen1 : c ≠ (-1 : ℤ) := by intro hc1; apply hcnu; rw [hc1]; simp
    have hbounds : -1 ≤ c ∧ c ≤ (1 : ℤ) := (abs_le.mp hle1c)
    omega
  have hcabs : (((|c| : ℤ) : ℝ)) = ‖(c : ℝ)‖ :=
    (Int.cast_abs (a := c)).trans (Real.norm_eq_abs (c : ℝ)).symm
  have hbig : (2 : ℝ) ≤ ‖(c : ℝ)‖ := by
    have hc2' : ((2 : ℤ) : ℝ) ≤ ((|c| : ℤ) : ℝ) := by exact_mod_cast hc2
    rwa [hcabs] at hc2'
  have hsup : supN P = ‖(c : ℝ)‖ := by
    rw [heq]
    dsimp [supN]
    rw [Polynomial.map_C]
    exact Polynomial.supNorm_C
  have hpv : |pv ξ P| = ‖(c : ℝ)‖ := by
    rw [heq]
    dsimp [pv]
    simp
  have hle : ‖(c : ℝ)‖ ≤ ‖(c : ℝ)‖ ^ (-(w2 - eps)) := by
    rwa [hpv, hsup] at hval
  have hx1 : 1 < ‖(c : ℝ)‖ := by linarith
  have hpos : 0 < w2 - eps := by linarith
  have hpow : 1 < ‖(c : ℝ)‖ ^ (w2 - eps) := Real.one_lt_rpow hx1 hpos
  have hnegpow : ‖(c : ℝ)‖ ^ (-(w2 - eps)) = (‖(c : ℝ)‖ ^ (w2 - eps))⁻¹ :=
    Real.rpow_neg (by linarith : 0 ≤ ‖(c : ℝ)‖) (w2 - eps)
  have hRHS : ‖(c : ℝ)‖ ^ (-(w2 - eps)) < 1 := by
    rw [hnegpow]
    exact inv_lt_one_of_one_lt₀ hpow
  linarith

/-! ### (1c) the ℝ-independence of the realizer pair -/

/-- The real maps of a realizer `Q` (with ‖Q‖ ≤ e^{-n}‖P‖) and the input `P` are
ℝ-linearly independent (for `n ≥ 1`, `Q ≠ 0`, `P` irreducible primitive). -/
theorem li_pair_maps_realizer {n : ℕ} (hn : 1 ≤ n) {Q P : Polynomial ℤ} (hQ : Q ≠ 0)
    (hP : Irreducible P) (hprim : P.IsPrimitive)
    (hQle : supN Q ≤ Real.exp (-(n : ℝ)) * supN P) :
    LinearIndependent ℝ (fun i : Fin 2 => ![Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)] i) := by
  have hPnz : P ≠ 0 := irreducible_ne_zero hP
  have hPpos : 0 < supN P := supN_pos_of_ne_zero hPnz
  apply li_pair_maps_of_supN_lt hQ hprim
  have he : Real.exp (-(n : ℝ)) < 1 := by
    have hz : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hx : (1 : ℝ) < Real.exp (n : ℝ) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hz
    rw [Real.exp_neg]
    exact inv_lt_one_of_one_lt₀ hx
  have hlt : Real.exp (-(n : ℝ)) * supN P < supN P := by
    exact (mul_lt_iff_lt_one_left hPpos).mpr he
  exact lt_of_le_of_lt hQle hlt



open Polynomial
open scoped BigOperators

/-! ## Sec14 (M5(d), IN PROGRESS): the span/drop assembly

Work in `E := ↥(Polynomial.degreeLT ℝ (n+1))` (degree ≤ n real polynomials, finrank
n+1).  From the corrected base family `C` (`C 0 = Q`, maps LI) and the corrected
tails `Ct j = tailCorr P (C (Fin.succ j)) = C(succ j) + λ·P`, we get that the maps of
`{Q, P} ∪ range Ct` span `degreeLT`, and then `li_pair_drop_some` produces an LI
`(n+1)`-element family containing `Q` and `P` whose remaining members are among the
`Ct j`'s.  We lift it back to an LI family of integer-polynomial maps. -/

/-! ### (A) degreeLT glue -/

/-- An ℝ-polynomial of natDegree ≤ n lies in `degreeLT ℝ (n+1)`. -/
lemma degreeLT_mem_of_natDegree_le {n : ℕ} {f : Polynomial ℝ} (h : f.natDegree ≤ n) :
    f ∈ Polynomial.degreeLT ℝ (n + 1) := by
  rw [Polynomial.mem_degreeLT]
  have hlt : f.natDegree < n + 1 := Nat.lt_succ_of_le h
  exact lt_of_le_of_lt (Polynomial.degree_le_natDegree (p := f)) (by exact_mod_cast hlt)

/-- Real map of an integer polynomial of degree ≤ n lies in `degreeLT ℝ (n+1)`. -/
lemma map_mem_degreeLT {n : ℕ} {P : Polynomial ℤ} (h : P.natDegree ≤ n) :
    (P.map (Int.castRingHom ℝ)) ∈ Polynomial.degreeLT ℝ (n + 1) := by
  apply degreeLT_mem_of_natDegree_le
  rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
  exact h

/-- The space of degree-≤-n real polynomials has dimension n+1. -/
lemma finrank_degreeLT_succ (n : ℕ) :
    Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 := by
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℝ (n + 1))]
  simp

/-- `n+1` LI elements of `degreeLT ℝ (n+1)` span the whole space. -/
lemma li_span_top_degreeLT {n : ℕ} (u : Fin (n + 1) → Polynomial.degreeLT ℝ (n + 1))
    (hu : LinearIndependent ℝ u) : Submodule.span ℝ (Set.range u) = ⊤ := by
  exact LinearIndependent.span_eq_top_of_card_eq_finrank hu (by rw [finrank_degreeLT_succ]; simp)

/-- membership translation: an element of a submodule lies in the ambient span of the coerced
set iff it lies in the submodule-span. -/
lemma mem_span_coe_iff {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (S : Set P) (y : P) :
    (y : M) ∈ Submodule.span R ((fun x : P => (x : M)) '' S) ↔ y ∈ Submodule.span R S := by
  change P.subtype y ∈ Submodule.span R (⇑P.subtype '' S) ↔ y ∈ Submodule.span R S
  exact Submodule.apply_mem_span_image_iff_mem_span (f := P.subtype) (x := y) (s := S)
    P.injective_subtype

/-- span-in-submodule ⊤ iff the ambient span of the coerced set is the submodule. -/
lemma span_eq_top_iff_ambient {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (S : Set P) :
    Submodule.span R S = ⊤ ↔
      Submodule.span R ((fun x : P => (x : M)) '' S) = P := by
  constructor
  · intro h
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro m ⟨y, hyS, rfl⟩
      exact y.2
    · intro m hm
      let y : P := ⟨m, hm⟩
      have hy : y ∈ Submodule.span R S := by rw [h]; trivial
      have hym : (y : M) ∈ Submodule.span R ((fun x : P => (x : M)) '' S) :=
        (mem_span_coe_iff (P := P) (S := S) y).mpr hy
      exact hym
  · intro h
    apply le_antisymm
    · exact le_top
    · intro y hy
      have hym : (y : M) ∈ Submodule.span R ((fun x : P => (x : M)) '' S) := by
        rw [h]
        exact y.2
      exact (mem_span_coe_iff (P := P) (S := S) y).mp hym

/-! ### (B) span statements in the ambient space -/

/-- The maps of an LI corrected family `C` of degree-≤-n polynomials span `degreeLT`. -/
lemma span_C_maps_eq_degreeLT {n : ℕ} {C : Fin (n + 1) → Polynomial ℤ}
    (hCdeg : ∀ i : Fin (n + 1), (C i).natDegree ≤ n)
    (hCli : LinearIndependent ℝ (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ))) :
    Submodule.span ℝ (Set.range (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ))) =
      (Polynomial.degreeLT ℝ (n + 1) : Submodule ℝ (Polynomial ℝ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact map_mem_degreeLT (hCdeg i)
  · intro x hx
    let u : Fin (n + 1) → Polynomial.degreeLT ℝ (n + 1) := fun i =>
      ⟨(C i).map (Int.castRingHom ℝ), map_mem_degreeLT (hCdeg i)⟩
    have huli : LinearIndependent ℝ u := by
      exact Commons.LinearAlgebra.Independence.linearIndependent_of_ambient
        (P := Polynomial.degreeLT ℝ (n + 1)) u hCli
    have hspan : Submodule.span ℝ (Set.range u) = ⊤ := li_span_top_degreeLT u huli
    have hxspan : (⟨x, hx⟩ : Polynomial.degreeLT ℝ (n + 1)) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]
      trivial
    have hxamb : x ∈ Submodule.span ℝ ((fun y : Polynomial.degreeLT ℝ (n + 1) => (y : Polynomial ℝ)) ''
        Set.range u) :=
      (mem_span_coe_iff (P := Polynomial.degreeLT ℝ (n + 1)) (S := Set.range u)
        (⟨x, hx⟩ : Polynomial.degreeLT ℝ (n + 1))).mpr hxspan
    have him : ((fun y : Polynomial.degreeLT ℝ (n + 1) => (y : Polynomial ℝ)) '' Set.range u) =
        Set.range (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        simpa [u] using congrArg (fun w : Polynomial.degreeLT ℝ (n + 1) => (w : Polynomial ℝ)) hi
      · rintro ⟨i, rfl⟩
        refine ⟨u i, ⟨i, rfl⟩, ?_⟩
        rfl
    rwa [him] at hxamb

/-- real map of `C (Fin.succ j)` lies in the span of `{Qm, Pm} ∪ range (Ct maps)`,
provided `C (succ j) = Ct j + C λ * P`. -/
lemma map_C_succ_mem_span {n : ℕ} {Q P : Polynomial ℤ} (C : Fin (n + 1) → Polynomial ℤ)
    (Ct : Fin n → Polynomial ℤ) {j : Fin n} {lam : ℤ}
    (hrel : C (Fin.succ j) = Ct j + Polynomial.C lam * P) :
    (C (Fin.succ j)).map (Int.castRingHom ℝ) ∈
      Submodule.span ℝ ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
        Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ))) := by
  have hmap : (C (Fin.succ j)).map (Int.castRingHom ℝ) =
      (Ct j).map (Int.castRingHom ℝ) + (lam : ℝ) • (P.map (Int.castRingHom ℝ)) := by
    rw [hrel]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    simp [Algebra.smul_def]
  rw [hmap]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.subset_span (by
      exact Or.inr (Set.mem_range.mpr ⟨j, rfl⟩))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by
      exact Or.inl (Or.inr rfl)))

/-- The maps of `{Q, P} ∪ range Ct` span `degreeLT` (from the corrected-family data). -/
lemma span_qp_ct_eq_degreeLT {n : ℕ} {Q P : Polynomial ℤ}
    (hdegQ : Q.natDegree ≤ n) (hdegP : P.natDegree ≤ n)
    (C : Fin (n + 1) → Polynomial ℤ) (Ct : Fin n → Polynomial ℤ)
    (hC0 : C 0 = Q)
    (hCdeg : ∀ i : Fin (n + 1), (C i).natDegree ≤ n)
    (hCli : LinearIndependent ℝ (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)))
    (hCtdeg : ∀ j : Fin n, (Ct j).natDegree ≤ n)
    (hrel : ∀ j : Fin n, ∃ lam : ℤ, C (Fin.succ j) = Ct j + Polynomial.C lam * P) :
    Submodule.span ℝ ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
        Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ))) =
      (Polynomial.degreeLT ℝ (n + 1) : Submodule ℝ (Polynomial ℝ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x hx
    rcases hx with hx | hx
    · rcases hx with rfl | rfl
      · exact map_mem_degreeLT hdegQ
      · exact map_mem_degreeLT hdegP
    · rcases hx with ⟨k, rfl⟩
      exact map_mem_degreeLT (hCtdeg k)
  · -- ⊇: degreeLT ⊆ span{Qm,Pm,Ct}
    have hCspan := span_C_maps_eq_degreeLT (C := C) hCdeg hCli
    -- show each C-map is in span{Qm,Pm,Ct}
    have hCsubset : Set.range (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)) ⊆
        Submodule.span ℝ ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
          Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ))) := by
      intro y hy
      rcases hy with ⟨i, rfl⟩
      change (C i).map (Int.castRingHom ℝ) ∈
        Submodule.span ℝ ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
          Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ)))
      by_cases hi0 : (i : ℕ) = 0
      · have hC0i : C i = Q := by
          have h0 : i = 0 := by
            apply Fin.ext
            exact hi0
          rw [h0, hC0]
        rw [hC0i]
        exact Submodule.subset_span (by exact Or.inl (Or.inl rfl))
      · let j : Fin n := ⟨(i : ℕ) - 1, by
          have hi : (i : ℕ) < n + 1 := i.2
          have hi0' : 1 ≤ (i : ℕ) := by omega
          omega⟩
        have hij : i = Fin.succ j := by
          apply Fin.ext
          dsimp [j]
          omega
        rw [hij]
        rcases hrel j with ⟨lam, hrelj⟩
        exact map_C_succ_mem_span (C := C) (Ct := Ct) (j := j) (lam := lam) hrelj
    calc
      (Polynomial.degreeLT ℝ (n + 1) : Submodule ℝ (Polynomial ℝ))
          = Submodule.span ℝ (Set.range (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ))) := hCspan.symm
      _ ≤ Submodule.span ℝ ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
          Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ))) :=
            Submodule.span_le.mpr hCsubset

/-! ### (C) the drop assembly in `degreeLT` -/

/-- **M5(d)(2-4)**: from the corrected family data, an LI family of integer-polynomial
maps containing `Q` and `P`, all of degree ≤ n, whose remaining members are corrected
tails `Ct j`. -/
theorem m5_li_family {n : ℕ} (hn : 1 ≤ n) {Q P : Polynomial ℤ}
    (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hP : Irreducible P) (hdegP : P.natDegree ≤ n) (hprimP : P.IsPrimitive)
    (hQle : supN Q ≤ Real.exp (-(n : ℝ)) * supN P)
    (C : Fin (n + 1) → Polynomial ℤ) (Ct : Fin n → Polynomial ℤ)
    (hC0 : C 0 = Q)
    (hCdeg : ∀ i : Fin (n + 1), (C i).natDegree ≤ n)
    (hCli : LinearIndependent ℝ (fun i : Fin (n + 1) => (C i).map (Int.castRingHom ℝ)))
    (hCtdeg : ∀ j : Fin n, (Ct j).natDegree ≤ n)
    (hrel : ∀ j : Fin n, ∃ lam : ℤ, C (Fin.succ j) = Ct j + Polynomial.C lam * P) :
    ∃ F : Fin (n + 1) → Polynomial ℤ,
      F ⟨0, by omega⟩ = Q ∧ F ⟨1, by omega⟩ = P ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)) ∧
      (∀ i : Fin (n + 1), (F i).natDegree ≤ n) ∧
      (∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j) := by
  classical
  let E : Submodule ℝ (Polynomial ℝ) := Polynomial.degreeLT ℝ (n + 1)
  let a : E := ⟨Q.map (Int.castRingHom ℝ), map_mem_degreeLT hdegQ⟩
  let b : E := ⟨P.map (Int.castRingHom ℝ), map_mem_degreeLT hdegP⟩
  let v : Fin n → E := fun j => ⟨(Ct j).map (Int.castRingHom ℝ), map_mem_degreeLT (hCtdeg j)⟩
  -- LI of the pair (a, b)
  have hfam : (fun i : Fin 2 => (((![a, b] : Fin 2 → E) i : E) : Polynomial ℝ)) =
      (fun i : Fin 2 => ![Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)] i) := by
    funext i
    fin_cases i
    · change ((a : E) : Polynomial ℝ) = Q.map (Int.castRingHom ℝ)
      rfl
    · change ((b : E) : Polynomial ℝ) = P.map (Int.castRingHom ℝ)
      rfl
  have hab : LinearIndependent ℝ (![a, b] : Fin 2 → E) := by
    exact Commons.LinearAlgebra.Independence.linearIndependent_of_ambient (P := E) ![a, b]
      (by
        rw [hfam]
        exact li_pair_maps_realizer (n := n) hn hQ hP hprimP hQle)
  -- spanning
  have hspanamb : Submodule.span ℝ (((fun y : E => (y : Polynomial ℝ)) '' ({a, b} ∪ Set.range v))) =
      (E : Submodule ℝ (Polynomial ℝ)) := by
    have hSamb : ((fun y : E => (y : Polynomial ℝ)) '' ({a, b} ∪ Set.range v)) =
        ({Q.map (Int.castRingHom ℝ), P.map (Int.castRingHom ℝ)} ∪
          Set.range (fun k : Fin n => (Ct k).map (Int.castRingHom ℝ))) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with hy | hy
        · rcases hy with rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr rfl)
        · rcases hy with ⟨j, rfl⟩
          exact Or.inr (⟨j, rfl⟩)
      · rintro hz
        rcases hz with hz | hz
        · rcases hz with rfl | rfl
          · refine ⟨a, Or.inl (Or.inl rfl), ?_⟩
            rfl
          · refine ⟨b, Or.inl (Or.inr rfl), ?_⟩
            rfl
        · rcases hz with ⟨j, rfl⟩
          refine ⟨v j, Or.inr (⟨j, rfl⟩), ?_⟩
          rfl
    rw [hSamb]
    exact span_qp_ct_eq_degreeLT (n := n) hdegQ hdegP C Ct hC0 hCdeg hCli hCtdeg hrel
  have hspanE : Submodule.span ℝ ({a, b} ∪ Set.range v) = ⊤ := by
    exact (span_eq_top_iff_ambient (P := E) (S := {a, b} ∪ Set.range v)).mpr hspanamb
  rcases Commons.LinearAlgebra.Independence.li_pair_drop_some (n := n) (E := E)
    (hE := finrank_degreeLT_succ n) hab v hspanE with ⟨f, hfLI, hf0, hf1, hftail⟩
  have htail_ex : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, f i = v j := by
    intro i hi
    rcases hftail i hi with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  -- F: integer polynomial whose map at index i is (f i : ℝ[X])
  let F : Fin (n + 1) → Polynomial ℤ := fun i =>
    if h0 : (i : ℕ) = 0 then Q
    else if h1 : (i : ℕ) = 1 then P
    else Ct (Classical.choose (htail_ex i (by omega)))
  have hF0 : F ⟨0, by omega⟩ = Q := by
    simp [F]
  have hF1 : F ⟨1, by omega⟩ = P := by
    simp [F]
  have hf0z : f ⟨0, by omega⟩ = a := by
    have h0eq : (⟨0, by omega⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    rw [h0eq]
    exact hf0
  have hf1z : f ⟨1, by omega⟩ = b := by
    have h1eq : (⟨1, by omega⟩ : Fin (n + 1)) = (1 : Fin (n + 1)) := by
      apply Fin.ext
      have hlt : 1 < n + 1 := by omega
      simp [Nat.mod_eq_of_lt hlt]
    rw [h1eq]
    exact hf1
  have hFmap0 : (F ⟨0, by omega⟩).map (Int.castRingHom ℝ) =
      ((f ⟨0, by omega⟩ : E) : Polynomial ℝ) := by
    rw [hF0, hf0z]
  have hFmap1 : (F ⟨1, by omega⟩).map (Int.castRingHom ℝ) =
      ((f ⟨1, by omega⟩ : E) : Polynomial ℝ) := by
    rw [hF1, hf1z]
  have hFmap : ∀ i : Fin (n + 1), (F i).map (Int.castRingHom ℝ) = ((f i : E) : Polynomial ℝ) := by
    intro i
    by_cases hi0 : i = (⟨0, by omega⟩ : Fin (n + 1))
    · subst i
      exact hFmap0
    · by_cases hi1 : i = (⟨1, by omega⟩ : Fin (n + 1))
      · subst i
        exact hFmap1
      · have hile : 2 ≤ (i : ℕ) := by
          have h0ne : (i : ℕ) ≠ 0 := by
            intro h
            apply hi0
            apply Fin.ext
            exact h
          have h1ne : (i : ℕ) ≠ 1 := by
            intro h
            apply hi1
            apply Fin.ext
            exact h
          omega
        have hmem := htail_ex i hile
        let j : Fin n := Classical.choose hmem
        have hspec : f i = v j := Classical.choose_spec hmem
        have hFi : F i = Ct j := by
          dsimp [F]
          rw [dif_neg (by intro h; apply hi0; apply Fin.ext; exact h),
              dif_neg (by intro h; apply hi1; apply Fin.ext; exact h)]
        rw [hFi]
        rw [hspec]
  have hfambLI : LinearIndependent ℝ (fun i : Fin (n + 1) => ((f i : E) : Polynomial ℝ)) := by
    exact LinearIndependent.map' hfLI E.subtype (by simp)
  have hFLI : LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)) := by
    convert hfambLI using 1
    funext i
    exact hFmap i
  refine ⟨F, hF0, hF1, hFLI, ?_, ?_⟩
  · intro i
    by_cases hi0 : i = (⟨0, by omega⟩ : Fin (n + 1))
    · subst i
      simpa [F] using hdegQ
    · by_cases hi1 : i = (⟨1, by omega⟩ : Fin (n + 1))
      · subst i
        simpa [F] using hdegP
      · have hile : 2 ≤ (i : ℕ) := by
          have h0ne : (i : ℕ) ≠ 0 := by
            intro h
            apply hi0
            apply Fin.ext
            exact h
          have h1ne : (i : ℕ) ≠ 1 := by
            intro h
            apply hi1
            apply Fin.ext
            exact h
          omega
        let j : Fin n := Classical.choose (htail_ex i hile)
        have hFi : F i = Ct j := by
          dsimp [F]
          rw [dif_neg (by intro h; apply hi0; apply Fin.ext; exact h),
              dif_neg (by intro h; apply hi1; apply Fin.ext; exact h)]
        rw [hFi]
        exact hCtdeg j
  · intro i hile
    let j : Fin n := Classical.choose (htail_ex i hile)
    refine ⟨j, ?_⟩
    by_cases hi0 : i = (⟨0, by omega⟩ : Fin (n + 1))
    · exfalso
      have hiv : (i : ℕ) = 0 := by
        simpa using congrArg (fun x : Fin (n + 1) => (x : ℕ)) hi0
      omega
    · by_cases hi1 : i = (⟨1, by omega⟩ : Fin (n + 1))
      · exfalso
        have hiv : (i : ℕ) = 1 := by
          simpa using congrArg (fun x : Fin (n + 1) => (x : ℕ)) hi1
        omega
      · dsimp [F]
        rw [dif_neg (by intro h; apply hi0; apply Fin.ext; exact h),
            dif_neg (by intro h; apply hi1; apply Fin.ext; exact h)]



open Polynomial
open scoped BigOperators

/-! ## Sec15 (M5(d)-(5), IN PROGRESS): the sorted ℕ-indexed final family

From an LI family `F : Fin (n+1) → ℤ[X]` (the output of `m5_li_family`: `F⟨0⟩ = Q`,
`F⟨1⟩ = P`, degree ≤ n, tails no smaller in norm than `P`), produce the final
ℕ-indexed family `Qfun : ℕ → ℤ[X]` with `Qfun 1 = Q`, `Qfun 2 = P` and the tail
positions sorted by increasing sup-norm (a permutation of the `Fin (n-1)` tail
slots), together with the degree / LI / monotonicity facts the theorem asserts. -/

/-- tail positions of a `Fin (n+1)`-family: `tailPos j = ⟨j.val + 2, _⟩`. -/
def tailPos {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) : Fin (n + 1) :=
  ⟨(j : ℕ) + 2, by
    have hj : (j : ℕ) < n - 1 := j.2
    omega⟩

/-- `v - 2 < n - 1` when `2 ≤ v ≤ n`, `2 ≤ n`. -/
lemma sub_lt_fin {n v : ℕ} (hn : 2 ≤ n) (hv : v ≤ n) (hv2 : 2 ≤ v) : v - 2 < n - 1 := by
  have h1 : v - 2 ≤ n - 2 := Nat.sub_le_sub_right hv 2
  have h2 : n - 2 < n - 1 := by omega
  exact lt_of_le_of_lt h1 h2

/-- total `Fin (n+1)`-valued version of `i - 1` (capped at n); equals `⟨i-1⟩` for
`3 ≤ i ≤ n+1`. -/
def finPred {n : ℕ} (i : ℕ) : Fin (n + 1) :=
  ⟨min (i - 1) n, by
    have hmin : min (i - 1) n ≤ n := min_le_right _ _
    omega⟩

/-- for `i ∈ Icc 3 (n+1)`, `finPred i` has value `i - 1`. -/
lemma finPred_val_of_Icc3 {n i : ℕ} (hi : i ∈ Finset.Icc 3 (n + 1)) :
    (finPred (n := n) i : ℕ) = i - 1 := by
  dsimp [finPred]
  have hge : 3 ≤ i := (Finset.mem_Icc.mp hi).1
  have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
  rw [min_eq_left (by omega)]

/-- `tailPos j = finPred (j + 3)` (both have value `j.val + 2`). -/
lemma tailPos_eq_finPred {n : ℕ} (hn : 2 ≤ n) (j : Fin (n - 1)) :
    tailPos hn j = finPred (n := n) ((j : ℕ) + 3) := by
  apply Fin.ext
  have hj : (j : ℕ) < n - 1 := j.2
  dsimp [tailPos, finPred]
  rw [min_eq_left (by omega)]

/-- product over the tail slots equals the product over `finPred` at `Icc 3 (n+1)`. -/
lemma prod_Icc3_finPred {n : ℕ} (hn : 2 ≤ n) (f : Fin (n + 1) → ℝ) :
    (∏ j : Fin (n - 1), f (tailPos hn j)) = ∏ i ∈ Finset.Icc 3 (n + 1), f (finPred (n := n) i) := by
  classical
  refine Finset.prod_bij (s := Finset.univ) (t := Finset.Icc 3 (n + 1))
    (fun a _ => (a : ℕ) + 3) ?_ ?_ ?_ ?_
  · intro a ha
    simp [Finset.mem_Icc]
    have hav : (a : ℕ) < n - 1 := a.2
    omega
  · intro a ha b hb h
    apply Fin.ext
    omega
  · intro i hi
    let a : Fin (n - 1) := ⟨i - 3, by
      have hge : 3 ≤ i := (Finset.mem_Icc.mp hi).1
      have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
      omega⟩
    refine ⟨a, by simp, ?_⟩
    have hge : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    have hva : (a : ℕ) = i - 3 := rfl
    rw [hva]
    omega
  · intro a ha
    rw [tailPos_eq_finPred hn a]

/-- value-level reindexing: 0 ↦ 0, 1 ↦ 1, v ↦ σ(v-2).val + 2 (v ≥ 2). -/
def reindexVal {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) (v : ℕ) (hv : v ≤ n) : ℕ :=
  if h0 : v = 0 then 0 else if h1 : v = 1 then 1 else
    ((σ ⟨v - 2, sub_lt_fin hn hv (by omega)⟩ : Fin (n - 1)) : ℕ) + 2

lemma reindexVal_0 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) :
    reindexVal hn σ 0 (by omega) = 0 := by
  simp [reindexVal]

lemma reindexVal_1 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) :
    reindexVal hn σ 1 (by omega) = 1 := by
  simp [reindexVal]

lemma reindexVal_ge2 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) {v : ℕ}
    (hv : v ≤ n) (hv2 : 2 ≤ v) :
    reindexVal hn σ v hv = ((σ ⟨v - 2, sub_lt_fin hn hv hv2⟩ : Fin (n - 1)) : ℕ) + 2 := by
  have hv0 : v ≠ 0 := by omega
  have hv1 : v ≠ 1 := by omega
  simp [reindexVal, hv0, hv1]

/-- the value-level reindexing is injective on `0..n`. -/
lemma reindexVal_inj {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) {v w : ℕ}
    (hv : v ≤ n) (hw : w ≤ n)
    (h : reindexVal hn σ v hv = reindexVal hn σ w hw) : v = w := by
  by_cases hv0 : v = 0
  · subst v
    have hw0 : w = 0 := by
      by_cases hw0 : w = 0
      · exact hw0
      · by_cases hw1 : w = 1
        · have hwv : reindexVal hn σ 0 (by omega) = reindexVal hn σ 1 (by omega) := by
            simpa [hw1] using h
          have h0' : reindexVal hn σ 0 (by omega) = 0 := reindexVal_0 hn σ
          have h1' : reindexVal hn σ 1 (by omega) = 1 := reindexVal_1 hn σ
          omega
        · have hw2 : 2 ≤ w := by omega
          have hwval : 2 ≤ reindexVal hn σ w hw := by
            rw [reindexVal_ge2 hn σ hw hw2]
            omega
          have h0' : reindexVal hn σ 0 (by omega) = 0 := reindexVal_0 hn σ
          omega
    omega
  · by_cases hv1 : v = 1
    · subst v
      have hw1 : w = 1 := by
        by_cases hw1 : w = 1
        · exact hw1
        · by_cases hw0 : w = 0
          · have hwv : reindexVal hn σ 1 (by omega) = reindexVal hn σ 0 (by omega) := by
              simpa [hw0] using h
            have h1' : reindexVal hn σ 1 (by omega) = 1 := reindexVal_1 hn σ
            have h0' : reindexVal hn σ 0 (by omega) = 0 := reindexVal_0 hn σ
            omega
          · have hw2 : 2 ≤ w := by omega
            have hwval : 2 ≤ reindexVal hn σ w hw := by
              rw [reindexVal_ge2 hn σ hw hw2]
              omega
            have h1' : reindexVal hn σ 1 (by omega) = 1 := reindexVal_1 hn σ
            omega
      omega
    · have hv2 : 2 ≤ v := by omega
      have hw2 : 2 ≤ w := by
        by_contra hwnot
        by_cases hw0 : w = 0
        · have hwv : reindexVal hn σ w hw = 0 := by
            subst w
            exact reindexVal_0 hn σ
          have hvval : 2 ≤ reindexVal hn σ v hv := by
            rw [reindexVal_ge2 hn σ hv hv2]
            omega
          omega
        · have hw1 : w = 1 := by omega
          have hwv : reindexVal hn σ w hw = 1 := by
            subst w
            exact reindexVal_1 hn σ
          have hvval : 2 ≤ reindexVal hn σ v hv := by
            rw [reindexVal_ge2 hn σ hv hv2]
            omega
          omega
      have hvval := reindexVal_ge2 hn σ hv hv2
      have hwval := reindexVal_ge2 hn σ hw hw2
      have hσ : ((σ ⟨v - 2, sub_lt_fin hn hv hv2⟩ : Fin (n - 1)) : ℕ) =
          ((σ ⟨w - 2, sub_lt_fin hn hw hw2⟩ : Fin (n - 1)) : ℕ) := by omega
      have hσij : (⟨v - 2, sub_lt_fin hn hv hv2⟩ : Fin (n - 1)) =
          (⟨w - 2, sub_lt_fin hn hw hw2⟩ : Fin (n - 1)) := by
        exact σ.injective (by
          apply Fin.ext
          exact hσ)
      have hsrcv : v - 2 = w - 2 := by
        exact congrArg Fin.val hσij
      omega

/-- index reindexing on `Fin (n+1)`: fix 0 and 1, permute the tail slots by `σ`. -/
def reindexPos {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) : Fin (n + 1) → Fin (n + 1) :=
  fun i => ⟨reindexVal hn σ (i : ℕ) (by
      have hlt : (i : ℕ) < n + 1 := i.2
      omega), by
    have hle : reindexVal hn σ (i : ℕ) (by omega) ≤ n := by
      dsimp [reindexVal]
      split_ifs <;> omega
    exact lt_of_le_of_lt hle (by omega)⟩

/-- `reindexPos` is injective. -/
lemma reindexPos_injective {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1))) :
    Function.Injective (reindexPos hn σ) := by
  intro i j hij
  apply Fin.ext
  have hval : (reindexPos hn σ i).val = (reindexPos hn σ j).val := by
    exact congrArg Fin.val hij
  dsimp [reindexPos] at hval
  have hv : (i : ℕ) ≤ n := by
    have hlt : (i : ℕ) < n + 1 := i.2
    omega
  have hw : (j : ℕ) ≤ n := by
    have hlt : (j : ℕ) < n + 1 := j.2
    omega
  have hinj := reindexVal_inj hn σ hv hw (by simpa using hval)
  exact hinj

/-- `reindexPos` fixes index 0. -/
lemma reindexPos_zero {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1)))
    (i : Fin (n + 1)) (hi : (i : ℕ) = 0) : reindexPos hn σ i = (⟨0, by omega⟩ : Fin (n + 1)) := by
  apply Fin.ext
  dsimp [reindexPos]
  dsimp [reindexVal]
  simp [hi]

/-- `reindexPos` fixes index 1. -/
lemma reindexPos_one {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1)))
    (i : Fin (n + 1)) (hi : (i : ℕ) = 1) : reindexPos hn σ i = (⟨1, by omega⟩ : Fin (n + 1)) := by
  apply Fin.ext
  dsimp [reindexPos]
  dsimp [reindexVal]
  simp [hi]

/-- `reindexPos` moves a tail index `i` (val ≥ 2) to the `σ`-permuted tail slot. -/
lemma reindexPos_tail {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1)))
    (i : Fin (n + 1)) (hi : 2 ≤ (i : ℕ)) :
    reindexPos hn σ i = tailPos hn (σ ⟨(i : ℕ) - 2, by omega⟩) := by
  apply Fin.ext
  dsimp [reindexPos]
  rw [reindexVal_ge2 hn σ (by
    have hlt : (i : ℕ) < n + 1 := i.2
    omega) hi]
  dsimp [tailPos]


/-- **M5(d)(5)** (first form): from an LI `Fin (n+1)`-family `F` whose tail members
(positions `tailPos j`, `j : Fin (n-1)`) already have nondecreasing sup-norms, build
the final ℕ-indexed family `Qfun` (`Qfun 1 = Q`, `Qfun 2 = P`, `Qfun k = F⟨k-1⟩`
for `k = 3..n+1`), with degree bounds, LI of the real maps, the two norm
monotonicity clauses, and the exponent `x := log(∏_{i=2}^{n+1} H_i)/log H_2`
satisfying `∏ H_i = H_2^x` and `(n : ℝ) ≤ x`. -/
theorem m5_sorted_family {n : ℕ} (hn : 2 ≤ n) {Q P : Polynomial ℤ}
    (F : Fin (n + 1) → Polynomial ℤ)
    (hF0 : F (0 : Fin (n + 1)) = Q) (hF1 : F (1 : Fin (n + 1)) = P)
    (hdegF : ∀ i : Fin (n + 1), (F i).natDegree ≤ n)
    (hliF : LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)))
    (hQP : supN Q ≤ supN P)
    (hPgt1 : 1 < supN P)
    (hFtail : ∀ j : Fin (n - 1), supN P ≤ supN (F (tailPos hn j)))
    (hFmono : ∀ j j' : Fin (n - 1), (j : ℕ) ≤ (j' : ℕ) →
      supN (F (tailPos hn j)) ≤ supN (F (tailPos hn j'))) :
    ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
      Qfun 1 = Q ∧ Qfun 2 = P ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) ∧
      (n : ℝ) ≤ x ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → ∃ j : Fin (n + 1), Qfun i = F j) := by
  classical
  let Qfun : ℕ → Polynomial ℤ := fun k =>
    if h1 : k = 1 then Q else if h2 : k = 2 then P else
      if hk : 3 ≤ k ∧ k ≤ n + 1 then F ⟨k - 1, by omega⟩ else 0
  -- Qfun k = F⟨k-1⟩ for 1 ≤ k ≤ n+1
  have hQfunF : ∀ (k : ℕ), 1 ≤ k → k ≤ n + 1 →
      ∀ p : k - 1 < n + 1, Qfun k = F (⟨k - 1, p⟩ : Fin (n + 1)) := by
    intro k hk1 hk2 p
    by_cases hk : k = 1
    · subst k
      have hzero : (⟨1 - 1, p⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp
      rw [hzero]
      simp [Qfun, hF0]
    · by_cases hk2' : k = 2
      · subst k
        have hone : (⟨2 - 1, p⟩ : Fin (n + 1)) = (1 : Fin (n + 1)) := by
          apply Fin.ext
          have hlt : 1 < n + 1 := by omega
          simp [Nat.mod_eq_of_lt hlt]
        rw [hone]
        simp [Qfun, hF1]
      · have hk3 : 3 ≤ k := by omega
        have hk1' : ¬ k = 1 := by omega
        have hk2' : ¬ k = 2 := by omega
        have hk3' : 3 ≤ k ∧ k ≤ n + 1 := by omega
        simp [Qfun, hk1', hk2', hk3']
  have hQfun1 : Qfun 1 = Q := by
    simp [Qfun]
  have hQfun2 : Qfun 2 = P := by
    simp [Qfun]
  let H : ℕ → ℝ := fun k => supN (Qfun k)
  have hH2P : H 2 = supN P := by
    dsimp [H]
    rw [hQfun2]
  have hQtail_pos : ∀ k : ℕ, 3 ≤ k → k ≤ n + 1 →
      ∃ p : k - 1 < n + 1, Qfun k = F (tailPos hn ⟨k - 3, by omega⟩) := by
    intro k hk3 hk1
    have hQ := hQfunF k (by omega) hk1 (by omega)
    -- RHS F⟨k-1, p⟩ equals F(tailPos⟨k-3⟩)
    refine ⟨by omega, ?_⟩
    rw [hQ]
    have hpos : (⟨k - 1, by omega⟩ : Fin (n + 1)) = tailPos hn (⟨k - 3, by omega⟩ : Fin (n - 1)) := by
      apply Fin.ext
      dsimp [tailPos]
      omega
    rw [hpos]
  have hHge2 : ∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → H 2 ≤ H i := by
    intro i hi
    have hge : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
    by_cases hi2 : i = 2
    · subst i
      rfl
    · have hge3 : 3 ≤ i := by omega
      rcases hQtail_pos i hge3 hle with ⟨p, hQi⟩
      dsimp [H]
      rw [hQfun2, hQi]
      exact hFtail ⟨i - 3, by omega⟩
  have hprod_eq : (∏ i ∈ Finset.Icc 2 (n + 1), H i) = (H 2) ^
      (Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log (H 2)) := by
    have hH2 : 1 < H 2 := by
      rw [hH2P]
      exact hPgt1
    have hprodpos : 0 < ∏ i ∈ Finset.Icc 2 (n + 1), H i := by
      refine Finset.prod_pos ?_
      intro i hi
      have h2 : 1 < H i := lt_of_lt_of_le hH2 (hHge2 i hi)
      nlinarith
    exact (rpow_log_div_log (H := H 2) hH2 hprodpos).symm
  have hx_ge : (n : ℝ) ≤ Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log (H 2) := by
    have hH2 : 1 < H 2 := by
      rw [hH2P]
      exact hPgt1
    have hxge := x_ge_n_of_rpow_prod_Icc (n := n) (H := H 2) hH2 hHge2
      (y := Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log (H 2)) hprod_eq
    exact hxge
  have hQtail_prod : (∏ i ∈ Finset.Icc 3 (n + 1), supN (Qfun i)) =
      ∏ j : Fin (n - 1), supN (F (tailPos hn j)) := by
    calc
      (∏ i ∈ Finset.Icc 3 (n + 1), supN (Qfun i))
          = (∏ i ∈ Finset.Icc 3 (n + 1), supN (F (finPred (n := n) i))) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              have hge3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
              have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
              have hQf : Qfun i = F (finPred (n := n) i) := by
                have hi1' : ¬ i = 1 := by omega
                have hi2' : ¬ i = 2 := by omega
                have hi3' : 3 ≤ i ∧ i ≤ n + 1 := ⟨hge3, hle⟩
                simp [Qfun, hi1', hi2', hi3']
                congr 1
                apply Fin.ext
                dsimp [finPred]
                rw [min_eq_left (by omega : i - 1 ≤ n)]
              exact congrArg supN hQf
      _ = ∏ j : Fin (n - 1), supN (F (tailPos hn j)) := by
          exact (prod_Icc3_finPred hn (fun k : Fin (n + 1) => supN (F k))).symm
  have hprodF : (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) =
      supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) := by
    calc
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i))
          = supN (Qfun 2) * (∏ i ∈ Finset.Icc 3 (n + 1), supN (Qfun i)) := by
              have hIcc : Finset.Icc 2 (n + 1) = insert 2 (Finset.Icc 3 (n + 1)) := by
                ext i
                constructor
                · intro hi
                  have hge : 2 ≤ i := (Finset.mem_Icc.mp hi).1
                  have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
                  rw [Finset.mem_insert]
                  by_cases hi2 : i = 2
                  · exact Or.inl hi2
                  · exact Or.inr (Finset.mem_Icc.mpr ⟨by omega, hle⟩)
                · intro hi
                  rw [Finset.mem_insert] at hi
                  rcases hi with h | h
                  · subst i
                    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
                  · exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp h).1; omega,
                      (Finset.mem_Icc.mp h).2⟩
              rw [hIcc, Finset.prod_insert (by simp [Finset.mem_Icc] : (2 : ℕ) ∉ Finset.Icc 3 (n + 1))]
      _ = supN P * (∏ i ∈ Finset.Icc 3 (n + 1), supN (Qfun i)) := by rw [hQfun2]
      _ = supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) := by rw [hQtail_prod]
  have hQmem : ∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → ∃ j : Fin (n + 1), Qfun i = F j := by
    intro i hi
    have hge : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
    have p : i - 1 < n + 1 := by omega
    refine ⟨⟨i - 1, p⟩, ?_⟩
    exact hQfunF i hge hle p
  refine ⟨Qfun, Real.log (∏ i ∈ Finset.Icc 2 (n + 1), H i) / Real.log (H 2),
    hQfun1, hQfun2, ?_, ?_, ?_, ?_, ?_, ?_, hx_ge, hQmem⟩
  · intro i hi
    have hge : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hle : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
    have hQ := hQfunF i hge hle (by omega)
    rw [hQ]
    exact hdegF ⟨i - 1, by omega⟩
  · -- LI: Qfun(i.val+1) = F i
    have hid : (fun i : Fin (n + 1) => (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) =
        (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)) := by
      funext i
      congr 1
      have hQ := hQfunF ((i : ℕ) + 1) (by omega) (by omega) (by omega)
      have hsub : ((i : ℕ) + 1) - 1 = (i : ℕ) := by omega
      simpa [hsub] using hQ
    rw [hid]
    exact hliF
  · intro i hi
    have hge : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hle : i ≤ n := (Finset.mem_Icc.mp hi).2
    by_cases hi1 : i = 1
    · subst i
      rw [hQfun1, hQfun2]
      exact hQP
    · by_cases hi2 : i = 2
      · subst i
        rcases hQtail_pos 3 (by omega) (by omega) with ⟨p, h3⟩
        rw [hQfun2, h3]
        exact hFtail ⟨0, by omega⟩
      · have hge3 : 3 ≤ i := by omega
        have hσb : (⟨i - 3, by omega⟩ : Fin (n - 1)).val ≤ (⟨i - 2, by omega⟩ : Fin (n - 1)).val := by
          dsimp
          omega
        have hmono := hFmono ⟨i - 3, by omega⟩ ⟨i - 2, by omega⟩ hσb
        rcases hQtail_pos i hge3 (by omega) with ⟨p1, hi3⟩
        rcases hQtail_pos (i + 1) (by omega) (by omega) with ⟨p2, hi4⟩
        rw [hi3, hi4]
        exact hmono
  · intro i hi
    simpa [H] using hHge2 i hi
  · simpa [H] using hprod_eq
  · exact hprodF

/-- `reindexPos` moves the tail slot `tailPos j` to the `σ`-permuted tail slot. -/
lemma reindexPos_tailPos {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin (n - 1)))
    (j : Fin (n - 1)) : reindexPos hn σ (tailPos hn j) = tailPos hn (σ j) := by
  apply Fin.ext
  dsimp [reindexPos]
  have hv : ((tailPos hn j : Fin (n + 1)) : ℕ) ≤ n := by
    dsimp [tailPos]
    omega
  rw [reindexVal_ge2 hn σ hv (by
    dsimp [tailPos]
    omega)]
  dsimp [tailPos]
  have hfi : (⟨(j : ℕ) + 2 - 2, by omega⟩ : Fin (n - 1)) = j := by
    apply Fin.ext
    dsimp
    omega
  rw [hfi]

/-- **M5(d)(5) second form**: sort the tail of an arbitrary LI `Fin (n+1)`-family
`F` in place (σ from `exists_norm_sorted` applied to `j ↦ F (tailPos j)`), keeping
`Q` at index 0, `P` at index 1, linear independence, degree bounds, the lower bound
`‖P‖ ≤` each tail, and now with nondecreasing tail norms. -/
theorem m5_tail_sorted {n : ℕ} (hn : 2 ≤ n) {Q P : Polynomial ℤ}
    (F : Fin (n + 1) → Polynomial ℤ)
    (hF0 : ∀ p : 0 < n + 1, F (⟨0, p⟩ : Fin (n + 1)) = Q)
    (hF1 : ∀ p : 1 < n + 1, F (⟨1, p⟩ : Fin (n + 1)) = P)
    (hdegF : ∀ i : Fin (n + 1), (F i).natDegree ≤ n)
    (hliF : LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)))
    (hPtail : ∀ j : Fin (n - 1), supN P ≤ supN (F (tailPos hn j))) :
    ∃ F' : Fin (n + 1) → Polynomial ℤ, ∃ σ : Equiv.Perm (Fin (n - 1)),
      F' (0 : Fin (n + 1)) = Q ∧ F' (1 : Fin (n + 1)) = P ∧
      (∀ i : Fin (n + 1), (F' i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (F' i).map (Int.castRingHom ℝ)) ∧
      (∀ j : Fin (n - 1), supN P ≤ supN (F' (tailPos hn j))) ∧
      (∀ j j' : Fin (n - 1), (j : ℕ) ≤ (j' : ℕ) →
        supN (F' (tailPos hn j)) ≤ supN (F' (tailPos hn j'))) ∧
      (∏ j : Fin (n - 1), supN (F' (tailPos hn j))) =
        ∏ j : Fin (n - 1), supN (F (tailPos hn j)) ∧
      F' = fun i => F (reindexPos hn σ i) := by
  classical
  rcases exists_norm_sorted (w := fun j : Fin (n - 1) => F (tailPos hn j)) with ⟨σ, hσmono, hσprod⟩
  let F' : Fin (n + 1) → Polynomial ℤ := fun i => F (reindexPos hn σ i)
  have hF'0 : F' (0 : Fin (n + 1)) = Q := by
    have p : 0 < n + 1 := by omega
    have hpos : reindexPos hn σ (0 : Fin (n + 1)) = (⟨0, p⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [reindexPos, reindexVal, p]
    dsimp [F']
    rw [hpos]
    exact hF0 p
  have hF'1 : F' (1 : Fin (n + 1)) = P := by
    have p : 1 < n + 1 := by omega
    have hpos : reindexPos hn σ (1 : Fin (n + 1)) = (⟨1, p⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [reindexPos, reindexVal, Nat.mod_eq_of_lt p]
    dsimp [F']
    rw [hpos]
    exact hF1 p
  have hprodsame : (∏ j : Fin (n - 1), supN (F' (tailPos hn j))) =
      ∏ j : Fin (n - 1), supN (F (tailPos hn j)) := by
    calc
      (∏ j : Fin (n - 1), supN (F' (tailPos hn j)))
          = ∏ j : Fin (n - 1), supN (F (tailPos hn (σ j))) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              dsimp [F']
              rw [reindexPos_tailPos hn σ j]
      _ = ∏ j : Fin (n - 1), supN (F (tailPos hn j)) := hσprod
  refine ⟨F', σ, hF'0, hF'1, ?_, ?_, ?_, ?_, hprodsame, ?_⟩
  · intro i
    dsimp [F']
    exact hdegF (reindexPos hn σ i)
  · have hmap : (fun i : Fin (n + 1) => (F' i).map (Int.castRingHom ℝ)) =
        (fun i : Fin (n + 1) => (F (reindexPos hn σ i)).map (Int.castRingHom ℝ)) := by
      funext i
      rfl
    rw [hmap]
    exact hliF.comp (reindexPos hn σ) (reindexPos_injective hn σ)
  · intro j
    dsimp [F']
    rw [reindexPos_tailPos hn σ j]
    exact hPtail (σ j)
  · intro j j' hj
    dsimp [F']
    rw [reindexPos_tailPos hn σ j, reindexPos_tailPos hn σ j']
    exact hσmono j j' hj
  · rfl

/-- **M5(d)(5) combined**: from an LI `Fin (n+1)`-family `F` (`F 0 = Q`, `F 1 = P`,
degree ≤ n, `‖Q‖ ≤ ‖P‖`, `1 < ‖P‖`, every tail norm ≥ ‖P‖) — tails in arbitrary
order — produce the final sorted ℕ-indexed family `Qfun` and exponent `x` with the
degree / LI / monotonicity / product / `x ≥ n` properties of the theorem statement. -/
theorem m5_family_final {n : ℕ} (hn : 2 ≤ n) {Q P : Polynomial ℤ}
    (F : Fin (n + 1) → Polynomial ℤ)
    (hF0 : ∀ p : 0 < n + 1, F (⟨0, p⟩ : Fin (n + 1)) = Q)
    (hF1 : ∀ p : 1 < n + 1, F (⟨1, p⟩ : Fin (n + 1)) = P)
    (hdegF : ∀ i : Fin (n + 1), (F i).natDegree ≤ n)
    (hliF : LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)))
    (hQP : supN Q ≤ supN P) (hPgt1 : 1 < supN P)
    (hPtail : ∀ j : Fin (n - 1), supN P ≤ supN (F (tailPos hn j))) :
    ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
      Qfun 1 = Q ∧ Qfun 2 = P ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) ∧
      (n : ℝ) ≤ x ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → ∃ j : Fin (n + 1), Qfun i = F j) := by
  classical
  rcases m5_tail_sorted (n := n) (hn := hn) (Q := Q) (P := P) F hF0 hF1 hdegF hliF hPtail
    with ⟨F', σ, hF'0, hF'1, hdegF', hliF', hPtail', hFmono', hprodsame, hF'def⟩
  rcases m5_sorted_family (n := n) (hn := hn) (Q := Q) (P := P) F' hF'0 hF'1 hdegF' hliF'
    hQP hPgt1 hPtail' hFmono' with ⟨Qfun, x, hq1, hq2, hdegQf, hLI, hmono1, hmono2,
      hprodEq, hprodF', hxge, hQmemF'⟩
  have hprodFin : (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) =
      supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) := by
    calc
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) =
          supN P * (∏ j : Fin (n - 1), supN (F' (tailPos hn j))) := hprodF'
      _ = supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) := by rw [hprodsame]
  have hQmem : ∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → ∃ j : Fin (n + 1), Qfun i = F j := by
    intro i hi
    rcases hQmemF' i hi with ⟨j', hQij⟩
    refine ⟨reindexPos hn σ j', ?_⟩
    rw [hQij]
    rw [hF'def]
  exact ⟨Qfun, x, hq1, hq2, hdegQf, hLI, hmono1, hmono2, hprodEq, hprodFin, hxge, hQmem⟩



open Polynomial
open scoped BigOperators

/-! ## Sec16 (M5(d) glue, IN PROGRESS): m5_li_family's output → m5_family_final

`m5_li_family` (Sec14) produces an LI family `F` with `F⟨0⟩ = Q`, `F⟨1⟩ = P`, degree
≤ n, whose remaining members (positions with value ≥ 2) are corrected tails `Ct j`.
`m5_family_final` (Sec15) needs, on top of that, the *norm* information:
`‖Q‖ ≤ ‖P‖`, `1 < ‖P‖`, and `‖P‖ ≤` every tail.  When the tails are known to come
from a `Ct` with `‖P‖ ≤ ‖Ct j‖` for all `j` (tailCorr data), this glue converts the
one interface into the other and returns the sorted final ℕ-family `Qfun` and the
exponent `x`. -/

/-- any proof `p` of `0 < n + 1` gives the same Fin element as the canonical one. -/
lemma fin0_all {n : ℕ} (p : 0 < n + 1) : (⟨0, p⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := by
  apply Fin.ext
  rfl

/-- any proof `p` of `1 < n + 1` gives the same Fin element as the canonical one. -/
lemma fin1_all {n : ℕ} (p : 1 < n + 1) : (⟨1, p⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := by
  apply Fin.ext
  rfl

/-- **M5(d) glue**: from the output of `m5_li_family` (an LI `Fin (n+1)`-family `F`
with `F⟨0⟩ = Q`, `F⟨1⟩ = P`, degree ≤ n, tails among a family `Ct` satisfying
`‖P‖ ≤ ‖Ct j‖`) plus `‖Q‖ ≤ ‖P‖` and `1 < ‖P‖`, produce the sorted final ℕ-family
`Qfun` and the exponent `x` with all the structural properties of the theorem
statement. -/
theorem m5_li_to_final {n : ℕ} (hn : 2 ≤ n) {Q P : Polynomial ℤ}
    (F : Fin (n + 1) → Polynomial ℤ) (Ct : Fin n → Polynomial ℤ)
    (hF0 : F ⟨0, by omega⟩ = Q) (hF1 : F ⟨1, by omega⟩ = P)
    (hdegF : ∀ i : Fin (n + 1), (F i).natDegree ≤ n)
    (hliF : LinearIndependent ℝ (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)))
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j)
    (hCtbig : ∀ j : Fin n, supN P ≤ supN (Ct j))
    (hQP : supN Q ≤ supN P) (hPgt1 : 1 < supN P) :
    ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
      Qfun 1 = Q ∧ Qfun 2 = P ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) =
        supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))) ∧
      (n : ℝ) ≤ x ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → ∃ j : Fin (n + 1), Qfun i = F j) := by
  classical
  have hF0' : ∀ p : 0 < n + 1, F (⟨0, p⟩ : Fin (n + 1)) = Q := by
    intro p
    rw [fin0_all p, hF0]
  have hF1' : ∀ p : 1 < n + 1, F (⟨1, p⟩ : Fin (n + 1)) = P := by
    intro p
    rw [fin1_all p, hF1]
  have hPtail : ∀ j : Fin (n - 1), supN P ≤ supN (F (tailPos hn j)) := by
    intro j
    rcases hFtailCt (tailPos hn j) (by
      dsimp [tailPos]
      omega) with ⟨k, hFjk⟩
    rw [hFjk]
    exact hCtbig k
  rcases m5_family_final (n := n) (hn := hn) (Q := Q) (P := P) F hF0' hF1' hdegF hliF hQP hPgt1
    hPtail with ⟨Qfun, x, hmain⟩
  exact ⟨Qfun, x, hmain⟩

/-- **M5(d) from the realizer**: given the value-active first-realizer `Q` at the
maximal level `sm 1(q) = e^{-n}‖P‖` (for irreducible primitive `P` with
`1 < ‖P‖`), run the whole Sec4/11/14/15 pipeline: corrected base family, corrected
tails `tailCorr P (C(succ j))`, the LI family of `m5_li_family`, the glue and the
norm sort — producing the final sorted ℕ-family `Qfun` and exponent `x`. -/
theorem m5_family_realizer {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) (q : ℝ) {Q P : Polynomial ℤ}
    (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hP : Irreducible P) (hdegP : P.natDegree ≤ n) (hprimP : P.IsPrimitive)
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hPgt1 : 1 < supN P) :
    ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
      Qfun 1 = Q ∧ Qfun 2 = P ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) => (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
      (n : ℝ) ≤ x := by
  classical
  have hval : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
  rcases corrected_family (n := n) (ξ := ξ) (q := q) Q hQ hdegQ hreal hslope
    with ⟨C, hC0, hCb, hCli⟩
  have hCdeg : ∀ i : Fin (n + 1), (C i).natDegree ≤ n := by
    intro i
    by_cases hi : i = (0 : Fin (n + 1))
    · subst i
      simpa [hC0] using hdegQ
    · exact (hCb i hi).1
  let Ct : Fin n → Polynomial ℤ := fun j => tailCorr P (C (Fin.succ j))
  have hCtdeg : ∀ j : Fin n, (Ct j).natDegree ≤ n := by
    intro j
    have hne : Fin.succ j ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
    exact tailCorr_natDegree_le (P := P) (C := C (Fin.succ j))
      (hCb (Fin.succ j) hne).1 hdegP
  have hrel : ∀ j : Fin n, ∃ lam : ℤ, C (Fin.succ j) = Ct j + Polynomial.C lam * P := by
    intro j
    by_cases h : supN (C (Fin.succ j)) ≤ supN P
    · refine ⟨-3, ?_⟩
      dsimp [Ct, tailCorr]
      rw [if_pos h]
      rw [Polynomial.C_mul', Polynomial.C_mul']
      abel
    · refine ⟨0, ?_⟩
      dsimp [Ct, tailCorr]
      rw [if_neg h]
      simp
  have hQle : supN Q ≤ Real.exp (-(n : ℝ)) * supN P :=
    realizer_norm_le_e_neg_n_supN (n := n) (ξ := ξ) (q := q) (Q := Q) (P := P) hreal hlevel
  have hPpos : 0 < supN P := lt_trans zero_lt_one hPgt1
  have hQP : supN Q ≤ supN P := by
    have he : Real.exp (-(n : ℝ)) ≤ 1 := by
      rw [Real.exp_neg]
      have hx : 1 ≤ Real.exp (n : ℝ) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by exact_mod_cast (by omega : 0 ≤ n))
      exact (inv_le_one_of_one_le₀ hx)
    calc
      supN Q ≤ Real.exp (-(n : ℝ)) * supN P := hQle
      _ ≤ supN P := by
        exact (mul_le_iff_le_one_left hPpos).mpr he
  rcases m5_li_family (n := n) (hn := by omega) hQ hdegQ hP hdegP hprimP hQle
    C Ct hC0 hCdeg hCli hCtdeg hrel with ⟨F, hF0, hF1, hliF, hdegF, hFtailCt⟩
  -- Ct members have norm ≥ ‖P‖ (they are tailCorr of C members with |pv| < |pv Q|)
  have hCtbig : ∀ j : Fin n, supN P ≤ supN (Ct j) := by
    intro j
    have hne : Fin.succ j ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
    have hdegC : (C (Fin.succ j)).natDegree ≤ n := (hCb (Fin.succ j) hne).1
    have hvalC : |pv ξ (C (Fin.succ j))| < |pv ξ Q| := (hCb (Fin.succ j) hne).2.1
    have hCne : C (Fin.succ j) ≠ 0 := li_poly_ne_zero (C := C) hCli (Fin.succ j)
    have hge : Real.exp (-(n : ℝ)) * supN P ≤ supN (C (Fin.succ j)) :=
      tail_norm_ge_level (n := n) (ξ := ξ) (q := q) (Q := Q) (C := C (Fin.succ j)) (P := P)
        hval hlevel hdegC hCne hvalC
    have hgt := tailCorr_supN_gt (n := n) (P := P) (C := C (Fin.succ j)) hge hPpos
    dsimp [Ct]
    exact le_of_lt hgt
  rcases m5_li_to_final (n := n) (hn := hn) (Q := Q) (P := P) F Ct hF0 hF1 hdegF hliF hFtailCt
    hCtbig hQP hPgt1 with ⟨Qfun, x, hmain⟩
  -- hmain is the 9-fold chain c1∧(…∧(c8∧c9)); its target drops the F-product conjunct c8
  exact ⟨Qfun, x, hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
    hmain.2.2.2.2.1, hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2.1,
    hmain.2.2.2.2.2.2.2.2.1⟩



open Polynomial
open scoped BigOperators

/-! ## Sec17 (M5(d)(6), IN PROGRESS): the value-bound engine

Goal: `|pv Q| · ‖P‖^x ≤ C` uniformly.  Inputs: the corrected family `C`
(`C 0 = Q`, `supN(C i) ≤ 3(sm+1)`, LI), the corrected tails `Ct k = tailCorr P (C(succ k))`
(`‖Ct k‖ ≤ K·‖C(succ k)‖`, `‖P‖ ≤ ‖Ct k‖`, `K = 1 + 3e^n`), and the LI family `F`
whose tail members are among the `Ct`'s.  Chain:
  |pv Q|·‖P‖·∏_j ‖F(tailPos j)‖           (this is ∏_{i=2}^{n+1} H_i of the final family)
    = |pv Q|·‖P‖·∏_j ‖Ct (g j)‖           (F-tail membership, g injective)
   ≤ |pv Q|·∏_k ‖Ct k‖                    (absorption: dropped tail ≥ ‖P‖;
                                            Commons.Algebra.BigOperators.
                                            prod_mul_le_prod_of_injective)
   ≤ |pv Q|·K^n·∏_k ‖C(succ k)‖           (tailCorr_supN_le)
   ≤ K^n · C₁                              (corrected_product_upper)
The general product lemmas `prod_le_prod_of_injective_ge_one` and
`prod_mul_le_prod_of_injective` are requested from the fleet in
Commons.Algebra.BigOperators; local copies keep this file compiling meanwhile. -/

/-- product over an injectively embedded index type ≤ product over the whole type
(factors ≥ 1). -/
lemma prod_le_prod_of_injective_ge_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι ↪ κ) (a : κ → ℝ) (h1 : ∀ k, 1 ≤ a k) :
    (∏ i : ι, a (f i)) ≤ ∏ k : κ, a k := by
  classical
  let s : Finset κ := Finset.univ.image f
  have hprod : (∏ k ∈ s, a k) = ∏ i ∈ (Finset.univ : Finset ι), a (f i) := by
    dsimp [s]
    exact Finset.prod_image (f := a) (g := f) (s := (Finset.univ : Finset ι))
      (by intro i hi j hj h; exact f.injective h)
  calc
    (∏ i ∈ (Finset.univ : Finset ι), a (f i)) ≤ ∏ k : κ, a k := by
      rw [← hprod]
      exact Finset.prod_le_prod_of_subset_of_one_le (s := s) (t := Finset.univ)
        (by simp [s]) (by intro i hi; exact le_trans zero_le_one (h1 i))
        (by intro k hk hkns; exact h1 k)

/-- a linearly independent family over a nontrivial ring is injective. -/
lemma li_injective {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {ι : Type*} {v : ι → M} (hv : LinearIndependent R v) : Function.Injective v :=
  hv.injective

/-- tail positions are injectively enumerated by `Fin (n - 1)`. -/
lemma tailPos_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (tailPos hn) := by
  intro i j hij
  apply Fin.ext
  have hv : ((tailPos hn i : Fin (n + 1)) : ℕ) = ((tailPos hn j : Fin (n + 1)) : ℕ) := by
    exact congrArg Fin.val hij
  dsimp [tailPos] at hv
  omega

/-- a tail member of an LI family `F` that lies in the range of `Ct` has a canonical
witness index `g j`; injectivity of `F` and of `Ct`-membership is captured by the
caller. -/
lemma tail_mem_range {n : ℕ} {Ct : Fin n → Polynomial ℤ} (F : Fin (n + 1) → Polynomial ℤ)
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j)
    (j : Fin (n - 1)) (hn : 2 ≤ n) : ∃ k : Fin n, F (tailPos hn j) = Ct k :=
  hFtailCt (tailPos hn j) (by
    dsimp [tailPos]
    omega)

/-- absorption: `g : Fin (n-1) → Fin n` injective, `b ≤ a k`, `1 ≤ a k` for all `k`
⟹ `b·∏_j a(g j) ≤ ∏_k a k`. -/
lemma prod_absorb_pred {n : ℕ} (hn : 1 ≤ n) (g : Fin (n - 1) → Fin n)
    (hginj : Function.Injective g) (a : Fin n → ℝ)
    (ha : ∀ k : Fin n, 1 ≤ a k) {b : ℝ} (hb : ∀ k : Fin n, b ≤ a k) :
    b * (∏ j : Fin (n - 1), a (g j)) ≤ ∏ k : Fin n, a k := by
  classical
  let s : Finset (Fin n) := Finset.univ.image g
  have hs : s.card = n - 1 := by
    dsimp [s]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_fin]
    · exact hginj
  have hscompl : sᶜ.card = 1 := by
    rw [Finset.card_compl, hs, Fintype.card_fin]
    omega
  rcases Finset.card_eq_one.mp hscompl with ⟨t, htcompl⟩
  have htnots : t ∉ s := by
    have htm : t ∈ sᶜ := by
      rw [htcompl]
      simp
    exact Finset.mem_compl.mp htm
  have hcover : insert t s = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem htnots, hs, Fintype.card_fin]
    omega
  have hprod : (∏ x ∈ s, a x) = ∏ j : Fin (n - 1), a (g j) := by
    dsimp [s]
    rw [Finset.prod_image]
    · intro x hx y hy hxy
      exact hginj hxy
  have hP : 0 ≤ (∏ j : Fin (n - 1), a (g j)) := by
    exact Finset.prod_nonneg (fun j hj => le_trans zero_le_one (ha (g j)))
  calc
    b * (∏ j : Fin (n - 1), a (g j)) ≤ a t * (∏ j : Fin (n - 1), a (g j)) := by
      exact mul_le_mul_of_nonneg_right (hb t) hP
    _ = a t * (∏ x ∈ s, a x) := by
      rw [← hprod]
    _ = ∏ x ∈ insert t s, a x := by
      rw [Finset.prod_insert htnots]
    _ = ∏ k : Fin n, a k := by
      rw [hcover]

/-- the `Ct`-witness index map of the tail members of an LI family is injective. -/
lemma tail_witness_inj {n : ℕ} (hn : 2 ≤ n) (F : Fin (n + 1) → Polynomial ℤ)
    (hFinj : Function.Injective F) (Ct : Fin n → Polynomial ℤ)
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j) :
    ∃ g : Fin (n - 1) → Fin n,
      (∀ j : Fin (n - 1), F (tailPos hn j) = Ct (g j)) ∧ Function.Injective g := by
  classical
  let g : Fin (n - 1) → Fin n := fun j => Classical.choose (tail_mem_range F hFtailCt j hn)
  have hspec : ∀ j : Fin (n - 1), F (tailPos hn j) = Ct (g j) := by
    intro j
    dsimp [g]
    exact Classical.choose_spec (tail_mem_range F hFtailCt j hn)
  refine ⟨g, hspec, ?_⟩
  intro j j' hgj
  apply Fin.ext
  have hFj : F (tailPos hn j) = F (tailPos hn j') := by
    rw [hspec j, hspec j', hgj]
  have hpos : tailPos hn j = tailPos hn j' := hFinj hFj
  have hval : ((tailPos hn j : Fin (n + 1)) : ℕ) = ((tailPos hn j' : Fin (n + 1)) : ℕ) := by
    exact congrArg Fin.val hpos
  dsimp [tailPos] at hval
  omega

/-- **M5(d)(6) core**: `|pv Q|·‖P‖·∏_j ‖F(tailPos j)‖ ≤ C` with a constant
`C = (1+3e^n)^n·C₁(n,ξ)` depending only on `n` and `ξ`.  Here `F` is the LI family
from the construction (tails among the corrected `Ct`'s) — this product is exactly
`∏_{i=2}^{n+1}` of the final family's norms (sorting preserves the product). -/
theorem pvQ_mul_prod_tail_bound {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) (q : ℝ) (hq : Real.log 2 ≤ q)
    {Q P : Polynomial ℤ}
    (hPne : P ≠ 0) (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (C : Fin (n + 1) → Polynomial ℤ) (hC0 : C 0 = Q)
    (hCsup : ∀ i : Fin (n + 1), i ≠ 0 → supN (C i) ≤ 3 * (sm n ξ q (i.val + 1) + 1))
    (Ct : Fin n → Polynomial ℤ)
    (hCtle : ∀ k : Fin n, supN (Ct k) ≤ (1 + 3 * Real.exp (n : ℝ)) * supN (C (Fin.succ k)))
    (hCtbig : ∀ k : Fin n, supN P ≤ supN (Ct k))
    (F : Fin (n + 1) → Polynomial ℤ)
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j)
    (hFinj : Function.Injective F) :
    ∃ Cb : ℝ, 0 < Cb ∧
      |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤ Cb := by
  classical
  rcases corrected_product_upper (n := n) (by omega : 1 ≤ n) ξ with ⟨C1, hC1pos, hC1⟩
  let K : ℝ := 1 + 3 * Real.exp (n : ℝ)
  let Cb : ℝ := K ^ n * C1
  refine ⟨Cb, ?_, ?_⟩
  · dsimp [Cb, K]
    positivity
  · have hK0 : 0 ≤ K := by
      dsimp [K]
      positivity
    have hAbs : 0 ≤ |pv ξ Q| := abs_nonneg _
    have hC1 : |pv ξ Q| * (∏ k : Fin n, supN (C (Fin.succ k))) ≤ C1 :=
      hC1 q hq Q hQ hdegQ hreal hslope C hC0 hCsup
    rcases tail_witness_inj (n := n) hn F hFinj Ct hFtailCt with ⟨g, hspec, hginj⟩
    have hprodeq : (∏ j : Fin (n - 1), supN (F (tailPos hn j))) =
        ∏ j : Fin (n - 1), supN (Ct (g j)) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      exact congrArg supN (hspec j)
    have ha : ∀ k : Fin n, 1 ≤ supN (Ct k) := by
      intro k
      exact le_trans (supN_one_le hPne) (hCtbig k)
    have habsorb : supN P * (∏ j : Fin (n - 1), supN (Ct (g j))) ≤
        ∏ k : Fin n, supN (Ct k) := by
      exact prod_absorb_pred (n := n) (by omega : 1 ≤ n) g hginj (fun k => supN (Ct k)) ha
        (by intro k; exact hCtbig k)
    have hstep1 : |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤
        |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := by
      calc
        |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))))
            = |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (Ct (g j)))) := by rw [hprodeq]
        _ ≤ |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := by
            exact mul_le_mul_of_nonneg_left habsorb hAbs
    have hstep2 : |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) ≤
        |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) := by
      have hle : (∏ k : Fin n, supN (Ct k)) ≤
          K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))) := by
        calc
          (∏ k : Fin n, supN (Ct k)) ≤ ∏ k : Fin n, K * supN (C (Fin.succ k)) := by
            refine Finset.prod_le_prod (s := Finset.univ) ?_ ?_
            · intro i hi
              exact supN_nonneg (Ct i)
            · intro i hi
              have hle' := hCtle i
              dsimp [K] at hle' ⊢
              exact hle'
          _ = K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))) := by
            exact prod_mul_const K (fun k : Fin n => supN (C (Fin.succ k)))
      exact mul_le_mul_of_nonneg_left hle hAbs
    have hstep3 : |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) ≤ K ^ n * C1 := by
      calc
        |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))))
            = K ^ n * (|pv ξ Q| * (∏ k : Fin n, supN (C (Fin.succ k)))) := by ring
        _ ≤ K ^ n * C1 := by
            exact mul_le_mul_of_nonneg_left hC1 (pow_nonneg hK0 n)
    calc
      |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤
          |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := hstep1
      _ ≤ |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) := hstep2
      _ ≤ K ^ n * C1 := hstep3
      _ = Cb := by dsimp [Cb]

/-- **(a) of the hB chain**: with the engine bound and the product identity
`∏_{i∈Icc 2 (n+1)} H_i = ‖P‖^x`, one has `|pv Q| ≤ C·‖P‖^{-x}` uniformly
(`C = (1+3e^n)^n·C₁(n,ξ)`). -/
theorem pvQ_le_H2_neg_x {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) (q : ℝ) (hq : Real.log 2 ≤ q)
    {Q P : Polynomial ℤ}
    (hPne : P ≠ 0) (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (C : Fin (n + 1) → Polynomial ℤ) (hC0 : C 0 = Q)
    (hCsup : ∀ i : Fin (n + 1), i ≠ 0 → supN (C i) ≤ 3 * (sm n ξ q (i.val + 1) + 1))
    (Ct : Fin n → Polynomial ℤ)
    (hCtle : ∀ k : Fin n, supN (Ct k) ≤ (1 + 3 * Real.exp (n : ℝ)) * supN (C (Fin.succ k)))
    (hCtbig : ∀ k : Fin n, supN P ≤ supN (Ct k))
    (F : Fin (n + 1) → Polynomial ℤ)
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j)
    (hFinj : Function.Injective F)
    (Hfun : ℕ → ℝ) (hH2 : Hfun 2 = supN P)
    (hprod_id : (∏ i ∈ Finset.Icc 2 (n + 1), Hfun i) =
      supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))))
    {x : ℝ} (hprod_x : (∏ i ∈ Finset.Icc 2 (n + 1), Hfun i) = supN P ^ x) :
    ∃ C : ℝ, 0 < C ∧ |pv ξ Q| ≤ C * (supN P) ^ (-x) := by
  classical
  rcases pvQ_mul_prod_tail_bound (n := n) (hn := hn) (ξ := ξ) (q := q) (hq := hq) (Q := Q) (P := P)
    hPne hQ hdegQ hreal hslope C hC0 hCsup Ct hCtle hCtbig F hFtailCt hFinj
    with ⟨Cb, hCbpos, hCb⟩
  -- hCb : |pv Q|·(‖P‖·∏_j ‖F(tailPos)‖) ≤ Cb
  let A : ℝ := supN P ^ x
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (supN_pos_of_ne_zero hPne) x
  have hEng : |pv ξ Q| * A ≤ Cb := by
    dsimp [A]
    rw [← hprod_x, hprod_id]
    exact hCb
  have hinv : A⁻¹ = (supN P) ^ (-x) := by
    dsimp [A]
    rw [Real.rpow_neg (supN_nonneg P) x]
  refine ⟨Cb, hCbpos, ?_⟩
  calc
    |pv ξ Q| = |pv ξ Q| * (A * A⁻¹) := by
      field_simp [ne_of_gt hApos]
    _ ≤ Cb * A⁻¹ := by
      -- |pvQ|·(A·A⁻¹) ≤ Cb·A⁻¹ from |pvQ|·A ≤ Cb : |pvQ| ≤ Cb·A^{-1}... do stepwise:
      have hm : |pv ξ Q| * A * A⁻¹ ≤ Cb * A⁻¹ := by
        exact mul_le_mul_of_nonneg_right hEng (inv_nonneg.mpr (le_of_lt hApos))
      calc
        |pv ξ Q| * (A * A⁻¹) = |pv ξ Q| * A * A⁻¹ := by ring
        _ ≤ Cb * A⁻¹ := hm
    _ = Cb * (supN P) ^ (-x) := by rw [← hinv]

/-- local copy (also requested from the fleet): `t^{-x} ≤ t^{-(n:ℝ)}` for `t ≥ 1`, `n ≤ x`. -/
lemma rpow_neg_le_of_exponent_le {t : ℝ} (ht1 : 1 ≤ t) {n : ℕ} {x : ℝ} (hxn : (n : ℝ) ≤ x) :
    t ^ (-x) ≤ t ^ (-(n : ℝ)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0]
  exact Real.exp_le_exp.mpr (by
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    nlinarith)

/-- local copy (also requested from the fleet): `C·t^{-(n:ℝ)} ≤ m` once `t` is past a
uniform threshold. -/
lemma rpow_neg_nat_small_of_large {C m : ℝ} (hC : 0 < C) (hm : 0 < m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → C * t ^ (-(n : ℝ)) ≤ m := by
  let T : ℝ := max 1 ((C / m) ^ (1 / (n : ℝ)))
  refine ⟨T, ?_, ?_⟩
  · dsimp [T]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro t ht
    have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
    have htT : ((C / m) ^ (1 / (n : ℝ))) ≤ t := le_trans (le_max_right _ _) ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hCm : 0 < C / m := div_pos hC hm
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hcancel : (1 / (n : ℝ)) * (n : ℝ) = (1 : ℝ) := by field_simp [hn0]
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ((C / m) ^ (1 / (n : ℝ)))) htT
      (by positivity : 0 ≤ (n : ℝ))
    have heq : ((C / m) ^ (1 / (n : ℝ))) ^ (n : ℝ) = C / m := by
      rw [← Real.rpow_mul hCm.le, hcancel, Real.rpow_one]
    have hgeq : C / m ≤ t ^ (n : ℝ) := by
      calc
        C / m = ((C / m) ^ (1 / (n : ℝ))) ^ (n : ℝ) := heq.symm
        _ ≤ t ^ (n : ℝ) := hpow
    have h1 : t ^ (-(n : ℝ)) = (t ^ (n : ℝ))⁻¹ := Real.rpow_neg ht0.le (n : ℝ)
    have htpow : 0 < t ^ (n : ℝ) := Real.rpow_pos_of_pos ht0 (n : ℝ)
    have hinv : (t ^ (n : ℝ))⁻¹ ≤ (C / m)⁻¹ := (inv_le_inv₀ htpow hCm).mpr hgeq
    calc
      C * t ^ (-(n : ℝ)) = C * (t ^ (n : ℝ))⁻¹ := by rw [h1]
      _ ≤ C * (C / m)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv hC.le
      _ = m := by
        field_simp [ne_of_gt hm]

/-- **(b) of the hB chain**: from the decay bound `|pv Q| ≤ C·‖P‖^{-x}` with
`x ≥ n ≥ 2`, transcendental ξ forces `‖Q‖ ≥ HE` once `‖P‖` is beyond a uniform
threshold (pv_lower_uniform + the `‖P‖^{-n}`-decay). -/
theorem realizer_norm_ge_HE {n : ℕ} (hn : 2 ≤ n) {ξ : ℝ} (hξ : Transcendental ℚ ξ)
    {Q P : Polynomial ℤ} (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n) (hPne : P ≠ 0)
    {C : ℝ} (hC0 : 0 < C) {x : ℝ} (hxn : (n : ℝ) ≤ x)
    (hval : |pv ξ Q| ≤ C * (supN P) ^ (-x)) (HE : ℝ) :
    ∃ T : ℝ, 0 < T ∧ (T ≤ supN P → HE ≤ supN Q) := by
  classical
  rcases pv_lower_uniform (n := n) (ξ := ξ) hξ HE with ⟨m, hm0, hm⟩
  rcases rpow_neg_nat_small_of_large (C := C) (m := m / 2) hC0
    (by positivity : 0 < m / 2) (n := n) (by omega : 1 ≤ n) with ⟨T0, hT0pos, hsmall⟩
  let T : ℝ := max T0 1
  refine ⟨T, ?_, ?_⟩
  · dsimp [T]
    exact lt_of_lt_of_le hT0pos (le_max_left T0 1)
  · intro hbigT
    by_contra hnot
    have hleQ : supN Q ≤ HE := le_of_lt (lt_of_not_ge hnot)
    have hT0le : T0 ≤ supN P := le_trans (by dsimp [T]; exact le_max_left T0 1) hbigT
    have h1le : 1 ≤ supN P := le_trans (by dsimp [T]; exact le_max_right T0 1) hbigT
    have hmQ : m ≤ |pv ξ Q| := hm Q hQ hdegQ hleQ
    have hdecay : (supN P) ^ (-x) ≤ (supN P) ^ (-(n : ℝ)) :=
      rpow_neg_le_of_exponent_le (t := supN P) h1le hxn
    have hsmall' : C * (supN P) ^ (-(n : ℝ)) ≤ m / 2 := hsmall (supN P) hT0le
    have hchain : |pv ξ Q| ≤ m / 2 := by
      calc
        |pv ξ Q| ≤ C * (supN P) ^ (-x) := hval
        _ ≤ C * (supN P) ^ (-(n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hdecay hC0.le
        _ ≤ m / 2 := hsmall'
    nlinarith

/-- ε-absorption: `H^{x−w2} ≤ C′` and `C′^{1/eps} ≤ H` (`H > 1`, `eps > 0`, `C′ > 0`)
⟹ `x ≤ w2 + eps`. -/
lemma x_le_add_eps {x w2 eps H C' : ℝ} (hH : 1 < H) (heps : 0 < eps) (hC : 0 < C')
    (hpow : H ^ (x - w2) ≤ C') (hbig : C' ^ (1 / eps) ≤ H) : x ≤ w2 + eps := by
  have hH0 : 0 < H := lt_trans zero_lt_one hH
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hcancel : (1 / eps) * eps = (1 : ℝ) := by
    have heps0 : eps ≠ 0 := ne_of_gt heps
    field_simp [heps0]
  have hlogpow : (x - w2) * Real.log H ≤ Real.log C' := by
    have hle : Real.log (H ^ (x - w2)) ≤ Real.log C' :=
      Real.log_le_log (Real.rpow_pos_of_pos hH0 (x - w2)) hpow
    rwa [Real.log_rpow hH0] at hle
  have hpow2 : C' ≤ H ^ eps := by
    have hle := Real.rpow_le_rpow (Real.rpow_nonneg hC.le (1 / eps)) hbig heps.le
    calc
      C' = (C' ^ (1 / eps)) ^ eps := by
        rw [← Real.rpow_mul hC.le, hcancel, Real.rpow_one]
      _ ≤ H ^ eps := hle
  have hlogC : Real.log C' ≤ eps * Real.log H := by
    have hle : Real.log C' ≤ Real.log (H ^ eps) := Real.log_le_log hC hpow2
    rwa [Real.log_rpow hH0] at hle
  have h1 : x - w2 ≤ Real.log C' / Real.log H := by
    exact (le_div_iff₀ hlogH).mpr hlogpow
  have h2 : Real.log C' / Real.log H ≤ eps := by
    exact (div_le_iff₀ hlogH).mpr hlogC
  linarith

/-- `t ↦ t^z` is decreasing for `z < 0` on positive bases. -/
lemma rpow_neg_anti {a b z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hz : z < 0) : b ^ z ≤ a ^ z := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hz' : 0 < -z := by linarith
  have hpow : a ^ (-z) ≤ b ^ (-z) := Real.rpow_le_rpow ha.le hab hz'.le
  rw [show z = -(-z) by ring]
  rw [Real.rpow_neg hb0.le (-z), Real.rpow_neg ha.le (-z)]
  have hbz : 0 < b ^ (-z) := Real.rpow_pos_of_pos hb0 (-z)
  have haz : 0 < a ^ (-z) := Real.rpow_pos_of_pos ha (-z)
  exact (inv_le_inv₀ hbz haz).mpr hpow

/-- **(c) of the hB chain**: hB applied to the realizer `Q` (`‖Q‖^{-w2} ≤ |pv Q|`),
`‖Q‖ ≤ ‖P‖`, the decay `|pv Q| ≤ C·‖P‖^{-x}`, and the large-`‖P‖` threshold
`C^{1/eps} ≤ ‖P‖` give `x ≤ w2 + eps`. -/
theorem x_le_w2_add_eps_of_hB {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) {w2 eps : ℝ}
    (hw2 : 0 < w2) (heps : 0 < eps) {Q P : Polynomial ℤ} {x : ℝ} {C : ℝ}
    (hC0 : 0 < C) (hQ : Q ≠ 0) (hPne : P ≠ 0) (hPgt1 : 1 < supN P)
    (hQle : supN Q ≤ supN P)
    (hBQ : (supN Q) ^ (-w2) ≤ |pv ξ Q|)
    (hval : |pv ξ Q| ≤ C * (supN P) ^ (-x))
    (hbig : C ^ (1 / eps) ≤ supN P) :
    x ≤ w2 + eps := by
  classical
  let t : ℝ := supN P
  have ht0 : 0 < t := by
    dsimp [t]
    exact supN_pos_of_ne_zero hPne
  have hQt0 : 0 < supN Q := supN_pos_of_ne_zero hQ
  have hneg : (-w2 : ℝ) < 0 := by linarith
  have hP_ge : t ^ (-w2) ≤ (supN Q) ^ (-w2) := by
    dsimp [t]
    exact rpow_neg_anti (a := supN Q) (b := supN P) hQt0 hQle hneg
  have hchain : t ^ (-w2) ≤ C * t ^ (-x) := by
    dsimp [t]
    exact le_trans hP_ge (le_trans hBQ hval)
  have hL : t ^ x * t ^ (-w2) = t ^ (x - w2) := by
    rw [show x - w2 = x + (-w2) by ring]
    rw [Real.rpow_add ht0 x (-w2)]
  have h1 : t ^ x * t ^ (-x) = 1 := by
    rw [← Real.rpow_add ht0 x (-x)]
    rw [show x + (-x) = 0 by ring, Real.rpow_zero]
  have hR : t ^ x * (C * t ^ (-x)) = C := by
    calc
      t ^ x * (C * t ^ (-x)) = C * (t ^ x * t ^ (-x)) := by ring
      _ = C * 1 := by rw [h1]
      _ = C := by ring
  have hpow : t ^ (x - w2) ≤ C := by
    have hm := mul_le_mul_of_nonneg_left hchain (le_of_lt (Real.rpow_pos_of_pos ht0 x))
    calc
      t ^ (x - w2) = t ^ x * t ^ (-w2) := hL.symm
      _ ≤ t ^ x * (C * t ^ (-x)) := hm
      _ = C := hR
  dsimp [t] at hpow
  exact x_le_add_eps (x := x) (w2 := w2) (eps := eps) (H := supN P) (C' := C)
    hPgt1 heps hC0 (by simpa using hpow) hbig

/-- every member of the construction family `F` (Q at index 0, P at index 1, tails
among a family `Ct` with `|pv(Ct j)| ≤ |pv Q| + 3|pv P|`) has value bounded by
`4·max(|pv Q|, |pv P|)`. -/
theorem member_value_le {n : ℕ} (hn : 2 ≤ n) {ξ : ℝ} {Q P : Polynomial ℤ}
    (F : Fin (n + 1) → Polynomial ℤ)
    (hF0 : ∀ p : 0 < n + 1, F (⟨0, p⟩ : Fin (n + 1)) = Q)
    (hF1 : ∀ p : 1 < n + 1, F (⟨1, p⟩ : Fin (n + 1)) = P)
    (Ct : Fin n → Polynomial ℤ)
    (hFtailCt : ∀ i : Fin (n + 1), 2 ≤ (i : ℕ) → ∃ j : Fin n, F i = Ct j)
    (hCtval : ∀ j : Fin n, |pv ξ (Ct j)| ≤ |pv ξ Q| + 3 * |pv ξ P|) :
    ∀ i : Fin (n + 1), |pv ξ (F i)| ≤ 4 * max (|pv ξ Q|) (|pv ξ P|) := by
  intro i
  have hmx : |pv ξ Q| ≤ max (|pv ξ Q|) (|pv ξ P|) := le_max_left _ _
  have hmx' : |pv ξ P| ≤ max (|pv ξ Q|) (|pv ξ P|) := le_max_right _ _
  have hmax0 : 0 ≤ max (|pv ξ Q|) (|pv ξ P|) :=
    le_trans (abs_nonneg (pv ξ Q)) (le_max_left _ _)
  have h4 : |pv ξ Q| + 3 * |pv ξ P| ≤ 4 * max (|pv ξ Q|) (|pv ξ P|) := by
    have h3 : 3 * |pv ξ P| ≤ 3 * max (|pv ξ Q|) (|pv ξ P|) :=
      mul_le_mul_of_nonneg_left hmx' (by norm_num)
    calc
      |pv ξ Q| + 3 * |pv ξ P| ≤ max (|pv ξ Q|) (|pv ξ P|) + 3 * max (|pv ξ Q|) (|pv ξ P|) := add_le_add hmx h3
      _ = 4 * max (|pv ξ Q|) (|pv ξ P|) := by ring
  by_cases hi0 : (i : ℕ) = 0
  · let p : 0 < n + 1 := by simpa [hi0] using i.2
    have hi : i = (⟨0, p⟩ : Fin (n + 1)) := by
      apply Fin.ext
      exact hi0
    rw [hi, hF0 p]
    calc
      |pv ξ Q| ≤ max (|pv ξ Q|) (|pv ξ P|) := hmx
      _ ≤ 4 * max (|pv ξ Q|) (|pv ξ P|) := by nlinarith [hmax0]
  · by_cases hi1 : (i : ℕ) = 1
    · let p : 1 < n + 1 := by simpa [hi1] using i.2
      have hi : i = (⟨1, p⟩ : Fin (n + 1)) := by
        apply Fin.ext
        exact hi1
      rw [hi, hF1 p]
      calc
        |pv ξ P| ≤ max (|pv ξ Q|) (|pv ξ P|) := hmx'
        _ ≤ 4 * max (|pv ξ Q|) (|pv ξ P|) := by nlinarith [hmax0]
    · have hge : 2 ≤ (i : ℕ) := by omega
      rcases hFtailCt i hge with ⟨j, hFij⟩
      rw [hFij]
      exact le_trans (hCtval j) h4

/-- `t ↦ t^y` is nondecreasing in `y` for base `t ≥ 1`. -/
lemma rpow_mono_exp {t : ℝ} (ht1 : 1 ≤ t) {y1 y2 : ℝ} (hy : y1 ≤ y2) :
    t ^ y1 ≤ t ^ y2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0]
  exact Real.exp_le_exp.mpr (by
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    nlinarith)

/-- the `c·H₂^{-x+eps}` bookkeeping: if `v ≤ t^{-(w2−eps)}`, `1 ≤ t`, and the
uniform bound `t^{x−w2} ≤ C` holds, then `v ≤ C·t^{-x+eps}`. -/
lemma value_le_rpow_eps {v t : ℝ} {w2 eps x : ℝ} {C : ℝ}
    (hval : v ≤ t ^ (-(w2 - eps))) (hv0 : 0 ≤ v)
    (ht1 : 1 ≤ t) (hpow : t ^ (x - w2) ≤ C) (hC0 : 0 ≤ C) :
    v ≤ C * t ^ (-x + eps) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hmul := Real.rpow_add htpos (-x + eps) (x - w2)
  -- t^{(-x+eps)+(x-w2)} = t^{-x+eps}·t^{x-w2}: exponent = -(w2-eps)
  have he : (-x + eps) + (x - w2) = -(w2 - eps) := by ring
  calc
    v ≤ t ^ (-(w2 - eps)) := hval
    _ = t ^ ((-x + eps) + (x - w2)) := by rw [he]
    _ = t ^ (-x + eps) * t ^ (x - w2) := hmul
    _ ≤ t ^ (-x + eps) * C := by
      have htpos2 : 0 ≤ t ^ (-x + eps) := Real.rpow_nonneg htpos.le (-x + eps)
      exact mul_le_mul_of_nonneg_left hpow htpos2
    _ = C * t ^ (-x + eps) := by ring

/-- `|pv Q| ≤ C·t^{-x}` forces `|pv Q| ≤ C·t^{-x+eps}` (`t ≥ 1`, `eps ≥ 0`). -/
lemma pv_le_rpow_eps {t v : ℝ} (hv0 : 0 ≤ v) (ht1 : 1 ≤ t) {x eps C : ℝ}
    (hC0 : 0 ≤ C) (heps : 0 ≤ eps) (hval : v ≤ C * t ^ (-x)) :
    v ≤ C * t ^ (-x + eps) := by
  have hm : t ^ (-x) ≤ t ^ (-x + eps) := rpow_mono_exp ht1 (by linarith)
  calc
    v ≤ C * t ^ (-x) := hval
    _ ≤ C * t ^ (-x + eps) := mul_le_mul_of_nonneg_left hm hC0



open Polynomial
open scoped BigOperators

/-! ## Sec18 (M5(d)(6) master): the value-bound family

Given the level data (`q ≥ log 2`, value-active first-realizer `Q`, irreducible
primitive `P`, `sm 1(q) = e^{-n}·‖P‖`), the hB lower bound applied to `Q`, the
hA-derived product constant `C1` (with its universal property), and the threshold
`(K^n·C1)^{1/eps} ≤ ‖P‖` (`K = 1 + 3e^n`), this file produces the final sorted
ℕ-indexed family `Qfun` and the exponent `x` with every structural property of the
theorem statement AND the uniform value bounds
`|pv(Qfun i)| ≤ (4·K^n·C1)·‖P‖^{-x+eps}` on `Icc 1 (n+1)`, plus `n ≤ x ≤ w2 + eps`. -/

/-- **M5(d)(6) master**.  (See module header.) -/
theorem m5_value_family {n : ℕ} (hn : 2 ≤ n) (ξ : ℝ) {q : ℝ} (hq : Real.log 2 ≤ q)
    {Q P : Polynomial ℤ}
    (hQnz : Q ≠ 0) (hdegQ : Q.natDegree ≤ n)
    (hreal : Tq ξ q Q = sm n ξ q 1)
    (hslope : supN Q ≤ Real.exp q * |pv ξ Q|)
    (hP : Irreducible P) (hdegP : P.natDegree ≤ n) (hPprim : P.IsPrimitive)
    (hlevel : sm n ξ q 1 = Real.exp (-(n : ℝ)) * supN P)
    (hPgt1 : 1 < supN P)
    {eps w2 : ℝ} (heps0 : 0 < eps) (hw2 : 0 < w2)
    (hvalP : |pv ξ P| ≤ supN P ^ (-(w2 - eps)))
    (hBQ : (supN Q) ^ (-w2) ≤ |pv ξ Q|)
    {C1 : ℝ} (hC1pos : 0 < C1)
    (hC1main : ∀ (q0 : ℝ), Real.log 2 ≤ q0 → ∀ (Q0 : Polynomial ℤ), Q0 ≠ 0 →
      Q0.natDegree ≤ n → Tq ξ q0 Q0 = sm n ξ q0 1 →
      supN Q0 ≤ Real.exp q0 * |pv ξ Q0| →
      ∀ C0 : Fin (n + 1) → Polynomial ℤ, C0 0 = Q0 →
      (∀ i : Fin (n + 1), i ≠ 0 →
        supN (C0 i) ≤ 3 * (sm n ξ q0 (i.val + 1) + 1)) →
      |pv ξ Q0| * (∏ j : Fin n, supN (C0 (Fin.succ j))) ≤ C1)
    (hbig : ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1) ^ (1 / eps) ≤ supN P) :
    ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
      Qfun 1 = Q ∧ Qfun 2 = P ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
      LinearIndependent ℝ (fun i : Fin (n + 1) =>
        (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
      (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
      (n : ℝ) ≤ x ∧ x ≤ w2 + eps ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) →
        |pv ξ (Qfun i)| ≤ (4 * ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1)) *
          ((supN (Qfun 2)) ^ (-x + eps))) := by
  classical
  let K : ℝ := 1 + 3 * Real.exp (n : ℝ)
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hK0 : 0 ≤ K := le_of_lt hKpos
  let Cb : ℝ := K ^ n * C1
  have hCbpos : 0 < Cb := by
    dsimp [Cb]
    positivity
  have hCb0 : 0 ≤ Cb := le_of_lt hCbpos
  have hCbeq : Cb = (1 + 3 * Real.exp (n : ℝ)) ^ n * C1 := by
    dsimp [Cb, K]
  have hval : Real.exp q * |pv ξ Q| = sm n ξ q 1 := value_active_eq (Q := Q) hslope hreal
  have hPne : P ≠ 0 := irreducible_ne_zero hP
  have hPpos : 0 < supN P := supN_pos_of_ne_zero hPne
  -- the corrected base family
  rcases corrected_family (n := n) (ξ := ξ) (q := q) Q hQnz hdegQ hreal hslope
    with ⟨C, hC0, hCbnd, hCli⟩
  have hCdeg : ∀ i : Fin (n + 1), (C i).natDegree ≤ n := by
    intro i
    by_cases hi : i = (0 : Fin (n + 1))
    · subst i
      simpa [hC0] using hdegQ
    · exact (hCbnd i hi).1
  have hCsup : ∀ i : Fin (n + 1), i ≠ 0 →
      supN (C i) ≤ 3 * (sm n ξ q (i.val + 1) + 1) := by
    intro i hi
    exact (hCbnd i hi).2.2
  -- corrected tails
  let Ct : Fin n → Polynomial ℤ := fun j => tailCorr P (C (Fin.succ j))
  have hCtdeg : ∀ j : Fin n, (Ct j).natDegree ≤ n := by
    intro j
    have hne : Fin.succ j ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
    exact tailCorr_natDegree_le (P := P) (C := C (Fin.succ j))
      (hCbnd (Fin.succ j) hne).1 hdegP
  have hrel : ∀ j : Fin n, ∃ lam : ℤ, C (Fin.succ j) = Ct j + Polynomial.C lam * P := by
    intro j
    by_cases h : supN (C (Fin.succ j)) ≤ supN P
    · refine ⟨-3, ?_⟩
      dsimp [Ct, tailCorr]
      rw [if_pos h]
      rw [Polynomial.C_mul', Polynomial.C_mul']
      abel
    · refine ⟨0, ?_⟩
      dsimp [Ct, tailCorr]
      rw [if_neg h]
      simp
  have hQle : supN Q ≤ Real.exp (-(n : ℝ)) * supN P :=
    realizer_norm_le_e_neg_n_supN (n := n) (ξ := ξ) (q := q) (Q := Q) (P := P) hreal hlevel
  have hQP : supN Q ≤ supN P := by
    have he : Real.exp (-(n : ℝ)) ≤ 1 := by
      rw [Real.exp_neg]
      have hx : 1 ≤ Real.exp (n : ℝ) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by exact_mod_cast (by omega : 0 ≤ n))
      exact (inv_le_one_of_one_le₀ hx)
    calc
      supN Q ≤ Real.exp (-(n : ℝ)) * supN P := hQle
      _ ≤ supN P := by
        exact (mul_le_iff_le_one_left hPpos).mpr he
  have hQt0 : 0 < supN Q := supN_pos_of_ne_zero hQnz
  -- each Ct member has norm ≥ ‖P‖ (level + value-lower bound on C members)
  have hCtbig : ∀ k : Fin n, supN P ≤ supN (Ct k) := by
    intro k
    have hne : Fin.succ k ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero k
    have hdegC : (C (Fin.succ k)).natDegree ≤ n := (hCbnd (Fin.succ k) hne).1
    have hvalC : |pv ξ (C (Fin.succ k))| < |pv ξ Q| := (hCbnd (Fin.succ k) hne).2.1
    have hCne : C (Fin.succ k) ≠ 0 := li_poly_ne_zero (C := C) hCli (Fin.succ k)
    have hge : Real.exp (-(n : ℝ)) * supN P ≤ supN (C (Fin.succ k)) :=
      tail_norm_ge_level (n := n) (ξ := ξ) (q := q) (Q := Q) (C := C (Fin.succ k)) (P := P)
        hval hlevel hdegC hCne hvalC
    have hgt := tailCorr_supN_gt (n := n) (P := P) (C := C (Fin.succ k)) hge hPpos
    dsimp [Ct]
    exact le_of_lt hgt
  have hCtle : ∀ k : Fin n, supN (Ct k) ≤ K * supN (C (Fin.succ k)) := by
    intro k
    have hne : Fin.succ k ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero k
    have hdegC : (C (Fin.succ k)).natDegree ≤ n := (hCbnd (Fin.succ k) hne).1
    have hvalC : |pv ξ (C (Fin.succ k))| < |pv ξ Q| := (hCbnd (Fin.succ k) hne).2.1
    have hCne : C (Fin.succ k) ≠ 0 := li_poly_ne_zero (C := C) hCli (Fin.succ k)
    have hge : Real.exp (-(n : ℝ)) * supN P ≤ supN (C (Fin.succ k)) :=
      tail_norm_ge_level (n := n) (ξ := ξ) (q := q) (Q := Q) (C := C (Fin.succ k)) (P := P)
        hval hlevel hdegC hCne hvalC
    have hle := tailCorr_supN_le (n := n) (P := P) (C := C (Fin.succ k)) hge
    dsimp [Ct, K]
    exact hle
  have hCtval : ∀ k : Fin n, |pv ξ (Ct k)| ≤ |pv ξ Q| + 3 * |pv ξ P| := by
    intro k
    have hne : Fin.succ k ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero k
    have hdegC : (C (Fin.succ k)).natDegree ≤ n := (hCbnd (Fin.succ k) hne).1
    have hvalC : |pv ξ (C (Fin.succ k))| < |pv ξ Q| := (hCbnd (Fin.succ k) hne).2.1
    have hle := tailCorr_value_le (ξ := ξ) (P := P) (C := C (Fin.succ k))
    dsimp [Ct]
    have h3 : 0 ≤ 3 * |pv ξ P| := by positivity
    linarith
  -- the LI family with tails among Ct
  rcases m5_li_family (n := n) (hn := by omega) (Q := Q) (P := P) hQnz hdegQ hP hdegP hPprim hQle
    C Ct hC0 hCdeg hCli hCtdeg hrel with ⟨F, hF0, hF1, hliF, hdegF, hFtailCt⟩
  have hmapinj : Function.Injective (fun i : Fin (n + 1) => (F i).map (Int.castRingHom ℝ)) := by
    exact li_injective hliF
  have hFinj : Function.Injective F := by
    intro i j hij
    apply hmapinj
    exact congrArg (fun P : Polynomial ℤ => P.map (Int.castRingHom ℝ)) hij
  have hF0' : ∀ p : 0 < n + 1, F (⟨0, p⟩ : Fin (n + 1)) = Q := by
    intro p
    rw [fin0_all p, hF0]
  have hF1' : ∀ p : 1 < n + 1, F (⟨1, p⟩ : Fin (n + 1)) = P := by
    intro p
    rw [fin1_all p, hF1]
  have hPtail : ∀ j : Fin (n - 1), supN P ≤ supN (F (tailPos hn j)) := by
    intro j
    rcases hFtailCt (tailPos hn j) (by
      dsimp [tailPos]
      omega) with ⟨k, hFjk⟩
    rw [hFjk]
    exact hCtbig k
  -- the sorted final family and exponent
  rcases m5_family_final (n := n) (hn := hn) (Q := Q) (P := P) F hF0' hF1' hdegF hliF hQP hPgt1
    hPtail with ⟨Qfun, x, hq1, hq2, hdegQf, hLI, hmono1, hmono2, hprodEq, hprodFid, hxge, hQmem⟩
  -- the product-constant instance
  have hC1inst : |pv ξ Q| * (∏ j : Fin n, supN (C (Fin.succ j))) ≤ C1 :=
    hC1main q hq Q hQnz hdegQ hreal hslope C hC0 hCsup
  have hAbsQ : 0 ≤ |pv ξ Q| := abs_nonneg _
  -- engine: |pvQ|·(‖P‖·∏_j ‖F(tailPos j)‖) ≤ K^n·C1 = Cb
  have hEng : |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤ Cb := by
    rcases tail_witness_inj (n := n) hn F hFinj Ct hFtailCt with ⟨g, hspec, hginj⟩
    have hprodeq : (∏ j : Fin (n - 1), supN (F (tailPos hn j))) =
        ∏ j : Fin (n - 1), supN (Ct (g j)) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      exact congrArg supN (hspec j)
    have ha : ∀ k : Fin n, 1 ≤ supN (Ct k) := by
      intro k
      exact le_trans (supN_one_le hPne) (hCtbig k)
    have habsorb : supN P * (∏ j : Fin (n - 1), supN (Ct (g j))) ≤
        ∏ k : Fin n, supN (Ct k) := by
      exact prod_absorb_pred (n := n) (by omega : 1 ≤ n) g hginj (fun k => supN (Ct k)) ha
        (by intro k; exact hCtbig k)
    have hstep1 : |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤
        |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := by
      calc
        |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j))))
            = |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (Ct (g j)))) := by rw [hprodeq]
        _ ≤ |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := by
            exact mul_le_mul_of_nonneg_left habsorb hAbsQ
    have hstep2 : |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) ≤
        |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) := by
      have hle : (∏ k : Fin n, supN (Ct k)) ≤
          K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))) := by
        calc
          (∏ k : Fin n, supN (Ct k)) ≤ ∏ k : Fin n, K * supN (C (Fin.succ k)) := by
            refine Finset.prod_le_prod (s := Finset.univ) ?_ ?_
            · intro i hi
              exact supN_nonneg (Ct i)
            · intro i hi
              have hle' := hCtle i
              dsimp [K] at hle' ⊢
              exact hle'
          _ = K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))) := by
            exact prod_mul_const K (fun k : Fin n => supN (C (Fin.succ k)))
      exact mul_le_mul_of_nonneg_left hle hAbsQ
    have hstep3 : |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) ≤ K ^ n * C1 := by
      calc
        |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k))))
            = K ^ n * (|pv ξ Q| * (∏ k : Fin n, supN (C (Fin.succ k)))) := by ring
        _ ≤ K ^ n * C1 := by
            exact mul_le_mul_of_nonneg_left hC1inst (pow_nonneg hK0 n)
    calc
      |pv ξ Q| * (supN P * (∏ j : Fin (n - 1), supN (F (tailPos hn j)))) ≤
          |pv ξ Q| * (∏ k : Fin n, supN (Ct k)) := hstep1
      _ ≤ |pv ξ Q| * (K ^ n * (∏ k : Fin n, supN (C (Fin.succ k)))) := hstep2
      _ ≤ K ^ n * C1 := hstep3
      _ = Cb := hCbeq.symm
  -- |pvQ|·‖P‖^x ≤ Cb
  have hApos : 0 < supN P ^ x := Real.rpow_pos_of_pos hPpos x
  have hEngX : |pv ξ Q| * (supN P ^ x) ≤ Cb := by
    have h : |pv ξ Q| * (supN (Qfun 2)) ^ x ≤ Cb := by
      rw [← hprodEq]
      rw [hprodFid]
      exact hEng
    simpa [hq2] using h
  have hdecay : |pv ξ Q| ≤ Cb * (supN P) ^ (-x) := by
    let A : ℝ := supN P ^ x
    have hApos' : 0 < A := by
      dsimp [A]
      exact Real.rpow_pos_of_pos hPpos x
    have hEngA : |pv ξ Q| * A ≤ Cb := by
      dsimp [A]
      exact hEngX
    have hinv : A⁻¹ = (supN P) ^ (-x) := by
      dsimp [A]
      rw [Real.rpow_neg (supN_nonneg P) x]
    calc
      |pv ξ Q| = |pv ξ Q| * (A * A⁻¹) := by
        field_simp [ne_of_gt hApos']
      _ ≤ Cb * A⁻¹ := by
        have hm : |pv ξ Q| * A * A⁻¹ ≤ Cb * A⁻¹ := by
          exact mul_le_mul_of_nonneg_right hEngA (inv_nonneg.mpr (le_of_lt hApos'))
        calc
          |pv ξ Q| * (A * A⁻¹) = |pv ξ Q| * A * A⁻¹ := by ring
          _ ≤ Cb * A⁻¹ := hm
      _ = Cb * (supN P) ^ (-x) := by rw [← hinv]
  -- x ≤ w2 + eps
  have hxle : x ≤ w2 + eps := by
    exact x_le_w2_add_eps_of_hB (n := n) (hn := hn) (ξ := ξ) (w2 := w2) (eps := eps)
      (hw2 := hw2) (heps := heps0) (Q := Q) (P := P) (x := x) (C := Cb) hCbpos hQnz hPne
      hPgt1 hQP hBQ hdecay (by simpa [Cb, K] using hbig)
  -- the uniform bound ‖P‖^(x−w2) ≤ Cb (needs hBQ, hQle, decay)
  have hpow : (supN P) ^ (x - w2) ≤ Cb := by
    let t : ℝ := supN P
    have ht0 : 0 < t := by
      dsimp [t]
      exact hPpos
    have hneg : (-w2 : ℝ) < 0 := by linarith
    have hP_ge : t ^ (-w2) ≤ (supN Q) ^ (-w2) := by
      dsimp [t]
      exact rpow_neg_anti (a := supN Q) (b := supN P) hQt0 hQP hneg
    have hchain : t ^ (-w2) ≤ Cb * t ^ (-x) := by
      dsimp [t]
      exact le_trans hP_ge (le_trans hBQ hdecay)
    have hL : t ^ x * t ^ (-w2) = t ^ (x - w2) := by
      rw [show x - w2 = x + (-w2) by ring]
      rw [Real.rpow_add ht0 x (-w2)]
    have h1 : t ^ x * t ^ (-x) = 1 := by
      rw [← Real.rpow_add ht0 x (-x)]
      rw [show x + (-x) = 0 by ring, Real.rpow_zero]
    have hR : t ^ x * (Cb * t ^ (-x)) = Cb := by
      calc
        t ^ x * (Cb * t ^ (-x)) = Cb * (t ^ x * t ^ (-x)) := by ring
        _ = Cb * 1 := by rw [h1]
        _ = Cb := by ring
    have hm := mul_le_mul_of_nonneg_left hchain (le_of_lt (Real.rpow_pos_of_pos ht0 x))
    calc
      t ^ (x - w2) = t ^ x * t ^ (-w2) := hL.symm
      _ ≤ t ^ x * (Cb * t ^ (-x)) := hm
      _ = Cb := hR
  -- per-member value bounds
  have h1P : 1 ≤ supN P := le_of_lt hPgt1
  have hQt1 : 1 ≤ supN Q := supN_one_le hQnz
  have hPvalPow : |pv ξ P| ≤ Cb * (supN P) ^ (-x + eps) := by
    exact value_le_rpow_eps (v := |pv ξ P|) (t := supN P) (w2 := w2) (eps := eps)
      (x := x) (C := Cb) hvalP (abs_nonneg _) h1P hpow hCb0
  have hQvalPow : |pv ξ Q| ≤ Cb * (supN P) ^ (-x + eps) := by
    exact pv_le_rpow_eps (t := supN P) (v := |pv ξ Q|) (abs_nonneg _) h1P (x := x)
      (eps := eps) (C := Cb) hCb0 heps0.le hdecay
  -- target constant
  let ct : ℝ := 4 * ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1)
  have hct : ct = 4 * Cb := by
    rfl
  have hct0 : 0 ≤ ct := by
    dsimp [ct]
    positivity
  have hs_pos : 0 ≤ (supN P) ^ (-x + eps) := Real.rpow_nonneg hPpos.le (-x + eps)
  have hcb_le : Cb * (supN P) ^ (-x + eps) ≤ ct * (supN P) ^ (-x + eps) := by
    rw [hct]
    exact mul_le_mul_of_nonneg_right (by linarith) hs_pos
  have hQfin : |pv ξ Q| ≤ ct * (supN P) ^ (-x + eps) := le_trans hQvalPow hcb_le
  have hPfin : |pv ξ P| ≤ ct * (supN P) ^ (-x + eps) := le_trans hPvalPow hcb_le
  have hCtf : ∀ k : Fin n, |pv ξ (Ct k)| ≤ ct * (supN P) ^ (-x + eps) := by
    intro k
    calc
      |pv ξ (Ct k)| ≤ |pv ξ Q| + 3 * |pv ξ P| := hCtval k
      _ ≤ Cb * (supN P) ^ (-x + eps) + 3 * (Cb * (supN P) ^ (-x + eps)) := by
        have h3 : 3 * |pv ξ P| ≤ 3 * (Cb * (supN P) ^ (-x + eps)) :=
          mul_le_mul_of_nonneg_left hPvalPow (by norm_num)
        exact add_le_add hQvalPow h3
      _ = 4 * (Cb * (supN P) ^ (-x + eps)) := by ring
      _ = ct * (supN P) ^ (-x + eps) := by
        rw [hct]
        ring
  have hval_all : ∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) →
      |pv ξ (Qfun i)| ≤ ct * (supN P) ^ (-x + eps) := by
    intro i hi
    rcases hQmem i hi with ⟨j, hQij⟩
    have hFj : |pv ξ (F j)| ≤ ct * (supN P) ^ (-x + eps) := by
      by_cases hj0 : (j : ℕ) = 0
      · have p : 0 < n + 1 := by omega
        have hjeq : j = (⟨0, p⟩ : Fin (n + 1)) := by
          apply Fin.ext
          exact hj0
        rw [hjeq, hF0' p]
        exact hQfin
      · by_cases hj1 : (j : ℕ) = 1
        · have p : 1 < n + 1 := by omega
          have hjeq : j = (⟨1, p⟩ : Fin (n + 1)) := by
            apply Fin.ext
            exact hj1
          rw [hjeq, hF1' p]
          exact hPfin
        · have hge2 : 2 ≤ (j : ℕ) := by omega
          rcases hFtailCt j hge2 with ⟨k, hFjk⟩
          rw [hFjk]
          exact hCtf k
    calc
      |pv ξ (Qfun i)| = |pv ξ (F j)| := by rw [hQij]
      _ ≤ ct * (supN P) ^ (-x + eps) := hFj
  -- assemble
  refine ⟨Qfun, x, hq1, hq2, hdegQf, hLI, hmono1, hmono2, hprodEq, hxge, hxle, ?_⟩
  intro i hi
  have hv := hval_all i hi
  -- rewrite target: ct · (supN(Qfun 2))^{...} with ct defeq target constant
  simpa [ct, hq2] using hv




open Polynomial
open scoped BigOperators

lemma m4_decay_le_half {n wbar m t : ℝ} (hwbar : 0 < wbar) (hm : 0 < m)
    (ht0 : 0 < t) (hbig : 2 * Real.exp (n : ℝ) * (2 / m) ^ (1 / wbar) ≤ t) :
    (Real.exp (-(n : ℝ)) * t / 2) ^ (-wbar) ≤ m / 2 := by
  let B : ℝ := (2 / m) ^ (1 / wbar)
  have hb0 : 0 < 2 / m := div_pos (by norm_num) hm
  have hB0 : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos hb0 _
  have hden : 0 < 2 * Real.exp (n : ℝ) := mul_pos (by norm_num) (Real.exp_pos (n : ℝ))
  have hle : B ≤ t / (2 * Real.exp (n : ℝ)) := by
    dsimp [B] at hbig ⊢
    exact (le_div_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbig)
  have hBleA : B ≤ Real.exp (-(n : ℝ)) * t / 2 := by
    calc
      B ≤ t / (2 * Real.exp (n : ℝ)) := hle
      _ = Real.exp (-(n : ℝ)) * t / 2 := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  let A : ℝ := Real.exp (-(n : ℝ)) * t / 2
  have hA0 : 0 < A := by
    dsimp [A]
    positivity
  have hBw : B ^ wbar = 2 / m := by
    dsimp [B]
    have hcancel : (1 / wbar) * wbar = (1 : ℝ) := by
      field_simp [ne_of_gt hwbar]
    calc
      ((2 / m) ^ (1 / wbar)) ^ wbar = (2 / m) ^ ((1 / wbar) * wbar) := by
        rw [← Real.rpow_mul hb0.le]
      _ = (2 / m) ^ (1 : ℝ) := by rw [hcancel]
      _ = 2 / m := Real.rpow_one (2 / m)
  have hAw : B ^ wbar ≤ A ^ wbar := Real.rpow_le_rpow hB0.le (by simpa [A] using hBleA) hwbar.le
  have hAm : A ^ (-wbar) = (A ^ wbar)⁻¹ := Real.rpow_neg (le_of_lt hA0) wbar
  have hBval : (B ^ wbar)⁻¹ = m / 2 := by
    rw [hBw]
    field_simp [ne_of_gt hm]
  calc
    A ^ (-wbar) = (A ^ wbar)⁻¹ := hAm
    _ ≤ (B ^ wbar)⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hA0 wbar) (Real.rpow_pos_of_pos hB0 wbar)).mpr hAw
    _ = m / 2 := hBval

theorem weak_lemma41_core (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1 / 2)
    (wbar : ℝ) (hwbar0 : 0 < wbar) (w2 : ℝ) (hw2_eps : eps < w2)
    (hA : ∃ H0 : ℝ, 1 ≤ H0 ∧ WbarOracle n ξ wbar H0)
    (hB : ∃ HE : ℝ, 1 ≤ HE ∧ ∀ Q0 : Polynomial ℤ, Q0 ≠ 0 → Q0.natDegree ≤ n →
      HE ≤ supN Q0 → (supN Q0) ^ (-w2) ≤ |pv ξ Q0|) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
      |pv ξ P| ≤ supN P ^ (-(w2 - eps)) → c ≤ supN P →
      ∃ Q0 : Polynomial ℤ, Q0 ≠ 0 ∧ Q0.natDegree ≤ n ∧
        supN Q0 ≤ Real.exp (-(n : ℝ)) * supN P ∧
        ∃ Qfun : ℕ → Polynomial ℤ, ∃ x : ℝ,
        Qfun 1 = Q0 ∧ Qfun 2 = P ∧ (n : ℝ) ≤ x ∧ x ≤ w2 + eps ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Qfun i).natDegree ≤ n) ∧
        LinearIndependent ℝ (fun i : Fin (n + 1) =>
          (Qfun (i.val + 1)).map (Int.castRingHom ℝ)) ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 n →
          supN (Qfun i) ≤ supN (Qfun (i + 1))) ∧
        (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → supN (Qfun 2) ≤ supN (Qfun i)) ∧
        (∏ i ∈ Finset.Icc 2 (n + 1), supN (Qfun i)) = (supN (Qfun 2)) ^ x ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) →
          |pv ξ (Qfun i)| ≤ c * ((supN (Qfun 2)) ^ (-x + eps))) := by
  classical
  rcases hA with ⟨H0, hH01, hA0⟩
  rcases hB with ⟨HE, hHE1, hB0⟩
  rcases corrected_product_upper (n := n) (by omega : 1 ≤ n) ξ with ⟨C1, hC1pos, hC1main⟩
  rcases pv_lower_uniform (n := n) (ξ := ξ) hξ HE with ⟨m, hm0, hmall⟩
  let eN : ℝ := Real.exp (n : ℝ)
  let cv : ℝ := 4 * ((1 + 3 * eN) ^ n * C1)
  let t1 : ℝ := eN * sm n ξ 0 1
  let t2 : ℝ := 1 + eN * sm n ξ (Real.log 2) 1
  let t3 : ℝ := 2 * eN * H0
  let t4 : ℝ := ((1 + 3 * eN) ^ n * C1) ^ (1 / eps)
  let t5 : ℝ := 2 * eN * (2 / m) ^ (1 / wbar)
  let c : ℝ := max 2 (max cv (max t1 (max t2 (max t3 (max t4 t5)))))
  refine ⟨c, ?_, ?_⟩
  · have h45 : 0 < max t4 t5 := by
      dsimp [t4, t5]
      positivity
    have h345 : 0 < max t3 (max t4 t5) := lt_of_lt_of_le h45 (le_max_right _ _)
    have h2345 : 0 < max t2 (max t3 (max t4 t5)) := lt_of_lt_of_le h345 (le_max_right _ _)
    have h12345 : 0 < max t1 (max t2 (max t3 (max t4 t5))) :=
      lt_of_lt_of_le h2345 (le_max_right _ _)
    have hcv12345 : 0 < max cv (max t1 (max t2 (max t3 (max t4 t5)))) :=
      lt_of_lt_of_le h12345 (le_max_right _ _)
    dsimp [c]
    exact lt_of_lt_of_le hcv12345 (le_max_right _ _)
  · intro P hPne hPirr hdegP hPval hcP
    let c45 : ℝ := max t4 t5
    let c345 : ℝ := max t3 c45
    let c2345 : ℝ := max t2 c345
    let c12345 : ℝ := max t1 c2345
    let cv12345 : ℝ := max cv c12345
    have hc_def : c = max 2 cv12345 := by
      dsimp [c, cv12345, c12345, c2345, c345, c45]
    have h2c : (2 : ℝ) ≤ c := by
      rw [hc_def]
      exact le_max_left _ _
    have h_cv : cv ≤ c := by
      rw [hc_def]
      exact le_trans (le_max_left cv c12345) (le_max_right 2 cv12345)
    have h_t1 : t1 ≤ c := by
      rw [hc_def]
      exact le_trans (le_trans (le_max_left t1 c2345) (le_max_right cv c12345))
        (le_max_right 2 cv12345)
    have h_t2 : t2 ≤ c := by
      rw [hc_def]
      exact le_trans (le_trans (le_trans (le_max_left t2 c345) (le_max_right t1 c2345))
        (le_max_right cv c12345)) (le_max_right 2 cv12345)
    have h_t3 : t3 ≤ c := by
      rw [hc_def]
      exact le_trans (le_trans (le_trans (le_trans (le_max_left t3 c45) (le_max_right t2 c345))
        (le_max_right t1 c2345)) (le_max_right cv c12345)) (le_max_right 2 cv12345)
    have h_t4 : t4 ≤ c := by
      rw [hc_def]
      exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left t4 t5)
        (le_max_right t3 c45)) (le_max_right t2 c345)) (le_max_right t1 c2345))
        (le_max_right cv c12345)) (le_max_right 2 cv12345)
    have h_t5 : t5 ≤ c := by
      rw [hc_def]
      exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right t4 t5)
        (le_max_right t3 c45)) (le_max_right t2 c345)) (le_max_right t1 c2345))
        (le_max_right cv c12345)) (le_max_right 2 cv12345)
    have hPgt1 : 1 < supN P := by
      have h2 : (2 : ℝ) ≤ supN P := le_trans h2c hcP
      linarith
    have hbig0 : Real.exp (n : ℝ) * sm n ξ 0 1 ≤ supN P := by
      exact le_trans h_t1 hcP
    have hPprim : P.IsPrimitive := isPrimitive_of_irreducible_tiny_value (n := n)
      (hw2 := hw2_eps) hdegP hPirr hPval
    rcases sm1_maximal_level_P (n := n) (ξ := ξ) hξ (P := P) hbig0 with ⟨q, hq0, hlevel, hmax⟩
    have hbigLog : Real.exp (n : ℝ) * sm n ξ (Real.log 2) 1 < supN P := by
      have hle : t2 ≤ supN P := le_trans h_t2 hcP
      dsimp [t2, eN] at hle
      linarith
    have hqLog : Real.log 2 ≤ q := le_of_lt (sm1_q_gt_log2_of_level_big (n := n) (ξ := ξ)
      (q := q) (P := P) hlevel hbigLog)
    rcases sm1_realizer (n := n) (ξ := ξ) (q := q) with ⟨Q, hQnz, hdegQ, hreal⟩
    have hslope : supN Q ≤ Real.exp q * |pv ξ Q| :=
      sm1_realizer_slope_right (n := n) (ξ := ξ) (q := q)
        (Real.exp (-(n : ℝ)) * supN P) Q hQnz hdegQ hreal hlevel hmax
    have hbigH0 : 2 * Real.exp (n : ℝ) * H0 ≤ supN P := by
      exact le_trans h_t3 hcP
    have hm4 : |pv ξ Q| ≤ (Real.exp (-(n : ℝ)) * supN P / 2) ^ (-wbar) :=
      m4_bound_of_level_big (n := n) (ξ := ξ) (q := q) (wbar := wbar) (H0 := H0) Q
        hdegQ hQnz hreal hslope hA0 (P := P) hlevel hbigH0
    have hQbig : HE ≤ supN Q := by
      by_contra hnot
      have hQlt : supN Q < HE := lt_of_not_ge hnot
      have hmQ : m ≤ |pv ξ Q| := hmall Q hQnz hdegQ (le_of_lt hQlt)
      have hbigT5 : 2 * Real.exp (n : ℝ) * (2 / m) ^ (1 / wbar) ≤ supN P := by
        exact le_trans h_t5 hcP
      have hdec := m4_decay_le_half (n := n) (wbar := wbar) (m := m)
        (t := supN P) hwbar0 hm0 (supN_pos_of_ne_zero hPne) hbigT5
      have hbad : m ≤ m / 2 := le_trans hmQ (le_trans hm4 hdec)
      linarith
    have hw2pos : 0 < w2 := lt_trans heps0 hw2_eps
    have hBQ : (supN Q) ^ (-w2) ≤ |pv ξ Q| := hB0 Q hQnz hdegQ hQbig
    have hbigX : ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1) ^ (1 / eps) ≤ supN P := by
      exact le_trans h_t4 hcP
    rcases m5_value_family (n := n) (hn := hn) (ξ := ξ) (q := q) (hq := hqLog)
      (Q := Q) (P := P) hQnz hdegQ hreal hslope hPirr hdegP hPprim hlevel hPgt1
      (eps := eps) (w2 := w2) heps0 hw2pos hPval hBQ (C1 := C1) hC1pos hC1main hbigX
      with ⟨Qfun, x, hq1, hq2, hdegQf, hLI, hmono1, hmono2, hprodEq, hxge, hxle, hvalQf⟩
    have hQle0 : supN Q ≤ Real.exp (-(n : ℝ)) * supN P :=
      realizer_norm_le_e_neg_n_supN (n := n) (ξ := ξ) (q := q) (P := P) (Q := Q) hreal hlevel
    refine ⟨Q, hQnz, hdegQ, hQle0, Qfun, x, hq1, hq2, hxge, hxle, hdegQf, hLI, hmono1, hmono2, hprodEq, ?_⟩
    intro i hi
    have hv := hvalQf i hi
    have hs0 : 0 ≤ (supN (Qfun 2)) ^ (-x + eps) :=
      Real.rpow_nonneg (supN_nonneg (Qfun 2)) (-x + eps)
    have hcc : 4 * ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1) ≤ c := by
      have h : cv ≤ c := h_cv
      dsimp [cv, eN] at h
      exact h
    calc
      |pv ξ (Qfun i)| ≤ 4 * ((1 + 3 * Real.exp (n : ℝ)) ^ n * C1) *
          (supN (Qfun 2)) ^ (-x + eps) := hv
      _ ≤ c * (supN (Qfun 2)) ^ (-x + eps) :=
        mul_le_mul_of_nonneg_right hcc hs0



lemma exp2_gt_seven : (7 : ℝ) < (Real.exp 1) ^ 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (7 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by
    norm_num [show (2.7182818283 : ℝ) = 27182818283 / 10 ^ 10 by norm_num]
  have h3 : (2.7182818283 : ℝ) ^ 2 < (Real.exp 1) ^ 2 :=
    (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) (Real.exp_pos 1).le).2 h1
  exact lt_trans h2 h3

lemma four_sqrt3_lt_seven : 4 * Real.sqrt 3 < (7 : ℝ) := by
  have hsq : (4 * Real.sqrt 3) ^ 2 < (7 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  exact (sq_lt_sq₀ (by positivity : 0 ≤ 4 * Real.sqrt 3) (by norm_num)).1 hsq

lemma exp2_sq (e : ℝ) : e ^ 2 / 4 = (e / 2) ^ 2 := by ring

lemma exp_nat_pow (n : ℕ) : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
  simpa using (Real.exp_nat_mul (1 : ℝ) n)

lemma sqrt_add_one_lt_exp_half_pow (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) < (Real.exp 1 / 2) ^ n := by
  let A : ℝ := Real.exp 1 / 2
  have hApos : 0 < A := by dsimp [A]; positivity
  have hE2 : (7 : ℝ) < (Real.exp 1) ^ 2 := exp2_gt_seven
  have hbA : Real.sqrt 3 < A ^ 2 := by
    have h47 : 4 * Real.sqrt 3 < 7 := four_sqrt3_lt_seven
    have hE : 4 * Real.sqrt 3 < (Real.exp 1) ^ 2 := lt_trans h47 hE2
    have h : Real.sqrt 3 < (Real.exp 1) ^ 2 / 4 := by nlinarith
    dsimp [A]
    rwa [show (Real.exp 1) ^ 2 / 4 = (Real.exp 1 / 2) ^ 2 by ring] at h
  have hA2 : (4 : ℝ) / 3 ≤ A ^ 2 := by
    dsimp [A]
    rw [show (Real.exp 1 / 2) ^ 2 = (Real.exp 1) ^ 2 / 4 by ring]
    nlinarith [hE2]
  have hstepR : ∀ k : ℕ, 1 ≤ k →
      Real.sqrt ((k : ℝ) + 2) < A ^ (k + 1) →
      Real.sqrt ((k : ℝ) + 3) < A ^ (k + 1 + 1) := by
    intro k hk ih
    have hsqle : Real.sqrt ((k : ℝ) + 3) ≤ A * Real.sqrt ((k : ℝ) + 2) := by
      rw [← sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt ((k : ℝ) + 3))
        (by positivity : 0 ≤ A * Real.sqrt ((k : ℝ) + 2))]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 3),
        mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 2)]
      have hmul : ((k : ℝ) + 3) ≤ A ^ 2 * ((k : ℝ) + 2) := by
        have hb' : ((k : ℝ) + 3) ≤ (4 / 3) * ((k : ℝ) + 2) := by
          have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith
        have hc' : (4 / 3) * ((k : ℝ) + 2) ≤ A ^ 2 * ((k : ℝ) + 2) := by
          exact mul_le_mul_of_nonneg_right hA2 (by positivity)
        nlinarith
      rwa [show A ^ 2 * ((k : ℝ) + 2) = A ^ 2 * ((k : ℝ) + 2) by ring]
    have hmul : A * Real.sqrt ((k : ℝ) + 2) < A ^ (k + 1 + 1) := by
      calc
        A * Real.sqrt ((k : ℝ) + 2) < A * A ^ (k + 1) := by
          exact mul_lt_mul_of_pos_left ih hApos
        _ = A ^ (k + 1 + 1) := by rw [pow_succ]; ring
    exact lt_of_le_of_lt hsqle hmul
  -- P j for j = n - 1 : sqrt ((j:ℝ)+2) < A^(j+1)
  let P : ℕ → Prop := fun j => Real.sqrt ((j : ℝ) + 2) < A ^ (j + 1)
  have hbase : P 1 := by
    dsimp [P]
    norm_num
    exact hbA
  have hsucc : ∀ k : ℕ, 1 ≤ k → P k → P (k + 1) := by
    intro k hk hPk
    have hPkR : Real.sqrt ((k : ℝ) + 2) < A ^ (k + 1) := by
      simpa [P] using hPk
    have hmain := hstepR k hk hPkR
    -- P (k+1) : sqrt(((k+1):ℝ)+2) < A^((k+1)+1) ; hmain sqrt ((k:ℝ)+3) < A^(k+1+1)
    have hconv : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by
      rw [Nat.cast_add]
      ring
    dsimp [P]
    rw [hconv]
    exact hmain
  -- n = (n - 1) + 1 with n ≥ 2
  have hnm : (n - 1) + 1 = n := by omega
  have hP : P (n - 1) := Nat.le_induction (m := 1) hbase hsucc (n - 1) (by omega)
  have hP' : Real.sqrt (((n - 1 : ℕ) : ℝ) + 2) < A ^ ((n - 1) + 1) := by
    simpa [P] using hP
  have hconv2 : ((n - 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 1 := by
    have hn1 : n - 1 + 1 = n := by omega
    rw [← hn1, Nat.cast_add, Nat.add_sub_cancel]
    ring
  have hPow : A ^ ((n - 1) + 1) = A ^ n := by rw [hnm]
  have hfin : Real.sqrt ((n : ℝ) + 1) < A ^ n := by
    rw [← hconv2, ← hPow]
    exact hP'
  simpa [A] using hfin

lemma factor_lt_one (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) ^ n * Real.sqrt (n + 1) * Real.exp (-(n : ℝ)) < 1 := by
  have h : Real.sqrt (n + 1) < (Real.exp 1 / 2) ^ n := sqrt_add_one_lt_exp_half_pow n hn
  have hpow : (Real.exp 1 / 2) ^ n = Real.exp (n : ℝ) / (2 : ℝ) ^ n := by
    rw [exp_nat_pow, div_pow]
  have h' : Real.sqrt (n + 1) < Real.exp (n : ℝ) / (2 : ℝ) ^ n := by
    rwa [hpow] at h
  have hmul : (2 : ℝ) ^ n * Real.sqrt (n + 1) < Real.exp (n : ℝ) := by
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    calc
      (2 : ℝ) ^ n * Real.sqrt (n + 1) < (2 : ℝ) ^ n * (Real.exp (n : ℝ) / (2 : ℝ) ^ n) := by
        exact mul_lt_mul_of_pos_left h' hp2
      _ = Real.exp (n : ℝ) := by field_simp [ne_of_gt hp2]
  have heneg : (0 : ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos (-(n : ℝ))
  have hfin : (2 : ℝ) ^ n * Real.sqrt (n + 1) * Real.exp (-(n : ℝ)) <
      Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) := by
    exact mul_lt_mul_of_pos_right hmul heneg
  have hcancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa [hcancel] using hfin

lemma realizer_coprime_over_rat (n : ℕ) (hn : 2 ≤ n) {Q P : Polynomial ℤ}
    (hQ : Q ≠ 0) (hdegQ : Q.natDegree ≤ n) (hdegP : P.natDegree ≤ n)
    (hP : Irreducible P) (hprim : P.IsPrimitive)
    (hQle : supN Q ≤ Real.exp (-(n : ℝ)) * supN P) :
    IsCoprime (Q.map (algebraMap ℤ ℚ)) (P.map (algebraMap ℤ ℚ)) := by
  classical
  have hPnz : P ≠ 0 := irreducible_ne_zero hP
  have hPirrQ : Irreducible (P.map (algebraMap ℤ ℚ)) := by
    exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hP
  have hndvdZ : ¬ P ∣ Q := by
    intro hPQ
    have hfac := int_poly_factor_supNorm_le n hPnz hQ hdegP hdegQ hPQ
    have hlt : (2 : ℝ) ^ n * Real.sqrt (n + 1) * Real.exp (-(n : ℝ)) < 1 :=
      factor_lt_one n hn
    have hsupP : (0 : ℝ) < supN P := supN_pos_of_ne_zero hPnz
    have hpos : 0 < (2 : ℝ) ^ n * Real.sqrt (n + 1) := by positivity
    have hstep : (2 : ℝ) ^ n * Real.sqrt (n + 1) * supN Q ≤
        (2 : ℝ) ^ n * Real.sqrt (n + 1) * (Real.exp (-(n : ℝ)) * supN P) := by
      exact mul_le_mul_of_nonneg_left hQle hpos.le
    have hltm : ((2 : ℝ) ^ n * Real.sqrt (n + 1) * Real.exp (-(n : ℝ))) * supN P < supN P := by
      exact (mul_lt_iff_lt_one_left hsupP).mpr hlt
    have hstrict : (2 : ℝ) ^ n * Real.sqrt (n + 1) * supN Q < supN P := by
      calc
        (2 : ℝ) ^ n * Real.sqrt (n + 1) * supN Q ≤
            (2 : ℝ) ^ n * Real.sqrt (n + 1) * (Real.exp (-(n : ℝ)) * supN P) := hstep
        _ = ((2 : ℝ) ^ n * Real.sqrt (n + 1) * Real.exp (-(n : ℝ))) * supN P := by ring
        _ < supN P := hltm
    exact (not_lt_of_ge hfac) hstrict
  have hndvdQ : ¬ (P.map (algebraMap ℤ ℚ)) ∣ (Q.map (algebraMap ℤ ℚ)) := by
    intro hd
    exact hndvdZ ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P Q hprim).mpr hd)
  exact (Irreducible.coprime_iff_not_dvd (p := P.map (algebraMap ℤ ℚ))
    (n := Q.map (algebraMap ℤ ℚ)) hPirrQ).mpr hndvdQ |>.symm


theorem weak_lemma41 (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1 / 2)
    (wbar : ℝ) (hwbar0 : 0 < wbar) (w2 : ℝ) (hw2_eps : eps < w2)
    (hA : ∃ H0 : ℝ, 1 ≤ H0 ∧ ∀ H : ℝ, H0 ≤ H → ∃ Q : Polynomial ℤ,
      Q ≠ 0 ∧ Q.natDegree ≤ n ∧
      (Q.map (Int.castRingHom ℝ)).supNorm ≤ H ∧
      ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖ ≤ H ^ (-wbar))
    (hB : ∃ HE : ℝ, 1 ≤ HE ∧ ∀ Q : Polynomial ℤ, Q ≠ 0 → Q.natDegree ≤ n →
      HE ≤ (Q.map (Int.castRingHom ℝ)).supNorm →
      ((Q.map (Int.castRingHom ℝ)).supNorm) ^ (-w2) ≤
        ‖Polynomial.eval ξ (Q.map (Int.castRingHom ℝ))‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-(w2 - eps)) →
      c ≤ (P.map (Int.castRingHom ℝ)).supNorm →
      ∃ Q : ℕ → Polynomial ℤ, ∃ x : ℝ,
        (n : ℝ) ≤ x ∧ x ≤ w2 + eps ∧
        Q 2 = P ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) → (Q i).natDegree ≤ n) ∧
        LinearIndependent ℝ (fun i : Fin (n + 1) =>
          (Q (i.val + 1)).map (Int.castRingHom ℝ)) ∧
        IsCoprime ((Q 1).map (algebraMap ℤ ℚ)) ((Q 2).map (algebraMap ℤ ℚ)) ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 n →
          ((Q i).map (Int.castRingHom ℝ)).supNorm ≤
            ((Q (i + 1)).map (Int.castRingHom ℝ)).supNorm) ∧
        (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) →
          ((Q 2).map (Int.castRingHom ℝ)).supNorm ≤
            ((Q i).map (Int.castRingHom ℝ)).supNorm) ∧
        (∏ i ∈ Finset.Icc 2 (n + 1), ((Q i).map (Int.castRingHom ℝ)).supNorm) =
          (((Q 2).map (Int.castRingHom ℝ)).supNorm) ^ x ∧
        (∀ i : ℕ, i ∈ Finset.Icc 1 (n + 1) →
          ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤
            c * ((((Q 2).map (Int.castRingHom ℝ)).supNorm) ^ (-x + eps))) := by
  classical
  rcases hA with ⟨H0, hH01, hA0⟩
  rcases hB with ⟨HE, hHE1, hB0⟩
  have hA' : WbarOracle n ξ wbar H0 := by
    intro H hH
    rcases hA0 H hH with ⟨R, hRnz, hdegR, hsupR, hvalR⟩
    refine ⟨R, hRnz, hdegR, ?_, ?_⟩
    · simpa [supN] using hsupR
    · rw [Real.norm_eq_abs] at hvalR
      simpa [pv] using hvalR
  have hB' : ∀ Q0 : Polynomial ℤ, Q0 ≠ 0 → Q0.natDegree ≤ n →
      HE ≤ supN Q0 → (supN Q0) ^ (-w2) ≤ |pv ξ Q0| := by
    intro Q0 hQ0nz hdeg hsup
    have h := hB0 Q0 hQ0nz hdeg (by simpa [supN] using hsup)
    rw [Real.norm_eq_abs] at h
    simpa [supN, pv] using h
  rcases weak_lemma41_core n hn ξ hξ eps heps0 heps1 wbar hwbar0 w2 hw2_eps
    ⟨H0, hH01, hA'⟩ ⟨HE, hHE1, hB'⟩ with ⟨c, hcpos, hcmain⟩
  refine ⟨c, hcpos, ?_⟩
  intro P hPne hPirr hdegP hval hcP
  have hvalP : |pv ξ P| ≤ supN P ^ (-(w2 - eps)) := by
    rw [Real.norm_eq_abs] at hval
    simpa [pv, supN] using hval
  have hcP' : c ≤ supN P := by simpa [supN] using hcP
  have hprim : P.IsPrimitive :=
    isPrimitive_of_irreducible_tiny_value (n := n) (hw2 := hw2_eps) hdegP hPirr hvalP
  rcases hcmain P hPne hPirr hdegP hvalP hcP' with
    ⟨Q0, hQ0nz, hQ0deg, hQ0le, Qfun, x, hq1, hq2, hxge, hxle, hdegQf, hLI, hmono1,
      hmono2, hprodEq, hvalQf⟩
  refine ⟨Qfun, x, hxge, hxle, hq2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hdegQf i hi
  · simpa using hLI
  · rw [hq1, hq2]
    exact realizer_coprime_over_rat n hn hQ0nz hQ0deg hdegP hPirr hprim hQ0le
  · intro i hi
    simpa [supN] using hmono1 i hi
  · intro i hi
    simpa [supN] using hmono2 i hi
  · simpa [supN] using hprodEq
  · intro i hi
    have hv := hvalQf i hi
    rw [Real.norm_eq_abs]
    simpa [pv, supN] using hv

end