import Mathlib

/-!
# `q`-Pochhammer symbols (for the semi-finite proof of the Jacobi triple product)

* `qpNat a q n = (a;q)_n = ∏_{j<n} (1 - a q^j)` for `n : ℕ`,
* `qpInf a q = (a;q)_∞ = ∏'_{n≥0} (1 - a q^n)`,
* `qpInt a q n` for `n : ℤ`, given by `(a;q)_{-k-1} = ((a q^{-k-1};q)_{k+1})⁻¹`,
* `qhalf q n = ∏_{j<n} q^j = q^{n(n-1)/2}` (a `q`-power that avoids division),
* `qhalfInt q n` for `n : ℤ`, the corresponding integer-index version,

together with the semi-finite summand `sfTerm` and the two pieces `Afun`, `Bfun` of the split.
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- The finite `q`-Pochhammer symbol `(a;q)_n = ∏_{j<n} (1 - a q^j)`. -/
noncomputable def qpNat (a q : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1 - a * q ^ j)

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏'_{n≥0} (1 - a q^n)`. -/
noncomputable def qpInf (a q : ℂ) : ℂ := ∏' n : ℕ, (1 - a * q ^ n)

/-- The `q`-Pochhammer symbol for integer index.  For `n : ℕ` this is `(a;q)_n`;
for `n = -k-1` it is `(a;q)_{-k-1} = ((a q^{-k-1};q)_{k+1})⁻¹`. -/
noncomputable def qpInt (a q : ℂ) : ℤ → ℂ
  | (n : ℕ) => qpNat a q n
  | Int.negSucc k => (qpNat (a * q ^ (-(k : ℤ) - 1)) q (k + 1))⁻¹

/-- `∏_{j<n} q^j`, i.e. `q^{n(n-1)/2}` (without division). -/
noncomputable def qhalf (q : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, q ^ j

/-- The integer-index version of `qhalf`: for `n ≥ 0` it is `q^{n(n-1)/2}` and
for `n = -k-1` it is `q^{(k+1)(k+2)/2} = q^{n(n-1)/2}`. -/
noncomputable def qhalfInt (q : ℂ) : ℤ → ℂ
  | (n : ℕ) => qhalf q n
  | Int.negSucc k => qhalf q (k + 2)

/-- The summand of the "semi-finite" sum, `q^{n(n-1)/2} z^n / (q^{m+1};q)_n`. -/
noncomputable def sfTerm (q z : ℂ) (m : ℕ) (n : ℤ) : ℂ :=
  qhalfInt q n * z ^ n / qpInt (q ^ ((m : ℤ) + 1)) q n

/-- The `n ≥ 0` part `∑_{n≥0} q^{n(n-1)/2} z^n / (q^{m+1};q)_n`. -/
noncomputable def Afun (q z : ℂ) (m : ℕ) : ℂ :=
  ∑' n : ℕ, qhalf q n * z ^ n / qpNat (q ^ ((m : ℤ) + 1)) q n

/-- The `n < 0` part `∑_{n=1}^{m} (q^{m+1-n};q)_n q^{n(n+1)/2} z^{-n}`. -/
noncomputable def Bfun (q z : ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, qpNat (q ^ ((m : ℤ) + 1 - n)) q n * qhalf q (n + 1) * z ^ (-(n : ℤ))

/-! ## Elementary facts about `qpNat` -/

@[simp] lemma qpNat_zero (a q : ℂ) : qpNat a q 0 = 1 := by simp [qpNat]

lemma qpNat_succ (a q : ℂ) (n : ℕ) :
    qpNat a q (n + 1) = qpNat a q n * (1 - a * q ^ n) := by
  simp [qpNat, Finset.prod_range_succ]

lemma qpNat_one (a q : ℂ) : qpNat a q 1 = 1 - a := by simp [qpNat]

/-- `(a;q)_{m+n} = (a;q)_m (aq^m;q)_n`. -/
lemma qpNat_mul_qpNat (a q : ℂ) (m n : ℕ) :
    qpNat a q m * qpNat (a * q ^ m) q n = qpNat a q (m + n) := by
  rw [qpNat, qpNat, qpNat, Finset.prod_range_add (f := fun x => 1 - a * q ^ x) m n]
  congr 1
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [pow_add, mul_assoc]

/-- `(q;q)_n ≠ 0` when `‖q‖ < 1`. -/
lemma qpNat_self_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : qpNat q q n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  intro h
  have h2 : q * q ^ j = 1 := (sub_eq_zero.mp h).symm
  have h1 : q ^ (j + 1) = 1 := by rw [pow_succ']; exact h2
  have h3 : ‖q‖ ^ (j + 1) = 1 := by rw [← norm_pow, h1, norm_one]
  have h4 : ‖q‖ ^ (j + 1) < 1 := pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero j)
  exact (ne_of_lt h4) h3

/-- More generally `(a q^k;q)_n ≠ 0` for `‖q‖ < 1` and `k ≥ 1`. -/
lemma qpNat_shift_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (k n : ℕ) (hk : 1 ≤ k) :
    qpNat (q ^ k) q n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  intro h
  have h2 : q ^ k * q ^ j = 1 := (sub_eq_zero.mp h).symm
  have h1 : q ^ (k + j) = 1 := by rw [← h2, pow_add]
  have h3 : ‖q‖ ^ (k + j) = 1 := by rw [← norm_pow, h1, norm_one]
  have h4 : ‖q‖ ^ (k + j) < 1 := pow_lt_one₀ (norm_nonneg q) hq (by omega)
  exact (ne_of_lt h4) h3

/-! ## Elementary facts about `qpInt` -/

lemma qpInt_ofNat (a q : ℂ) (n : ℕ) : qpInt a q (n : ℤ) = qpNat a q n := rfl

@[simp] lemma qpInt_zero (a q : ℂ) : qpInt a q 0 = 1 := by simp [qpInt]

lemma qpInt_negSucc (a q : ℂ) (k : ℕ) :
    qpInt a q (Int.negSucc k) = (qpNat (a * q ^ (-(k : ℤ) - 1)) q (k + 1))⁻¹ := rfl

/-- `(a;q)_{-n} = ((a q^{-n};q)_n)⁻¹`. -/
lemma qpInt_neg_natCast (a q : ℂ) (n : ℕ) :
    qpInt a q (-(n : ℤ)) = (qpNat (a * q ^ (-(n : ℤ))) q n)⁻¹ := by
  match n with
  | 0 => simp
  | (k + 1) =>
    have h : (-(↑(k + 1) : ℤ)) = Int.negSucc k := by rw [Int.negSucc_eq]; push_cast; ring
    have h3 : Int.negSucc k = -↑k - 1 := by rw [Int.negSucc_eq]; push_cast; ring
    rw [h, qpInt_negSucc, h3]

/-- `(q^{m+1};q)_{-m} = ((q;q)_m)⁻¹`. -/
lemma qpInt_neg_self {q : ℂ} (hq : q ≠ 0) (m : ℕ) :
    qpInt (q ^ ((m : ℤ) + 1)) q (-(m : ℤ)) = (qpNat q q m)⁻¹ := by
  rw [qpInt_neg_natCast]
  congr 2
  have h : q ^ ((m : ℤ) + 1) * q ^ (-(m : ℤ)) = q := by
    rw [← zpow_add₀ hq]
    norm_num
  rw [h]

/-! ## Elementary facts about `qhalf` -/

lemma qhalf_succ (q : ℂ) (n : ℕ) : qhalf q (n + 1) = qhalf q n * q ^ n := by
  simp [qhalf, Finset.prod_range_succ]

@[simp] lemma qhalf_zero (q : ℂ) : qhalf q 0 = 1 := by simp [qhalf]

@[simp] lemma qhalf_one (q : ℂ) : qhalf q 1 = 1 := by simp [qhalf]

lemma qhalf_two (q : ℂ) : qhalf q 2 = q := by
  rw [show (2:ℕ) = 1 + 1 from rfl, qhalf_succ, qhalf_one]
  simp

/-- `qhalf q (m+n) = qhalf q m * qhalf q n * q^{mn}`. -/
lemma qhalf_add (q : ℂ) (m n : ℕ) :
    qhalf q (m + n) = qhalf q m * qhalf q n * q ^ (m * n) := by
  rw [qhalf, qhalf, qhalf, Finset.prod_range_add (f := fun x => q ^ x) m n]
  have h1 : (∏ x ∈ Finset.range n, q ^ (m + x))
      = q ^ (m * n) * ∏ x ∈ Finset.range n, q ^ x := by
    simp only [pow_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, Nat.mul_comm]
  rw [h1]
  ring

lemma qhalfInt_natCast (q : ℂ) (n : ℕ) : qhalfInt q (n : ℤ) = qhalf q n := rfl

lemma qhalfInt_negSucc (q : ℂ) (k : ℕ) : qhalfInt q (Int.negSucc k) = qhalf q (k + 2) := rfl

@[simp] lemma qhalfInt_zero (q : ℂ) : qhalfInt q 0 = 1 := by simp [qhalfInt]

lemma qhalfInt_one (q : ℂ) : qhalfInt q 1 = 1 := by simp [qhalfInt]

/-- `qhalfInt q (-m) = qhalf q (m+1)`. -/
lemma qhalfInt_neg_natCast (q : ℂ) (m : ℕ) : qhalfInt q (-(m : ℤ)) = qhalf q (m + 1) := by
  match m with
  | 0 => simp
  | (k + 1) =>
    have h : (-(↑(k + 1) : ℤ)) = Int.negSucc k := by rw [Int.negSucc_eq]; push_cast; ring
    rw [h, qhalfInt_negSucc]

end Work.Haupt
