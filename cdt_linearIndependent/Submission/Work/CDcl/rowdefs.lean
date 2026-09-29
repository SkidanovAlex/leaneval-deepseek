import Mathlib
import Submission.CDTPlan.InterfacesC

/-!
# The explicit rows for the "easy half" of `CDClosed`

Definitions used by `Submission.Work.CDcl.easy_relations`: the truncation jet `jet`, the
denominator `qOf q0 = X^4 * q0`, and the coefficient matrix `AOf q0 A0 G` of the theorem.

The matrix `AOf q0 A0 G` has one row per index `i : Fin 17` of `Submission.CDTPlan.seventeen`:

* rows `0..4` (`B₁..B₅`) and `9,10` (`B₆,B₇`): the `B`-row `rowB q0 A0 a`, i.e. `X^4 * A0 a k` in
  the `k`-th `B`-slot (slots `0..4,9,10` of the 17-tuple) and `0` elsewhere;
* rows `5,6,7` (`G, G', G''`): `q = X^4 * q₀` in the next column;
* rows `11,12` (`∫yG`, `∫G`): `X·q` resp. `q` in column `5` (`G`);
* rows `13..16` (`∫ (G − jet_k)/y^k`, `k = 1..4`): `X^{4-k} q₀` in column `5` (`G`) and
  `−X^{4-k} q₀ · jet_k G` in column `0` (`B₁ = 1`).
-/

namespace Work.CDcl

open PowerSeries Polynomial

noncomputable section

/-- The truncation jet `Σ_{j<k} (coeff j f) y^j` of a power series. -/
noncomputable def jet (k : ℕ) (f : PowerSeries ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range k, Polynomial.C (PowerSeries.coeff j f) * Polynomial.X ^ j

/-- Coefficient formula for the truncation jet. -/
lemma jet_coeff (k : ℕ) (f : PowerSeries ℚ) (n : ℕ) :
    (jet k f).coeff n = if n < k then PowerSeries.coeff n f else 0 := by
  rw [jet, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]

/-- `d/dy` of the formal integral with zero constant term. -/
lemma derivative_intY (f : PowerSeries ℚ) :
    PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.intY f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, Submission.CDTPlan.intY, PowerSeries.coeff_mk]
  have h : n + 1 ≠ 0 := by omega
  rw [if_neg h, Nat.add_sub_cancel]
  have h2 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hc : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
  rw [hc]
  exact div_mul_cancel₀ _ h2

/-- `y^k · ((f − jet_k f)/y^k) = f − jet_k f`, i.e. `y^k · tq k f = f − jet k f`. -/
lemma X_pow_mul_tq (k : ℕ) (f : PowerSeries ℚ) :
    (PowerSeries.X : PowerSeries ℚ) ^ k * Submission.CDTPlan.tq k f
      = f - (jet k f : PowerSeries ℚ) := by
  ext n
  rw [map_sub, PowerSeries.coeff_X_pow_mul', Submission.CDTPlan.tq, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, jet_coeff]
  by_cases h : k ≤ n
  · rw [if_pos h, Nat.sub_add_cancel h, if_neg (by omega : ¬ n < k), sub_zero]
  · rw [if_neg h, if_pos (by omega : n < k), sub_self]

/-- The common denominator `X^4 * q₀`. -/
noncomputable def qOf (q0 : Polynomial ℚ) : Polynomial ℚ := Polynomial.X ^ 4 * q0

lemma qOf_ne_zero {q0 : Polynomial ℚ} (h : q0 ≠ 0) : qOf q0 ≠ 0 := by
  rw [qOf]
  exact mul_ne_zero (pow_ne_zero 4 Polynomial.X_ne_zero) h

/-- The index embedding of the seven `B`-slots into the 17-tuple: `0..4 ↦ 0..4`, `5 ↦ 9`, `6 ↦ 10`. -/
noncomputable def eIdx (a : Fin 7) : Fin 17 :=
  if h : a.val < 5 then ⟨a.val, by omega⟩ else if a.val = 5 then 9 else 10

/-- The row of the seven `B`-functions: `X^4 * A0 a k` in the `k`-th `B`-slot, `0` elsewhere. -/
noncomputable def rowB (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7)
    (j : Fin 17) : Polynomial ℚ :=
  if j.val = 0 then Polynomial.X ^ 4 * A0 a 0
  else if j.val = 1 then Polynomial.X ^ 4 * A0 a 1
  else if j.val = 2 then Polynomial.X ^ 4 * A0 a 2
  else if j.val = 3 then Polynomial.X ^ 4 * A0 a 3
  else if j.val = 4 then Polynomial.X ^ 4 * A0 a 4
  else if j.val = 9 then Polynomial.X ^ 4 * A0 a 5
  else if j.val = 10 then Polynomial.X ^ 4 * A0 a 6
  else 0

/-- The row of `∫ (G − jet_k G)/y^k` for `k = 1..4`: `X^{4-k} q₀` on `G` and
`−X^{4-k} q₀ · jet_k G` on `B₁ = 1`. -/
noncomputable def rowT (q0 : Polynomial ℚ) (G : PowerSeries ℚ) (k : ℕ) (j : Fin 17) :
    Polynomial ℚ :=
  if j.val = 5 then Polynomial.X ^ (4 - k) * q0
  else if j.val = 0 then -(Polynomial.X ^ (4 - k) * q0 * jet k G)
  else 0

/-- The coefficient matrix of the easy half of `CDClosed`.  Column `j` indexes
`Submission.CDTPlan.seventeen m n ra rb rab r0 j`. -/
noncomputable def AOf (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (G : PowerSeries ℚ) (i j : Fin 17) : Polynomial ℚ :=
  if _ : i.val < 5 then rowB q0 A0 ⟨i.val, by omega⟩ j
  else if i.val = 5 then (if j.val = 6 then qOf q0 else 0)
  else if i.val = 6 then (if j.val = 7 then qOf q0 else 0)
  else if i.val = 7 then (if j.val = 8 then qOf q0 else 0)
  else if i.val = 9 then rowB q0 A0 5 j
  else if i.val = 10 then rowB q0 A0 6 j
  else if i.val = 11 then (if j.val = 5 then Polynomial.X * qOf q0 else 0)
  else if i.val = 12 then (if j.val = 5 then qOf q0 else 0)
  else if i.val = 13 then rowT q0 G 1 j
  else if i.val = 14 then rowT q0 G 2 j
  else if i.val = 15 then rowT q0 G 3 j
  else if i.val = 16 then rowT q0 G 4 j
  else 0

end

end Work.CDcl
