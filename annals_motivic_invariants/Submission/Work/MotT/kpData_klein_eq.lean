import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotT.KpDataDev
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Klein identity for the parametric datum `(u,1)`

`Work.MotT.kpData_klein_eq`: the five Klein (Pfaffian) quadrics vanish on the Klein
coordinates of the parametric datum `kpData K u`, i.e. the `klein_eq` field of
`Work.MotV.KleinData.Good`.

The Klein coordinates `κ_i` have coefficients with denominators `w²` (`w = 2u⁵-1`); the
*cleared* coordinates `κ̂_i = w²·κ_i` (the `kpKi`) are polynomials, and the Pfaffian quadrics
of the `κ̂_i` are the quotient `w·Q_k` times the cleared Weierstrass relation `Λ·W` (a
polynomial identity, proved by `ring`).  Since `Λ·W = 0` in the function field and the
clearing factor `5⁹u¹²w⁴` is nonzero, the quadrics of the `κ_i` vanish as well.
-/

namespace Work.MotT
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The scaled Klein coordinates are `w²·κ` -/

/-- The scaled Klein coordinate `w²·κ_j`, written in the basis `1, x, y, x², x·y`. -/
lemma kpKsum (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] (j : Fin 5) :
    kpKappaHat K u L j =
      ∑ m : Fin 5, algebraMap K (kpFF K u L) (kpChat K u j m) * kpBas K u L m := by
  fin_cases j <;>
  · simp only [kpKappaHat]
    norm_num
    rw [Fin.sum_univ_five]
    dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpChat, kpBas, kpX, kpY, kpUF, kpWF, kpDF]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ',
      map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one, map_natCast, map_zero,
      kpW, kpDelta]
    try ring

/-- The scaling relation `w²·κ_j = κ̂_j`. -/
lemma kpBridge (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : kpW K u ≠ 0) (j : Fin 5) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L j = kpKappaHat K u L j := by
  rw [kpKsum K u L j]
  simp only [kpKap]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h1 : (kpWF K u L) ^(2:ℕ) = (algebraMap K (kpFF K u L) (kpW K u)) ^(2:ℕ) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have h2 : (algebraMap K (kpFF K u L) (kpW K u)) ^(2:ℕ)
        * algebraMap K (kpFF K u L) (kpCoord K u j m)
      = algebraMap K (kpFF K u L) (kpChat K u j m) := by
    rw [← map_pow, ← map_mul, ← kpChat_spec K u hw j m]
  rw [h1, ← mul_assoc, h2]

/-! ## The cleared Weierstrass relation -/

/-- `kpUF`, `kpWF`, `kpDF` are the images of `u`, `w`, `Δ`. -/
lemma kpUF_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpUF K u L = algebraMap K (kpFF K u L) u := rfl

lemma kpWF_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
  simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]

lemma kpDF_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
  simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]

/-- `Λ·a₁` is `Λ` times the Weierstrass coefficient. -/
lemma kpAhat1_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpAhat1F K u L = kpLambdaF K u L * algebraMap K (kpFF K u L) (kpA1 K u) := by
  have hUF : kpUF K u L = algebraMap K (kpFF K u L) u := rfl
  have hWF : kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have hDF : kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
    simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : algebraMap K (kpFF K u L) (kpW K u) ≠ 0 := fun h =>
    hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5 : algebraMap K (kpFF K u L) (5 : K) ≠ 0 := fun h =>
    h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h1953 : algebraMap K (kpFF K u L) (1953125 : K) ≠ 0 := by
    rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow]
    exact pow_ne_zero 9 h5
  dsimp only [kpAhat1F, kpLambdaF, kpA1]
  simp only [hUF, hWF, hDF]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    map_natCast, map_zero]
  have h5' : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact h5
  have h125 : (125 : kpFF K u L) ≠ 0 := by
    rw [show (125 : kpFF K u L) = (5 : kpFF K u L) ^(3:ℕ) by norm_num]
    exact pow_ne_zero 3 h5'
  have h625 : (625 : kpFF K u L) ≠ 0 := by
    rw [show (625 : kpFF K u L) = (5 : kpFF K u L) ^(4:ℕ) by norm_num]
    exact pow_ne_zero 4 h5'
  have h15625 : (15625 : kpFF K u L) ≠ 0 := by
    rw [show (15625 : kpFF K u L) = (5 : kpFF K u L) ^(6:ℕ) by norm_num]
    exact pow_ne_zero 6 h5'
  have h1953125 : (1953125 : kpFF K u L) ≠ 0 := by
    rw [show (1953125 : kpFF K u L) = (5 : kpFF K u L) ^(9:ℕ) by norm_num]
    exact pow_ne_zero 9 h5'
  field_simp [hUnz, hWnz, h5, h1953, h125, h625, h15625, h1953125,
    show algebraMap K (kpFF K u L) (1953125 : K) = (5 : kpFF K u L) ^(9:ℕ) by
      rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow, map_ofNat]]
  try ring

/-- `Λ·a₂` is `Λ` times the Weierstrass coefficient. -/
lemma kpAhat2_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpAhat2F K u L = kpLambdaF K u L * algebraMap K (kpFF K u L) (kpA2 K u) := by
  have hUF : kpUF K u L = algebraMap K (kpFF K u L) u := rfl
  have hWF : kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have hDF : kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
    simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : algebraMap K (kpFF K u L) (kpW K u) ≠ 0 := fun h =>
    hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5 : algebraMap K (kpFF K u L) (5 : K) ≠ 0 := fun h =>
    h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h1953 : algebraMap K (kpFF K u L) (1953125 : K) ≠ 0 := by
    rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow]
    exact pow_ne_zero 9 h5
  dsimp only [kpAhat2F, kpLambdaF, kpA2]
  simp only [hUF, hWF, hDF]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    map_natCast, map_zero]
  have h5' : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact h5
  have h125 : (125 : kpFF K u L) ≠ 0 := by
    rw [show (125 : kpFF K u L) = (5 : kpFF K u L) ^(3:ℕ) by norm_num]
    exact pow_ne_zero 3 h5'
  have h625 : (625 : kpFF K u L) ≠ 0 := by
    rw [show (625 : kpFF K u L) = (5 : kpFF K u L) ^(4:ℕ) by norm_num]
    exact pow_ne_zero 4 h5'
  have h15625 : (15625 : kpFF K u L) ≠ 0 := by
    rw [show (15625 : kpFF K u L) = (5 : kpFF K u L) ^(6:ℕ) by norm_num]
    exact pow_ne_zero 6 h5'
  have h1953125 : (1953125 : kpFF K u L) ≠ 0 := by
    rw [show (1953125 : kpFF K u L) = (5 : kpFF K u L) ^(9:ℕ) by norm_num]
    exact pow_ne_zero 9 h5'
  field_simp [hUnz, hWnz, h5, h1953, h125, h625, h15625, h1953125,
    show algebraMap K (kpFF K u L) (1953125 : K) = (5 : kpFF K u L) ^(9:ℕ) by
      rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow, map_ofNat]]
  try ring

/-- `Λ·a₃` is `Λ` times the Weierstrass coefficient. -/
lemma kpAhat3_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpAhat3F K u L = kpLambdaF K u L * algebraMap K (kpFF K u L) (kpA3 K u) := by
  have hUF : kpUF K u L = algebraMap K (kpFF K u L) u := rfl
  have hWF : kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have hDF : kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
    simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : algebraMap K (kpFF K u L) (kpW K u) ≠ 0 := fun h =>
    hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5 : algebraMap K (kpFF K u L) (5 : K) ≠ 0 := fun h =>
    h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h1953 : algebraMap K (kpFF K u L) (1953125 : K) ≠ 0 := by
    rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow]
    exact pow_ne_zero 9 h5
  dsimp only [kpAhat3F, kpLambdaF, kpA3]
  simp only [hUF, hWF, hDF]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    map_natCast, map_zero]
  have h5' : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact h5
  have h125 : (125 : kpFF K u L) ≠ 0 := by
    rw [show (125 : kpFF K u L) = (5 : kpFF K u L) ^(3:ℕ) by norm_num]
    exact pow_ne_zero 3 h5'
  have h625 : (625 : kpFF K u L) ≠ 0 := by
    rw [show (625 : kpFF K u L) = (5 : kpFF K u L) ^(4:ℕ) by norm_num]
    exact pow_ne_zero 4 h5'
  have h15625 : (15625 : kpFF K u L) ≠ 0 := by
    rw [show (15625 : kpFF K u L) = (5 : kpFF K u L) ^(6:ℕ) by norm_num]
    exact pow_ne_zero 6 h5'
  have h1953125 : (1953125 : kpFF K u L) ≠ 0 := by
    rw [show (1953125 : kpFF K u L) = (5 : kpFF K u L) ^(9:ℕ) by norm_num]
    exact pow_ne_zero 9 h5'
  field_simp [hUnz, hWnz, h5, h1953, h125, h625, h15625, h1953125,
    show algebraMap K (kpFF K u L) (1953125 : K) = (5 : kpFF K u L) ^(9:ℕ) by
      rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow, map_ofNat]]
  try ring

/-- `Λ·a₄` is `Λ` times the Weierstrass coefficient. -/
lemma kpAhat4_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpAhat4F K u L = kpLambdaF K u L * algebraMap K (kpFF K u L) (kpA4 K u) := by
  have hUF : kpUF K u L = algebraMap K (kpFF K u L) u := rfl
  have hWF : kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have hDF : kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
    simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : algebraMap K (kpFF K u L) (kpW K u) ≠ 0 := fun h =>
    hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5 : algebraMap K (kpFF K u L) (5 : K) ≠ 0 := fun h =>
    h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h1953 : algebraMap K (kpFF K u L) (1953125 : K) ≠ 0 := by
    rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow]
    exact pow_ne_zero 9 h5
  dsimp only [kpAhat4F, kpLambdaF, kpA4]
  simp only [hUF, hWF, hDF]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    map_natCast, map_zero]
  have h5' : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact h5
  have h125 : (125 : kpFF K u L) ≠ 0 := by
    rw [show (125 : kpFF K u L) = (5 : kpFF K u L) ^(3:ℕ) by norm_num]
    exact pow_ne_zero 3 h5'
  have h625 : (625 : kpFF K u L) ≠ 0 := by
    rw [show (625 : kpFF K u L) = (5 : kpFF K u L) ^(4:ℕ) by norm_num]
    exact pow_ne_zero 4 h5'
  have h15625 : (15625 : kpFF K u L) ≠ 0 := by
    rw [show (15625 : kpFF K u L) = (5 : kpFF K u L) ^(6:ℕ) by norm_num]
    exact pow_ne_zero 6 h5'
  have h1953125 : (1953125 : kpFF K u L) ≠ 0 := by
    rw [show (1953125 : kpFF K u L) = (5 : kpFF K u L) ^(9:ℕ) by norm_num]
    exact pow_ne_zero 9 h5'
  field_simp [hUnz, hWnz, h5, h1953, h125, h625, h15625, h1953125,
    show algebraMap K (kpFF K u L) (1953125 : K) = (5 : kpFF K u L) ^(9:ℕ) by
      rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow, map_ofNat]]
  try ring

/-- `Λ·a₆` is `Λ` times the Weierstrass coefficient. -/
lemma kpAhat6_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpAhat6F K u L = kpLambdaF K u L * algebraMap K (kpFF K u L) (kpA6 K u) := by
  have hUF : kpUF K u L = algebraMap K (kpFF K u L) u := rfl
  have hWF : kpWF K u L = algebraMap K (kpFF K u L) (kpW K u) := by
    simp only [kpWF, kpUF, kpW, map_sub, map_mul, map_pow, map_ofNat, map_one]
  have hDF : kpDF K u L = algebraMap K (kpFF K u L) (kpDelta K u) := by
    simp only [kpDF, kpUF, kpDelta, map_sub, map_mul, map_pow, map_ofNat, map_one, map_natCast]
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : algebraMap K (kpFF K u L) (kpW K u) ≠ 0 := fun h =>
    hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5 : algebraMap K (kpFF K u L) (5 : K) ≠ 0 := fun h =>
    h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h1953 : algebraMap K (kpFF K u L) (1953125 : K) ≠ 0 := by
    rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow]
    exact pow_ne_zero 9 h5
  dsimp only [kpAhat6F, kpLambdaF, kpA6]
  simp only [hUF, hWF, hDF]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    map_natCast, map_zero]
  have h5' : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact h5
  have h125 : (125 : kpFF K u L) ≠ 0 := by
    rw [show (125 : kpFF K u L) = (5 : kpFF K u L) ^(3:ℕ) by norm_num]
    exact pow_ne_zero 3 h5'
  have h625 : (625 : kpFF K u L) ≠ 0 := by
    rw [show (625 : kpFF K u L) = (5 : kpFF K u L) ^(4:ℕ) by norm_num]
    exact pow_ne_zero 4 h5'
  have h15625 : (15625 : kpFF K u L) ≠ 0 := by
    rw [show (15625 : kpFF K u L) = (5 : kpFF K u L) ^(6:ℕ) by norm_num]
    exact pow_ne_zero 6 h5'
  have h1953125 : (1953125 : kpFF K u L) ≠ 0 := by
    rw [show (1953125 : kpFF K u L) = (5 : kpFF K u L) ^(9:ℕ) by norm_num]
    exact pow_ne_zero 9 h5'
  field_simp [hUnz, hWnz, h5, h1953, h125, h625, h15625, h1953125,
    show algebraMap K (kpFF K u L) (1953125 : K) = (5 : kpFF K u L) ^(9:ℕ) by
      rw [show (1953125 : K) = (5 : K) ^(9:ℕ) by norm_num, map_pow, map_ofNat]]
  try ring

/-- `Λ·W` is `Λ` times the Weierstrass relation. -/
lemma kpWhatF_eq (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hu : u ≠ 0) (hw : kpW K u ≠ 0) (hk : ringChar K ≠ 5) :
    kpWhatF K u L = kpLambdaF K u L * kpWrel K u L := by
  dsimp only [kpWhatF, kpWrel]
  rw [kpAhat1_eq K u L hu hw hk, kpAhat2_eq K u L hu hw hk, kpAhat3_eq K u L hu hw hk,
    kpAhat4_eq K u L hu hw hk, kpAhat6_eq K u L hu hw hk]
  refl_ring1

/-! ## The Pfaffian quadrics in coordinates -/

lemma kpPf0 {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b x 0 = -a * b * (x 0) ^(2:ℕ) + a ^(2:ℕ) * (x 2) * (x 3)
      - b ^(2:ℕ) * (x 1) * (x 4) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Matrix.cons_val_zero]

lemma kpPf1 {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b x 1 = -a * b * (x 2) ^(2:ℕ) + a ^(2:ℕ) * (x 0) * (x 4)
      - b ^(2:ℕ) * (x 1) * (x 3) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP1, Matrix.cons_val_one, Matrix.cons_val_zero]

lemma kpPf2 {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b x 2 = -a * b * (x 4) ^(2:ℕ) + a ^(2:ℕ) * (x 1) * (x 2)
      - b ^(2:ℕ) * (x 0) * (x 3) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP2, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

lemma kpPf3 {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b x 3 = -a * b * (x 1) ^(2:ℕ) + a ^(2:ℕ) * (x 3) * (x 4)
      - b ^(2:ℕ) * (x 0) * (x 2) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP3, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

lemma kpPf4 {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinP a b x 4 = -a * b * (x 3) ^(2:ℕ) + a ^(2:ℕ) * (x 0) * (x 1)
      - b ^(2:ℕ) * (x 2) * (x 4) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP4, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-! ## The scaled coordinates -/

lemma kpKappaHat_0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpKappaHat K u L 0 = kpK0 K u L := by simp [kpKappaHat]

lemma kpScal_0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L 0 = kpK0 K u L := by
  rw [kpBridge K u L hw 0, kpKappaHat_0]

lemma kpKappaHat_1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpKappaHat K u L 1 = kpK1 K u L := by simp [kpKappaHat]

lemma kpScal_1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L 1 = kpK1 K u L := by
  rw [kpBridge K u L hw 1, kpKappaHat_1]

lemma kpKappaHat_2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpKappaHat K u L 2 = kpK2 K u L := by simp [kpKappaHat]

lemma kpScal_2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L 2 = kpK2 K u L := by
  rw [kpBridge K u L hw 2, kpKappaHat_2]

lemma kpKappaHat_3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpKappaHat K u L 3 = kpK3 K u L := by simp [kpKappaHat]

lemma kpScal_3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L 3 = kpK3 K u L := by
  rw [kpBridge K u L hw 3, kpKappaHat_3]

lemma kpKappaHat_4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpKappaHat K u L 4 = kpK4 K u L := by simp [kpKappaHat]

lemma kpScal_4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(2:ℕ) * kpKap K u L 4 = kpK4 K u L := by
  rw [kpBridge K u L hw 4, kpKappaHat_4]

/-! ## The polynomial identities -/

lemma kpPoly_0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) *
        (-((kpUF K u L) * 1 * (kpK0 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK2 K u L) * (kpK3 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK4 K u L))
      = kpQhat0 K u L * kpWhatF K u L := by
  dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpQhat0, kpWhatF, kpLambdaF, kpAhat1F,
    kpAhat2F, kpAhat3F, kpAhat4F, kpAhat6F, kpUF, kpWF, kpDF, kpX, kpY]
  refl_ring1

lemma kpPoly_1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) *
        (-((kpUF K u L) * 1 * (kpK2 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK4 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK3 K u L))
      = kpQhat1 K u L * kpWhatF K u L := by
  dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpQhat1, kpWhatF, kpLambdaF, kpAhat1F,
    kpAhat2F, kpAhat3F, kpAhat4F, kpAhat6F, kpUF, kpWF, kpDF, kpX, kpY]
  refl_ring1

lemma kpPoly_2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) *
        (-((kpUF K u L) * 1 * (kpK4 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK2 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK3 K u L))
      = kpQhat2 K u L * kpWhatF K u L := by
  dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpQhat2, kpWhatF, kpLambdaF, kpAhat1F,
    kpAhat2F, kpAhat3F, kpAhat4F, kpAhat6F, kpUF, kpWF, kpDF, kpX, kpY]
  refl_ring1

lemma kpPoly_3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) *
        (-((kpUF K u L) * 1 * (kpK1 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK3 K u L) * (kpK4 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK2 K u L))
      = kpQhat3 K u L * kpWhatF K u L := by
  dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpQhat3, kpWhatF, kpLambdaF, kpAhat1F,
    kpAhat2F, kpAhat3F, kpAhat4F, kpAhat6F, kpUF, kpWF, kpDF, kpX, kpY]
  refl_ring1

lemma kpPoly_4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) *
        (-((kpUF K u L) * 1 * (kpK3 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK1 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK2 K u L) * (kpK4 K u L))
      = kpQhat4 K u L * kpWhatF K u L := by
  dsimp only [kpK0, kpK1, kpK2, kpK3, kpK4, kpQhat4, kpWhatF, kpLambdaF, kpAhat1F,
    kpAhat2F, kpAhat3F, kpAhat4F, kpAhat6F, kpUF, kpWF, kpDF, kpX, kpY]
  refl_ring1

/-! ## Scaling the Pfaffian quadrics -/

lemma kpKey_0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4))
      = -((kpUF K u L) * 1 * (kpK0 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK2 K u L) * (kpK3 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK4 K u L) := by
  rw [show (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4))
      = -((kpUF K u L) * 1 * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 0) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 2) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 3)
        - (1 : kpFF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 1) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 4) by ring]
  rw [kpScal_0 K u L hw, kpScal_1 K u L hw, kpScal_2 K u L hw, kpScal_3 K u L hw,
    kpScal_4 K u L hw]

lemma kpKey_1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3))
      = -((kpUF K u L) * 1 * (kpK2 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK4 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK3 K u L) := by
  rw [show (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3))
      = -((kpUF K u L) * 1 * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 2) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 0) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 1) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 3) by ring]
  rw [kpScal_0 K u L hw, kpScal_1 K u L hw, kpScal_2 K u L hw, kpScal_3 K u L hw,
    kpScal_4 K u L hw]

lemma kpKey_2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3))
      = -((kpUF K u L) * 1 * (kpK4 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK1 K u L) * (kpK2 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK3 K u L) := by
  rw [show (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3))
      = -((kpUF K u L) * 1 * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 4) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 1) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 2)
        - (1 : kpFF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 0) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 3) by ring]
  rw [kpScal_0 K u L hw, kpScal_1 K u L hw, kpScal_2 K u L hw, kpScal_3 K u L hw,
    kpScal_4 K u L hw]

lemma kpKey_3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2))
      = -((kpUF K u L) * 1 * (kpK1 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK3 K u L) * (kpK4 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK2 K u L) := by
  rw [show (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2))
      = -((kpUF K u L) * 1 * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 1) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 3) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 0) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 2) by ring]
  rw [kpScal_0 K u L hw, kpScal_1 K u L hw, kpScal_2 K u L hw, kpScal_3 K u L hw,
    kpScal_4 K u L hw]

lemma kpKey_4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (hw : Work.MotT.kpW K u ≠ 0) :
    (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4))
      = -((kpUF K u L) * 1 * (kpK3 K u L) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpK0 K u L) * (kpK1 K u L)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpK2 K u L) * (kpK4 K u L) := by
  rw [show (kpWF K u L) ^(4:ℕ) *
        (-((kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4))
      = -((kpUF K u L) * 1 * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 3) ^(2:ℕ))
        + (kpUF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 0) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 1)
        - (1 : kpFF K u L) ^(2:ℕ) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 2) * ((kpWF K u L) ^(2:ℕ) * kpKap K u L 4) by ring]
  rw [kpScal_0 K u L hw, kpScal_1 K u L hw, kpScal_2 K u L hw, kpScal_3 K u L hw,
    kpScal_4 K u L hw]

theorem kpData_klein_eq (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K)
    (hu : u ≠ 0) (hw : Work.MotT.kpW K u ≠ 0) (hΔ : Work.MotT.kpDelta K u ≠ 0) :
    ∀ (L : Type) [Field L] [Algebra K L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap K (WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpE K u).baseChange L)) u)
        (algebraMap K (WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpE K u).baseChange L)) 1)
        (Work.MotV.kleinCoord (Work.MotT.kpData K u) L) k = 0 := by
  intro L _ _ k
  have hUnz : algebraMap K (kpFF K u L) u ≠ 0 := fun h =>
    hu ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hWnz : kpWF K u L ≠ 0 := by
    rw [kpWF_eq]
    exact fun h => hw ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one h1).elim
    · exact hk h5
  have h5F : (5 : kpFF K u L) ≠ 0 := by
    rw [show (5 : kpFF K u L) = algebraMap K (kpFF K u L) (5 : K) from
      (map_ofNat (algebraMap K (kpFF K u L)) 5).symm]
    exact fun h => h5K ((FaithfulSMul.algebraMap_eq_zero_iff K (kpFF K u L)).mp h)
  have hne : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 9 h5F) (pow_ne_zero 12 hUnz)) (pow_ne_zero 4 hWnz)
  have hWhat : kpWhatF K u L = 0 := by
    rw [kpWhatF_eq K u L hu hw hk, kpWrel_eq_zero, mul_zero]
  change Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
    (Work.MotV.kleinCoord (kpData K u) L) k = 0
  rw [kleinCoord_eq_kpKap K u L]
  fin_cases k
  · show Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
      (kpKap K u L) 0 = 0
    rw [kpPf0]
    simp only [map_one]
    change -(kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4) = 0
    have h4 : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
        (-(kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4)) = 0 := by
      rw [show 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
          (-(kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ)
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4))
          = 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * ((kpWF K u L) ^(4:ℕ) *
          (-((kpUF K u L) * 1 * (kpKap K u L 0) ^(2:ℕ))
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 3)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 4))) by ring]
      rw [kpKey_0 K u L hw, kpPoly_0 K u L, hWhat, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left hne
  · show Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
      (kpKap K u L) 1 = 0
    rw [kpPf1]
    simp only [map_one]
    change -(kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3) = 0
    have h4 : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
        (-(kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3)) = 0 := by
      rw [show 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
          (-(kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ)
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3))
          = 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * ((kpWF K u L) ^(4:ℕ) *
          (-((kpUF K u L) * 1 * (kpKap K u L 2) ^(2:ℕ))
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 4)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 3))) by ring]
      rw [kpKey_1 K u L hw, kpPoly_1 K u L, hWhat, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left hne
  · show Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
      (kpKap K u L) 2 = 0
    rw [kpPf2]
    simp only [map_one]
    change -(kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3) = 0
    have h4 : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
        (-(kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3)) = 0 := by
      rw [show 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
          (-(kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ)
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3))
          = 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * ((kpWF K u L) ^(4:ℕ) *
          (-((kpUF K u L) * 1 * (kpKap K u L 4) ^(2:ℕ))
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 1) * (kpKap K u L 2)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 3))) by ring]
      rw [kpKey_2 K u L hw, kpPoly_2 K u L, hWhat, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left hne
  · show Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
      (kpKap K u L) 3 = 0
    rw [kpPf3]
    simp only [map_one]
    change -(kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2) = 0
    have h4 : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
        (-(kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2)) = 0 := by
      rw [show 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
          (-(kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ)
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2))
          = 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * ((kpWF K u L) ^(4:ℕ) *
          (-((kpUF K u L) * 1 * (kpKap K u L 1) ^(2:ℕ))
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 3) * (kpKap K u L 4)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 2))) by ring]
      rw [kpKey_3 K u L hw, kpPoly_3 K u L, hWhat, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left hne
  · show Work.MotK.kleinP (algebraMap K (kpFF K u L) u) (algebraMap K (kpFF K u L) 1)
      (kpKap K u L) 4 = 0
    rw [kpPf4]
    simp only [map_one]
    change -(kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4) = 0
    have h4 : 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
        (-(kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ)
        + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
        - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4)) = 0 := by
      rw [show 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(4:ℕ) *
          (-(kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ)
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4))
          = 5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * ((kpWF K u L) ^(4:ℕ) *
          (-((kpUF K u L) * 1 * (kpKap K u L 3) ^(2:ℕ))
          + (kpUF K u L) ^(2:ℕ) * (kpKap K u L 0) * (kpKap K u L 1)
          - (1 : kpFF K u L) ^(2:ℕ) * (kpKap K u L 2) * (kpKap K u L 4))) by ring]
      rw [kpKey_4 K u L hw, kpPoly_4 K u L, hWhat, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left hne

end
end Work.MotT
