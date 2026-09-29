import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.SeqUtil

/-!
# Shape lemmas for the cost bound of Theorem 3.1

Each `shape*` lemma turns a bound on a "shape" (an expression built from `T`, `p`, `r`, `V`) into
the canonical `K * (3000000 * S)` form required by `Work.Transform.costAbsorb`.  They are stated
in a *small* context so that the nonlinear arithmetic is fast; the assembly calls them by `exact`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- `X ≤ S` implies `K * X + K ≤ K * (3000000 * S) + K`. -/
theorem shapeOne {K X S : ℕ} (h : X ≤ S) : K * X + K ≤ K * (3000000 * S) + K := by
  have hS : S ≤ 3000000 * S := by
    calc S = 1 * S := (one_mul S).symm
      _ ≤ 3000000 * S := Nat.mul_le_mul_right S (by norm_num)
  exact add_le_add (Nat.mul_le_mul_left K (le_trans h hS)) (le_refl K)

/-- `X ≤ 2 * S` implies `K * X + K ≤ K * (3000000 * S) + K`. -/
theorem shapeTwo {K X S : ℕ} (h : X ≤ 2 * S) : K * X + K ≤ K * (3000000 * S) + K := by
  have h2 : 2 * S ≤ 3000000 * S := Nat.mul_le_mul_right S (by norm_num)
  exact add_le_add (Nat.mul_le_mul_left K (le_trans h h2)) (le_refl K)

/-- Roll shape: `Kr * k * (R + 1)` with `R ≤ k * V`, `V ≤ 100 * S`, `k ≤ 9`. -/
theorem shapeRoll {Kr V R S k : ℕ} (hk : k ≤ 9) (hR : R ≤ k * V) (hV : V ≤ 100 * S)
    (hS : 1 ≤ S) : Kr * k * (R + 1) ≤ Kr * (3000000 * S) := by
  rw [mul_assoc]
  refine Nat.mul_le_mul_left Kr ?_
  nlinarith [hk, hR, hV, hS]

/-- Five-value sum shape. -/
theorem shapeAdd5 {Kr V a b c d e S : ℕ} (ha : a ≤ V) (hb : b ≤ V) (hc : c ≤ V) (hd : d ≤ V)
    (he : e ≤ V) (hV : V ≤ 100 * S) (hS : 1 ≤ S) :
    Kr * (a + b + c + d + e + 1) + Kr ≤ Kr * (3000000 * S) + Kr := by
  have h : a + b + c + d + e + 1 ≤ 3000000 * S := by nlinarith [ha, hb, hc, hd, he, hV, hS]
  exact add_le_add (Nat.mul_le_mul_left Kr h) (le_refl Kr)

/-- Eight-value sum times `3000` (the `arrangeWord` shape). -/
theorem shapeArr {Ka V a b c d e f g h S : ℕ} (h1 : a ≤ V) (h2 : b ≤ V) (h3 : c ≤ V)
    (h4 : d ≤ V) (h5 : e ≤ V) (h6 : f ≤ V) (h7 : g ≤ V) (h8 : h ≤ V) (hV : V ≤ 100 * S)
    (hS : 1 ≤ S) :
    Ka * ((((a + b) + c) + d + e + f + g + h) * 3000 + 1) + Ka ≤
      Ka * (3000000 * S) + Ka := by
  have h : ((((a + b) + c) + d + e + f + g + h) * 3000 + 1) ≤ 3000000 * S := by
    nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, hV, hS]
  exact add_le_add (Nat.mul_le_mul_left Ka h) (le_refl Ka)

/-- Four terms plus one (the `ztabWord` shape): the first two are bounded by `S`, the last two
by a size bound `V ≤ 100 * S`. -/
theorem shapeSum4 {K a b c d S V : ℕ} (h1 : a ≤ S) (h2 : b ≤ S) (h3 : c ≤ V) (h4 : d ≤ V)
    (hV : V ≤ 100 * S) (h5 : 1 ≤ S) : K * (a + b + c + d + 1) + K ≤ K * (3000000 * S) + K := by
  have h : a + b + c + d + 1 ≤ 3000000 * S := by nlinarith [h1, h2, h3, h4, hV, h5]
  exact add_le_add (Nat.mul_le_mul_left K h) (le_refl K)

/-- Pointwise-product shape `T * p^2 + p + 1`. -/
theorem shapeMul {K T p S : ℕ} (h1 : T * p ^ 2 ≤ S) (h2 : p ≤ S) (h3 : 1 ≤ S) :
    K * (T * p ^ 2 + p + 1) + K ≤ K * (3000000 * S) + K := by
  have h : T * p ^ 2 + p + 1 ≤ 3000000 * S := by nlinarith [h1, h2, h3]
  exact add_le_add (Nat.mul_le_mul_left K h) (le_refl K)

/-- Array-map shape `(M*r) * p^2 + p + r + 1`. -/
theorem shapePhi {K M r p S : ℕ} (h1 : (M * r) * p ^ 2 ≤ S) (h2 : p ≤ S) (h3 : r ≤ S)
    (h4 : 1 ≤ S) : K * ((M * r) * p ^ 2 + p + r + 1) + K ≤ K * (3000000 * S) + K := by
  have h : (M * r) * p ^ 2 + p + r + 1 ≤ 3000000 * S := by nlinarith [h1, h2, h3, h4]
  exact add_le_add (Nat.mul_le_mul_left K h) (le_refl K)

/-- `(p+1)^Ki ≤ (p+1)^KB` when `Ki ≤ KB`. -/
theorem pow_succ_base {p Ki KB : ℕ} (h : Ki ≤ KB) : (p + 1) ^ Ki ≤ (p + 1) ^ KB :=
  Nat.pow_le_pow_right (Nat.succ_pos p) h

/-- Each of the ten area constants is at most their sum plus the slack `100`. -/
theorem le_exp_1 (a b c d e f g h i j : ℕ) :
    a ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_2 (a b c d e f g h i j : ℕ) :
    b ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_3 (a b c d e f g h i j : ℕ) :
    c ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_4 (a b c d e f g h i j : ℕ) :
    d ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_5 (a b c d e f g h i j : ℕ) :
    e ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_6 (a b c d e f g h i j : ℕ) :
    f ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_7 (a b c d e f g h i j : ℕ) :
    g ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_8 (a b c d e f g h i j : ℕ) :
    h ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_9 (a b c d e f g h i j : ℕ) :
    i ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega
theorem le_exp_10 (a b c d e f g h i j : ℕ) :
    j ≤ a + b + c + d + e + f + g + h + i + j + 100 := by omega

theorem le_sum_1 (a b c d e f g h i j : ℕ) :
    a ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_2 (a b c d e f g h i j : ℕ) :
    b ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_3 (a b c d e f g h i j : ℕ) :
    c ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_4 (a b c d e f g h i j : ℕ) :
    d ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_5 (a b c d e f g h i j : ℕ) :
    e ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_6 (a b c d e f g h i j : ℕ) :
    f ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_7 (a b c d e f g h i j : ℕ) :
    g ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_8 (a b c d e f g h i j : ℕ) :
    h ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_9 (a b c d e f g h i j : ℕ) :
    i ≤ a + b + c + d + e + f + g + h + i + j := by omega
theorem le_sum_10 (a b c d e f g h i j : ℕ) :
    j ≤ a + b + c + d + e + f + g + h + i + j := by omega

end Work.Transform
