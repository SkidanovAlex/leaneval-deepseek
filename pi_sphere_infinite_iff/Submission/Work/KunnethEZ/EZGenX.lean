import Mathlib
import Submission.Work.KunnethEZ.EZComb

/-!
# The general Eilenberg–Zilber chain-map identity for the shuffle chain

Let `p = P + 1` and `q = Q + 1`.  Working in this "successor" shape makes the natural-number
subtractions `(p - 1) + 1 = p`, `(p + q - 1) + 1 = p + q` definitional, which is what allows the
simplicial face maps `SimplexCategory.δ` to be composed at these degrees.

This file develops

* the `X`-side bijection: a `(p-1,q)`-shuffle `T` together with a face index `i : Fin (p+1)` gives
  a `(p,q)`-shuffle `SX i T` and an `X`-boundary face `jX i T` of it;
* the `Y`-side mirror, with `SY`, `jY`;
* the sign and face-matching lemmas for both;
* the assembly of the Eilenberg–Zilber chain-map identity.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.KunnethEZ

open Work.Cohomology.Crux33

noncomputable section

variable {P Q : ℕ}

local notation "p" => P + 1
local notation "q" => Q + 1

/-! ## The vertex evaluation of a face -/

lemma delta_val {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) :
    ((SimplexCategory.δ j) k).val = delV j.val k.val := by
  rw [SimplexCategory.δ]
  show (j.succAbove k).val = delV j.val k.val
  rw [delV]
  by_cases h : k.val < j.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt j k (by show k.val < j.val; exact h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc j k (by show j.val ≤ k.val; omega)]
    rfl

lemma comp_val {m n l : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋n⦌ ⟶ ⦋l⦌) (k : Fin (m + 1)) :
    ((f ≫ g) k).val = (g (f k)).val := rfl

lemma pA_eq_ANat {n m : ℕ} (S : Finset (Fin (n + m))) (i : Fin (n + m + 1)) :
    pA S i = ANat S i.val := rfl

lemma pB_eq_BNat {n m : ℕ} (S : Finset (Fin (n + m))) (i : Fin (n + m + 1)) :
    pB S i = BNat S i.val := rfl

lemma delV_lt {j k : ℕ} (h : k < j) : delV j k = k := if_pos h

lemma delV_ge {j k : ℕ} (h : ¬ k < j) : delV j k = k + 1 := if_neg h

lemma delV_ne {j k : ℕ} : delV j k ≠ j := by
  rw [delV]
  by_cases h : k < j
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

lemma delV_succ {j k : ℕ} (h : ¬ k < j) : delV j k - 1 = k := by
  rw [delV_ge h]; omega

/-! ## The `X`-side: inserting an `E`-step -/

lemma ANat_exists_ge (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    ∃ m, ANat T.1 m ≥ i.val := by
  refine ⟨p + q - 1, ?_⟩
  have h2 := ANat_add_BNat T.1 (p + q - 1)
  rw [BNat_last, T.2, min_self] at h2
  have hcard := T.1.card_le_univ
  rw [T.2, Fintype.card_fin] at hcard
  omega

noncomputable def jX0 (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) : ℕ :=
  Nat.find (ANat_exists_ge i T h)

lemma jX0_spec (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    ANat T.1 (jX0 i T h) ≥ i.val :=
  Nat.find_spec (ANat_exists_ge i T h)

lemma jX0_min (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) {m : ℕ}
    (hm : m < jX0 i T h) : ANat T.1 m < i.val :=
  not_le.mp (Nat.find_min (ANat_exists_ge i T h) hm)

lemma jX0_le (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    jX0 i T h ≤ p + q - 1 := by
  refine Nat.find_min' (ANat_exists_ge i T h) ?_
  have h2 := ANat_add_BNat T.1 (p + q - 1)
  rw [BNat_last, T.2, min_self] at h2
  have hcard := T.1.card_le_univ
  rw [T.2, Fintype.card_fin] at hcard
  omega

lemma jX0_val (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    ANat T.1 (jX0 i T h) = i.val := by
  rcases Nat.eq_zero_or_pos (jX0 i T h) with h0 | hpos
  · have h3 := jX0_spec i T h
    rw [h0, ANat_zero] at h3 ⊢
    omega
  · have h1 := ANat_succ T.1 (show jX0 i T h - 1 < p + q - 1 by
      have := jX0_le i T h; omega)
    rw [show jX0 i T h - 1 + 1 = jX0 i T h from by omega] at h1
    have h2 := jX0_min i T h (show jX0 i T h - 1 < jX0 i T h by omega)
    have h3 := jX0_spec i T h
    by_cases hmem : (⟨jX0 i T h - 1, by have := jX0_le i T h; omega⟩ : Fin (p + q - 1)) ∈ T.1
    · rw [if_pos hmem] at h1
      omega
    · rw [if_neg hmem] at h1
      omega

noncomputable def jX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : ℕ :=
  if h : i.val < p then jX0 i T h else p + q

lemma jX_eq_jX0 (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    jX i T = jX0 i T h := by
  rw [jX, dif_pos h]

lemma jX_eq_last (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : ¬ i.val < p) :
    jX i T = p + q := by
  rw [jX, dif_neg h]

lemma jX_le (i : Fin (p - 1 + 2)) (T : Sh23 p q) : jX i T ≤ p + q := by
  rw [jX]
  by_cases h : i.val < p
  · rw [dif_pos h]; have := jX0_le i T h; omega
  · rw [dif_neg h]

lemma jX_value (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    ANat T.1 (jX i T) = i.val := by
  rw [jX_eq_jX0 i T h]; exact jX0_val i T h

lemma jX_min (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) {m : ℕ}
    (hm : m < jX i T) : ANat T.1 m < i.val := by
  rw [jX_eq_jX0 i T h] at hm
  exact jX0_min i T h hm

lemma ANat_le_self {n : ℕ} (S : Finset (Fin n)) (m : ℕ) : ANat S m ≤ m :=
  le_trans (ANat_le S m) (min_le_left _ _)

noncomputable def posX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : Fin (p + q) :=
  ⟨min (jX i T) (p + q - 1), by
    have h1 : (min (jX i T) (p + q - 1)) ≤ p + q - 1 := min_le_right _ _
    have h2 : 0 < p + q := by omega
    omega⟩

noncomputable def SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : PShuffle p q :=
  ⟨insertE T.1 (posX i T), by rw [card_insertE]; exact T.2⟩

noncomputable def jfX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : Fin ((p + q - 1) + 2) :=
  ⟨jX i T, by have := jX_le i T; omega⟩

@[simp] lemma jfX_val (i : Fin (p - 1 + 2)) (T : Sh23 p q) : (jfX i T).val = jX i T := rfl

lemma posX_eq_jX (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : i.val < p) :
    (posX i T).val = jX i T := by
  show min (jX i T) (p + q - 1) = jX i T
  exact min_eq_left (by rw [jX_eq_jX0 i T h]; exact jX0_le i T h)

lemma posX_eq_last (i : Fin (p - 1 + 2)) (T : Sh23 p q) (h : ¬ i.val < p) :
    (posX i T).val = p + q - 1 := by
  show min (jX i T) (p + q - 1) = p + q - 1
  rw [jX_eq_last i T h]
  exact min_eq_right (Nat.sub_le (p + q) 1)

lemma le_posX_of_lt_jX (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ} (hv : v < jX i T) :
    v ≤ (posX i T).val := by
  by_cases h : i.val < p
  · rw [posX_eq_jX i T h]; exact le_of_lt hv
  · rw [posX_eq_last i T h]
    have hj : jX i T = p + q := jX_eq_last i T h
    have hk : v < p + q := by rw [← hj]; exact hv
    omega

lemma lt_posX_succ_of_le_jX (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ} (hv : jX i T ≤ v) :
    (posX i T).val < v + 1 := by
  have h1 : (posX i T).val ≤ jX i T := min_le_left _ _
  omega

lemma ANat_SX_of_le (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ}
    (hv : v ≤ (posX i T).val) : ANat (SX i T).1 v = ANat T.1 v := by
  rw [SX, ANat_insertE, if_pos hv]

lemma ANat_SX_of_gt (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ}
    (hv : (posX i T).val < v) : ANat (SX i T).1 v = ANat T.1 (v - 1) + 1 := by
  rw [SX, ANat_insertE, if_neg (by omega)]

lemma BNat_SX_of_le (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ}
    (hv : v ≤ (posX i T).val) : BNat (SX i T).1 v = BNat T.1 v := by
  rw [SX, BNat_insertE, if_pos hv]

lemma BNat_SX_of_gt (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : ℕ}
    (hv : (posX i T).val < v) : BNat (SX i T).1 v = BNat T.1 (v - 1) := by
  rw [SX, BNat_insertE, if_neg (by omega)]

lemma ANat_SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : ANat (SX i T).1 (jX i T) = i.val := by
  by_cases h : i.val < p
  · rw [ANat_SX_of_le i T (by rw [posX_eq_jX i T h])]
    exact jX_value i T h
  · have hi : i.val = p := by have := i.isLt; omega
    have hpos := posX_eq_last i T h
    have hj := jX_eq_last i T h
    have hlt : (posX i T).val < jX i T := by
      rw [hpos, hj]; omega
    rw [ANat_SX_of_gt i T hlt, hj]
    have h2 := ANat_last T.1
    rw [T.2] at h2
    rw [h2, hi]
    have h3 := ANat_add_BNat T.1 (p + q - 1)
    rw [BNat_last, T.2, min_self] at h3
    omega

lemma ANat_SX_lt (i : Fin (p - 1 + 2)) (T : Sh23 p q) {m : ℕ} (hm : m < jX i T) :
    ANat (SX i T).1 m < i.val := by
  by_cases h : i.val < p
  · rw [ANat_SX_of_le i T (le_posX_of_lt_jX i T hm)]
    exact jX_min i T h hm
  · have hi : i.val = p := by have := i.isLt; omega
    rw [ANat_SX_of_le i T (le_posX_of_lt_jX i T hm), hi]
    have h2 := ANat_last T.1
    rw [T.2] at h2
    have hmono : ANat T.1 m ≤ ANat T.1 (p + q - 1) := by
      have hk' := le_posX_of_lt_jX i T hm
      rw [posX_eq_last i T h] at hk'
      exact ANat_mono T.1 hk'
    rw [h2] at hmono
    have hcard := T.1.card_le_univ
    rw [T.2, Fintype.card_fin] at hcard
    omega

lemma ANat_SX_inj (i : Fin (p - 1 + 2)) (T : Sh23 p q) {v : Fin ((p + q - 1) + 2)}
    (hv : ANat (SX i T).1 v.val = ANat (SX i T).1 (jX i T)) : v.val = jX i T := by
  have hJ : ANat (SX i T).1 (jX i T) = i.val := ANat_SX i T
  rcases lt_trichotomy v.val (jX i T) with hlt | heq | hgt
  · exfalso
    have := ANat_SX_lt i T hlt
    omega
  · exact heq
  · exfalso
    have hgt' : i.val < ANat (SX i T).1 v.val := by
      by_cases h : i.val < p
      · have hsucc : ANat (SX i T).1 (jX i T + 1) = i.val + 1 := by
          have hlt : (posX i T).val < jX i T + 1 :=
            Nat.lt_succ_of_le (min_le_left (jX i T) (p + q - 1))
          rw [ANat_SX_of_gt i T hlt]
          have hsub : jX i T + 1 - 1 = jX i T := by omega
          rw [hsub, jX_value i T h]
        have hmono : ANat (SX i T).1 (jX i T + 1) ≤ ANat (SX i T).1 v.val :=
          ANat_mono (SX i T).1 (by omega)
        omega
      · have hj : jX i T = p + q := jX_eq_last i T h
        have h1 : p + q < v.val := by rw [hj] at hgt; exact hgt
        have h2 : v.val < p + q + 1 := v.isLt
        omega
    omega

lemma posX_notMem (i : Fin (p - 1 + 2)) (T : Sh23 p q) : (posX i T) ∉ (SX i T).1 :=
  pos_notMem_insertE T.1 (posX i T)

lemma IsBX_SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) : IsBX (SX i T).1 (jfX i T) := by
  refine value_IsBX (SX i T).1 (jfX i T) (fun v hv => ?_)
  exact Fin.ext (by rw [jfX_val]; exact ANat_SX_inj i T hv)

lemma delta_jfX_val (i : Fin (p - 1 + 2)) (T : Sh23 p q) (k : Fin ((p + q - 1) + 1)) :
    ((SimplexCategory.δ (jfX i T)) k).val = delV (jX i T) k.val := by
  rw [delta_val]
  rfl

lemma ANat_SX_delV (i : Fin (p - 1 + 2)) (T : Sh23 p q) (k : Fin ((p + q - 1) + 1)) :
    ANat (SX i T).1 (delV (jX i T) k.val) = delV i.val (ANat T.1 k.val) := by
  by_cases hk : k.val < jX i T
  · rw [delV_lt hk, ANat_SX_of_le i T (le_posX_of_lt_jX i T hk)]
    by_cases h : i.val < p
    · exact (delV_lt (jX_min i T h hk)).symm
    · have hi : i.val = p := by have := i.isLt; omega
      have h2 := ANat_last T.1
      rw [T.2] at h2
      have hmono : ANat T.1 k.val ≤ ANat T.1 (p + q - 1) := by
        have hk' := le_posX_of_lt_jX i T hk
        rw [posX_eq_last i T h] at hk'
        exact ANat_mono T.1 hk'
      rw [h2] at hmono
      have hcard := T.1.card_le_univ
      rw [T.2, Fintype.card_fin] at hcard
      rw [hi, delV_lt (by omega)]
  · rw [delV_ge hk, ANat_SX_of_gt i T (lt_posX_succ_of_le_jX i T (not_lt.mp hk)),
      show k.val + 1 - 1 = k.val from by omega]
    by_cases h : i.val < p
    · rw [delV_ge (by
        have hmono : ANat T.1 (jX i T) ≤ ANat T.1 k.val :=
          ANat_mono T.1 (not_lt.mp hk)
        rw [jX_value i T h] at hmono
        omega)]
    · have hj : jX i T = p + q := jX_eq_last i T h
      rw [hj] at hk
      omega

lemma BNat_SX_delV (i : Fin (p - 1 + 2)) (T : Sh23 p q) (k : Fin ((p + q - 1) + 1)) :
    BNat (SX i T).1 (delV (jX i T) k.val) = BNat T.1 k.val := by
  by_cases hk : k.val < jX i T
  · rw [delV_lt hk, BNat_SX_of_le i T (le_posX_of_lt_jX i T hk)]
  · rw [delV_ge hk, BNat_SX_of_gt i T (lt_posX_succ_of_le_jX i T (not_lt.mp hk)),
      show k.val + 1 - 1 = k.val from by omega]

lemma aFace_SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) :
    SimplexCategory.δ (jfX i T) ≫ @aHom (P + 1) (Q + 1) (SX i T).1 (SX i T).2
      = aMap23 p q T ≫ SimplexCategory.δ i := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  refine Fin.ext ?_
  show ((SimplexCategory.δ (jfX i T) ≫ @aHom (P + 1) (Q + 1) (SX i T).1 (SX i T).2) k).val
      = ((aMap23 p q T ≫ SimplexCategory.δ i) k).val
  rw [comp_val, comp_val, aHom_val, pA_eq_ANat, delta_jfX_val, delta_val, aMap23_apply]
  exact ANat_SX_delV i T k

lemma bFace_SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) :
    SimplexCategory.δ (jfX i T) ≫ @bHom (P + 1) (Q + 1) (SX i T).1 (SX i T).2 = bMap23 p q T := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  refine Fin.ext ?_
  show ((SimplexCategory.δ (jfX i T) ≫ @bHom (P + 1) (Q + 1) (SX i T).1 (SX i T).2) k).val
      = ((bMap23 p q T) k).val
  rw [comp_val, bHom_val, pB_eq_BNat, delta_jfX_val, bMap23_apply]
  exact BNat_SX_delV i T k

/-! ## The sign of the `X`-side insertion -/

lemma neg_one_pow_add_two_mul (i k : ℕ) : (-1 : ℤ) ^ (i + 2 * k) = (-1) ^ i := by
  rw [pow_add, pow_mul, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_pow, mul_one]

lemma BNat_posX_add_jX (i : Fin (p - 1 + 2)) (T : Sh23 p q) :
    ∃ k, BNat T.1 (posX i T).val + jX i T = i.val + 2 * k := by
  by_cases h : i.val < p
  · refine ⟨jX i T - i.val, ?_⟩
    have hJ := jX_eq_jX0 i T h
    have hJle : jX i T ≤ p + q - 1 := by rw [hJ]; exact jX0_le i T h
    have hpos : (posX i T).val = jX i T := posX_eq_jX i T h
    rw [hpos]
    have hsum : ANat T.1 (jX i T) + BNat T.1 (jX i T) = jX i T := by
      have h2 := ANat_add_BNat T.1 (jX i T)
      rw [min_eq_left hJle] at h2
      exact h2
    have hval : ANat T.1 (jX i T) = i.val := jX_value i T h
    have hile : i.val ≤ jX i T := by rw [← hval]; exact ANat_le_self T.1 (jX i T)
    omega
  · refine ⟨q, ?_⟩
    have hi : i.val = p := by have := i.isLt; omega
    have hj := jX_eq_last i T h
    have hpos := posX_eq_last i T h
    have h2 := BNat_last T.1
    rw [T.2] at h2
    rw [hpos, hj, hi]
    omega

lemma shufSign_SX (i : Fin (p - 1 + 2)) (T : Sh23 p q) :
    @shufSign (P + 1) (Q + 1) (SX i T).1 * (-1 : ℤ) ^ (jfX i T).val
      = (-1 : ℤ) ^ (i.val) * shufSignN T.1 := by
  rw [jfX_val]
  obtain ⟨k, hk⟩ := BNat_posX_add_jX i T
  have hexp : invCountN T.1 + BNat T.1 (posX i T).val + jX i T
      = (i.val + invCountN T.1) + 2 * k := by omega
  have hsig : @shufSign (P + 1) (Q + 1) (SX i T).1 = shufSignN (SX i T).1 :=
    @shufSign_eq_shufSignN (P + 1) (Q + 1) _
  have hins : invCountN (SX i T).1 = invCountN T.1 + BNat T.1 (posX i T).val :=
    invCountN_insertE T.1 (posX i T)
  calc @shufSign (P + 1) (Q + 1) (SX i T).1 * (-1 : ℤ) ^ (jX i T)
      = (-1 : ℤ) ^ (invCountN (SX i T).1) * (-1 : ℤ) ^ (jX i T) := by rw [hsig, shufSignN]
    _ = (-1 : ℤ) ^ (invCountN T.1 + BNat T.1 (posX i T).val + jX i T) := by
        rw [hins, ← pow_add]
    _ = (-1 : ℤ) ^ ((i.val + invCountN T.1) + 2 * k) := by rw [hexp]
    _ = (-1 : ℤ) ^ (i.val + invCountN T.1) := neg_one_pow_add_two_mul _ _
    _ = (-1 : ℤ) ^ (i.val) * shufSignN T.1 := by rw [pow_add]; rfl


/-! ## Deleting an `E`-step back out -/

lemma erase_eq_self {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (h : pos ∉ S) :
    S.erase pos = S := by
  ext k
  rw [Finset.mem_erase]
  constructor
  · rintro ⟨-, hk⟩; exact hk
  · intro hk; exact ⟨fun hkp => h (hkp ▸ hk), hk⟩

lemma card_deleteE {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (h : pos ∉ S) :
    (deleteE S pos).card = S.card := by
  have h1 : (insertE (deleteE S pos) pos).card = (deleteE S pos).card := card_insertE _ _
  rw [insertE_deleteE S pos, erase_eq_self S pos h] at h1
  exact h1.symm

/-- The number of `E`-steps before the vertex `j` of a shuffle, as a `ℕ`-indexed count. -/
lemma ANat_deleteE_le {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) {m : ℕ} (hm : m ≤ pos.val) :
    ANat (deleteE S pos) m = ANat S m := by
  rw [ANat, ANat]
  refine Finset.card_bij (fun k _ => (⟨k.val, by have := k.isLt; omega⟩ : Fin N)) ?_ ?_ ?_
  · rintro k hk
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    obtain ⟨hklt, hknd⟩ := hk
    rw [mem_deleteE] at hknd
    rw [insIdx_lt pos k (by omega)] at hknd
    exact ⟨hklt, hknd⟩
  · intro k1 hk1 k2 hk2 heq
    exact Fin.ext (by simpa using congrArg Fin.val heq)
  · rintro b hb
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hblt, hbS⟩ := hb
    have hbpos : b.val < pos.val := by omega
    have hbN : b.val < N - 1 := by have := pos.isLt; omega
    refine ⟨⟨b.val, hbN⟩, ?_, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hblt, ?_⟩
    rw [mem_deleteE, insIdx_lt pos ⟨b.val, hbN⟩ (by simpa using hbpos)]
    exact hbS

/-- The vertex of a shuffle cell at which the `X`-boundary face is taken. -/
noncomputable def posOf (j : Fin (p + q + 1)) : Fin (p + q) :=
  ⟨min j.val (p + q - 1), by
    have h1 : (min j.val (p + q - 1)) ≤ p + q - 1 := min_le_right _ _
    have h2 : 0 < p + q := by omega
    omega⟩

@[simp] lemma posOf_val (j : Fin (p + q + 1)) : (posOf j).val = min j.val (p + q - 1) := rfl

lemma posOf_notMem (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    posOf j ∉ S.1 :=
  IsBX_pos_notMem (by omega) S.1 j h

lemma ANat_le_p_of_IsBX (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    ANat S.1 j.val ≤ p := by
  calc ANat S.1 j.val ≤ ANat S.1 (p + q) := ANat_mono S.1 (by have := j.isLt; omega)
    _ = p := by rw [ANat_last, S.2]; omega

lemma ANat_lt_p_of_IsBX (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j)
    (hj : j.val < p + q) : ANat S.1 j.val < p := by
  have h1 := ANat_succ S.1 (m := j.val) (by omega)
  rw [if_neg (fun hc => h ⟨j.val, _⟩ (Or.inr rfl) hc)] at h1
  have h2 : ANat S.1 (j.val + 1) ≤ ANat S.1 (p + q) := ANat_mono S.1 (by omega)
  rw [ANat_last, S.2] at h2
  omega

/-- The `(p-1,q)`-shuffle obtained by deleting the `E`-step at the `X`-boundary vertex. -/
noncomputable def bwdT (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) : Sh23 p q :=
  ⟨deleteE S.1 (posOf j), by rw [card_deleteE S.1 (posOf j) (posOf_notMem S j h), S.2]⟩

/-- The face index matched with the `X`-boundary vertex. -/
noncomputable def bwdI (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    Fin (p - 1 + 2) :=
  ⟨ANat S.1 j.val, by have := ANat_le_p_of_IsBX S j h; omega⟩

@[simp] lemma bwdT_val (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    (bwdT S j h).1 = deleteE S.1 (posOf j) := rfl

@[simp] lemma bwdI_val (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    (bwdI S j h).val = ANat S.1 j.val := rfl

lemma jX_bwdT (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    jX (bwdI S j h) (bwdT S j h) = j.val := by
  by_cases hj : j.val < p + q
  · have hlt : (bwdI S j h).val < p := by
      rw [bwdI_val]; exact ANat_lt_p_of_IsBX S j h hj
    rw [jX_eq_jX0 _ _ hlt]
    have hle : jX0 (bwdI S j h) (bwdT S j h) hlt ≤ j.val :=
      Nat.find_min' (ANat_exists_ge (bwdI S j h) (bwdT S j h) hlt) (by
        rw [bwdT_val, bwdI_val, ANat_deleteE_le S.1 (posOf j) (by rw [posOf_val]; omega)])
    have hge : j.val ≤ jX0 (bwdI S j h) (bwdT S j h) hlt := by
      show j.val ≤ Nat.find _
      rw [Nat.le_find_iff]
      intro m hm
      rw [bwdT_val, bwdI_val, ANat_deleteE_le S.1 (posOf j) (by rw [posOf_val]; omega)]
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · omega
      · have h2 : ANat S.1 j.val = ANat S.1 (j.val - 1) + 1 := by
          have h3 := ANat_succ S.1 (m := j.val - 1) (by omega)
          rw [show j.val - 1 + 1 = j.val from by omega,
            if_neg (fun hc => h ⟨j.val - 1, _⟩ (Or.inl rfl) hc)] at h3
          exact h3
        have h4 : ANat S.1 m ≤ ANat S.1 (j.val - 1) := ANat_mono S.1 (by omega)
        omega
    omega
  · have hjE : j.val = p + q := by have := j.isLt; omega
    have hge : ¬ (bwdI S j h).val < p := by
      rw [bwdI_val]
      have h2 : ANat S.1 j.val = p := by
        rw [hjE, ANat_last, S.2]; omega
      omega
    rw [jX_eq_last _ _ hge]
    exact hjE.symm

lemma SX_bwdT (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBX S.1 j) :
    SX (bwdI S j h) (bwdT S j h) = S := by
  have hpos : posX (bwdI S j h) (bwdT S j h) = posOf j := by
    refine Fin.ext ?_
    rw [posOf_val]
    show min (jX (bwdI S j h) (bwdT S j h)) (p + q - 1) = min j.val (p + q - 1)
    rw [jX_bwdT S j h]
  refine Subtype.ext ?_
  show insertE (bwdT S j h).1 (posX (bwdI S j h) (bwdT S j h)) = S.1
  rw [hpos, bwdT_val, insertE_deleteE, erase_eq_self S.1 (posOf j) (posOf_notMem S j h)]


/-! ## The `Y`-side: inserting an `N`-step -/

lemma BNat_exists_ge (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    ∃ m, BNat U.1 m ≥ j.val := by
  refine ⟨p + q - 1, ?_⟩
  rw [BNat_last, U.2]
  omega

noncomputable def jY0 (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) : ℕ :=
  Nat.find (BNat_exists_ge j U h)

lemma jY0_spec (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    BNat U.1 (jY0 j U h) ≥ j.val :=
  Nat.find_spec (BNat_exists_ge j U h)

lemma jY0_min (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) {m : ℕ}
    (hm : m < jY0 j U h) : BNat U.1 m < j.val :=
  not_le.mp (Nat.find_min (BNat_exists_ge j U h) hm)

lemma jY0_le (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    jY0 j U h ≤ p + q - 1 := by
  refine Nat.find_min' (BNat_exists_ge j U h) ?_
  rw [BNat_last, U.2]
  omega

lemma jY0_val (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    BNat U.1 (jY0 j U h) = j.val := by
  rcases Nat.eq_zero_or_pos (jY0 j U h) with h0 | hpos
  · have h3 := jY0_spec j U h
    rw [h0, BNat_zero] at h3 ⊢
    omega
  · have h1 := BNat_succ U.1 (show jY0 j U h - 1 < p + q - 1 by
      have := jY0_le j U h; omega)
    rw [show jY0 j U h - 1 + 1 = jY0 j U h from by omega] at h1
    have h2 := jY0_min j U h (show jY0 j U h - 1 < jY0 j U h by omega)
    have h3 := jY0_spec j U h
    by_cases hmem : (⟨jY0 j U h - 1, by have := jY0_le j U h; omega⟩ : Fin (p + q - 1)) ∈ U.1
    · rw [if_pos hmem] at h1
      omega
    · rw [if_neg hmem] at h1
      omega

noncomputable def jY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : ℕ :=
  if h : j.val < q then jY0 j U h else p + q

lemma jY_eq_jY0 (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    jY j U = jY0 j U h := by
  rw [jY, dif_pos h]

lemma jY_eq_last (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : ¬ j.val < q) :
    jY j U = p + q := by
  rw [jY, dif_neg h]

lemma jY_le (j : Fin (q - 1 + 2)) (U : Sh32 p q) : jY j U ≤ p + q := by
  rw [jY]
  by_cases h : j.val < q
  · rw [dif_pos h]; have := jY0_le j U h; omega
  · rw [dif_neg h]

lemma jY_value (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    BNat U.1 (jY j U) = j.val := by
  rw [jY_eq_jY0 j U h]; exact jY0_val j U h

lemma jY_min (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) {m : ℕ}
    (hm : m < jY j U) : BNat U.1 m < j.val := by
  rw [jY_eq_jY0 j U h] at hm
  exact jY0_min j U h hm

lemma BNat_le_self {n : ℕ} (S : Finset (Fin n)) (m : ℕ) : BNat S m ≤ m :=
  le_trans (BNat_le S m) (min_le_left _ _)

noncomputable def posY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : Fin (p + q) :=
  ⟨min (jY j U) (p + q - 1), by
    have h1 : (min (jY j U) (p + q - 1)) ≤ p + q - 1 := min_le_right _ _
    have h2 : 0 < p + q := by omega
    omega⟩

noncomputable def SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : PShuffle p q :=
  ⟨insertN U.1 (posY j U), by rw [card_insertN, U.2]; omega⟩

noncomputable def jfY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : Fin ((p + q - 1) + 2) :=
  ⟨jY j U, by have := jY_le j U; omega⟩

@[simp] lemma jfY_val (j : Fin (q - 1 + 2)) (U : Sh32 p q) : (jfY j U).val = jY j U := rfl

lemma posY_eq_jY (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : j.val < q) :
    (posY j U).val = jY j U := by
  show min (jY j U) (p + q - 1) = jY j U
  exact min_eq_left (by rw [jY_eq_jY0 j U h]; exact jY0_le j U h)

lemma posY_eq_last (j : Fin (q - 1 + 2)) (U : Sh32 p q) (h : ¬ j.val < q) :
    (posY j U).val = p + q - 1 := by
  show min (jY j U) (p + q - 1) = p + q - 1
  rw [jY_eq_last j U h]
  exact min_eq_right (Nat.sub_le (p + q) 1)

lemma le_posY_of_lt_jY (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ} (hv : v < jY j U) :
    v ≤ (posY j U).val := by
  by_cases h : j.val < q
  · rw [posY_eq_jY j U h]; exact le_of_lt hv
  · rw [posY_eq_last j U h]
    have hj : jY j U = p + q := jY_eq_last j U h
    have hk : v < p + q := by rw [← hj]; exact hv
    omega

lemma lt_posY_succ_of_le_jY (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ} (hv : jY j U ≤ v) :
    (posY j U).val < v + 1 := by
  have h1 : (posY j U).val ≤ jY j U := min_le_left _ _
  omega

lemma ANat_SY_of_le (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ}
    (hv : v ≤ (posY j U).val) : ANat (SY j U).1 v = ANat U.1 v := by
  rw [SY, ANat_insertN, if_pos hv]

lemma ANat_SY_of_gt (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ}
    (hv : (posY j U).val < v) : ANat (SY j U).1 v = ANat U.1 (v - 1) := by
  rw [SY, ANat_insertN, if_neg (by omega)]

lemma BNat_SY_of_le (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ}
    (hv : v ≤ (posY j U).val) : BNat (SY j U).1 v = BNat U.1 v := by
  rw [SY, BNat_insertN, if_pos hv]

lemma BNat_SY_of_gt (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : ℕ}
    (hv : (posY j U).val < v) : BNat (SY j U).1 v = BNat U.1 (v - 1) + 1 := by
  rw [SY, BNat_insertN, if_neg (by omega)]

lemma BNat_SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : BNat (SY j U).1 (jY j U) = j.val := by
  by_cases h : j.val < q
  · rw [BNat_SY_of_le j U (by rw [posY_eq_jY j U h])]
    exact jY_value j U h
  · have hi : j.val = q := by have := j.isLt; omega
    have hpos := posY_eq_last j U h
    have hj := jY_eq_last j U h
    have hlt : (posY j U).val < jY j U := by rw [hpos, hj]; omega
    rw [BNat_SY_of_gt j U hlt, hj]
    have h2 := BNat_last U.1
    rw [U.2] at h2
    rw [h2, hi]
    omega

lemma BNat_SY_lt (j : Fin (q - 1 + 2)) (U : Sh32 p q) {m : ℕ} (hm : m < jY j U) :
    BNat (SY j U).1 m < j.val := by
  by_cases h : j.val < q
  · rw [BNat_SY_of_le j U (le_posY_of_lt_jY j U hm)]
    exact jY_min j U h hm
  · have hi : j.val = q := by have := j.isLt; omega
    rw [BNat_SY_of_le j U (le_posY_of_lt_jY j U hm), hi]
    have h2 := BNat_last U.1
    rw [U.2] at h2
    have hmono : BNat U.1 m ≤ BNat U.1 (p + q - 1) := by
      have hk' := le_posY_of_lt_jY j U hm
      rw [posY_eq_last j U h] at hk'
      exact BNat_mono U.1 hk'
    rw [h2] at hmono
    have hcard := U.1.card_le_univ
    rw [U.2, Fintype.card_fin] at hcard
    omega

lemma BNat_SY_inj (j : Fin (q - 1 + 2)) (U : Sh32 p q) {v : Fin ((p + q - 1) + 2)}
    (hv : BNat (SY j U).1 v.val = BNat (SY j U).1 (jY j U)) : v.val = jY j U := by
  have hJ : BNat (SY j U).1 (jY j U) = j.val := BNat_SY j U
  rcases lt_trichotomy v.val (jY j U) with hlt | heq | hgt
  · exfalso
    have := BNat_SY_lt j U hlt
    omega
  · exact heq
  · exfalso
    have hgt' : j.val < BNat (SY j U).1 v.val := by
      by_cases h : j.val < q
      · have hsucc : BNat (SY j U).1 (jY j U + 1) = j.val + 1 := by
          have hlt : (posY j U).val < jY j U + 1 :=
            Nat.lt_succ_of_le (min_le_left (jY j U) (p + q - 1))
          rw [BNat_SY_of_gt j U hlt]
          have hsub : jY j U + 1 - 1 = jY j U := by omega
          rw [hsub, jY_value j U h]
        have hmono : BNat (SY j U).1 (jY j U + 1) ≤ BNat (SY j U).1 v.val :=
          BNat_mono (SY j U).1 (by omega)
        omega
      · have hj : jY j U = p + q := jY_eq_last j U h
        have h1 : p + q < v.val := by rw [hj] at hgt; exact hgt
        have h2 : v.val < p + q + 1 := v.isLt
        omega
    omega

lemma posY_mem (j : Fin (q - 1 + 2)) (U : Sh32 p q) : (posY j U) ∈ (SY j U).1 := by
  rw [SY]
  exact Finset.mem_insert_self _ _

lemma value_IsBY {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1))
    (h : ∀ v : Fin (N + 1), BNat S v.val = BNat S j.val → v = j) : IsBY S j := by
  intro k hk
  by_contra hkS
  have h1 : BNat S (k.val + 1) = BNat S k.val := by
    have hsucc := BNat_succ S k.isLt
    rw [if_neg hkS, add_zero] at hsucc
    exact hsucc
  have hkj : k.val ≤ j.val := by rcases hk with hk | hk <;> omega
  have hjk : j.val ≤ k.val + 1 := by rcases hk with hk | hk <;> omega
  have heq : BNat S k.val = BNat S j.val := by
    refine le_antisymm (BNat_mono S hkj) ?_
    calc BNat S j.val ≤ BNat S (k.val + 1) := BNat_mono S hjk
      _ = BNat S k.val := h1
  have hklt : k.val + 1 < N + 1 := by have := k.isLt; omega
  have e1 := h ⟨k.val + 1, hklt⟩ (by rw [h1]; exact heq)
  have e2 := h ⟨k.val, by have := k.isLt; omega⟩ heq
  have hp1 := congrArg Fin.val e1
  have hp2 := congrArg Fin.val e2
  simp only [Fin.val_mk] at hp1 hp2
  omega

lemma IsBY_SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) : IsBY (SY j U).1 (jfY j U) := by
  refine value_IsBY (SY j U).1 (jfY j U) (fun v hv => ?_)
  exact Fin.ext (by rw [jfY_val]; exact BNat_SY_inj j U hv)

lemma delta_jfY_val (j : Fin (q - 1 + 2)) (U : Sh32 p q) (k : Fin ((p + q - 1) + 1)) :
    ((SimplexCategory.δ (jfY j U)) k).val = delV (jY j U) k.val := by
  rw [delta_val]
  rfl

lemma ANat_SY_delV (j : Fin (q - 1 + 2)) (U : Sh32 p q) (k : Fin ((p + q - 1) + 1)) :
    ANat (SY j U).1 (delV (jY j U) k.val) = ANat U.1 k.val := by
  by_cases hk : k.val < jY j U
  · rw [delV_lt hk, ANat_SY_of_le j U (le_posY_of_lt_jY j U hk)]
  · rw [delV_ge hk, ANat_SY_of_gt j U (lt_posY_succ_of_le_jY j U (not_lt.mp hk)),
      show k.val + 1 - 1 = k.val from by omega]

lemma BNat_SY_delV (j : Fin (q - 1 + 2)) (U : Sh32 p q) (k : Fin ((p + q - 1) + 1)) :
    BNat (SY j U).1 (delV (jY j U) k.val) = delV j.val (BNat U.1 k.val) := by
  by_cases hk : k.val < jY j U
  · rw [delV_lt hk, BNat_SY_of_le j U (le_posY_of_lt_jY j U hk)]
    by_cases h : j.val < q
    · exact (delV_lt (jY_min j U h hk)).symm
    · have hi : j.val = q := by have := j.isLt; omega
      have h2 := BNat_last U.1
      rw [U.2] at h2
      have hmono : BNat U.1 k.val ≤ BNat U.1 (p + q - 1) := by
        have hk' := le_posY_of_lt_jY j U hk
        rw [posY_eq_last j U h] at hk'
        exact BNat_mono U.1 hk'
      rw [h2] at hmono
      exact (delV_lt (by omega)).symm
  · rw [delV_ge hk, BNat_SY_of_gt j U (lt_posY_succ_of_le_jY j U (not_lt.mp hk)),
      show k.val + 1 - 1 = k.val from by omega]
    by_cases h : j.val < q
    · rw [delV_ge (by
        have hmono : BNat U.1 (jY j U) ≤ BNat U.1 k.val :=
          BNat_mono U.1 (not_lt.mp hk)
        rw [jY_value j U h] at hmono
        omega)]
    · have hj : jY j U = p + q := jY_eq_last j U h
      rw [hj] at hk
      omega

lemma aFace_SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) :
    SimplexCategory.δ (jfY j U) ≫ @aHom (P + 1) (Q + 1) (SY j U).1 (SY j U).2
      = aMap32 p q U := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  refine Fin.ext ?_
  show ((SimplexCategory.δ (jfY j U) ≫ @aHom (P + 1) (Q + 1) (SY j U).1 (SY j U).2) k).val
      = ((aMap32 p q U) k).val
  rw [comp_val, aHom_val, pA_eq_ANat, delta_jfY_val, aMap32_apply]
  exact ANat_SY_delV j U k

lemma bFace_SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) :
    SimplexCategory.δ (jfY j U) ≫ @bHom (P + 1) (Q + 1) (SY j U).1 (SY j U).2
      = bMap32 p q U ≫ SimplexCategory.δ j := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  refine Fin.ext ?_
  show ((SimplexCategory.δ (jfY j U) ≫ @bHom (P + 1) (Q + 1) (SY j U).1 (SY j U).2) k).val
      = ((bMap32 p q U ≫ SimplexCategory.δ j) k).val
  rw [comp_val, comp_val, bHom_val, pB_eq_BNat, delta_jfY_val, delta_val, bMap32_apply]
  exact BNat_SY_delV j U k

lemma ANat_posY_add_jY (j : Fin (q - 1 + 2)) (U : Sh32 p q) :
    (p - ANat U.1 (posY j U).val) + jY j U = p + j.val := by
  by_cases h : j.val < q
  · have hJ := jY_eq_jY0 j U h
    have hJle : jY j U ≤ p + q - 1 := by rw [hJ]; exact jY0_le j U h
    have hpos : (posY j U).val = jY j U := posY_eq_jY j U h
    rw [hpos]
    have hsum : ANat U.1 (jY j U) + BNat U.1 (jY j U) = jY j U := by
      have h2 := ANat_add_BNat U.1 (jY j U)
      rw [min_eq_left hJle] at h2
      exact h2
    have hval : BNat U.1 (jY j U) = j.val := jY_value j U h
    have hpa : p - ANat U.1 (jY j U) + jY j U = p + (jY j U - ANat U.1 (jY j U)) := by
      have hle : ANat U.1 (jY j U) ≤ jY j U := ANat_le_self U.1 (jY j U)
      have hlep : ANat U.1 (jY j U) ≤ p := by
        have h3 : ANat U.1 (jY j U) ≤ ANat U.1 (p + q - 1) := ANat_mono U.1 hJle
        have h4 := ANat_last U.1
        rw [U.2] at h4
        rw [h4] at h3
        have hcard := U.1.card_le_univ
        rw [U.2, Fintype.card_fin] at hcard
        omega
      omega
    rw [hpa]
    omega
  · have hi : j.val = q := by have := j.isLt; omega
    have hj := jY_eq_last j U h
    have hpos := posY_eq_last j U h
    have h2 := ANat_last U.1
    rw [U.2] at h2
    rw [hpos, hj, h2, hi]
    have hcard := U.1.card_le_univ
    rw [U.2, Fintype.card_fin] at hcard
    omega

lemma shufSign_SY (j : Fin (q - 1 + 2)) (U : Sh32 p q) :
    @shufSign (P + 1) (Q + 1) (SY j U).1 * (-1 : ℤ) ^ (jfY j U).val
      = (-1 : ℤ) ^ (p) * ((-1 : ℤ) ^ (j.val) * shufSignN U.1) := by
  rw [jfY_val, @shufSign_eq_shufSignN (P + 1) (Q + 1) (SY j U).1]
  have hexp : invCountN U.1 + (p - ANat U.1 (posY j U).val) + jY j U
      = p + j.val + invCountN U.1 := by
    have h := ANat_posY_add_jY j U
    omega
  have hins : invCountN (SY j U).1 = invCountN U.1 + (p - ANat U.1 (posY j U).val) := by
    show invCountN (insertN U.1 (posY j U)) = invCountN U.1 + (p - ANat U.1 (posY j U).val)
    rw [invCountN_insertN U.1 (posY j U), U.2]
    omega
  calc shufSignN (SY j U).1 * (-1 : ℤ) ^ (jY j U)
      = (-1 : ℤ) ^ (invCountN U.1 + (p - ANat U.1 (posY j U).val) + jY j U) := by
        rw [shufSignN, hins, ← pow_add]
    _ = (-1 : ℤ) ^ (p + j.val + invCountN U.1) := by rw [hexp]
    _ = (-1 : ℤ) ^ (p) * ((-1 : ℤ) ^ (j.val) * shufSignN U.1) := by
        rw [pow_add, pow_add, shufSignN]; ring

/-! ## Deleting an `N`-step back out -/

lemma BNat_deleteN_le {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (hp : pos ∈ S) {m : ℕ}
    (hm : m ≤ pos.val) : BNat (deleteN S pos) m = BNat S m := by
  rw [BNat, BNat]
  refine Finset.card_bij (fun k _ => (⟨k.val, by have := k.isLt; omega⟩ : Fin N)) ?_ ?_ ?_
  · rintro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    obtain ⟨hkmem, hklt⟩ := hk
    rw [mem_deleteN] at hkmem
    obtain ⟨h1, h2⟩ := hkmem
    rw [insIdx_lt pos k (by omega)] at h1
    exact ⟨h1, hklt⟩
  · intro k1 hk1 k2 hk2 heq
    exact Fin.ext (by simpa using congrArg Fin.val heq)
  · rintro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hbS, hblt⟩ := hb
    have hbpos : b.val < pos.val := by omega
    have hbN : b.val < N - 1 := by have := pos.isLt; omega
    refine ⟨⟨b.val, hbN⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, by simpa using hblt⟩
    rw [mem_deleteN, insIdx_lt pos ⟨b.val, hbN⟩ (by simpa using hbpos)]
    exact ⟨hbS, fun hc => by
      have h := congrArg Fin.val hc
      simp only [Fin.val_mk] at h
      omega⟩

lemma posOf_mem (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    posOf j ∈ S.1 := by
  rcases Nat.lt_or_ge (p + q - 1) j.val with hc | hc
  · have hfin : posOf j = ⟨p + q - 1, by omega⟩ :=
      Fin.ext (by rw [posOf_val]; exact min_eq_right (le_of_lt hc))
    rw [hfin]
    exact h ⟨p + q - 1, by omega⟩ (Or.inl (by simp only [Fin.val_mk]; omega))
  · have hfin : posOf j = ⟨j.val, by omega⟩ :=
      Fin.ext (by rw [posOf_val]; exact min_eq_left hc)
    rw [hfin]
    exact h ⟨j.val, by omega⟩ (Or.inr rfl)

lemma BNat_le_q_of_IsBY (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    BNat S.1 j.val ≤ q := by
  calc BNat S.1 j.val ≤ BNat S.1 (p + q) := BNat_mono S.1 (by have := j.isLt; omega)
    _ = q := by rw [BNat_last, S.2]

lemma BNat_lt_q_of_IsBY (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j)
    (hj : j.val < p + q) : BNat S.1 j.val < q := by
  have h1 := BNat_succ S.1 (m := j.val) (by omega)
  rw [if_pos (h ⟨j.val, _⟩ (Or.inr rfl))] at h1
  have h2 : BNat S.1 (j.val + 1) ≤ BNat S.1 (p + q) := BNat_mono S.1 (by omega)
  rw [BNat_last, S.2] at h2
  omega

noncomputable def bwdU (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) : Sh32 p q :=
  ⟨deleteN S.1 (posOf j), by
    rw [card_deleteN S.1 (posOf j) (posOf_mem S j h), S.2]⟩

noncomputable def bwdJ (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    Fin (q - 1 + 2) :=
  ⟨BNat S.1 j.val, by have := BNat_le_q_of_IsBY S j h; omega⟩

@[simp] lemma bwdU_val (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    (bwdU S j h).1 = deleteN S.1 (posOf j) := rfl

@[simp] lemma bwdJ_val (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    (bwdJ S j h).val = BNat S.1 j.val := rfl

lemma jY_bwdU (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    jY (bwdJ S j h) (bwdU S j h) = j.val := by
  by_cases hj : j.val < p + q
  · have hlt : (bwdJ S j h).val < q := by
      rw [bwdJ_val]
      exact BNat_lt_q_of_IsBY S j h hj
    rw [jY_eq_jY0 _ _ hlt]
    have hle : jY0 (bwdJ S j h) (bwdU S j h) hlt ≤ j.val :=
      Nat.find_min' (BNat_exists_ge (bwdJ S j h) (bwdU S j h) hlt) (by
        rw [bwdU_val, bwdJ_val, BNat_deleteN_le S.1 (posOf j) (posOf_mem S j h)
          (by rw [posOf_val]; omega)])
    have hge : j.val ≤ jY0 (bwdJ S j h) (bwdU S j h) hlt := by
      show j.val ≤ Nat.find _
      rw [Nat.le_find_iff]
      intro m hm
      rw [bwdU_val, bwdJ_val, BNat_deleteN_le S.1 (posOf j) (posOf_mem S j h)
        (by rw [posOf_val]; omega)]
      rcases Nat.eq_zero_or_pos j.val with h0 | hpos
      · omega
      · have h2 : BNat S.1 j.val = BNat S.1 (j.val - 1) + 1 := by
          have h3 := BNat_succ S.1 (m := j.val - 1) (by omega)
          rw [show j.val - 1 + 1 = j.val from by omega,
            if_pos (h ⟨j.val - 1, _⟩ (Or.inl rfl))] at h3
          exact h3
        have h4 : BNat S.1 m ≤ BNat S.1 (j.val - 1) := BNat_mono S.1 (by omega)
        omega
    omega
  · have hjE : j.val = p + q := by have := j.isLt; omega
    have hge : ¬ (bwdJ S j h).val < q := by
      rw [bwdJ_val]
      have h2 : BNat S.1 j.val = q := by rw [hjE, BNat_last, S.2]
      omega
    rw [jY_eq_last _ _ hge]
    exact hjE.symm

lemma SY_bwdU (S : PShuffle p q) (j : Fin (p + q + 1)) (h : IsBY S.1 j) :
    SY (bwdJ S j h) (bwdU S j h) = S := by
  have hpos : posY (bwdJ S j h) (bwdU S j h) = posOf j := by
    refine Fin.ext ?_
    rw [posOf_val]
    show min (jY (bwdJ S j h) (bwdU S j h)) (p + q - 1) = min j.val (p + q - 1)
    rw [jY_bwdU S j h]
  refine Subtype.ext ?_
  show insertN (bwdU S j h).1 (posY (bwdJ S j h) (bwdU S j h)) = S.1
  rw [hpos, bwdU_val, insertN_deleteN S.1 (posOf j) (posOf_mem S j h)]


/-! ## The `X`- and `Y`-side index maps -/

noncomputable def phiX :
    Sh23 p q × Fin (p - 1 + 2) → PShuffle p q × Fin ((p + q - 1) + 2) :=
  fun y => (SX y.2 y.1, jfX y.2 y.1)

noncomputable def phiY :
    Sh32 p q × Fin (q - 1 + 2) → PShuffle p q × Fin ((p + q - 1) + 2) :=
  fun y => (SY y.2 y.1, jfY y.2 y.1)

lemma phiX_inj : Function.Injective (phiX (P := P) (Q := Q)) := by
  rintro ⟨T₁, i₁⟩ ⟨T₂, i₂⟩ heq
  have hS : SX i₁ T₁ = SX i₂ T₂ := congrArg Prod.fst heq
  have hJ : jX i₁ T₁ = jX i₂ T₂ := congrArg (fun z => z.2.val) heq
  have hi : i₁ = i₂ := by
    refine Fin.ext ?_
    calc i₁.val = ANat (SX i₁ T₁).1 (jX i₁ T₁) := (ANat_SX i₁ T₁).symm
      _ = ANat (SX i₂ T₂).1 (jX i₂ T₂) := by rw [hS, hJ]
      _ = i₂.val := ANat_SX i₂ T₂
  have hT : T₁ = T₂ := by
    refine Subtype.ext ?_
    have h1 : (SX i₁ T₁).1 = (SX i₂ T₂).1 := congrArg Subtype.val hS
    have h2 : posX i₁ T₁ = posX i₂ T₂ := by
      refine Fin.ext ?_
      show min (jX i₁ T₁) (p + q - 1) = min (jX i₂ T₂) (p + q - 1)
      rw [hJ]
    calc T₁.1 = deleteE (SX i₁ T₁).1 (posX i₁ T₁) := (deleteE_insertE T₁.1 (posX i₁ T₁)).symm
      _ = deleteE (SX i₂ T₂).1 (posX i₂ T₂) := by rw [h1, h2]
      _ = T₂.1 := deleteE_insertE T₂.1 (posX i₂ T₂)
  rw [hi]
  exact congrArg (fun t => (t, i₂)) hT

lemma phiX_bwd (S : PShuffle p q) (j : Fin ((p + q - 1) + 2)) (h : IsBX S.1 j) :
    phiX (bwdT S j h, bwdI S j h) = (S, j) := by
  refine Prod.ext ?_ ?_
  · exact SX_bwdT S j h
  · exact Fin.ext (jX_bwdT S j h)

lemma phiX_surj (S : PShuffle p q) (j : Fin ((p + q - 1) + 2)) (h : IsBX S.1 j) :
    ∃ y : Sh23 p q × Fin (p - 1 + 2), phiX y = (S, j) :=
  ⟨(bwdT S j h, bwdI S j h), phiX_bwd S j h⟩

lemma phiY_inj : Function.Injective (phiY (P := P) (Q := Q)) := by
  rintro ⟨U₁, j₁⟩ ⟨U₂, j₂⟩ heq
  have hS : SY j₁ U₁ = SY j₂ U₂ := congrArg Prod.fst heq
  have hJ : jY j₁ U₁ = jY j₂ U₂ := congrArg (fun z => z.2.val) heq
  have hi : j₁ = j₂ := by
    refine Fin.ext ?_
    calc j₁.val = BNat (SY j₁ U₁).1 (jY j₁ U₁) := (BNat_SY j₁ U₁).symm
      _ = BNat (SY j₂ U₂).1 (jY j₂ U₂) := by rw [hS, hJ]
      _ = j₂.val := BNat_SY j₂ U₂
  have hT : U₁ = U₂ := by
    refine Subtype.ext ?_
    have h1 : (SY j₁ U₁).1 = (SY j₂ U₂).1 := congrArg Subtype.val hS
    have h2 : posY j₁ U₁ = posY j₂ U₂ := by
      refine Fin.ext ?_
      show min (jY j₁ U₁) (p + q - 1) = min (jY j₂ U₂) (p + q - 1)
      rw [hJ]
    have hmem : posY j₁ U₁ ∈ (SY j₁ U₁).1 := posY_mem j₁ U₁
    calc U₁.1 = deleteN (SY j₁ U₁).1 (posY j₁ U₁) := (deleteN_insertN U₁.1 (posY j₁ U₁)).symm
      _ = deleteN (SY j₂ U₂).1 (posY j₂ U₂) := by rw [h1, h2]
      _ = U₂.1 := deleteN_insertN U₂.1 (posY j₂ U₂)
  rw [hi]
  exact congrArg (fun t => (t, j₂)) hT

lemma phiY_bwd (S : PShuffle p q) (j : Fin ((p + q - 1) + 2)) (h : IsBY S.1 j) :
    phiY (bwdU S j h, bwdJ S j h) = (S, j) := by
  refine Prod.ext ?_ ?_
  · exact SY_bwdU S j h
  · exact Fin.ext (jY_bwdU S j h)

lemma phiY_surj (S : PShuffle p q) (j : Fin ((p + q - 1) + 2)) (h : IsBY S.1 j) :
    ∃ y : Sh32 p q × Fin (q - 1 + 2), phiY y = (S, j) :=
  ⟨(bwdU S j h, bwdJ S j h), phiY_bwd S j h⟩

/-! ## The chain complex differential and the tensor faces -/

abbrev eZR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The generator of the `n`-chains attached to an `n`-simplex. -/
noncomputable def genT (Z : SSet) {n : ℕ} (z : Z _⦋n⦌) : (Z.chainComplex eZR).X n :=
  (Z.ιChainComplex (R := eZR) z).hom 1

lemma d_genT (Z : SSet) {n : ℕ} (z : Z _⦋n + 1⦌) :
    ((Z.chainComplex eZR).d (n + 1) n) (genT Z z)
      = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • genT Z (Z.δ j z) := by
  have h2 := congrArg (fun (f : eZR ⟶ (Z.chainComplex eZR).X n) => f.hom (1 : ℤ))
    (SSet.ιChainComplex_d Z eZR (n := n) z)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.comp_apply] at h2
  exact h2

lemma tensor_delta (X Y : SSet) {n : ℕ} (j : Fin (n + 2))
    (x : X _⦋n + 1⦌) (y : Y _⦋n + 1⦌) :
    (X ⊗ Y).δ j (x, y) = (X.δ j x, Y.δ j y) := rfl

lemma map_delta {n l : ℕ} (X : SSet) (j : Fin (n + 2)) (a : ⦋n + 1⦌ ⟶ ⦋l⦌)
    (x : X _⦋l⦌) :
    X.δ j (X.map a.op x) = X.map (SimplexCategory.δ j ≫ a).op x := by
  unfold SimplicialObject.δ
  rw [← Functor.map_comp_apply, ← op_comp]

lemma map_op_comp {X : SSet} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (x : X.obj (Opposite.op c)) :
    X.map (f ≫ g).op x = X.map f.op (X.map g.op x) := by
  rw [op_comp, Functor.map_comp_apply]

/-! ## The Eilenberg–Zilber summands and the linear extensions -/

/-- The generator of the `n`-chains attached to a *pair* of simplices of `X` and `Y`. -/
noncomputable def genP {X Y : SSet} {n : ℕ} (x : X _⦋n⦌) (y : Y _⦋n⦌) :
    ((X ⊗ Y).chainComplex eZR).X n :=
  ((X ⊗ Y).ιChainComplex (R := eZR) (x, y)).hom 1

lemma d_genP {X Y : SSet} {n : ℕ} (x : X _⦋n + 1⦌) (y : Y _⦋n + 1⦌) :
    ((X ⊗ Y).chainComplex eZR).d (n + 1) n (genP x y)
      = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • genP (X.δ j x) (Y.δ j y) := by
  have h := d_genT (Z := X ⊗ Y) (n := n) (x, y)
  rw [show ((X ⊗ Y).chainComplex eZR).d (n + 1) n (genP x y)
      = ((X ⊗ Y).chainComplex eZR).d (n + 1) n (genT (X ⊗ Y) (x, y)) from rfl]
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tensor_delta]
  rfl

lemma ezGen_eq_genP (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Work.Cohomology.Crux33.ezGen p q X Y σ τ
      = ∑ S : PShuffle p q, @shufSign (P + 1) (Q + 1) S.1 •
          genP (X.map (@aHom (P + 1) (Q + 1) S.1 S.2).op σ)
               (Y.map (@bHom (P + 1) (Q + 1) S.1 S.2).op τ) := by
  rw [Work.Cohomology.Crux33.ezGen]
  refine Finset.sum_congr rfl (fun S _ => rfl)

noncomputable def GX23 (X Y : SSet) (τ : Y _⦋q⦌) (x : X _⦋p - 1⦌) :
    ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  ∑ T : Sh23 p q, shufSignN T.1 • genP (X.map (aMap23 p q T).op x) (Y.map (bMap23 p q T).op τ)

noncomputable def GY23 (X Y : SSet) (σ : X _⦋p⦌) (y : Y _⦋q - 1⦌) :
    ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  ∑ U : Sh32 p q, shufSignN U.1 • genP (X.map (aMap32 p q U).op σ) (Y.map (bMap32 p q U).op y)

noncomputable def ezLin23 (X Y : SSet) (τ : Y _⦋q⦌) :
    (X.chainComplex eZR).X (p - 1) ⟶ ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  (X.isColimitChainComplexXCofan eZR (p - 1)).desc
    (Cofan.mk (((X ⊗ Y).chainComplex eZR).X (p + q - 1))
      (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (GX23 X Y τ x))))

noncomputable def ezLin32 (X Y : SSet) (σ : X _⦋p⦌) :
    (Y.chainComplex eZR).X (q - 1) ⟶ ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  (Y.isColimitChainComplexXCofan eZR (q - 1)).desc
    (Cofan.mk (((X ⊗ Y).chainComplex eZR).X (p + q - 1))
      (fun y => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (GY23 X Y σ y))))

theorem ezLin23_ι (X Y : SSet) (τ : Y _⦋q⦌) (x : X _⦋p - 1⦌) :
    (X.ιChainComplex (R := eZR) x) ≫ ezLin23 X Y τ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (GX23 X Y τ x)) :=
  Cofan.IsColimit.fac _ _ _

theorem ezLin32_ι (X Y : SSet) (σ : X _⦋p⦌) (y : Y _⦋q - 1⦌) :
    (Y.ιChainComplex (R := eZR) y) ≫ ezLin32 X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (GY23 X Y σ y)) :=
  Cofan.IsColimit.fac _ _ _

lemma ezLin23_apply (X Y : SSet) (τ : Y _⦋q⦌) (x : X _⦋p - 1⦌) :
    (ezLin23 X Y τ).hom (genT X x) = GX23 X Y τ x := by
  have h2 := congrArg (fun (f : eZR ⟶ ((X ⊗ Y).chainComplex eZR).X (p + q - 1)) =>
      f.hom (1 : ℤ)) (ezLin23_ι X Y τ x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

lemma ezLin32_apply (X Y : SSet) (σ : X _⦋p⦌) (y : Y _⦋q - 1⦌) :
    (ezLin32 X Y σ).hom (genT Y y) = GY23 X Y σ y := by
  have h2 := congrArg (fun (f : eZR ⟶ ((X ⊗ Y).chainComplex eZR).X (p + q - 1)) =>
      f.hom (1 : ℤ)) (ezLin32_ι X Y σ y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The `(S,j)`-term of the boundary of the Eilenberg–Zilber shuffle chain. -/
noncomputable def lhsT (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    PShuffle p q × Fin ((p + q - 1) + 2) → ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  fun x => (@shufSign (P + 1) (Q + 1) x.1.1 * (-1 : ℤ) ^ (x.2 : ℕ)) •
    genP (X.map ((SimplexCategory.δ x.2) ≫ @aHom (P + 1) (Q + 1) x.1.1 x.1.2).op σ)
         (Y.map ((SimplexCategory.δ x.2) ≫ @bHom (P + 1) (Q + 1) x.1.1 x.1.2).op τ)

/-- The `(T,i)`-term of the `X`-boundary chain. -/
noncomputable def gX23 (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Sh23 p q × Fin (p - 1 + 2) → ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  fun y => (shufSignN y.1.1 * (-1 : ℤ) ^ (y.2 : ℕ)) •
    genP (X.map (aMap23 p q y.1).op (X.δ y.2 σ)) (Y.map (bMap23 p q y.1).op τ)

/-- The `(U,j)`-term of the `Y`-boundary chain. -/
noncomputable def gY32 (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Sh32 p q × Fin (q - 1 + 2) → ((X ⊗ Y).chainComplex eZR).X (p + q - 1) :=
  fun y => ((-1 : ℤ) ^ (p) * (shufSignN y.1.1 * (-1 : ℤ) ^ (y.2 : ℕ))) •
    genP (X.map (aMap32 p q y.1).op σ) (Y.map (bMap32 p q y.1).op (Y.δ y.2 τ))

/-- The interior involution on `(p,q)`-shuffles. -/
noncomputable def flipP (S : PShuffle p q) (j : Fin ((p + q - 1) + 2))
    (h : IsInt S.1 j) : PShuffle p q :=
  ⟨Work.KunnethEZ.flipS S.1 j, (Work.KunnethEZ.flipS_card S.1 j h).trans S.2⟩

set_option maxHeartbeats 8000000 in
theorem ezGen_isCycle_aux (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌)
    (hσ : ((X.chainComplex eZR).d p (p - 1)).hom (genT X σ) = 0)
    (hτ : ((Y.chainComplex eZR).d q (q - 1)).hom (genT Y τ) = 0) :
    ((X ⊗ Y).chainComplex eZR).d (p + q) (p + q - 1)
      (Work.Cohomology.Crux33.ezGen p q X Y σ τ) = 0 := by
  classical
  change ((X ⊗ Y).chainComplex eZR).d ((p + q - 1) + 1) (p + q - 1)
      (Work.Cohomology.Crux33.ezGen p q X Y σ τ) = 0
  have hL : ((X ⊗ Y).chainComplex eZR).d ((p + q - 1) + 1) (p + q - 1)
        (Work.Cohomology.Crux33.ezGen p q X Y σ τ)
      = ∑ S : PShuffle p q, ∑ j : Fin ((p + q - 1) + 2), lhsT X Y σ τ (S, j) := by
    rw [ezGen_eq_genP, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_zsmul, d_genP (n := p + q - 1), ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_smul]
    congr 1
    simp only [lhsT]
    rw [map_delta, map_delta]
  rw [hL, ← Fintype.sum_prod_type (f := lhsT X Y σ τ)]
  have hpt : ∀ x : PShuffle p q × Fin ((p + q - 1) + 2), lhsT X Y σ τ x
      = (if IsBX x.1.1 x.2 then lhsT X Y σ τ x else 0)
        + (if IsBY x.1.1 x.2 then lhsT X Y σ τ x else 0)
        + (if IsInt x.1.1 x.2 then lhsT X Y σ τ x else 0) := by
    intro x
    have hnb := not_both_boundary (by omega : 0 < p + q) x.1.1 x.2
    by_cases h1 : IsBX x.1.1 x.2
    · rw [if_pos h1, if_neg (fun h2 => hnb ⟨h1, h2⟩), if_neg (fun h2 => h2.1 h1)]
      abel
    · by_cases h2 : IsBY x.1.1 x.2
      · rw [if_neg h1, if_pos h2, if_neg (fun h3 => h3.2 h2)]
        abel
      · rw [if_neg h1, if_neg h2, if_pos (show IsInt x.1.1 x.2 from ⟨h1, h2⟩)]
        abel
  have hpart :
      (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBX x.1.1 x.2), lhsT X Y σ τ x)
      + (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBY x.1.1 x.2), lhsT X Y σ τ x)
      + (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsInt x.1.1 x.2), lhsT X Y σ τ x)
      = ∑ x : PShuffle p q × Fin ((p + q - 1) + 2), lhsT X Y σ τ x := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (hpt x).symm)
  rw [hpart.symm]
  have hInt : (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
      IsInt x.1.1 x.2), lhsT X Y σ τ x) = 0 := by
    refine Finset.sum_involution
      (g := fun x hx => (flipP x.1 x.2 (Finset.mem_filter.mp hx).2, x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      have hsign : @shufSign (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
          = - @shufSign (P + 1) (Q + 1) x.1.1 := by
        rw [@shufSign_eq_shufSignN (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1,
          @shufSign_eq_shufSignN (P + 1) (Q + 1) x.1.1]
        exact Work.KunnethEZ.shufSignN_flipS x.1.1 x.2 hxI
      have hmap : SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2
          = SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) x.1.1 x.1.2 := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext k
        refine Fin.ext ?_
        show ((SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2) k).val
          = ((SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) x.1.1 x.1.2) k).val
        rw [comp_val, comp_val, aHom_val, aHom_val, pA_eq_ANat, pA_eq_ANat, delta_val]
        exact Work.KunnethEZ.ANat_flipS x.1.1 x.2 hxI (delV_ne (j := x.2.val) (k := k.val))
      have hmapb : SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2
          = SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) x.1.1 x.1.2 := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext k
        refine Fin.ext ?_
        show ((SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2) k).val
          = ((SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) x.1.1 x.1.2) k).val
        rw [comp_val, comp_val, bHom_val, bHom_val, pB_eq_BNat, pB_eq_BNat, delta_val]
        exact Work.KunnethEZ.BNat_flipS x.1.1 x.2 hxI (delV_ne (j := x.2.val) (k := k.val))
      have hgoal : lhsT X Y σ τ (flipP x.1 x.2 hxI, x.2) = - lhsT X Y σ τ x := by
        simp only [lhsT]
        rw [hmap, hmapb, hsign, neg_mul, neg_zsmul]
      rw [hgoal]
      abel
    · intro x hx _
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      intro hc
      have h1 := congrArg Prod.fst hc
      exact Work.KunnethEZ.flipS_ne x.1.1 x.2 hxI (Subtype.ext_iff.mp h1)
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Work.KunnethEZ.IsInt_flipS x.1.1 x.2 hxI⟩
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (Work.KunnethEZ.flipS_flipS x.1.1 x.2 hxI)
      · rfl
  rw [hInt]
  have hBX : (∑ y : Sh23 p q × Fin (p - 1 + 2), gX23 X Y σ τ y)
      = ∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBX x.1.1 x.2), lhsT X Y σ τ x := by
    refine Finset.sum_bij (fun y _ => phiX y) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsBX_SX y.2 y.1⟩
    · intro y₁ _ y₂ _ heq
      exact phiX_inj heq
    · intro z hz
      obtain ⟨-, hzBX⟩ := Finset.mem_filter.mp hz
      exact ⟨(bwdT z.1 z.2 hzBX, bwdI z.1 z.2 hzBX), Finset.mem_univ _, phiX_bwd z.1 z.2 hzBX⟩
    · intro y _
      obtain ⟨T, i⟩ := y
      simp only [gX23, lhsT, phiX]
      rw [aFace_SX i T, map_op_comp (aMap23 p q T) (SimplexCategory.δ i) σ, bFace_SX i T,
        shufSign_SX i T, mul_comm (shufSignN T.1) ((-1 : ℤ) ^ (i : ℕ))]
      rfl
  rw [← hBX]
  have hBY : (∑ y : Sh32 p q × Fin (q - 1 + 2), gY32 X Y σ τ y)
      = ∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBY x.1.1 x.2), lhsT X Y σ τ x := by
    refine Finset.sum_bij (fun y _ => phiY y) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsBY_SY y.2 y.1⟩
    · intro y₁ _ y₂ _ heq
      exact phiY_inj heq
    · intro z hz
      obtain ⟨-, hzBY⟩ := Finset.mem_filter.mp hz
      exact ⟨(bwdU z.1 z.2 hzBY, bwdJ z.1 z.2 hzBY), Finset.mem_univ _, phiY_bwd z.1 z.2 hzBY⟩
    · intro y _
      obtain ⟨U, j⟩ := y
      simp only [gY32, lhsT, phiY]
      rw [aFace_SY j U, bFace_SY j U, map_op_comp (bMap32 p q U) (SimplexCategory.δ j) τ,
        shufSign_SY j U, mul_comm (shufSignN U.1) ((-1 : ℤ) ^ (j : ℕ))]
      rfl
  rw [← hBY]
  have hGX : (∑ y : Sh23 p q × Fin (p - 1 + 2), gX23 X Y σ τ y)
      = (ezLin23 X Y τ).hom
          (∑ i : Fin (p - 1 + 2), (-1 : ℤ) ^ (i : ℕ) • genT X (X.δ i σ)) := by
    rw [Fintype.sum_prod_type (f := gX23 X Y σ τ), Finset.sum_comm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, ezLin23_apply]
    simp only [GX23]
    rw [← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    simp only [gX23]
    rw [mul_comm (shufSignN T.1) ((-1 : ℤ) ^ (i : ℕ)), mul_smul]
  have hGY : (∑ y : Sh32 p q × Fin (q - 1 + 2), gY32 X Y σ τ y)
      = (-1 : ℤ) ^ (p) • (ezLin32 X Y σ).hom
          (∑ j : Fin (q - 1 + 2), (-1 : ℤ) ^ (j : ℕ) • genT Y (Y.δ j τ)) := by
    rw [Fintype.sum_prod_type (f := gY32 X Y σ τ), Finset.sum_comm]
    rw [map_sum]
    simp only [GY23]
    rw [← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, ezLin32_apply, GY23, ← Finset.sum_zsmul, ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    simp only [gY32]
    rw [mul_comm (shufSignN U.1) ((-1 : ℤ) ^ (j : ℕ)), ← mul_assoc, mul_smul, mul_smul]
  rw [hGX, hGY]
  have hσ0 : (∑ i : Fin (p - 1 + 2), (-1 : ℤ) ^ (i : ℕ) • genT X (X.δ i σ)) = 0 := by
    rw [← d_genT (Z := X) (n := p - 1) σ]
    exact hσ
  have hτ0 : (∑ j : Fin (q - 1 + 2), (-1 : ℤ) ^ (j : ℕ) • genT Y (Y.δ j τ)) = 0 := by
    rw [← d_genT (Z := Y) (n := q - 1) τ]
    exact hτ
  rw [hσ0, hτ0, map_zero, map_zero, zsmul_zero]
  abel

end

end Work.KunnethEZ
