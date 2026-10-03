import Mathlib
import Submission.Work.FIArea2.roots_card_le_four_unit
import Submission.Work.FIArea2.congAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

open Finset

attribute [local instance] Classical.propDecidable

set_option linter.style.haveILetI false

/-- The number of `z : ZMod n` with `z ^ 2 = a`. -/
private def Cnt (n : ℕ) [NeZero n] (a : ℤ) : ℕ :=
  ((Finset.univ : Finset (ZMod n)).filter (fun z => z ^ 2 = (a : ZMod n))).card

/-- `(c : ZMod n)^2 = b` iff `n ∣ c^2 - b` (over `ℤ`). -/
private lemma natCast_sq_eq_iff_dvd {n : ℕ} [NeZero n] (c : ℕ) (b : ℤ) :
    ((c : ZMod n)) ^ 2 = (b : ZMod n) ↔ (n : ℤ) ∣ (c : ℤ) ^ 2 - b := by
  rw [← sub_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine iff_of_eq (congrArg (fun t : ZMod n => t = 0) ?_)
  push_cast
  ring

/-- Same, for an arbitrary element, in terms of its canonical representative. -/
private lemma sq_eq_iff_dvd {n : ℕ} [NeZero n] (z : ZMod n) (a : ℤ) :
    z ^ 2 = (a : ZMod n) ↔ (n : ℤ) ∣ (z.val : ℤ) ^ 2 - a := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact natCast_sq_eq_iff_dvd z.val a

/-- `m ∣ a.natAbs` iff `(m : ℤ) ∣ a`. -/
private lemma natAbs_dvd_intCast_iff (m : ℕ) (a : ℤ) : m ∣ a.natAbs ↔ (m : ℤ) ∣ a := by
  have h := Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := a)
  simpa using h

/-- In `ZMod (p^d)` (`p` prime, `d > 0`) the class of `a : ℤ` is a unit iff `p ∤ a.natAbs`. -/
private lemma isUnit_intCast_prime_pow {p d : ℕ} (hp : p.Prime) (hd : 0 < d) (a : ℤ) :
    IsUnit ((a : ℤ) : ZMod (p ^ d)) ↔ ¬ p ∣ a.natAbs := by
  rcases Int.natAbs_eq a with h | h
  · conv_lhs => rw [h]
    rw [show ((a.natAbs : ℤ) : ZMod (p ^ d)) = ((a.natAbs : ℕ) : ZMod (p ^ d)) by
      norm_num]
    exact ZMod.isUnit_natCast_iff_not_dvd_pow hp hd
  · conv_lhs => rw [h]
    rw [show ((-(a.natAbs : ℤ) : ℤ) : ZMod (p ^ d)) = -((a.natAbs : ℕ) : ZMod (p ^ d)) by
      rw [Int.cast_neg, Int.cast_natCast], IsUnit.neg_iff]
    exact ZMod.isUnit_natCast_iff_not_dvd_pow hp hd

/-- `p ^ 2 ∣ p ^ k` over `ℤ`, for `k ≥ 2`. -/
private lemma sq_dvd_pow_int {p k : ℕ} (hk : 2 ≤ k) : (p : ℤ) ^ 2 ∣ (p ^ k : ℤ) := by
  refine ⟨(p : ℤ) ^ (k - 2), ?_⟩
  push_cast
  rw [← pow_add, Nat.add_sub_cancel' hk]

/-- **Fibre counting.** For `m ∣ n` and `b : ℤ`, the number of `x : ZMod n` with
`(x mod m)^2 = b` is `n / m` times the number of `w : ZMod m` with `w^2 = b`. -/
private lemma card_filter_sq_castHom {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (b : ℤ) :
    ((Finset.univ : Finset (ZMod n)).filter
      (fun x => (ZMod.castHom h (ZMod m) x) ^ 2 = (b : ZMod m))).card
      = n / m
        * ((Finset.univ : Finset (ZMod m)).filter (fun w => w ^ 2 = (b : ZMod m))).card := by
  classical
  let ψ : ZMod n → ZMod m := fun x => ZMod.castHom h (ZMod m) x
  let S : Finset (ZMod n) :=
    (Finset.univ : Finset (ZMod n)).filter (fun x => ψ x ^ 2 = (b : ZMod m))
  have hS : S = (Finset.univ : Finset (ZMod n)).filter
      (fun x => (ZMod.castHom h (ZMod m) x) ^ 2 = (b : ZMod m)) := rfl
  have hmain : S.card = ∑ c ∈ (Finset.univ : Finset (ZMod m)),
      (S.filter (fun x => ψ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (ψ x))
  have hterm : ∀ c : ZMod m, (S.filter (fun x => ψ x = c)).card
      = if c ^ 2 = (b : ZMod m) then n / m else 0 := by
    intro c
    by_cases hc : c ^ 2 = (b : ZMod m)
    · have heq : S.filter (fun x => ψ x = c)
          = (Finset.univ : Finset (ZMod n)).filter (fun x => ψ x = c) := by
        ext x
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hx => hx.2
        · exact fun hx => ⟨by rw [hx]; exact hc, hx⟩
      rw [heq, if_pos hc]
      exact fiber_card_zmod_castHom h c
    · have heq : S.filter (fun x => ψ x = c) = ∅ := by
        apply Finset.filter_false_of_mem
        intro x hx hxc
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hc (hxc ▸ hx)
      rw [heq, if_neg hc, Finset.card_empty]
  have hsum : (∑ c ∈ (Finset.univ : Finset (ZMod m)),
        (if c ^ 2 = (b : ZMod m) then n / m else 0))
      = n / m * ((Finset.univ : Finset (ZMod m)).filter (fun w => w ^ 2 = (b : ZMod m))).card := by
    rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]
    exact Nat.mul_comm _ _
  rw [← hS]
  calc S.card = ∑ c ∈ (Finset.univ : Finset (ZMod m)), (S.filter (fun x => ψ x = c)).card := hmain
    _ = ∑ c ∈ (Finset.univ : Finset (ZMod m)),
          (if c ^ 2 = (b : ZMod m) then n / m else 0) :=
        Finset.sum_congr rfl (fun c _ => hterm c)
    _ = n / m * ((Finset.univ : Finset (ZMod m)).filter (fun w => w ^ 2 = (b : ZMod m))).card := hsum

/-- **Reduction step.** For `k ≥ 2`, `p` prime, `a : ℤ` with `p^2 ∣ a`: the number of
square roots of `a` mod `p^k` is `p` times the number of square roots of `a / p^2` mod
`p^(k-2)`. -/
private lemma cnt_eq_mul_pred {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) [NeZero (p ^ k)]
    [NeZero (p ^ (k - 2))] (a : ℤ) (hdiv : (p : ℤ) ^ 2 ∣ a) :
    Cnt (p ^ k) a = p * Cnt (p ^ (k - 2)) (a / (p : ℤ) ^ 2) := by
  classical
  have hk1 : 1 ≤ k := by omega
  haveI : NeZero (p ^ (k - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set b : ℤ := a / (p : ℤ) ^ 2 with hb
  have ha : a = (p : ℤ) ^ 2 * b := by rw [hb]; exact (Int.mul_ediv_cancel' hdiv).symm
  have hp2pk : (p : ℤ) ^ 2 ∣ (p ^ k : ℤ) := sq_dvd_pow_int hk
  -- Step 1: every solution has `p ∣ z.val`
  have hstep1 : ∀ z : ZMod (p ^ k), z ^ 2 = (a : ZMod (p ^ k)) → p ∣ z.val := by
    intro z hz
    have hz2 : (p ^ k : ℤ) ∣ (z.val : ℤ) ^ 2 - a := (sq_eq_iff_dvd z a).mp hz
    have h1 : (p : ℤ) ^ 2 ∣ (z.val : ℤ) ^ 2 - a := dvd_trans hp2pk hz2
    have h2 : (p : ℤ) ^ 2 ∣ (z.val : ℤ) ^ 2 := by
      have h3 : (p : ℤ) ^ 2 ∣ ((z.val : ℤ) ^ 2 - a) + a := dvd_add h1 hdiv
      simpa using h3
    have hnat : p ^ 2 ∣ z.val ^ 2 := by
      have h4 : ((p ^ 2 : ℕ) : ℤ) ∣ ((z.val ^ 2 : ℕ) : ℤ) := by push_cast; exact h2
      exact Int.natCast_dvd_natCast.mp h4
    exact hp.dvd_of_dvd_pow
      (dvd_trans (by simpa using Nat.pow_dvd_pow p (by norm_num : 1 ≤ 2)) hnat)
  -- sets
  set A : Finset (ZMod (p ^ k)) :=
    (Finset.univ : Finset (ZMod (p ^ k))).filter (fun z => z ^ 2 = (a : ZMod (p ^ k))) with hA
  set B : Finset (ZMod (p ^ k)) := A.filter (fun z => p ∣ z.val) with hB
  have hBA : B = A := by
    rw [hB]
    exact Finset.filter_true_of_mem (fun z hz => hstep1 z (Finset.mem_filter.mp hz).2)
  -- bijection with `ZMod (p^(k-1))`
  set T : Finset (ZMod (p ^ (k - 1))) :=
    (Finset.univ : Finset (ZMod (p ^ (k - 1)))).filter
      (fun u => (plift p k u) ^ 2 = (a : ZMod (p ^ k))) with hT
  have himage : T.image (plift p k) = B := by
    ext z
    rw [Finset.mem_image]
    simp only [hT, hB, hA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, huz⟩
      refine ⟨huz ▸ hu, ?_⟩
      rw [← huz, plift_val hp hk1]
      exact dvd_mul_right p u.val
    · rintro ⟨hz, hzdvd⟩
      exact ⟨_, by rw [plift_div hp hk1 z hzdvd]; exact hz, plift_div hp hk1 z hzdvd⟩
  have hBT : B.card = T.card := by
    rw [← himage, Finset.card_image_of_injective T (plift_injective hp hk1)]
  -- reduction to `ZMod (p^(k-2))`
  have hψ : p ^ (k - 2) ∣ p ^ (k - 1) := Nat.pow_dvd_pow p (by omega)
  set T' : Finset (ZMod (p ^ (k - 1))) :=
    (Finset.univ : Finset (ZMod (p ^ (k - 1)))).filter
      (fun u => (ZMod.castHom hψ (ZMod (p ^ (k - 2))) u) ^ 2 = (b : ZMod (p ^ (k - 2)))) with hT'
  have hψu : ∀ u : ZMod (p ^ (k - 1)),
      ZMod.castHom hψ (ZMod (p ^ (k - 2))) u = (u.val : ZMod (p ^ (k - 2))) := by
    intro u
    conv_lhs => rw [← ZMod.natCast_zmod_val u]
    exact castHom_natCast hψ (ZMod (p ^ (k - 2))) u.val
  have hTT : T = T' := by
    apply Finset.filter_congr
    intro u _
    have hpk : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ 2 * (p : ℤ) ^ (k - 2) := by
      rw [Nat.cast_pow, ← pow_add, Nat.add_sub_cancel' hk]
    have hL : (plift p k u) ^ 2 = (a : ZMod (p ^ k))
        ↔ (p : ℤ) ^ (k - 2) ∣ (u.val : ℤ) ^ 2 - b := by
      rw [plift, natCast_sq_eq_iff_dvd, hpk, ha,
        show ((p * u.val : ℕ) : ℤ) ^ 2 = (p : ℤ) ^ 2 * (u.val : ℤ) ^ 2 by push_cast; ring,
        ← mul_sub]
      rw [mul_dvd_mul_iff_left (pow_ne_zero 2 (by exact_mod_cast hp.ne_zero) : (p : ℤ) ^ 2 ≠ 0)]
    have hR : (ZMod.castHom hψ (ZMod (p ^ (k - 2))) u) ^ 2 = (b : ZMod (p ^ (k - 2)))
        ↔ (p : ℤ) ^ (k - 2) ∣ (u.val : ℤ) ^ 2 - b := by
      rw [hψu, natCast_sq_eq_iff_dvd, Nat.cast_pow]
    exact hL.trans hR.symm
  have hT'card : T'.card = p * Cnt (p ^ (k - 2)) b := by
    have hmain : ((Finset.univ : Finset (ZMod (p ^ (k - 1)))).filter
          (fun u => (ZMod.castHom hψ (ZMod (p ^ (k - 2))) u) ^ 2 = (b : ZMod (p ^ (k - 2))))).card
        = p * Cnt (p ^ (k - 2)) b := by
      have h := card_filter_sq_castHom (m := p ^ (k - 2)) (n := p ^ (k - 1)) hψ b
      have hCnt : Cnt (p ^ (k - 2)) b
          = ((Finset.univ : Finset (ZMod (p ^ (k - 2)))).filter
              (fun w => w ^ 2 = (b : ZMod (p ^ (k - 2))))).card := rfl
      have hdivp : p ^ (k - 1) / p ^ (k - 2) = p := by
        have : p ^ (k - 1) = p ^ (k - 2) * p := by
          rw [← pow_succ]
          congr 1
          omega
        rw [this, Nat.mul_div_cancel_left p (pow_pos hp.pos _)]
      rw [hdivp] at h
      rw [hCnt]
      exact h
    rw [hT']
    exact hmain
  calc Cnt (p ^ k) a = A.card := by rw [Cnt, hA]
    _ = B.card := by rw [hBA]
    _ = T.card := hBT
    _ = T'.card := by rw [hTT]
    _ = p * Cnt (p ^ (k - 2)) b := hT'card
    _ = p * Cnt (p ^ (k - 2)) (a / (p : ℤ) ^ 2) := by rw [hb]

/-- For a prime `p`, `k ≥ 1` and any `a : ℤ`, the number of square roots of `a` modulo `p ^ k`
is at most `4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ k))`. -/
theorem count_sqroot_prime_pow_self (p k : ℕ) (hp : p.Prime) [NeZero (p ^ k)] (hk : 1 ≤ k) (a : ℤ) :
    ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun z => z ^ 2 = (a : ZMod (p ^ k)))).card
      ≤ 4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ k)) := by
  have h : ∀ k : ℕ, [NeZero (p ^ k)] → ∀ a : ℤ,
      Cnt (p ^ k) a ≤ 4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro _ a
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · -- `k = 0`
        subst hk0
        have hle1 : Cnt (p ^ 0) a ≤ 4 := by
          have hc : Cnt (p ^ 0) a ≤ 1 := by
            rw [Cnt]
            calc ((Finset.univ : Finset (ZMod (p ^ 0))).filter
                  (fun z => z ^ 2 = (a : ZMod (p ^ 0)))).card
                ≤ (Finset.univ : Finset (ZMod (p ^ 0))).card := Finset.card_filter_le _ _
              _ = Fintype.card (ZMod (p ^ 0)) := Finset.card_univ
              _ = p ^ 0 := ZMod.card _
              _ = 1 := pow_zero p
          omega
        have hrhs : 4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ 0)) = 4 := by
          rw [pow_zero, Nat.gcd_one_right, Nat.sqrt_one, mul_one]
        rw [hrhs]
        exact hle1
      · rcases Nat.lt_or_ge k 2 with hk1 | hk2
        · -- `k = 1`
          have hk1' : k = 1 := by omega
          subst hk1'
          have hle : Cnt (p ^ 1) a ≤ 4 := by
            by_cases hunit : IsUnit ((a : ℤ) : ZMod (p ^ 1))
            · exact roots_card_le_four_unit p 1 hp le_rfl a hunit
            · haveI : Fact (Nat.Prime (p ^ 1)) := ⟨by simpa using hp⟩
              have ha0 : ((a : ℤ) : ZMod (p ^ 1)) = 0 := by
                have hdv : p ∣ ((a : ℤ) : ZMod (p ^ 1)).val := by
                  by_contra hnot
                  exact hunit ((isUnit_iff_not_dvd_val hp (by norm_num) _).mpr hnot)
                have hlt : ((a : ℤ) : ZMod (p ^ 1)).val < p := by
                  have := ZMod.val_lt ((a : ℤ) : ZMod (p ^ 1))
                  simpa using this
                exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdv hlt)
              have hle1 : Cnt (p ^ 1) a ≤ 1 := by
                rw [Cnt]
                have hsub : ((Finset.univ : Finset (ZMod (p ^ 1))).filter
                      (fun z => z ^ 2 = (a : ZMod (p ^ 1))))
                    ⊆ ({0} : Finset (ZMod (p ^ 1))) := by
                  intro z hz
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
                  rw [Finset.mem_singleton]
                  exact mul_self_eq_zero.mp (by rw [← pow_two, hz, ha0])
                have := Finset.card_le_card hsub
                simpa using this
              omega
          have hg : 1 ≤ Nat.sqrt (Nat.gcd a.natAbs (p ^ 1)) := by
            apply Nat.le_sqrt'.mpr
            have hpos : 0 < Nat.gcd a.natAbs (p ^ 1) :=
              Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right a.natAbs (p ^ 1)) (pow_pos hp.pos 1)
            have h1 : (1 : ℕ) ≤ Nat.gcd a.natAbs (p ^ 1) := by omega
            simpa using h1
          calc Cnt (p ^ 1) a ≤ 4 := hle
            _ = 4 * 1 := (mul_one 4).symm
            _ ≤ 4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ 1)) := Nat.mul_le_mul_left 4 hg
        · -- `k ≥ 2`
          by_cases hpdvd : p ∣ a.natAbs
          · by_cases hp2dvd : p ^ 2 ∣ a.natAbs
            · -- reduction step
              have hdiv : (p : ℤ) ^ 2 ∣ a := by
                simpa using ((natAbs_dvd_intCast_iff (p ^ 2) a).mp hp2dvd)
              haveI : NeZero (p ^ (k - 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
              have hrec := cnt_eq_mul_pred hp hk2 a hdiv
              have hih := ih (k - 2) (by omega) (a / (p : ℤ) ^ 2)
              have hnatAbs : a.natAbs = p ^ 2 * (a / (p : ℤ) ^ 2).natAbs := by
                set c : ℤ := a / (p : ℤ) ^ 2 with hc
                have ha' : a = (p : ℤ) ^ 2 * c := (Int.mul_ediv_cancel' hdiv).symm
                rw [ha', Int.natAbs_mul]
                simp
              have hpk : p ^ k = p ^ 2 * p ^ (k - 2) := by
                rw [← pow_add, Nat.add_sub_cancel' hk2]
              have hgcd : Nat.gcd a.natAbs (p ^ k)
                  = p ^ 2 * Nat.gcd (a / (p : ℤ) ^ 2).natAbs (p ^ (k - 2)) := by
                rw [hnatAbs, hpk, Nat.gcd_mul_left]
              have hsqrt : p * Nat.sqrt (Nat.gcd (a / (p : ℤ) ^ 2).natAbs (p ^ (k - 2)))
                  ≤ Nat.sqrt (Nat.gcd a.natAbs (p ^ k)) := by
                rw [hgcd, Nat.le_sqrt', mul_pow]
                exact Nat.mul_le_mul_left _ (Nat.sqrt_le' _)
              calc Cnt (p ^ k) a = p * Cnt (p ^ (k - 2)) (a / (p : ℤ) ^ 2) := hrec
                _ ≤ p * (4 * Nat.sqrt (Nat.gcd (a / (p : ℤ) ^ 2).natAbs (p ^ (k - 2)))) :=
                    Nat.mul_le_mul_left p hih
                _ = 4 * (p * Nat.sqrt (Nat.gcd (a / (p : ℤ) ^ 2).natAbs (p ^ (k - 2)))) := by ring
                _ ≤ 4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ k)) := Nat.mul_le_mul_left 4 hsqrt
            · -- no solutions
              have hzero : Cnt (p ^ k) a = 0 := by
                rw [Cnt]
                apply Finset.card_eq_zero.mpr
                apply Finset.filter_false_of_mem
                intro z _ hz
                by_cases hzv : p ∣ z.val
                · have hz2 : (p ^ k : ℤ) ∣ (z.val : ℤ) ^ 2 - a := (sq_eq_iff_dvd z a).mp hz
                  have hp2zsq : (p : ℤ) ^ 2 ∣ (z.val : ℤ) ^ 2 := by
                    obtain ⟨c, hc⟩ := hzv
                    exact ⟨(c : ℤ) ^ 2, by rw [hc]; push_cast; ring⟩
                  have hp2a : (p : ℤ) ^ 2 ∣ a := by
                    have h1 : (p : ℤ) ^ 2 ∣ (z.val : ℤ) ^ 2 - a :=
                      dvd_trans (sq_dvd_pow_int hk2) hz2
                    have h3 : (p : ℤ) ^ 2 ∣ ((z.val : ℤ) ^ 2 - a) - (z.val : ℤ) ^ 2 :=
                      dvd_sub h1 hp2zsq
                    have h4 : (p : ℤ) ^ 2 ∣ -a := by
                      convert h3 using 1
                      ring
                    exact (dvd_neg).mp h4
                  exact hp2dvd ((natAbs_dvd_intCast_iff (p ^ 2) a).mpr (by simpa using hp2a))
                · have hunitz : IsUnit z := (isUnit_iff_not_dvd_val hp (by omega) z).mpr hzv
                  have hunita : IsUnit ((a : ℤ) : ZMod (p ^ k)) := by
                    rw [← hz]
                    exact hunitz.pow 2
                  exact ((isUnit_intCast_prime_pow hp (by omega) a).mp hunita) hpdvd
              rw [hzero]
              exact Nat.zero_le _
          · -- `a` is a unit mod `p^k`
            have hunit : IsUnit ((a : ℤ) : ZMod (p ^ k)) :=
              (isUnit_intCast_prime_pow hp (by omega) a).mpr hpdvd
            have hle : Cnt (p ^ k) a ≤ 4 := roots_card_le_four_unit p k hp (by omega) a hunit
            have hgcd : Nat.gcd a.natAbs (p ^ k) = 1 := by
              have h1 : p.Coprime a.natAbs := (hp.coprime_iff_not_dvd).mpr hpdvd
              exact (h1.pow_left k).symm.gcd_eq_one
            rw [hgcd, Nat.sqrt_one, mul_one]
            exact hle
  exact h k a

end Work.FIArea2.R6
