import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The number of `y` in `ZMod (2 ^ n)` with `(y + d) ^ 2 = y ^ 2`

For `d` in `ZMod (2 ^ n)`, the equation `(y + d) ^ 2 = y ^ 2` is equivalent to
`d * (2 * y + d) = 0`, a *linear* congruence in `y`.  Writing `D = d.val` for the
canonical representative in `[0, 2 ^ n)`:

* if `d = 0` the equation holds for every `y`, giving `2 ^ n` solutions;
* if `D` is odd then `D * (2 y + D)` is odd for every `y`, while `2 ^ n` is even
  (`n ≥ 1`), so there are no solutions;
* if `2 ∣ D`, writing `v = padicValNat 2 D`, the congruence is equivalent to
  `y ≡ -D/2 (mod 2 ^ (n - v - 1))`, one residue class modulo `2 ^ (n-v-1)`; since
  `2 ^ (n-v-1) ∣ 2 ^ n` it has `2 ^ (v+1)` solutions in `[0, 2 ^ n)`.

The three lemmas below implement exactly this chain.
-/

namespace Work.FIArea2

/-- **Counting a residue class in `[0, M)`.**  If `k ∣ M` then `Y ↦ Y + c` is divisible
by `k` on a single residue class modulo `k`, and of the `M` integers `0, …, M - 1`
exactly `M / k` lie in it.  The residue is `-(c : ZMod k)).val`, which makes the two
key facts (`k ∣ r + c`, and `k ∣ Y + c → Y % k = r`) pure `ZMod` computations. -/
lemma card_range_filter_dvd_add (M k c : ℕ) (hk : 0 < k) (hdiv : k ∣ M) :
    ((Finset.range M).filter (fun Y => k ∣ Y + c)).card = M / k := by
  haveI : NeZero k := ⟨hk.ne'⟩
  set r : ℕ := (-(c : ZMod k)).val with hr_def
  have hr_lt : r < k := ZMod.val_lt _
  have hr_val : (r : ZMod k) = -(c : ZMod k) := ZMod.natCast_zmod_val _
  have hr_dvd : k ∣ r + c := by
    rw [← ZMod.natCast_eq_zero_iff (r + c) k]
    rw [Nat.cast_add, hr_val]
    simp
  obtain ⟨m, hm⟩ := hdiv
  subst hm
  have hset : (Finset.range (k * m)).filter (fun Y => k ∣ Y + c)
      = (Finset.range m).image (fun j => r + j * k) := by
    ext Y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hY, hdvd⟩
      refine ⟨Y / k, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hk, mul_comm]; exact hY
      · have hmod : Y % k = r := by
          have hYc : (Y : ZMod k) = -(c : ZMod k) := by
            have h : ((Y + c : ℕ) : ZMod k) = 0 :=
              (ZMod.natCast_eq_zero_iff (Y + c) k).mpr hdvd
            rw [Nat.cast_add] at h
            exact (add_eq_zero_iff_eq_neg).mp h
          have hmodeq : Y ≡ r [MOD k] :=
            (ZMod.natCast_eq_natCast_iff Y r k).mp (by rw [hYc, hr_val])
          exact Nat.ModEq.eq_of_lt_of_lt ((Nat.mod_modEq Y k).trans hmodeq)
            (Nat.mod_lt Y hk) hr_lt
        rw [← hmod, Nat.mul_comm (Y / k) k]
        exact Nat.mod_add_div Y k
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ?_⟩
      · have hjk : j * k + k ≤ m * k := by
          have := Nat.mul_le_mul_right k (show j + 1 ≤ m by omega)
          rwa [Nat.add_mul, one_mul] at this
        have := Nat.add_lt_add_right hr_lt (j * k)
        rw [Nat.mul_comm k m]
        exact lt_of_lt_of_le this (by linarith [hjk])
      · rw [show r + j * k + c = (r + c) + j * k by ring]
        exact dvd_add hr_dvd ⟨j, mul_comm j k⟩
  rw [hset, Finset.card_image_of_injective _ (fun a b hab =>
    Nat.mul_right_cancel hk (Nat.add_left_cancel hab)), Finset.card_range]
  exact (Nat.mul_div_right m hk).symm

/-- Transporting a count along the canonical representative `ZMod N → {0, …, N-1}`. -/
lemma card_filter_val_eq (N : ℕ) [NeZero N] (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (ZMod N)).filter (fun y => P y.val)).card
      = ((Finset.range N).filter P).card := by
  refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hy ⊢
    exact ⟨y.val_lt, hy⟩
  · intro y1 _ y2 _ h
    exact ZMod.val_injective N h
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_range] at hY
    refine ⟨(Y : ZMod N), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ZMod.val_natCast_of_lt hY.1]; exact hY.2
    · exact ZMod.val_natCast_of_lt hY.1

/-- The solution condition `(y + d) ^ 2 = y ^ 2` rewritten as a divisibility statement
about the canonical representatives. -/
lemma sq_eq_iff_dvd (n : ℕ) (d y : ZMod (2 ^ n)) :
    (y + d)^2 = y^2 ↔ (2^n) ∣ d.val * (2 * y.val + d.val) := by
  have hring : (y + d)^2 - y^2 = d * (2*y + d) := by ring
  rw [← sub_eq_zero, hring]
  conv_lhs => rw [← ZMod.natCast_zmod_val d, ← ZMod.natCast_zmod_val y]
  rw [show (↑d.val : ZMod (2^n)) * (2 * ↑y.val + ↑d.val)
        = ((d.val * (2 * y.val + d.val) : ℕ) : ZMod (2^n)) by push_cast; ring]
  exact ZMod.natCast_eq_zero_iff _ _

theorem card_y_sols (n : ℕ) (d : ZMod (2 ^ n)) :
    ((Finset.univ : Finset (ZMod (2 ^ n))).filter
      (fun y => (y + d) ^ 2 = y ^ 2)).card
      = if d = 0 then 2 ^ n else if 2 ∣ d.val then 2 ^ (padicValNat 2 d.val + 1) else 0 := by
  haveI : NeZero (2 ^ n) := ⟨(pow_pos (by norm_num) n).ne'⟩
  rw [Finset.filter_congr (fun y _ => sq_eq_iff_dvd n d y)]
  rw [card_filter_val_eq (2 ^ n) (fun Y => 2 ^ n ∣ d.val * (2 * Y + d.val))]
  by_cases hd0 : d = 0
  · rw [if_pos hd0]
    simp [hd0, Finset.card_range]
  · rw [if_neg hd0]
    have hDne : d.val ≠ 0 := by
      intro h
      apply hd0
      rw [← ZMod.natCast_zmod_val d, h]
      simp
    have hDpos : 0 < d.val := Nat.pos_of_ne_zero hDne
    have hDM : d.val < 2 ^ n := d.val_lt
    have hn1 : 1 ≤ n := by
      rcases n with _ | k
      · simp only [pow_zero] at hDM; omega
      · omega
    by_cases h2 : 2 ∣ d.val
    · rw [if_pos h2]
      set v := padicValNat 2 d.val with hv
      set c := d.val / 2 with hc
      have h2c : 2 * c = d.val := by rw [hc]; exact Nat.mul_div_cancel' h2
      have hv_le : 2 ^ v ≤ d.val := by
        rw [hv]; exact Nat.le_of_dvd hDpos pow_padicValNat_dvd
      have hvlt : v < n := by
        have h : 2 ^ v < 2 ^ n := lt_of_le_of_lt hv_le hDM
        rwa [Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)] at h
      have hv1n : v + 1 ≤ n := by omega
      have hcpos : 0 < c := by rw [hc]; omega
      have hiff : ∀ Y : ℕ, (2 ^ n ∣ d.val * (2 * Y + d.val)) ↔ (2 ^ (n - v - 1) ∣ Y + c) := by
        intro Y
        have hYDne : 2 * Y + d.val ≠ 0 := by omega
        have hXne : d.val * (2 * Y + d.val) ≠ 0 := Nat.mul_ne_zero hDne hYDne
        have hYcne : Y + c ≠ 0 := by omega
        have hvaleq : padicValNat 2 (d.val * (2 * Y + d.val))
            = v + 1 + padicValNat 2 (Y + c) := by
          rw [padicValNat.mul hDne hYDne]
          have hstep : 2 * Y + d.val = 2 * (Y + c) := by rw [← h2c]; ring
          rw [hstep, padicValNat.mul (by norm_num : (2:ℕ) ≠ 0) (by omega : Y + c ≠ 0),
              padicValNat_self]
          ring
        rw [padicValNat_dvd_iff n (d.val * (2*Y + d.val)),
            padicValNat_dvd_iff (n - v - 1) (Y + c)]
        simp only [hXne, hYcne, false_or, hvaleq]
        omega
      have hkeq : (Finset.range (2 ^ n)).filter (fun Y => 2 ^ n ∣ d.val * (2 * Y + d.val))
          = (Finset.range (2 ^ n)).filter (fun Y => 2 ^ (n - v - 1) ∣ Y + c) :=
        Finset.filter_congr (fun Y _ => hiff Y)
      rw [hkeq, card_range_filter_dvd_add (2 ^ n) (2 ^ (n - v - 1)) c
        (pow_pos (by norm_num) _) (pow_dvd_pow 2 (by omega))]
      rw [Nat.pow_div (by omega) (by norm_num : 0 < 2)]
      congr 1
      omega
    · rw [if_neg h2]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro Y _
      intro hdvd
      have h2M : 2 ∣ 2 ^ n := by
        have := pow_dvd_pow 2 hn1
        simpa using this
      have hodd : ¬ 2 ∣ d.val * (2 * Y + d.val) := by
        intro h
        rcases Nat.prime_two.dvd_mul.mp h with h1 | h1
        · exact h2 h1
        · have h2Y : 2 ∣ 2 * Y := dvd_mul_right 2 Y
          have hD : 2 ∣ d.val := by
            have := Nat.dvd_sub h1 h2Y
            rwa [Nat.add_sub_cancel_left] at this
          exact h2 hD
      exact hodd (dvd_trans h2M hdvd)

end Work.FIArea2
