import Mathlib
import Submission.Work.FIArea2.Tsum_odd_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

/-! ### Auxiliary arithmetic lemmas for `ramSum_bound` -/

/-- Divisibility of `b.natAbs` by `m : ℕ` is divisibility of `b : ℤ` by `m`. -/
lemma int_dvd_natAbs (m : ℕ) (b : ℤ) : m ∣ b.natAbs ↔ (m : ℤ) ∣ b := by
  constructor
  · intro hh
    have : ((m : ℤ)).natAbs ∣ b.natAbs := by simpa using hh
    exact (Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := b)).mp this
  · intro hh
    have : ((m : ℤ)).natAbs ∣ b.natAbs := (Int.natAbs_dvd_natAbs (a := (m : ℤ)) (b := b)).mpr hh
    simpa using this

/-- The `p`-adic order of the class of an integer modulo `p^ν` is the `p`-adic valuation of its
absolute value, capped at `ν`. -/
lemma ordv_intCast {p ν : ℕ} (hp : p.Prime) (γ : ℤ) :
    ordv p ν ((γ : ℤ) : ZMod (p ^ ν)) = cval p ν γ.natAbs := by
  haveI : NeZero (p ^ ν) := ⟨pow_ne_zero ν hp.ne_zero⟩
  set v : ℕ := ((γ : ℤ) : ZMod (p ^ ν)).val with hv
  have hvc : (v : ℤ) = γ % (p ^ ν : ℤ) := by rw [hv]; exact ZMod.val_intCast γ
  have hdvdν : (p ^ ν : ℤ) ∣ (v : ℤ) - γ := by
    refine ⟨-(γ / (p ^ ν : ℤ)), ?_⟩
    have h := Int.emod_add_mul_ediv γ (p ^ ν : ℤ)
    rw [hvc]
    linarith
  have key : ∀ j ≤ ν, (p ^ j : ℤ) ∣ (v : ℤ) ↔ (p ^ j : ℤ) ∣ γ := by
    intro j hj
    have hmem : (p ^ j : ℤ) ∣ (p ^ ν : ℤ) := by exact_mod_cast pow_dvd_pow p hj
    have h1 : (p ^ j : ℤ) ∣ (v : ℤ) - γ := dvd_trans hmem hdvdν
    constructor
    · intro h
      have h2 : (p ^ j : ℤ) ∣ γ := by
        have := Int.dvd_sub h h1
        rwa [show (v : ℤ) - ((v : ℤ) - γ) = γ by ring] at this
      exact h2
    · intro h
      have h2 : (p ^ j : ℤ) ∣ (v : ℤ) := by
        have := Int.dvd_add h h1
        rwa [show γ + ((v : ℤ) - γ) = (v : ℤ) by ring] at this
      exact h2
  have hle : cval p ν v ≤ cval p ν γ.natAbs := by
    have h1 : p ^ cval p ν v ∣ v := pow_cval_dvd hp v
    have h2 : (p ^ (cval p ν v) : ℤ) ∣ (v : ℤ) := by exact_mod_cast h1
    have h3 : (p ^ (cval p ν v) : ℤ) ∣ γ := (key (cval p ν v) (cval_le p ν v)).mp h2
    have h4 : p ^ cval p ν v ∣ γ.natAbs := (int_dvd_natAbs _ γ).mpr h3
    exact (dvd_iff_le_cval hp (cval_le p ν v) γ.natAbs).mp h4
  have hge : cval p ν γ.natAbs ≤ cval p ν v := by
    have h1 : p ^ cval p ν γ.natAbs ∣ γ.natAbs := pow_cval_dvd hp γ.natAbs
    have h2 : (p ^ cval p ν γ.natAbs : ℤ) ∣ γ := (int_dvd_natAbs _ γ).mp h1
    have h3 : (p ^ cval p ν γ.natAbs : ℤ) ∣ (v : ℤ) := (key _ (cval_le p ν γ.natAbs)).mpr h2
    have h4 : p ^ cval p ν γ.natAbs ∣ v := by exact_mod_cast h3
    exact (dvd_iff_le_cval hp (cval_le p ν γ.natAbs) v).mp h4
  have hfin : cval p ν ((γ : ℤ) : ZMod (p ^ ν)).val = cval p ν γ.natAbs := by
    rw [← hv]; exact le_antisymm hle hge
  simpa [ordv] using hfin

/-- **Key arithmetic input.**  From `4 a α β = γ` in `ZMod (p^ν)` we get
`min ν (v_p α + v_p β) ≤ v_p γ`: the factor `4 a` contributes a nonnegative `p`-adic order, so it
cannot increase the capped valuation of the product. -/
lemma key_bound {p ν : ℕ} (hp : p.Prime) (a : ℤ) {α β : ZMod (p ^ ν)} {γ : ℤ}
    (hrel : (4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν)) * α * β = ((γ : ℤ) : ZMod (p ^ ν))) :
    min ν (ordv p ν α + ordv p ν β) ≤ cval p ν γ.natAbs := by
  have h1 : cval p ν γ.natAbs = ordv p ν ((((4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν))) * α) * β) := by
    rw [hrel, ordv_intCast hp γ]
  have step1 : ordv p ν α ≤ ordv p ν (((4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν))) * α) := by
    rw [ordv_mul hp]
    exact le_min (ordv_le α) (Nat.le_add_left _ _)
  calc min ν (ordv p ν α + ordv p ν β)
      ≤ min ν (ordv p ν (((4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν))) * α) + ordv p ν β) :=
        min_le_min le_rfl (Nat.add_le_add_right step1 _)
    _ = ordv p ν ((((4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν))) * α) * β) := (ordv_mul hp _ β).symm
    _ = cval p ν γ.natAbs := h1.symm

/-- The capped `p`-adic valuation is compatible with passing from level `ν` down to level `k ≤ ν`. -/
lemma cval_eq_min (p k ν : ℕ) (hk : k ≤ ν) (x : ℕ) : cval p k x = min k (cval p ν x) := by
  unfold cval
  by_cases hx : x = 0
  · subst hx; rw [if_pos rfl, if_pos rfl, min_eq_left hk]
  · rw [if_neg hx, if_neg hx, ← min_assoc, min_eq_left hk]

/-- The elementary exponent inequality controlling a single summand. -/
lemma exp_le (k ν A B : ℕ) (hk : k ≤ ν) (hA : ν - k ≤ A) :
    (ν - k) + min k B ≤ min ν (A + B) := by omega

/-- **The arithmetic bound on the Ramanujan decomposition.**  Let `p` be prime, `ν ≥ 1`, `a` an
integer not divisible by `p` (so `4 a` is a unit modulo `p^ν`), and let `α, β : ZMod (p^ν)` and
`γ : ℤ` satisfy `4 a α β = γ` in `ZMod (p^ν)`.  Then

  `∑_{k=0}^{ν} p^{ν-k} [p^{ν-k} ∣ α.val] ‖ram (p^k) β.val‖ ≤ (ν+1)³ · Nat.gcd (p^ν) |γ|`.

Route.  `‖ram (p^k) c‖ ≤ Nat.gcd (p^k) c.natAbs = p ^ min (k, v_p c)` (by
`Work.FIArea2.ramanujan_primepow` and `Work.FIArea2.gcd_pow_cval`); and `4 a α β = γ` in
`ZMod (p^ν)`, together with `ordv_mul` and `cval_mod`, gives
`min (ν, cval p ν α.val + cval p ν β.val) ≤ cval p ν γ.natAbs` (there is no need for `4a` to be a
unit: `ordv` of the class of `4a` is `≥ 0`; note that for `p = 2` it is not a unit).  For a fixed
`k`, the `k`-th term is nonzero only when `p^{ν-k} ∣ α.val`, i.e. `ν-k ≤ cval p ν α.val`, and then
`(ν-k) + min (k, cval p ν β.val) ≤ min (ν, cval p ν α.val + cval p ν β.val)`; hence every term is at
most `p ^ cval p ν γ.natAbs = Nat.gcd (p^ν) γ.natAbs`, and there are `ν+1 ≤ (ν+1)³` of them. -/
theorem ramSum_bound {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (α β : ZMod (p ^ ν)) (γ : ℤ)
    (hrel : (4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν)) * α * β = ((γ : ℤ) : ZMod (p ^ ν))) :
    (∑ k ∈ Finset.range (ν + 1),
        ((p : ℝ) ^ (ν - k)) * (if p ^ (ν - k) ∣ α.val then (1 : ℝ) else 0)
          * ‖ram (p ^ k) (β.val : ℤ)‖)
      ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := by
  have hterm : ∀ k ∈ Finset.range (ν + 1),
      ((p : ℝ) ^ (ν - k)) * (if p ^ (ν - k) ∣ α.val then (1 : ℝ) else 0)
        * ‖ram (p ^ k) (β.val : ℤ)‖ ≤ (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := by
    intro k hk
    have hkν : k ≤ ν := by
      have := Finset.mem_range.mp hk; omega
    by_cases hd : p ^ (ν - k) ∣ α.val
    · rw [if_pos hd]
      have hnorm : ‖ram (p ^ k) (β.val : ℤ)‖ ≤ (p : ℝ) ^ min k (cval p ν β.val) := by
        calc ‖ram (p ^ k) (β.val : ℤ)‖ ≤ (Nat.gcd (p ^ k) (β.val : ℤ).natAbs : ℝ) :=
              ramanujan_primepow p k hp (β.val : ℤ)
          _ = ((p : ℝ) ^ min k (cval p ν β.val)) := by
              rw [Int.natAbs_natCast, gcd_pow_cval hp (β.val),
                  cval_eq_min p k ν hkν (β.val), Nat.cast_pow]
      have hdivα : ν - k ≤ cval p ν α.val := by
        have h := (dvd_val_iff_le_ordv hp (by omega : ν - k ≤ ν) α).mp hd
        simpa [ordv] using h
      have hexp : (ν - k) + min k (cval p ν β.val) ≤ cval p ν γ.natAbs := by
        have h1 := exp_le k ν (cval p ν α.val) (cval p ν β.val) hkν hdivα
        have h2 := key_bound hp a hrel
        simp only [ordv] at h2
        linarith
      calc ((p : ℝ) ^ (ν - k)) * (1 : ℝ) * ‖ram (p ^ k) (β.val : ℤ)‖
          = (p : ℝ) ^ (ν - k) * ‖ram (p ^ k) (β.val : ℤ)‖ := by ring
        _ ≤ (p : ℝ) ^ (ν - k) * (p : ℝ) ^ (min k (cval p ν β.val)) :=
              mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = (p : ℝ) ^ ((ν - k) + min k (cval p ν β.val)) := (pow_add _ _ _).symm
        _ ≤ (p : ℝ) ^ (cval p ν γ.natAbs) :=
              pow_le_pow_right₀ (by exact_mod_cast hp.one_le) hexp
        _ = (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := by
              rw [gcd_pow_cval hp γ.natAbs, Nat.cast_pow]
    · rw [if_neg hd]
      simp only [mul_zero, zero_mul]
      exact Nat.cast_nonneg _
  calc (∑ k ∈ Finset.range (ν + 1),
        ((p : ℝ) ^ (ν - k)) * (if p ^ (ν - k) ∣ α.val then (1 : ℝ) else 0)
          * ‖ram (p ^ k) (β.val : ℤ)‖)
      ≤ ∑ k ∈ Finset.range (ν + 1), (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := Finset.sum_le_sum hterm
    _ = ((ν : ℝ) + 1) * (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := by
        have hM : (0 : ℝ) ≤ (Nat.gcd (p ^ ν) γ.natAbs : ℝ) := Nat.cast_nonneg _
        have hc : (1 : ℝ) ≤ (ν : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg _
          linarith
        have hsq : (1 : ℝ) ≤ ((ν : ℝ) + 1) ^ 2 := by nlinarith
        have hcu : (ν : ℝ) + 1 ≤ ((ν : ℝ) + 1) ^ 3 := by
          calc (ν : ℝ) + 1 = ((ν : ℝ) + 1) * 1 := by ring
            _ ≤ ((ν : ℝ) + 1) * ((ν : ℝ) + 1) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (by linarith)
            _ = ((ν : ℝ) + 1) ^ 3 := by ring
        exact mul_le_mul_of_nonneg_right hcu hM

end Work.FIArea2
