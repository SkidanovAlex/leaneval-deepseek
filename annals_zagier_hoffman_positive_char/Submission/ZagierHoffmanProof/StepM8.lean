import Submission.ZagierHoffmanProof.StepM6
import Submission.Commons.Data.Nat.step_iter_ge
import Submission.Commons.Data.Nat.step_iter_two_pow_mul
import Submission.Commons.Data.Nat.step_R_pres

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero
open Commons.Data.Nat

/-!
# Step M8: the odd-form digit estimate of Thakur's §8.1

Thakur's analysis at `q = 2` needs the estimate

  `T^i(m+1) ≤ T^i(m+u)`   for odd `m ≥ 1`, `u ≥ 1` with `u &&& (m-1) = 0`,

where `T n = n + 2 ^ v_2(n) = n + lowbit(n)`.

The proof is a strong induction on `m + u`.  If `u` is odd, dividing by `2` reduces the
claim to the commons "no-carry monotonicity" `step_iter_ge`.  If `u = 2v` is even, writing
`m = 2M+1` and `M + 1 = 2^β·u₀` (with `u₀` odd), the condition `v &&& M = 0` forces
`u = 2^{β+1}w` with `w &&& (u₀-1) = 0`, and the claim becomes the same statement for the
strictly smaller pair `(u₀, w)`.
-/

namespace ZagierHoffmanPositiveChar

/-- The lowbit-step map `step n = n + lowbit n` in the form used by the commons API. -/
def stepf (n : ℕ) : ℕ := n + (n - (n &&& (n - 1)))

lemma land_self' (n : ℕ) : n &&& n = n := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_land]
  cases n.testBit i <;> simp

lemma land_le_right' (a b : ℕ) : a &&& b ≤ b := by
  rw [Nat.land_comm]; exact Nat.and_le_left

/-- `step` of an odd number is the successor. -/
lemma stepf_odd {n : ℕ} (hn : Odd n) : stepf n = n + 1 := by
  obtain ⟨c, rfl⟩ := hn
  unfold stepf
  rw [Nat.add_sub_cancel, StepR.land_odd_two, land_self', Nat.add_sub_cancel_left]

/-- Scaling the bitwise "and" by a power of two. -/
lemma land_mul_two_pow (k a b : ℕ) :
    (2 ^ k * a) &&& (2 ^ k * b) = 2 ^ k * (a &&& b) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (2 ^ (k + 1) * a) &&& (2 ^ (k + 1) * b)
          = (2 * (2 ^ k * a)) &&& (2 * (2 ^ k * b)) := by
            rw [pow_succ]; ring_nf
        _ = 2 * ((2 ^ k * a) &&& (2 ^ k * b)) := StepR.land_two_two _ _
        _ = 2 * (2 ^ k * (a &&& b)) := by rw [ih]
        _ = 2 ^ (k + 1) * (a &&& b) := by rw [pow_succ]; ring_nf

/-- The low mask of a natural number is its remainder modulo the corresponding power of two. -/
lemma land_two_pow_sub_one_eq_mod (n k : ℕ) : n &&& (2 ^ k - 1) = n % 2 ^ k := by
  have hlt : n &&& (2 ^ k - 1) < 2 ^ k :=
    lt_of_le_of_lt (land_le_right' n (2 ^ k - 1))
      (Nat.sub_lt (pow_pos (by norm_num) _) Nat.zero_lt_one)
  have h1 : n &&& (2 ^ k - 1) = (n &&& (2 ^ k - 1)) % 2 ^ k := (Nat.mod_eq_of_lt hlt).symm
  rw [h1, Nat.and_mod_two_pow]
  have h2 : (2 ^ k - 1) % 2 ^ k = 2 ^ k - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (pow_pos (by norm_num) _) Nat.zero_lt_one)
  rw [h2, Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.mod_lt n (pow_pos (by norm_num) _))]

/-- For odd `m`, clearing the lowest set bit does nothing. -/
lemma land_pred_self_of_odd' {m : ℕ} (hm : Odd m) : m &&& (m - 1) = m - 1 := by
  obtain ⟨c, rfl⟩ := hm
  rw [Nat.add_sub_cancel, StepR.land_odd_two, land_self']

/-- The lowbit `k - (k &&& (k-1))` is the largest power of two dividing `k`. -/
lemma lowbit_eq_factorization (k : ℕ) (hk : k ≠ 0) :
    k - (k &&& (k - 1)) = 2 ^ k.factorization 2 := by
  set a := k.factorization 2 with ha
  have h2a_dvd : 2 ^ a ∣ k := (Nat.prime_two.pow_dvd_iff_le_factorization hk).mpr (by rw [ha])
  have hk_eq : k = 2 ^ a * (k / 2 ^ a) := (Nat.mul_div_cancel' h2a_dvd).symm
  have hle : 2 ^ a ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h2a_dvd
  have hm_odd : Odd (k / 2 ^ a) := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c, hc⟩
    have h2 : 2 ^ (a + 1) ∣ k := by
      refine ⟨c, ?_⟩
      have hkk : k = 2 ^ a * (c + c) := by rw [hk_eq, hc]
      rw [hkk, pow_succ]; ring
    have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization hk).mp h2
    exact Nat.not_succ_le_self a (ha ▸ h3)
  have hpred : k - 1 = 2 ^ a * (k / 2 ^ a - 1) + (2 ^ a - 1) := by
    have h1 : 2 ^ a * (k / 2 ^ a - 1) = k - 2 ^ a := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_div_cancel' h2a_dvd]
    rw [h1, ← Nat.add_sub_assoc (Nat.one_le_two_pow (n := a)), Nat.sub_add_cancel hle]
  have hmod : (k - 1) % 2 ^ a = 2 ^ a - 1 := by
    rw [hpred, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one)]
  have hdiv : (k - 1) / 2 ^ a = k / 2 ^ a - 1 := by
    rw [hpred, Nat.mul_add_div (Nat.two_pow_pos a),
      Nat.div_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one), Nat.add_zero]
  have e1 : (k &&& (k - 1)) % 2 ^ a = k % 2 ^ a := by
    rw [Nat.and_mod_two_pow, hmod,
      Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.mod_lt k (Nat.two_pow_pos a))]
  have e2 : (k &&& (k - 1)) / 2 ^ a = (k / 2 ^ a) &&& (k / 2 ^ a - 1) := by
    rw [Nat.and_div_two_pow, hdiv]
  have hself : (k / 2 ^ a) &&& (k / 2 ^ a - 1) = k / 2 ^ a - 1 := land_pred_self_of_odd' hm_odd
  have hkmod : k % 2 ^ a = 0 := Nat.dvd_iff_mod_eq_zero.mp h2a_dvd
  have hd : 2 ^ a * ((k &&& (k - 1)) / 2 ^ a) + (k &&& (k - 1)) % 2 ^ a = k &&& (k - 1) :=
    Nat.div_add_mod _ _
  rw [e2, hself, e1, hkmod, Nat.add_zero] at hd
  have hthis : 2 ^ a * (k / 2 ^ a - 1) = k - 2 ^ a := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_div_cancel' h2a_dvd]
  rw [← hd, hthis, Nat.sub_sub_self hle]

/-- `step n = n + 2 ^ v_2(n)` for nonzero `n`. -/
lemma stepf_eq_add_factorization {n : ℕ} (hn : n ≠ 0) :
    stepf n = n + 2 ^ n.factorization 2 := by
  unfold stepf
  rw [lowbit_eq_factorization n hn]

/-- `step` of `2·z` is `2·step z`. -/
lemma stepf_two_mul (z : ℕ) : stepf (2 * z) = 2 * stepf z := by
  have h := stepIter_mul_two_pow 1 z
  simpa only [stepf, pow_one] using h

/-- The iterate of `step` at `2·z`. -/
lemma stepf_iter_two_mul (z i : ℕ) : stepf^[i] (2 * z) = 2 * (stepf^[i] z) := by
  have h := step_iter_two_pow_mul 1 z i
  have h2 : stepf = fun n : ℕ => n + (n - (n &&& (n - 1))) := rfl
  rw [h2]
  simpa only [pow_one] using h


/-- The iterate of `step` at `2^a·z`. -/
lemma stepf_iter_two_pow_mul (a z i : ℕ) :
    stepf^[i] (2 ^ a * z) = 2 ^ a * stepf^[i] z := by
  have h := step_iter_two_pow_mul a z i
  have h2 : stepf = fun n : ℕ => n + (n - (n &&& (n - 1))) := rfl
  rw [h2]
  exact h

/-- The commons no-carry monotonicity, in `stepf` form. -/
lemma stepf_iter_ge_of_land (X v : ℕ) (hX : 1 ≤ X) (h : (X - 1) &&& v = 0) (i : ℕ) :
    stepf^[i] X ≤ stepf^[i] (X + v) := by
  have h1 := step_iter_ge X v hX h i
  have h2 : stepf = fun n : ℕ => n + (n - (n &&& (n - 1))) := rfl
  rw [h2]
  exact h1

/-- **The odd-form digit estimate** of Thakur's §8.1 at `q = 2`. -/
theorem step_iter_ge_odd : ∀ N m u : ℕ, m + u ≤ N → Odd m → 1 ≤ u → (m - 1) &&& u = 0 →
    ∀ i, stepf^[i] (m + 1) ≤ stepf^[i] (m + u) := by
  intro N
  induction N with
  | zero => intro m u hN hm hu h i; omega
  | succ N ih =>
    intro m u hN hm hu h
    by_cases hod : Odd u
    · -- `u` odd: divide by `2` and apply the no-carry monotonicity
      obtain ⟨w, rfl⟩ := hod
      obtain ⟨M, rfl⟩ := hm
      have hMland : M &&& w = 0 := by
        have h' : (2 * M) &&& (2 * w + 1) = 0 := by
          have hm1 : 2 * M + 1 - 1 = 2 * M := by omega
          rwa [hm1] at h
        rw [StepR.land_two_odd] at h'
        omega
      intro i
      have h1 : 2 * M + 1 + 1 = 2 * (M + 1) := by ring
      have h2 : 2 * M + 1 + (2 * w + 1) = 2 * (M + 1 + w) := by ring
      rw [h1, h2, stepf_iter_two_mul, stepf_iter_two_mul]
      refine Nat.mul_le_mul_left _ ?_
      exact stepf_iter_ge_of_land (M + 1) w (by omega) hMland i
    · -- `u` even: reduce to the same statement for the pair `(u₀, w)`
      have hev : Even u := Nat.not_odd_iff_even.mp hod
      obtain ⟨v, rfl⟩ := hev
      have hv1 : 1 ≤ v := by omega
      obtain ⟨M, rfl⟩ := hm
      have hMland : M &&& v = 0 := by
        have h' : (2 * M) &&& (2 * v) = 0 := by
          have hm1 : 2 * M + 1 - 1 = 2 * M := by omega
          have hv2 : v + v = 2 * v := by ring
          rw [hv2] at h
          rwa [hm1] at h
        rw [StepR.land_two_two] at h'
        omega
      set β := (M + 1).factorization 2 with hβ
      have hM1_dvd : 2 ^ β ∣ M + 1 := by
        rw [hβ]; exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
      have hMeq : 2 ^ β * ((M + 1) / 2 ^ β) = M + 1 := Nat.mul_div_cancel' hM1_dvd
      have hu₀_odd : Odd ((M + 1) / 2 ^ β) := by
        rw [← Nat.not_even_iff_odd]
        rintro ⟨c, hc⟩
        have h2 : 2 ^ (β + 1) ∣ M + 1 := by
          refine ⟨c, ?_⟩
          calc M + 1 = 2 ^ β * ((M + 1) / 2 ^ β) := hMeq.symm
            _ = 2 ^ β * (c + c) := by rw [hc]
            _ = 2 ^ (β + 1) * c := by rw [pow_succ]; ring
        have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h2
        exact Nat.not_succ_le_self β (hβ ▸ h3)
      set u₀ := (M + 1) / 2 ^ β with hu₀
      have hMeq' : 2 ^ β * u₀ = M + 1 := hMeq
      have hu₀_pos : 1 ≤ u₀ := by
        have : 0 < u₀ := by
          rcases Nat.eq_zero_or_pos u₀ with hz | hp
          · rw [hz, mul_zero] at hMeq'; omega
          · exact hp
        omega
      have hMdecomp : M = 2 ^ β * (u₀ - 1) + (2 ^ β - 1) := by
        have h1 : 2 ^ β * (u₀ - 1) = 2 ^ β * u₀ - 2 ^ β := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        rw [h1, hMeq']
        have hle : 2 ^ β ≤ M + 1 := Nat.le_of_dvd (by omega) hM1_dvd
        have h1le : 1 ≤ 2 ^ β := Nat.one_le_two_pow
        omega
      have hxy : (2 ^ β * (u₀ - 1)) &&& (2 ^ β - 1) = 0 := by
        rw [land_two_pow_sub_one_eq_mod]
        exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_right _ _)
      have hsub : (2 ^ β * (u₀ - 1)) &&& M = 2 ^ β * (u₀ - 1) := by
        rw [hMdecomp, StepR.land_eq_zero_add_lor _ _ hxy]
        exact StepR.land_lor_self _ _
      have hv_dvd : 2 ^ β ∣ v := by
        have h1 : v &&& (2 ^ β - 1) = 0 := by
          have h2 : M &&& (2 ^ β - 1) = 2 ^ β - 1 := by
            rw [land_two_pow_sub_one_eq_mod, hMdecomp, Nat.mul_add_mod_self_left]
            exact Nat.mod_eq_of_lt (Nat.sub_lt (pow_pos (by norm_num) _) Nat.zero_lt_one)
          calc v &&& (2 ^ β - 1) = v &&& (M &&& (2 ^ β - 1)) := by rw [h2]
            _ = (v &&& M) &&& (2 ^ β - 1) := by rw [Nat.land_assoc]
            _ = 0 := by rw [Nat.land_comm v M, hMland]; simp
        rw [land_two_pow_sub_one_eq_mod] at h1
        exact Nat.dvd_iff_mod_eq_zero.mpr h1
      set w := v / 2 ^ β with hw
      have hveq : v = 2 ^ β * w := (Nat.mul_div_cancel' hv_dvd).symm
      have hw1 : 1 ≤ w := by
        have hpos : 0 < w := by
          rcases Nat.eq_zero_or_pos w with hz | hp
          · rw [hz, mul_zero] at hveq; omega
          · exact hp
        omega
      have huw : (u₀ - 1) &&& w = 0 := by
        have hmain : (2 ^ β * (u₀ - 1)) &&& (2 ^ β * w) = 0 := by
          calc (2 ^ β * (u₀ - 1)) &&& (2 ^ β * w)
              = (2 ^ β * (u₀ - 1)) &&& v := by rw [hveq]
            _ = ((2 ^ β * (u₀ - 1)) &&& M) &&& v := by rw [hsub]
            _ = (2 ^ β * (u₀ - 1)) &&& (M &&& v) := by rw [Nat.land_assoc]
            _ = 0 := by rw [hMland]; exact Nat.and_zero _
        rw [land_mul_two_pow] at hmain
        rcases Nat.mul_eq_zero.mp hmain with h | h
        · exact absurd h (by positivity)
        · exact h
      have hu₀_le : u₀ ≤ M + 1 := by
        have := Nat.div_le_div_left (b := 2 ^ β) (c := 1) (a := M + 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by norm_num)
        simpa [u₀, Nat.div_one] using this
      have hw_le : w ≤ v := by
        have := Nat.div_le_div_left (b := 2 ^ β) (c := 1) (a := v)
          (Nat.one_le_pow _ _ (by norm_num)) (by norm_num)
        simpa [w, Nat.div_one] using this
      have hbound : u₀ + w ≤ N := by omega
      have hIH := ih u₀ w hbound hu₀_odd hw1 huw
      intro i
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        simp only [Function.iterate_zero_apply]
        omega
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [Function.iterate_succ]
        simp only [Function.comp_apply]
        have hstep_u : stepf (2 * M + 1 + (v + v)) = 2 * (M + v + 1) := by
          rw [stepf_odd (show Odd (2 * M + 1 + (v + v)) from ⟨M + v, by ring⟩)]
          ring
        have hstep_1 : stepf (2 * M + 1 + 1) = 2 * (M + 1 + 2 ^ β) := by
          rw [show 2 * M + 1 + 1 = 2 * (M + 1) by ring, stepf_two_mul,
            stepf_eq_add_factorization (by omega : M + 1 ≠ 0)]
        rw [hstep_u, hstep_1, stepf_iter_two_mul, stepf_iter_two_mul]
        refine Nat.mul_le_mul_left _ ?_
        have hA : M + v + 1 = 2 ^ β * (u₀ + w) := by rw [hveq, mul_add]; omega
        have hB : M + 1 + 2 ^ β = 2 ^ β * (u₀ + 1) := by rw [← hMeq']; ring
        rw [hA, hB, stepf_iter_two_pow_mul, stepf_iter_two_pow_mul]
        refine Nat.mul_le_mul_left _ ?_
        exact hIH j

/-- The odd-form digit estimate, without the bookkeeping parameter. -/
theorem step_iter_ge_odd' (m u : ℕ) (hm : Odd m) (hu : 1 ≤ u) (h : (m - 1) &&& u = 0) (i : ℕ) :
    stepf^[i] (m + 1) ≤ stepf^[i] (m + u) :=
  step_iter_ge_odd (m + u) m u le_rfl hm hu h i

end ZagierHoffmanPositiveChar
