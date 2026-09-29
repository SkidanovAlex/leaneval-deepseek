import Mathlib
import Submission.Work.Haupt.defs

/-! # The Landen-type theta identity `θ₃(x)·θ₄(x) = θ₄(x²)²`

Formalises `Work.Haupt.theta_landen`.  The proof is a direct manipulation of the defining
theta series: the product `θ₃(x)θ₄(x)` is written as a double sum over `ℤ × ℤ`, the summation
variable is symmetrised (which replaces the summand by its average over the two coordinates,
i.e. by the part supported on `n ≡ m (mod 2)`), and reindexing by the bijection
`(p,q) ↦ (p+q, p-q)` turns it into the square of the theta series `θ₄(x²)`. -/

namespace Work.Haupt

set_option maxHeartbeats 4000000

open scoped BigOperators

noncomputable section

/-! ## Summability of the elementary theta series -/

lemma summable_int_pow_natAbs (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ n.natAbs) := by
  have hg : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one (x := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  apply Summable.of_nat_of_neg_add_one
  · simpa using hg
  · have h2 : Summable (fun n : ℕ => r ^ (n + 1)) := by
      simpa [pow_succ'] using hg.mul_left r
    convert h2 using 1
    ext n
    rw [show ((-(↑n + 1) : ℤ)).natAbs = n + 1 by omega]

lemma summable_int_pow_sq_theta_landen (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ (n ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_int_pow_natAbs r hr0 hr1)
  · rw [← Int.natAbs_sq n, ← Nat.cast_pow, zpow_natCast]
    exact pow_nonneg hr0 _
  · rw [← Int.natAbs_sq n, ← Nat.cast_pow, zpow_natCast]
    exact pow_le_pow_of_le_one hr0 hr1.le (by simpa [pow_two] using Nat.le_mul_self n.natAbs)

lemma summable_norm_theta3 (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun n : ℤ => ‖x ^ (n ^ 2)‖) :=
  (summable_int_pow_sq_theta_landen ‖x‖ (norm_nonneg x) hx).congr (fun n => (norm_zpow x (n ^ 2)).symm)

lemma summable_norm_theta4 (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun n : ℤ => ‖(-1 : ℂ) ^ n * x ^ (n ^ 2)‖) := by
  refine Summable.of_norm_bounded (summable_int_pow_sq_theta_landen ‖x‖ (norm_nonneg x) hx) (fun n => ?_)
  rw [norm_mul, norm_zpow, norm_zpow]
  simp

lemma summable_norm_theta4sq (x : ℂ) (hx : ‖x‖ < 1) :
    Summable (fun n : ℤ => ‖(-1 : ℂ) ^ n * (x ^ 2) ^ (n ^ 2)‖) := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  refine Summable.of_norm_bounded (summable_int_pow_sq_theta_landen ‖x ^ 2‖ (norm_nonneg _) hx2) (fun n => ?_)
  rw [norm_mul, norm_zpow, norm_zpow]
  simp

/-! ## Elementary auxiliary lemmas -/

/-- For nonnegative exponents, powers add. -/
lemma zpow_mul_zpow_of_nonneg {x : ℂ} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    x ^ m * x ^ n = x ^ (m + n) := by
  have hm' : m = (m.toNat : ℤ) := (Int.toNat_of_nonneg hm).symm
  have hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
  rw [hm', hn', ← Nat.cast_add]
  simp only [zpow_natCast, pow_add]

lemma negOne_zpow_even {a : ℤ} (h : Even a) : (-1 : ℂ) ^ a = 1 := by
  rw [← Int.cast_negOnePow ℂ a, Int.negOnePow_even a h]
  norm_num

lemma negOne_zpow_odd {a : ℤ} (h : Odd a) : (-1 : ℂ) ^ a = -1 := by
  rw [← Int.cast_negOnePow ℂ a, Int.negOnePow_odd a h]
  norm_num

lemma negOne_zpow_eq_of_even {a b : ℤ} (h : Even (a - b)) :
    (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
  have h2 : a.negOnePow = b.negOnePow := (Int.negOnePow_eq_iff a b).mpr h
  rw [← Int.cast_negOnePow ℂ a, ← Int.cast_negOnePow ℂ b, h2]

/-- If `a` and `b` have different parities then `((-1)^a + (-1)^b)/2 = 0`. -/
lemma neg_one_zpow_sum_eq_zero {a b : ℤ} (h : a % 2 ≠ b % 2) :
    ((-1 : ℂ) ^ a + (-1 : ℂ) ^ b) / 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · exact absurd (by rw [ha, hb]) h
  · rw [negOne_zpow_even (Int.even_iff.mpr ha), negOne_zpow_odd (Int.odd_iff.mpr hb)]
    norm_num
  · rw [negOne_zpow_odd (Int.odd_iff.mpr ha), negOne_zpow_even (Int.even_iff.mpr hb)]
    norm_num
  · exact absurd (by rw [ha, hb]) h

/-- The bijection `(p,q) ↦ (p+q, p-q)` onto the pairs of equal parity. -/
def phiL : ℤ × ℤ → ℤ × ℤ := fun z => (z.1 + z.2, z.1 - z.2)

lemma phiL_injective : Function.Injective phiL := by
  intro a b h
  simp only [phiL, Prod.mk.injEq] at h
  ext <;> omega

/-! ## The Landen identity -/

theorem theta_landen (x : ℂ) (hx : ‖x‖ < 1) : T3 x * T4 x = T4 (x ^ 2) ^ 2 := by
  have hf : Summable (fun n : ℤ => ‖x ^ (n ^ 2)‖) := summable_norm_theta3 x hx
  have hgn : Summable (fun n : ℤ => ‖(-1 : ℂ) ^ n * x ^ (n ^ 2)‖) := summable_norm_theta4 x hx
  have hgsn : Summable (fun n : ℤ => ‖(-1 : ℂ) ^ n * (x ^ 2) ^ (n ^ 2)‖) :=
    summable_norm_theta4sq x hx
  have hT3 : T3 x = ∑' n : ℤ, x ^ (n ^ 2) := rfl
  have hT4 : T4 x = ∑' n : ℤ, (-1 : ℂ) ^ n * x ^ (n ^ 2) := rfl
  have hT4sq : T4 (x ^ 2) = ∑' n : ℤ, (-1 : ℂ) ^ n * (x ^ 2) ^ (n ^ 2) := rfl
  -- ### Step 1: expand the product as a double sum
  have step1 : T3 x * T4 x =
      ∑' z : ℤ × ℤ, x ^ (z.1 ^ 2) * ((-1 : ℂ) ^ z.2 * x ^ (z.2 ^ 2)) := by
    rw [hT3, hT4]
    exact tsum_mul_tsum_of_summable_norm (f := fun n : ℤ => x ^ (n ^ 2))
      (g := fun n : ℤ => (-1 : ℂ) ^ n * x ^ (n ^ 2)) hf hgn
  -- ### the three auxiliaries
  set G : ℤ × ℤ → ℂ := fun z => x ^ (z.1 ^ 2) * ((-1 : ℂ) ^ z.2 * x ^ (z.2 ^ 2)) with hG
  set Gsw : ℤ × ℤ → ℂ := fun z => ((-1 : ℂ) ^ z.1 * x ^ (z.1 ^ 2)) * x ^ (z.2 ^ 2) with hGsw
  set H : ℤ × ℤ → ℂ :=
    fun z => (((-1 : ℂ) ^ z.1 + (-1 : ℂ) ^ z.2) / 2) * (x ^ (z.1 ^ 2) * x ^ (z.2 ^ 2))
    with hH
  have hGsum : Summable G := by
    rw [hG]
    exact summable_mul_of_summable_norm (f := fun n : ℤ => x ^ (n ^ 2))
      (g := fun n : ℤ => (-1 : ℂ) ^ n * x ^ (n ^ 2)) hf hgn
  have hGswsum : Summable Gsw := by
    rw [hGsw]
    exact summable_mul_of_summable_norm (f := fun n : ℤ => (-1 : ℂ) ^ n * x ^ (n ^ 2))
      (g := fun n : ℤ => x ^ (n ^ 2)) hgn hf
  have hswap : (∑' z, Gsw z) = ∑' z, G z := by
    have hGeq : ∀ z : ℤ × ℤ, Gsw z = G (z.2, z.1) := by
      intro z; simp only [hG, hGsw]; ring
    rw [tsum_congr hGeq]
    exact Equiv.tsum_eq (Equiv.prodComm ℤ ℤ) G
  have hHpt : ∀ z, H z = (G z + Gsw z) / 2 := by
    intro z; rw [hH, hG, hGsw]; ring
  -- ### Step 2: symmetrise
  have step2 : (∑' z, G z) = ∑' z, H z := by
    calc (∑' z, G z)
        = (1 / 2 : ℂ) * (∑' z, G z + ∑' z, Gsw z) := by rw [hswap]; ring
      _ = (1 / 2 : ℂ) * ∑' z, (G z + Gsw z) := by
            rw [Summable.tsum_add hGsum hGswsum]
      _ = ∑' z, (1 / 2 : ℂ) * (G z + Gsw z) :=
            (Summable.tsum_mul_left (1 / 2) (hGsum.add hGswsum)).symm
      _ = ∑' z, H z := tsum_congr (fun z => by rw [hHpt z]; ring)
  -- ### Step 3: reindex by `phiL`
  have step3 : (∑' z, H z) = ∑' z, H (phiL z) := by
    refine tsum_eq_tsum_of_ne_zero_bij (f := H) (g := fun z => H (phiL z))
      (fun p => phiL (p : ℤ × ℤ)) ?_ ?_ ?_
    · intro p q hpq; exact Subtype.ext (phiL_injective hpq)
    · intro w hw
      have hne : (((-1 : ℂ) ^ w.1 + (-1 : ℂ) ^ w.2) / 2) ≠ 0 := by
        intro h0
        exact hw (by simp [hH, h0])
      have hpar : w.1 % 2 = w.2 % 2 := by
        by_contra h
        exact hne (neg_one_zpow_sum_eq_zero h)
      have hsubEven : Even (w.1 - w.2) :=
        Int.even_iff.mpr
          ((Int.emod_eq_emod_iff_emod_sub_eq_zero (m := w.1) (n := 2) (k := w.2)).mp hpar)
      have heven2 : Even (w.1 + w.2) := by
        have h1 : w.1 + w.2 = (w.1 - w.2) + 2 * w.2 := by ring
        rw [h1]; exact Even.add hsubEven (even_two_mul w.2)
      obtain ⟨l, hl⟩ := hsubEven
      obtain ⟨k, hk⟩ := heven2
      have hval : phiL (k, l) = w := by
        obtain ⟨w1, w2⟩ := w
        rw [phiL]
        exact Prod.ext (by omega) (by omega)
      exact ⟨⟨(k, l), by show H (phiL (k, l)) ≠ 0; rw [hval]; exact hw⟩, hval⟩
    · intro p; rfl
  -- ### Step 4: identify with `T4 (x^2)^2`
  have hprod : T4 (x ^ 2) * T4 (x ^ 2) =
      ∑' z : ℤ × ℤ,
        ((-1 : ℂ) ^ z.1 * (x ^ 2) ^ (z.1 ^ 2)) * ((-1 : ℂ) ^ z.2 * (x ^ 2) ^ (z.2 ^ 2)) := by
    rw [hT4sq]
    exact tsum_mul_tsum_of_summable_norm
      (f := fun n : ℤ => (-1 : ℂ) ^ n * (x ^ 2) ^ (n ^ 2))
      (g := fun n : ℤ => (-1 : ℂ) ^ n * (x ^ 2) ^ (n ^ 2)) hgsn hgsn
  have step4 : (∑' z, H (phiL z)) = T4 (x ^ 2) ^ 2 := by
    rw [pow_two, hprod]
    apply tsum_congr
    intro z
    have h1 : (-1 : ℂ) ^ (z.1 - z.2) = (-1 : ℂ) ^ (z.1 + z.2) :=
      negOne_zpow_eq_of_even (a := z.1 - z.2) (b := z.1 + z.2) ⟨-z.2, by ring⟩
    have hx1 : x ^ ((z.1 + z.2) ^ 2) * x ^ ((z.1 - z.2) ^ 2) =
        x ^ (2 * z.1 ^ 2) * x ^ (2 * z.2 ^ 2) := by
      rw [zpow_mul_zpow_of_nonneg (sq_nonneg _) (sq_nonneg _),
          zpow_mul_zpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      ring
    have hnum : (((-1 : ℂ) ^ (z.1 + z.2) + (-1 : ℂ) ^ (z.1 - z.2)) / 2) =
        (-1 : ℂ) ^ (z.1 + z.2) := by
      rw [h1]; ring
    have hx2 : (x ^ 2) ^ (z.1 ^ 2) = x ^ (2 * z.1 ^ 2) := (zpow_mul x 2 (z.1 ^ 2)).symm
    have hx3 : (x ^ 2) ^ (z.2 ^ 2) = x ^ (2 * z.2 ^ 2) := (zpow_mul x 2 (z.2 ^ 2)).symm
    simp only [hH, phiL]
    rw [hx1, hnum, hx2, hx3, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    ring
  exact step1.trans (step2.trans (step3.trans step4))

end

end Work.Haupt
