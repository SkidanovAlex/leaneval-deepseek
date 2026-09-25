import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT

namespace Work.BourgainPlan.IonescuWainger

/-- The per-tuple smallness hypothesis of `comp_sum_bound_perTuple` follows from `(r,c)`-goodness:
for a core `A₀ ⊆ S` with `|A₀| ≤ k` and petals `A_i ⊆ S ∖ A₀` with `|A_i| ≤ k - |A₀|`, one has
`Q_{A₀} · ∏_i Q_{A_i} ≤ q_max^{|A₀| + r(k-|A₀|)} ≤ q_max^{rk}`, so `2r·ε < c/q_max^{2rk}` gives
`2r·ε·Q_{A₀}·∏_i Q_{A_i} < 1`. -/
theorem petal_smallness_of_good {S : Finset ℕ} {r k qmax : ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hqmax : 1 ≤ qmax) (hmax : ∀ q ∈ S, q ≤ qmax) {c ε : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k)))
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) (hA₀card : A₀.card ≤ k)
    {A : Fin r → Finset ℕ} (hA : ∀ i, A i ⊆ S \ A₀) (hAcard : ∀ i, (A i).card ≤ k - A₀.card) :
    2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA (A i)) : ℕ) : ℝ) < 1 := by
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    simp
  · have hqmaxpos : 0 < qmax := lt_of_lt_of_le Nat.zero_lt_one hqmax
    -- Abbreviate the petal product (this also turns it into the goal's left factor).
    set Qr : ℝ := ((QA A₀ * (∏ i, QA (A i)) : ℕ) : ℝ) with hQrdef
    -- ## The arithmetic bound `Q_{A₀} · ∏_i Q_{A_i} ≤ qmax^{rk}`
    have hQAmax : QA A₀ ≤ qmax ^ A₀.card :=
      Finset.prod_le_pow_card A₀ (fun q => q) qmax (fun q hq => hmax q (hA₀ hq))
    have hQimax : ∀ i, QA (A i) ≤ qmax ^ (k - A₀.card) := by
      intro i
      have hsub : A i ⊆ S := (hA i).trans Finset.sdiff_subset
      exact (Finset.prod_le_pow_card (A i) (fun q => q) qmax
        (fun q hq => hmax q (hsub hq))).trans
        (Nat.pow_le_pow_right hqmaxpos (hAcard i))
    have hQAprod_le : (∏ i, QA (A i)) ≤ ∏ _i : Fin r, qmax ^ (k - A₀.card) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => hQimax i)
    have hprodeq : (∏ _i : Fin r, qmax ^ (k - A₀.card)) = qmax ^ (r * (k - A₀.card)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      congr 1
      ring
    have hexp : A₀.card + r * (k - A₀.card) ≤ r * k := by
      have h1 : A₀.card ≤ r * A₀.card := Nat.le_mul_of_pos_left A₀.card hrpos
      calc A₀.card + r * (k - A₀.card)
          ≤ r * A₀.card + r * (k - A₀.card) := Nat.add_le_add_right h1 _
        _ = r * (A₀.card + (k - A₀.card)) := (Nat.mul_add r A₀.card (k - A₀.card)).symm
        _ = r * k := by rw [Nat.add_sub_of_le hA₀card]
    have hQle : QA A₀ * ∏ i, QA (A i) ≤ qmax ^ (r * k) := by
      calc QA A₀ * ∏ i, QA (A i)
          ≤ qmax ^ A₀.card * qmax ^ (r * (k - A₀.card)) :=
            Nat.mul_le_mul hQAmax (hQAprod_le.trans_eq hprodeq)
        _ = qmax ^ (A₀.card + r * (k - A₀.card)) := (pow_add qmax _ _).symm
        _ ≤ qmax ^ (r * k) := Nat.pow_le_pow_right hqmaxpos hexp
    -- ## Casting to `ℝ`
    have hM1 : (1 : ℝ) ≤ (qmax : ℝ) := by
      have h := Nat.cast_le (α := ℝ).mpr hqmax
      simpa using h
    have hMpos : (0 : ℝ) < (qmax : ℝ) := lt_of_lt_of_le zero_lt_one hM1
    have hRpos : (0 : ℝ) < (r : ℝ) := by
      have h := Nat.cast_pos (α := ℝ).mpr hrpos
      simpa using h
    have h2Rpos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
    have hQr : 0 ≤ Qr := by rw [hQrdef]; exact Nat.cast_nonneg _
    have hQbound : Qr ≤ (qmax : ℝ) ^ (r * k) := by
      rw [hQrdef]
      have h := Nat.cast_le (α := ℝ).mpr hQle
      rwa [Nat.cast_pow] at h
    have hdivnn : 0 ≤ c / (qmax : ℝ) ^ (2 * r * k) :=
      div_nonneg hc.le (pow_pos hMpos _).le
    have heq : 2 * (r : ℝ) * (c / (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k)))
        = c / (qmax : ℝ) ^ (2 * r * k) := by
      rw [← mul_div_assoc, mul_div_mul_left c ((qmax : ℝ) ^ (2 * r * k))
        (ne_of_gt h2Rpos)]
    have hstepA : 2 * (r : ℝ) * ε < c / (qmax : ℝ) ^ (2 * r * k) := by
      have h := mul_lt_mul_of_pos_left hgood h2Rpos
      rwa [heq] at h
    have hpow2 : (qmax : ℝ) ^ (2 * r * k)
        = (qmax : ℝ) ^ (r * k) * (qmax : ℝ) ^ (r * k) := by
      rw [show 2 * r * k = r * k + r * k by ring, pow_add]
    have hstepD : (c / (qmax : ℝ) ^ (2 * r * k)) * (qmax : ℝ) ^ (r * k)
        = c / (qmax : ℝ) ^ (r * k) := by
      rw [hpow2, div_mul_eq_mul_div,
        mul_div_mul_right c ((qmax : ℝ) ^ (r * k)) (pow_ne_zero _ hMpos.ne')]
    have hlt1 : c / (qmax : ℝ) ^ (r * k) < 1 := by
      rw [div_lt_one (pow_pos hMpos (r * k))]
      exact lt_of_lt_of_le hc1 (one_le_pow₀ hM1)
    have hmain : 2 * (r : ℝ) * ε * Qr ≤ c / (qmax : ℝ) ^ (r * k) := by
      calc 2 * (r : ℝ) * ε * Qr
          ≤ (c / (qmax : ℝ) ^ (2 * r * k)) * Qr :=
            mul_le_mul_of_nonneg_right hstepA.le hQr
        _ ≤ (c / (qmax : ℝ) ^ (2 * r * k)) * (qmax : ℝ) ^ (r * k) :=
            mul_le_mul_of_nonneg_left hQbound hdivnn
        _ = c / (qmax : ℝ) ^ (r * k) := hstepD
    exact lt_of_le_of_lt hmain hlt1

end Work.BourgainPlan.IonescuWainger
