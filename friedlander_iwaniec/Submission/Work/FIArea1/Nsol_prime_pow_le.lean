import Mathlib
import Submission.Work.FIArea1.Defs
import Submission.Work.FIArea1.Nsol_div_part_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea1

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The `Fin`-model of `Nsol` -/

/-- `cnt n` is the number of pairs of residues `(r,s)` mod `n` with `n ∣ r² + s²`. -/
def cnt (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => n ∣ z.1.val ^ 2 + z.2.val ^ 2)).card

lemma zsq (n : ℕ) [NeZero n] (z : ZMod n × ZMod n) :
    z.1 ^ 2 + z.2 ^ 2 = ((z.1.val ^ 2 + z.2.val ^ 2 : ℕ) : ZMod n) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z.1, ← ZMod.natCast_zmod_val z.2]
  push_cast
  ring

lemma zsol (n : ℕ) [NeZero n] (z : ZMod n × ZMod n) :
    z.1 ^ 2 + z.2 ^ 2 = 0 ↔ n ∣ z.1.val ^ 2 + z.2.val ^ 2 := by
  rw [zsq, ZMod.natCast_eq_zero_iff]

/-- `Nsol` agrees with the `Fin`-model `cnt`. -/
lemma Nsol_eq_cnt (n : ℕ) [NeZero n] : Nsol n = cnt n := by
  have h1 : Nsol n = Fintype.card {z : ZMod n × ZMod n // z.1 ^ 2 + z.2 ^ 2 = 0} := by
    rw [Nsol]; exact (Set.fintypeCard_eq_ncard _).symm
  have h3 : cnt n = Fintype.card {z : Fin n × Fin n // n ∣ z.1.val ^ 2 + z.2.val ^ 2} := by
    rw [cnt, Fintype.card_subtype]
  have h2 : Fintype.card {z : ZMod n × ZMod n // z.1 ^ 2 + z.2 ^ 2 = 0}
      = Fintype.card {z : Fin n × Fin n // n ∣ z.1.val ^ 2 + z.2.val ^ 2} := by
    apply Fintype.card_congr
    refine {
      toFun := fun z => ⟨(⟨z.1.1.val, ZMod.val_lt _⟩, ⟨z.1.2.val, ZMod.val_lt _⟩), ?_⟩
      invFun := fun w => ⟨((w.1.1.val : ZMod n), (w.1.2.val : ZMod n)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · simpa using (zsol n z.1).mp z.2
    · rw [zsol]
      obtain ⟨⟨a,b⟩, hw⟩ := w
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]
      exact hw
    · intro z; apply Subtype.ext; obtain ⟨⟨a,b⟩, hz⟩ := z
      ext <;> simp [ZMod.natCast_zmod_val]
    · intro w; apply Subtype.ext; obtain ⟨⟨a,b⟩, hw⟩ := w
      ext <;> simp [ZMod.val_natCast, Nat.mod_eq_of_lt]
  rw [h1, h2, h3]

/-! ## 1. Auxiliaries -/

lemma p_dvd_pow_self (p e : ℕ) (he : 1 ≤ e) : p ∣ p ^ e := by
  obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [hk, pow_succ]
  exact dvd_mul_left p _

/-- If `k ∣ n`, `0 < n` and `n < 2k`, then `n = k`. -/
lemma eq_of_dvd_of_lt_two_mul {k n : ℕ} (hk : 0 < k) (hpos : 0 < n) (hdvd : k ∣ n)
    (hlt : n < 2 * k) : n = k := by
  have hc := Nat.div_mul_cancel hdvd
  have hlt2 : n / k < 2 := by rw [Nat.div_lt_iff_lt_mul hk]; omega
  have hge1 : 1 ≤ n / k := by
    rw [Nat.le_div_iff_mul_le hk]
    have := Nat.le_of_dvd hpos hdvd
    omega
  have h1 : n / k = 1 := by omega
  rw [h1, one_mul] at hc
  exact hc.symm

/-- If `p ∤ r.val` and `r² + a² ≡ 0 (mod p^e)`, then `p ∤ a.val`. -/
lemma not_dvd_of_sol {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {r a : Fin (p ^ e)}
    (ha : p ^ e ∣ r.val ^ 2 + a.val ^ 2) (hr : ¬ p ∣ r.val) : ¬ p ∣ a.val := by
  intro hpa
  have hpE : p ∣ p ^ e := p_dvd_pow_self p e he
  have h1 : p ∣ r.val ^ 2 + a.val ^ 2 := hpE.trans ha
  have h2 : p ∣ a.val ^ 2 := by
    obtain ⟨c, hc⟩ := hpa; exact ⟨p * c ^ 2, by rw [hc]; ring⟩
  have h3 : p ∣ r.val ^ 2 := by
    have := Nat.dvd_sub h1 h2
    rwa [Nat.add_sub_cancel] at this
  exact hr (hp.dvd_of_dvd_pow h3)


lemma sq_mod_four (s : ℕ) : s^2 % 4 = 0 ∨ s^2 % 4 = 1 := by
  rcases Nat.even_or_odd s with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk]
    have h : (k+k)^2 = 4*k^2 := by ring
    rw [h, Nat.mul_mod_right]
  · right
    rw [hk]
    have h : (2*k+1)^2 = 4*(k^2+k)+1 := by ring
    rw [h]
    simp [Nat.add_mod, Nat.mul_mod_right]

lemma odd_sq_mod_four (s : ℕ) (hs : Odd s) : s^2 % 4 = 1 := by
  obtain ⟨k, hk⟩ := hs
  rw [hk]
  have h : (2*k+1)^2 = 4*(k^2+k)+1 := by ring
  rw [h]
  simp [Nat.add_mod, Nat.mul_mod_right]

lemma sq_sub_sq_eq (a b : ℕ) (h : b ≤ a) : a^2 - b^2 = (a-b)*(a+b) := by
  have hs : b^2 ≤ a^2 := Nat.pow_le_pow_left h 2
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hs, Nat.cast_sub h]
  push_cast
  ring

lemma aux_add (a b : ℕ) (h : b ≤ a) : (a - b) + (a + b) = 2 * a := by omega

lemma pair_claim_pow_ge {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 1 ≤ e)
    {r a b : Fin (p ^ e)} (hle : b.val ≤ a.val)
    (ha : p ^ e ∣ r.val ^ 2 + a.val ^ 2) (hb : p ^ e ∣ r.val ^ 2 + b.val ^ 2)
    (hr : ¬ p ∣ r.val) : a = b ∨ a.val + b.val = p ^ e := by
  have hpa := not_dvd_of_sol hp he ha hr
  have hpE : p ∣ p ^ e := p_dvd_pow_self p e he
  have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have hle2 := Nat.le_of_dvd (by norm_num) hd
    have h2 := hp.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  have hdvd_mul : p ^ e ∣ (a.val - b.val)*(a.val + b.val) := by
    have hsub := Nat.dvd_sub ha hb
    rw [Nat.add_sub_add_left] at hsub
    rwa [sq_sub_sq_eq a.val b.val hle] at hsub
  rcases hp.dvd_mul.mp (hpE.trans hdvd_mul) with h | h
  · have hnb : ¬ p ∣ a.val + b.val := by
      intro hcon
      have h2 : p ∣ 2 * a.val := by
        have hsum := Nat.dvd_add h hcon
        rwa [aux_add a.val b.val hle] at hsum
      rcases (hp.dvd_mul).mp h2 with h2' | h2'
      · exact absurd h2' hp2
      · exact absurd h2' hpa
    have hcop : (p ^ e).Coprime (a.val + b.val) := (hp.coprime_iff_not_dvd.mpr hnb).pow_left e
    have hd : p ^ e ∣ a.val - b.val := hcop.dvd_of_dvd_mul_right hdvd_mul
    left
    rcases Nat.eq_zero_or_pos (a.val - b.val) with h0 | hpos
    · exact Fin.ext (by omega)
    · have hlt : a.val - b.val < p ^ e := lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
      exact absurd (Nat.le_of_dvd hpos hd) (not_le.mpr hlt)
  · have hna : ¬ p ∣ a.val - b.val := by
      intro hcon
      have h2 : p ∣ 2 * a.val := by
        have hsum := Nat.dvd_add h hcon
        rwa [show (a.val + b.val) + (a.val - b.val) = 2 * a.val by omega] at hsum
      rcases (hp.dvd_mul).mp h2 with h2' | h2'
      · exact absurd h2' hp2
      · exact absurd h2' hpa
    have hcop : (p ^ e).Coprime (a.val - b.val) := (hp.coprime_iff_not_dvd.mpr hna).pow_left e
    have hd : p ^ e ∣ a.val + b.val := hcop.dvd_of_dvd_mul_left hdvd_mul
    right
    refine eq_of_dvd_of_lt_two_mul hpe_pos ?_ hd ?_
    · have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun hh => hpa (by rw [hh]; exact dvd_zero p))
      omega
    · have h1 := a.isLt; have h2 := b.isLt; omega

lemma pair_claim_pow {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 1 ≤ e)
    {r a b : Fin (p ^ e)}
    (ha : p ^ e ∣ r.val ^ 2 + a.val ^ 2) (hb : p ^ e ∣ r.val ^ 2 + b.val ^ 2)
    (hr : ¬ p ∣ r.val) : a = b ∨ a.val + b.val = p ^ e := by
  rcases le_total b.val a.val with h | h
  · exact pair_claim_pow_ge hp hodd he h ha hb hr
  · rcases pair_claim_pow_ge hp hodd he h hb ha hr with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (by rw [add_comm]; exact h')

lemma fiber_le_two {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (r : Fin (p ^ e))
    (hr : ¬ p ∣ r.val) :
    ((Finset.univ : Finset (Fin (p ^ e))).filter (fun s => p ^ e ∣ r.val ^ 2 + s.val ^ 2)).card ≤ 2 := by
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2
    rw [← not_lt]
    intro h
    rw [Finset.two_lt_card] at h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact absurd ha (by
      intro hs
      have h4 : 4 ∣ r.val^2 + a.val^2 := by
        have : 2^2 ∣ 2^e := pow_dvd_pow 2 he
        simpa using this.trans hs
      have hrodd : Odd r.val := Nat.not_even_iff_odd.mp (fun hh => hr (even_iff_two_dvd.mp hh))
      have hr4 := odd_sq_mod_four r.val hrodd
      have ha4 := sq_mod_four a.val
      have hmod : (r.val^2 + a.val^2) % 4 ≠ 0 := by
        rw [Nat.add_mod, hr4]
        rcases ha4 with hh | hh
        · rw [hh]; norm_num
        · rw [hh]; norm_num
      exact hmod (Nat.mod_eq_zero_of_dvd h4))
  · have hodd : Odd p := hp.odd_of_ne_two h2
    rw [← not_lt]
    intro h
    rw [Finset.two_lt_card] at h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    have h1 := pair_claim_pow hp hodd (by omega) ha hb hr
    have h2' := pair_claim_pow hp hodd (by omega) ha hc hr
    have h1' : a.val + b.val = p^e := by
      rcases h1 with hh | hh
      · exact absurd hh hab
      · exact hh
    have h2'' : a.val + c.val = p^e := by
      rcases h2' with hh | hh
      · exact absurd hh hac
      · exact hh
    exact hbc (Fin.ext (by omega))

/-! ## 2. The unit fibre bound modulo `p` -/

lemma pair_claim_mod_p {p : ℕ} (hp : p.Prime) {r a b : Fin p}
    (ha : p ∣ r.val ^ 2 + a.val ^ 2) (hb : p ∣ r.val ^ 2 + b.val ^ 2) :
    a = b ∨ a.val + b.val = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : ((r.val ^ 2 + a.val ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact ha
  have hB : ((r.val ^ 2 + b.val ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hb
  push_cast at hA hB
  have heq : ((a.val : ZMod p)) ^ 2 = ((b.val : ZMod p)) ^ 2 := by linear_combination hA - hB
  have hfac : (((a.val : ZMod p) - b.val)) * (((a.val : ZMod p) + b.val)) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hfac with h | h
  · left
    have h2 := (ZMod.natCast_eq_natCast_iff' a.val b.val p).mp (sub_eq_zero.mp h)
    simp only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h2
    exact Fin.ext h2
  · have h0 : ((a.val + b.val : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
    have hdvd : p ∣ a.val + b.val := (ZMod.natCast_eq_zero_iff _ _).mp h0
    rcases Nat.eq_zero_or_pos (a.val + b.val) with hz | hpos
    · left
      exact Fin.ext (by omega)
    · right
      have hlt : a.val + b.val < 2 * p := by
        have h1 := a.isLt; have h2 := b.isLt; omega
      exact eq_of_dvd_of_lt_two_mul hp.pos hpos hdvd hlt

lemma fiber_mod_p_le_two (p : ℕ) (hp : p.Prime) (r : Fin p) :
    ((Finset.univ : Finset (Fin p)).filter (fun s => p ∣ r.val ^ 2 + s.val ^ 2)).card ≤ 2 := by
  rw [← not_lt]
  intro h
  rw [Finset.two_lt_card] at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have h1 := pair_claim_mod_p hp ha hb
  have h2 := pair_claim_mod_p hp ha hc
  have h1' : a.val + b.val = p := by
    rcases h1 with h | h
    · exact absurd h hab
    · exact h
  have h2' : a.val + c.val = p := by
    rcases h2 with h | h
    · exact absurd h hac
    · exact h
  exact hbc (Fin.ext (by omega))

/-! ## 3. Base cases -/

lemma cnt_one : cnt 1 = 1 := by
  rw [cnt]; simp

lemma cnt_prime_le (p : ℕ) (hp : p.Prime) : cnt p ≤ 2 * p := by
  rw [cnt]
  have hmain := Finset.card_le_mul_card_image (f := Prod.fst)
      ((Finset.univ : Finset (Fin p × Fin p)).filter (fun z => p ∣ z.1.val ^ 2 + z.2.val ^ 2))
      2 (fun b hb => ?_)
  · calc ((Finset.univ : Finset (Fin p × Fin p)).filter
          (fun z => p ∣ z.1.val ^ 2 + z.2.val ^ 2)).card
        ≤ 2 * (Finset.image Prod.fst ((Finset.univ : Finset (Fin p × Fin p)).filter
            (fun z => p ∣ z.1.val ^ 2 + z.2.val ^ 2))).card := hmain
      _ ≤ 2 * p := by
          gcongr
          calc _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = p := by simp
  · calc (((Finset.univ : Finset (Fin p × Fin p)).filter
            (fun z => p ∣ z.1.val ^ 2 + z.2.val ^ 2)).filter (fun z => z.1 = b)).card
        ≤ ((Finset.univ : Finset (Fin p)).filter (fun s => p ∣ b.val ^ 2 + s.val ^ 2)).card := by
          apply Finset.card_le_card_of_injOn (fun z => z.2)
          · intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hz ⊢
            rw [← hz.2]
            exact hz.1
          · intro z hz z' hz' heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hz hz'
            exact Prod.ext (by rw [hz.2, hz'.2]) heq
      _ ≤ 2 := fiber_mod_p_le_two p hp b

/-! ## 4. The recursion -/

lemma cnt_rec (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    cnt (p ^ e) ≤ 2 * p ^ e + p ^ 2 * cnt (p ^ (e - 2)) := by
  have hU : ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ p ∣ z.1.val)).card
      ≤ p ^ 2 * cnt (p ^ (e - 2)) := by
    have hsub : ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
          (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ p ∣ z.1.val))
        ⊆ ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
          (fun z => p ∣ z.1.val ∧ p ∣ z.2.val ∧ p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2)) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      refine ⟨hz.2, ?_, hz.1⟩
      have hpE : p ∣ p ^ e := p_dvd_pow_self p e (by omega)
      have h1 : p ∣ z.1.val ^ 2 + z.2.val ^ 2 := hpE.trans hz.1
      have h2 : p ∣ z.1.val ^ 2 := by
        obtain ⟨c, hc⟩ := hz.2; exact ⟨p * c ^ 2, by rw [hc]; ring⟩
      have h3 : p ∣ z.2.val ^ 2 := by
        have := Nat.dvd_sub h1 h2
        rwa [Nat.add_sub_cancel_left] at this
      exact hp.dvd_of_dvd_pow h3
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ p ^ 2 * cnt (p ^ (e - 2)) := by
          simpa [cnt] using Nsol_div_part_le hp he
  have hV : ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ ¬ p ∣ z.1.val)).card ≤ 2 * p ^ e := by
    set V := (Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ ¬ p ∣ z.1.val) with hVdef
    have hmain := Finset.card_le_mul_card_image (f := Prod.fst) V 2 (fun b hb => ?_)
    · calc V.card ≤ 2 * (Finset.image Prod.fst V).card := hmain
        _ ≤ 2 * p ^ e := by
            gcongr
            calc (Finset.image Prod.fst V).card ≤ (Finset.univ : Finset (Fin (p ^ e))).card :=
                  Finset.card_le_card (Finset.subset_univ _)
              _ = p ^ e := by simp
    · have hbT : ¬ p ∣ b.val := by
        rcases Finset.mem_image.mp hb with ⟨z, hz, rfl⟩
        simp only [hVdef, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hz.2
      calc (V.filter (fun z => z.1 = b)).card
          ≤ ((Finset.univ : Finset (Fin (p ^ e))).filter (fun s => p ^ e ∣ b.val ^ 2 + s.val ^ 2)).card := by
            apply Finset.card_le_card_of_injOn (fun z => z.2)
            · intro z hz
              simp only [hVdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hz ⊢
              rw [← hz.2]
              exact hz.1.1
            · intro z hz z' hz' heq
              simp only [hVdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hz hz'
              exact Prod.ext (by rw [hz.2, hz'.2]) heq
        _ ≤ 2 := fiber_le_two hp he b hbT
  have hsplit : cnt (p ^ e) = ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ p ∣ z.1.val)).card
      + ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2 ∧ ¬ p ∣ z.1.val)).card := by
    rw [cnt, ← Finset.card_filter_add_card_filter_not (fun z : Fin (p ^ e) × Fin (p ^ e) => p ∣ z.1.val)]
    simp only [Finset.filter_filter]
  calc cnt (p ^ e) = _ + _ := hsplit
    _ ≤ p ^ 2 * cnt (p ^ (e - 2)) + 2 * p ^ e := add_le_add hU hV
    _ = 2 * p ^ e + p ^ 2 * cnt (p ^ (e - 2)) := by ring

/-! ## 5. The main bound -/

theorem Nsol_prime_pow_le {p e : ℕ} (hp : p.Prime) :
    Work.FIArea1.Nsol (p ^ e) ≤ (e + 1) * p ^ e := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have key : ∀ e, cnt (p ^ e) ≤ (e + 1) * p ^ e := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      rcases e with _ | _ | k
      · show cnt (p ^ 0) ≤ (0 + 1) * p ^ 0
        rw [pow_zero, cnt_one]; norm_num
      · show cnt (p ^ 1) ≤ (1 + 1) * p ^ 1
        rw [pow_one]
        simpa using cnt_prime_le p hp
      · have hrec := cnt_rec p (k + 2) hp (by omega)
        have hih := ih k (by omega)
        have hpow : p ^ (k + 2) = p ^ 2 * p ^ k := by
          rw [show k + 2 = 2 + k by omega, pow_add]
        calc cnt (p ^ (k + 2)) ≤ 2 * p ^ (k + 2) + p ^ 2 * cnt (p ^ ((k + 2) - 2)) := hrec
          _ = 2 * p ^ (k + 2) + p ^ 2 * cnt (p ^ k) := by rw [show (k + 2) - 2 = k by omega]
          _ ≤ 2 * p ^ (k + 2) + p ^ 2 * ((k + 1) * p ^ k) := by gcongr
          _ = (k + 2 + 1) * p ^ (k + 2) := by rw [hpow]; ring
  rw [Nsol_eq_cnt]
  exact key e

end

end Work.FIArea1
