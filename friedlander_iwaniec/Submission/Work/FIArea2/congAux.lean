import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary lemmas toward the quadratic-congruence count of *FI* §9 (9.9). -/

namespace Work.FIArea2

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Fibres of the reduction map `ZMod n → ZMod m` -/

/-- The fibre of the reduction `ZMod n → ZMod m` (`m ∣ n`) over any point has exactly `n / m`
elements. -/
theorem fiber_card_zmod_castHom {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (c : ZMod m) :
    ((Finset.univ : Finset (ZMod n)).filter (fun x => ZMod.castHom h (ZMod m) x = c)).card
      = n / m := by
  let φ : ZMod n →+ ZMod m := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  change ((Finset.univ : Finset (ZMod n)).filter (fun x => φ x = c)).card = n / m
  have hsurj : Function.Surjective φ := ZMod.castHom_surjective h
  have hfib : (Finset.univ.filter (fun x : ZMod n => φ x = c)).card
      = (Finset.univ.filter (fun x : ZMod n => φ x = 0)).card :=
    (AddMonoidHom.card_fiber_eq_of_mem_range φ (x := 0) (y := c)
      ⟨0, map_zero φ⟩ (hsurj c)).symm
  have hker : (Finset.univ.filter (fun x : ZMod n => φ x = 0)).card = Nat.card φ.ker := by
    have h_eq : (Finset.univ.filter (fun x : ZMod n => φ x = 0))
        = (Finset.univ.filter (fun x : ZMod n => x ∈ φ.ker)) :=
      Finset.filter_congr (fun x _ => AddMonoidHom.mem_ker)
    rw [h_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hidx : φ.ker.index = Nat.card φ.range := by
    rw [AddSubgroup.index_eq_card]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
  have hrange : Nat.card φ.range = m := by
    rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_zmod]
  have hmul : m * Nat.card φ.ker = n := by
    have h1 := AddSubgroup.card_mul_index φ.ker
    rw [hidx, hrange, Nat.card_zmod] at h1
    rw [mul_comm]
    exact h1
  rw [hfib, hker]
  exact Nat.eq_div_of_mul_eq_right (NeZero.ne m) hmul

/-! ### The local ring `ZMod (p^e)` and square roots of units -/

theorem pow_dvd_pow_of_pos {p e : ℕ} (he : 0 < e) : p ∣ p ^ e :=
  ⟨p ^ (e - 1), by rw [← pow_succ', Nat.sub_add_cancel he]⟩

/-- In `ZMod (p^e)` (`p` prime, `e > 0`) an element is a unit iff `p` does not divide its
canonical representative. -/
theorem isUnit_iff_not_dvd_val {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e)
    (x : ZMod (p ^ e)) : IsUnit x ↔ ¬ p ∣ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp he]

theorem dvd_val_add {p e : ℕ} [NeZero (p ^ e)] (he : 0 < e) {a b : ZMod (p ^ e)}
    (ha : p ∣ a.val) (hb : p ∣ b.val) : p ∣ (a + b).val := by
  rw [ZMod.val_add]
  obtain ⟨k, hk⟩ := Nat.dvd_add ha hb
  obtain ⟨l, hl⟩ := pow_dvd_pow_of_pos (p := p) he
  rw [hk, hl, Nat.mul_mod_mul_left]
  exact ⟨k % l, rfl⟩

/-- `ZMod (p^e)` is a local ring (`p` prime, `e > 0`). -/
theorem isLocalRing_zmod_prime_pow (p e : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e) :
    IsLocalRing (ZMod (p ^ e)) := by
  haveI : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he.ne' hp.one_lt⟩
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab => ?_
  rw [isUnit_iff_not_dvd_val hp he] at hab
  simp only [isUnit_iff_not_dvd_val hp he]
  by_cases ha : p ∣ a.val
  · by_cases hb : p ∣ b.val
    · exact absurd (dvd_val_add he ha hb) hab
    · exact Or.inr hb
  · exact Or.inl ha

/-- A unit of `ZMod (p^e)`, `p` odd, has at most two square roots. -/
theorem sq_root_card_le_two {p e : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (c : ZMod (p ^ e)) (hc : IsUnit c) :
    ((Finset.univ : Finset (ZMod (p ^ e))).filter (fun z => z ^ 2 = c)).card ≤ 2 := by
  have he0 : 0 < e := he
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ e)) := by
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp he0]
    intro hdiv
    have h1 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have h2' : 2 ≤ p := hp.two_le
    omega
  have hloc : IsLocalRing (ZMod (p ^ e)) := isLocalRing_zmod_prime_pow p e hp he0
  by_cases hne : (Finset.univ.filter (fun z : ZMod (p ^ e) => z ^ 2 = c)).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz₀
    have hsub : (Finset.univ.filter (fun z : ZMod (p ^ e) => z ^ 2 = c))
        ⊆ ({z₀, -z₀} : Finset (ZMod (p ^ e))) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have h1 : (z - z₀) * (z + z₀) = 0 := by
        have hzz : z ^ 2 = z₀ ^ 2 := by rw [hz, hz₀]
        linear_combination hzz
      have hzun : IsUnit z :=
        ⟨⟨z, z * c⁻¹, by rw [← mul_assoc, ← sq, hz, ZMod.mul_inv_of_unit c hc],
            by rw [mul_comm (z * c⁻¹) z, ← mul_assoc, ← sq, hz,
              ZMod.mul_inv_of_unit c hc]⟩, rfl⟩
      have hsum : IsUnit ((z - z₀) + (z + z₀)) := by
        have hss : (z - z₀) + (z + z₀) = 2 * z := by ring
        rw [hss]; exact h2.mul hzun
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
      · right
        have := (IsUnit.mul_right_eq_zero h).mp h1
        linear_combination this
      · left
        have := (IsUnit.mul_left_eq_zero h).mp h1
        linear_combination this
    calc (Finset.univ.filter (fun z : ZMod (p ^ e) => z ^ 2 = c)).card
        ≤ ({z₀, -z₀} : Finset (ZMod (p ^ e))).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le z₀ ({-z₀} : Finset (ZMod (p ^ e)))) ?_
          simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-! ### Square roots of units modulo `2^e` -/

/-- If `2 ^ e ∣ k ^ 2 - 1` with `e ≥ 3`, then `k ≡ ±1 (mod 2 ^ (e-1))`. -/
lemma two_pow_dvd_sq_sub_one_imp {e k : ℕ} (he : 3 ≤ e) (h : 2 ^ e ∣ k ^ 2 - 1) :
    2 ^ (e - 1) ∣ k - 1 ∨ 2 ^ (e - 1) ∣ k + 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact Or.inl (by simp)
  have he0 : 0 < e := by omega
  have hk2ge : 1 ≤ k ^ 2 := by nlinarith
  have h2dvd : 2 ∣ k ^ 2 - 1 := dvd_trans (pow_dvd_pow_of_pos he0) h
  have hkodd : ¬ 2 ∣ k := by
    intro h2
    have h4 : 2 ∣ k ^ 2 := by
      obtain ⟨m, hm⟩ := h2
      exact ⟨2 * m ^ 2, by rw [hm]; ring⟩
    have h5 : 2 ∣ k ^ 2 - (k ^ 2 - 1) := Nat.dvd_sub h4 h2dvd
    have h6 : k ^ 2 - (k ^ 2 - 1) = 1 := by omega
    rw [h6] at h5
    obtain ⟨c, hc⟩ := h5
    omega
  have hkodd' : Odd k := by
    rw [← Nat.not_even_iff_odd]
    rwa [even_iff_two_dvd]
  obtain ⟨a, ha⟩ := hkodd'
  have hfac : k ^ 2 - 1 = 4 * (a * (a + 1)) := by
    have h1 : k ^ 2 = 4 * (a * (a + 1)) + 1 := by rw [ha]; ring
    omega
  rw [hfac] at h
  have hee : 2 ^ e = 4 * 2 ^ (e - 2) := by
    conv_lhs => rw [show e = (e - 2) + 2 by omega]
    rw [pow_add]
    ring
  rw [hee] at h
  have hd : 2 ^ (e - 2) ∣ a * (a + 1) := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h
  have hcase : 2 ^ (e - 2) ∣ a ∨ 2 ^ (e - 2) ∣ a + 1 := by
    rcases Nat.mod_two_eq_zero_or_one a with h2a | h2a
    · left
      have hodd_a1 : Odd (a + 1) := by rw [Nat.odd_iff]; omega
      have hcop' : (2 ^ (e - 2)).Coprime (a + 1) :=
        Nat.Coprime.pow_left (e - 2) (Nat.coprime_two_left.mpr hodd_a1)
      exact hcop'.dvd_of_dvd_mul_right hd
    · right
      have hodd_a : Odd a := by rw [Nat.odd_iff]; omega
      have hcop' : (2 ^ (e - 2)).Coprime a :=
        Nat.Coprime.pow_left (e - 2) (Nat.coprime_two_left.mpr hodd_a)
      exact hcop'.dvd_of_dvd_mul_left hd
  have h2e : 2 ^ (e - 1) = 2 ^ (e - 2) * 2 := by
    rw [show e - 1 = (e - 2) + 1 by omega, pow_succ, mul_comm]
  rcases hcase with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    refine ⟨t, ?_⟩
    have hk1 : k - 1 = 2 * a := by omega
    calc k - 1 = 2 * a := hk1
      _ = 2 * (2 ^ (e - 2) * t) := by rw [ht]
      _ = 2 ^ (e - 1) * t := by rw [h2e, mul_comm (2 ^ (e - 2)) 2, ← mul_assoc]
  · right
    refine ⟨t, ?_⟩
    have hk1 : k + 1 = 2 * (a + 1) := by omega
    calc k + 1 = 2 * (a + 1) := hk1
      _ = 2 * (2 ^ (e - 2) * t) := by rw [ht]
      _ = 2 ^ (e - 1) * t := by rw [h2e, mul_comm (2 ^ (e - 2)) 2, ← mul_assoc]


/-- The solutions of `u ^ 2 = 1` in `ZMod (2^e)` number at most `4`. -/
theorem card_sq_eq_one_two_pow_le_four (e : ℕ) (he : 1 ≤ e) :
    ((Finset.univ : Finset (ZMod (2 ^ e))).filter (fun u => u ^ 2 = 1)).card ≤ 4 := by
  rcases lt_or_ge e 3 with h2 | h2
  · have h1 := Finset.card_le_card
      (Finset.filter_subset (fun u : ZMod (2 ^ e) => u ^ 2 = 1) Finset.univ)
    rw [Finset.card_univ, ZMod.card] at h1
    have h3 : 2 ^ e ≤ 4 := by
      interval_cases e <;> norm_num
    omega
  · have he3 : 3 ≤ e := h2
    have hd : 2 ^ (e - 1) ∣ 2 ^ e := pow_dvd_pow 2 (by omega)
    have hsub : (Finset.univ.filter (fun u : ZMod (2 ^ e) => u ^ 2 = 1))
        ⊆ ((Finset.univ.filter (fun u : ZMod (2 ^ e) =>
              ZMod.castHom hd (ZMod (2 ^ (e - 1))) u = 1))
           ∪ (Finset.univ.filter (fun u : ZMod (2 ^ e) =>
              ZMod.castHom hd (ZMod (2 ^ (e - 1))) u = -1))) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      set k := u.val with hk
      have hcast : ((k : ℕ) : ZMod (2 ^ e)) = u := ZMod.natCast_zmod_val u
      have hcastHom : (ZMod.castHom hd (ZMod (2 ^ (e - 1)))) u
          = ((k : ℕ) : ZMod (2 ^ (e - 1))) := by
        rw [← hcast, ZMod.castHom_apply, ZMod.cast_natCast hd]
      have hkpos : 1 ≤ k := by
        by_contra hcon
        have hk0 : k = 0 := by omega
        have hu0 : u = 0 := by rw [← hcast, hk0]; simp
        rw [hu0] at hu
        have h01 : (1 : ZMod (2 ^ e)) = 0 := by simpa using hu.symm
        have h02 : ((1 : ℕ) : ZMod (2 ^ e)) = 0 := by simpa using h01
        rw [CharP.cast_eq_zero_iff (ZMod (2 ^ e)) (2 ^ e)] at h02
        have h03 : 1 < 2 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
        have h04 : 2 ^ e ≤ 1 := Nat.le_of_dvd (by norm_num) h02
        omega
      have hk1 : 1 ≤ k ^ 2 := by nlinarith
      have hdiv : 2 ^ e ∣ k ^ 2 - 1 := by
        rw [← CharP.cast_eq_zero_iff (ZMod (2 ^ e)) (2 ^ e)]
        rw [Nat.cast_sub hk1, Nat.cast_pow, hcast, hu]
        norm_num
      rcases two_pow_dvd_sq_sub_one_imp he3 hdiv with ⟨t, ht⟩ | ⟨t, ht⟩
      · left
        rw [hcastHom]
        have hkk : k = 2 ^ (e - 1) * t + 1 := by omega
        rw [hkk]
        have hzero : ((2 ^ (e - 1) : ℕ) : ZMod (2 ^ (e - 1))) = 0 := ZMod.natCast_self _
        rw [Nat.cast_add, Nat.cast_mul, hzero, zero_mul, zero_add, Nat.cast_one]
      · right
        rw [hcastHom]
        have hkk : k + 1 = 2 ^ (e - 1) * t := ht
        have : ((k + 1 : ℕ) : ZMod (2 ^ (e - 1))) = 0 := by
          rw [hkk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
        push_cast at this
        linear_combination this
    have h1 : (Finset.univ.filter (fun u : ZMod (2 ^ e) =>
          ZMod.castHom hd (ZMod (2 ^ (e - 1))) u = 1)).card = 2 := by
      rw [fiber_card_zmod_castHom hd 1, Nat.pow_div (by omega) (by norm_num),
        show e - (e - 1) = 1 by omega, pow_one]
    have h1' : (Finset.univ.filter (fun u : ZMod (2 ^ e) =>
          ZMod.castHom hd (ZMod (2 ^ (e - 1))) u = -1)).card = 2 := by
      rw [fiber_card_zmod_castHom hd (-1), Nat.pow_div (by omega) (by norm_num),
        show e - (e - 1) = 1 by omega, pow_one]
    calc (Finset.univ.filter (fun u : ZMod (2 ^ e) => u ^ 2 = 1)).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ = 4 := by rw [h1, h1']

/-- A unit of `ZMod (2^e)` has at most four square roots. -/
theorem sq_root_card_le_four {e : ℕ} (he : 1 ≤ e) (c : ZMod (2 ^ e)) (hc : IsUnit c) :
    ((Finset.univ : Finset (ZMod (2 ^ e))).filter (fun z => z ^ 2 = c)).card ≤ 4 := by
  by_cases hne : (Finset.univ.filter (fun z : ZMod (2 ^ e) => z ^ 2 = c)).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz₀
    have hz₀unit : IsUnit z₀ :=
      ⟨⟨z₀, z₀ * c⁻¹, by rw [← mul_assoc, ← sq, hz₀, ZMod.mul_inv_of_unit c hc],
          by rw [mul_comm (z₀ * c⁻¹) z₀, ← mul_assoc, ← sq, hz₀,
            ZMod.mul_inv_of_unit c hc]⟩, rfl⟩
    have hinv : (z₀⁻¹) ^ 2 = (z₀ ^ 2)⁻¹ := by
      have hgoal : (z₀ ^ 2) * (z₀⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, ZMod.mul_inv_of_unit z₀ hz₀unit, one_pow]
      exact (ZMod.inv_eq_of_mul_eq_one _ _ _ hgoal).symm
    refine le_trans (Finset.card_le_card_of_injOn (fun z : ZMod (2 ^ e) => z * z₀⁻¹) ?_ ?_)
      (card_sq_eq_one_two_pow_le_four e he)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [mul_pow, hinv, hz, hz₀, ZMod.mul_inv_of_unit c hc]
    · intro a ha b hb hab
      simp only at hab
      have h := congrArg (fun t => t * z₀) hab
      rwa [mul_assoc, ZMod.inv_mul_of_unit z₀ hz₀unit, mul_one,
           mul_assoc, ZMod.inv_mul_of_unit z₀ hz₀unit, mul_one] at h
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; norm_num

/-! ### Generic counting lemmas -/

/-- If `f` has all fibres of size `k` over the set `{Q}`, and `{P}` is exactly the preimage of
`{Q}` under `f`, then `#{P} = k · #{Q}`. -/
lemma card_preimage_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q] (k : ℕ)
    (h1 : ∀ z, P z → Q (f z))
    (h2 : ∀ z, Q (f z) → P z)
    (h3 : ∀ t, Q t → (Finset.univ.filter (fun z => f z = t)).card = k) :
    (Finset.univ.filter P).card = k * (Finset.univ.filter Q).card := by
  have hmap : Set.MapsTo f ↑(Finset.univ.filter P) ↑(Finset.univ.filter Q) := by
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h1 z hz
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfiber : ∀ t ∈ (Finset.univ.filter Q),
      (Finset.univ.filter P).filter (fun z => f z = t) = Finset.univ.filter (fun z => f z = t) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h2 z (h ▸ ht), h⟩⟩
  have hsum : ∀ t ∈ (Finset.univ.filter Q),
      ((Finset.univ.filter P).filter (fun z => f z = t)).card = k := by
    intro t ht
    rw [hfiber t ht]
    exact h3 t (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ht)
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The fibres of a map on a product, acting separately on the two factors. -/
lemma card_fiber_prod {α β γ δ : Type*} [Fintype α] [Fintype β] [DecidableEq γ] [DecidableEq δ]
    (g : α → γ) (h : β → δ) (t : γ × δ) :
    (Finset.univ.filter (fun z : α × β => (g z.1, h z.2) = t)).card
      = (Finset.univ.filter (fun x => g x = t.1)).card
        * (Finset.univ.filter (fun y => h y = t.2)).card := by
  have hset : (Finset.univ.filter (fun z : α × β => (g z.1, h z.2) = t))
      = (Finset.univ.filter (fun x => g x = t.1)) ×ˢ (Finset.univ.filter (fun y => h y = t.2)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Prod.ext_iff]
  rw [hset, Finset.card_product]


/-- The reduction `ZMod n → R` of a natural number is that natural number. -/
lemma castHom_natCast {m n : ℕ} (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] (k : ℕ) :
    ZMod.castHom h R (k : ZMod n) = (k : R) := by
  rw [ZMod.castHom_apply, ZMod.cast_natCast h]

/-! ### Divisibility in `ZMod (p^e)` -/

/-- In `ZMod (p^e)`, `p^k · C = 0` iff `C` vanishes modulo `p^(e-k)`. -/
lemma zmod_pow_mul_eq_zero_iff {p e k : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - k))]
    (hp : p.Prime) (hk : k < e) (h : p ^ (e - k) ∣ p ^ e) (C : ZMod (p ^ e)) :
    (p : ZMod (p ^ e)) ^ k * C = 0 ↔ ZMod.castHom h (ZMod (p ^ (e - k))) C = 0 := by
  have hlt : p ^ k < p ^ e := Nat.pow_lt_pow_right hp.one_lt hk
  have hval : (ZMod.castHom h (ZMod (p ^ (e - k))) C).val = C.val % p ^ (e - k) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have hpe : p ^ k * p ^ (e - k) = p ^ e := by
    rw [← pow_add, Nat.add_sub_cancel' hk.le]
  have key : (p ^ e ∣ p ^ k * C.val) ↔ (p ^ (e - k) ∣ C.val) := by
    constructor
    · intro hh
      have h2 : p ^ k * p ^ (e - k) ∣ p ^ k * C.val := by rwa [hpe]
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos k)).mp h2
    · intro hh
      have h2 : p ^ k * p ^ (e - k) ∣ p ^ k * C.val :=
        (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos k)).mpr hh
      rwa [hpe] at h2
  rw [← Nat.cast_pow (α := ZMod (p ^ e)), ← ZMod.val_eq_zero, ZMod.val_mul, ZMod.val_natCast,
    Nat.mod_eq_of_lt hlt, ← ZMod.val_eq_zero, hval]
  rw [Nat.dvd_iff_mod_eq_zero.symm, Nat.dvd_iff_mod_eq_zero.symm, key]

/-- The equality form of the previous divisibility statement. -/
lemma castHom_eq_iff_pow_mul_eq {p e k : ℕ} [NeZero (p ^ e)] [NeZero (p ^ (e - k))]
    (hp : p.Prime) (hk : k < e) (h : p ^ (e - k) ∣ p ^ e) (C D : ZMod (p ^ e)) :
    ZMod.castHom h (ZMod (p ^ (e - k))) C = ZMod.castHom h (ZMod (p ^ (e - k))) D ↔
      (p : ZMod (p ^ e)) ^ k * C = (p : ZMod (p ^ e)) ^ k * D := by
  have hh := zmod_pow_mul_eq_zero_iff (p := p) (e := e) (k := k) hp hk h (C - D)
  rw [mul_sub, map_sub, sub_eq_zero, sub_eq_zero] at hh
  exact hh.symm

/-! ### Lifting `ZMod (p^(e-1))` onto the multiples of `p` in `ZMod (p^e)` -/

/-- The class of `p * u.val` in `ZMod (p^e)`.  For `e ≥ 1` this gives a bijection between
`ZMod (p^(e-1))` and the multiples of `p` in `ZMod (p^e)`. -/
def plift (p e : ℕ) (u : ZMod (p ^ (e - 1))) : ZMod (p ^ e) :=
  ((p * u.val : ℕ) : ZMod (p ^ e))

lemma plift_eq_mul (p e : ℕ) (u : ZMod (p ^ (e - 1))) :
    plift p e u = (p : ZMod (p ^ e)) * ((u.val : ℕ) : ZMod (p ^ e)) := by
  rw [plift, Nat.cast_mul]

lemma plift_val {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) [NeZero (p ^ (e - 1))]
    (u : ZMod (p ^ (e - 1))) :
    (plift p e u).val = p * u.val := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [plift, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h1 : u.val < p ^ (e - 1) := ZMod.val_lt u
  calc p * u.val < p * p ^ (e - 1) := Nat.mul_lt_mul_of_pos_left h1 hp.pos
    _ = p ^ e := by
        conv_rhs => rw [show e = (e - 1) + 1 by omega]
        rw [pow_succ']

lemma plift_div {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) [NeZero (p ^ (e - 1))]
    (x : ZMod (p ^ e)) (hx : p ∣ x.val) :
    plift p e (((x.val / p : ℕ)) : ZMod (p ^ (e - 1))) = x := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hlt : x.val / p < p ^ (e - 1) := by
    have h1 : x.val < p ^ e := ZMod.val_lt x
    have h2 : x.val = p * (x.val / p) := (Nat.mul_div_cancel' hx).symm
    conv_rhs at h1 => rw [show e = (e - 1) + 1 by omega]
    rw [h2, pow_succ'] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  rw [plift, ZMod.val_cast_of_lt hlt, Nat.mul_div_cancel' hx, ZMod.natCast_zmod_val x]

lemma div_plift {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) [NeZero (p ^ (e - 1))]
    (u : ZMod (p ^ (e - 1))) :
    (((plift p e u).val / p : ℕ) : ZMod (p ^ (e - 1))) = u := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [plift_val hp he, Nat.mul_div_cancel_left _ hp.pos, ZMod.natCast_zmod_val u]

lemma plift_injective {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) [NeZero (p ^ (e - 1))]
    [NeZero (p ^ e)] : Function.Injective (plift p e) := by
  rcases eq_or_lt_of_le he with rfl | hlt
  · intro u v _
    have hu : u.val = 0 := Nat.lt_one_iff.mp (ZMod.val_lt u)
    have hv : v.val = 0 := Nat.lt_one_iff.mp (ZMod.val_lt v)
    rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v, hu, hv]
  · have hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (by omega)
    intro u v huv
    rw [plift_eq_mul, plift_eq_mul] at huv
    have h := (castHom_eq_iff_pow_mul_eq (p := p) (e := e) (k := 1) hp hlt hd
      (C := ((u.val : ℕ) : ZMod (p ^ e))) (D := ((v.val : ℕ) : ZMod (p ^ e)))).mpr
      (by simpa using huv)
    have hu : ZMod.castHom hd (ZMod (p ^ (e - 1))) ((u.val : ℕ) : ZMod (p ^ e)) = u := by
      rw [ZMod.castHom_apply, ZMod.cast_natCast hd, ZMod.natCast_zmod_val u]
    have hv : ZMod.castHom hd (ZMod (p ^ (e - 1))) ((v.val : ℕ) : ZMod (p ^ e)) = v := by
      rw [ZMod.castHom_apply, ZMod.cast_natCast hd, ZMod.natCast_zmod_val v]
    rw [hu, hv] at h
    exact h


end

end Work.FIArea2
