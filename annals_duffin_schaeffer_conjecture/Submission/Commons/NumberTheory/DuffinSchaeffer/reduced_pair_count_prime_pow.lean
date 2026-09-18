import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.Nat.coprime_prime_pow_right_iff_not_dvd

open scoped BigOperators Nat

namespace Commons.NumberTheory.DuffinSchaeffer

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private lemma card_mod_class (p k c : ℕ) (hp0 : 0 < p) (hc : c < p) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun n => n % p = c)).card = p ^ (k - 1) := by
  classical
  have hk2 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have hmain : (Finset.range (p ^ k)).filter (fun n => n % p = c) =
      (Finset.range (p ^ (k - 1))).image (fun j => c + p * j) := by
    ext n
    constructor
    · intro hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnrange, hnmod⟩
      rw [Finset.mem_image]
      refine ⟨n / p, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hnlt : n < p ^ k := (Finset.mem_range.mp hnrange)
        rw [hk2, pow_succ, mul_comm] at hnlt
        exact Nat.div_lt_of_lt_mul hnlt
      · have hmain3 : p * (n / p) + c = n := by
          rw [← hnmod]
          exact Nat.div_add_mod n p
        rw [add_comm]
        exact hmain3
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        calc
          c + p * j < p + p * j := Nat.add_lt_add_right hc (p * j)
          _ = p * (j + 1) := by ring
          _ ≤ p * p ^ (k - 1) := Nat.mul_le_mul_left p (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
          _ = p ^ k := by
            rw [mul_comm, ← pow_succ]
            rw [← hk2]
      · have hpm : (p * j) % p = 0 := by
          rw [Nat.mul_mod]
          simp
        rw [Nat.add_mod, hpm, add_zero]
        rw [Nat.mod_eq_of_lt (Nat.mod_lt c hp0)]
        exact Nat.mod_eq_of_lt hc
  rw [hmain]
  have hinj : Function.Injective (fun j : ℕ => c + p * j) := by
    intro x y h
    have : p * x = p * y := Nat.add_left_cancel h
    exact Nat.mul_left_cancel hp0 this
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
private lemma mod_add_eq_zero_iff (p x r : ℕ) (hp : 0 < p) (hr0 : 0 < r) (hr : r < p) (hx : x < p) :
    (x + r) % p = 0 ↔ x = p - r := by
  constructor
  · intro h
    by_cases hlt : x + r < p
    · have : x + r = 0 := by
        rw [Nat.mod_eq_of_lt hlt] at h
        exact h
      omega
    · have hge : p ≤ x + r := le_of_not_gt hlt
      have hmod : (x + r) % p = (x + r - p) % p := Nat.mod_eq_sub_mod hge
      rw [hmod] at h
      have hlt2 : x + r - p < p := by omega
      have : x + r - p = 0 := by
        rw [Nat.mod_eq_of_lt hlt2] at h
        exact h
      omega
  · intro hxeq
    rw [hxeq]
    have : p - r + r = p := Nat.sub_add_cancel (le_of_lt hr)
    rw [this]
    simp
private lemma mod_add_e_eq_zero_iff (p e n : ℕ) (hp : 0 < p) (hne : ¬ p ∣ e) :
    (n + e) % p = 0 ↔ n % p = p - e % p := by
  have hr0 : 0 < e % p := by
    by_contra h
    have : e % p = 0 := Nat.eq_zero_of_not_pos h
    exact hne (Nat.dvd_iff_mod_eq_zero.mpr this)
  have hr : e % p < p := Nat.mod_lt e hp
  have hx : n % p < p := Nat.mod_lt n hp
  rw [Nat.add_mod]
  exact mod_add_eq_zero_iff p (n % p) (e % p) hp hr0 hr hx
private lemma card_bad_set (p k e : ℕ) (hp : p.Prime) (hk : 0 < k) (hne : ¬ p ∣ e) :
    ((Finset.range (p ^ k)).filter (fun n => p ∣ n + e)).card = p ^ (k - 1) := by
  classical
  have hc : (p - e % p) < p := by
    have hr : e % p < p := Nat.mod_lt e hp.pos
    by_cases he0 : e % p = 0
    · exfalso
      exact hne (Nat.dvd_iff_mod_eq_zero.mpr he0)
    · have hr0 : 0 < e % p := Nat.pos_of_ne_zero he0
      omega
  have hmain : (Finset.range (p ^ k)).filter (fun n => p ∣ n + e) =
      (Finset.range (p ^ k)).filter (fun n => n % p = p - e % p) := by
    apply Finset.filter_congr
    intro n hn
    rw [Nat.dvd_iff_mod_eq_zero]
    exact mod_add_e_eq_zero_iff p e n hp.pos hne
  rw [hmain]
  exact card_mod_class p k (p - e % p) hp.pos hc hk
private lemma card_coprime_filter (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n)).card = (p ^ k).totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [Nat.coprime_comm]
  exact (Commons.NumberTheory.Nat.coprime_prime_pow_right_iff_not_dvd p k n hp hk).symm
private lemma card_nondvd_nondvd_add (p k e : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card =
      if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) := by
  classical
  by_cases he : p ∣ e
  · rw [if_pos he]
    have hiff : ∀ n : ℕ, p ∣ n + e ↔ p ∣ n := by
      intro n
      rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd he, add_zero, Nat.mod_mod]
    have hT : (Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e)) =
        (Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n) := by
      ext n
      constructor
      · intro h
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1⟩
      · intro h
        have h1 := (Finset.mem_filter.mp h).1
        have hn := (Finset.mem_filter.mp h).2
        exact Finset.mem_filter.mpr ⟨h1, ⟨hn, by
          intro hpne
          exact hn ((hiff n).mp hpne)⟩⟩
    rw [hT]
    exact card_coprime_filter p k hp hk
  · rw [if_neg he]
    let A := (Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n)
    let B := (Finset.range (p ^ k)).filter (fun n => p ∣ n + e)
    have hA : A.card = (p ^ k).totient := by
      dsimp [A]
      exact card_coprime_filter p k hp hk
    have hB : B.card = p ^ (k - 1) := by
      dsimp [B]
      exact card_bad_set p k e hp hk he
    have hB' : A.filter (fun n => p ∣ n + e) = B := by
      unfold A B
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro n hn
      constructor
      · intro h
        exact h.2
      · intro hpe
        constructor
        · intro hpn
          exact he (by
            have hsub : p ∣ n + e - n := Nat.dvd_sub hpe hpn
            have hsub' : n + e - n = e := Nat.add_sub_cancel_left n e
            rwa [← hsub'])
        · exact hpe
    have hT' : A.filter (fun n => ¬ p ∣ n + e) =
        (Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e)) := by
      unfold A
      rw [Finset.filter_filter]
    have hsplit := Finset.card_filter_add_card_filter_not (fun n : ℕ => p ∣ n + e) (s := A)
    -- hsplit : (A.filter q).card + (A.filter (¬q)).card = A.card
    rw [hB'] at hsplit
    rw [hT'] at hsplit
    rw [hA] at hsplit
    omega
-- Transfer: natural pair count over range (p^k) equals count of IsUnit pairs in ZMod (p^k)
private lemma card_pair_range_zmod_pow (p k R Q e : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) :
    ((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
      (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧
         ((mn.1 * R) % (p ^ k) = ((mn.2 * Q + e) % (p ^ k))))).card =
      Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
        z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k))} := by
  classical
  let Pz : ZMod (p ^ k) × ZMod (p ^ k) → Prop := fun z => IsUnit z.1 ∧ IsUnit z.2 ∧
      z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k))
  let A := (Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
      (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧ ((mn.1 * R) % (p ^ k) = ((mn.2 * Q + e) % (p ^ k))))
  let ZZ := (Finset.univ : Finset (ZMod (p ^ k) × ZMod (p ^ k))).filter Pz
  have hcast (m : ℕ) : ¬ p ∣ m ↔ IsUnit (m : ZMod (p ^ k)) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := m)).symm
  have heq (m n : ℕ) : (m : ZMod (p ^ k)) * (R : ZMod (p ^ k)) = (n : ZMod (p ^ k)) * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k)) ↔
      (m * R) % (p ^ k) = (n * Q + e) % (p ^ k) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]
    exact ZMod.natCast_eq_natCast_iff' (m * R) (n * Q + e) (p ^ k)
  calc
    A.card = ZZ.card := by
      refine Finset.card_bij' (fun mn _ => ((mn.1 : ZMod (p ^ k)), (mn.2 : ZMod (p ^ k))))
        (fun z _ => (z.1.val, z.2.val)) ?hi ?hj ?left ?right
      · intro mn hmn
        have hmem := (Finset.mem_filter.mp hmn).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact ⟨(hcast mn.1).mp hmem.1, ⟨(hcast mn.2).mp hmem.2.1, (heq mn.1 mn.2).mpr hmem.2.2⟩⟩
      · intro z hz
        have hmem := (Finset.mem_filter.mp hz).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_range.mpr (ZMod.val_lt z.1)
        · exact Finset.mem_range.mpr (ZMod.val_lt z.2)
        refine ⟨?_, ⟨?_, ?_⟩⟩
        · intro hd
          have hz0 : IsUnit (z.1.val : ZMod (p ^ k)) := by
            simpa [ZMod.natCast_zmod_val z.1] using hmem.1
          exact (hcast z.1.val).mpr hz0 hd
        · intro hd
          have hz0 : IsUnit (z.2.val : ZMod (p ^ k)) := by
            simpa [ZMod.natCast_zmod_val z.2] using hmem.2.1
          exact (hcast z.2.val).mpr hz0 hd
        · apply (heq z.1.val z.2.val).mp
          rw [ZMod.natCast_zmod_val z.1, ZMod.natCast_zmod_val z.2]
          exact hmem.2.2
      · intro mn hmn
        have hm1 : mn.1 < p ^ k := (Finset.mem_range.mp ((Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).1))
        have hm2 : mn.2 < p ^ k := (Finset.mem_range.mp ((Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).2))
        ext <;> simp [ZMod.val_natCast, Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2]
      · intro z hz
        ext <;> simp [ZMod.natCast_zmod_val]
    _ = Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // Pz z} := by
      calc
        ZZ.card = Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // z ∈ ZZ} := (Fintype.card_coe ZZ).symm
        _ = Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // Pz z} := by
          apply Fintype.card_congr
          refine Equiv.subtypeEquivRight ?_
          intro z
          simp [ZZ, Pz]
private lemma isUnit_iff_val (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) (z : ZMod (p ^ k)) :
    IsUnit z ↔ ¬ p ∣ z.val := by
  constructor
  · intro hu
    rw [← ZMod.natCast_zmod_val z] at hu
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := z.val)).mp hu
  · intro hnd
    simpa [ZMod.natCast_zmod_val z] using (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := z.val)).mpr hnd
private lemma isUnit_inv_zmod {p k : ℕ} [NeZero (p ^ k)] (ρ : ZMod (p ^ k)) (hρ : IsUnit ρ) :
    IsUnit ρ⁻¹ := by
  refine ⟨⟨ρ⁻¹, ρ, ?_, ?_⟩, rfl⟩
  · exact ZMod.inv_mul_of_unit ρ hρ
  · exact ZMod.mul_inv_of_unit ρ hρ
/-- right multiplication by a unit is a ring-element equivalence -/
private def ringMulEquiv {p k : ℕ} [NeZero (p ^ k)] (ρ : ZMod (p ^ k)) (hρ : IsUnit ρ) :
    ZMod (p ^ k) ≃ ZMod (p ^ k) where
  toFun x := x * ρ
  invFun x := x * ρ⁻¹
  left_inv x := by
    calc
      (x * ρ) * ρ⁻¹ = x * (ρ * ρ⁻¹) := by rw [mul_assoc]
      _ = x * 1 := by rw [ZMod.mul_inv_of_unit ρ hρ]
      _ = x := by rw [mul_one]
  right_inv x := by
    calc
      (x * ρ⁻¹) * ρ = x * (ρ⁻¹ * ρ) := by rw [mul_assoc]
      _ = x * 1 := by rw [ZMod.inv_mul_of_unit ρ hρ]
      _ = x := by rw [mul_one]
private lemma isUnit_of_mul_unit {p k : ℕ} [NeZero (p ^ k)] {ρ x : ZMod (p ^ k)} (hρ : IsUnit ρ) :
    IsUnit (x * ρ) → IsUnit x := by
  intro h
  have hx : (x * ρ) * ρ⁻¹ = x := by
    calc
      (x * ρ) * ρ⁻¹ = x * (ρ * ρ⁻¹) := by rw [mul_assoc]
      _ = x * 1 := by rw [ZMod.mul_inv_of_unit ρ hρ]
      _ = x := by rw [mul_one]
  rw [← hx]
  exact h.mul (isUnit_inv_zmod ρ hρ)
-- (S1 = S2)
private lemma card_pair_mul_units (p k R Q e : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (hR : ¬ p ∣ R) (hQ : ¬ p ∣ Q) :
    Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
        z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k))} =
    Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
        z.1 = z.2 + (e : ZMod (p ^ k))} := by
  classical
  have hRu : IsUnit (R : ZMod (p ^ k)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := R)).mpr hR
  have hQu : IsUnit (Q : ZMod (p ^ k)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := Q)).mpr hQ
  let e0 : ZMod (p ^ k) × ZMod (p ^ k) ≃ ZMod (p ^ k) × ZMod (p ^ k) :=
    Equiv.prodCongr (ringMulEquiv (R : ZMod (p ^ k)) hRu) (ringMulEquiv (Q : ZMod (p ^ k)) hQu)
  have hprop : ∀ z : ZMod (p ^ k) × ZMod (p ^ k),
      (IsUnit z.1 ∧ IsUnit z.2 ∧ z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k)))
        ↔ (IsUnit (e0 z).1 ∧ IsUnit (e0 z).2 ∧ (e0 z).1 = (e0 z).2 + (e : ZMod (p ^ k))) := by
    intro z
    change (IsUnit z.1 ∧ IsUnit z.2 ∧ z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k)))
        ↔ (IsUnit (z.1 * (R : ZMod (p ^ k))) ∧ IsUnit (z.2 * (Q : ZMod (p ^ k))) ∧
            z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k)))
    constructor
    · intro h
      exact ⟨h.1.mul hRu, ⟨h.2.1.mul hQu, h.2.2⟩⟩
    · intro h
      exact ⟨isUnit_of_mul_unit hRu h.1, ⟨isUnit_of_mul_unit hQu h.2.1, h.2.2⟩⟩
  exact Fintype.card_congr (Equiv.subtypeEquiv e0 hprop)
-- (S2 = S3)
private def pairToX {p k : ℕ} [NeZero (p ^ k)] (e : ℕ) :
    {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
      z.1 = z.2 + (e : ZMod (p ^ k))} ≃
    {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))} where
  toFun z := ⟨z.1.2, z.2.2.1, by
      rw [← z.2.2.2]
      exact z.2.1⟩
  invFun x := ⟨(x.1 + (e : ZMod (p ^ k)), x.1), x.2.2, x.2.1, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.2.2.2.symm
    · rfl
  right_inv x := by
    apply Subtype.ext
    rfl
private lemma card_pairs_eq_add_zmod (p k e : ℕ) [NeZero (p ^ k)] :
    Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
        z.1 = z.2 + (e : ZMod (p ^ k))} =
    Fintype.card {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))} := by
  classical
  exact Fintype.card_congr (pairToX (p := p) (k := k) e)
private lemma card_zmod_units_eq_nat (p k e : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) :
    Fintype.card {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))} =
    ((Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card := by
  classical
  let Px : ZMod (p ^ k) → Prop := fun x => IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))
  let UZ := (Finset.univ : Finset (ZMod (p ^ k))).filter Px
  let TN := (Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e))
  have h1 : UZ.card = Fintype.card {x : ZMod (p ^ k) // Px x} := by
    calc
      UZ.card = Fintype.card {x : ZMod (p ^ k) // x ∈ UZ} := (Fintype.card_coe UZ).symm
      _ = Fintype.card {x : ZMod (p ^ k) // Px x} := by
        apply Fintype.card_congr
        refine Equiv.subtypeEquivRight ?_
        intro x
        simp [UZ, Px]
  calc
    Fintype.card {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))}
        = UZ.card := by
          rw [h1]
    _ = TN.card := by
      refine Finset.card_bij' (fun x _ => x.val) (fun n _ => (n : ZMod (p ^ k))) ?hi ?hj ?left ?right
      · intro x hx
        have hm := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
        constructor
        · exact (isUnit_iff_val p k hp hk x).mp hm.1
        · have hx2 : IsUnit ((x.val + e : ℕ) : ZMod (p ^ k)) := by
            simpa [ZMod.natCast_zmod_val x, Nat.cast_add] using hm.2
          exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := x.val + e)).mp hx2
      · intro n hn
        have hm := (Finset.mem_filter.mp hn).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        constructor
        · exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := n)).mpr hm.1
        · have hn2 : IsUnit ((n + e : ℕ) : ZMod (p ^ k)) :=
            (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk (a := n + e)).mpr hm.2
          simpa [Nat.cast_add] using hn2
      · intro x hx
        simp [ZMod.natCast_zmod_val]
      · intro n hn
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)]

-- Main theorem
theorem reduced_pair_count_prime_pow (p k R Q e : ℕ) (hp : p.Prime) (hk : 0 < k) (hR : ¬ p ∣ R) (hQ : ¬ p ∣ Q) :
    ((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
      (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧
         ((mn.1 * R) % (p ^ k) = ((mn.2 * Q + e) % (p ^ k))))).card =
      if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) := by
  classical
  haveI : NeZero (p ^ k) := ⟨(pow_pos hp.pos k).ne'⟩
  calc
    ((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
      (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧
         ((mn.1 * R) % (p ^ k) = ((mn.2 * Q + e) % (p ^ k))))).card
        = Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
            z.1 * (R : ZMod (p ^ k)) = z.2 * (Q : ZMod (p ^ k)) + (e : ZMod (p ^ k))} :=
            card_pair_range_zmod_pow p k R Q e hp hk
    _ = Fintype.card {z : ZMod (p ^ k) × ZMod (p ^ k) // IsUnit z.1 ∧ IsUnit z.2 ∧
            z.1 = z.2 + (e : ZMod (p ^ k))} := card_pair_mul_units p k R Q e hp hk hR hQ
    _ = Fintype.card {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))} :=
            card_pairs_eq_add_zmod p k e
    _ = ((Finset.range (p ^ k)).filter (fun n => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card :=
            card_zmod_units_eq_nat p k e hp hk
    _ = if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) :=
            card_nondvd_nondvd_add p k e hp hk

end Commons.NumberTheory.DuffinSchaeffer