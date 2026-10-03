import Mathlib
import Submission.Work.FIArea2.NsolDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea2

attribute [local instance] Classical.propDecidable

/-- Hensel lifting of a square root modulo an odd prime power. -/
theorem henselSqDvdAux (p : ℕ) (hp : p.Prime) (hodd : Odd p) (k : ℕ) (hk : 0 < k) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hx : ∃ x : ℤ, (p : ℤ) ∣ x ^ 2 - a) :
    ∃ z : ℤ, (p : ℤ) ^ k ∣ z ^ 2 - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have H : ∀ j : ℕ, 1 ≤ j → ∃ z : ℤ, (p : ℤ) ^ j ∣ z ^ 2 - a := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        simpa using hx
      · obtain ⟨z, hz⟩ := ih hjpos
        have hjne : j ≠ 0 := by omega
        have hpz : ¬ (p : ℤ) ∣ z := by
          intro hd
          apply ha
          have hpj : (p : ℤ) ∣ (p : ℤ) ^ j := dvd_pow_self (p : ℤ) hjne
          have h1 : (p : ℤ) ∣ z ^ 2 - a := dvd_trans hpj hz
          have h2 : (p : ℤ) ∣ z ^ 2 := by
            have := dvd_mul_of_dvd_left hd z
            rwa [← pow_two] at this
          have h3 := dvd_sub h2 h1
          rwa [sub_sub_cancel] at h3
        have hqz : ((z : ℤ) : ZMod p) ≠ 0 := by
          show ¬ (((z : ℤ) : ZMod p) = 0)
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hpz
        have hq2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
          show ¬ (((2 : ℤ) : ZMod p) = 0)
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro hd
          have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
          have hle' : p ≤ 2 := by exact_mod_cast hle
          omega
        have h2z : ¬ (p : ℤ) ∣ 2 * z := by
          intro hd
          have hd' : ((2 * z : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * z) p).mpr hd
          rw [Int.cast_mul] at hd'
          exact (mul_ne_zero hq2 hqz) hd'
        have hA0 : ((2 * z : ℤ) : ZMod p) ≠ 0 := by
          show ¬ (((2 * z : ℤ) : ZMod p) = 0)
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact h2z
        have hzj : (p : ℤ) ^ j ∣ z ^ 2 - a := hz
        obtain ⟨m, hm⟩ := hzj
        obtain ⟨t, ht⟩ := ZMod.intCast_surjective
          (-(((m : ℤ) : ZMod p) * (((2 * z : ℤ) : ZMod p))⁻¹))
        have hmt : (p : ℤ) ∣ m + 2 * z * t := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd (m + 2 * z * t) p).mp
          have he : ((m + 2 * z * t : ℤ) : ZMod p)
              = ((m : ℤ) : ZMod p) + ((2 * z : ℤ) : ZMod p) * ((t : ℤ) : ZMod p) := by
            push_cast; ring
          rw [he, ht]
          have hAm : ((2 * z : ℤ) : ZMod p) * (((m : ℤ) : ZMod p) * (((2 * z : ℤ) : ZMod p))⁻¹)
              = ((m : ℤ) : ZMod p) := by
            rw [mul_comm (((m : ℤ) : ZMod p)) _, ← mul_assoc, mul_inv_cancel₀ hA0, one_mul]
          rw [mul_neg, hAm, add_neg_cancel]
        set z' : ℤ := z + (p : ℤ) ^ j * t with hz'def
        have hident : z' ^ 2 - a
            = (p : ℤ) ^ j * (m + 2 * z * t) + ((p : ℤ) ^ j) ^ 2 * t ^ 2 := by
          have e1 : z' ^ 2 - a
              = (z ^ 2 - a) + 2 * z * ((p : ℤ) ^ j * t) + ((p : ℤ) ^ j * t) ^ 2 := by
            rw [hz'def]; ring
          have e2 : ((p : ℤ) ^ j * t) ^ 2 = ((p : ℤ) ^ j) ^ 2 * t ^ 2 := by rw [mul_pow]
          rw [e1, hm, e2]; ring
        refine ⟨z', ?_⟩
        rw [hident]
        apply dvd_add
        · obtain ⟨u, hu⟩ := hmt
          refine ⟨u, ?_⟩
          rw [hu, pow_succ']
          ring
        · have h1 : (p : ℤ) ^ (j + 1) ∣ ((p : ℤ) ^ j) ^ 2 := by
            rw [← pow_mul]
            exact pow_dvd_pow (p : ℤ) (by omega)
          exact dvd_mul_of_dvd_left h1 (t ^ 2)
  exact H k hk

/-- The solutions of `s ^ 2 = 1` modulo an odd prime power number two. -/
theorem card_sq_eq_one_zmod_prime_pow (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (hk : 0 < k) :
    Nat.card {s : ZMod (p ^ k) // s ^ 2 = 1} = 2 := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hpne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2lt : 2 < p ^ k := by
    have h1 : p ≤ p ^ k := Nat.le_self_pow hk.ne' p
    omega
  have h1lt : 1 < p ^ k := by omega
  haveI : Fact (2 < p ^ k) := ⟨h2lt⟩
  have hmem : ∀ s : ZMod (p ^ k), s ^ 2 = 1 → s = 1 ∨ s = -1 := by
    intro s hs
    have hn0 : s.val ≠ 0 := by
      intro h0
      have hz : s = 0 := by rw [← ZMod.natCast_zmod_val s, h0]; simp
      rw [hz] at hs
      have h1 : (1 : ZMod (p ^ k)) = 0 := by rw [← hs]; ring
      have hdvd : (p ^ k) ∣ 1 := by
        rw [← CharP.cast_eq_zero_iff (ZMod (p ^ k)) (p ^ k) 1]
        simpa using h1
      exact (Nat.not_dvd_of_pos_of_lt (by norm_num) h1lt) hdvd
    have hlt1 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr hn0
    have hsv : s = ((s.val : ℕ) : ZMod (p ^ k)) := (ZMod.natCast_zmod_val s).symm
    by_cases hp1 : p ∣ s.val - 1
    · have hp2' : ¬ p ∣ s.val + 1 := by
        intro hpp
        have hsub : p ∣ (s.val + 1) - (s.val - 1) := Nat.dvd_sub hpp hp1
        have heq : (s.val + 1) - (s.val - 1) = 2 := by omega
        rw [heq] at hsub
        have hz : (p : ℤ) ∣ 2 := by exact_mod_cast hsub
        have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hz
        have hle' : p ≤ 2 := by exact_mod_cast hle
        omega
      have hunit : IsUnit (((s.val + 1 : ℕ) : ZMod (p ^ k))) :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).mpr hp2'
      have hs1 : s + 1 = ((s.val + 1 : ℕ) : ZMod (p ^ k)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val s]
        rw [Nat.cast_add, Nat.cast_one]
      have hunit' : IsUnit (s + 1) := by rw [hs1]; exact hunit
      have hprod : (s - 1) * (s + 1) = 0 := by linear_combination hs
      exact Or.inl (sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hunit').mp hprod))
    · have hunit : IsUnit (((s.val - 1 : ℕ) : ZMod (p ^ k))) :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).mpr hp1
      have hs1 : s - 1 = ((s.val - 1 : ℕ) : ZMod (p ^ k)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val s]
        rw [Nat.cast_sub hlt1, Nat.cast_one]
      have hunit' : IsUnit (s - 1) := by rw [hs1]; exact hunit
      have hprod : (s - 1) * (s + 1) = 0 := by linear_combination hs
      exact Or.inr (add_eq_zero_iff_eq_neg.mp ((IsUnit.mul_right_eq_zero hunit').mp hprod))
  have hset : (Finset.univ.filter (fun s : ZMod (p ^ k) => s ^ 2 = 1)) = {1, -1} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨fun h => hmem s h, fun h => by rcases h with h | h <;> rw [h] <;> ring⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hset]
  exact Finset.card_pair (fun h => ZMod.neg_one_ne_one h.symm)

/-- **The number of square roots of a unit modulo an odd prime power.**  For an odd prime `p`, `k ≥ 1` and an integer `c` coprime to `p`, the congruence `z² ≡ c (mod p^k)` has `1 + (c/p)` solutions modulo `p^k`, where `(c/p)` is the Legendre/Jacobi symbol (so `2` if `c` is a quadratic residue mod `p` and `0` otherwise).  This is the paper's (8.12) `n(a;p^α) = 1 + (a/p)` (`n(z;b)` = number of solutions of `ω² ≡ z (mod b)`), which is the only arithmetic input of Lemma 8.2/(8.10).  A route: `k = 1` (field `ZMod p`; `z₁² = z₂² ⟹ z₁ = ±z₂`), then Hensel lifting: each root mod `p^j` (`j ≥ 1`) lifts to exactly one root mod `p^{j+1}` (`z ↦ z + p^j t`, solve `2zt ≡ (c - z²)/p^j (mod p)`; note `z` and `2` are units). -/
theorem sqRoots_card (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (hk : 0 < k) (c : ℤ)
    (hc : ¬ (p : ℤ) ∣ c) :
    (Nat.card {z : ZMod (p ^ k) // z ^ 2 = (c : ZMod (p ^ k))} : ℤ) = 1 + jacobiSym c p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hdvd : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hjc : jacobiSym c p = legendreSym p c := (jacobiSym.legendreSym.to_jacobiSym p c).symm
  have hcp0 : ((c : ℤ) : ZMod p) ≠ 0 := by
    show ¬ (((c : ℤ) : ZMod p) = 0)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hc
  have hcu : IsUnit ((c : ℤ) : ZMod (p ^ k)) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    have h1 : IsCoprime (p : ℤ) c := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hd => hc ((Int.natAbs_dvd_natAbs).mp (by simpa using hd)))
    have h2 : IsCoprime ((p : ℤ) ^ k) c := h1.pow_left
    simpa [Nat.cast_pow] using h2
  by_cases hs : IsSquare ((c : ℤ) : ZMod p)
  · have hleg : legendreSym p c = 1 := (legendreSym.eq_one_iff p hcp0).mpr hs
    obtain ⟨x, hx⟩ := (isSquare_iff_exists_sq ((c : ℤ) : ZMod p)).mp hs
    obtain ⟨x0, hx0⟩ := ZMod.intCast_surjective x
    have hxdvd : (p : ℤ) ∣ x0 ^ 2 - c := by
      have h : (((x0 : ℤ) ^ 2 : ℤ) : ZMod p) = ((c : ℤ) : ZMod p) := by
        rw [Int.cast_pow, hx0]; exact hx.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
      have hh := dvd_neg.mpr h
      rwa [neg_sub] at hh
    obtain ⟨z, hz⟩ := henselSqDvdAux p hp hodd k hk c hc ⟨x0, hxdvd⟩
    have hroot : (((z : ℤ) : ZMod (p ^ k))) ^ 2 = (c : ZMod (p ^ k)) := by
      have h : (((z : ℤ) ^ 2 : ℤ) : ZMod (p ^ k)) = ((c : ℤ) : ZMod (p ^ k)) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Nat.cast_pow]
        have hh := dvd_neg.mpr hz
        rwa [neg_sub] at hh
      rwa [Int.cast_pow] at h
    have hcard : Nat.card {w : ZMod (p ^ k) // w ^ 2 = (c : ZMod (p ^ k))} = 2 := by
      have hz0unit : IsUnit (((z : ℤ) : ZMod (p ^ k))) := by
        have h : IsUnit (((z : ℤ) : ZMod (p ^ k)) * ((z : ℤ) : ZMod (p ^ k))) := by
          rw [← pow_two, hroot]; exact hcu
        exact (IsUnit.mul_iff.mp h).1
      have e : {w : ZMod (p ^ k) // w ^ 2 = (c : ZMod (p ^ k))} ≃
          {s : ZMod (p ^ k) // s ^ 2 = 1} :=
        { toFun := fun w => ⟨w.1 * (((z : ℤ) : ZMod (p ^ k)))⁻¹, by
            have hZ : ((z : ℤ) : ZMod (p ^ k)) * (((z : ℤ) : ZMod (p ^ k)))⁻¹ = 1 :=
              ZMod.mul_inv_of_unit _ hz0unit
            rw [mul_pow, w.2, ← hroot, ← mul_pow, hZ, one_pow]⟩
          invFun := fun s => ⟨s.1 * ((z : ℤ) : ZMod (p ^ k)), by
            rw [mul_pow, s.2, one_mul, hroot]⟩
          left_inv := fun w => by
            ext
            simp only
            rw [mul_assoc, ZMod.inv_mul_of_unit _ hz0unit, mul_one]
          right_inv := fun s => by
            ext
            simp only
            rw [mul_assoc, ZMod.mul_inv_of_unit _ hz0unit, mul_one] }
      rw [Nat.card_congr e]
      exact card_sq_eq_one_zmod_prime_pow p k hp hodd hk
    rw [hcard, hjc, hleg]; norm_num
  · have hleg : legendreSym p c = -1 := (legendreSym.eq_neg_one_iff p).mpr hs
    have hcard : Nat.card {w : ZMod (p ^ k) // w ^ 2 = (c : ZMod (p ^ k))} = 0 := by
      haveI : IsEmpty {w : ZMod (p ^ k) // w ^ 2 = (c : ZMod (p ^ k))} :=
        ⟨fun w => hs ⟨(ZMod.castHom hdvd (ZMod p)) w.1, by
          have h2 : (ZMod.castHom hdvd (ZMod p)) ((c : ℤ) : ZMod (p ^ k))
              = ((c : ℤ) : ZMod p) := by
            rw [ZMod.castHom_apply]
            exact ZMod.cast_intCast hdvd c
          have h := congrArg (ZMod.castHom hdvd (ZMod p)) w.2
          rw [map_pow, h2] at h
          simpa [pow_two] using h.symm⟩⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hcard, hjc, hleg]; norm_num

end Work.FIArea2
