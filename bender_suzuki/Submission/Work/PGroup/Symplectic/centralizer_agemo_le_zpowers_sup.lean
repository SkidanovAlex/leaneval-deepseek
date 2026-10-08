import Mathlib
import Submission.Work.PGroup.Symplectic.exists_pow_eq_one_add_mul_p

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of `c ^ p` lies in `⟨c⟩ · ⟨y⟩`

Let `X` be a group, `p` a prime, `n ≥ 2`, `c ∈ X` of order `p ^ n`, and `R ≤ X` a subgroup
containing `c` and normalizing `⟨c⟩` (`hnormal`), with `R ∩ C_X(c) = ⟨c⟩` (`hCen`).  Let
`y ∈ R ∖ ⟨c⟩` conjugate `c` to `c ^ (1 + m * p ^ (n - 1))` (`hyconj`).

Then every `u ∈ R` centralizing `c ^ p` is a product `c ^ i * y ^ j`.

This is the group-theoretic structure lemma behind P. Hall's classification of `p`-groups of
symplectic type (Feit–Thompson 3.5 / Gorenstein §5.4).
-/

set_option linter.style.haveILetI false

namespace Work.PGroup.Symplectic

/-- Iterated conjugation by `y⁻¹`: if `y⁻¹ * c * y = c ^ d` then
`(y ^ j)⁻¹ * c * y ^ j = c ^ (d ^ j)`. -/
theorem inv_conj_pow {X : Type*} [Group X] {c y : X} {d : ℕ}
    (h : y⁻¹ * c * y = c ^ d) :
    ∀ j : ℕ, (y ^ j)⁻¹ * c * y ^ j = c ^ (d ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    have hstep : (y ^ (k + 1))⁻¹ * c * y ^ (k + 1)
        = y⁻¹ * ((y ^ k)⁻¹ * c * y ^ k) * y := by
      rw [pow_succ, mul_inv_rev]; group
    rw [hstep, ih]
    have hconj : y⁻¹ * c ^ (d ^ k) * y = (y⁻¹ * c * y) ^ (d ^ k) := by
      simpa using (conj_pow (a := y⁻¹) (b := c) (i := d ^ k)).symm
    rw [hconj, h, ← pow_mul, pow_succ']

/-- `(1 + x) ^ j ≡ 1 + j * x` modulo `x ^ 2`. -/
theorem pow_one_add_modEq_sq {x : ℕ} (j : ℕ) : (1 + x) ^ j ≡ 1 + j * x [MOD x ^ 2] := by
  induction j with
  | zero => simpa using Nat.ModEq.refl (n := x ^ 2) 1
  | succ k ih =>
    have hx2 : x * x ≡ 0 [MOD x ^ 2] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨1, by ring⟩
    calc (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := pow_succ _ _
      _ ≡ (1 + k * x) * (1 + x) [MOD x ^ 2] := ih.mul_right _
      _ = 1 + (k + 1) * x + k * (x * x) := by ring
      _ ≡ 1 + (k + 1) * x + 0 [MOD x ^ 2] :=
            Nat.ModEq.add_left _ (by simpa using hx2.mul_left k)
      _ = 1 + (k + 1) * x := by ring

/-- Arithmetic core: `1 + m * p ^ (n-1)` generates, modulo `p ^ n`, the class of `k` whenever
`k ≡ 1 mod p ^ (n-1)` and `p ∤ m`. -/
theorem exists_pow_modEq_of_agemo {p n m k : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hm : ¬ p ∣ m)
    (hk1 : 1 ≤ k) (hk : p ^ (n - 1) ∣ k - 1) :
    ∃ j : ℕ, (1 + m * p ^ (n - 1)) ^ j ≡ k [MOD p ^ n] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have hpe : p * p ^ (n - 1) = p ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn1]
  obtain ⟨s, hs⟩ := hk
  have hk_eq : k = 1 + s * p ^ (n - 1) := by
    have : k = (k - 1) + 1 := (Nat.sub_add_cancel hk1).symm
    rw [this, hs]; ring
  have hmz : (m : ZMod p) ≠ 0 := fun h => hm ((ZMod.natCast_eq_zero_iff m p).mp h)
  set j : ℕ := ((s : ZMod p) * (m : ZMod p)⁻¹).val with hjdef
  have hjval : (j : ZMod p) = (s : ZMod p) * (m : ZMod p)⁻¹ := by
    rw [hjdef]; exact ZMod.natCast_zmod_val _
  have hjm : j * m ≡ s [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff (j * m) s p).mp
    rw [Nat.cast_mul, hjval, mul_assoc, inv_mul_cancel₀ hmz, mul_one]
  refine ⟨j, ?_⟩
  have step1 : (1 + m * p ^ (n - 1)) ^ j ≡ 1 + j * (m * p ^ (n - 1))
      [MOD (m * p ^ (n - 1)) ^ 2] := pow_one_add_modEq_sq j
  have hdiv : p ^ n ∣ (m * p ^ (n - 1)) ^ 2 := by
    have hle : n ≤ 2 * (n - 1) := by omega
    have he : (m * p ^ (n - 1)) ^ 2 = m ^ 2 * p ^ (2 * (n - 1)) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    rw [he]
    exact dvd_mul_of_dvd_right (pow_dvd_pow p hle) (m ^ 2)
  have step2 : (1 + m * p ^ (n - 1)) ^ j ≡ 1 + j * (m * p ^ (n - 1)) [MOD p ^ n] :=
    Nat.ModEq.of_dvd hdiv step1
  have step3 : 1 + j * (m * p ^ (n - 1)) ≡ k [MOD p ^ n] := by
    rw [hk_eq]
    have h : (j * m) * p ^ (n - 1) ≡ s * p ^ (n - 1) [MOD p ^ n] := by
      have hh := hjm.mul_right' (p ^ (n - 1))
      rwa [hpe] at hh
    have hjeq : j * (m * p ^ (n - 1)) = (j * m) * p ^ (n - 1) := by ring
    rw [hjeq]
    exact Nat.ModEq.add_left 1 h
  exact step2.trans step3

theorem centralizer_agemo_le_zpowers_sup {X : Type*} [Group X] {p n m : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) {R : Subgroup X} {c y : X} (hcR : c ∈ R) (hyR : y ∈ R) (hc : orderOf c = p ^ n)
    (hnormal : ∀ r ∈ R, r⁻¹ * c * r ∈ Subgroup.zpowers c)
    (hCen : ∀ r ∈ R, r⁻¹ * c * r = c → r ∈ Subgroup.zpowers c)
    (hy : y ∉ Subgroup.zpowers c) (hyconj : y⁻¹ * c * y = c ^ (1 + m * p ^ (n - 1))) :
    ∀ u ∈ R, u⁻¹ * c ^ p * u = c ^ p → ∃ i j : ℕ, u = c ^ i * y ^ j := by
  intro u huR hu
  have hn1 : 1 ≤ n := by omega
  have hcpn : c ^ (p ^ n) = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hfc : IsOfFinOrder c :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ n, pow_pos hp.pos n, hcpn⟩
  obtain ⟨k, hk0⟩ := exists_pow_eq_of_mem_zpowers hfc (hnormal u huR)
  have hk : u⁻¹ * c * u = c ^ k := hk0.symm
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hk
      have hc1 : c = 1 := by
        have hcc : c = u * (u⁻¹ * c * u) * u⁻¹ := by group
        rw [hcc, hk]; group
      have : orderOf c = 1 := by rw [hc1]; exact orderOf_one
      rw [hc] at this
      have hlt : 1 < p ^ n := one_lt_pow₀ hp.one_lt (by omega)
      omega
    · exact hpos
  have hkdvd : p ^ (n - 1) ∣ k - 1 := by
    have hkp : c ^ (k * p) = c ^ p := by
      have h1 : (u⁻¹ * c * u) ^ p = c ^ (k * p) := by rw [hk, pow_mul]
      have h2 : (u⁻¹ * c * u) ^ p = c ^ p := by
        rw [show (u⁻¹ * c * u) ^ p = u⁻¹ * c ^ p * u by
              simpa using (conj_pow (a := u⁻¹) (b := c) (i := p))]
        exact hu
      rw [← h1, h2]
    have hmod : k * p ≡ p [MOD p ^ n] := by
      have := (pow_eq_pow_iff_modEq (x := c) (n := k * p) (m := p)).mp hkp
      rwa [hc] at this
    have hdvd : p ^ n ∣ k * p - p := hmod.symm.dvd'
    have hkeq : k * p - p = p * (k - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one, mul_comm k p]
    rw [hkeq, show p ^ n = p * p ^ (n - 1) by rw [← pow_succ', Nat.sub_add_cancel hn1]] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
  have hpm : ¬ p ∣ m := by
    intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hmt : m * p ^ (n - 1) = t * p ^ n := by
      rw [ht, show p * t * p ^ (n - 1) = t * (p * p ^ (n - 1)) by ring,
        show p * p ^ (n - 1) = p ^ n by rw [← pow_succ', Nat.sub_add_cancel hn1]]
    have hyd : y⁻¹ * c * y = c := by
      have : c ^ (1 + t * p ^ n) = c := by
        rw [pow_add, pow_one, mul_comm t (p ^ n), pow_mul, hcpn, one_pow, mul_one]
      rw [hyconj, hmt, this]
    exact hy (hCen y hyR hyd)
  obtain ⟨j, hj⟩ := exists_pow_modEq_of_agemo hp hn hpm hk1 hkdvd
  have hdj : (y ^ j)⁻¹ * c * y ^ j = c ^ ((1 + m * p ^ (n - 1)) ^ j) := inv_conj_pow hyconj j
  have hck : c ^ k = c ^ ((1 + m * p ^ (n - 1)) ^ j) :=
    (pow_eq_pow_iff_modEq (x := c) (m := (1 + m * p ^ (n - 1)) ^ j) (n := k)).mpr
      (by rw [hc]; exact hj.symm)
  have hck2 : c ^ k = (y ^ j)⁻¹ * c * y ^ j := hck.trans hdj.symm
  have hwcen : (u * (y ^ j)⁻¹)⁻¹ * c * (u * (y ^ j)⁻¹) = c := by
    have e1 : (u * (y ^ j)⁻¹)⁻¹ * c * (u * (y ^ j)⁻¹)
        = y ^ j * (u⁻¹ * c * u) * (y ^ j)⁻¹ := by
      rw [mul_inv_rev, inv_inv]; group
    rw [e1, hk, hck2]; group
  have hwR : u * (y ^ j)⁻¹ ∈ R := R.mul_mem huR (R.inv_mem (R.pow_mem hyR j))
  obtain ⟨i, hi⟩ := exists_pow_eq_of_mem_zpowers hfc (hCen _ hwR hwcen)
  exact ⟨i, j, by rw [hi]; group⟩

end Work.PGroup.Symplectic
