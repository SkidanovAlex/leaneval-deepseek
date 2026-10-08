import Mathlib
import Submission.Work.PGroup.Symplectic.pow_eq_of_conj_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# A `p`-th root of unity of the form `r * c ^ s`

Let `X` be a group, `p` an odd prime, `n ≥ 2`, and let `c, r ∈ X` with `c` of order `p ^ n` and

`r⁻¹ * c * r = c ^ (1 + m * p ^ (n - 1))`,  where `p ∤ m`,

so that conjugation by `r` acts on `⟨c⟩ ≅ ℤ/p^n` by an automorphism of order `p` (the
`p`-group of symplectic type setting, Feit–Thompson 3.5 / Gorenstein §5.4).  Assume moreover
that `r ^ p ∈ ⟨c⟩`.  Then some translate `r * c ^ s` of `r` by an element of `⟨c⟩` has order
dividing `p`, and it conjugates `c` to the same power as `r`:

`∃ s : ℕ, (r * c ^ s) ^ p = 1 ∧ (r * c ^ s)⁻¹ * c * (r * c ^ s) = c ^ (1 + m * p ^ (n - 1))`.

Mathematically: writing `r ^ p = c ^ K` and `z = c ^ (p ^ (n - 1))` (of order `p`), the relation
`r⁻¹ * c ^ K * r = r⁻¹ * r ^ p * r = r ^ p = c ^ K` combined with `r⁻¹ * c ^ K * r =
(r⁻¹ * c * r) ^ K = c ^ K * z ^ (m * K)` forces `z ^ (m * K) = 1`, hence `p ∣ m * K`; as
`p ∤ m`, we get `p ∣ K`, say `K = p * j`, so `r ^ p = (c ^ j) ^ p`.  The class-two power formula
`(c ^ s * r) ^ p = c ^ (s * p) * r ^ p = c ^ ((s + j) * p)` of `pow_eq_of_conj_eq` then gives
`(c ^ s * r) ^ p = 1` as soon as `p ^ (n - 1) ∣ s + j`; the conjugate `r * c ^ s` is the required
element.
-/

namespace Work.PGroup.Symplectic

theorem exists_mul_pow_eq_one_of_conj {X : Type*} [Group X] {p n m : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hn : 2 ≤ n) {c r : X} (hc : orderOf c = p ^ n)
    (hconj : r⁻¹ * c * r = c ^ (1 + m * p ^ (n - 1))) (hm : ¬ p ∣ m)
    (hrp : r ^ p ∈ Subgroup.zpowers c) :
    ∃ s : ℕ, (r * c ^ s) ^ p = 1 ∧ (r * c ^ s)⁻¹ * c * (r * c ^ s) = c ^ (1 + m * p ^ (n - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have hpp : p ^ (n - 1) * p = p ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  have hcpn : c ^ (p ^ n) = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  -- `c` has finite order, so `r ^ p`, which lies in `⟨c⟩`, is a natural power `c ^ K` of `c`.
  have hfc : IsOfFinOrder c := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p ^ n, pow_pos hp.pos n, hcpn⟩
  obtain ⟨K, hK⟩ := (Submonoid.mem_powers_iff (r ^ p) c).mp
    ((IsOfFinOrder.mem_powers_iff_mem_zpowers hfc).mpr hrp)
  -- The central element `z = c ^ (p ^ (n - 1))`, of order `p`.
  set z : X := c ^ (p ^ (n - 1)) with hzdef
  have hzp : z ^ p = 1 := by
    rw [hzdef, ← pow_mul, hpp, hcpn]
  have hzne : z ≠ 1 := by
    intro hz1
    have hc1 : c ^ (p ^ (n - 1)) = 1 := by rw [← hzdef]; exact hz1
    have hdvd : p ^ n ∣ p ^ (n - 1) := by
      rw [← hc, orderOf_dvd_iff_pow_eq_one]; exact hc1
    have hlt : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd) (not_le.mpr hlt)
  have hzord : orderOf z = p := orderOf_eq_prime hzp hzne
  -- `z ^ (m * K) = 1`, hence `p ∣ m * K`.
  have hzK : z ^ (m * K) = 1 := by
    have h1 : (r⁻¹ * c * r) ^ K = c ^ K * z ^ (m * K) := by
      rw [hconj, hzdef]
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    have h2 : (r⁻¹ * c * r) ^ K = c ^ K := by
      have hh : (r⁻¹ * c * r) ^ K = r⁻¹ * c ^ K * r := by
        simpa using (conj_pow (a := r⁻¹) (b := c) (i := K))
      rw [hh, hK]; group
    rw [h1] at h2
    exact mul_left_cancel (a := c ^ K) (by rw [h2, mul_one])
  have hdvd : p ∣ m * K := by
    rw [← hzord, orderOf_dvd_iff_pow_eq_one]; exact hzK
  have hpK : p ∣ K := (hp.dvd_mul.mp hdvd).resolve_left hm
  obtain ⟨j, hj⟩ := hpK
  -- `r ^ p = (c ^ j) ^ p`.
  have hrpj : r ^ p = (c ^ j) ^ p := by
    rw [← hK, hj, mul_comm p j, pow_mul]
  -- Choose `s` with `p ^ (n - 1) ∣ s + j`.
  have hle : j ≤ p ^ (n - 1) * (j + 1) := by
    have h1 : 1 ≤ p ^ (n - 1) := Nat.one_le_pow _ _ hp.pos
    calc j ≤ j + 1 := by omega
      _ = 1 * (j + 1) := by ring
      _ ≤ p ^ (n - 1) * (j + 1) := Nat.mul_le_mul_right _ h1
  set s : ℕ := p ^ (n - 1) * (j + 1) - j with hsdef
  have hs : s + j = p ^ (n - 1) * (j + 1) := by
    rw [hsdef]; exact Nat.sub_add_cancel hle
  have hsp : s * p + j * p = p ^ n * (j + 1) := by
    rw [← add_mul, hs, mul_assoc, mul_comm (j + 1) p, ← mul_assoc, hpp]
  refine ⟨s, ?_, ?_⟩
  · -- `(c ^ s * r) ^ p = 1`, hence the conjugate `r * c ^ s` has order dividing `p`.
    have hpow : (c ^ s * r) ^ p = 1 := by
      have key : (c ^ s * r) ^ p = c ^ (s * p) * r ^ p :=
        (by simpa only [pow_one, one_mul] using
          (pow_eq_of_conj_eq hp hodd hn hc hconj s 1))
      rw [key, hrpj, ← pow_mul, ← pow_add, hsp, pow_mul, hcpn, one_pow]
    have h1 : r * c ^ s = r * (c ^ s * r) * r⁻¹ := by group
    have hh : (r * (c ^ s * r) * r⁻¹) ^ p = r * (c ^ s * r) ^ p * r⁻¹ :=
      conj_pow (a := r) (b := c ^ s * r) (i := p)
    rw [h1, hh, hpow, mul_one, mul_inv_cancel]
  · -- The conjugation action is unchanged.
    have h1 : (r * c ^ s)⁻¹ * c * (r * c ^ s)
        = (c ^ s)⁻¹ * (r⁻¹ * c * r) * c ^ s := by
      rw [mul_inv_rev]; group
    rw [h1, hconj]; group

end Work.PGroup.Symplectic
