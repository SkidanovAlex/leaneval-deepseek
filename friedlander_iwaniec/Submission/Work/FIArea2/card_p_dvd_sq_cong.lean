import Mathlib

namespace Work.FIArea2

open Finset

attribute [local instance] Classical.propDecidable

/-- Reducing a square modulo `m`: `a * n ^ 2 ≡ a * (n % m) ^ 2 (mod m)`, in `%` form. -/
lemma mul_sq_mod_mod (a n m : ℕ) : (a * n ^ 2) % m = (a * (n % m) ^ 2) % m := by
  calc (a * n ^ 2) % m = (a % m) * (n ^ 2 % m) % m := Nat.mul_mod a _ m
    _ = (a % m) * ((n % m) ^ 2 % m) % m := by rw [Nat.pow_mod]
    _ = (a * (n % m) ^ 2) % m := (Nat.mul_mod a _ m).symm

/-- `k * A ≡ k * B (mod k * m)` iff `A ≡ B (mod m)`, for `k > 0`. -/
lemma mul_mod_mul_iff {k m A B : ℕ} (hk : 0 < k) :
    (k * A) % (k * m) = (k * B) % (k * m) ↔ A % m = B % m := by
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact ⟨fun h => Nat.mul_left_cancel hk h, fun h => by rw [h]⟩

/-- If `p ∣ x` and `a * x ^ 2 ≡ y ^ 2 (mod p ^ ν)` with `ν ≥ 2`, then `p ∣ y`. -/
lemma dvd_snd_of_cong (p ν a : ℕ) (hp : p.Prime) (hν : 2 ≤ ν) {x y : ℕ}
    (hx : p ∣ x) (h : (a * x ^ 2) % p ^ ν = (y ^ 2) % p ^ ν) : p ∣ y := by
  have h2ν : p ^ 2 ∣ p ^ ν := pow_dvd_pow p hν
  have hx2 : p ^ 2 ∣ x ^ 2 := by
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c ^ 2, by ring⟩
  have hmod : (a * x ^ 2) % p ^ 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hx2 a)
  have hy : (y ^ 2) % p ^ 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd (y ^ 2) h2ν, ← h, Nat.mod_mod_of_dvd (a * x ^ 2) h2ν, hmod]
  exact hp.dvd_of_dvd_pow
    (dvd_trans (dvd_pow_self p (by norm_num)) (Nat.dvd_of_mod_eq_zero hy))

/-- **The `p ∣ x` part of the congruence `a x² ≡ y² (mod p^ν)` at residue level.**  For a prime `p` and `ν ≥ 2`, the number of pairs of residues `(x,y)` with `0 ≤ x,y < p^ν`, `p ∣ x` and `a x² ≡ y² (mod p^ν)` equals `p²` times the number of pairs `(x',y')` with `0 ≤ x',y' < p^{ν-2}` and `a x'² ≡ y'² (mod p^{ν-2})`.  Indeed `p ∣ x` forces `p ∣ y`, and writing `x = p x'`, `y = p y'` with `x',y' < p^{ν-1}` the condition is `p^{ν-2} ∣ a x'² - y'²`, which involves only the residues of `x', y'` mod `p^{ν-2}`; each residue class mod `p^{ν-2}` in `[0, p^{ν-1})` has exactly `p` elements.  This is one half of the two-step recursion `N_ν = U_ν + p²N_{ν-2}` for the count `N_ν` of solutions of `aγ₁² ≡ γ₂² (mod p^ν)`.  No coprimality assumption on `a` is needed. -/
theorem card_p_dvd_sq_cong (p ν a : ℕ) (hp : p.Prime) (hν : 2 ≤ ν) :
    ((Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
        (fun z => p ∣ z.1 ∧ (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν)).card
      = p ^ 2 * ((Finset.range (p ^ (ν - 2)) ×ˢ Finset.range (p ^ (ν - 2))).filter
          (fun z => (a * z.1 ^ 2) % p ^ (ν - 2) = (z.2 ^ 2) % p ^ (ν - 2))).card := by
  set m := p ^ (ν - 2) with hm_def
  have hm : 0 < m := by rw [hm_def]; exact pow_pos hp.pos _
  have hpν : p ^ ν = p ^ 2 * m := by
    rw [hm_def]
    conv_lhs => rw [show ν = (ν - 2) + 2 by omega]
    rw [pow_add]; ring
  have hpν' : p ^ ν = p * p ^ (ν - 1) := by
    conv_lhs => rw [show ν = (ν - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hpν1 : p ^ (ν - 1) = p * m := by
    rw [hm_def]
    conv_lhs => rw [show ν - 1 = (ν - 2) + 1 by omega]
    rw [pow_succ]; ring
  set S : Finset (ℕ × ℕ) := (Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
      (fun z => p ∣ z.1 ∧ (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν) with hS_def
  set R : Finset (ℕ × ℕ) := (Finset.range m ×ˢ Finset.range m).filter
      (fun z => (a * z.1 ^ 2) % m = (z.2 ^ 2) % m) with hR_def
  have key : S.card = (R ×ˢ (Finset.range p ×ˢ Finset.range p)).card := by
    refine Finset.card_bij (s := S) (t := R ×ˢ (Finset.range p ×ˢ Finset.range p))
      (fun z _ => (((z.1 / p) % m, (z.2 / p) % m), ((z.1 / p) / m, (z.2 / p) / m)))
      ?_ ?_ ?_
    · -- forward: membership
      intro z hz
      rw [hS_def] at hz
      obtain ⟨hzP, hpz1, hcong⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzP
      rw [Finset.mem_range] at hz1 hz2
      have hpz2 : p ∣ z.2 := dvd_snd_of_cong p ν a hp hν hpz1 hcong
      have hz1e : z.1 = p * (z.1 / p) := (Nat.mul_div_cancel' hpz1).symm
      have hz2e : z.2 = p * (z.2 / p) := (Nat.mul_div_cancel' hpz2).symm
      have hdiv1 : z.1 / p < p ^ (ν - 1) := by
        have hlt : p * (z.1 / p) < p * p ^ (ν - 1) := by rw [← hz1e, ← hpν']; exact hz1
        exact Nat.lt_of_mul_lt_mul_left hlt
      have hdiv2 : z.2 / p < p ^ (ν - 1) := by
        have hlt : p * (z.2 / p) < p * p ^ (ν - 1) := by rw [← hz2e, ← hpν']; exact hz2
        exact Nat.lt_of_mul_lt_mul_left hlt
      have hred : (a * (z.1 / p) ^ 2) % m = ((z.2 / p) ^ 2) % m := by
        have hA : a * z.1 ^ 2 = p ^ 2 * (a * (z.1 / p) ^ 2) := by
          conv_lhs => rw [hz1e]
          ring_nf
        have hB : z.2 ^ 2 = p ^ 2 * (z.2 / p) ^ 2 := by
          conv_lhs => rw [hz2e]
          ring_nf
        have h' : (p ^ 2 * (a * (z.1 / p) ^ 2)) % (p ^ 2 * m)
            = (p ^ 2 * (z.2 / p) ^ 2) % (p ^ 2 * m) := by
          rw [← hpν, ← hA, ← hB]; exact hcong
        exact (mul_mod_mul_iff (k := p ^ 2) (pow_pos hp.pos 2)).mp h'
      rw [hR_def]
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), Finset.mem_range.mpr (Nat.mod_lt _ hm)⟩
        · show (a * ((z.1 / p) % m) ^ 2) % m = (((z.2 / p) % m) ^ 2) % m
          rw [← mul_sq_mod_mod a (z.1 / p) m, ← Nat.pow_mod (z.2 / p) 2 m]
          exact hred
      · refine Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hpν1]; exact hdiv1)),
           Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hpν1]; exact hdiv2))⟩
    · -- injective
      intro z hz w hw hzw
      rw [hS_def] at hz hw
      obtain ⟨-, hpz1, hcz⟩ := Finset.mem_filter.mp hz
      obtain ⟨-, hpw1, hcw⟩ := Finset.mem_filter.mp hw
      have hpz2 : p ∣ z.2 := dvd_snd_of_cong p ν a hp hν hpz1 hcz
      have hpw2 : p ∣ w.2 := dvd_snd_of_cong p ν a hp hν hpw1 hcw
      have h11 : (z.1 / p) % m = (w.1 / p) % m := by
        have := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.1) hzw
        simpa using this
      have h22 : (z.2 / p) % m = (w.2 / p) % m := by
        have := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.1.2) hzw
        simpa using this
      have h33 : (z.1 / p) / m = (w.1 / p) / m := by
        have := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.1) hzw
        simpa using this
      have h44 : (z.2 / p) / m = (w.2 / p) / m := by
        have := congrArg (fun t : (ℕ × ℕ) × (ℕ × ℕ) => t.2.2) hzw
        simpa using this
      have hz1e : p * (z.1 / p) = z.1 := Nat.mul_div_cancel' hpz1
      have hw1e : p * (w.1 / p) = w.1 := Nat.mul_div_cancel' hpw1
      have hz2e : p * (z.2 / p) = z.2 := Nat.mul_div_cancel' hpz2
      have hw2e : p * (w.2 / p) = w.2 := Nat.mul_div_cancel' hpw2
      have e1 : z.1 / p = w.1 / p := by
        rw [← Nat.mod_add_div (z.1 / p) m, ← Nat.mod_add_div (w.1 / p) m, h11, h33]
      have e2 : z.2 / p = w.2 / p := by
        rw [← Nat.mod_add_div (z.2 / p) m, ← Nat.mod_add_div (w.2 / p) m, h22, h44]
      exact Prod.ext (by rw [← hz1e, ← hw1e, e1]) (by rw [← hz2e, ← hw2e, e2])
    · -- surjective
      intro b hb
      rcases b with ⟨⟨u, v⟩, ⟨i, j⟩⟩
      rw [hR_def] at hb
      obtain ⟨hbR, hbij⟩ := Finset.mem_product.mp hb
      obtain ⟨hrange, hRc⟩ := Finset.mem_filter.mp hbR
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hrange
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbij
      simp only [Finset.mem_range] at hu hv hi hj
      have huim : u + i * m < p * m := by
        calc u + i * m < m + i * m := Nat.add_lt_add_right hu (i * m)
          _ = (i + 1) * m := by ring
          _ ≤ p * m := Nat.mul_le_mul_right m (by omega)
      have hvjm : v + j * m < p * m := by
        calc v + j * m < m + j * m := Nat.add_lt_add_right hv (j * m)
          _ = (j + 1) * m := by ring
          _ ≤ p * m := Nat.mul_le_mul_right m (by omega)
      have h1 : (u + i * m) % m = u := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      have h2 : (v + j * m) % m = v := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
      have hcl : (a * (u + i * m) ^ 2) % m = ((v + j * m) ^ 2) % m := by
        rw [mul_sq_mod_mod a (u + i * m) m, Nat.pow_mod (v + j * m) 2 m, h1, h2]
        simpa using hRc
      refine ⟨(p * (u + i * m), p * (v + j * m)), ?_, ?_⟩
      · rw [hS_def]
        refine Finset.mem_filter.mpr ⟨?_, dvd_mul_right p _, ?_⟩
        · rw [hpν]
          refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · exact Finset.mem_range.mpr
              (calc p * (u + i * m) < p * (p * m) := Nat.mul_lt_mul_of_pos_left huim hp.pos
                _ = p ^ 2 * m := by ring)
          · exact Finset.mem_range.mpr
              (calc p * (v + j * m) < p * (p * m) := Nat.mul_lt_mul_of_pos_left hvjm hp.pos
                _ = p ^ 2 * m := by ring)
        · rw [hpν]
          have hA : a * (p * (u + i * m)) ^ 2 = p ^ 2 * (a * (u + i * m) ^ 2) := by ring
          have hB : (p * (v + j * m)) ^ 2 = p ^ 2 * (v + j * m) ^ 2 := by ring
          rw [hA, hB]
          exact (mul_mod_mul_iff (k := p ^ 2) (pow_pos hp.pos 2)).mpr hcl
      · have hf1 : (p * (u + i * m)) / p = u + i * m := Nat.mul_div_cancel_left _ hp.pos
        have hf2 : (p * (v + j * m)) / p = v + j * m := Nat.mul_div_cancel_left _ hp.pos
        have hd1 : (u + i * m) / m = i := by
          rw [Nat.add_mul_div_right u i hm, Nat.div_eq_of_lt hu, zero_add]
        have hd2 : (v + j * m) / m = j := by
          rw [Nat.add_mul_div_right v j hm, Nat.div_eq_of_lt hv, zero_add]
        simp only [hf1, hf2, h1, h2, hd1, hd2]
  rw [key, Finset.card_product, Finset.card_product, Finset.card_range]
  ring

end Work.FIArea2
