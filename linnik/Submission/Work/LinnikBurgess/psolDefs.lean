import Mathlib
import Submission.Work.LinnikBurgess.capContent_fiber_six_base
import Submission.Work.LinnikBurgess.eq_of_dvd_sub_of_lt

/-!
# Helper lemmas for `Work.LinnikBurgess.countPsol`

Counts the integers `x < p^n` with `p^B ∣ x*u + x^2 * H.eval (y0 + p^ν * x)`.
The key input is a Hensel-type analysis: modulo `p^B` there is at most one solution
in each of the two classes `p ∣ x` (necessarily `x ≡ 0`) and `p ∤ x`.
-/

namespace Work.LinnikBurgess

open Polynomial

noncomputable def psolVal (p ν : ℕ) (y0 : ℤ) (H : Polynomial ℤ) (u : ℤ) (z : ℤ) : ℤ :=
  z * u + z ^ 2 * H.eval (y0 + ((p ^ ν : ℕ) : ℤ) * z)

noncomputable def psolPoly (p ν : ℕ) (y0 : ℤ) (H : Polynomial ℤ) (u : ℤ) : Polynomial ℤ :=
  C u * X + X ^ 2 * H.comp (C y0 + C (((p ^ ν : ℕ) : ℤ)) * X)

lemma psolPoly_eval (p ν : ℕ) (y0 : ℤ) (H : Polynomial ℤ) (u : ℤ) (z : ℤ) :
    (psolPoly p ν y0 H u).eval z = psolVal p ν y0 H u z := by
  simp only [psolPoly, psolVal, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_comp]
  ring

lemma psolPoly_sub_dvd {p B ν : ℕ} (y0 : ℤ) (H : Polynomial ℤ) (u : ℤ) {a b : ℤ}
    (h : ((p:ℤ)^B) ∣ (a - b)) :
    ((p:ℤ)^B) ∣ (psolPoly p ν y0 H u).eval a - (psolPoly p ν y0 H u).eval b := by
  obtain ⟨E, hE⟩ := int_dividedDiff (psolPoly p ν y0 H u) a b
  rw [hE]
  exact h.trans (dvd_mul_right (a - b) E)

lemma psol_p_dvd_p_pow {p ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) :
    (p:ℤ) ∣ (((p^ν:ℕ)) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ν ≠ 0)
  rw [Nat.cast_pow, pow_succ]
  exact dvd_mul_left _ _

lemma psol_modp_linear {p ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ) (H : Polynomial ℤ)
    (u : ℤ) {r : ℤ} (hr : ¬ (p:ℤ) ∣ r) (hroot : (p:ℤ) ∣ psolVal p ν y0 H u r) :
    (p:ℤ) ∣ u + r * H.eval y0 := by
  have hW : (p:ℤ) ∣ H.eval (y0 + ((p^ν:ℕ):ℤ) * r) - H.eval y0 := by
    obtain ⟨E, hE⟩ := int_dividedDiff H (y0 + ((p^ν:ℕ):ℤ) * r) y0
    rw [hE]
    have hfac : (y0 + ((p^ν:ℕ):ℤ) * r) - y0 = ((p^ν:ℕ):ℤ) * r := by ring
    rw [hfac]
    exact (dvd_mul_of_dvd_left (psol_p_dvd_p_pow (p := p) hν) r).mul_right E
  have hdiff : (p:ℤ) ∣ psolVal p ν y0 H u r - r * (u + r * H.eval y0) := by
    have hfac : psolVal p ν y0 H u r - r * (u + r * H.eval y0)
        = r^2 * (H.eval (y0 + ((p^ν:ℕ):ℤ) * r) - H.eval y0) := by
      simp only [psolVal]; ring
    rw [hfac]
    exact dvd_mul_of_dvd_right hW (r^2)
  have h2 : (p:ℤ) ∣ r * (u + r * H.eval y0) := by
    have h := dvd_sub hroot hdiff
    have heq : psolVal p ν y0 H u r - (psolVal p ν y0 H u r - r * (u + r * H.eval y0))
        = r * (u + r * H.eval y0) := by ring
    rwa [heq] at h
  have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  rcases hp.dvd_mul.mp h2 with h | h
  · exact absurd h hr
  · exact h

lemma psol_nonunit_step {p B j ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ)
    (H : Polynomial ℤ) (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) (hj : 1 ≤ j) (hjB : j < B)
    {r : ℤ} (hjr : ((p:ℤ)^j) ∣ r) (hroot : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r) :
    ((p:ℤ)^(j+1)) ∣ r := by
  have hpz : (p:ℤ) ≠ 0 := by
    have : (0:ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    omega
  obtain ⟨s, rfl⟩ := hjr
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero j hpz)]
  have hGfac : psolVal p ν y0 H u ((p:ℤ)^j * s)
      = (p:ℤ)^j * (s * u + (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s))) := by
    simp only [psolVal]; ring
  rw [hGfac] at hroot
  have hpow : (p:ℤ)^B = (p:ℤ)^j * (p:ℤ)^(B-j) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hjB)]
  rw [hpow] at hroot
  have hX : ((p:ℤ)^(B-j)) ∣
      (s * u + (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s))) :=
    (mul_dvd_mul_iff_left (pow_ne_zero j hpz)).mp hroot
  have hpdvdpow : (p:ℤ) ∣ (p:ℤ)^(B-j) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B - j ≠ 0)
    rw [hk, pow_succ]; exact dvd_mul_left _ _
  have hpdvdX : (p:ℤ) ∣
      (s * u + (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s))) :=
    hpdvdpow.trans hX
  have hjpow : (p:ℤ) ∣ (p:ℤ)^j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [pow_succ]; exact dvd_mul_left _ _
  have hW : (p:ℤ) ∣ (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s)) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hjpow (s^2)) _
  have hsu : (p:ℤ) ∣ s * u := by
    have h := dvd_sub hpdvdX hW
    have heq : (s * u + (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s)))
        - (p:ℤ)^j * s^2 * H.eval (y0 + ((p^ν:ℕ):ℤ) * ((p:ℤ)^j * s)) = s * u := by ring
    rwa [heq] at h
  have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  rcases hp.dvd_mul.mp hsu with h | h
  · exact h
  · exact absurd h hu

lemma psol_unit_step {p B k ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ)
    (H : Polynomial ℤ) (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) (hkB : k < B) {r r' : ℤ}
    (hr : ¬ (p:ℤ) ∣ r) (hr' : ¬ (p:ℤ) ∣ r')
    (hroot : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r)
    (hroot' : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r')
    (hk : ((p:ℤ)^k) ∣ (r - r')) :
    ((p:ℤ)^(k+1)) ∣ (r - r') := by
  have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hB1 : 1 ≤ B := by omega
  have hpdvdB : (p:ℤ) ∣ (p:ℤ)^B := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
    rw [pow_succ]; exact dvd_mul_left _ _
  have hbr : (p:ℤ) ∣ u + r * H.eval y0 := psol_modp_linear hν y0 H u hr (hpdvdB.trans hroot)
  have hbr' : (p:ℤ) ∣ u + r' * H.eval y0 := psol_modp_linear hν y0 H u hr' (hpdvdB.trans hroot')
  have hsum : (p:ℤ) ∣ 2*u + (r+r')*H.eval y0 := by
    have h := dvd_add hbr hbr'
    have heq : (u + r*H.eval y0) + (u + r'*H.eval y0) = 2*u + (r+r')*H.eval y0 := by ring
    rwa [heq] at h
  have hbrk : ¬ (p:ℤ) ∣ (u + (r+r')*H.eval y0) := by
    intro hcon
    have h := dvd_sub hsum hcon
    have heq : (2*u + (r+r')*H.eval y0) - (u + (r+r')*H.eval y0) = u := by ring
    rw [heq] at h
    exact hu h
  have hA : ((p:ℤ)^(k+1)) ∣
      r^2 * (H.eval (y0 + ((p^ν:ℕ):ℤ)*r) - H.eval (y0 + ((p^ν:ℕ):ℤ)*r')) := by
    have hdiff : ((p:ℤ)^(k+1)) ∣
        (H.eval (y0 + ((p^ν:ℕ):ℤ)*r) - H.eval (y0 + ((p^ν:ℕ):ℤ)*r')) := by
      obtain ⟨E, hE⟩ := int_dividedDiff H (y0 + ((p^ν:ℕ):ℤ)*r) (y0 + ((p^ν:ℕ):ℤ)*r')
      rw [hE]
      have hfac : (y0 + ((p^ν:ℕ):ℤ)*r) - (y0 + ((p^ν:ℕ):ℤ)*r') = ((p^ν:ℕ):ℤ) * (r - r') := by ring
      rw [hfac]
      obtain ⟨t, ht⟩ := hk
      rw [ht, Nat.cast_pow]
      have heq : (p:ℤ)^ν * ((p:ℤ)^k * t) = (p:ℤ)^(ν+k) * t := by
        rw [← mul_assoc, ← pow_add]
      rw [heq]
      have hle : k+1 ≤ ν+k := by omega
      exact (dvd_mul_of_dvd_left (pow_dvd_pow _ hle) t).mul_right E
    exact dvd_mul_of_dvd_right hdiff (r^2)
  have hB' : ((p:ℤ)^(k+1)) ∣
      (r - r') * (r + r') * (H.eval (y0 + ((p^ν:ℕ):ℤ)*r') - H.eval y0) := by
    have hW0 : (p:ℤ) ∣ (H.eval (y0 + ((p^ν:ℕ):ℤ)*r') - H.eval y0) := by
      obtain ⟨E, hE⟩ := int_dividedDiff H (y0 + ((p^ν:ℕ):ℤ)*r') y0
      rw [hE]
      have hfac : (y0 + ((p^ν:ℕ):ℤ)*r') - y0 = ((p^ν:ℕ):ℤ) * r' := by ring
      rw [hfac]
      exact (dvd_mul_of_dvd_left (psol_p_dvd_p_pow (p := p) hν) r').mul_right E
    obtain ⟨t, ht⟩ := hk
    obtain ⟨c, hc⟩ := hW0
    rw [ht, hc, pow_succ]
    exact ⟨t * (r + r') * c, by ring⟩
  have hD : ((p:ℤ)^(k+1)) ∣
      psolVal p ν y0 H u r - psolVal p ν y0 H u r' - (r - r') * (u + (r+r')*H.eval y0) := by
    have heq : psolVal p ν y0 H u r - psolVal p ν y0 H u r' - (r - r') * (u + (r+r')*H.eval y0)
        = r^2 * (H.eval (y0 + ((p^ν:ℕ):ℤ)*r) - H.eval (y0 + ((p^ν:ℕ):ℤ)*r'))
          + (r - r') * (r + r') * (H.eval (y0 + ((p^ν:ℕ):ℤ)*r') - H.eval y0) := by
      simp only [psolVal]; ring
    rw [heq]
    exact dvd_add hA hB'
  have h4 : ((p:ℤ)^(k+1)) ∣ psolVal p ν y0 H u r - psolVal p ν y0 H u r' := by
    have hle : k+1 ≤ B := by omega
    have h1 : ((p:ℤ)^(k+1)) ∣ (p:ℤ)^B := pow_dvd_pow _ hle
    exact dvd_sub (h1.trans hroot) (h1.trans hroot')
  have hprod : ((p:ℤ)^(k+1)) ∣ (r - r') * (u + (r+r')*H.eval y0) := by
    have h := dvd_sub h4 hD
    have heq : (psolVal p ν y0 H u r - psolVal p ν y0 H u r')
        - (psolVal p ν y0 H u r - psolVal p ν y0 H u r' - (r - r') * (u + (r+r')*H.eval y0))
        = (r - r') * (u + (r+r')*H.eval y0) := by ring
    rwa [heq] at h
  have hcop : IsCoprime ((p:ℤ)^(k+1)) (u + (r+r')*H.eval y0) := by
    have h1 : IsCoprime (p:ℤ) (u + (r+r')*H.eval y0) := (hp.coprime_iff_not_dvd).mpr hbrk
    exact h1.pow_left
  rw [mul_comm] at hprod
  exact hcop.dvd_of_dvd_mul_left hprod

lemma psol_nonunit {p B ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ) (H : Polynomial ℤ)
    (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) {r : ℤ} (hr : (p:ℤ) ∣ r)
    (hroot : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r) :
    ((p:ℤ)^B) ∣ r := by
  have aux : ∀ B r, (p:ℤ) ∣ r → ((p:ℤ)^B) ∣ psolVal p ν y0 H u r → ((p:ℤ)^B) ∣ r := by
    intro B
    induction B with
    | zero => intro r hr hroot; exact one_dvd r
    | succ B ih =>
      intro r hr hroot
      have hrootB : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r :=
        (pow_dvd_pow _ (Nat.le_succ B)).trans hroot
      cases B with
      | zero => simpa [pow_one] using hr
      | succ j =>
        have hBr : ((p:ℤ)^(j+1)) ∣ r := ih r hr hrootB
        exact psol_nonunit_step hν y0 H u hu (show 1 ≤ j+1 by omega)
          (show j+1 < j+2 by omega) hBr hroot
  exact aux B r hr hroot

lemma psol_unit_congr {p B ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ) (H : Polynomial ℤ)
    (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) {r r' : ℤ} (hr : ¬ (p:ℤ) ∣ r) (hr' : ¬ (p:ℤ) ∣ r')
    (hroot : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r)
    (hroot' : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r') :
    ((p:ℤ)^B) ∣ (r - r') := by
  have aux : ∀ B r r', ¬ (p:ℤ) ∣ r → ¬ (p:ℤ) ∣ r' →
      ((p:ℤ)^B) ∣ psolVal p ν y0 H u r → ((p:ℤ)^B) ∣ psolVal p ν y0 H u r' →
      ((p:ℤ)^B) ∣ (r - r') := by
    intro B
    induction B with
    | zero => intro r r' hr hr' _ _; exact one_dvd _
    | succ B ih =>
      intro r r' hr hr' hroot hroot'
      have hrootB : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r :=
        (pow_dvd_pow _ (Nat.le_succ B)).trans hroot
      have hrootB' : ((p:ℤ)^B) ∣ psolVal p ν y0 H u r' :=
        (pow_dvd_pow _ (Nat.le_succ B)).trans hroot'
      have hk : ((p:ℤ)^B) ∣ (r - r') := ih r r' hr hr' hrootB hrootB'
      exact psol_unit_step hν y0 H u hu (show B < B+1 by omega) hr hr' hroot hroot' hk
  exact aux B r r' hr hr' hroot hroot'

lemma psol_S_nonunit_eq_zero {p B ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ)
    (H : Polynomial ℤ) (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) {a : ℕ} (ha : a < p^B)
    (hpdvd : (p:ℤ) ∣ (a:ℤ)) (haP : ((p:ℤ)^B) ∣ psolVal p ν y0 H u (a:ℤ)) : a = 0 := by
  have hdvd : ((p:ℤ)^B) ∣ (a:ℤ) := psol_nonunit hν y0 H u hu hpdvd haP
  have hnat : p^B ∣ a := by
    have : ((p^B:ℕ):ℤ) ∣ (a:ℤ) := by rw [Nat.cast_pow]; exact hdvd
    exact_mod_cast this
  exact Nat.eq_zero_of_dvd_of_lt hnat ha

lemma psol_S_unit_eq {p B ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (y0 : ℤ)
    (H : Polynomial ℤ) (u : ℤ) (hu : ¬ (p:ℤ) ∣ u) {a b : ℕ} (ha : a < p^B) (hb : b < p^B)
    (hap : ¬ (p:ℤ) ∣ (a:ℤ)) (hbp : ¬ (p:ℤ) ∣ (b:ℤ))
    (haP : ((p:ℤ)^B) ∣ psolVal p ν y0 H u (a:ℤ))
    (hbP : ((p:ℤ)^B) ∣ psolVal p ν y0 H u (b:ℤ)) : a = b := by
  have hdvd : ((p:ℤ)^B) ∣ ((a:ℤ) - (b:ℤ)) := psol_unit_congr hν y0 H u hu hap hbp haP hbP
  have : ((p^B:ℕ):ℤ) ∣ ((a:ℤ) - (b:ℤ)) := by rw [Nat.cast_pow]; exact hdvd
  exact eq_of_dvd_sub_of_lt ha hb this

lemma card_residue_filter_le {p : ℕ} (hp : 1 ≤ p) (B n c : ℕ) :
    ((Finset.range (p ^ n)).filter (fun x : ℕ => x % p ^ B = c)).card ≤ p ^ (n - B) := by
  classical
  have hmaps : Set.MapsTo (fun x : ℕ => x / p^B)
      ↑((Finset.range (p ^ n)).filter (fun x : ℕ => x % p ^ B = c))
      ↑(Finset.range (p^(n-B))) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxn, -⟩ := hx
    refine Finset.mem_range.mpr (show x / p ^ B < p ^ (n - B) from ?_)
    by_cases hnB : B ≤ n
    · by_contra hcon
      simp only [not_lt] at hcon
      have h1 : p^(n-B) * p^B ≤ (x / p^B) * p^B := Nat.mul_le_mul_right _ hcon
      have h2 : (x / p^B) * p^B ≤ x := Nat.div_mul_le_self x (p^B)
      have h3 : p^(n-B) * p^B = p^n := by rw [← pow_add, Nat.sub_add_cancel hnB]
      have hx' : p^n ≤ x := by rw [← h3]; exact le_trans h1 h2
      omega
    · simp only [not_le] at hnB
      have hxlt : x < p^B :=
        lt_of_lt_of_le hxn (pow_le_pow_right' (by omega : 1 ≤ p) (le_of_lt hnB))
      rw [Nat.div_eq_of_lt hxlt]
      exact pow_pos (by omega : 0 < p) _
  have hinj : Set.InjOn (fun x : ℕ => x / p^B)
      ↑((Finset.range (p ^ n)).filter (fun x : ℕ => x % p ^ B = c)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    obtain ⟨-, hxc⟩ := hx
    obtain ⟨-, hyc⟩ := hy
    have hxy' : x / p^B = y / p^B := hxy
    have h1 : x = p^B * (x / p^B) + x % p^B := (Nat.div_add_mod x (p^B)).symm
    have h2 : y = p^B * (y / p^B) + y % p^B := (Nat.div_add_mod y (p^B)).symm
    rw [h1, h2, hxy', hxc, hyc]
  calc ((Finset.range (p ^ n)).filter (fun x : ℕ => x % p ^ B = c)).card
      ≤ (Finset.range (p^(n-B))).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = p^(n-B) := Finset.card_range _

end Work.LinnikBurgess
