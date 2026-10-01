import Mathlib
import Submission.Work.LinnikBurgess.capContent_fiber_six_base

namespace Work.LinnikBurgess

open Polynomial

/-- Auxiliary `p`-adic core of `clusterStep`.  Suppose `d ≠ 0`, `p ∣ d`, the derivative value
`a` is exactly divisible by `p^ν` (with `p ∤ a/p^ν`), the second derivative value `a2` is a unit,
`p^A ∣ d * (a + d * g)` with `A ≥ 2ν+1`, and `2g - a2` is divisible by `d`.  Then `p^ν ∣ d`. -/
lemma clusterStep_aux {p : ℕ} [Fact p.Prime] {d a a2 g E : ℤ} {ν A : ℕ}
    (_hν : 1 ≤ ν) (hA : 2 * ν + 1 ≤ A)
    (hd : d ≠ 0) (hp : (p : ℤ) ∣ d)
    (ha1 : ((p ^ ν : ℕ) : ℤ) ∣ a)
    (ha2 : ¬ (((p ^ (ν + 1) : ℕ) : ℤ)) ∣ a)
    (h3 : ¬ ((p : ℤ) ∣ a2))
    (hAdvd : ((p ^ A : ℕ) : ℤ) ∣ d * (a + d * g))
    (hrel : 2 * g - a2 = d * E) :
    ((p ^ ν : ℕ) : ℤ) ∣ d := by
  by_contra hcon
  have hd0 : d.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hd
  have ha_ne : a ≠ 0 := by
    intro h; exact ha2 (by rw [h]; exact dvd_zero _)
  have ha_abs_ne : a.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using ha_ne
  have hva : ν ≤ padicValNat p a.natAbs := by
    have hdvd : (p ^ ν : ℕ) ∣ a.natAbs := by
      have h' := (Int.natAbs_dvd_natAbs).mpr ha1
      simpa using h'
    rcases (padicValNat_dvd_iff (p := p) ν a.natAbs).mp hdvd with h | h
    · exact absurd h ha_abs_ne
    · exact h
  have hv_lt : padicValNat p d.natAbs < ν := by
    have hnot : ¬ ((p ^ ν : ℕ) ∣ d.natAbs) := by
      intro h
      exact hcon ((Int.natAbs_dvd_natAbs).mp (by simpa using h))
    have h2 : ¬ (ν ≤ padicValNat p d.natAbs) := by
      intro h; exact hnot ((padicValNat_dvd_iff (p := p) ν d.natAbs).mpr (Or.inr h))
    omega
  by_cases hpg : (p : ℤ) ∣ g
  · have hpa2 : (p : ℤ) ∣ a2 := by
      have h1 : (p : ℤ) ∣ 2 * g := dvd_mul_of_dvd_right hpg 2
      have h2 : (p : ℤ) ∣ d * E := dvd_mul_of_dvd_left hp E
      have hEq : a2 = 2 * g - d * E := by linarith [hrel]
      rw [hEq]; exact dvd_sub h1 h2
    exact h3 hpa2
  · have hg_ne : g ≠ 0 := by
      intro h; exact hpg (by rw [h]; exact dvd_zero _)
    have hg_abs_ne : g.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hg_ne
    have hvg : padicValNat p g.natAbs = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      exact hpg ((Int.natAbs_dvd_natAbs).mp (by simpa using h))
    have hdg_ne : d * g ≠ 0 := mul_ne_zero hd hg_ne
    have hvY : padicValNat p (d * g).natAbs = padicValNat p d.natAbs := by
      rw [Int.natAbs_mul, padicValNat.mul (p := p) hd0 hg_abs_ne, hvg, add_zero]
    have hY_ne : a + d * g ≠ 0 := by
      intro hY0
      have hva' : ν ≤ padicValNat p (d * g).natAbs := by
        have haeq : a = -(d * g) := by linarith [hY0]
        have e : padicValNat p a.natAbs = padicValNat p (d * g).natAbs := by
          rw [haeq, Int.natAbs_neg]
        rw [e] at hva; exact hva
      omega
    have hlt : padicValNat p (d * g).natAbs < padicValNat p a.natAbs := by
      rw [hvY]; omega
    have hYval : padicValNat p (a + d * g).natAbs = padicValNat p d.natAbs := by
      have h := int_padicVal_add_eq_left (p := p) (x := d * g) (z := a)
        (by rw [add_comm]; exact hY_ne) hdg_ne ha_ne hlt
      have e1 : (d * g) + a = a + (d * g) := add_comm _ _
      rw [e1] at h
      rw [h, hvY]
    have hA_le : A ≤ 2 * padicValNat p d.natAbs := by
      have hY_abs_ne : (a + d * g).natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hY_ne
      have hdY_ne : d * (a + d * g) ≠ 0 := mul_ne_zero hd hY_ne
      have hdvd : (p ^ A : ℕ) ∣ (d * (a + d * g)).natAbs := by
        have h' := (Int.natAbs_dvd_natAbs).mpr hAdvd
        simpa using h'
      have hAle : A ≤ padicValNat p (d * (a + d * g)).natAbs := by
        rcases (padicValNat_dvd_iff (p := p) A (d * (a + d * g)).natAbs).mp hdvd with h | h
        · exact absurd h (by simpa [Int.natAbs_eq_zero] using hdY_ne)
        · exact h
      have hval : padicValNat p (d * (a + d * g)).natAbs = 2 * padicValNat p d.natAbs := by
        rw [Int.natAbs_mul, padicValNat.mul (p := p) hd0 hY_abs_ne, hYval]
        ring
      omega
    omega

theorem clusterStep {p : ℕ} [Fact p.Prime] {Q : Polynomial ℤ} {y y0 : ℤ} {ν A : ℕ}
    (hν : 1 ≤ ν) (hA : 2 * ν + 1 ≤ A)
    (h1 : (((p ^ ν : ℕ) : ℤ)) ∣ Q.derivative.eval y0)
    (h2 : ¬ (((p ^ (ν + 1) : ℕ) : ℤ)) ∣ Q.derivative.eval y0)
    (h3 : ¬ ((p : ℤ) ∣ Q.derivative.derivative.eval y0))
    (hyA : ((p ^ A : ℕ) : ℤ) ∣ Q.eval y)
    (hy0A : ((p ^ A : ℕ) : ℤ) ∣ Q.eval y0)
    (hp : (p : ℤ) ∣ (y - y0)) :
    ((p ^ ν : ℕ) : ℤ) ∣ (y - y0) := by
  by_cases hd : y - y0 = 0
  · rw [hd]; exact dvd_zero _
  · obtain ⟨H, hT, hH⟩ := taylor2_expansion Q y0
    obtain ⟨E, hE⟩ :=
      int_dividedDiff (Polynomial.C 2 * H - Polynomial.C (Q.derivative.derivative.eval y0)) y y0
    have hE' : 2 * H.eval y - Q.derivative.derivative.eval y0 = (y - y0) * E := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hE
      rw [hH] at hE
      linarith
    have hQy := hT y
    have hdiff : Q.eval y - Q.eval y0
        = (y - y0) * (Q.derivative.eval y0 + (y - y0) * H.eval y) := by
      rw [hQy]; ring
    have hAdvd : ((p ^ A : ℕ) : ℤ) ∣
        (y - y0) * (Q.derivative.eval y0 + (y - y0) * H.eval y) := by
      have h0 : ((p ^ A : ℕ) : ℤ) ∣ Q.eval y - Q.eval y0 := dvd_sub hyA hy0A
      rw [hdiff] at h0
      exact h0
    exact clusterStep_aux hν hA hd hp h1 h2 h3 hAdvd hE'

end Work.LinnikBurgess
