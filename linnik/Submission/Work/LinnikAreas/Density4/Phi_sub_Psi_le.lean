/-
# The estimate `Φ(s) - Ψ(s) ≤ 9/10`

For the shifted divisor sum estimate one needs the numerical bound
`Φ(s) - Ψ(s) ≤ 9/10` for every finite set `s` of primes, where
`Φ(s) = ∏_{p∈s} (1/p + g(p))`, `Ψ(s) = ∏_{p∈s} g(p)` and `g(p) = (1+p^{-1/2})^{-1}`.

The proof is a strong induction on the cardinality of `s`.  Writing `Q = max s` and
`s' = s \ {Q}` one has the exact identity

  `Φ(s) - Ψ(s) = g(Q) * (Φ(s') - Ψ(s')) + Φ(s') / Q`,

because `f(p) = g(p) + 1/p`.  Since `Φ(s') ≤ 11/10` and, by the induction
hypothesis, `Φ(s') - Ψ(s') ≤ 9/10`, the required estimate reduces to

  `(9/10) * g(Q) + (11/10)/Q ≤ 9/10`,

which is `11(1+√Q) ≤ 9Q` and holds for every `Q ≥ 5`.  The only sets with all
elements `≤ 4` (i.e. subsets of `{2,3}`) are checked by hand.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.ShiftedDefs

namespace Work.LinnikAreas.Density4

noncomputable section

open Finset

/-! ### Elementary properties of the local factors -/

/-- Closed form of the local factor: `g(p) = √p/(√p+1)` for `p ≥ 1`. -/
lemma gR_eq (p : ℕ) (hp : 1 ≤ p) : gR p = Real.sqrt (p : ℝ) / (Real.sqrt (p : ℝ) + 1) := by
  unfold gR
  have h1 : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  rw [eq_div_iff (by positivity)]
  field_simp

lemma gR_nonneg (p : ℕ) : 0 ≤ gR p := by
  unfold gR
  positivity

lemma gR_le_one (p : ℕ) : gR p ≤ 1 := by
  unfold gR
  apply inv_le_one_of_one_le₀
  have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by positivity
  linarith

lemma fR_nonneg (p : ℕ) : 0 ≤ fR p := by
  unfold fR
  exact add_nonneg (by positivity) (gR_nonneg p)

/-- For a prime `p ≥ 3` the local factor `f(p)` is at most `1`. -/
lemma fR_le_one_of_prime (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) : fR p ≤ 1 := by
  unfold fR
  have hg : gR p = 1 - 1 / (Real.sqrt (p : ℝ) + 1) := by
    rw [gR_eq p (by omega)]
    have : (0 : ℝ) < Real.sqrt (p : ℝ) + 1 := by positivity
    field_simp
    ring
  rw [hg]
  have hp' : (0 : ℝ) < (p : ℝ) := by positivity
  have hden : (0 : ℝ) < Real.sqrt (p : ℝ) + 1 := by positivity
  rw [show (1 : ℝ) / (p : ℝ) + (1 - 1 / (Real.sqrt (p : ℝ) + 1)) ≤ 1 ↔
      1 / (p : ℝ) ≤ 1 / (Real.sqrt (p : ℝ) + 1) by
    constructor <;> intro h <;> linarith]
  apply one_div_le_one_div_of_le hden
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have hsq : Real.sqrt (p : ℝ) ≤ (p : ℝ) - 1 := by
    rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)]
    nlinarith
  linarith

/-! ### Numerical bounds at the small primes -/

lemma gR_two_bounds : (58 : ℝ) / 100 ≤ gR 2 ∧ gR 2 ≤ 6 / 10 := by
  constructor
  · rw [gR_eq 2 (by norm_num)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  · rw [gR_eq 2 (by norm_num)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

lemma gR_three_bounds : (63 : ℝ) / 100 ≤ gR 3 ∧ gR 3 ≤ 64 / 100 := by
  constructor
  · rw [gR_eq 3 (by norm_num)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  · rw [gR_eq 3 (by norm_num)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]

lemma fR_two_le : fR 2 ≤ 11 / 10 := by
  unfold fR
  have := gR_two_bounds.2
  linarith

lemma fR_three_le : fR 3 ≤ 98 / 100 := by
  unfold fR
  have := gR_three_bounds.2
  linarith

/-! ### The key arithmetic inequality -/

lemma key_ineq (x : ℝ) (hx : 5 ≤ x) : 11 * (1 + Real.sqrt x) ≤ 9 * x := by
  have hs : Real.sqrt x ≤ x / 2 := by
    rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ x / 2)]
    nlinarith
  nlinarith

lemma step_ineq (Q : ℕ) (hQ : 5 ≤ Q) :
    (9 / 10 : ℝ) * gR Q + (11 / 10) / (Q : ℝ) ≤ 9 / 10 := by
  have hQ1 : 1 ≤ Q := by omega
  have hkey : 11 * (1 + Real.sqrt (Q : ℝ)) ≤ 9 * (Q : ℝ) :=
    key_ineq Q (by exact_mod_cast hQ)
  rw [gR_eq Q hQ1]
  rw [show Real.sqrt (Q : ℝ) / (Real.sqrt (Q : ℝ) + 1) = 1 - 1 / (Real.sqrt (Q : ℝ) + 1) by
    have : (0 : ℝ) < Real.sqrt (Q : ℝ) + 1 := by positivity
    field_simp
    ring]
  have hmain : 11 / (10 * (Q : ℝ)) ≤ (9 / 10) * (1 / (Real.sqrt (Q : ℝ) + 1)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 * (Q : ℝ))]
    rw [show (9 : ℝ) / 10 * (1 / (Real.sqrt (Q : ℝ) + 1)) * (10 * (Q : ℝ)) =
        9 * (Q : ℝ) / (Real.sqrt (Q : ℝ) + 1) by field_simp]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (Q : ℝ) + 1)]
    nlinarith [hkey]
  have e1 : (11 : ℝ) / 10 / (Q : ℝ) = 11 / (10 * (Q : ℝ)) := by ring
  rw [e1]
  linarith [hmain]

/-! ### Nonnegativity of `Φ` and `Ψ`, and the bound `Φ ≤ 11/10` -/

lemma Phi_nonneg (s : Finset ℕ) : 0 ≤ PhiSh s := by
  unfold PhiSh
  exact Finset.prod_nonneg (fun p _ => fR_nonneg p)

lemma Psi_nonneg (s : Finset ℕ) : 0 ≤ Psi s := by
  unfold Psi
  exact Finset.prod_nonneg (fun p _ => gR_nonneg p)

/-- `Φ(t) ≤ 11/10` for every finite set `t` of primes. -/
lemma Phi_le_eleven_tenths (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) : PhiSh t ≤ 11 / 10 := by
  by_cases h2 : 2 ∈ t
  · have hfac : PhiSh t = fR 2 * PhiSh (t.erase 2) := by
      unfold PhiSh
      rw [← Finset.prod_erase_mul t fR h2]
      ring
    rw [hfac]
    have hle1 : PhiSh (t.erase 2) ≤ 1 := by
      unfold PhiSh
      apply Finset.prod_le_one₀
      · intro p _; exact fR_nonneg p
      · intro p hp
        have hpt : p ∈ t := Finset.mem_of_mem_erase hp
        have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
        have hpp : p.Prime := ht p hpt
        have h3 : 3 ≤ p := by have h2' := hpp.two_le; omega
        exact fR_le_one_of_prime p hpp h3
    have hnn : 0 ≤ PhiSh (t.erase 2) := Phi_nonneg _
    calc fR 2 * PhiSh (t.erase 2) ≤ (11 / 10) * 1 := by
          apply mul_le_mul fR_two_le hle1 hnn (by norm_num)
      _ = 11 / 10 := by ring
  · have hle1 : PhiSh t ≤ 1 := by
      unfold PhiSh
      apply Finset.prod_le_one₀
      · intro p _; exact fR_nonneg p
      · intro p hp
        have hpne : p ≠ 2 := fun h => h2 (h ▸ hp)
        have hpp : p.Prime := ht p hp
        have h3 : 3 ≤ p := by have h2' := hpp.two_le; omega
        exact fR_le_one_of_prime p hpp h3
    linarith

/-! ### The main induction -/

theorem Phi_sub_Psi_le (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) :
    PhiSh s - Psi s ≤ 9/10 := by
  classical
  have main : ∀ n, ∀ s : Finset ℕ, s.card = n → (∀ p ∈ s, p.Prime) →
      PhiSh s - Psi s ≤ 9/10 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hcard hpr
      by_cases hmax : ∃ p ∈ s, 5 ≤ p
      · -- main case: the largest element is at least `5`
        obtain ⟨p0, hp0s, hp05⟩ := hmax
        have hne : s.Nonempty := ⟨p0, hp0s⟩
        set Q := s.max' hne with hQdef
        have hQs : Q ∈ s := Finset.max'_mem s hne
        have hQ5 : 5 ≤ Q := le_trans hp05 (Finset.le_max' s p0 hp0s)
        have hpr' : ∀ p ∈ s.erase Q, p.Prime := fun p hpx => hpr p (Finset.mem_of_mem_erase hpx)
        have hcard' : (s.erase Q).card = n - 1 := by
          rw [Finset.card_erase_of_mem hQs, hcard]
        have hcardpos : 0 < n := by
          rw [← hcard]; exact Finset.card_pos.mpr ⟨Q, hQs⟩
        have hlt : (s.erase Q).card < n := by rw [hcard']; omega
        have ihs : PhiSh (s.erase Q) - Psi (s.erase Q) ≤ 9/10 :=
          ih (s.erase Q).card hlt (s.erase Q) rfl hpr'
        have hPhi : PhiSh s = fR Q * PhiSh (s.erase Q) := by
          unfold PhiSh
          rw [← Finset.prod_erase_mul s fR hQs]
          rw [mul_comm]
        have hPsi : Psi s = gR Q * Psi (s.erase Q) := by
          unfold Psi
          rw [← Finset.prod_erase_mul s gR hQs]
          rw [mul_comm]
        have hdec : PhiSh s - Psi s =
            gR Q * (PhiSh (s.erase Q) - Psi (s.erase Q)) + PhiSh (s.erase Q) / (Q : ℝ) := by
          rw [hPhi, hPsi]
          unfold fR
          ring
        calc PhiSh s - Psi s
            = gR Q * (PhiSh (s.erase Q) - Psi (s.erase Q)) + PhiSh (s.erase Q) / (Q : ℝ) := hdec
          _ ≤ gR Q * (9/10) + (11/10) / (Q : ℝ) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left ihs (gR_nonneg Q)
              · apply div_le_div_of_nonneg_right
                · exact Phi_le_eleven_tenths _ hpr'
                · positivity
          _ ≤ 9/10 := by
              rw [mul_comm (gR Q) (9/10)]
              exact step_ineq Q hQ5
      · -- small case: all elements are `≤ 4`, hence `s ⊆ {2,3}`
        have hle4 : ∀ p ∈ s, p ≤ 4 := by
          intro p hps
          by_contra h
          have h5 : 5 ≤ p := by omega
          exact hmax ⟨p, hps, h5⟩
        have hsub : s ⊆ ({2, 3} : Finset ℕ) := by
          intro p hps
          have hpp : p.Prime := hpr p hps
          have h2 : 2 ≤ p := hpp.two_le
          have h4 : p ≤ 4 := hle4 p hps
          interval_cases p
          · simp
          · simp
          · exact absurd hpp (by decide)
        have key : ∀ x ∈ s, x = 2 ∨ x = 3 := by
          intro x hx
          have hx' := hsub hx
          simpa using hx'
        have hs23 : s = ∅ ∨ s = {2} ∨ s = {3} ∨ s = {2, 3} := by
          by_cases h2 : (2 : ℕ) ∈ s
          · by_cases h3 : (3 : ℕ) ∈ s
            · right; right; right
              ext x
              simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor
              · intro hx; exact key x hx
              · rintro (rfl | rfl)
                · exact h2
                · exact h3
            · right; left
              ext x
              simp only [Finset.mem_singleton]
              constructor
              · intro hx
                rcases key x hx with h | h
                · exact h
                · exact absurd (h ▸ hx) h3
              · intro hx; rw [hx]; exact h2
          · by_cases h3 : (3 : ℕ) ∈ s
            · right; right; left
              ext x
              simp only [Finset.mem_singleton]
              constructor
              · intro hx
                rcases key x hx with h | h
                · exact absurd (h ▸ hx) h2
                · exact h
              · intro hx; rw [hx]; exact h3
            · left
              apply Finset.not_nonempty_iff_eq_empty.mp
              rintro ⟨x, hx⟩
              rcases key x hx with h | h
              · exact h2 (h ▸ hx)
              · exact h3 (h ▸ hx)
        rcases hs23 with rfl | rfl | rfl | rfl
        · norm_num [PhiSh, Psi]
        · have h : PhiSh ({2} : Finset ℕ) - Psi ({2} : Finset ℕ) = 1 / 2 := by
            simp [PhiSh, Psi, fR]
          rw [h]; norm_num
        · have h : PhiSh ({3} : Finset ℕ) - Psi ({3} : Finset ℕ) = 1 / 3 := by
            simp [PhiSh, Psi, fR]
          rw [h]; norm_num
        · have h1 : PhiSh ({2, 3} : Finset ℕ) = fR 2 * fR 3 := by simp [PhiSh]
          have h2 : Psi ({2, 3} : Finset ℕ) = gR 2 * gR 3 := by simp [Psi]
          rw [h1, h2]
          have b2 := gR_two_bounds
          have b3 := gR_three_bounds
          nlinarith [fR_two_le, fR_three_le, b2.1, b3.1,
            fR_nonneg 2, fR_nonneg 3, gR_nonneg 2, gR_nonneg 3]
  exact main s.card s rfl hp

end

end Work.LinnikAreas.Density4

