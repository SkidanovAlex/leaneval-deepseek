import Mathlib

namespace Work.WilE4.CAD

/-- If a polynomial has nonnegative derivative on `[a, b]`, then it is monotone there. -/
private lemma monotoneOn_eval_of_deriv_nonneg (p : Polynomial ℝ) {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, 0 ≤ p.derivative.eval x) :
    MonotoneOn (fun x => p.eval x) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) p.continuous.continuousOn p.differentiableOn
  intro x hx
  rw [Polynomial.deriv]
  exact h x (interior_subset hx)

/-- If a polynomial has nonpositive derivative on `[a, b]`, then it is antitone there. -/
private lemma antitoneOn_eval_of_deriv_nonpos (p : Polynomial ℝ) {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, p.derivative.eval x ≤ 0) :
    AntitoneOn (fun x => p.eval x) (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) p.continuous.continuousOn p.differentiableOn
  intro x hx
  rw [Polynomial.deriv]
  exact h x (interior_subset hx)

/-- The final step of the induction: a monotone polynomial whose endpoint signs are
prescribed by `v0` keeps those signs throughout the interval. -/
private lemma concl_of_monotone (p : Polynomial ℝ) {a b x : ℝ} {v0 : SignType}
    (hx : x ∈ Set.Icc a b) (hab : a ≤ b)
    (hmono : MonotoneOn (fun y => p.eval y) (Set.Icc a b))
    (ha1 : v0 = 1 → 0 ≤ p.eval a) (hb1 : v0 = -1 → p.eval b ≤ 0)
    (ha0 : v0 = 0 → p.eval a = 0) (hb0 : v0 = 0 → p.eval b = 0) :
    (v0 = 1 → 0 ≤ p.eval x) ∧ (v0 = -1 → p.eval x ≤ 0) ∧ (v0 = 0 → p.eval x = 0) := by
  have hamem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hv; have h1 := hmono hamem hx hx.1; have h2 := ha1 hv; linarith
  · intro hv; have h1 := hmono hx hbmem hx.2; have h2 := hb1 hv; linarith
  · intro hv; have h1 := hmono hamem hx hx.1; have h2 := hmono hx hbmem hx.2
    have h3 := ha0 hv; have h4 := hb0 hv; linarith

/-- The final step of the induction: an antitone polynomial whose endpoint signs are
prescribed by `v0` keeps those signs throughout the interval. -/
private lemma concl_of_antitone (p : Polynomial ℝ) {a b x : ℝ} {v0 : SignType}
    (hx : x ∈ Set.Icc a b) (hab : a ≤ b)
    (hanti : AntitoneOn (fun y => p.eval y) (Set.Icc a b))
    (hb1 : v0 = 1 → 0 ≤ p.eval b) (ha1 : v0 = -1 → p.eval a ≤ 0)
    (ha0 : v0 = 0 → p.eval a = 0) (hb0 : v0 = 0 → p.eval b = 0) :
    (v0 = 1 → 0 ≤ p.eval x) ∧ (v0 = -1 → p.eval x ≤ 0) ∧ (v0 = 0 → p.eval x = 0) := by
  have hamem : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hv; have h1 := hanti hx hbmem hx.2; have h2 := hb1 hv; linarith
  · intro hv; have h1 := hanti hamem hx hx.1; have h2 := ha1 hv; linarith
  · intro hv; have h1 := hanti hx hbmem hx.2; have h2 := hanti hamem hx hx.1
    have h3 := ha0 hv; have h4 := hb0 hv; linarith

theorem derivChain_interval (d : ℕ) (f : ℕ → Polynomial ℝ) (v : ℕ → SignType) {a b : ℝ}
    (hab : a ≤ b)
    (hstep : ∀ s ≤ d, (f s).derivative = f (s + 1)) (hlast : (f d).derivative = 0)
    (ha : ∀ s ≤ d, (v s = 1 → 0 ≤ (f s).eval a) ∧ (v s = -1 → (f s).eval a ≤ 0) ∧
      (v s = 0 → (f s).eval a = 0))
    (hb : ∀ s ≤ d, (v s = 1 → 0 ≤ (f s).eval b) ∧ (v s = -1 → (f s).eval b ≤ 0) ∧
      (v s = 0 → (f s).eval b = 0)) :
    ∀ x ∈ Set.Icc a b, ∀ s ≤ d, (v s = 1 → 0 ≤ (f s).eval x) ∧ (v s = -1 → (f s).eval x ≤ 0) ∧
      (v s = 0 → (f s).eval x = 0) := by
  induction d generalizing f v with
  | zero =>
    intro x hx s hs
    have hs0 : s = 0 := Nat.eq_zero_of_le_zero hs
    subst hs0
    have hconst : (f 0).eval x = (f 0).eval a := by
      rw [Polynomial.eq_C_of_derivative_eq_zero hlast]
      simp
    have ha0 := ha 0 (le_refl 0)
    refine ⟨?_, ?_, ?_⟩
    · intro hv; rw [hconst]; exact ha0.1 hv
    · intro hv; rw [hconst]; exact ha0.2.1 hv
    · intro hv; rw [hconst]; exact ha0.2.2 hv
  | succ d ih =>
    intro x hx s hs
    have hsub := ih (fun t => f (t + 1)) (fun t => v (t + 1))
      (by intro t ht; simpa using hstep (t + 1) (Nat.succ_le_succ ht))
      (by simpa using hlast)
      (by intro t ht; simpa using ha (t + 1) (Nat.succ_le_succ ht))
      (by intro t ht; simpa using hb (t + 1) (Nat.succ_le_succ ht))
    cases s with
    | zero =>
      have key : ∀ y ∈ Set.Icc a b,
          (v (0 + 1) = 1 → 0 ≤ (f (0 + 1)).eval y) ∧
          (v (0 + 1) = -1 → (f (0 + 1)).eval y ≤ 0) ∧
          (v (0 + 1) = 0 → (f (0 + 1)).eval y = 0) :=
        fun y hy => hsub y hy 0 (Nat.zero_le d)
      have ha0 := ha 0 (Nat.zero_le _)
      have hb0 := hb 0 (Nat.zero_le _)
      have hv1cases : v (0 + 1) = SignType.pos ∨ v (0 + 1) = SignType.neg ∨
          v (0 + 1) = SignType.zero := by
        cases h : v (0 + 1) <;> simp
      rcases hv1cases with hpos | hneg | hzero
      · have hv1 : v (0 + 1) = 1 := by rw [hpos, SignType.pos_eq_one]
        have hmono : MonotoneOn (fun y => (f 0).eval y) (Set.Icc a b) :=
          monotoneOn_eval_of_deriv_nonneg (f 0) (by
            intro y hy
            rw [hstep 0 (Nat.zero_le _)]
            exact (key y hy).1 hv1)
        exact concl_of_monotone (f 0) hx hab hmono ha0.1 hb0.2.1 ha0.2.2 hb0.2.2
      · have hv1 : v (0 + 1) = -1 := by rw [hneg, SignType.neg_eq_neg_one]
        have hanti : AntitoneOn (fun y => (f 0).eval y) (Set.Icc a b) :=
          antitoneOn_eval_of_deriv_nonpos (f 0) (by
            intro y hy
            rw [hstep 0 (Nat.zero_le _)]
            exact (key y hy).2.1 hv1)
        exact concl_of_antitone (f 0) hx hab hanti hb0.1 ha0.2.1 ha0.2.2 hb0.2.2
      · have hv1 : v (0 + 1) = 0 := by rw [hzero, SignType.zero_eq_zero]
        have hderiv0 : ∀ y ∈ Set.Icc a b, (f 0).derivative.eval y = 0 := by
          intro y hy
          rw [hstep 0 (Nat.zero_le _)]
          exact (key y hy).2.2 hv1
        have hmono : MonotoneOn (fun y => (f 0).eval y) (Set.Icc a b) :=
          monotoneOn_eval_of_deriv_nonneg (f 0) (fun y hy => by rw [hderiv0 y hy])
        exact concl_of_monotone (f 0) hx hab hmono ha0.1 hb0.2.1 ha0.2.2 hb0.2.2
    | succ s' =>
      have hs' : s' ≤ d := Nat.succ_le_succ_iff.mp hs
      exact hsub x hx s' hs'

end Work.WilE4.CAD
