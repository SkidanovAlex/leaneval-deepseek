import Mathlib

namespace Work.WilE4.Ana

open Polynomial

/-- Rolle's theorem for real polynomials: two distinct roots of `p` bound a root of `p.derivative`. -/
lemma rolle_of_two_roots {p : Polynomial ℝ} {a b : ℝ} (hab : a < b) (ha : p.IsRoot a)
    (hb : p.IsRoot b) : ∃ c ∈ Set.Ioo a b, p.derivative.IsRoot c := by
  have h0 : p.eval a = p.eval b := by rw [Polynomial.IsRoot.def] at ha hb; rw [ha, hb]
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_zero hab p.continuousOn h0
  refine ⟨c, hc, ?_⟩
  rw [Polynomial.IsRoot.def, ← p.deriv]
  exact hcd

/-- The intermediate value theorem for a real polynomial: if the signs of the values at two points
differ, then the polynomial has a root in between. -/
lemma exists_root_of_sign_ne {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : SignType.sign (p.eval a) ≠ SignType.sign (p.eval b)) :
    ∃ c ∈ Set.Icc a b, p.IsRoot c := by
  by_cases ha : p.eval a = 0
  · exact ⟨a, ⟨le_rfl, hab⟩, by rw [Polynomial.IsRoot.def, ha]⟩
  by_cases hb : p.eval b = 0
  · exact ⟨b, ⟨hab, le_rfl⟩, by rw [Polynomial.IsRoot.def, hb]⟩
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · have hsb : 0 < p.eval b := by
      have hs : SignType.sign (p.eval b) = 1 := by
        rcases SignType.trichotomy (SignType.sign (p.eval b)) with h' | h' | h'
        · rw [sign_neg hlt, h'] at h; exact absurd rfl h
        · exact absurd (sign_eq_zero_iff.mp h') hb
        · exact h'
      exact sign_eq_one_iff.mp hs
    obtain ⟨c, hc, hce⟩ := (intermediate_value_Icc hab p.continuousOn)
      (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨le_of_lt hlt, le_of_lt hsb⟩)
    exact ⟨c, hc, by rwa [Polynomial.IsRoot.def]⟩
  · have hsb : p.eval b < 0 := by
      have hs : SignType.sign (p.eval b) = -1 := by
        rcases SignType.trichotomy (SignType.sign (p.eval b)) with h' | h' | h'
        · exact h'
        · exact absurd (sign_eq_zero_iff.mp h') hb
        · rw [sign_pos hgt, h'] at h; exact absurd rfl h
      exact sign_eq_neg_one_iff.mp hs
    obtain ⟨c, hc, hce⟩ := (intermediate_value_Icc' hab p.continuousOn)
      (show (0:ℝ) ∈ Set.Icc (p.eval b) (p.eval a) from ⟨le_of_lt hsb, le_of_lt hgt⟩)
    exact ⟨c, hc, by rwa [Polynomial.IsRoot.def]⟩

/-- A nonzero real polynomial with a single, simple root `r` inside `(y, y')` and no other root on
`[y, y']` takes values of opposite signs at `y` and `y'`. -/
lemma sign_ne_of_unique_root {p : Polynomial ℝ} {y y' r : ℝ} (hyy : y < y') (hy : y < r)
    (hry : r < y') (hroot : p.IsRoot r) (hsimp : p.derivative.eval r ≠ 0)
    (huniq : ∀ x ∈ Set.Icc y y', p.IsRoot x → x = r) :
    SignType.sign (p.eval y) ≠ SignType.sign (p.eval y') := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hder : p.derivative.eval r = q.eval r := by
    rw [hq, derivative_mul, derivative_X_sub_C, one_mul]
    simp
  have hqnr : ∀ x ∈ Set.Icc y y', ¬ q.IsRoot x := by
    intro x hx hxq
    have hpix : p.IsRoot x := by
      rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.IsRoot.def.mp hxq, mul_zero]
    have hxr : x = r := huniq x hx hpix
    rw [hxr, Polynomial.IsRoot.def] at hxq
    exact hsimp (by rw [hder]; exact hxq)
  have hqsign : SignType.sign (q.eval y) = SignType.sign (q.eval y') := by
    by_contra hc
    obtain ⟨c, hc_mem, hcroot⟩ := exists_root_of_sign_ne (le_of_lt hyy) hc
    exact hqnr c hc_mem hcroot
  have hsy : SignType.sign (p.eval y) = - SignType.sign (q.eval y) := by
    rw [hq, Polynomial.eval_mul, sign_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [sign_neg (show y - r < 0 by linarith)]
    simp
  have hsy' : SignType.sign (p.eval y') = SignType.sign (q.eval y') := by
    rw [hq, Polynomial.eval_mul, sign_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [sign_pos (show 0 < y' - r by linarith)]
    simp
  intro heq
  have hzero : SignType.sign (q.eval y) = 0 := by
    have h1 : - SignType.sign (q.eval y) = SignType.sign (q.eval y) := by
      rw [← hsy, heq, hsy', hqsign]
    exact SignType.neg_eq_self_iff.mp h1
  exact hqnr y ⟨le_rfl, le_of_lt hyy⟩ (sign_eq_zero_iff.mp hzero)

/-- Two points with the same sign vector for a derivative-closed family of real polynomials have
no root of any member of the family strictly between them. -/
theorem jet_separation (F : List (Polynomial ℝ)) (hne : ∀ P ∈ F, P ≠ 0)
    (hclosed : ∀ P ∈ F, P.derivative = 0 ∨ P.derivative ∈ F) {y y' : ℝ} (hyy : y < y')
    (hsign : ∀ P ∈ F, SignType.sign (P.eval y) = SignType.sign (P.eval y')) :
    ∀ P ∈ F, ∀ r : ℝ, P.IsRoot r → r ≤ y ∨ y' ≤ r := by
  -- Strong (degree-bounded) induction on the degree of the polynomial.
  have main : ∀ n, ∀ P ∈ F, P.natDegree ≤ n → ∀ r : ℝ, P.IsRoot r → r ≤ y ∨ y' ≤ r := by
    intro n
    induction n with
    | zero =>
      intro P hP hdeg r hr
      exfalso
      have hnd : P.natDegree = 0 := Nat.le_zero.mp hdeg
      have hdeg0 : P.degree ≤ 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hnd
      have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg0
      have hz : P.coeff 0 = 0 := by
        rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hr
        exact hr
      exact hne P hP (by rw [hC, hz, Polynomial.C_0])
    | succ n ih =>
      intro P hP hdeg r hr
      by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨hyr, hry⟩ := hcon
      -- The derivative of `P` is a nonzero member of `F`.
      have hnn : P.derivative ≠ 0 := by
        intro h0
        have hC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero h0
        have hz : P.coeff 0 = 0 := by
          rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at hr
          exact hr
        exact hne P hP (by rw [hC, hz, Polynomial.C_0])
      have hPF : P.derivative ∈ F := (hclosed P hP).resolve_left hnn
      have hdeg' : P.derivative.natDegree ≤ n := by
        have := Polynomial.natDegree_derivative_le P
        omega
      -- By the induction hypothesis, `P.derivative` has no root in `(y, y')`.
      have ih' := ih P.derivative hPF hdeg'
      -- Hence `r` is a simple root of `P`.
      have hsimp : P.derivative.eval r ≠ 0 := by
        intro h0
        have hr' : P.derivative.IsRoot r := by rwa [Polynomial.IsRoot.def]
        rcases ih' r hr' with h | h
        · linarith
        · linarith
      -- And `r` is the only root of `P` in `[y, y']`.
      have huniq : ∀ x ∈ Set.Icc y y', P.IsRoot x → x = r := by
        intro x hx hxroot
        by_contra hxr
        rcases lt_or_gt_of_ne hxr with hlt | hgt
        · obtain ⟨c, hc, hcroot⟩ := rolle_of_two_roots hlt hxroot hr
          rcases ih' c hcroot with h | h
          · linarith [hc.1, hx.1, h]
          · linarith [hc.2, hry, h]
        · obtain ⟨c, hc, hcroot⟩ := rolle_of_two_roots hgt hr hxroot
          rcases ih' c hcroot with h | h
          · linarith [hc.1, hyr, h]
          · linarith [hc.2, hx.2, h]
      exact sign_ne_of_unique_root hyy hyr hry hr hsimp huniq (hsign P hP)
  intro P hP r hr
  exact main P.natDegree P hP le_rfl r hr

end Work.WilE4.Ana
