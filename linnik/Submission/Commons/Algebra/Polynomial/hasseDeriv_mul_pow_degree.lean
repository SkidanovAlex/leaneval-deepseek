import Mathlib.Algebra.Polynomial.HasseDeriv

namespace Commons.Algebra.Polynomial

/-- For `j ≤ r`, the polynomial `g ^ (r - j)` divides the `j`-th Hasse
derivative of `g ^ r`. -/
lemma pow_dvd_hasseDeriv_pow {R : Type*} [CommRing R] (g : Polynomial R) :
    ∀ r j : ℕ, j ≤ r → g ^ (r - j) ∣ Polynomial.hasseDeriv j (g ^ r) := by
  intro r
  induction r with
  | zero =>
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      simp
  | succ r ih =>
      intro j hj
      rw [show g ^ Nat.succ r = g ^ r * g from pow_succ g r, Polynomial.hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      obtain ⟨a, b⟩ := ij
      by_cases hb : b = 0
      · subst hb
        simp only [add_zero] at hij
        subst a
        simp only [Polynomial.hasseDeriv_zero, LinearMap.id_apply]
        by_cases hjle : j ≤ r
        · obtain ⟨u, hu⟩ := ih j hjle
          refine ⟨u, ?_⟩
          rw [hu]
          rw [show g ^ (Nat.succ r - j) = g ^ (r - j) * g by
                rw [← pow_succ]; congr 1; omega]
          ring
        · have hj' : j = r + 1 := by omega
          subst hj'
          simp
      · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
        have ha : a ≤ r := by omega
        obtain ⟨u, hu⟩ := ih a ha
        refine ⟨g ^ (j - 1 - a) * u * Polynomial.hasseDeriv b g, ?_⟩
        rw [hu]
        rw [show g ^ (r - a) = g ^ (Nat.succ r - j) * g ^ (j - 1 - a) by
              rw [← pow_add]; congr 1; omega]
        ring

/-- `g ^ (r - k)` divides the `k`-th Hasse derivative of `f * g ^ r`. -/
lemma dvd_hasseDeriv_mul_pow {R : Type*} [CommRing R] (f g : Polynomial R) (k r : ℕ)
    (hkr : k ≤ r) : g ^ (r - k) ∣ Polynomial.hasseDeriv k (f * g ^ r) := by
  rw [Polynomial.hasseDeriv_mul]
  apply Finset.dvd_sum
  intro ij hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  obtain ⟨a, b⟩ := ij
  have hb : b ≤ r := by omega
  obtain ⟨u, hu⟩ := pow_dvd_hasseDeriv_pow g r b hb
  have hle : r - k ≤ r - b := by omega
  obtain ⟨v, hv⟩ := pow_dvd_pow g hle
  exact ⟨v * u * Polynomial.hasseDeriv a f, by rw [hu, hv]; ring⟩

theorem hasseDeriv_mul_pow_degree {R : Type*} [CommRing R] [IsDomain R] (f g : Polynomial R) (k r : ℕ) (hkr : k ≤ r) :
    ∃ h : Polynomial R, Polynomial.hasseDeriv k (f * g ^ r) = h * g ^ (r - k) ∧ h.natDegree ≤ f.natDegree + k * g.natDegree - k := by
  rcases eq_or_ne g 0 with rfl | hg
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkr
      subst hk
      exact ⟨f, by simp, by simp⟩
    · refine ⟨0, ?_, by simp⟩
      simp [zero_pow hr.ne']
  · obtain ⟨h, hh⟩ := dvd_hasseDeriv_mul_pow f g k r hkr
    refine ⟨h, ?_, ?_⟩
    · rw [hh, mul_comm]
    · by_cases hh0 : h = 0
      · rw [hh0]; simp
      · have hP : Polynomial.hasseDeriv k (f * g ^ r) ≠ 0 := by
          rw [hh]; exact mul_ne_zero (pow_ne_zero (r - k) hg) hh0
        have hf : f ≠ 0 := by
          rintro rfl; simp at hP
        have hdegP : (Polynomial.hasseDeriv k (f * g ^ r)).natDegree ≤
            (f * g ^ r).natDegree - k := Polynomial.natDegree_hasseDeriv_le _ _
        have hdegF : (f * g ^ r).natDegree = f.natDegree + r * g.natDegree := by
          rw [Polynomial.natDegree_mul hf (pow_ne_zero r hg), Polynomial.natDegree_pow]
        have hQ : (Polynomial.hasseDeriv k (f * g ^ r)).natDegree =
            (r - k) * g.natDegree + h.natDegree := by
          rw [hh, Polynomial.natDegree_mul (pow_ne_zero (r - k) hg) hh0,
            Polynomial.natDegree_pow]
        rw [hdegF] at hdegP
        have hM : (r - k) * g.natDegree = r * g.natDegree - k * g.natDegree :=
          Nat.sub_mul r k g.natDegree
        omega

end Commons.Algebra.Polynomial