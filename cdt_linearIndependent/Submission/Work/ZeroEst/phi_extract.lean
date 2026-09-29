import Mathlib
import Submission.Work.ZeroEst.defs

/-!
# `Work.ZeroEst.phi_extract`

Coefficient extraction for a polynomial times a product of one-variable series, as used in the
multivariate Shidlovsky reduction (`Submission.CDTPlan.auxSeries`).

Writing `embedVar s (g s)` for `g s` viewed as a series in the single variable `x_s`, the theorem
computes the coefficient of `x^{(n.update j t)}` in
`(P : MvPowerSeries (Fin d) ℚ) * ∏ s, embedVar s (g s)`
by the coefficient of `x_j^t` in the natural one-variable polynomial `Q` (whose monomial
coefficients record the contributions in the other variables) multiplied by `g j`.

The proof splits into the expansion of the left-hand side (`phi_lhs`) and of the right-hand side
(`phi_rhs_expand`); both equal the same explicit sum over `P.support`.
-/

namespace Work.ZeroEst

private lemma coeff_embedVar {d : ℕ} (a : Fin d) (f : PowerSeries ℚ) (e : Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (Submission.CDTPlan.embedVar a f) =
      if e = Finsupp.single a (e a) then PowerSeries.coeff (e a) f else 0 := rfl

private lemma prod_coeff_embedVar {d : ℕ} (g : Fin d → PowerSeries ℚ)
    (l : Fin d →₀ (Fin d →₀ ℕ)) :
    (∏ i, MvPowerSeries.coeff (l i) (Submission.CDTPlan.embedVar i (g i)))
      = if (∀ i, l i = Finsupp.single i ((l i) i)) then
          ∏ i, PowerSeries.coeff ((l i) i) (g i) else 0 := by
  simp only [coeff_embedVar]
  rw [Finset.prod_ite_zero]
  simp

/-- Coefficient of a product of one-variable series: `∏ s, embedVar s (g s)` has coefficients
`∏ s, (g s).coeff (e s)`. -/
theorem phi_coeffProd {d : ℕ} (g : Fin d → PowerSeries ℚ) (e : Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (∏ s, Submission.CDTPlan.embedVar s (g s)) =
      ∏ s, PowerSeries.coeff (e s) (g s) := by
  classical
  set l₀ : Fin d →₀ (Fin d →₀ ℕ) := Finsupp.equivFunOnFinite.symm (fun s => Finsupp.single s (e s))
  have hl₀ : ∀ s, l₀ s = Finsupp.single s (e s) :=
    fun s => Finsupp.equivFunOnFinite_symm_apply_apply _ s
  have hmem : l₀ ∈ Finset.univ.finsuppAntidiag e := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    apply Finsupp.ext
    intro t
    rw [Finsupp.finsetSum_apply]
    simp only [hl₀, Finsupp.single_apply]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ t)]
  have hdiag_l₀ : ∀ i, l₀ i = Finsupp.single i ((l₀ i) i) := by
    intro i; rw [hl₀ i, Finsupp.single_eq_same]
  have key : ∀ b ∈ Finset.univ.finsuppAntidiag e, b ≠ l₀ →
      (if (∀ i, b i = Finsupp.single i ((b i) i)) then
          ∏ i, PowerSeries.coeff ((b i) i) (g i) else 0) = 0 := by
    intro b hb hne
    rw [if_neg]
    intro hdiag
    apply hne
    apply Finsupp.ext
    intro t
    have hb' := (Finset.mem_finsuppAntidiag.mp hb).1
    have ht : (∑ i ∈ Finset.univ, (b i) t) = e t := by
      rw [← hb', Finsupp.finsetSum_apply]
    have ht2 : (∑ i ∈ Finset.univ, (if i = t then (b i) i else 0)) = e t := by
      rw [← ht]
      exact Finset.sum_congr rfl (fun i _ => by
        conv_rhs => rw [hdiag i]
        rw [Finsupp.single_apply])
    have ht3 : (b t) t = e t := by
      rw [← ht2, Finset.sum_ite_eq', if_pos (Finset.mem_univ t)]
    rw [hdiag t, ht3, hl₀ t]
  calc MvPowerSeries.coeff e (∏ s, Submission.CDTPlan.embedVar s (g s))
      = ∑ l ∈ Finset.univ.finsuppAntidiag e,
          (if (∀ i, l i = Finsupp.single i ((l i) i)) then
            ∏ i, PowerSeries.coeff ((l i) i) (g i) else 0) := by
        rw [MvPowerSeries.coeff_prod]
        exact Finset.sum_congr rfl (fun l _ => prod_coeff_embedVar g l)
    _ = (if (∀ i, l₀ i = Finsupp.single i ((l₀ i) i)) then
            ∏ i, PowerSeries.coeff ((l₀ i) i) (g i) else 0) :=
        Finset.sum_eq_single l₀ key (fun h => absurd hmem h)
    _ = ∏ s, PowerSeries.coeff (e s) (g s) := by
        rw [if_pos hdiag_l₀]
        exact Finset.prod_congr rfl (fun i _ => by rw [hl₀ i, Finsupp.single_eq_same])

private lemma coe_as_sum {d : ℕ} (P : MvPolynomial (Fin d) ℚ) :
    (P : MvPowerSeries (Fin d) ℚ) = ∑ c ∈ P.support, MvPowerSeries.monomial c (P.coeff c) := by
  ext e
  rw [MvPolynomial.coeff_coe, map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact MvPolynomial.notMem_support_iff.mp h

private lemma update_le_iff {d : ℕ} (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) (c : Fin d →₀ ℕ) :
    c ≤ n.update j t ↔ (∀ s, s ≠ j → c s ≤ n s) ∧ c j ≤ t := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    refine ⟨fun s hs => ?_, ?_⟩
    · have := h s; rw [Finsupp.update_apply, if_neg hs] at this; exact this
    · have := h j; simpa using this
  · rintro ⟨h1, h2⟩ i
    rw [Finsupp.update_apply]
    by_cases hi : i = j
    · subst hi; simpa using h2
    · rw [if_neg hi]; exact h1 i hi

/-- Left-hand side of `phi_extract`: the coefficient at `n.update j t` of
`P * ∏ s, embedVar s (g s)` written as a sum over `P.support`. -/
theorem phi_lhs {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (g : Fin d → PowerSeries ℚ)
    (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) :
    MvPowerSeries.coeff (n.update j t)
        ((P : MvPowerSeries (Fin d) ℚ) * ∏ s, Submission.CDTPlan.embedVar s (g s)) =
      ∑ c ∈ P.support,
        if (∀ s, s ≠ j → c s ≤ n s) ∧ c j ≤ t then
          P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s)) *
            PowerSeries.coeff (t - c j) (g j)
        else 0 := by
  classical
  rw [coe_as_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [MvPowerSeries.coeff_monomial_mul, phi_coeffProd]
  by_cases h : c ≤ n.update j t
  · rw [if_pos h]
    rw [if_pos (update_le_iff n j t c |>.mp h)]
    have hE : (∏ x ∈ Finset.univ.erase j, PowerSeries.coeff ((n.update j t - c) x) (g x))
        = ∏ x ∈ Finset.univ.erase j, PowerSeries.coeff (n x - c x) (g x) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [Finsupp.tsub_apply, Finsupp.update_apply, if_neg (Finset.mem_erase.mp hx).1]
    have hF : PowerSeries.coeff ((n.update j t - c) j) (g j)
        = PowerSeries.coeff (t - c j) (g j) := by
      rw [Finsupp.tsub_apply, Finsupp.update_apply, if_pos rfl]
    rw [← Finset.prod_erase_mul Finset.univ
        (fun s => PowerSeries.coeff ((n.update j t - c) s) (g s)) (Finset.mem_univ j),
      hE, hF, mul_assoc]
  · rw [if_neg h]
    rw [if_neg (fun hh => h ((update_le_iff n j t c).mpr hh))]

private lemma antidiag_sum (k t : ℕ) (a : ℚ) (h : ℕ → ℚ) :
    (∑ i ∈ Finset.HasAntidiagonal.antidiagonal t, (if i.1 = k then a * h i.2 else 0))
      = if k ≤ t then a * h (t - k) else 0 := by
  by_cases hk : k ≤ t
  · rw [if_pos hk, Finset.sum_eq_single (k, t - k)]
    · simp
    · intro b hb hne
      rw [if_neg]
      intro hbk
      exact hne (by
        have h1 : b.1 + b.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
        ext <;> omega)
    · intro hmem
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)) hmem
  · rw [if_neg hk, Finset.sum_eq_zero]
    intro b hb
    rw [if_neg]
    intro hbk
    have h1 : b.1 + b.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    omega

/-- Right-hand side of `phi_extract`: coefficient extraction in the variable `j`. -/
theorem phi_rhs_expand {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (g : Fin d → PowerSeries ℚ)
    (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) :
    PowerSeries.coeff t
        (((∑ c ∈ P.support,
            if ∀ s, s ≠ j → c s ≤ n s then
              Polynomial.monomial (c j)
                (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
            else 0 : Polynomial ℚ) : PowerSeries ℚ) * g j) =
      ∑ c ∈ P.support,
        if (∀ s, s ≠ j → c s ≤ n s) ∧ c j ≤ t then
          P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s)) *
            PowerSeries.coeff (t - c j) (g j)
        else 0 := by
  classical
  rw [PowerSeries.coeff_mul]
  have hcoeff : ∀ m : ℕ,
      PowerSeries.coeff m
        (((∑ c ∈ P.support,
            if ∀ s, s ≠ j → c s ≤ n s then
              Polynomial.monomial (c j)
                (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
            else 0 : Polynomial ℚ)) : PowerSeries ℚ)
      = ∑ c ∈ P.support,
          if (∀ s, s ≠ j → c s ≤ n s) then
            (if c j = m then
              P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
            else 0)
          else 0 := by
    intro m
    rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : (∀ s, s ≠ j → c s ≤ n s)
    · rw [if_pos hc, if_pos hc, Polynomial.coeff_monomial]
    · rw [if_neg hc, if_neg hc]
      simp
  simp only [hcoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (∀ s, s ≠ j → c s ≤ n s)
  · have key : (∑ i ∈ Finset.HasAntidiagonal.antidiagonal t,
        (if (∀ s, s ≠ j → c s ≤ n s) then
          (if c j = i.1 then
            P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
          else 0) else 0)
        * PowerSeries.coeff i.2 (g j))
        = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal t,
            (if i.1 = c j then
              (P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s)))
              * PowerSeries.coeff i.2 (g j) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_pos hc]
      by_cases hij : i.1 = c j
      · rw [if_pos hij.symm, if_pos hij]
      · rw [if_neg (fun hh => hij hh.symm), zero_mul, if_neg hij]
    rw [key, antidiag_sum (c j) t
        (P.coeff c * (∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s)))
        (fun m => PowerSeries.coeff m (g j))]
    by_cases hk : c j ≤ t
    · rw [if_pos hk, if_pos ⟨hc, hk⟩]
    · rw [if_neg hk, if_neg (fun hh => hk hh.2)]
  · rw [if_neg (fun hh => hc hh.1), Finset.sum_eq_zero]
    intro i _
    rw [if_neg hc, zero_mul]

theorem phi_extract {d : ℕ} (P : MvPolynomial (Fin d) ℚ) (g : Fin d → PowerSeries ℚ)
    (n : Fin d →₀ ℕ) (j : Fin d) (t : ℕ) :
    MvPowerSeries.coeff (n.update j t)
        ((P : MvPowerSeries (Fin d) ℚ) * ∏ s, Submission.CDTPlan.embedVar s (g s)) =
      PowerSeries.coeff t
        (((∑ c ∈ P.support,
            if ∀ s, s ≠ j → c s ≤ n s then
              Polynomial.monomial (c j)
                (P.coeff c * ∏ s ∈ Finset.univ.erase j, PowerSeries.coeff (n s - c s) (g s))
            else 0 : Polynomial ℚ) : PowerSeries ℚ) * g j) := by
  rw [phi_lhs, phi_rhs_expand]

end Work.ZeroEst
