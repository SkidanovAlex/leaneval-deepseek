/-
# Max-monotonicity of the Ionescu--Wainger denominator sets

`iwP ρ l` is the set `P_{≤l}` of admissible denominators at height `2^l` (`Finset.Icc 1 (2^l)` in
the small-height regime, the concrete set `iwPconcrete ρ l` above the threshold `iwC0 ρ`).  The
present file proves

`iwP_pred_le : (∀ q ∈ iwP ρ l, q ≤ Q) → ∀ q ∈ iwP ρ (l-1), q ≤ Q`,

the *numerical* monotonicity of the maximal denominator from level `l` to level `l - 1`.  The naive
proof through the set inclusion `iwP ρ (l-1) ⊆ iwP ρ l` is false in general: for `ρ = 0` one has
`iwC0 0 = 100` and `iwP 0 100 = Finset.Icc 1 (2^100) ∋ 4`, whereas `iwP 0 101 = iwPconcrete 0 101`
does not contain `4`.  The three regimes are:

* `l ≤ iwC0 ρ`: both sets are `Finset.Icc 1 (2 ^ ·)`;
* `iwC0 ρ < l - 1`: `iwPconcrete_mono` gives the inclusion;
* `l = iwC0 ρ + 1`: the boundary case, where it suffices to exhibit an element of
  `iwPconcrete ρ (iwC0 ρ + 1)` which is at least `2 ^ iwC0 ρ` (`exists_mem_iwP_ge` below).
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwPconcrete_contains_range

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-! ## Elementary arithmetic -/

lemma hundred_le_iwC0 (ρ : ℝ) : 100 ≤ iwC0 ρ := by
  rw [iwC0]
  omega

/-- `n + 1 ≤ 2 ^ (n / 2)` for `n ≥ 6`. -/
lemma succ_le_two_pow_div_two {n : ℕ} (hn : 6 ≤ n) : n + 1 ≤ 2 ^ (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num
    · have h2 : 6 ≤ n - 2 := by omega
      have hrec := ih (n - 2) (by omega) h2
      have hdiv : (n - 2) / 2 + 1 = n / 2 := by omega
      have hpow : 2 ^ (n / 2) = 2 * 2 ^ ((n - 2) / 2) := by
        rw [← hdiv, pow_succ]; ring
      have hrec' : n - 1 ≤ 2 ^ ((n - 2) / 2) := by omega
      calc n + 1 ≤ 2 * (n - 1) := by omega
        _ ≤ 2 * 2 ^ ((n - 2) / 2) := by omega
        _ = 2 ^ (n / 2) := hpow.symm

/-- `iwC0 ρ = 100` for `ρ ≤ 0`. -/
lemma iwC0_eq_hundred_of_nonpos {ρ : ℝ} (hρ : ρ ≤ 0) : iwC0 ρ = 100 := by
  rw [iwC0]
  have hD : (0 : ℝ) ≤ (iwD ρ : ℝ) := Nat.cast_nonneg _
  have heps : iwEps ρ ≤ -1 := by
    rw [iwEps]
    nlinarith [hρ, hD]
  have hnum : (1 + iwEps ρ) ≤ 0 := by linarith
  have hden : iwEps ρ ≤ 0 := by linarith
  have hratio : (0 : ℝ) ≤ (1 + iwEps ρ) / iwEps ρ := by
    rw [← neg_div_neg_eq]
    exact div_nonneg (by linarith) (by linarith)
  have h1 : ⌈(2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)⌉₊ = 0 := by
    rw [Nat.ceil_eq_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_iff.mpr (Or.inl ⟨by norm_num, hρ⟩)) hratio
  have h2 : ⌈10 / ρ⌉₊ = 0 := by
    rw [Nat.ceil_eq_zero]
    exact div_nonpos_iff.mpr (Or.inl ⟨by norm_num, hρ⟩)
  rw [h1, h2]

/-- `iwN0 ρ l ≤ 2` for `ρ ≤ 0` and `l ≥ 1`. -/
lemma iwN0_le_two_of_nonpos {ρ : ℝ} (hρ : ρ ≤ 0) {l : ℕ} (hl : 1 ≤ l) : iwN0 ρ l ≤ 2 := by
  rcases eq_or_lt_of_le hρ with h0 | hneg
  · rw [h0, iwN0]
    norm_num
  · have hlt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
      have hl' : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
      nlinarith
    rw [iwN0, Nat.floor_eq_zero.mpr hlt]
    norm_num

/-! ## An element of `iwP ρ (iwC0 ρ + 1)` above `2 ^ iwC0 ρ` -/

/-- **The boundary element.**  In the critical case `l = iwC0 ρ + 1` the lower level `l - 1` has
admissible denominators `Finset.Icc 1 (2 ^ iwC0 ρ)`, while the upper level is the concrete set.  The
element exhibited here (of the upper level) is at least `2 ^ iwC0 ρ`. -/
lemma exists_mem_iwP_ge (ρ : ℝ) :
    ∃ q ∈ iwP ρ (iwC0 ρ + 1), 2 ^ iwC0 ρ ≤ q := by
  have hC := hundred_le_iwC0 ρ
  by_cases hρ : ρ ≤ 0
  · -- `ρ ≤ 0`: a Bertrand prime in `(2 ^ 100, 2 ^ 101]`
    have hC100 : iwC0 ρ = 100 := iwC0_eq_hundred_of_nonpos hρ
    obtain ⟨p, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ 100) (by positivity)
    have hle101 : p ≤ 2 ^ (iwC0 ρ + 1) := by
      rw [hC100, pow_succ]
      omega
    refine ⟨p, ?_, by rw [hC100]; omega⟩
    rw [mem_iwP]
    refine Or.inr ⟨by rw [hC100]; norm_num, ?_⟩
    rw [mem_iwPconcrete]
    refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero _ _⟩, p, ?_, (one_mul p).symm⟩
    rw [mem_iwW]
    refine ⟨?_, ?_⟩
    · rw [iwProd]
      have hmem : p ∈ iwPrimeRange ρ (iwC0 ρ + 1) := by
        rw [iwPrimeRange, Finset.mem_filter, Finset.mem_Icc]
        have hN0 : iwN0 ρ (iwC0 ρ + 1) ≤ 2 := by
          rw [hC100]
          exact iwN0_le_two_of_nonpos hρ (l := 101) (by norm_num)
        refine ⟨⟨by omega, ?_⟩, hp⟩
        rw [hC100, pow_succ]
        omega
      have hD : 1 ≤ iwD ρ := by unfold iwD; omega
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => i ^ iwD ρ) hmem)
      simpa using pow_dvd_pow p hD
    · rw [hp.factorization]
      have hcard : (Finsupp.single p (1 : ℕ)).support.card = 1 := by
        rw [Finsupp.support_single_ne_zero p (by norm_num)]
        simp
      rw [hcard]
      have hD : 1 ≤ iwD ρ := by unfold iwD; omega
      exact hD
  · have hρpos : 0 < ρ := not_le.mp hρ
    by_cases hρ1 : ρ ≤ 1
    · -- `0 < ρ ≤ 1`: the element `2 ^ (iwC0 ρ + 1)`
      refine ⟨2 ^ (iwC0 ρ + 1), ?_, Nat.pow_le_pow_right (by norm_num) (by omega)⟩
      rw [mem_iwP]
      exact Or.inr ⟨by omega,
        iwPconcrete_contains_range hρpos hρ1 (Nat.le_succ _) (Nat.one_le_pow _ 2 (by norm_num))
          (le_refl _)⟩
    · -- `1 < ρ`: the element `(iwN0 ρ (iwC0 ρ + 1)).factorial ^ iwD ρ`
      have hρ1' : 1 < ρ := not_le.mp hρ1
      refine ⟨(iwN0 ρ (iwC0 ρ + 1)).factorial ^ iwD ρ, ?_, ?_⟩
      · rw [mem_iwP]
        refine Or.inr ⟨by omega, ?_⟩
        rw [mem_iwPconcrete]
        exact ⟨iwQ0 ρ (iwC0 ρ + 1), Nat.mem_divisors.mpr ⟨dvd_rfl, iwQ0_ne_zero _ _⟩,
          1, one_mem_iwW _ _, by rw [mul_one, iwQ0]⟩
      · have hD : 1 ≤ iwD ρ := by rw [iwD]; omega
        have hC6 : 6 ≤ iwC0 ρ := by omega
        -- `2 ^ ((iwC0 ρ + 1) / 2) ≤ iwN0 ρ (iwC0 ρ + 1)`
        have hstep : 2 ^ ((iwC0 ρ + 1) / 2) ≤ iwN0 ρ (iwC0 ρ + 1) := by
          have hx : ((2 ^ ((iwC0 ρ + 1) / 2) : ℕ) : ℝ)
              ≤ (2 : ℝ) ^ (ρ * ((iwC0 ρ : ℝ) + 1) / 2) := by
            rw [show ((2 ^ ((iwC0 ρ + 1) / 2) : ℕ) : ℝ)
                = (2 : ℝ) ^ (((iwC0 ρ + 1) / 2 : ℕ) : ℝ) by
              push_cast
              rw [Real.rpow_natCast]]
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            have hcast : (((iwC0 ρ + 1 : ℕ)) : ℝ) = (iwC0 ρ : ℝ) + 1 := by push_cast; ring
            have hdiv := Nat.cast_div_le (α := ℝ) (m := iwC0 ρ + 1) (n := 2)
            rw [hcast] at hdiv
            nlinarith [hρ1'.le, hdiv]
          have hy : (2 : ℝ) ^ (ρ * ((iwC0 ρ : ℝ) + 1) / 2) < (iwN0 ρ (iwC0 ρ + 1) : ℝ) := by
            rw [iwN0]
            push_cast
            exact Nat.lt_floor_add_one _
          exact_mod_cast le_of_lt (lt_of_le_of_lt hx hy)
        have hnat : iwC0 ρ + 1 ≤ 2 ^ ((iwC0 ρ + 1) / 2) := by
          have h1 := succ_le_two_pow_div_two hC6
          exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hN0 : iwC0 ρ + 1 ≤ iwN0 ρ (iwC0 ρ + 1) := le_trans hnat hstep
        have hfac : 2 ^ (iwC0 ρ) ≤ (iwN0 ρ (iwC0 ρ + 1)).factorial := by
          have h1 : iwC0 ρ ≤ iwN0 ρ (iwC0 ρ + 1) - 1 := by omega
          refine le_trans (Nat.pow_le_pow_right (by norm_num) h1) ?_
          have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := iwN0 ρ (iwC0 ρ + 1) - 1)
          rw [Nat.factorial_one, one_mul] at h
          have h2 : 1 + (iwN0 ρ (iwC0 ρ + 1) - 1) = iwN0 ρ (iwC0 ρ + 1) := by omega
          rwa [h2] at h
        calc 2 ^ (iwC0 ρ) ≤ (iwN0 ρ (iwC0 ρ + 1)).factorial := hfac
          _ ≤ (iwN0 ρ (iwC0 ρ + 1)).factorial ^ iwD ρ := by
              calc (iwN0 ρ (iwC0 ρ + 1)).factorial = (iwN0 ρ (iwC0 ρ + 1)).factorial ^ 1 := (pow_one _).symm
                _ ≤ _ := Nat.pow_le_pow_right (Nat.factorial_pos _) hD

/-- **Max-monotonicity of the Ionescu--Wainger denominator sets.** -/
theorem iwP_pred_le (ρ : ℝ) (l Q : ℕ)
    (hQ : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q ≤ Q) :
    ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ (l - 1), q ≤ Q := by
  intro q hq
  by_cases hl : l ≤ iwC0 ρ
  · have hQl : 2 ^ l ≤ Q := hQ _ (by rw [mem_iwP]; exact Or.inl ⟨hl, Nat.one_le_pow l 2 (by norm_num), le_rfl⟩)
    rw [mem_iwP] at hq
    rcases hq with ⟨-, -, h2⟩ | ⟨hcon, -⟩
    · calc q ≤ 2 ^ (l - 1) := h2
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le l 1)
        _ ≤ Q := hQl
    · omega
  · rw [not_le] at hl
    by_cases hl2 : l - 1 ≤ iwC0 ρ
    · -- boundary case `l = iwC0 ρ + 1`
      have hl_eq : l = iwC0 ρ + 1 := by omega
      have hle : l - 1 = iwC0 ρ := by omega
      rw [mem_iwP] at hq
      have hq2 : q ≤ 2 ^ (iwC0 ρ) := by
        rcases hq with ⟨-, -, h2⟩ | ⟨hcon, -⟩
        · rwa [hle] at h2
        · omega
      obtain ⟨q', hq'mem, hq'ge⟩ := exists_mem_iwP_ge ρ
      have hq'mem' : q' ∈ iwP ρ l := by rw [hl_eq]; exact hq'mem
      calc q ≤ 2 ^ (iwC0 ρ) := hq2
        _ ≤ q' := hq'ge
        _ ≤ Q := hQ q' hq'mem'
    · rw [not_le] at hl2
      have hq' : q ∈ iwPconcrete ρ (l - 1) := by
        rw [mem_iwP] at hq
        rcases hq with ⟨h, -⟩ | ⟨-, h⟩
        · omega
        · exact h
      have hmem : q ∈ iwP ρ l := by
        rw [mem_iwP]
        exact Or.inr ⟨hl, iwPconcrete_mono (Nat.sub_le l 1) hq'⟩
      exact hQ q hmem

end Work.KMTPlan.A6
