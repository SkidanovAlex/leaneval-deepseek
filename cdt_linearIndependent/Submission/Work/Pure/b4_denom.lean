import Mathlib
import Submission.Work.Pure.interfaces
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.b4_rel
import Submission.Work.Pure.b4_PF_facts
import Submission.Work.Pure.b4_theta_bridge
import Submission.CDT.SympDescent
import Submission.CDT.SympExplicitodeBridge

/-!
# Denominator type of the pure function `B₄` (CDT, arXiv:2408.15403)

`Work.Pure.b4_denom : HasDenomType 0 ![2,2] B4`.

`B₄` is defined by the paper's double sum (see `Submission.CDTPlan.B4`); the proof shows

* `B₄` and `Work.Pure.b4F = Σ_k k⁻²(P_{k+1} - y·P_{k-1})` both satisfy the paper's equation
  `x(4-x)B₄' = (2-x)B₄ + (4-x)B₂ - 2x(4-x)` (`Work.Pure.b4_rel` for `B₄`, `b4F_ode` below for
  `b4F`, using the x-side bridge `Work.Pure.b4_theta_bridge`), and that this equation determines
  the coefficients from the constant term (`eq_of_ode`), whence `B₄ = b4F`;
* `b4F.subst sympY = b4Theta` and the `P`-polynomials have integral coefficients with
  valuation `⌊k/2⌋+1` (`Work.Pure.b4_PF_facts`), so
  `[xⁿ]B₄ = Σ_{k ≤ 2n} k⁻²·(integer)`, and `[1..2n]²` clears the denominators.
-/

namespace Work.Pure

open PowerSeries
open Submission.CDT
open Submission.CDTPlan
open scoped BigOperators

noncomputable section

/-! ## coefficient helpers -/

private lemma coeff_X_mul_ser (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (X * f) = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 n

private lemma coeff_XD (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (X * PowerSeries.derivative (R := ℚ) f) = (n : ℚ) * PowerSeries.coeff n f := by
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

private lemma coeff_XsqD (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (X ^ 2 * PowerSeries.derivative (R := ℚ) f)
      = ((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) f := by
  have h : (X : PowerSeries ℚ) ^ 2 * PowerSeries.derivative (R := ℚ) f
      = X * (X * PowerSeries.derivative (R := ℚ) f) := by ring
  rw [h]
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_XD]; simp only [Nat.add_sub_cancel]

private lemma coeff_four_sub_X_mul (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n ((4 - X : PowerSeries ℚ) * f)
      = 4 * PowerSeries.coeff n f - (if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0) := by
  have h : (4 - X : PowerSeries ℚ) * f
      = (4 : PowerSeries ℚ) * f - X * f := by ring
  rw [h, map_sub, show (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) from rfl,
    PowerSeries.coeff_C_mul, coeff_X_mul_ser]

private lemma coeff_two_sub_X_mul (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n ((2 - X : PowerSeries ℚ) * f)
      = 2 * PowerSeries.coeff n f - (if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0) := by
  have h : (2 - X : PowerSeries ℚ) * f
      = (2 : PowerSeries ℚ) * f - X * f := by ring
  rw [h, map_sub, show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl,
    PowerSeries.coeff_C_mul, coeff_X_mul_ser]

private lemma coeff_XDsq (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (X * (4 - X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) f)
      = 4 * ((n : ℚ) * PowerSeries.coeff n f)
        - ((n - 1 : ℕ) : ℚ) * PowerSeries.coeff (n - 1) f := by
  have h : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) f
      = (4 : PowerSeries ℚ) * (X * PowerSeries.derivative (R := ℚ) f)
        - X ^ 2 * PowerSeries.derivative (R := ℚ) f := by ring
  rw [h, map_sub, show (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) from rfl,
    PowerSeries.coeff_C_mul, coeff_XD, coeff_XsqD]

private lemma b4d_subst_two : PowerSeries.subst sympY (2 : PowerSeries ℚ) = 2 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, PowerSeries.subst_C]
  rfl

private lemma b4d_subst_four : PowerSeries.subst sympY (4 : PowerSeries ℚ) = 4 := by
  rw [show (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) from rfl, PowerSeries.subst_C]
  rfl

/-! ## `b4F` satisfies the same ODE as `B4` -/

private lemma b4F_ode (hF : b4F.subst sympY = b4Theta)
    (hTheta : sympY * (4 - sympY) * PowerSeries.derivative (R := ℚ) b4Theta
      = (PowerSeries.derivative (R := ℚ) sympY)
        * ((2 - sympY) * b4Theta + (4 - sympY) * (Submission.CDTPlan.B2.subst sympY)
            - 2 * sympY * (4 - sympY))) :
    (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) b4F
      = (2 - X) * b4F + (4 - X) * Submission.CDTPlan.B2 - 2 * X * (4 - X) := by
  set Z : PowerSeries ℚ := (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) b4F
      - ((2 - X) * b4F + (4 - X) * Submission.CDTPlan.B2 - 2 * X * (4 - X)) with hZdef
  have hsubst : Z.subst sympY
      = sympY * (4 - sympY) * (PowerSeries.derivative (R := ℚ) b4F).subst sympY
        - ((2 - sympY) * (b4F.subst sympY) + (4 - sympY) * (Submission.CDTPlan.B2.subst sympY)
            - 2 * sympY * (4 - sympY)) := by
    rw [hZdef]
    simp only [subst_sub sympY_hasSubst, subst_add sympY_hasSubst, subst_mul sympY_hasSubst,
      subst_X sympY_hasSubst, b4d_subst_two, b4d_subst_four]
  have hkey : (PowerSeries.derivative (R := ℚ) sympY) * Z.subst sympY = 0 := by
    have h1 : (PowerSeries.derivative (R := ℚ) sympY) * (PowerSeries.derivative (R := ℚ) b4F).subst sympY
        = PowerSeries.derivative (R := ℚ) b4Theta := by
      rw [mul_comm, ← PowerSeries.derivative_subst (R := ℚ) (f := b4F) sympY_hasSubst, hF]
    rw [hsubst, hF]
    have h2 : (PowerSeries.derivative (R := ℚ) sympY)
          * (sympY * (4 - sympY) * (PowerSeries.derivative (R := ℚ) b4F).subst sympY
              - ((2 - sympY) * b4Theta + (4 - sympY) * (Submission.CDTPlan.B2.subst sympY)
                  - 2 * sympY * (4 - sympY)))
        = sympY * (4 - sympY) * ((PowerSeries.derivative (R := ℚ) sympY)
              * (PowerSeries.derivative (R := ℚ) b4F).subst sympY)
          - (PowerSeries.derivative (R := ℚ) sympY)
            * ((2 - sympY) * b4Theta + (4 - sympY) * (Submission.CDTPlan.B2.subst sympY)
                - 2 * sympY * (4 - sympY)) := by ring
    rw [h2, h1]
    linear_combination hTheta
  have hZ : Z.subst sympY = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (by simpa [Yp] using Yp_ne_zero)
    · exact h
  have hZ0 : Z = 0 := symp_subst_y_injective Z hZ
  rw [hZdef] at hZ0
  linear_combination hZ0

/-! ## the ODE determines the series -/

private lemma hom_rec {w : PowerSeries ℚ}
    (hw : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) w = (2 - X) * w) :
    ∀ n : ℕ, (4 * (n : ℚ) - 2) * PowerSeries.coeff n w
      = ((n : ℚ) - 2) * PowerSeries.coeff (n - 1) w := by
  intro n
  by_cases hn : 1 ≤ n
  · have h := congrArg (PowerSeries.coeff n) hw
    rw [coeff_XDsq, coeff_two_sub_X_mul, if_pos hn] at h
    have hsub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub hn]; norm_num
    rw [hsub] at h
    linear_combination h
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [Nat.cast_zero, mul_zero, Nat.reduceSub]

private lemma hom_eq_zero {w : PowerSeries ℚ}
    (hw : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) w = (2 - X) * w) : w = 0 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h0 := congrArg (PowerSeries.coeff 0) hw
      simp only [coeff_XDsq, coeff_two_sub_X_mul] at h0
      simp at h0
      simpa using h0
    · have hrec := hom_rec hw n
      have hne : (4 * (n : ℚ) - 2) ≠ 0 := by
        have : (1 : ℚ) ≤ n := by exact_mod_cast h
        nlinarith
      rw [ih (n - 1) (by omega),
        show PowerSeries.coeff (n - 1) (0 : PowerSeries ℚ) = 0 from by simp, mul_zero] at hrec
      rw [show PowerSeries.coeff n (0 : PowerSeries ℚ) = 0 from by simp]
      exact (mul_eq_zero.mp hrec).resolve_left hne

private lemma eq_of_ode {u v : PowerSeries ℚ}
    (hu : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) u
      = (2 - X) * u + (4 - X) * Submission.CDTPlan.B2 - 2 * X * (4 - X))
    (hv : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) v
      = (2 - X) * v + (4 - X) * Submission.CDTPlan.B2 - 2 * X * (4 - X)) :
    u = v := by
  have hhom : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) (u - v)
      = (2 - X) * (u - v) := by
    have h1 : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) (u - v)
        = ((X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) u)
          - ((X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) v) := by
      rw [map_sub]; ring
    rw [h1, hu, hv]; ring
  have hz := hom_eq_zero hhom
  exact sub_eq_zero.mp hz




/-- a finite sum of integers is an integer -/
private lemma exists_int_sum_of_term {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, ∃ z : ℤ, (z : ℚ) = f i) : ∃ z : ℤ, (z : ℚ) = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨w, hw⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨z + w, by rw [Finset.sum_insert ha, ← hz, ← hw]; push_cast; ring⟩

private theorem b4_denom_of_bridges
    (hB4ode : (X : PowerSeries ℚ) * (4 - X) * PowerSeries.derivative (R := ℚ) Submission.CDTPlan.B4
      = (2 - X) * Submission.CDTPlan.B4 + (4 - X) * Submission.CDTPlan.B2
        - 2 * X * (4 - X))
    (hF : b4F.subst sympY = b4Theta)
    (hTheta : sympY * (4 - sympY) * PowerSeries.derivative (R := ℚ) b4Theta
      = (PowerSeries.derivative (R := ℚ) sympY)
        * ((2 - sympY) * b4Theta + (4 - sympY) * (Submission.CDTPlan.B2.subst sympY)
            - 2 * sympY * (4 - sympY)))
    (hPF : (∀ j : ℕ, (b4P j).subst sympY = Submission.CDT.sympP j) ∧
      (∀ n k : ℕ, ∃ z : ℤ, PowerSeries.coeff n (b4Q k) = (z : ℚ)) ∧
      (∀ n k : ℕ, 2 * n ≤ k → PowerSeries.coeff n (b4Q k) = 0)) :
    HasDenomType 0 ![2, 2] Submission.CDTPlan.B4 := by
  have hFode := b4F_ode hF hTheta
  have hBF : Submission.CDTPlan.B4 = b4F := eq_of_ode hB4ode hFode
  refine ⟨1, 0, by norm_num, ?_⟩
  intro n hn
  have htwo : ∀ j : Fin 2, (![2, 2] : Fin 2 → ℕ) j = 2 := by
    intro j; fin_cases j <;> rfl
  have hprod : (∏ j : Fin 2, (Submission.CDTPlan.lcmUpto ((![2, 2] : Fin 2 → ℕ) j * n + 0) : ℚ))
      = (Submission.CDTPlan.lcmUpto (2 * n) : ℚ) ^ 2 := by
    simp only [htwo]
    rw [Finset.prod_const]
    norm_num
  rw [hprod, hBF]
  simp only [pow_zero, mul_one, Nat.cast_one, one_mul]
  rw [coeff_b4F]
  have hterm : ∀ k ∈ Finset.range (2 * n + 1), ∃ z : ℤ,
      (z : ℚ) = (Submission.CDTPlan.lcmUpto (2 * n) : ℚ) ^ 2
        * ((1 / (((k + 1 : ℕ)) : ℚ) ^ 2) * PowerSeries.coeff n (b4Q (k + 1))) := by
    intro k hk
    rcases lt_or_ge (k + 1) (2 * n) with hcase | hcase
    · have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hdvd : (k + 1) ∣ Submission.CDTPlan.lcmUpto (2 * n) := by
        rw [Submission.CDTPlan.lcmUpto]
        exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
      obtain ⟨q, hq⟩ := hdvd
      obtain ⟨z, hz⟩ := hPF.2.1 n (k + 1)
      refine ⟨z * (q : ℤ) ^ 2, ?_⟩
      rw [hz, hq]
      push_cast
      field_simp
    · rw [hPF.2.2 n (k + 1) hcase]
      exact ⟨0, by ring⟩
  obtain ⟨A, hA⟩ := exists_int_sum_of_term (Finset.range (2 * n + 1))
    (fun k => (Submission.CDTPlan.lcmUpto (2 * n) : ℚ) ^ 2
      * ((1 / (((k + 1 : ℕ)) : ℚ) ^ 2) * PowerSeries.coeff n (b4Q (k + 1)))) hterm
  exact ⟨A, by rw [Finset.mul_sum, hA]⟩

/-- **The denominator type of the pure function `B₄`** (paper Lemma `bdenominators`, case `i = 4`):
`B₄` (the double-binomial series of `Submission.CDTPlan`) has denominator type `[1..2n]²`. -/
theorem b4_denom : HasDenomType 0 ![2, 2] B4 := by
  have hPF := Work.Pure.b4_PF_facts
  have hTB := Work.Pure.b4_theta_bridge
  exact b4_denom_of_bridges Work.Pure.b4_rel hPF.2.2.2 hTB.2.2.2.2
    ⟨hPF.1, hPF.2.1, hPF.2.2.1⟩


end

end Work.Pure
