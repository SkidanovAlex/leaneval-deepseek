import Mathlib
import Submission.Work.Haupt.defs

/-! # The two-variable theta product and theta series

For a nome `x` and a variable `z` we introduce

* `ThetaProd x z = ∏_{n ≥ 0} (1 + x^{2n+1} z) (1 + x^{2n+1}/z)`,
* `ThetaSum  x z = ∑_{n ∈ ℤ} x^{n²} z^n`,

and record the basic relation `T2 x = ThetaSum x x` together with the functional
equation `F (x²z) = (xz)⁻¹ F z` shared by both.
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-- `ThetaProd x z = ∏_{n ≥ 0} (1 + x^{2n+1} z)(1 + x^{2n+1}/z)`. -/
def ThetaProd (x z : ℂ) : ℂ := ∏' n : ℕ, (1 + x ^ (2 * n + 1) * z) * (1 + x ^ (2 * n + 1) / z)

/-- `ThetaSum x z = ∑_{n ∈ ℤ} x^{n²} z^n`. -/
def ThetaSum (x z : ℂ) : ℂ := ∑' n : ℤ, x ^ (n ^ 2) * z ^ n

/-- `T2` is the theta series evaluated at `z = x`. -/
theorem T2_eq_ThetaSum_self (x : ℂ) (hx : x ≠ 0) : T2 x = ThetaSum x x := by
  simp only [T2, ThetaSum]
  refine tsum_congr fun n => ?_
  rw [← zpow_add₀ hx]
  congr 1
  ring


/-! ## Auxiliary lemmas used in the final assembly -/

/-- Every `x` with `‖x‖ < 1` is the cube of some `X` with `‖X‖ < 1`. -/
theorem exists_cube_root (x : ℂ) (hx : ‖x‖ < 1) : ∃ X : ℂ, X ^ 3 = x ∧ ‖X‖ < 1 := by
  obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 3) (by norm_num)
  refine ⟨X, hX, ?_⟩
  have h3 : ‖X‖ ^ 3 = ‖x‖ := by rw [← norm_pow, hX]
  have hlt : ‖X‖ ^ 3 < 1 := by rw [h3]; exact hx
  exact lt_of_pow_lt_pow_left₀ 3 zero_le_one (by simpa using hlt)

/-- The even product `∏_{m ≥ 0}(1 - x^{2m+2})` is nonzero for `‖x‖ < 1`. -/
theorem prod_even_ne_zero (x : ℂ) (hx : ‖x‖ < 1) :
    (∏' m : ℕ, (1 - x ^ (2 * m + 2))) ≠ 0 := by
  have hx2 : ‖x‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hsum : Summable (fun m : ℕ => ‖-(x ^ (2 * m + 2))‖) := by
    have hgeom : Summable (fun m : ℕ => (‖x‖ ^ 2) ^ (m + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity) hx2)
    refine hgeom.congr (fun m => ?_)
    have h1 : ‖-(x ^ (2 * m + 2))‖ = ‖x‖ ^ (2 * (m + 1)) := by
      rw [norm_neg, norm_pow, show 2 * m + 2 = 2 * (m + 1) by ring]
    have h2 : (‖x‖ ^ 2) ^ (m + 1) = ‖x‖ ^ (2 * (m + 1)) := (pow_mul _ _ _).symm
    rw [h1, h2]
  have hne : ∀ m : ℕ, (1 : ℂ) + (-(x ^ (2 * m + 2))) ≠ 0 := by
    intro m h
    have h1 : x ^ (2 * m + 2) = 1 := by
      have := add_eq_zero_iff_eq_neg.mp h
      simpa using this.symm
    have h2 : ‖x ^ (2 * m + 2)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg x) hx (by positivity)
    rw [h1, norm_one] at h2
    exact lt_irrefl 1 h2
  have hthis : (∏' m : ℕ, (1 + -(x ^ (2 * m + 2)))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hsum
  refine fun hzero => hthis ?_
  rwa [show (∏' m : ℕ, (1 - x ^ (2 * m + 2))) = (∏' m : ℕ, (1 + -(x ^ (2 * m + 2)))) from
    tprod_congr fun m => by ring] at hzero


/-- At `x = 0`, `T2` is `2`. -/
theorem T2_zero : T2 0 = 2 := by
  rw [T2]
  rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) (fun n hn => ?_)]
  · norm_num
  · have hne : n * (n + 1) ≠ 0 := by
      intro h
      have : n = 0 ∨ n = -1 := by
        have h' : n = 0 ∨ n + 1 = 0 := mul_eq_zero.mp h
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      tauto
    rw [zero_zpow_eq, if_neg hne]

/-- At `x = 0`, `T2prod` is `2`. -/
theorem T2prod_zero : T2prod 0 = 2 := by
  rw [T2prod]
  have h : ∀ n : ℕ, (1 - (0 : ℂ) ^ (2 * (n + 1))) * (1 + (0 : ℂ) ^ (2 * (n + 1))) ^ 2 = 1 := by
    intro n
    rw [zero_pow (by omega : 2 * (n + 1) ≠ 0)]
    ring
  rw [tprod_congr h]
  simp


/-- `T2prod` splits as `2 · A · B²` with `A = ∏(1-x^{2m+2})` and `B = ∏(1+x^{2m+2})`. -/
theorem T2prod_split (x : ℂ) (hx : ‖x‖ < 1) :
    T2prod x = 2 * ((∏' m : ℕ, (1 - x ^ (2 * m + 2))) *
      (∏' m : ℕ, (1 + x ^ (2 * m + 2))) ^ 2) := by
  rw [T2prod]
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hs : Summable (fun n : ℕ => (x ^ 2) ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hx2)
  have hmB : Multipliable (fun n : ℕ => 1 + (x ^ 2) ^ (n + 1)) :=
    Complex.multipliable_one_add_of_summable hs
  have hmA : Multipliable (fun n : ℕ => 1 - (x ^ 2) ^ (n + 1)) :=
    (Complex.multipliable_one_add_of_summable hs.neg).congr (fun n => by
      simp [sub_eq_add_neg])
  have hp : ∀ n : ℕ, (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * (n + 1))) ^ 2 =
      (1 - (x ^ 2) ^ (n + 1)) * (1 + (x ^ 2) ^ (n + 1)) ^ 2 := by
    intro n
    rw [← pow_mul]
  have hexp : ∀ n : ℕ, (x ^ 2) ^ (n + 1) = x ^ (2 * n + 2) := by
    intro n
    rw [← pow_mul, show 2 * (n + 1) = 2 * n + 2 by omega]
  have hAid : (∏' n : ℕ, (1 - (x ^ 2) ^ (n + 1))) = ∏' m : ℕ, (1 - x ^ (2 * m + 2)) :=
    tprod_congr fun n => by rw [hexp n]
  have hBid : (∏' n : ℕ, (1 + (x ^ 2) ^ (n + 1))) = ∏' m : ℕ, (1 + x ^ (2 * m + 2)) :=
    tprod_congr fun n => by rw [hexp n]
  rw [tprod_congr hp, Multipliable.tprod_mul hmA (hmB.pow 2), Multipliable.tprod_pow hmB 2,
    hAid, hBid]

end

end Work.Haupt
