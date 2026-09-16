import Submission.ZagierHoffmanProof.CarlitzExpLog

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Anderson–Thakur polynomials `Ψ_k` and the Carlitz module action

The Anderson–Thakur polynomials `Ψ_k` are defined by
```
exp_C(u log_C x) = ∑_{k ≥ 0} Ψ_k(u) x^(q^k);
```
equivalently (since the Carlitz exponential uniformizes the Carlitz module,
`C_a(x) = exp_C(a log_C x)`) `atPsi k a` is the coefficient of `x^(q^k)` in the polynomial
`C_a(x)` giving the Carlitz module action of `a ∈ A = F[X]` on the additive group.

In this file we take the second description as the definition (`atPsi`) and prove the two
*interpolation* properties of the Anderson–Thakur polynomials:

* `atPsi_vanishes : a.natDegree < k → atPsi k a = 0`, and
* `atPsi_X_pow : atPsi k (X ^ k) = 1`;

the mathematical content is that the action `C_a(x) = ∑_k Ψ_k(a) x^(q^k)` has `x`-degree `q ^ deg a`
with leading coefficient the leading coefficient of `a` (`C_{θ^k}(x) = x^(q^k) + ` lower terms).

We also record the exponential form `carlitzAct_X_eq_exp_log : C_a(x) = exp_C(a log_C x)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section CoeffFrob

open PowerSeries

/-- The `q`-th power of a power series raises the coefficients to the `q`-th power and multiplies
the exponents. -/
lemma coeff_pow_card (f : PowerSeries (RatFunc F)) (n : ℕ) :
    PowerSeries.coeff n (f ^ Nat.card F)
      = if Nat.card F ∣ n then (PowerSeries.coeff (n / Nat.card F) f) ^ Nat.card F else 0 := by
  have hf : f = PowerSeries.mk (fun m => PowerSeries.coeff m f) := by
    ext m
    rw [PowerSeries.coeff_mk]
  conv_lhs => rw [hf]
  rw [mk_pow_card, PowerSeries.coeff_mk]

lemma coeff_pow_card_pow (f : PowerSeries (RatFunc F)) (k : ℕ) :
    PowerSeries.coeff (Nat.card F ^ k) (f ^ Nat.card F)
      = if k = 0 then 0 else (PowerSeries.coeff (Nat.card F ^ (k - 1)) f) ^ Nat.card F := by
  have h2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [coeff_pow_card]
  by_cases hk : k = 0
  · subst hk
    rw [if_neg (by
      intro hdvd
      have h1 : Nat.card F = 1 := Nat.dvd_one.mp (by simpa using hdvd)
      omega), if_pos rfl]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hdiv : Nat.card F ^ k / Nat.card F = Nat.card F ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk1).symm]
      rw [pow_succ, Nat.mul_div_cancel _ (by omega : 0 < Nat.card F)]
    rw [if_pos (dvd_pow_self _ hk), if_neg hk, hdiv]


end CoeffFrob

section Action

open PowerSeries

/-- The coefficient of `x ^ (q ^ n)` in `C_{θ ^ n}(x)` is `1`; and all higher coefficients vanish.
This is the statement that `C_{θ ^ n}` has `x`-degree `q ^ n` with leading coefficient `1`. -/
lemma carlitzAction_X_coeff (n : ℕ) :
    PowerSeries.coeff (Nat.card F ^ n) (carlitzAction F n PowerSeries.X) = 1 ∧
      ∀ j, Nat.card F ^ n < j →
        PowerSeries.coeff j (carlitzAction F n PowerSeries.X) = 0 := by
  have h2 : 1 < Nat.card F := by have := carlitz_card_ge_two F; omega
  induction n with
  | zero =>
      constructor
      · rw [carlitzAction_zero, pow_zero, PowerSeries.coeff_X, if_pos rfl]
      · intro j hj
        rw [carlitzAction_zero, PowerSeries.coeff_X, if_neg (by
          have h1 : (1 : ℕ) < j := by simpa using hj
          omega)]
  | succ n ih =>
      obtain ⟨htop, habove⟩ := ih
      have hstep : ∀ j, Nat.card F ^ (n + 1) < j →
          PowerSeries.coeff j (carlitzAction F (n + 1) PowerSeries.X) = 0 := by
        intro j hj
        rw [carlitzAction_succ, map_add, PowerSeries.coeff_C_mul, coeff_pow_card]
        have hjn : Nat.card F ^ n < j :=
          lt_trans (Nat.pow_lt_pow_right h2 (Nat.lt_succ_self n)) hj
        rw [habove j hjn, mul_zero, zero_add]
        by_cases hdvd : Nat.card F ∣ j
        · obtain ⟨t, rfl⟩ := hdvd
          rw [if_pos ⟨t, rfl⟩, Nat.mul_div_cancel_left t (by omega)]
          rw [habove t (by
            have h : Nat.card F * Nat.card F ^ n < Nat.card F * t := by
              rw [mul_comm (Nat.card F) (Nat.card F ^ n)]
              simpa [pow_succ] using hj
            exact Nat.lt_of_mul_lt_mul_left h)]
          exact zero_pow (by have := carlitz_card_ge_two F; omega)
        · rw [if_neg hdvd]
      refine ⟨?_, hstep⟩
      rw [carlitzAction_succ, map_add, PowerSeries.coeff_C_mul, coeff_pow_card,
        habove (Nat.card F ^ (n + 1)) (Nat.pow_lt_pow_right h2 (Nat.lt_succ_self n)),
        mul_zero, zero_add]
      rw [if_pos (dvd_pow_self _ (Nat.succ_ne_zero n)),
        Nat.pow_succ, Nat.mul_div_cancel _ (by omega : 0 < Nat.card F), htop, one_pow]

/-- ★ The Anderson–Thakur polynomial `Ψ_k` evaluated at `a ∈ A`, i.e. the coefficient of
`x ^ (q ^ k)` in the Carlitz module action `C_a(x)`. -/
noncomputable def atPsi (k : ℕ) (a : F[X]) : RatFunc F :=
  PowerSeries.coeff (Nat.card F ^ k) (carlitzAct F a PowerSeries.X)

/-- The top coefficient of `C_a(x)`: it is the leading coefficient of `a`. -/
lemma atPsi_eq_zero_of_lt_degree (k : ℕ) (a : F[X]) (h : a.natDegree < k) : atPsi F k a = 0 := by
  rw [atPsi, carlitzAct, map_sum, Finset.sum_eq_zero]
  intro i hi
  rw [Finset.mem_range] at hi
  rw [PowerSeries.coeff_C_mul, (carlitzAction_X_coeff F i).2 (Nat.card F ^ k)]
  · rw [mul_zero]
  · exact Nat.pow_lt_pow_right (by have := carlitz_card_ge_two F; omega) (by omega)

/-- ★ `Ψ_k(θ ^ k) = 1` (the Anderson–Thakur polynomial interpolates the `k`-th layer). -/
lemma atPsi_X_pow (k : ℕ) : atPsi F k (Polynomial.X ^ k) = 1 := by
  rw [atPsi, carlitzAct]
  have hsingle : ∀ i ∈ Finset.range ((Polynomial.X ^ k : F[X]).natDegree + 1),
      PowerSeries.C (algebraMap F (RatFunc F) ((Polynomial.X ^ k : F[X]).coeff i))
          * carlitzAction F i PowerSeries.X
        = if i = k then carlitzAction F k PowerSeries.X else 0 := by
    intro i _
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, Polynomial.coeff_X_pow_self, map_one, map_one PowerSeries.C, one_mul]
    · rw [if_neg hik, Polynomial.coeff_X_pow, if_neg (by omega)]
      rw [map_zero, map_zero PowerSeries.C, zero_mul]
  have hsum : (∑ i ∈ Finset.range ((Polynomial.X ^ k : F[X]).natDegree + 1),
        PowerSeries.C (algebraMap F (RatFunc F) ((Polynomial.X ^ k : F[X]).coeff i))
          * carlitzAction F i PowerSeries.X) = carlitzAction F k PowerSeries.X := by
    rw [Finset.sum_congr rfl hsingle,
      Finset.sum_ite_eq' (Finset.range ((Polynomial.X ^ k : F[X]).natDegree + 1)) k
        (fun _ => carlitzAction F k PowerSeries.X),
      if_pos (by rw [Polynomial.natDegree_X_pow]; exact Finset.mem_range.mpr (Nat.lt_succ_self k))]
  rw [hsum, (carlitzAction_X_coeff F k).1]

end Action

section Subst

open PowerSeries

/-- Substitution of power series commutes with the iteration `C_{θ ^ n}` of the Carlitz action. -/
lemma subst_carlitzAction (g : PowerSeries (RatFunc F)) (hg : PowerSeries.HasSubst g) (n : ℕ)
    (f : PowerSeries (RatFunc F)) :
    PowerSeries.subst g (carlitzAction F n f) = carlitzAction F n (PowerSeries.subst g f) := by
  induction n with
  | zero => rw [carlitzAction_zero, carlitzAction_zero]
  | succ n ih =>
      rw [carlitzAction_succ, PowerSeries.subst_add hg, PowerSeries.subst_mul hg, ih,
        PowerSeries.subst_pow hg, ih, PowerSeries.subst_C, carlitzAction_succ]
      rfl

/-- Substitution of power series commutes with the Carlitz action `C_a`. -/
lemma subst_carlitzAct (g : PowerSeries (RatFunc F)) (hg : PowerSeries.HasSubst g) (a : F[X])
    (f : PowerSeries (RatFunc F)) :
    PowerSeries.subst g (carlitzAct F a f) = carlitzAct F a (PowerSeries.subst g f) := by
  have hterm : ∀ i ∈ Finset.range (a.natDegree + 1),
      PowerSeries.subst g (PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i f)
        = PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i))
            * carlitzAction F i (PowerSeries.subst g f) := by
    intro i _
    rw [PowerSeries.subst_mul hg, PowerSeries.subst_C, subst_carlitzAction F g hg i f]
    rfl
  have hsum : PowerSeries.subst g (∑ i ∈ Finset.range (a.natDegree + 1),
        PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i f)
      = ∑ i ∈ Finset.range (a.natDegree + 1), PowerSeries.subst g
          (PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i f) := by
    rw [← PowerSeries.coe_substAlgHom hg, map_sum]
  rw [carlitzAct, carlitzAct, hsum]
  exact Finset.sum_congr rfl hterm

lemma hasSubst_C_mul_X' (F : Type*) [Field F] (r : RatFunc F) :
    PowerSeries.HasSubst (PowerSeries.C r * (PowerSeries.X : PowerSeries (RatFunc F))) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero])

/-- ★★ **The Carlitz module action is given by the Carlitz exponential and logarithm**:
`C_a(x) = exp_C(a log_C x)` — the Anderson–Thakur description of the module. -/
theorem carlitzAct_X_eq_exp_log (a : F[X]) :
    carlitzAct F a PowerSeries.X
      = (carlitzExp F).subst (PowerSeries.C ((a : RatFunc F)) * carlitzLog F) := by
  have hlog : PowerSeries.HasSubst (carlitzLog F) := hasSubst_carlitzLog F
  have hexp : PowerSeries.HasSubst (carlitzExp F) := hasSubst_carlitzExp F
  have h1 : PowerSeries.subst (carlitzLog F) (carlitzAct F a (carlitzExp F))
      = carlitzAct F a PowerSeries.X := by
    rw [subst_carlitzAct F (carlitzLog F) hlog a (carlitzExp F), carlitzExp_subst_log]
  have h2 : PowerSeries.subst (carlitzLog F)
        (PowerSeries.rescale ((algebraMap F[X] (RatFunc F)) a) (carlitzExp F))
      = PowerSeries.subst (PowerSeries.C ((a : RatFunc F)) * carlitzLog F) (carlitzExp F) := by
    rw [PowerSeries.rescale_eq_subst]
    rw [show ((algebraMap F[X] (RatFunc F)) a) • (PowerSeries.X : PowerSeries (RatFunc F))
        = PowerSeries.C ((a : RatFunc F)) * PowerSeries.X from by
      rw [Algebra.smul_def, PowerSeries.C_eq_algebraMap]
      rfl]
    rw [PowerSeries.subst_comp_subst_apply (hasSubst_C_mul_X' F (a : RatFunc F)) hlog,
      PowerSeries.subst_mul hlog, PowerSeries.subst_C, PowerSeries.subst_X hlog]
    rfl
  have h3 : PowerSeries.subst (carlitzLog F) (carlitzAct F a (carlitzExp F))
      = PowerSeries.subst (PowerSeries.C ((a : RatFunc F)) * carlitzLog F) (carlitzExp F) := by
    rw [carlitzAct_exp]
    exact h2
  rw [← h1]
  exact h3

/-- `Ψ_k` is additive in the polynomial variable. -/
lemma atPsi_add (k : ℕ) (a b : F[X]) : atPsi F k (a + b) = atPsi F k a + atPsi F k b := by
  rw [atPsi, atPsi, atPsi, carlitzAct_add, map_add]

/-- `Ψ_k` is `F`-homogeneous in the polynomial variable. -/
lemma atPsi_C_mul (k : ℕ) (c : F) (a : F[X]) :
    atPsi F k (Polynomial.C c * a) = algebraMap F (RatFunc F) c * atPsi F k a := by
  rw [atPsi, atPsi, carlitzAct_C_mul, ← IsScalarTower.algebraMap_smul (RatFunc F) c, map_smul,
    smul_eq_mul]

/-- `Ψ_k` vanishes at `0`. -/
@[simp] lemma atPsi_zero (F : Type*) [Field F] (k : ℕ) : atPsi F k 0 = 0 := by
  rw [atPsi, carlitzAct, Polynomial.natDegree_zero]
  simp

end Subst

section Interp

open PowerSeries

variable {F}

/-- `Ψ_k` is additive in the polynomial variable. -/
lemma atPsi_sum (F : Type*) [Field F] [Finite F] (k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → F[X]) : atPsi F k (∑ i ∈ s, f i) = ∑ i ∈ s, atPsi F k (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, atPsi_add, Finset.sum_cons, ih]

/-- ★ `Ψ_k(a)` depends only on the coefficients of `a` in degrees `≥ k`. -/
lemma atPsi_eq_sum_Icc (F : Type*) [Field F] [Finite F] (k : ℕ) (a : F[X]) :
    atPsi F k a = ∑ i ∈ Finset.Icc k a.natDegree,
      algebraMap F (RatFunc F) (a.coeff i) * atPsi F k (Polynomial.X ^ i) := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow a]
  rw [atPsi_sum, Finset.sum_congr rfl (fun i _ => by rw [atPsi_C_mul])]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro i hi hnot
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc] at hnot
    have hlt : i < k := by
      by_contra hc
      exact hnot ⟨Nat.le_of_not_lt hc, by omega⟩
    rw [atPsi_eq_zero_of_lt_degree F k (Polynomial.X ^ i) (by
      rw [Polynomial.natDegree_X_pow]; exact hlt), mul_zero]

/-- ★★ `Ψ_{deg a}(a) = lc(a)`: the Anderson–Thakur polynomial on the `k`-th layer
(`C_a(x) = lc(a) x^(q^deg a) +` lower terms). -/
lemma atPsi_self (F : Type*) [Field F] [Finite F] (a : F[X]) :
    atPsi F a.natDegree a = algebraMap F (RatFunc F) a.leadingCoeff := by
  rw [atPsi_eq_sum_Icc F a.natDegree a, Finset.sum_eq_single a.natDegree]
  · rw [atPsi_X_pow, mul_one, Polynomial.coeff_natDegree]
  · intro i hi hne
    rw [Finset.mem_Icc] at hi
    exact absurd (le_antisymm hi.2 hi.1) hne
  · intro h
    rw [Finset.mem_Icc] at h
    have hk : a.natDegree < a.natDegree := by
      by_contra hc
      exact h ⟨Nat.le_of_not_lt hc, le_rfl⟩
    exact absurd hk (lt_irrefl _)

end Interp

section Zero

open PowerSeries

lemma carlitzAction_X_coeff_one (i : ℕ) :
    PowerSeries.coeff 1 (carlitzAction F i PowerSeries.X) = (carlitzTheta F) ^ i := by
  have hq : ¬ (Nat.card F ∣ 1) := by
    intro h
    have h1 : Nat.card F ≤ 1 := Nat.le_of_dvd (by norm_num) h
    have := carlitz_card_ge_two F
    omega
  induction i with
  | zero => rw [carlitzAction_zero, pow_zero, PowerSeries.coeff_X, if_pos rfl]
  | succ i ih =>
      rw [carlitzAction_succ, map_add, PowerSeries.coeff_C_mul, coeff_pow_card, ih, if_neg hq,
        add_zero, pow_succ, mul_comm]

lemma atPsi_zero_eq (a : F[X]) : atPsi F 0 a = algebraMap F[X] (RatFunc F) a := by
  rw [atPsi, carlitzAct, map_sum]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [PowerSeries.coeff_C_mul, pow_zero, carlitzAction_X_coeff_one])]
  conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow a]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, carlitz_coe_C,
    show (algebraMap F[X] (RatFunc F)) Polynomial.X = carlitzTheta F from rfl]


end Zero

end ZagierHoffmanPositiveChar
