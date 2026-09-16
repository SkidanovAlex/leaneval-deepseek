import Submission.ZagierHoffmanProof.CarlitzLog

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The Carlitz module as a Drinfeld module over `A = F[X]`

Let `F` be a finite field, `q = Nat.card F`, `A = F[X]` (`θ = X`) and `K = RatFunc F`.  This file
constructs the action of `A` on power series defined by the *Carlitz module*
`C_θ(z) = θ z + z ^ q`: for `a = ∑_i c_i θ ^ i ∈ A` (`c_i ∈ F`) one sets
`C_a = ∑_i c_i C_{θ ^ i}` (`carlitzAct`), where `C_{θ ^ i}` is the `i`-fold iterate `carlitzAction`.

The main result is that the *Carlitz exponential* uniformizes this module:
★★ `carlitzAct_exp : C_a(e_C(z)) = e_C(a z)` for every `a ∈ A`, stated as
`carlitzAct F a (carlitzExp F) = PowerSeries.rescale (algebraMap F[X] (RatFunc F) a) (carlitzExp F)`.

The proof is a coefficient computation, resting on the two structural lemmas

* `rescale_eq_smul_of_qpowSparse` : on series supported on the `q`-powers (`QpowSparse`), rescaling
  by a constant `c ∈ F` coincides with scalar multiplication;
* `rescale_add_of_qpowSparse` : on such series, `rescale` is additive in the parameter (because
  `(x + y) ^ (q ^ i) = x ^ (q ^ i) + y ^ (q ^ i)`, `add_pow_card_pow`).

Together with `carlitzAction_exp` (`C_{θ ^ i}(e_C z) = e_C(θ ^ i z)`) this gives the result term by
term; note that both properties genuinely use that `e_C` is an `F_q`-linear series.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Act

open PowerSeries

def QpowSparse (f : PowerSeries (RatFunc F)) : Prop :=
  ∀ n : ℕ, (∀ i, n ≠ Nat.card F ^ i) → f.coeff n = 0

lemma qpowSparse_rescale {f : PowerSeries (RatFunc F)} (hf : QpowSparse F f) (x : RatFunc F) :
    QpowSparse F (PowerSeries.rescale x f) := by
  intro n hn
  rw [PowerSeries.coeff_rescale, hf n hn, mul_zero]

lemma add_pow_card_pow (x y : RatFunc F) (i : ℕ) :
    (x + y) ^ (Nat.card F ^ i) = x ^ (Nat.card F ^ i) + y ^ (Nat.card F ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show Nat.card F ^ (i + 1) = Nat.card F ^ i * Nat.card F from pow_succ _ _, pow_mul, ih,
        carlitz_add_pow_card F, ← pow_mul, ← pow_mul,
        show Nat.card F ^ i * Nat.card F = Nat.card F ^ (i + 1) from (pow_succ _ _).symm]

lemma pow_card_coe (c : F) :
    (algebraMap F (RatFunc F) c) ^ Nat.card F = algebraMap F (RatFunc F) c := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [← map_pow, show c ^ Nat.card F = c from by
    rw [← Fintype.card_eq_nat_card]; exact FiniteField.pow_card c]

lemma pow_natCard_pow (x : RatFunc F) (hx : x ^ Nat.card F = x) (i : ℕ) :
    x ^ (Nat.card F ^ i) = x := by
  induction i with
  | zero => rw [pow_zero, pow_one]
  | succ i ih =>
      rw [show Nat.card F ^ (i + 1) = Nat.card F ^ i * Nat.card F from pow_succ _ _, pow_mul, ih, hx]

lemma rescale_eq_smul_of_qpowSparse {f : PowerSeries (RatFunc F)} (hf : QpowSparse F f) (c : F) :
    PowerSeries.rescale (algebraMap F (RatFunc F) c) f = algebraMap F (RatFunc F) c • f := by
  ext n
  rw [PowerSeries.coeff_rescale, map_smul]
  by_cases hn : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, rfl⟩ := hn
    rw [pow_natCard_pow (x := algebraMap F (RatFunc F) c) (hx := pow_card_coe F c) (i := i),
      smul_eq_mul]
  · rw [hf n (fun i h => hn ⟨i, h⟩), smul_zero, mul_zero]

lemma rescale_add_of_qpowSparse {f : PowerSeries (RatFunc F)} (hf : QpowSparse F f)
    (x y : RatFunc F) :
    PowerSeries.rescale (x + y) f = PowerSeries.rescale x f + PowerSeries.rescale y f := by
  ext n
  rw [PowerSeries.coeff_rescale, map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
  by_cases hn : ∃ i, n = Nat.card F ^ i
  · obtain ⟨i, rfl⟩ := hn
    rw [add_pow_card_pow F x y i, add_mul]
  · rw [hf n (fun i h => hn ⟨i, h⟩), mul_zero, mul_zero, mul_zero, add_zero]

lemma constantCoeff_carlitzExp : (carlitzExp F).constantCoeff = 0 := by
  rw [carlitzExp, PowerSeries.constantCoeff_mk, carlitzECoeff_eq_zero F (fun i h => by
    have h1 : 0 < Nat.card F ^ i := pow_pos (by have := carlitz_card_ge_two F; omega) i
    omega)]

lemma qpowSparse_carlitzExp : QpowSparse F (carlitzExp F) := by
  intro n hn
  rw [carlitzExp, PowerSeries.coeff_mk, carlitzECoeff_eq_zero F (fun i h => hn i h)]

lemma carlitz_coe_C (c : F) :
    (algebraMap F[X] (RatFunc F)) (Polynomial.C c) = algebraMap F (RatFunc F) c := by
  rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F) c, Polynomial.algebraMap_eq]

noncomputable def carlitzAct (a : F[X]) (f : PowerSeries (RatFunc F)) : PowerSeries (RatFunc F) :=
  ∑ i ∈ Finset.range (a.natDegree + 1),
    PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i f

lemma carlitzAct_term (a : F[X]) (f : PowerSeries (RatFunc F)) (i : ℕ) :
    PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i f
      = algebraMap F (RatFunc F) (a.coeff i) • carlitzAction F i f := by
  rw [Algebra.smul_def]
  congr 1

theorem carlitzAct_exp (a : F[X]) :
    carlitzAct F a (carlitzExp F)
      = PowerSeries.rescale ((algebraMap F[X] (RatFunc F)) a) (carlitzExp F) := by
  have he := qpowSparse_carlitzExp F
  have hterm : ∀ i : ℕ,
      PowerSeries.C (algebraMap F (RatFunc F) (a.coeff i)) * carlitzAction F i (carlitzExp F)
      = PowerSeries.rescale ((algebraMap F (RatFunc F) (a.coeff i)) * carlitzTheta F ^ i)
          (carlitzExp F) := by
    intro i
    rw [carlitzAct_term, carlitzAction_exp]
    rw [← rescale_eq_smul_of_qpowSparse F (qpowSparse_rescale F he ((carlitzTheta F) ^ i)) (a.coeff i)]
    rw [PowerSeries.rescale_rescale, mul_comm]
  rw [carlitzAct, Finset.sum_congr rfl (fun i _ => hterm i)]
  have hsum : ∀ s : Finset ℕ,
      (∑ i ∈ s, PowerSeries.rescale ((algebraMap F (RatFunc F) (a.coeff i)) * carlitzTheta F ^ i)
          (carlitzExp F))
        = PowerSeries.rescale ((∑ i ∈ s, (algebraMap F (RatFunc F) (a.coeff i)) * carlitzTheta F ^ i))
          (carlitzExp F) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, PowerSeries.rescale_eq_subst,
          show (0 : RatFunc F) • (PowerSeries.X : PowerSeries (RatFunc F)) = 0 from zero_smul _ _,
          PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_carlitzExp F)]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih,
        ← rescale_add_of_qpowSparse F he]
  rw [hsum]
  have h1 : (∑ i ∈ Finset.range (a.natDegree + 1),
        (algebraMap F (RatFunc F)) (a.coeff i) * carlitzTheta F ^ i)
      = ∑ i ∈ Finset.range (a.natDegree + 1),
          (algebraMap F[X] (RatFunc F)) (Polynomial.C (a.coeff i) * Polynomial.X ^ i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_pow, carlitz_coe_C, ← carlitz_coe_X]
    rfl
  rw [show (∑ i ∈ Finset.range (a.natDegree + 1),
        (algebraMap F (RatFunc F)) (a.coeff i) * carlitzTheta F ^ i)
      = ((a : F[X]) : RatFunc F) from by
    rw [h1, ← map_sum]
    exact congrArg (algebraMap F[X] (RatFunc F))
      (Polynomial.as_sum_range_C_mul_X_pow a).symm]
  rfl

end Act

section End

open PowerSeries

lemma pow_card_coe' (c : F) : c ^ Nat.card F = c := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [← Fintype.card_eq_nat_card]
  exact FiniteField.pow_card c

/-- The Carlitz module `C_θ` as an `F`-linear endomorphism of `K⟦z⟧` (`K = RatFunc F`):
`C_θ(f) = θ f + f ^ q`. -/
noncomputable def carlitzThetaEnd : Module.End F (PowerSeries (RatFunc F)) where
  toFun f := PowerSeries.C (carlitzTheta F) * f + f ^ (Nat.card F)
  map_add' f g := by
    show PowerSeries.C (carlitzTheta F) * (f + g) + (f + g) ^ Nat.card F
      = (PowerSeries.C (carlitzTheta F) * f + f ^ Nat.card F)
        + (PowerSeries.C (carlitzTheta F) * g + g ^ Nat.card F)
    rw [mul_add, ps_add_pow_card F]
    ring
  map_smul' c f := by
    show PowerSeries.C (carlitzTheta F) * (c • f) + (c • f) ^ Nat.card F
      = c • (PowerSeries.C (carlitzTheta F) * f + f ^ Nat.card F)
    rw [Algebra.smul_def, Algebra.smul_def, mul_add]
    congr 1
    · ring
    · rw [mul_pow]
      congr 1
      rw [← map_pow]
      exact congrArg (algebraMap F (PowerSeries (RatFunc F))) (pow_card_coe' F c)

lemma carlitzThetaEnd_apply (f : PowerSeries (RatFunc F)) :
    carlitzThetaEnd F f = PowerSeries.C (carlitzTheta F) * f + f ^ (Nat.card F) := rfl

lemma carlitzThetaEnd_pow_apply (i : ℕ) (f : PowerSeries (RatFunc F)) :
    ((carlitzThetaEnd F) ^ i) f = carlitzAction F i f := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, carlitzAction_succ, carlitzThetaEnd_apply]

lemma carlitzAct_eq_aeval (a : F[X]) (f : PowerSeries (RatFunc F)) :
    carlitzAct F a f = (Polynomial.aeval (carlitzThetaEnd F) a) f := by
  rw [carlitzAct, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.smul_apply, carlitzThetaEnd_pow_apply]
  rw [carlitzAct_term, IsScalarTower.algebraMap_smul]

/-- ★ The action of `A` on power series given by the Carlitz module is multiplicative:
`C_{ab} = C_a ∘ C_b`. -/
theorem carlitzAct_mul (a b : F[X]) (f : PowerSeries (RatFunc F)) :
    carlitzAct F (a * b) f = carlitzAct F a (carlitzAct F b f) := by
  rw [carlitzAct_eq_aeval, carlitzAct_eq_aeval, carlitzAct_eq_aeval, Polynomial.aeval_mul]
  rfl

/-- ★ The action of `A` is additive in the polynomial: `C_{a+b} = C_a + C_b`. -/
theorem carlitzAct_add (a b : F[X]) (f : PowerSeries (RatFunc F)) :
    carlitzAct F (a + b) f = carlitzAct F a f + carlitzAct F b f := by
  rw [carlitzAct_eq_aeval, carlitzAct_eq_aeval, carlitzAct_eq_aeval, map_add, LinearMap.add_apply]

/-- `C_a` is `F`-linear in the coefficient: `C_{ca} = c C_a` for `c ∈ F`. -/
theorem carlitzAct_C_mul (c : F) (a : F[X]) (f : PowerSeries (RatFunc F)) :
    carlitzAct F (Polynomial.C c * a) f = c • carlitzAct F a f := by
  rw [carlitzAct_eq_aeval, carlitzAct_eq_aeval, map_mul, Polynomial.aeval_C, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

end End

end ZagierHoffmanPositiveChar
