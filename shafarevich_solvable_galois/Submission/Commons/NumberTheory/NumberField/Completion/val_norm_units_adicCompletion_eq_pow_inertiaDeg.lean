import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- In the value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` of a discrete valuation, the `e`-th
power map is injective on nonzero elements as soon as `e ≠ 0`: `ℤᵐ⁰` is a linearly ordered
commutative group with zero, i.e. the multiplicative group `exp ℤ` adjoined by `0`, and
`(exp m)^e = exp (m * e)`. -/
private lemma withZero_pow_left_cancel {e : ℕ} (he : e ≠ 0)
    {a b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) (h : a ^ e = b ^ e) : a = b := by
  -- `a ≠ 0` as well, since `0 ^ e = 0` and `b ^ e ≠ 0`
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow he] at h
    exact (pow_ne_zero e hb) h.symm
  -- write both elements as `exp` of an integer
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨WithZero.log a, WithZero.exp_log ha⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, WithZero.exp n = b := ⟨WithZero.log b, WithZero.exp_log hb⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul] at h
  rw [WithZero.exp_inj]
  exact mul_left_cancel₀ (show (e : ℤ) ≠ 0 from by exact_mod_cast he) h

/-- For a unit `x` of the local field `L_q`, the valuation of its norm in `K_Q` is the `f`-th
power of the valuation of `x`, where `f = e(q|Q)` is the inertia degree: the norm multiplies
valuations by `f`.  This follows from
`Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow` (which gives the
`[L_q : K_Q] = e·f`-th power) together with
`Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow` (the `e`-th power
relation between the two valuations on the embedded base field) and the uniqueness of `e`-th
roots in the value group `ℤᵐ⁰`. -/
theorem val_norm_units_adicCompletion_eq_pow_inertiaDeg {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : (q.adicCompletion L)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L)) =
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (x : q.adicCompletion L)) ^ (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro x
  -- the ramification index is nonzero (the extension is finite and `q` is nonzero)
  have he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 0 :=
    (Ideal.ramificationIdx_pos (R := NumberField.RingOfIntegers K) q.asIdeal).ne'
  -- the norm relation for the `[L_q : K_Q]`-th power, phrased with `adicCompletionMap`
  have hnorm := val_norm_adicCompletion_eq_pow Q q hq (x : q.adicCompletion L)
  rw [RingHom.algebraMap_toAlgebra] at hnorm
  -- the `e`-th power relation along the embedded base field
  have hmap := val_adicCompletionMap_eq_pow Q q hq
    (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L))
  -- the local fundamental identity `[L_q : K_Q] = e · f`
  have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    (finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq).symm
  -- the right hand side is nonzero, so the `e`-th powers determine the elements
  have hb : (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (x : q.adicCompletion L)) ^ (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr (Units.ne_zero x))
  refine withZero_pow_left_cancel he hb ?_
  -- `v_K (norm x) ^ e = v_L (map (norm x)) = (v_L x) ^ [L_q : K_Q] = ((v_L x) ^ f) ^ e`
  rw [← hmap, hnorm, hfin, mul_comm, pow_mul]

end Commons.NumberTheory.NumberField.Completion
