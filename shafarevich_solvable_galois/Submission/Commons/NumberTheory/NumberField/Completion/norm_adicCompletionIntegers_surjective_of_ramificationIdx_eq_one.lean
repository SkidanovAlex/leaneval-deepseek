import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- In the value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, a power of an element which is equal
to `1` forces the element to be `1` (the value group is torsion free). -/
private lemma val_eq_one_of_pow_eq_one {F : Type*} [Field F]
    (v : Valuation F Zstar0) {x : F} {n : ℕ} (hn : n ≠ 0) (h : (v x) ^ n = 1) : v x = 1 := by
  have ha0 : v x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn] at h
    exact zero_ne_one h
  have hlog : WithZero.log (v x) = 0 := by
    have hc := congrArg WithZero.log h
    rw [WithZero.log_pow, WithZero.log_one] at hc
    rw [nsmul_eq_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_left (Nat.cast_ne_zero.mpr hn)
  calc v x = WithZero.exp (WithZero.log (v x)) := (WithZero.exp_log ha0).symm
    _ = WithZero.exp 0 := by rw [hlog]
    _ = 1 := WithZero.exp_zero

theorem norm_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ y : (Q.adicCompletion K)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (y : Q.adicCompletion K) = 1 →
      ∃ x : (q.adicCompletionIntegers L)ˣ,
        Algebra.norm (Q.adicCompletion K)
          ((x : q.adicCompletionIntegers L) : q.adicCompletion L) =
          (y : Q.adicCompletion K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro y hy
  obtain ⟨x, hx⟩ := norm_units_surjective_of_ramificationIdx_eq_one Q q hq h1
    (y : Q.adicCompletion K) hy
  have hn : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ≠ 0 := by
    haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    exact Module.finrank_pos.ne'
  have hpow : (Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) x) ^
      (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) = 1 := by
    have h1' := val_norm_adicCompletion_eq_pow Q q hq x
    rw [hx] at h1'
    have hmap : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0)
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (y : Q.adicCompletion K)) = 1 := by
      rw [RingHom.algebraMap_toAlgebra, val_adicCompletionMap_eq_pow Q q hq (y : Q.adicCompletion K),
        hy, h1, one_pow]
    rw [hmap] at h1'
    exact h1'.symm
  have hvx : Valued.v (R := q.adicCompletion L) (Γ₀ := Zstar0) x = 1 :=
    val_eq_one_of_pow_eq_one _ hn hpow
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact zero_ne_one hvx
  obtain ⟨hxmem, hxinvmem⟩ := (val_eq_one_iff q x hxne).mp hvx
  refine ⟨Units.mk ⟨x, hxmem⟩ ⟨x⁻¹, hxinvmem⟩ ?_ ?_, ?_⟩
  · exact Subtype.ext (by simp [mul_inv_cancel₀ hxne])
  · exact Subtype.ext (by simp [inv_mul_cancel₀ hxne])
  · show Algebra.norm (Q.adicCompletion K) x = (y : Q.adicCompletion K)
    exact hx

end Commons.NumberTheory.NumberField.Completion
