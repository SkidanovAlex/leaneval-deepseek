import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LocalFieldArith.finite_units_quotient_adicCompletion
import Submission.Work.SSGRoute.adicCompletion_pow_of_deep_principalUnit
import Submission.Work.SSGRoute.exists_algebraMap_approx
import Submission.Work.SSGRoute.val_mul_inv_sub_one_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute

/-- **The exponent of `p` in the value group of a `𝔭`-adic completion.**

For a number field `K`, a finite prime `𝔭` of `K` and a prime `p`, there is `e : ℕ` with
`v p = exp (-e)` in the value group `ℤᵐ⁰` of the completion `𝔭.adicCompletion K`.
(The corresponding lemma `Work.SSGRoute.LocalFieldArith.exists_exp_neg_val_prime` is `private`, so
the argument is repeated here.) -/
theorem exists_exp_neg_val_prime {K : Type*} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) [Fact p.Prime] :
    ∃ e : ℕ, (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
        ((p : ℕ) : 𝔭.adicCompletion K) = WithZero.exp (-(e : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hchar : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have hnat_val : ∀ n : ℕ, (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((n : ℕ) : 𝔭.adicCompletion K) ≤ 1 := by
    intro n; induction n with
    | zero => rw [Nat.cast_zero, Valuation.map_zero]; exact zero_le
    | succ k ih =>
      rw [Nat.cast_succ]
      refine Valuation.map_add_le _ ih ?_
      rw [Valuation.map_one]
  have hne : ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hvalne : (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  set m : ℤ := WithZero.log ((Valued.v :
      Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K)) with hm
  have hexpm : (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K) = WithZero.exp m := by
    rw [hm]; exact (WithZero.exp_log hvalne).symm
  have hmle : m ≤ 0 := by
    have h : WithZero.exp m ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero, ← hexpm]; exact hnat_val p
    exact WithZero.exp_le_exp.mp h
  refine ⟨m.natAbs, ?_⟩
  have hcast : (((m.natAbs : ℕ) : ℤ)) = -m := Int.ofNat_natAbs_of_nonpos hmle
  rw [hexpm, hcast]
  congr 1
  ring

/-- **Every unit of a `𝔭`-adic completion is a global unit times a `p`-th power.**

For a number field `K`, a finite place `Q` and a prime `p`, every `b ∈ (Q.adicCompletion K)ˣ` is of
the form `β · c ^ p` with `β ∈ Kˣ` and `c` a unit of the completion.

Route: the `p`-th power subgroup of `(Q.adicCompletion K)ˣ` contains the deep principal units
`pu Q (M + e)` where `v p = exp (-e)` (`principalUnits_deep_mem_pow` with any `LogData Q M`:
`Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow`), and the image of `K` (hence of `Kˣ`)
is dense in the completion; density gives `t ∈ K` with `v (t - b)` small enough that
`b * t⁻¹ ∈ pu Q (M + e)`.
`Commons.NumberTheory.NumberField.Completion.exists_algebraMap_mem_exp_ball` supplies the
approximant at a prescribed `exp`-ball, and `Commons.NumberTheory.NumberField.Completion.valued_alg_eq`
identifies the valuation on the image of `K`.
(The exponent `e` with `v p = exp (-e)` has to be produced locally: the copy
`exists_exp_neg_val_prime` in `Work/SSGRoute/LocalFieldArith/finite_units_quotient_adicCompletion.lean`
is `private`, so inline or re-prove it, e.g. by `WithZero.log` of `v p` and `Int.ofNat_natAbs_of_nonpos`.) -/
theorem adicCompletion_units_mul_pow (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) [Fact p.Prime] (b : (Q.adicCompletion K)ˣ) :
    ∃ (β : Kˣ) (c : (Q.adicCompletion K)ˣ),
      Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom β * c ^ p = b := by
  classical
  -- the exponential/logarithm of the completion at some level `M ≥ 1`
  obtain ⟨M, hM, ⟨D⟩⟩ := NK.LocalInputs.PowerQuotient.exists_logData (K := K) Q
  -- the exponent `e` of `p` in the value group
  obtain ⟨e, he⟩ := exists_exp_neg_val_prime (K := K) Q p
  -- density: approximate `b` by an element `t ∈ K`
  obtain ⟨t, ht0, htval, htclose⟩ := exists_algebraMap_approx K Q hM e b
  set Aβ : (Q.adicCompletion K)ˣ :=
    Units.map (algebraMap K (Q.adicCompletion K)).toMonoidHom (Units.mk0 t ht0) with hAβ
  have hAβval : ((Aβ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      algebraMap K (Q.adicCompletion K) t := by
    rw [hAβ, Units.coe_map, Units.val_mk0]
    rfl
  have hvb : Valued.v ((b : Q.adicCompletion K)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero b)
  have hδ1 : WithZero.exp (-(((M + e : ℕ) : ℤ))) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm]
    exact WithZero.exp_le_exp.mpr (by omega)
  -- the element `b / t` of the completion
  set w : (Q.adicCompletion K)ˣ := b * Aβ⁻¹ with hw
  have hwval : Valued.v ((w : Q.adicCompletion K)) = 1 := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, hAβval, Valuation.map_mul,
      Valuation.map_inv, htval]
    exact mul_inv_cancel₀ hvb
  have hwsub : Valued.v ((w : Q.adicCompletion K) - 1) ≤
      WithZero.exp (-(((M + e : ℕ) : ℤ))) := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, hAβval]
    refine val_mul_inv_sub_one_le (v := Valued.v) (a := algebraMap K (Q.adicCompletion K) t)
      (b := (b : Q.adicCompletion K))
      (δ := WithZero.exp (-(((M + e : ℕ) : ℤ)))) hvb hδ1 ?_
    have h2 : Valued.v ((b : Q.adicCompletion K) - algebraMap K (Q.adicCompletion K) t) =
        Valued.v (algebraMap K (Q.adicCompletion K) t - (b : Q.adicCompletion K)) := by
      rw [← neg_sub, Valuation.map_neg]
    rw [h2]
    exact htclose
  -- the deep principal unit `b / t` is a `p`-th power
  obtain ⟨c, hc⟩ := adicCompletion_pow_of_deep_principalUnit K Q D p he hwval hwsub
  refine ⟨Units.mk0 t ht0, c, ?_⟩
  rw [← hAβ]
  rw [hc]
  rw [hw, ← mul_assoc]
  exact mul_inv_cancel_comm Aβ b

end Work.SSGRoute
