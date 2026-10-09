import Mathlib
import Submission.Work.SSGRoute.LocalFieldArith.Prelude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Deep principal units of a `𝔭`-adic completion are `p`-th powers

For a number field `K`, a finite prime `𝔭`, a prime `p` and the level-`M` exponential/logarithm
`D` of `κ = 𝔭.adicCompletion K` (`NK.LocalInputs.PowerQuotient.LogData 𝔭 M`), every principal
unit at the deeper level `M + e` is a `p`-th power of a unit of `𝔭.adicCompletionIntegers K`,
where `e : ℕ` is the exponent of `p` in the valuation of `κ`, i.e. `v p = exp (-e)`.

Indeed the `p`-adic logarithm identifies the level-`M` principal units with the additive group
`𝔪 ^ M`, where the `p`-th power map becomes multiplication by `p`; multiplication by `p` maps
`𝔪 ^ M` onto `𝔪 ^ (M + e)`, so every element of the latter is a `p`-th power.
-/

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute.LocalFieldArith

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem principalUnits_deep_mem_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M : ℕ} (D : NK.LocalInputs.PowerQuotient.LogData 𝔭 M) (p : ℕ) [Fact p.Prime] {e : ℕ}
    (hpe : (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
        ((p : ℕ) : 𝔭.adicCompletion K) = WithZero.exp (-(e : ℤ)))
    {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ NK.LocalInputs.PowerQuotient.pu 𝔭 (M + e)) :
    ∃ y : (𝔭.adicCompletionIntegers K)ˣ, y ^ p = u := by
  have hp : p.Prime := Fact.out
  have hchar : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have hpκ_ne : ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  -- valuation of p
  have hpevv : NK.LocalInputs.PowerQuotient.vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := hpe
  -- membership in the deep principal units
  have huv : NK.LocalInputs.PowerQuotient.vv 𝔭
      (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) - 1)
      ≤ WithZero.exp (-(((M + e : ℕ) : ℤ))) :=
    (NK.LocalInputs.PowerQuotient.mem_pu_iff_val 𝔭 (M + e) u).mp hu
  have hExp_le : (WithZero.exp (-(((M + e : ℕ) : ℤ))) : WithZero (Multiplicative ℤ))
      ≤ WithZero.exp (-(M : ℤ)) := by
    apply WithZero.exp_le_exp.mpr
    push_cast
    omega
  have hDisk : NK.LocalInputs.PowerQuotient.Disk 𝔭 M
      (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) := by
    rw [NK.LocalInputs.PowerQuotient.Disk]
    exact le_trans huv hExp_le
  -- the logarithm of u
  have hlogval : NK.LocalInputs.PowerQuotient.vv 𝔭
        (D.log (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)))
      = NK.LocalInputs.PowerQuotient.vv 𝔭
        (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) - 1) := D.val_log _ hDisk
  have hlogle : NK.LocalInputs.PowerQuotient.vv 𝔭
        (D.log (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)))
      ≤ WithZero.exp (-(((M + e : ℕ) : ℤ))) := by rw [hlogval]; exact huv
  -- x = log u / p
  set x : 𝔭.adicCompletion K :=
    D.log (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) /
      ((p : ℕ) : 𝔭.adicCompletion K) with hx
  have hMe : (WithZero.exp (-(((M + e : ℕ) : ℤ))) : WithZero (Multiplicative ℤ))
      = WithZero.exp (-(M : ℤ)) * WithZero.exp (-(e : ℤ)) := by
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring
  have hxval : NK.LocalInputs.PowerQuotient.vv 𝔭 x ≤ WithZero.exp (-(M : ℤ)) := by
    rw [hx, Valuation.map_div, hpevv]
    rw [div_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)]
    rw [← hMe]
    exact hlogle
  have hxEDisk : NK.LocalInputs.PowerQuotient.EDisk 𝔭 M x := hxval
  set y : 𝔭.adicCompletion K := D.exp x with hy
  have hysub : NK.LocalInputs.PowerQuotient.vv 𝔭 (y - 1)
      = NK.LocalInputs.PowerQuotient.vv 𝔭 x := by
    rw [hy]; exact D.val_exp_sub_one x hxEDisk
  have hyDisk : NK.LocalInputs.PowerQuotient.Disk 𝔭 M y := by
    rw [NK.LocalInputs.PowerQuotient.Disk, hysub]; exact hxval
  have hyval : NK.LocalInputs.PowerQuotient.vv 𝔭 y = 1 :=
    NK.LocalInputs.PowerQuotient.disk_val_eq_one D.hM hyDisk
  have hy_mem : y ∈ 𝔭.adicCompletionIntegers K :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers K) K 𝔭).mpr (le_of_eq hyval)
  have hy_isUnit : IsUnit (⟨y, hy_mem⟩ : 𝔭.adicCompletionIntegers K) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hyval
  -- auxiliary: exp of natural multiples
  have hnat_val : ∀ n : ℕ, NK.LocalInputs.PowerQuotient.vv 𝔭
      ((n : ℕ) : 𝔭.adicCompletion K) ≤ 1 := by
    intro n; induction n with
    | zero => rw [Nat.cast_zero, Valuation.map_zero]; exact zero_le
    | succ k ih =>
      rw [Nat.cast_succ]
      refine Valuation.map_add_le (NK.LocalInputs.PowerQuotient.vv 𝔭) ih ?_
      rw [Valuation.map_one]
  have hnsmul_EDisk : ∀ n : ℕ, NK.LocalInputs.PowerQuotient.EDisk 𝔭 M (n • x) := by
    intro n
    show NK.LocalInputs.PowerQuotient.vv 𝔭 (n • x) ≤ WithZero.exp (-(M : ℤ))
    rw [nsmul_eq_mul, Valuation.map_mul]
    calc NK.LocalInputs.PowerQuotient.vv 𝔭 ((n : ℕ) : 𝔭.adicCompletion K)
            * NK.LocalInputs.PowerQuotient.vv 𝔭 x
        ≤ 1 * WithZero.exp (-(M : ℤ)) := mul_le_mul' (hnat_val n) hxval
      _ = WithZero.exp (-(M : ℤ)) := one_mul _
  have hexp_nsmul : ∀ n : ℕ, D.exp (n • x) = (D.exp x) ^ n := by
    intro n; induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact D.exp_zero
    | succ k ih =>
      rw [succ_nsmul, D.exp_add _ _ (hnsmul_EDisk k) hxEDisk, ih, pow_succ]
  refine ⟨hy_isUnit.unit, ?_⟩
  apply Units.ext
  apply Subtype.ext
  have key : (((hy_isUnit.unit : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) = y := by
    rw [IsUnit.unit_spec]
  calc (((hy_isUnit.unit ^ p : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K))
      = (((hy_isUnit.unit : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) ^ p := by
        rw [Units.val_pow_eq_pow_val]
        rfl
    _ = y ^ p := by rw [key]
    _ = (D.exp x) ^ p := by rw [hy]
    _ = D.exp (p • x) := (hexp_nsmul p).symm
    _ = D.exp (((p : ℕ) : 𝔭.adicCompletion K) * x) := by rw [nsmul_eq_mul]
    _ = D.exp (D.log (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K))) := by
        rw [hx, mul_div_cancel₀ _ hpκ_ne]
    _ = (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) := D.exp_log _ hDisk
    _ = ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) := rfl


end
end Work.SSGRoute.LocalFieldArith
