import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.NKRayClassImports
import Submission.Work.SSGRoute.adicCompletion_pow_of_deep_principalUnit
import Submission.Work.SSGRoute.adicCompletion_units_mul_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Deep principal units of a `𝔭`-adic completion are `p`-th powers (modulus form)

For a number field `K`, a finite prime `𝔭` of `K` and a prime `p`, there is a modulus `N` such that
every global unit `x ∈ Kˣ` whose image in the completion `K_𝔭` is `1` modulo `𝔭^N` is a `p`-th power
in `K_𝔭ˣ`.

This is the local input "the modulus can be chosen so that `1 + 𝔭^N ⊆ (K_𝔭^×)^p`" of the Grünwald
escape correction (step 1 of `NOTE_escape_correction_route.md`).  The proof is the level-shifted
`p`-adic logarithm:

* `NK.LocalInputs.PowerQuotient.exists_logData` supplies the exponential/logarithm `D` of `K_𝔭` at
  some level `M ≥ 1` (`D : NK.LocalInputs.PowerQuotient.LogData 𝔭 M`);
* `Work.SSGRoute.exists_exp_neg_val_prime` supplies `e` with `v p = exp (-e)`;
* `Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow` (through
  `Work.SSGRoute.adicCompletion_pow_of_deep_principalUnit`) shows that an arbitrary unit `w` of the
  completion with `v w = 1` and `v (w - 1) ≤ exp (-(M + e))` is a `p`-th power;
* `v (w - 1) ≤ exp (-(M + e)) < 1` forces `v w = 1`, so the hypothesis of the previous point is
  automatic.

Hence `N := M + e` works.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open NumberField IsDedekindDomain
open scoped NumberField WithZero

theorem exists_pow_eq_of_isCongAt {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ N : ℕ, ∀ x : Kˣ, NK.NUV2.RouteB.IsCongAt K N 𝔭
        (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom x) →
      ∃ c : (𝔭.adicCompletion K)ˣ,
        c ^ p = Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom x := by
  -- the exponential/logarithm of the completion at some level `M ≥ 1`
  obtain ⟨M, hM, ⟨D⟩⟩ := NK.LocalInputs.PowerQuotient.exists_logData (K := K) 𝔭
  -- the exponent `e` of `p` in the value group of the completion
  obtain ⟨e, he⟩ := Work.SSGRoute.exists_exp_neg_val_prime (K := K) 𝔭 p
  refine ⟨M + e, fun x hx => ?_⟩
  set w : (𝔭.adicCompletion K)ˣ :=
    Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom x with hw
  have hN : 1 ≤ M + e := by omega
  -- `IsCongAt` is the statement that `w` lies on the logarithm disk at level `M + e`
  have hdisk : NK.LocalInputs.PowerQuotient.Disk 𝔭 (M + e) (w : 𝔭.adicCompletion K) := hx
  -- a point of the disk has valuation one
  have hval : Valued.v ((w : 𝔭.adicCompletion K)) = 1 :=
    NK.LocalInputs.PowerQuotient.disk_val_eq_one hN hdisk
  have hsub : Valued.v ((w : 𝔭.adicCompletion K) - 1)
      ≤ WithZero.exp (-(((M + e : ℕ) : ℤ))) := hx
  -- the deep principal unit `w` is a `p`-th power of a unit of the completion
  obtain ⟨c, hc⟩ :=
    Work.SSGRoute.adicCompletion_pow_of_deep_principalUnit K 𝔭 D p he hval hsub
  exact ⟨c, hc⟩

end Work.SSGRoute.GrunwaldEscapeCore
