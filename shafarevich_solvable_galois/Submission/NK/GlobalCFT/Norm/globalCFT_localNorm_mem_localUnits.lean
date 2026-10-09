/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Norm
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local norm of a local unit is a local unit

Let `L / K` be a finite extension of number fields, `q` a nonzero prime of `𝓞 L` and `Q` a
nonzero prime of `𝓞 K` with `q` lying over `Q`.  The local norm
`N_{L_q/K_Q} : L_qˣ →* K_Qˣ` (`NK.GlobalCFT.Place.localNormFinite`) maps the group of local
units `𝒪_qˣ` into the group of local units `𝒪_Qˣ`.

The proof does not use the Galois case of the norm formula
(`Commons.NumberTheory.NumberField.Completion.norm_adicCompletionIntegers_mem`, which assumes
`IsGalois K L`).  Instead it uses the fact that `q.adicCompletionIntegers L` is the integral
closure of `Q.adicCompletionIntegers K` in `q.adicCompletion L`
(`isIntegralClosure_adicCompletionIntegers_extension`), that the norm of an integral element is
integral (`Algebra.isIntegral_norm`), and that a valuation ring is integrally closed in its
fraction field (`Valuation.Integers.isIntegral_iff_v_le_one`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField WithZero
open IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Norm

/-- **The norm of an integral element is integral.**  Let `q` be a nonzero prime of `𝓞 L` lying
over the nonzero prime `Q` of `𝓞 K`.  Viewing the local field `L_q = q.adicCompletion L` as an
extension of `K_Q = Q.adicCompletion K` via `adicCompletionMap`, the norm `N_{L_q/K_Q} x` of an
element `x` of the ring of integers of `L_q` lies in the ring of integers of `K_Q`. -/
theorem globalCFT_localNorm_adicCompletionIntegers_mem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {x : q.adicCompletion L} (hx : x ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L))) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
    Algebra.norm (Q.adicCompletion K) x ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q q hq)
  haveI hIC : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q q hq
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletionIntegers_adicCompletion
      Q q hq
  haveI hST2 : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxint : IsIntegral (Q.adicCompletionIntegers K) x :=
    (IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)).mpr ⟨⟨x, hx⟩, rfl⟩
  have hnormint : IsIntegral (Q.adicCompletionIntegers K) (Algebra.norm (Q.adicCompletion K) x) :=
    Algebra.isIntegral_norm (Q.adicCompletion K) hxint
  -- a valuation ring is integrally closed in its fraction field
  have hv : (Valued.v : Valuation (Q.adicCompletion K) ℤᵐ⁰).Integers (Q.adicCompletionIntegers K) :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun r =>
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K Q).mp r.2
      exists_of_le_one := fun r hr =>
        ⟨⟨r, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K Q).mpr hr⟩,
          rfl⟩ }
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K Q).mpr
    ((Valuation.Integers.isIntegral_iff_v_le_one hv).mp hnormint)

/-- The local norm `N_{L_q/K_Q}` maps the group of local units `𝒪_qˣ` of `L_q` into the group
of local units `𝒪_Qˣ` of `K_Q`. -/
theorem globalCFT_localNorm_mem_localUnits {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : q.asIdeal.LiesOver Q.asIdeal) {z : (q.adicCompletion L)ˣ}
    (hz : z ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q)) :
    NK.GlobalCFT.Place.localNormFinite q Q h z ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q h).toAlgebra
  -- membership in the local units is membership of the element and of its inverse in the ring
  -- of integers of the completion
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite] at hz
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite]
  constructor
  · have hcoe : ((NK.GlobalCFT.Place.localNormFinite q Q h z : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) = Algebra.norm (Q.adicCompletion K) (z : q.adicCompletion L) := rfl
    rw [hcoe]
    exact globalCFT_localNorm_adicCompletionIntegers_mem Q q h hz.1
  · -- the norm is multiplicative, so it suffices to apply the previous step to `z⁻¹`
    have hinv : (NK.GlobalCFT.Place.localNormFinite q Q h z)⁻¹ =
        NK.GlobalCFT.Place.localNormFinite q Q h z⁻¹ :=
      (map_inv (NK.GlobalCFT.Place.localNormFinite q Q h) z).symm
    rw [hinv]
    have hcoe : ((NK.GlobalCFT.Place.localNormFinite q Q h z⁻¹ : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K) = Algebra.norm (Q.adicCompletion K)
          ((z⁻¹ : (q.adicCompletion L)ˣ) : q.adicCompletion L) := rfl
    rw [hcoe]
    exact globalCFT_localNorm_adicCompletionIntegers_mem Q q h hz.2

end NK.GlobalCFT.Norm
