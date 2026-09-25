import Mathlib
import Submission.NK.NUV2.RouteC.val_sequence
import Submission.NK.NUV2.RouteC.field_units_H1_vanish

/-!
# `ord_* : H²(G, L_qˣ) → H²(G, ℤ)` out of the long exact sequence

The LES of the valuation sequence `0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0`
(`NK.NUV2.RouteC.valSeq_shortExact`) gives the exactness of

`H²(G, 𝒪_qˣ) --→ H²(G, L_qˣ) --→ H²(G, ℤ) --→ H³(G, 𝒪_qˣ)`

via `groupCohomology.mapShortComplex₂_exact` (the middle piece) and
`groupCohomology.mapShortComplex₃_exact` (the right piece).  With the vanishings
`H²(G, 𝒪_qˣ) = 0` and `H³(G, 𝒪_qˣ) = 0` (`NK.NUV2.RouteC.unramified_units_vanish`), the map
`ord_*` induced by `valSeqG` is injective (its kernel is the range of the vanishing group) and
surjective (its range is the kernel of a map out of `H²(G, ℤ)` into a vanishing group).  It is
therefore an isomorphism — the canonical unramified invariant, composed with
`Commons…groupCohomology_two_int_iso_one_qmodz` and evaluation at Frobenius.
-/

open IsDedekindDomain
open CategoryTheory

set_option maxHeartbeats 1600000

namespace NK.NUV2.RouteC

/-- **Injectivity of `ord_* : H²(G, L_qˣ) → H²(G, ℤ)`.** -/
theorem ord_injective
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    Function.Injective ⇑((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).g) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  have hex : (groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).Exact :=
    groupCohomology.mapShortComplex₂_exact (valSeq_shortExact Q q hq h1) 2
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
  haveI hsub : Subsingleton ↑((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).X₁) :=
    (unramified_units_vanish Q q hq h1).2.1
  have hzero : LinearMap.range
      ((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).f.hom) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨z, rfl⟩
    have hz0 : z = 0 := @Subsingleton.elim _ hsub z 0
    rw [hz0, map_zero]
  intro a b hab
  have hmem : a - b ∈ LinearMap.ker
      ((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).g.hom) := by
    rw [LinearMap.mem_ker, map_sub, hab, sub_self]
  have hker : LinearMap.ker
      ((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).g.hom) = ⊥ :=
    le_antisymm (hzero ▸ hex) bot_le
  rw [hker, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- **Surjectivity of `ord_* : H²(G, L_qˣ) → H²(G, ℤ)`.**

Exactness of `H²(G, L_qˣ) → H²(G, ℤ) → H³(G, 𝒪_qˣ)` together with `H³(G, 𝒪_qˣ) = 0`
(`NK.NUV2.RouteC.unramified_units_vanish`). -/
theorem ord_surjective
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    Function.Surjective ⇑((groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).g) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  have hX : (valSeq Q q hq h1).ShortExact := valSeq_shortExact Q q hq h1
  have hex : (groupCohomology.mapShortComplex₃ hX (show 2 + 1 = 3 from rfl)).Exact :=
    groupCohomology.mapShortComplex₃_exact hX (show 2 + 1 = 3 from rfl)
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
  haveI hsub : Subsingleton ↑((groupCohomology.mapShortComplex₃ hX
      (show 2 + 1 = 3 from rfl)).X₃) :=
    (unramified_units_vanish Q q hq h1).2.2
  have hzero : (groupCohomology.mapShortComplex₃ hX
      (show 2 + 1 = 3 from rfl)).g.hom = 0 := by
    apply LinearMap.ext
    intro x
    exact @Subsingleton.elim _ hsub _ 0
  have htop : LinearMap.ker ((groupCohomology.mapShortComplex₃ hX
      (show 2 + 1 = 3 from rfl)).g.hom) = ⊤ := by
    rw [hzero, LinearMap.ker_zero]
  rw [htop] at hex
  have hrange : LinearMap.range ((groupCohomology.mapShortComplex₃ hX
      (show 2 + 1 = 3 from rfl)).f.hom) = ⊤ := le_antisymm le_top hex
  have hiff : (groupCohomology.mapShortComplex₃ hX (show 2 + 1 = 3 from rfl)).f.hom
      = (groupCohomology.mapShortComplex₂ (valSeq Q q hq h1) 2).g.hom := rfl
  rw [hiff] at hrange
  exact LinearMap.range_eq_top.mp hrange

end NK.NUV2.RouteC
