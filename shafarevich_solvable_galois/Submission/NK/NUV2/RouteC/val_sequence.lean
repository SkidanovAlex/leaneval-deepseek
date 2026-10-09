import Mathlib
import Submission.NK.NUV2.RouteC.unramified_invariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The valuation sequence `0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0` of `Gal(L_q/K_Q)`-modules

For `q | Q` unramified, the valuation `Valued.v` is `Gal(L_q/K_Q)`-invariant
(`NK.NUV2.RouteC.val_algEquiv_eq`), so the valuation, read on the units
`ord = WithZero.log ∘ Valued.v : L_qˣ → ℤ`, is a homomorphism of `Gal(L_q/K_Q)`-modules for the
*trivial* action on `ℤ` (`NK.NUV2.RouteC.ord_algEquiv_eq`).  This file builds the resulting short
exact sequence of `Rep ℤ G` objects; its long exact sequence (Mathlib's `groupCohomology.δ` and
`groupCohomology.isIso_δ_of_isZero`) is what turns the vanishings
`H^i(G, 𝒪_qˣ) = 0` (`NK.NUV2.RouteC.unramified_units_vanish`) into the canonical unramified
invariant `H²(G, L_qˣ) ≅ H²(G, ℤ) ≅ ℤ/[L_q : K_Q]`.

The verification follows the template of the commons' coefficient sequence `ℤ → ℚ → ℚ/ℤ`
(`Submission/Commons/RepresentationTheory/GroupCohomology/groupCohomology_two_int_iso_one_qmodz.lean`):
the elements of a `Rep ℤ G` are checked elementwise, and `Exact` is obtained through the commons'
criterion `shortExact_of_mono_epi_elementwise`, which exists precisely because at `k = ℤ` the
`Module ℤ`-structure on a `Rep` is a diamond and the `forget₂`-based exactness recipe is not
synthesizable.
-/

open IsDedekindDomain
open scoped WithZero
open CategoryTheory

set_option maxHeartbeats 1600000

namespace NK.NUV2.RouteC

/-- **The three objects of the valuation sequence.**

* `𝒪_qˣ`, with its Galois action (`Commons…adicIntegersUnitsRep`);
* `L_qˣ`, with the canonical Galois action (`Rep.ofAlgebraAutOnUnits`);
* `ℤ` with trivial action (`Rep.trivial`). -/
noncomputable abbrev valSeqUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Rep ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact Rep.of (Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq)

/-- The middle object `L_qˣ`. -/
noncomputable abbrev valSeqMiddle (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Rep ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)

/-- The right object `ℤ` (trivial action). -/
noncomputable abbrev valSeqTriv (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Rep ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact Rep.trivial ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ℤ

/-- **The units of `𝒪_q` have valuation `1`.** -/
theorem val_eq_one_of_units
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (z : (q.adicCompletionIntegers L)ˣ) :
    Valued.v (R := q.adicCompletion L)
      ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) = 1 := by
  let coe : (q.adicCompletionIntegers L)ˣ →* q.adicCompletion L :=
    (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom.comp
      (Units.coeHom (q.adicCompletionIntegers L))
  have hcoe_apply : ∀ w : (q.adicCompletionIntegers L)ˣ,
      coe w = ((w : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := fun w => rfl
  have hle : Valued.v (R := q.adicCompletion L)
      ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers L) L q).mp z.1.2
  have hle' : Valued.v (R := q.adicCompletion L)
      (((z⁻¹ : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) ≤ 1 :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers L) L q).mp (z⁻¹).1.2
  have hprod : Valued.v (R := q.adicCompletion L)
        ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) *
      Valued.v (R := q.adicCompletion L)
        (((z⁻¹ : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) = 1 := by
    rw [← Valuation.map_mul, ← hcoe_apply z, ← hcoe_apply (z⁻¹), ← map_mul coe,
      mul_inv_cancel z, map_one, map_one]
  have hge : 1 ≤ Valued.v (R := q.adicCompletion L)
      ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
    calc 1 = Valued.v (R := q.adicCompletion L)
            ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) *
          Valued.v (R := q.adicCompletion L)
            (((z⁻¹ : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) := hprod.symm
      _ ≤ Valued.v (R := q.adicCompletion L)
            ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) * 1 :=
          mul_le_mul_of_nonneg_left hle' zero_le
      _ = Valued.v (R := q.adicCompletion L)
            ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := mul_one _
  exact le_antisymm hle hge

section Seq

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The additive homomorphism `ord = WithZero.log ∘ Valued.v` on `L_qˣ`.

It is a *global* definition (not a local `have`) on purpose: the intertwining identity below is
`rfl`-level once `ord` can be unfolded, and a local `have`-bound map is **not** unfolded by the defeq
check of `rfl`/`exact`/`show` (this cost a session). -/
private noncomputable def ordHom {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Additive (q.adicCompletion L)ˣ →+ ℤ :=
  { toFun := fun x => WithZero.log (Valued.v (R := q.adicCompletion L)
      ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))
    map_zero' := by
      show WithZero.log (Valued.v (R := q.adicCompletion L)
        ((Additive.toMul (0 : Additive (q.adicCompletion L)ˣ) : (q.adicCompletion L)ˣ) :
          q.adicCompletion L)) = 0
      rw [show Additive.toMul (0 : Additive (q.adicCompletion L)ˣ) = (1 : (q.adicCompletion L)ˣ)
          from rfl,
        show (((1 : (q.adicCompletion L)ˣ)) : q.adicCompletion L) = 1 from rfl,
        Valuation.map_one, WithZero.log_one]
    map_add' := fun x y => by
      show WithZero.log (Valued.v (R := q.adicCompletion L)
          ((Additive.toMul (x + y) : (q.adicCompletion L)ˣ) : q.adicCompletion L)) =
        WithZero.log (Valued.v (R := q.adicCompletion L)
          ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L)) +
        WithZero.log (Valued.v (R := q.adicCompletion L)
          ((Additive.toMul y : (q.adicCompletion L)ˣ) : q.adicCompletion L))
      rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
        show ((((Additive.toMul x * Additive.toMul y : (q.adicCompletion L)ˣ))) : q.adicCompletion L)
          = (((Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L) *
            (((Additive.toMul y : (q.adicCompletion L)ˣ)) : q.adicCompletion L) from rfl,
        Valuation.map_mul,
        WithZero.log_mul
          ((Valuation.ne_zero_iff (Valued.v (R := q.adicCompletion L))).mpr
            (Units.ne_zero (Additive.toMul x)))
          ((Valuation.ne_zero_iff (Valued.v (R := q.adicCompletion L))).mpr
            (Units.ne_zero (Additive.toMul y)))] }

/-- **The valuation `ord = WithZero.log ∘ Valued.v`**, as a morphism of `Gal(L_q/K_Q)`-modules
with trivial action on `ℤ`. -/
noncomputable def valSeqG
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    valSeqMiddle K L Q q hq ⟶ valSeqTriv K L Q q hq := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  refine Rep.ofHom ⟨(ordHom q).toIntLinearMap, ?_⟩
  intro γ
  ext x
  simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply]
  rw [Rep.trivial_ρ γ, LinearMap.id_apply]
  show WithZero.log (Valued.v (R := q.adicCompletion L)
      (((γ • Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L))
    = WithZero.log (Valued.v (R := q.adicCompletion L)
      ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))
  rw [show (((γ • Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L)
      = γ ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L) from rfl]
  exact ord_algEquiv_eq Q q hq h1 γ (Additive.toMul x)

/-- The inclusion `(𝒪_q)ˣ →* (L_q)ˣ`, as a global definition (see the remark on `ordHom`). -/
private noncomputable def coeUnitsHom {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (q.adicCompletionIntegers L)ˣ →* (q.adicCompletion L)ˣ :=
  Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom

/-- The underlying additive map of the inclusion `𝒪_qˣ → L_qˣ`. -/
private noncomputable def coeAddHom {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Additive (q.adicCompletionIntegers L)ˣ →+ Additive (q.adicCompletion L)ˣ :=
  { toFun := fun x => Additive.ofMul (coeUnitsHom q (Additive.toMul x))
    map_zero' := rfl
    map_add' := fun x y => by
      show Additive.ofMul (coeUnitsHom q (Additive.toMul (x + y))) =
        Additive.ofMul (coeUnitsHom q (Additive.toMul x)) +
          Additive.ofMul (coeUnitsHom q (Additive.toMul y))
      rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
      rfl }

/-- **The inclusion `𝒪_qˣ → L_qˣ`**, as a morphism of `Gal(L_q/K_Q)`-modules. -/
noncomputable def valSeqF
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    valSeqUnits K L Q q hq ⟶ valSeqMiddle K L Q q hq := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  refine Rep.ofHom ⟨(coeAddHom q).toIntLinearMap, ?_⟩
  intro γ
  ext x
  simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply]
  have hunits : Additive.toMul ((coeAddHom q).toIntLinearMap
        (((Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq) γ) x))
      = γ • Additive.toMul ((coeAddHom q).toIntLinearMap x) := by
    show coeUnitsHom q (γ • Additive.toMul x) = γ • coeUnitsHom q (Additive.toMul x)
    apply Units.ext
    rw [show (((coeUnitsHom q (γ • Additive.toMul x) : (q.adicCompletion L)ˣ)) :
        q.adicCompletion L)
        = γ (((Additive.toMul x : (q.adicCompletionIntegers L)ˣ)) : q.adicCompletion L) from
          Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep_apply_coe Q q hq γ
            (Additive.toMul x)]
    rfl
  rw [hunits]
  rfl

/-- **The composition of the two maps of the valuation sequence is zero.** -/
theorem valSeq_comp
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    valSeqF Q q hq ≫ valSeqG Q q hq h1 = 0 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext x
  show WithZero.log (Valued.v (R := q.adicCompletion L)
      ((coeUnitsHom q (Additive.toMul x) : (q.adicCompletion L)ˣ) : q.adicCompletion L)) = 0
  rw [show (((coeUnitsHom q (Additive.toMul x) : (q.adicCompletion L)ˣ)) : q.adicCompletion L)
      = (((Additive.toMul x : (q.adicCompletionIntegers L)ˣ)) : q.adicCompletion L) from rfl,
    val_eq_one_of_units Q q hq (Additive.toMul x), WithZero.log_one]

/-- **The valuation sequence** `0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0` of `Gal(L_q/K_Q)`-modules
(trivial action on `ℤ`), for `q | Q` unramified. -/
noncomputable def valSeq
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    ShortComplex (Rep ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  exact ShortComplex.mk (valSeqF Q q hq) (valSeqG Q q hq h1) (valSeq_comp Q q hq h1)

/-- **The valuation sequence is short exact.** -/
theorem valSeq_shortExact
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ :=
      Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
    (valSeq Q q hq h1).ShortExact := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := ℤ) (G := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    (valSeq Q q hq h1) ?_ ?_ ?_
  · rw [Rep.mono_iff_injective]
    intro x y hxy
    have h2 : (((coeUnitsHom q (Additive.toMul x) : (q.adicCompletion L)ˣ)) :
        q.adicCompletion L)
        = (((coeUnitsHom q (Additive.toMul y) : (q.adicCompletion L)ˣ)) :
            q.adicCompletion L) :=
      congrArg (fun w : (q.adicCompletion L)ˣ => ((w : (q.adicCompletion L)ˣ) :
        q.adicCompletion L)) hxy
    rw [show (((coeUnitsHom q (Additive.toMul x) : (q.adicCompletion L)ˣ)) :
          q.adicCompletion L)
        = (((Additive.toMul x : (q.adicCompletionIntegers L)ˣ)) : q.adicCompletion L) from rfl,
      show (((coeUnitsHom q (Additive.toMul y) : (q.adicCompletion L)ˣ)) :
          q.adicCompletion L)
        = (((Additive.toMul y : (q.adicCompletionIntegers L)ˣ)) : q.adicCompletion L) from rfl]
      at h2
    have h3 : Additive.toMul x = Additive.toMul y := by
      apply Units.ext
      apply Subtype.ext
      exact h2
    exact Additive.toMul.injective h3
  · rw [Rep.epi_iff_surjective]
    intro n
    obtain ⟨x, hx⟩ := Commons.RingTheory.Henselian.adicCompletion_valued_surjective (K := L) q
      (WithZero.exp (show ℤ from n))
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx
      exact WithZero.exp_ne_zero hx.symm
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    show WithZero.log (Valued.v (R := q.adicCompletion L)
      (((Units.mk0 x hx0 : (q.adicCompletion L)ˣ)) : q.adicCompletion L)) = n
    rw [show (((Units.mk0 x hx0 : (q.adicCompletion L)ˣ)) : q.adicCompletion L) = x from rfl,
      hx, WithZero.log_exp]
  · intro x hx
    have hx' : Valued.v (R := q.adicCompletion L)
        ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 :=
      (ord_eq_zero_iff Q q hq (Additive.toMul x)).mp hx
    have hne : ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L) ≠ 0 :=
      Units.ne_zero (Additive.toMul x)
    have hmem : ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L)
        ∈ q.adicCompletionIntegers L :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (NumberField.RingOfIntegers L) L q).mpr (le_of_eq hx')
    have hmem_inv : (((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))⁻¹
        ∈ q.adicCompletionIntegers L :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (NumberField.RingOfIntegers L) L q).mpr (le_of_eq (by rw [map_inv₀, hx', inv_one]))
    let u : (q.adicCompletionIntegers L)ˣ :=
      ⟨⟨((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L), hmem⟩,
        ⟨(((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))⁻¹, hmem_inv⟩,
        Subtype.ext (by
          change ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L) *
            (((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))⁻¹
            = (1 : q.adicCompletion L)
          exact mul_inv_cancel₀ hne),
        Subtype.ext (by
          change (((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L))⁻¹ *
            ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L)
            = (1 : q.adicCompletion L)
          exact inv_mul_cancel₀ hne)⟩
    refine ⟨Additive.ofMul u, ?_⟩
    have hxeq : coeUnitsHom q u = Additive.toMul x := by
      apply Units.ext
      rfl
    exact congrArg Additive.ofMul hxeq

end Seq

end NK.NUV2.RouteC
