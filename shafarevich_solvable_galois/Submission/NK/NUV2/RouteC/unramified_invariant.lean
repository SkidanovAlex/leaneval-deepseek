import Mathlib
import Submission.NK.NUV2.RouteC.CommonsUnramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical unramified invariant: the valuation is Galois-invariant

The first rung of the *canonical* unramified invariant of local class field theory
(Milne, *CFT*, I.1 / III.1): the valuation `Valued.v : L_q → ℤᵐ⁰` is invariant under
`Gal(L_q/K_Q)` when `q | Q` is unramified.  This is what turns
`1 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0` into a sequence of `Gal(L_q/K_Q)`-modules with *trivial* action on
`ℤ`, whose long exact sequence produces the isomorphism
`H²(Gal(L_q/K_Q), L_qˣ) ≅ H²(Gal(L_q/K_Q), ℤ) ≅ ℤ/[L_q : K_Q]` — the invariant map.

## The argument

* on the units of `𝒪_q` the valuation is `1` (`val_eq_one_of_units`), and the Galois action on them
  is the Galois action on the field (`adicIntegersUnitsRep_apply_coe`), so `Valued.v` is
  Galois-invariant *on units*;
* for general `x ≠ 0` one scales: `Valued.v` is surjective (`adicCompletion_valued_surjective`), so
  there is `k ∈ K_Q` with `Valued.v (algebraMap k) = Valued.v x` (here `e(q|Q) = 1` enters, through
  `valuation_completion_liesOver`); then `x / algebraMap k` is a *unit* of `𝒪_q`, and `γ` fixes
  `algebraMap k` (`AlgEquiv.commutes`), so the case of general `x` follows from the unit case.
-/

open IsDedekindDomain
open scoped WithZero

set_option maxHeartbeats 800000

namespace NK.NUV2.RouteC

/-- **The valuation is invariant under `Gal(L_q/K_Q)` for an unramified `q | Q`.**

This is the `G`-equivariance that makes `1 → 𝒪_qˣ → L_qˣ → ℤ → 0` a sequence of
`Gal(L_q/K_Q)`-modules with trivial action on `ℤ`, i.e. the input of the canonical unramified
invariant `H²(Gal(L_q/K_Q), L_qˣ) ≅ ℤ/[L_q : K_Q]`. -/
theorem val_algEquiv_eq
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
    ∀ (γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) (x : q.adicCompletion L),
      Valued.v (R := q.adicCompletion L) (γ x) = Valued.v (R := q.adicCompletion L) x := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  letI hact : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (↥(q.adicCompletionIntegers L))ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsUnitsAction Q q hq
  -- the units of `𝒪_q` have valuation one
  have hval_one : ∀ z : (q.adicCompletionIntegers L)ˣ,
      Valued.v (R := q.adicCompletion L)
        ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) = 1 := by
    intro z
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
  -- the Galois action on units preserves the valuation
  have hunit : ∀ (γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (z : (q.adicCompletionIntegers L)ˣ),
      Valued.v (R := q.adicCompletion L)
          (γ ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L))
        = Valued.v (R := q.adicCompletion L)
          ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
    intro γ z
    have hcoe : γ ((z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
        = ((γ • z : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
      have h2 := Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep_apply_coe
        Q q hq γ z
      rw [show Additive.toMul
          ((Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep Q q hq) γ
            (Additive.ofMul z)) = γ • z from rfl] at h2
      exact h2.symm
    rw [hcoe, hval_one (γ • z), hval_one z]
  -- the ramification index in the form used by `valuation_completion_liesOver`
  have he : Q.asIdeal.ramificationIdx' q.asIdeal = 1 := by
    haveI := hq
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := Q.asIdeal) (q := q.asIdeal) Q.ne_bot]
    exact h1
  have hval_map : ∀ y : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) y)
        = Valued.v (R := Q.adicCompletion K) y := by
    intro y
    rw [show algebraMap (Q.adicCompletion K) (q.adicCompletion L) y
        = Commons.RingTheory.Henselian.adicCompletionMap Q q hq y from rfl,
      Commons.RingTheory.Henselian.valuation_completion_liesOver Q q hq y, he, pow_one]
  intro γ x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨k, hk⟩ := Commons.RingTheory.Henselian.adicCompletion_valued_surjective Q
    (Valued.v (R := q.adicCompletion L) x)
  set a : q.adicCompletion L := algebraMap (Q.adicCompletion K) (q.adicCompletion L) k with ha
  have hva : Valued.v (R := q.adicCompletion L) a = Valued.v (R := q.adicCompletion L) x := by
    rw [ha, hval_map k, hk]
  have hx0 : Valued.v (R := q.adicCompletion L) x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := q.adicCompletion L))).mpr hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hva
    exact hx0 hva.symm
  have hvu : Valued.v (R := q.adicCompletion L) (x / a) = 1 := by
    rw [map_div₀, hva, div_self hx0]
  have hne : x / a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  have hmem : x / a ∈ q.adicCompletionIntegers L :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers L)
      L q).mpr (le_of_eq hvu)
  have hmem_inv : (x / a)⁻¹ ∈ q.adicCompletionIntegers L :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers L)
      L q).mpr (le_of_eq (by rw [map_inv₀, hvu, inv_one]))
  let u : (q.adicCompletionIntegers L)ˣ :=
    ⟨⟨x / a, hmem⟩, ⟨(x / a)⁻¹, hmem_inv⟩,
      Subtype.ext (by
        change x / a * (x / a)⁻¹ = (1 : q.adicCompletion L)
        exact mul_inv_cancel₀ hne),
      Subtype.ext (by
        change (x / a)⁻¹ * (x / a) = (1 : q.adicCompletion L)
        exact inv_mul_cancel₀ hne)⟩
  have hu : ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) = x / a := rfl
  have hxa : x = ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) * a := by
    rw [hu]
    exact (div_mul_cancel₀ x ha0).symm
  calc Valued.v (R := q.adicCompletion L) (γ x)
      = Valued.v (R := q.adicCompletion L)
          (γ (((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) * a)) := by rw [hxa]
    _ = Valued.v (R := q.adicCompletion L)
          (γ ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) * γ a) := by rw [map_mul]
    _ = Valued.v (R := q.adicCompletion L)
          (γ ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) *
        Valued.v (R := q.adicCompletion L) (γ a) := by rw [Valuation.map_mul]
    _ = Valued.v (R := q.adicCompletion L)
          ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) *
        Valued.v (R := q.adicCompletion L) a := by
      rw [hunit γ u, show γ a = a from AlgEquiv.commutes γ k]
    _ = Valued.v (R := q.adicCompletion L)
          (((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) * a) := by
      rw [Valuation.map_mul]
    _ = Valued.v (R := q.adicCompletion L) x := by rw [← hxa]

/-- **`ord = WithZero.log ∘ Valued.v` is `Gal(L_q/K_Q)`-invariant on `L_qˣ`** for an unramified
`q | Q`.  This is the `ℤ`-equivariance (with the *trivial* action on `ℤ`) of the right-hand map of
the valuation sequence `0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0`; it is an immediate consequence of
`val_algEquiv_eq`. -/
theorem ord_algEquiv_eq
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (z : (q.adicCompletion L)ˣ),
      WithZero.log (Valued.v (R := q.adicCompletion L)
          (γ ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L)))
        = WithZero.log (Valued.v (R := q.adicCompletion L)
          ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro γ z
  rw [val_algEquiv_eq Q q hq h1 γ ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L)]

/-- **The valuation of a unit is `exp` of the `log` of the unit's `Valued.v`; in particular
`ord` classifies the units of `𝒪_q`.**  Recorded here because it is the elementwise content of the
exactness of `0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0` at the middle term. -/
theorem ord_eq_zero_iff
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (z : (q.adicCompletion L)ˣ) :
    WithZero.log (Valued.v (R := q.adicCompletion L)
        ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L)) = 0 ↔
      Valued.v (R := q.adicCompletion L)
        ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 := by
  constructor
  · intro h
    have hz0 : Valued.v (R := q.adicCompletion L)
        ((z : (q.adicCompletion L)ˣ) : q.adicCompletion L) ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v (R := q.adicCompletion L))).mpr (Units.ne_zero z)
    have h2 := WithZero.exp_log hz0
    rw [h, WithZero.exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, WithZero.log_one]

end NK.NUV2.RouteC
