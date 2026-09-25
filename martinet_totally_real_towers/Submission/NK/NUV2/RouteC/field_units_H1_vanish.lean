import Mathlib
import Submission.NK.NUV2.RouteC.units_H1_vanish

/-!
# `H¹(Gal(L_q/K_Q), L_qˣ) = 0` (Hilbert 90 for the local field) — in progress

The second of the two "middle" vanishings of the long exact sequence of the valuation sequence
`0 → 𝒪_qˣ → L_qˣ →^{ord} ℤ → 0`.  The plan (and how far it got, so the next stretch is short):

* the generic cyclic reduction `NK.NUV2.RouteC.subsingleton_groupCohomology_one_of_h90` is applied
  with `A := Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)` (its carrier is
  `Additive (L_q)ˣ`) and a generator `g` of the cyclic group `G` (`h1 : e(q|Q) = 1` gives cyclicity);
* the integral Hilbert 90 of Layer 2 of `units_H1_vanish.lean` is replaced by the *field* level
  theorem `Commons.FieldTheory.Galois.hilbert90_cyclic`: given `x : Additive (L_q)ˣ` with
  `A.norm.hom x = 0`, the norm of the representation is the product of the conjugates
  (`Representation.norm_ofMulDistribMulAction_eq`), so `∏ γ, γ • (Additive.toMul x) = 1`, and pushing
  that product through `Units.coeHom` plus `Algebra.norm_eq_prod_automorphisms` and the injectivity of
  `algebraMap` gives `Algebra.norm K_Q ↑(Additive.toMul x) = 1`; then `hilbert90_cyclic` produces
  `z : L_qˣ` with `↑(Additive.toMul x) = g ↑z / ↑z`;
* the witness is `Additive.ofMul z`, and the only remaining identity is the units-level statement
  `(g • z) / z = Additive.toMul x` (then `Rep.sub_hom` + the `rfl`-bridge
  `ofMul a - ofMul b = ofMul (a/b)` closes the goal).

**Where the attempt stopped (two coercion snags, both of the kind already diagnosed in
`val_sequence.lean`):**

1. the unit product `∏ γ, ↑(γ • u)` must be rewritten into the `Units.coeHom` form *before*
   `map_prod` (a `show … from rfl` bridge), and the `↑1` on the other side then needs
   `Units.val_one`, not `map_one` — this part is worked out;
2. the final step `rw [show ↑(g • z) = g ↑z from rfl, hz]` leaves
   `g ↑z = (g ↑z / ↑z) * ↑z`, and neither `div_mul_cancel₀` nor `field_simp` closed it in the form
   Lean prints — the same `.toCompletion`/coercion display issue as in `valSeqF`, whose *working*
   remedy was: prove the units-level identity as a local `have` in the form
   `show ↑u = ↑v`, `rw` the `rfl`-bridges, and close with `rfl` (rather than fighting the printed
   goal).  Applying exactly that recipe here is the first move of the next stretch; the mathematics
   (`hilbert90_cyclic`) is already in place above.
-/

open IsDedekindDomain
open CategoryTheory

set_option maxHeartbeats 1600000

namespace NK.NUV2.RouteC

/-- `algebraMap` of a field extension is injective (local copy, since the one in
`units_H1_vanish.lean` is private). -/
private theorem algebraMap_injective_of_field' {K L : Type*} [Field K] [Field L] [Algebra K L] :
    Function.Injective (algebraMap K L) := by
  intro a b h
  by_contra hne
  have h1 : algebraMap K L (a - b) = 0 := by rw [map_sub, h, sub_self]
  have h2 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h3 : algebraMap K L (a - b) * algebraMap K L ((a - b)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h2, map_one]
  rw [h1, zero_mul] at h3
  exact zero_ne_one h3

/-- **`H¹(Gal(L_q/K_Q), L_qˣ) = 0`** for `q | Q` unramified (Hilbert 90 over the local field). -/
theorem field_units_H1_vanish
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K)
      (q.adicCompletion L)) 1) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  letI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  letI hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q q hq h1
  letI hcg : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    IsCyclic.commGroup
  letI hfint : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
  refine (subsingleton_groupCohomology_one_of_h90
    (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) (q.adicCompletion L)) g hg) ?_
  intro x hx
  have hprod : (∏ γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      γ • (Additive.toMul x : (q.adicCompletion L)ˣ)) = 1 := by
    have h := hx
    rw [Rep.norm_apply] at h
    change (Representation.ofMulDistribMulAction
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletion L)ˣ).norm x = 0 at h
    have h2 := Representation.norm_ofMulDistribMulAction_eq
      (G := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (M := (q.adicCompletion L)ˣ) x
    rw [h] at h2
    simpa using h2.symm
  have hbridge : ∀ γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      (((γ • (Additive.toMul x : (q.adicCompletion L)ˣ) : (q.adicCompletion L)ˣ)) :
        q.adicCompletion L)
        = γ (((Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L) := fun γ => rfl
  have hprod_field : (∏ γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      γ (((Additive.toMul x : (q.adicCompletion L)ˣ)) : q.adicCompletion L)) = 1 := by
    rw [Finset.prod_congr rfl (fun γ _ => (hbridge γ).symm)]
    have h := congrArg (fun w : (q.adicCompletion L)ˣ =>
      ((w : (q.adicCompletion L)ˣ) : q.adicCompletion L)) hprod
    rw [show (((∏ γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
          γ • (Additive.toMul x : (q.adicCompletion L)ˣ) : (q.adicCompletion L)ˣ)) :
          q.adicCompletion L)
        = Units.coeHom (q.adicCompletion L)
          (∏ γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
            γ • (Additive.toMul x : (q.adicCompletion L)ˣ)) from rfl,
      map_prod (Units.coeHom (q.adicCompletion L))
        (fun γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L =>
          γ • (Additive.toMul x : (q.adicCompletion L)ˣ)) Finset.univ,
      Units.val_one] at h
    exact h
  have hnorm : Algebra.norm (Q.adicCompletion K)
      ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 := by
    apply algebraMap_injective_of_field' (K := Q.adicCompletion K) (L := q.adicCompletion L)
    rw [Algebra.norm_eq_prod_automorphisms, map_one]
    exact hprod_field
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg
  obtain ⟨z, hz⟩ := (Commons.FieldTheory.Galois.hilbert90_cyclic
      (K := Q.adicCompletion K) (L := q.adicCompletion L) g htop
      ((Additive.toMul x : (q.adicCompletion L)ˣ) : q.adicCompletion L)).mp hnorm
  refine ⟨Additive.ofMul z, ?_⟩
  have hmul : (g • z) = (Additive.toMul x : (q.adicCompletion L)ˣ) * z := by
    apply Units.ext
    show (((g • z : (q.adicCompletion L)ˣ)) : q.adicCompletion L)
      = ((((Additive.toMul x : (q.adicCompletion L)ˣ)) * z : (q.adicCompletion L)ˣ) :
        q.adicCompletion L)
    rw [show (((g • z : (q.adicCompletion L)ˣ)) : q.adicCompletion L)
        = g (((z : (q.adicCompletion L)ˣ)) : q.adicCompletion L) from rfl,
      Units.val_mul, hz,
      div_mul_cancel₀ (g (((z : (q.adicCompletion L)ˣ)) : q.adicCompletion L))
        (Units.ne_zero z)]
  have hunits : (g • z) / z = (Additive.toMul x : (q.adicCompletion L)ˣ) := by
    rw [hmul, mul_div_cancel_right]
  rw [Rep.sub_hom]
  show (Additive.ofMul (g • z) : Additive (q.adicCompletion L)ˣ) - Additive.ofMul z = x
  rw [show (Additive.ofMul (g • z) : Additive (q.adicCompletion L)ˣ) - Additive.ofMul z
      = Additive.ofMul ((g • z) / z) from rfl, hunits]
  rfl

end NK.NUV2.RouteC
