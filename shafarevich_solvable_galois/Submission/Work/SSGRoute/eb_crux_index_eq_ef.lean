import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.E8Helpers
import Submission.Work.SSGRoute.eb_loc_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.SSGRoute

open CategoryTheory NumberField

/-- **Index of the `M`-stabiliser inside the `k`-stabiliser.**  For the tower `k ⊆ M ⊆ E` of
number fields with `M/k`, `E/k`, `E/M` finite Galois, a finite place `ŵ` of `E`, `W` the finite
place of `M` below it and `v₀` the finite place of `k` below `W`, the index of
`Stab_{Gal(E/M)}(ŵ)` (via `Work.SSGRoute.stabIncl`) in `Stab_{Gal(E/k)}(ŵ)` is the local degree
`[M_W : k_{v₀}] = e(W|v₀)·f(W|v₀)`.

Proof route.  `Work.SSGRoute.stabIncl ŵ` is injective (restriction of scalars, `AlgEquiv.ext`), so
`Nat.card ↥(range (stabIncl ŵ)) = Nat.card (Stab_{Gal(E/M)}(ŵ))`; `Subgroup.card_mul_index` then
gives `Nat.card (Stab_{Gal(E/M)}(ŵ)) * (range (stabIncl ŵ)).index = Nat.card (Stab_{Gal(E/k)}(ŵ))`.
`Work.SSGRoute.eb_stab_card_aux` identifies the two cardinalities with
`finrank (W.adicCompletion M) (ŵ.adicCompletion E)` and
`finrank (v₀.adicCompletion k) (ŵ.adicCompletion E)` respectively, which by the tower formula
`Module.finrank_mul_finrank` yields `(range (stabIncl ŵ)).index = finrank (v₀.adicCompletion k)
(W.adicCompletion M)`; the latter is `e(W|v₀)·f(W|v₀)` by
`Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`. -/
theorem eb_crux_index_eq_ef (k M E : Type) [Field k] [NumberField k] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra k M] [Algebra k E] [Algebra M E] [IsScalarTower k M E]
    [FiniteDimensional k M] [FiniteDimensional M E] [FiniteDimensional k E]
    [IsGalois k M] [IsGalois k E] [IsGalois M E]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hW : ŵ.asIdeal.LiesOver W.asIdeal) (hWv : W.asIdeal.LiesOver v₀.asIdeal) :
    (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ)).range.index =
      W.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
        W.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  classical
  -- the place of `k` below `ŵ`
  have hvw : ŵ.asIdeal.LiesOver v₀.asIdeal :=
    Ideal.LiesOver.trans ŵ.asIdeal W.asIdeal v₀.asIdeal
  -- the three `adicCompletion` algebras involved in the finrank tower
  letI hAlg_ME : Algebra (W.adicCompletion M) (ŵ.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap W ŵ hW)
  letI hAlg_kE : Algebra (v₀.adicCompletion k) (ŵ.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap v₀ ŵ hvw)
  letI hAlg_kM : Algebra (v₀.adicCompletion k) (W.adicCompletion M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap v₀ W hWv)
  haveI hfd_ME : FiniteDimensional (W.adicCompletion M) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion W ŵ hW
  haveI hfd_kM : FiniteDimensional (v₀.adicCompletion k) (W.adicCompletion M) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion v₀ W hWv
  -- the scalar tower `k_{v₀} → M_W → E_ŵ` of adic completions
  haveI htower : IsScalarTower (v₀.adicCompletion k) (W.adicCompletion M) (ŵ.adicCompletion E) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
        Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp v₀ W ŵ hWv hW hvw])
  -- `stabIncl ŵ` is injective (restriction of scalars)
  have hinj : Function.Injective (Work.SSGRoute.stabIncl (k := k) (M := M)
      (NK.GlobalCFT.Place.ofFinite ŵ)) := by
    intro σ τ h
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    have h2 := congrArg (fun (f : MulAction.stabilizer (E ≃ₐ[k] E)
        (NK.GlobalCFT.Place.ofFinite ŵ)) => f.1 x) h
    simpa [Work.SSGRoute.stabIncl] using h2
  -- the two stabiliser cardinalities are local degrees
  have hcard_M : Nat.card (MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofFinite ŵ)) =
      Module.finrank (W.adicCompletion M) (ŵ.adicCompletion E) :=
    Work.SSGRoute.eb_stab_card_aux k M E ŵ W hW
  have hcard_k : Nat.card (MulAction.stabilizer (E ≃ₐ[k] E) (NK.GlobalCFT.Place.ofFinite ŵ)) =
      Module.finrank (v₀.adicCompletion k) (ŵ.adicCompletion E) :=
    Work.SSGRoute.eb_stab_card_aux k k E ŵ v₀ hvw
  -- the range of `stabIncl` has the cardinality of `Stab_{Gal(E/M)}(ŵ)`
  have hrange : Nat.card ↥(Work.SSGRoute.stabIncl (k := k) (M := M)
        (NK.GlobalCFT.Place.ofFinite ŵ)).range =
      Nat.card (MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofFinite ŵ)) := by
    have hset : ((Work.SSGRoute.stabIncl (k := k) (M := M)
        (NK.GlobalCFT.Place.ofFinite ŵ)).range : Set (MulAction.stabilizer (E ≃ₐ[k] E)
          (NK.GlobalCFT.Place.ofFinite ŵ))) =
        Set.range (Work.SSGRoute.stabIncl (k := k) (M := M)
          (NK.GlobalCFT.Place.ofFinite ŵ)) := by
      ext y; simp
    change Nat.card ↥((Work.SSGRoute.stabIncl (k := k) (M := M)
        (NK.GlobalCFT.Place.ofFinite ŵ)).range : Set (MulAction.stabilizer (E ≃ₐ[k] E)
          (NK.GlobalCFT.Place.ofFinite ŵ))) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[M] E) (NK.GlobalCFT.Place.ofFinite ŵ))
    rw [Nat.card_congr (Set.equivOfEq hset), Nat.card_congr (Equiv.ofInjective _ hinj)]
  -- the local degree `[E_ŵ : M_W]` is non-zero
  have hA : Module.finrank (W.adicCompletion M) (ŵ.adicCompletion E) ≠ 0 := by
    rw [← hcard_M]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  -- `Subgroup.card_mul_index` with the two local degrees substituted
  have h1 : Module.finrank (W.adicCompletion M) (ŵ.adicCompletion E) *
      (Work.SSGRoute.stabIncl (k := k) (M := M) (NK.GlobalCFT.Place.ofFinite ŵ)).range.index =
      Module.finrank (v₀.adicCompletion k) (ŵ.adicCompletion E) := by
    rw [← hcard_k, ← Subgroup.card_mul_index (Work.SSGRoute.stabIncl (k := k) (M := M)
      (NK.GlobalCFT.Place.ofFinite ŵ)).range, hrange, hcard_M]
  -- the tower formula for the local degrees
  have h2 : Module.finrank (v₀.adicCompletion k) (ŵ.adicCompletion E) =
      Module.finrank (v₀.adicCompletion k) (W.adicCompletion M) *
        Module.finrank (W.adicCompletion M) (ŵ.adicCompletion E) := by
    rw [Module.finrank_mul_finrank (v₀.adicCompletion k) (W.adicCompletion M)
      (ŵ.adicCompletion E)]
  have h3 : (Work.SSGRoute.stabIncl (k := k) (M := M)
        (NK.GlobalCFT.Place.ofFinite ŵ)).range.index =
      Module.finrank (v₀.adicCompletion k) (W.adicCompletion M) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA) ((mul_comm _ _).trans (h1.trans h2))
  rw [h3]
  exact (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    v₀ W hWv).symm

end Work.SSGRoute
