import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.e1a_shift
import Submission.Work.SSGRoute.PT.freeCoverSES_res_comparison
import Submission.Work.SSGRoute.ExtChain.ext_shift_natural_res
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.NK.HassePrinciple.locUnits_compatible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the two formal bricks of the localisation comparison

This module collects, `sorry`-free and **without importing the target files** (so that it can be
imported by the E1a nodes whose files are still open (all four brick names live in the namespace `Work.SSGRoute.SSGStage`)), the formal content of the E1a "localisation
comparison square" (`PT/NOTE_e1aChainC_localComparison.md` §10.2, §11):

* `extClass_freeCoverSES_res_comparison` — **(i)**: the connecting classes of the two canonical
  presentations of `Rep.res φ X` agree (piece (i) of §11.1, the "only genuinely new rule" of §10.2);
* `e1aShiftEquiv_extRes` — the canonical syzygy shift commutes with restriction to a subgroup;
* `extLoc_extToIdeles_eq` — **(F)**: `extLoc_w ∘ extToIdeles` is "restrict to `D_w` and evaluate
  the `w`-component", i.e. `extRes_{D_w}` followed by the coefficient `Kˣ → K_wˣ`;
* `extLoc_extToIdeles_e1aSyzShift_eq_zero` — **(F)**, degree-reduced: the conclusion of the
  landing clause is *deduced* from the vanishing of the degree-one class
  `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)`.

The trap that cost the most is recorded in `PT/PING_phiE_transport_brick_proved.md`: after
`rw [extClass_naturality]` the goal contains `mk₀ (𝟙 (Rep.res φ X))` where `mk₀` expects
`(freeCoverSES (Rep.res φ X)).X₃ ⟶ ((freeCoverSES X).map (Rep.resFunctor φ)).X₃`; the two endpoints
are equal only up to unfolding `Rep.res`/`freeCoverSES`/`ShortComplex.map`, which `rw`'s matcher does
not do.  One must state the `mapExactFunctor_extClass` equation as a `have` *before* rewriting.
-/

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.SSGStage

open CategoryTheory

/-! ## `(i)`: the connecting classes of the two canonical presentations

For `φ : H →* G` and a `G`-representation `X`, `freeCoverSES (Rep.res φ X)` and
`(freeCoverSES X).map (Rep.resFunctor φ)` are two canonical presentations of the *same* module
`Rep.res φ X` (their middle terms, `Rep.free Coeff H X.V` and `Rep.res φ (Rep.free Coeff G X.V)`,
are genuinely different — `PT/NOTE_e1aChainC_localComparison.md` §11.3).  The comparison
`freeCoverSES_res_comparison` (`PT/freeCoverSES_res_comparison.lean`, proved) relates them.

The following lemma records the *consequence* that the E1a comparison square consumes: the
connecting classes of the two presentations agree, i.e. `extClass` of the restricted canonical
presentation is `extClass` of the canonical presentation, precomposed with the comparison of the
syzygies.  This is the "only genuinely new rule" of `PT/NOTE_e1aChainC_localComparison.md` §10.2.

Mathlib supplies the two ingredients:
`ShortComplex.ShortExact.extClass_naturality` (naturality of `extClass` in a morphism of short
complexes) and `Abelian.Ext.mapExactFunctor_extClass` (`mapExactFunctor` commutes with `extClass`),
together with `Abelian.Ext.mk₀_id_comp` for the identity third component. -/
theorem extClass_freeCoverSES_res_comparison {G H : Type} [Group G] [Group H] [Fintype G]
    [Fintype H] (φ : H →* G) (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ Φ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res φ X))
        ((Work.SSGRoute.freeCoverSES X).map
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)),
      Φ.τ₂ = Work.SSGRoute.PT.freeCoverCompat φ X ∧
        Φ.τ₃ = CategoryTheory.CategoryStruct.id (Rep.res φ X) ∧
        (Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X)).extClass.comp
            (CategoryTheory.Abelian.Ext.mk₀ Φ.τ₁) (add_zero 1) =
          CategoryTheory.Abelian.Ext.mapExactFunctor
            (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)
            (Work.SSGRoute.freeCoverSES_shortExact X).extClass := by
  obtain ⟨Φ, h2, h3⟩ := Work.SSGRoute.PT.freeCoverSES_res_comparison φ X
  refine ⟨Φ, h2, h3, ?_⟩
  have hnat := CategoryTheory.ShortComplex.ShortExact.extClass_naturality
    (Work.SSGRoute.freeCoverSES_shortExact (Rep.res φ X))
    ((Work.SSGRoute.freeCoverSES_shortExact X).map_of_exact
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)) Φ
  have hα : CategoryTheory.Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)
        (Work.SSGRoute.freeCoverSES_shortExact X).extClass
      = ((Work.SSGRoute.freeCoverSES_shortExact X).map_of_exact
          (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)).extClass :=
    CategoryTheory.Abelian.Ext.mapExactFunctor_extClass
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) φ)
      (Work.SSGRoute.freeCoverSES_shortExact X)
  rw [hnat, h3, hα]
  exact CategoryTheory.Abelian.Ext.mk₀_id_comp _

section ExtSideLocalisation

variable {k : Type} [Field k] [NumberField k] {K : Type} [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **The Ext-side localisation factorises through the degree-one class.**

`extLoc_w ∘ extToIdeles` is "restrict to `D_w` and evaluate the `w`-component"; it is the
restriction `extRes_{D_w}` composed with the coefficient the principal idèles `Kˣ → K_wˣ`:

  `extLoc_w (extToIdeles x) = extRes_{D_w}(x) ∘ mk₀ (unitsToLocalUnits)`.

This is the *degree reduction* of the conclusion of the landing clause
(`PT/NOTE_e1aChainC_localComparison.md` §11.5): it lets `extLoc_q (extToIdeles y)` be read off the
degree-one class `(e1aSyzShift N)⁻¹ y`, where the local `E1c` dictionary lives.  The proof is the
computation rule of `Ext.mapExactFunctor` (`mapExactFunctor_comp`, `mapExactFunctor_mk₀`),
the associativity of `Ext.comp` (`comp_assoc_of_third_deg_zero`),
`Ext.mk₀_comp_mk₀` and the coefficient triangle
`NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits`. -/
theorem extLoc_extToIdeles_eq
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (w : NK.GlobalCFT.Place K)
    (x : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.unitsK k K) r) :
    SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) (M := M) x) =
      (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) w).subtype x).comp
        (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K w))
        (add_zero r) := by
  have hcomp : CategoryTheory.Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) w).subtype)
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K))
          (add_zero r))
      = (CategoryTheory.Abelian.Ext.mapExactFunctor
            (Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) w).subtype) x).comp
          (CategoryTheory.Abelian.Ext.mk₀
            ((Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) w).subtype).map
              (NK.HassePrinciple.ideleIncl k K)))
          (add_zero r) := by
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  rw [SSGRoute.PTExt.extLoc, SSGRoute.PTExt.extToIdeles, SSGRoute.PTExt.extRes, hcomp]
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  rw [NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits]
  rfl

end ExtSideLocalisation

section ExtSideLocalisationField

variable {G : Type} [Group G]

/-- **Restriction-naturality of the canonical syzygy shift, in the connecting-class form.**  For a
short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` with projective middle term, a subgroup `D ≤ G`,
a coefficient `Y` and a degree `n ≥ 1`, the *canonical* syzygy shift `e1aShiftEquiv` (the connecting
class `S.extClass`) commutes with the restriction `extRes D.subtype`:

  `extRes_D (e1aShiftEquiv S hS Y n x) = (S.map F).extClass.comp (extRes_D x) (1 + n = n + 1)`.

The proof is `ExtChain.bijective_extClass_precomp_map` (restriction-naturality of the connecting map)
read through `e1aShiftEquiv_apply`.  Only the *forward* computation is recorded: the `AddEquiv` at
the restricted presentation would additionally need the projectivity of the restricted middle term,
which is not needed here. -/
theorem e1aShiftEquiv_extRes (D : Subgroup G)
    (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) [CategoryTheory.Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) (hn : 1 ≤ n)
    (x : CategoryTheory.Abelian.Ext.{0} S.X₁ Y n) :
    SSGRoute.PTExt.extRes D.subtype (Work.SSGRoute.PT.e1aShiftEquiv S hS Y n hn x)
      = ((hS.map_of_exact (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype)).extClass).comp
          (SSGRoute.PTExt.extRes D.subtype x) (by omega : 1 + n = n + 1) := by
  rw [Work.SSGRoute.PT.e1aShiftEquiv_apply, SSGRoute.PTExt.extRes]
  exact Work.SSGRoute.ExtChain.bijective_extClass_precomp_map
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) D.subtype) hS Y hn (by omega) x

end ExtSideLocalisationField

section ExtSideLocalisationLevel

-- The `extLoc`/`extToIdeles`/`unitsK` terms below are equal to the `Rep.resFunctor`-spelled ones
-- only up to unfolding `Rep.res`/`freeCoverSES`/`ShortComplex.map`, which the rewriting machinery
-- uses at a transparency level that does not unfold them (the same situation as in
-- `NK/HassePrinciple/locUnits_compatible.lean`).
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]

/-- **The conclusion of the landing clause, on the degree-one class (forward direction).**

Let `0 → R → F → N → 0` be the canonical free cover of `N` (`R = kernel (freeCover N)`) and let
`z ∈ Ext¹_{Gal(K/k)}(R, Kˣ)`; put `y := e1aSyzShift N z ∈ Ext²(N, Kˣ)`.  If the *localised
degree-one* class `(extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits)` vanishes in
`Ext¹_{D_q}(res R, K_qˣ)`, then so does `extLoc_q (extToIdeles y)`:

  `(extRes_{D_q}(z)) ∘ mk₀ (unitsToLocalUnits) = 0  ⟹  extLoc_q (extToIdeles (e1aSyzShift N z)) = 0`.

This is the reduction of the conclusion promised in `PT/NOTE_e1aChainC_localComparison.md` §11.5, in
the direction the comparison square consumes: it lets the landing clause be *deduced* from the
vanishing of the degree-one class `(e1aSyzShift N)⁻¹ y`.  The proof composes
`extLoc_extToIdeles_eq` (the coefficient triangle) with `e1aShiftEquiv_extRes` (the syzygy shift
commutes with restriction). -/
theorem extLoc_extToIdeles_e1aSyzShift_eq_zero
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (q : NK.GlobalCFT.Place K)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1) :
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K q))
        (add_zero 1) = 0 →
      SSGRoute.PTExt.extLoc (k := k) q
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0 := by
  haveI hproj : CategoryTheory.Projective (Work.SSGRoute.freeCoverSES N).X₂ :=
    Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := N.V)
  intro hz
  rw [extLoc_extToIdeles_eq (k := k) (K := ↥K) q
    (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)]
  rw [Work.SSGRoute.ExtChain.e1aSyzShift,
    e1aShiftEquiv_extRes (SSGRoute.PTExt.decompK (k := k) q)
      (Work.SSGRoute.freeCoverSES N) (Work.SSGRoute.freeCoverSES_shortExact N)
      (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1) z]
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero, hz]
  simp only [CategoryTheory.Abelian.Ext.comp_zero]

end ExtSideLocalisationLevel
end Work.SSGRoute.SSGStage
