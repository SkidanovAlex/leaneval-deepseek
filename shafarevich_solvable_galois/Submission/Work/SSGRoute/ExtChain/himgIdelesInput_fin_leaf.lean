import Mathlib
import Submission.Work.SSGRoute.ExtChain.himgLeafCore
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen
import Submission.Work.SSGRoute.ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift
import Submission.Work.SSGRoute.ExtChain.ext_push_engine
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_le_ker
import Submission.Work.SSGRoute.ExtChain.subsingletonH1_homCoind_of_trivial_action
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
import Submission.Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective
import Submission.Work.SSGRoute.ExtChain.push_injective_syzygy
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.PT.e1a_shift
import Submission.Work.ExtChain.ptorsion_e1aN0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

/-! ## Step 1 of the finite-place clause: the per-place vanishing

The global hypothesis `extToIdeles (e1aSyzShift N z) = 0` of the target is *stronger* than its
localisation at any one place; specialising at the place `q` of `K` below the finite place `A` and
using the proved converse `ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp` gives the
per-place vanishing of the localised class

    (extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits k K q) = 0,      D_q = decompK q.

This is the hypothesis consumed both by the proved landing direction
(`E1aClean.finLocalCriterion`: `resH1_{D_A}(e1cMap R z) = 0` ⟹ this vanishing) and by the converse
route recorded in `NOTE_fin_leaf_route_session.md` (this vanishing ⟹ the target), whose residual
arithmetic inputs are `K^h := Ω^{D_A ⊓ G_K}` embedding in `K_q` as a henselisation.
-/

/-- **The per-place vanishing of the localised class from the global hypothesis.** -/
theorem extRes_comp_unitsToLocalUnits_eq_zero_of_hz
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite N.V] (q : NK.GlobalCFT.Place ↥K)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) = 0) :
    (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype z).comp
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q))
      (add_zero 1) = 0 := by
  refine Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
    (k := k) (Ω := Ω) (K := K) N q z ?_
  rw [hz]
  exact SSGRoute.PTExt.extLoc_zero (k := k) (K := ↥K) q

/-! ## Step 2 of the finite-place clause: the formal `H¹ ← H²` reduction at an arbitrary closed
subgroup

The proved `ExtChain.resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero` states the formal
reduction of the *involution* input: if the `H²`-side chain class restricts to `0` at `⟨σ⟩`
(`σ² = 1`), then so does the `H¹`-side `E1c` class of the syzygy shift of `z`.  Nothing in its
proof uses `σ² = 1`: the only input is the injectivity of the connecting map of the dualised
canonical resolution restricted to the subgroup, whose kernel is
`H¹(D, Hom_ℤ(ℤ[G]^n, Ωˣ)) = 0` (`ExtChain.homCoindFreeT_H1_subgroup`, available for **every
closed** subgroup `D` by Shapiro at `D ⊓ Gal(Ω/K)` plus Hilbert 90 there).  The lemma below is that
verbatim generalisation, which is what lets the finite-place clause be reduced to a single
statement about `resH2_{decomp k A}`. -/

/-- **The formal `H¹ ← H²` reduction at an arbitrary closed subgroup.**  For a closed subgroup
`D ≤ Gal(Ω/k)` and `z ∈ Ext¹_G(ker (freeCover N), Kˣ)`, the vanishing of the restricted `H²`-side
chain class of the syzygy shift `y = e1aSyzShift N z` implies the vanishing of the restricted
`E1c`-class of `z`.

(This is a verbatim copy of the lemma of the same name in `ExtChain/himgIdelesInput_fin.lean`,
which cannot be imported here; it is kept `private` so that adding the import of this module to
that file does not clash.) -/
private theorem resH1_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω)))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.resH2 D
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 D
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 := by
  have hInj := Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective'
    (k := k) (Ω := Ω) (K := K) N D hD
  have key : (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.ExtChain.e1aSES N) D).deltaH2
      (Work.SSGRoute.PT.H2Fin.resH1 D
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)) = 0 := by
    rw [← Work.SSGRoute.ExtChain.deltaH2_restriction (Work.SSGRoute.ExtChain.e1aSES N) D
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)]
    have hH : (Work.SSGRoute.ExtChain.e1aSES N).deltaH2
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)
        = Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
            (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) := by
      rw [Work.SSGRoute.PT.e1aChainH_apply (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z),
        AddEquiv.symm_apply_apply]
      rfl
    rw [hH]
    exact h
  exact hInj (by rw [key, map_zero])

/-! ## State of this leaf (session record, 2026-10-06)

**Proved and sorry-free here**: `extRes_comp_unitsToLocalUnits_eq_zero_of_hz` — the *first* step of
the route (the per-place vanishing of the localised class, from the global hypothesis `hz`).  The
target `himgIdelesInput_fin_leaf` itself is **not yet proved**: the remaining pieces are recorded
in `NOTE_fin_leaf_route_session.md` (the corrected route, which avoids the `(BC)` base change of the
`E1c` dictionary) and `PING_finleaf_route_and_density_gap.md` (the residual gaps).  As of this
session, the arithmetic half of `(PUSH)` has landed sorry-free
(`E1aClean.adicCompletion_units_eq_baseUnits_mul_pow`, `E1aClean.completion_quotient_uniqueDivisible`,
`E1aClean.decompField_embeds_completion`, `E1aClean.unitsQuotient_pow_bijective`), and the
`D_A`-representation structure on the henselisation is begun in `ExtChain/khUnitsRep.lean` and
`ExtChain/khUnitsRepA.lean`.

Route of the remaining work, in order:

1. `z = PhiE R w` (`PhiE_surjective`);
2. `zq := (extRes_{D_q} z) ∘ mk₀ (unitsToLocalUnits) = 0` — *proved here*;
3. `zq = δ_{S|D_q}(Y_q)` with `S = freeCoverSES R` and `Y_q := (extRes_{D_q} w) ∘ mk₀ (unitsToLocalUnits)`
   (`Abelian.Ext.mapExactFunctor_comp`, `Abelian.Ext.mapExactFunctor_extClass`, associativity of
   `Ext.comp`);
4. `(PUSH)`: the coefficient change `(K^h)ˣ → K_qˣ` induces a *bijection* on
   `Ext²_{D_q}(res N, ·)` (`ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible` plus the
   short exact sequence `0 → (K^h)ˣ → K_qˣ → Q → 0` of `↥(decompK q)`-representations with `hQ` from
   `E1aClean.unitsQuotient_pow_bijective`), transported to `Ext¹_{D_q}(res R, ·)` along the syzygy
   shift of `freeCoverSES N`; hence `ζ := (extRes_{D_q} z) ∘ mk₀ (Kˣ → (K^h)ˣ) = 0`;
5. `ζ = δ_{S|D_q}(Y_h) = 0` and `ExtChain.ext_connecting_range_ker` give a `D_q`-equivariant
   `(K^h)ˣ`-valued extension `ξ` of `Y_h` on `E1cF R`;
6. `ξ` (values in `K^h = Ω^{D_A ⊓ G_K}`, `D_A` acting through `D_q`) is a `D_A`-invariant element of
   `H⁰(D_A, homCoind k Ω K R)` with `Φ ∘ κ = (PsiEMap (E1cR1 R) w).1`, so
   `ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift` gives the goal.
-/

/-! ## The formal half of `(PUSH)`: injectivity of the coefficient change on the syzygy lattice

The lead's `(PUSH)` (`_lead_design/flags_0030/NOTE.md` §2, re-affirmed in `flags_0530/NOTE.md` §1)
asks for the *injectivity* of the coefficient change

    Ext¹_{D_q}(res R, (K^h)ˣ) → Ext¹_{D_q}(res R, K_qˣ),      R = ker (freeCover N),  N = E^∨(1),

where `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` is the henselisation of `K` at `q` and the quotient
`Q = K_qˣ/(K^h)ˣ` is uniquely `p`-divisible.  The *arithmetic* half of this is
`E1aClean.unitsQuotient_pow_bijective` (proved); the *formal* half is the lemma below, which is
purely `Ext`-bookkeeping and holds in the abstract setting: it is the syzygy-shifted form of the
engine `ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible`.

The point of the shift is that `R` is a *lattice*, not `p`-torsion: the engine does not apply to
`Ext¹(res R, ·)` directly.  But `0 → res R → res F → res N → 0` has `res F` projective, so the
syzygy shift `Ext¹(res R, ·) ≅ Ext²(res N, ·)` is a natural isomorphism (`PT.e1aShiftEquiv`), and
the pushed coefficient change is the engine's bijection on `Ext²(res N, ·)`.  Hence the change on
`Ext¹(res R, ·)` is injective as well. -/

/-- The henselisation `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` of `K` at the finite place `A`: the fixed field of
`D_A ⊓ Gal(Ω/K)`, i.e. of the decomposition group of `A` over the finite extension `K`. -/
noncomputable abbrev Kh {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (A : ValuationSubring Ω) : IntermediateField k Ω :=
  IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)

/-- **The three clauses of the `(K^h)ˣ`-valued equivariant lift**, packaged so that they can be
passed around as one hypothesis.  This is exactly the shape of the witness produced by
`ExtChain.exists_khLift_of_extToIdeles_eq_zero`: `ξ : E1cF R → (K^h)ˣ` is multiplicative, is
`↥(decomp k A)`-equivariant for the action on `K^h ⊆ Ω`, and extends the `K`-valued datum `w` on
the canonical syzygy `E1cR1 R` along the syzygy inclusion `kappa`. -/
def IsKhLift {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (A : ValuationSubring Ω) (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 (k := k) (Ω := Ω) (K := K) R)
      (SSGRoute.PTExt.unitsK k K) 0)
    (ξ : (E1cF (k := k) (Ω := Ω) (K := K) R).V
      → (↥(Work.SSGRoute.E1aClean.henselField k Ω K A))ˣ) : Prop :=
  (∀ a b : (E1cF (k := k) (Ω := Ω) (K := K) R).V, ξ (a + b) = ξ a * ξ b) ∧
    (∀ (δ : ↥(SSGRoute.decomp k A)) (v : (E1cF (k := k) (Ω := Ω) (K := K) R).V),
      ((ξ ((E1cF (k := k) (Ω := Ω) (K := K) R).ρ
            (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v)
          : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
        = (δ : Ω ≃ₐ[k] Ω)
            (((ξ v : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω))) ∧
    (∀ x : (E1cR1 (k := k) (Ω := Ω) (K := K) R).V,
      ((ξ (kappa (k := k) (Ω := Ω) (K := K) R x)
          : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
        = (((Additive.toMul
              (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) : (↥K)ˣ) : ↥K) : Ω))

/-- **The criterion, in the form in which the finite-place clause consumes it.**  If the
`K`-valued data `w` on the canonical syzygy `E1cR1 R` extends to a `↥(decomp k A)`-equivariant
`(K^h)ˣ`-valued map `ξ` on the free cover `E1cF R`, where `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` carries the
action of `δ ∈ decomp k A` through the embedding `K^h ⊆ Ω`, then the `E1c` class of the
`PhiE`-generator of `w` restricts to `0` at `decomp k A`.

This is `ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift` applied to
`Φ : (E1cF R).V →+ Additive Ωˣ`, `v ↦ (ξ v : Ω)`: that `Ωˣ`-valued extension is `D_A`-invariant
because `ξ` is `↥(decomp k A)`-equivariant for the action on `(K^h)ˣ` *induced from* the action of
`decomp k A` on `K^h ⊆ Ω` — which is exactly the representation structure of `(K^h)ˣ` produced by
the coefficient-change step of the finite-place clause, so no arithmetic enters here. -/
theorem resH1_e1cMap_eq_zero_of_khLift
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 (k := k) (Ω := Ω) (K := K) R)
      (SSGRoute.PTExt.unitsK k K) 0)
    (ξ : (E1cF (k := k) (Ω := Ω) (K := K) R).V → (↥(Work.SSGRoute.E1aClean.henselField k Ω K A))ˣ)
    (hξ : IsKhLift (k := k) (Ω := Ω) (K := K) A R w ξ) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K R)
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)) = 0 := by
  obtain ⟨hξadd, hξeq, hξκ⟩ := hξ
  classical
  let Φ : E1cN (k := k) (Ω := Ω) (K := K) R :=
    { toFun := fun v => Additive.ofMul
        (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ v))
      map_zero' := by
        have h0 : ξ 0 = 1 := by
          have h := hξadd 0 0
          rw [add_zero] at h
          exact (mul_eq_left).mp h.symm
        show Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ 0)) = 0
        rw [h0, map_one]
        rfl
      map_add' := fun a b => by
        show Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ (a + b)))
          = Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ a))
            + Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ b))
        rw [hξadd, map_mul]
        rfl }
  have hΦmem : Φ ∈ Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A)
      (E1cN (k := k) (Ω := Ω) (K := K) R) := by
    rw [Work.GroupCohomology.mem_invariants]
    intro hh
    change (homCoind.instDistribMulActionAlgEquiv (E1cF (k := k) (Ω := Ω) (K := K) R)).smul
      (hh : Ω ≃ₐ[k] Ω) Φ = Φ
    apply AddMonoidHom.ext
    intro v
    rw [smul_conj_homCoindFreeT]
    have key : ∀ u : (E1cF (k := k) (Ω := Ω) (K := K) R).V,
        Φ ((E1cF (k := k) (Ω := Ω) (K := K) R).ρ
            (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u)
          = homCoind.smulHom (k := k) (Ω := Ω) (hh : Ω ≃ₐ[k] Ω) (Φ u) := by
      intro u
      show Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom
            (ξ ((E1cF (k := k) (Ω := Ω) (K := K) R).ρ
              (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u)))
          = homCoind.smulHom (k := k) (Ω := Ω) (hh : Ω ≃ₐ[k] Ω)
              (Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ u)))
      rw [homCoind.smulHom_apply]
      apply Additive.toMul.injective
      show Additive.toMul (Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom
            (ξ ((E1cF (k := k) (Ω := Ω) (K := K) R).ρ
              (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω)) u))))
          = Additive.toMul ((hh : Ω ≃ₐ[k] Ω) • Additive.ofMul
              (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom (ξ u)))
      rw [toMul_ofMul, Work.SSGRoute.addUnits_smul_toMulΩ, toMul_ofMul]
      apply Units.ext
      rw [Units.coe_map, Work.SSGRoute.algEquivUnitsMapΩ_coe, Units.coe_map]
      simpa using hξeq hh u
    rw [← key ((E1cF (k := k) (Ω := Ω) (K := K) R).ρ
      (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))⁻¹ v)]
    congr 1
    first
      | (rw [← Module.End.mul_apply, mul_inv_cancel, Module.End.one_apply])
      | (rw [← Module.End.mul_apply,
            ← map_mul (E1cF (k := k) (Ω := Ω) (K := K) R).ρ
              (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))
              (SSGRoute.res k K (hh : Ω ≃ₐ[k] Ω))⁻¹,
            mul_inv_cancel, map_one, Module.End.one_apply])
  have hΦκ : ∀ x : (E1cR1 (k := k) (Ω := Ω) (K := K) R).V,
      Φ (kappa (k := k) (Ω := Ω) (K := K) R x)
        = (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 x := by
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    show ((Additive.toMul (Additive.ofMul (Units.map (algebraMap ↥(Work.SSGRoute.E1aClean.henselField k Ω K A) Ω).toMonoidHom
            (ξ (kappa (k := k) (Ω := Ω) (K := K) R x)))) : Ωˣ) : Ω)
        = ((Additive.toMul ((PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 (k := k) (Ω := Ω) (K := K) R) w).1 x) : Ωˣ) : Ω)
    rw [toMul_ofMul, Units.coe_map]
    rw [PsiEMap_apply_toCoindH0, Work.SSGRoute.toCoindH0_apply, toMul_ofMul, Units.coe_map]
    simpa using hξκ x
  exact resH1_e1cMap_eq_zero_of_invariant_lift (k := k) (Ω := Ω) (K := K) R w
    (SSGRoute.decomp k A) Φ hΦmem (AddMonoidHom.ext hΦκ)

/-- **The finite-place clause, reduced to the existence of the `(K^h)ˣ`-valued equivariant lift.**

The hypothesis `H` is exactly the arithmetic content of the finite-place clause in the form
produced by the *coefficient change to the henselisation* `(K^h)ˣ`: for
`N = E^∨(1)` (`p`-torsion), `R = ker (freeCover N)`, `w` with `extToIdeles (e1aSyzShift N (PhiE R w))
= 0` and `A` a finite place that is not completely split, there exist the prime `q` of `𝒪_K` below
`A`, and a `↥(decomp k A)`-equivariant `(K^h)ˣ`-valued extension `ξ` of the localised data `w` on
the canonical syzygy, with `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` acting through `K^h ⊆ Ω`.

Given `H`, the target follows immediately: `PhiE_surjective` writes `z = PhiE R w`, the hypothesis
`extToIdeles (e1aSyzShift N z) = 0` transfers along it, and the criterion
`resH1_e1cMap_eq_zero_of_khLift` above concludes.  In particular *no* cohomological identification
of `resH1_{D_A}(e1cMap R z)` with a localisation is needed at this point: the whole content of that
identification is absorbed into the two facts (i) that the `K_qˣ`-localisation of the `(K^h)ˣ`-lift
is the datum `w` (used to *construct* `ξ` from `hz` in `H`) and (ii) that `ξ`'s values lie in the
fixed field `K^h`, from which the `D_A`-invariance of the `Ωˣ`-valued extension is `rfl`-level. -/
theorem himgIdelesInput_fin_leaf_of_khLift
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (H : ∀ (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (hN : ∀ x : N.V, (p : SSGRoute.PTExt.Coeff) • x = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker))
    (w : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (SSGRoute.PTExt.unitsK k K) 0)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w)) = 0),
    ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (hAq : ∀ x : NumberField.RingOfIntegers K,
        x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
      (ξ : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V
          → (↥(Work.SSGRoute.E1aClean.henselField k Ω K A))ˣ),
      (∀ a b : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
        ξ (a + b) = ξ a * ξ b) ∧
      (∀ (δ : ↥(SSGRoute.decomp k A))
        (v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V),
        ((ξ ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).ρ
              (SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω)) v)
            : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
          = (δ : Ω ≃ₐ[k] Ω)
              (((ξ v : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω))) ∧
      (∀ x : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
        ((ξ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K)
              (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) x)
            : ↥(Work.SSGRoute.E1aClean.henselField k Ω K A)) : Ω)
          = (((Additive.toMul
                (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) x) : (↥K)ˣ) : ↥K) : Ω))
)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker)) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  obtain ⟨w, hw⟩ := E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K)
    (CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z
  rw [← hw]
  obtain ⟨q, hAq, ξ, h1, h2, h3⟩ := H
    (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
    (Work.ExtChain.ptorsion_e1aN0 p k Ω K T E) A hA hns w (by rw [← hw] at hz; exact hz)
  exact resH1_e1cMap_eq_zero_of_khLift (k := k) (Ω := Ω) (K := K)
    (CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
    A hA w ξ ⟨h1, h2, h3⟩

/-- **The finite-place clause of the `himg` half of `(C')`, in a module that sits *below*
`ExtChain/extToIdeles_eq_zero_imp_chainC_locallyTrivial.lean`.**

Statement verbatim `Work.SSGRoute.ExtChain.himgIdelesInput_fin`
(`Submission/Work/SSGRoute/ExtChain/himgIdelesInput_fin.lean`), re-stated at a path whose import
cone avoids the `himg` leaf file, so that the leaf file — which may not import its own children —
can cite it. Content: for `z ∈ Ext¹_{Gal(K/k)}(R, Kˣ)`, `R = ker (freeCover (E^∨(1)))`,
`E^∨(1) = DualMod p (E ⊗ T)`, if the idèle localisation of the syzygy-shifted class vanishes,
`extToIdeles (e1aSyzShift N z) = 0`, then the canonical `E1c` dictionary class `e1cMap R z` restricts
to `0` at the decomposition group `decomp k A` of every finite place `A` of `Ω` that is not
completely split (`¬ decomp k A ≤ ker (res k K)`).

Route (recorded by the project lead, `_lead_design/flags_0030/NOTE.md` §4; the earlier
lattice-Hasse framing of this clause must be dropped — it asks for `extRes_{D_q} z = 0` in the
`Kˣ`-coefficient, a Hasse principle for a torus split by `K`, which *fails* for non-cyclic `D_q`,
e.g. norm-one tori of biquadratic extensions):

1. **(BC)** `res_{D_A}(e1cMap z) = e1cMap^{(k^h, Ω, K^h)}(z^h)` where `k^h := Ω^{D_A}` (fixed field of
   `D_A = decomp k A`), `K^h := K · k^h`, and `z^h` is `z` restricted to `D_q = D_A/H` with
   coefficients changed along `Kˣ → (K^h)ˣ`; `E1cGeneric` is field-generic so it applies to
   `(k^h, Ω, K^h)`.
2. `e1cMap^{(k^h,…)}` is injective, so it suffices that `z^h = 0`.
3. `δ : Ext¹_D(R, ·) → Ext²_D(E^∨(1), ·)` is injective (`Ext¹_D(F, ·) = H¹(D, coinduced) = 0` for the
   free cover `F`), so it suffices that `y^h := δ z^h = 0` in `Ext²_D(E^∨(1), (K^h)ˣ)`.
4. **(PUSH)** for the finite `p`-torsion `E^∨(1)`: `Ext^i_D(E^∨(1), (K^h)ˣ) → Ext^i_D(E^∨(1), K_qˣ)` is
   an isomorphism, because the quotient `K_qˣ/(K^h)ˣ` is uniquely `p`-divisible. Its formal half is
   `ExtChain.subsingleton_ext_of_ptorsion_uniqueDivisible` and
   `ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible`
   (`Submission/Work/SSGRoute/ExtChain/ext_push_engine.lean`, sorry-free). Hence `y^h = 0` iff its
   push to `K_qˣ` vanishes; that push is `extLoc_q (extToIdeles (e1aSyzShift z))`, which is `0` by
   `hz` (`extLoc_extToIdeles_eq_mk₀`). -/
theorem himgIdelesInput_fin_leaf (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker)) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  exact himgIdelesInput_fin_leaf_of_khLift (p := p) (k := k) (Ω := Ω) (K := K)
    (ζ := ζ) (hζ := hζ) (hζK := hζK) (T := T) (hT := hT) (E := E)
    (z := z) (hz := hz) (A := A) (hA := hA) (hns := hns)
    (fun N _ _ hN A' hA' hns' w hz' =>
      exists_khLift_of_extToIdeles_eq_zero p N hN A' hA' hns' w hz')

end Work.SSGRoute.ExtChain
