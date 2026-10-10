import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.E7cC.exists_unramifiedDetector
import Submission.Work.SSGRoute.SSGStage.levelPair_eCoh_cocycles_ne_zero
import Submission.Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ
import Submission.Work.Sha2Lib.shapiroCocycle_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick of node `C6`: the detector for the permutation module

**The state of this file.**  The target `C6_rankOneBrick` is the detector
`IsUnramifiedDetector p k K Ω w q hwq M` for the permutation module
`M = Ind_N^{Gal(K/k)} 𝔽_p`, where `N ⊴ Gal(K/k)` contains the inertia of the place `q ∤ p` and
fixes a primitive `p`-th root of unity `ζ ∈ K`.

What is verified here is the entire cohomological bookkeeping of the brick: the proof that the
detector for this `M` follows from the workspace's single arithmetic node

`Work.SSGRoute.E7cOmega.exists_level_detecting_functional`

(the *level input* of node `C6`: for every non-zero `D_w`-equivariant `μ : res_{D_w} M ⟶ ℚ/ℤ`
there are a finite Galois level `L ⊇ K`, a place `q' | q` with `p ∤ e(q'|q)`, a splitting `s` of
`galRes k K L`, and a `Gal(K/k)`-equivariant additive `φ` on `ker (galRes k K L)` vanishing on the
inertia coordinates of `q'` and non-zero under `μ` at the coordinate of some `d ∈ D_{q'}`)
through the *proved* assembly

* `Work.SSGRoute.E7cC.coordDatum_of_level_detecting_functional` (this file: the community node in
  the `CoordDatum` spelling of the assembly) and
* `Work.SSGRoute.E7cC.hcrux_of_coordDatum` (`CoordDatum` for every `μ ≠ 0` ⟹ `DetectsAt`),

together with the three structural facts about the permutation module, proved here directly:

* `instFinitePermModule` — `M` is finite;
* `permModule_psmul` — `M` is `p`-torsion;
* `permModule_inertia` — the inertia at `q` acts trivially on `M` (this is where `N ⊴ Γ` and
  `I_q ⊆ N` are used).

All three are reduced to the *coinduced* model `Rep.coind N.subtype 𝔽_p` (functions on the finite
group `Gal(K/k)` satisfying a left-`N`-invariance), where they are pointwise statements, and then
transported along the isomorphism `Rep.indCoindIso`.

**Consequence.**  The brick is *equivalent*, modulo the proved assembly above, to the community node
`exists_level_detecting_functional`, which the workspace's own analysis
(`Submission/Work/SSGRoute/E7cC/NOTE_C6_session18_tame_detector.md` and
`.../exists_tame_level_datum.lean`) identifies as the deep Shafarevich–Iwasawa-shaped input of node
`C6`.  No proof of that node exists on disk, so the statement of the node remains the single gap.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The permutation module `Ind_N^{Gal(K/k)} 𝔽_p` of the target. -/
abbrev permModule (N : Subgroup (K ≃ₐ[k] K)) : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))

/-- The coinduced model of the permutation module: a submodule of the functions
`Gal(K/k) → 𝔽_p`. -/
abbrev coindModule (N : Subgroup (K ≃ₐ[k] K)) : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))

variable {p k K}

section Structure

variable [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal] [N.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel N)]

/-- The carrier of the coinduced model is a subtype of the finite type of functions
`Gal(K/k) → 𝔽_p`. -/
instance instFiniteCoindV :
    Finite ↥(Representation.coindV N.subtype
      (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)).ρ) := by
  refine Finite.of_injective (fun f => (f.1 : (K ≃ₐ[k] K) → ZMod p))
    (fun _ _ h => Subtype.ext h)

/-- The coinduced model of the permutation module is finite. -/
instance instFiniteCoindModule : Finite ↥(coindModule (p := p) (N := N)) :=
  Finite.of_injective (fun x : ↥(coindModule (p := p) (N := N)) => x.1)
    (fun _ _ h => Subtype.ext h)

/-- The coinduced model is `p`-torsion. -/
lemma coindModule_psmul (m : ↥(coindModule (p := p) (N := N))) : p • m = 0 := by
  apply Subtype.ext
  ext g
  show p • ((m : (K ≃ₐ[k] K) → ZMod p) g) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **The inertia acts trivially on the permutation module** (`I_q ⊆ N ⊴ Γ`).

In the coinduced model the action is `(σ • f) g = f (g σ)`, and for `σ` an inertia element at `q`
the hypothesis `hNI` puts `σ` in the normal subgroup `N`, so `g σ = (g σ g⁻¹) g` with
`g σ g⁻¹ ∈ N`; the defining left-`N`-invariance of the coinduced model then gives `f (g σ) = f g`. -/
theorem coindModule_inertia
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hNI : ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → σ ∈ N)
    (σ : K ≃ₐ[k] K) (hσ : IsInertiaAt q σ) (m : ↥(coindModule (p := p) (N := N))) :
    (coindModule (p := p) (N := N)).ρ σ m = m := by
  have hσN : σ ∈ N := hNI σ hσ
  apply Subtype.ext
  ext g
  have hkey : g * σ = (g * σ * g⁻¹) * g := by group
  have hmem : g * σ * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem σ hσN g
  rw [Work.Sha2Lib.coind_subtype_ρ_apply (W := Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))
    σ m g, hkey]
  have h1 := (Representation.mem_coindV (φ := N.subtype)
    (A := ZMod p) (σ := (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)).ρ)
    (f := (m : (K ≃ₐ[k] K) → ZMod p))).mp m.2 ⟨g * σ * g⁻¹, hmem⟩ g
  simpa using h1

end Structure

section Transport

variable [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal] [N.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel N)]

/-- The isomorphism between the induced (tensor) model and the coinduced (function) model of the
permutation module. -/
abbrev permIso : permModule (p := p) (k := k) (K := K) N ≅ coindModule (p := p) (N := N) :=
  Rep.indCoindIso (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))

/-- **The permutation module is finite.** -/
instance instFinitePermModule : Finite ↥(permModule (p := p) (k := k) (K := K) N) :=
  Finite.of_injective (fun x => (permIso (p := p) (k := k) (K := K) N).hom x) (by
    intro a b h
    have h1 := congrArg (fun f => (permIso (p := p) (k := k) (K := K) N).inv f) h
    simpa using h1)

/-- **The permutation module is `p`-torsion.** -/
lemma permModule_psmul (m : ↥(permModule (p := p) (k := k) (K := K) N)) : p • m = 0 := by
  have h1 : (permIso (p := p) (k := k) (K := K) N).inv
      ((permIso (p := p) (k := k) (K := K) N).hom m) = m := by
    simp
  have h2 : (permIso (p := p) (k := k) (K := K) N).inv
      (p • ((permIso (p := p) (k := k) (K := K) N).hom m))
      = p • ((permIso (p := p) (k := k) (K := K) N).inv
          ((permIso (p := p) (k := k) (K := K) N).hom m)) :=
    map_nsmul
      (Representation.IntertwiningMap.toLinearMap
        (permIso (p := p) (k := k) (K := K) N).inv.hom) p _
  have h3 : p • ((permIso (p := p) (k := k) (K := K) N).hom m) = 0 :=
    coindModule_psmul (p := p) (N := N) _
  calc p • m = p • ((permIso (p := p) (k := k) (K := K) N).inv
        ((permIso (p := p) (k := k) (K := K) N).hom m)) := by rw [h1]
    _ = (permIso (p := p) (k := k) (K := K) N).inv
        (p • ((permIso (p := p) (k := k) (K := K) N).hom m)) := h2.symm
    _ = (permIso (p := p) (k := k) (K := K) N).inv 0 := by rw [h3]
    _ = 0 := (Representation.IntertwiningMap.toLinearMap
        (permIso (p := p) (k := k) (K := K) N).inv.hom).map_zero

/-- **The inertia acts trivially on the permutation module.** -/
theorem permModule_inertia
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hNI : ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → σ ∈ N)
    (σ : K ≃ₐ[k] K) (hσ : IsInertiaAt q σ) (m : ↥(permModule (p := p) (k := k) (K := K) N)) :
    (permModule (p := p) (k := k) (K := K) N).ρ σ m = m := by
  have hinj : Function.Injective (permIso (p := p) (k := k) (K := K) N).hom := by
    intro a b h
    have h1 := congrArg (fun f => (permIso (p := p) (k := k) (K := K) N).inv f) h
    simpa using h1
  refine hinj ?_
  rw [Rep.hom_comm_apply]
  have h1 : (permIso (p := p) (k := k) (K := K) N).hom m
      = (permIso (p := p) (k := k) (K := K) N).hom
        ((permIso (p := p) (k := k) (K := K) N).inv
          ((permIso (p := p) (k := k) (K := K) N).hom m)) := by
    rw [Iso.hom_inv_id_apply]
  rw [h1]
  exact coindModule_inertia (p := p) (N := N) q hNI σ hσ _

end Transport

/-! ## The fixed field `K₁ = K^N` and its cover in `Ω`

`K₁ := K^N` (the fixed field of the normal subgroup `N ⊴ Gal(K/k)`) is the base field of the
Shapiro/level route to the brick: the cocycle of the detecting class is the Shapiro `1`-cocycle of a
character of `Gal(L/K₁)`, and the level is built over `K₁` (where the Kummer/Grünwald input lives,
`K₁ ⊇ ζ_p` by the hypothesis `hNζ`).

The three facts recorded here are the interface of every route: `ζ ∈ K₁`, `K₁/k` is Galois (it is
the fixed field of a *normal* subgroup), and `Gal(K/K₁) = N`.  In `Ω` we take the image
`K₁Ω := (K^N).map (k → K → Ω)`, so that the level `L ⊇ K` of the datum satisfies `K₁Ω ⊆ L`. -/

section FixedField

variable [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]

/-- **`ζ` lies in the fixed field of `N`**, by the hypothesis `hNζ`. -/
theorem mem_fixedField_of_apply_eq (ζ : K) (hζ : ∀ σ ∈ N, σ ζ = ζ) :
    ζ ∈ IntermediateField.fixedField N :=
  (IntermediateField.mem_fixedField_iff N ζ).mpr hζ

/-- **`K^N/k` is Galois**: the fixed field of the normal subgroup `N`. -/
theorem isGalois_fixedField : IsGalois k ↥(IntermediateField.fixedField N) := inferInstance

/-- **The Galois group of `K` over `K^N` is `N`.** -/
theorem fixingSubgroup_fixedField_eq :
    (IntermediateField.fixedField N).fixingSubgroup = N :=
  IntermediateField.fixingSubgroup_fixedField N

end FixedField

section FixedFieldOmega

variable [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **The image of the fixed field `K^N` in `Ω`**: the base field over which the level is built.
It lies below `K`, hence below every level `L ⊇ K`. -/
noncomputable def fixedFieldOmega : IntermediateField k Ω :=
  (IntermediateField.fixedField N).map (IsScalarTower.toAlgHom k K Ω)

end FixedFieldOmega

section CoordDatum

/-- **The level input `Work.SSGRoute.E7cOmega.exists_level_detecting_functional` in the
`CoordDatum` spelling of the assembly.**  The two statements differ only in the nesting of the
existential quantifiers and of the conjunctions. -/
theorem coordDatum_of_level_detecting_functional (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    Work.SSGRoute.E7cC.CoordDatum p k K Ω M w μ := by
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φ, hφeq, hφin, d, hdmem, hdval⟩ :=
    Work.SSGRoute.E7cOmega.exists_level_detecting_functional p k K Ω M hM w q hwq hpq hI μ hμ
  exact ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φ, hφeq, hφin, d, hdmem, hdval⟩

end CoordDatum


section RegularModule

attribute [local instance] Classical.propDecidable

/-- The regular module `𝔽_p[Γ] = Ind_⊥^Γ 𝔽_p`, in the coinduced (function) model: functions on `Γ`
with the invariance condition of the trivial subgroup (which is vacuous). -/
noncomputable abbrev regularModule (p : ℕ) (Γ : Type) [Group Γ] :
    Rep.{0} SSGRoute.PTExt.Coeff Γ :=
  Rep.coind (⊥ : Subgroup Γ).subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥(⊥ : Subgroup Γ) (ZMod p))

/-- **The generator `δ_1` of the regular module**: the indicator function of the identity, which
lies in the coinduced model because the invariance condition is vacuous for the trivial subgroup. -/
noncomputable def diracOne (p : ℕ) (Γ : Type) [Group Γ] :
    ↥(regularModule p Γ) :=
  ⟨fun γ => if γ = 1 then 1 else 0, by
    intro g h
    have hg : (⊥ : Subgroup Γ).subtype g = (1 : Γ) := by
      have h1 : g = (1 : ↥(⊥ : Subgroup Γ)) := Subsingleton.elim _ _
      rw [h1]
      rfl
    rw [hg, one_mul]
    simp⟩

end RegularModule

section InvariantCase

variable [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K)) [N.Normal] [N.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel N)]

/-- The constant function `Γ → 𝔽_p` lies in the coinduced model (the defining invariance is
automatic because the coefficients are trivial). -/
lemma const_mem_coindV (x : ZMod p) :
    (fun _ : K ≃ₐ[k] K => x) ∈ Representation.coindV N.subtype
      (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)).ρ := by
  rw [Representation.mem_coindV]
  intro g h
  rfl

/-- The `Coeff`-linear map sending `x` to the constant function with value `x`. -/
noncomputable def constLinearMap :
    ZMod p →ₗ[SSGRoute.PTExt.Coeff] ↥(Representation.coindV N.subtype
      (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)).ρ) where
  toFun x := ⟨fun _ => x, const_mem_coindV (p := p) (N := N) x⟩
  map_add' a b := Subtype.ext (funext fun _ => rfl)
  map_smul' c a := Subtype.ext (funext fun _ => rfl)

/-- The constant-function morphism `𝔽_p ⟶ Rep.coind N.subtype 𝔽_p`: the trivial summand of the
permutation module, in the coinduced model. -/
noncomputable def constCoind :
    Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ coindModule (p := p) (N := N) :=
  Rep.ofHom (Representation.IntertwiningMap.mk
    (ρ := (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p)).ρ)
    (σ := (coindModule (p := p) (N := N)).ρ)
    (constLinearMap (p := p) (N := N)) (by
      intro g
      ext x g'
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [Work.Sha2Lib.coind_subtype_ρ_apply]
      rfl))

/-- The constant function is fixed by the `Gal(K/k)`-action of the coinduced model. -/
lemma constCoind_fixed (σ : K ≃ₐ[k] K) :
    (coindModule (p := p) (N := N)).ρ σ ((constCoind (p := p) (N := N)).hom 1)
      = (constCoind (p := p) (N := N)).hom 1 := by
  apply Subtype.ext
  funext g
  rw [Work.Sha2Lib.coind_subtype_ρ_apply]
  rfl

/-- The trivial summand of the permutation module itself: the constants. -/
noncomputable def constToPerm :
    Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p) ⟶
      permModule (p := p) (k := k) (K := K) N :=
  constCoind (p := p) (N := N) ≫ (permIso (p := p) (k := k) (K := K) N).inv

/-- The constant vector of the permutation module. -/
noncomputable def permConstVec : ↥(permModule (p := p) (k := k) (K := K) N) :=
  (constToPerm (p := p) (k := k) (K := K) N).hom 1

/-- The constant vector is `Gal(K/k)`-fixed. -/
theorem permConstVec_fixed (σ : K ≃ₐ[k] K) :
    (permModule (p := p) (k := k) (K := K) N).ρ σ (permConstVec (p := p) (k := k) (K := K) N)
      = permConstVec (p := p) (k := k) (K := K) N := by
  show (permModule (p := p) (k := k) (K := K) N).ρ σ
      ((permIso (p := p) (k := k) (K := K) N).inv
        ((constCoind (p := p) (N := N)).hom 1))
    = (permIso (p := p) (k := k) (K := K) N).inv ((constCoind (p := p) (N := N)).hom 1)
  rw [← Rep.hom_comm_apply (permIso (p := p) (k := k) (K := K) N).inv σ
    ((constCoind (p := p) (N := N)).hom 1)]
  rw [constCoind_fixed]

/-- **The invariant case of the rank-one brick.**  If `φ ∈ Ext¹_{D_w}(res M, ℤ)` does not kill the
constant vector of the permutation module (equivalently, if it is non-zero on the trivial summand
`M^{Gal(K/k)} ≅ 𝔽_p`, which for the permutation module is the *only* trivial summand), then `φ` is
detected — and this needs **no arithmetic at all**: it is the statement
`Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ` (proved, axiom-clean), i.e. the trivial module
over the sumbled `𝔽_p` detected by the proved `Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial`,
pushed forward along the invariant summand. -/
theorem C6_rankOneBrick_invariantCase
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (permModule (p := p) (k := k) (K := K) N))
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0)
    (hφι : (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (constToPerm (p := p) (k := k) (K := K) N))).comp φ (zero_add 1) ≠ 0) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq
      (permModule (p := p) (k := k) (K := K) N) φ :=
  Work.SSGRoute.Sha2Lib.detectorInvariantCaseExtZ p k K
    (permModule (p := p) (k := k) (K := K) N) Ω
    (fun m => permModule_psmul (p := p) (k := k) (K := K) N m)
    w q hwq hpq
    (fun σ hσ m => permModule_inertia (p := p) (k := k) (K := K) N q hNI σ hσ m)
    (permConstVec (p := p) (k := k) (K := K) N)
    (fun σ => permConstVec_fixed (p := p) (k := k) (K := K) N σ)
    φ hφ ⟨constToPerm (p := p) (k := k) (K := K) N, rfl, hφι⟩

end InvariantCase

/-! ## The route through the Shapiro class: the detecting-cocycle datum

Everything below is the *assembly* of the brick from the following single arithmetic input: for
every non-zero `D_w`-equivariant `μ : res_{D_w} M ⟶ ℚ/ℤ` there are a finite Galois level `L ⊇ K`
over `k`, a place `q' | w` with `p ∤ e(q'|q)`, and a `1`-cocycle `z` of `H¹(Gal(L/k), res M)`
which *vanishes on the inertia* at `q'` and whose value at some `d` in the decomposition group of
`q'` is not killed by `μ`.

That datum is the shape in which the Shapiro construction of the detector delivers its witness: the
cocycle `z` is the Shapiro `1`-cocycle of a character `χ` of the subgroup `Gal(L/K₁)`
(`K₁ = K^N`) with `z γ = (x ↦ χ (s_x γ s_{xγ}⁻¹))`, so that `μ (z d)` computes the coset sum
`Σ_u c_u χ (Frob_u)` and is made non-zero by prescribing the values of `χ` at the Frobenius
elements of the places over `q` with Grünwald's theorem over `K₁`; the inertia-vanishing is
`χ` killing the inertia at `q'`, which holds because the extension `L/K` is unramified at `q'` (the
ramified part `K/K₁` lies in the kernel of `χ`).

The present section converts that datum into `DetectsAt`, using only *proved* workspace lemmas:
`SSGStage.divRep_detecting_class` (`φ` is a connecting class `δμ`), the `ℚ/ℤ`-criterion
`E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff` (the level pairing is the `μ`-pushforward of the
class), `E7cC.isUnramifiedClassAt_eCoh_of_vanishes_on_inertia` (a cocycle vanishing on the inertia
defines an unramified class) and `E7cC.extHMap_eCoh_id_ne_zero_of_value` (a single non-zero value
certifies that the class is non-zero). -/

section CocycleDatum

/-- **The detecting-cocycle datum of the rank-one brick.**  For a `D_w`-equivariant functional
`μ : res_{D_w} M ⟶ ℚ/ℤ` there are a level `L ⊇ K` (finite Galois over `k`), a place `q' | w` with
`p ∤ e(q'|q)`, and a `1`-cocycle `z` of `H¹(Gal(L/k), res M)` with

* `z γ = 0` for every inertia element `γ` at `q'` (the class is unramified), and
* `μ (z d) ≠ 0` for some `d` in the decomposition group of `q'`.

The value clause is stated on the underlying type `M.V` of the coefficient module (the restriction
functors do not change the underlying type), so that `μ.hom` applies to `z d` directly. -/
def LevelCocycleDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
    Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
    ∃ z : ↥(groupCohomology.cocycles₁ (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M)),
      (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        (z : (↥L ≃ₐ[k] ↥L) → M.V) γ = 0) ∧
      ∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q') ∧
        μ.hom ((z : (↥L ≃ₐ[k] ↥L) → M.V) d) ≠ 0

/-- **The detecting-cocycle datum produces the detector.**

The proof is the assembly described in the header of this section: `φ = δ μ` (or rather, the class
`δ μ` of the datum is the class the brick has to detect at `μ`), the pairing is computed by the
`ℚ/ℤ`-criterion at the decomposition group of `q'`, and its non-vanishing is read off the non-zero
value of the cocycle `z` supplied by the datum. -/
theorem detectsAt_of_levelCocycleDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (hM : ∀ m : M.V, p • m = 0)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (h : LevelCocycleDatum p k K Ω w q hwq M μ) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M
      ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
            (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1)) := by
  classical
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq'lies, hcop, z, hzit, d, hdmem, hdval⟩ := h
  letI : FiniteDimensional k ↥L := hfdL
  letI : IsGalois k ↥L := hgalL
  have hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := hq'lies
  letI : Fintype ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L)
    (NK.GlobalCFT.Place.ofFinite q')) := Fintype.ofFinite _
  let A : Rep.{0} SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (SSGRoute.PTExt.galRes k K ↥L) M
  let hL : SSGRoute.PTExt.extH A 1 :=
    SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z)
  refine ⟨L, hnfL, hfdL, hgalL, q', hq', hL, ?_, hcop, ?_⟩
  · exact Work.SSGRoute.E7cC.isUnramifiedClassAt_eCoh_of_vanishes_on_inertia A q' z hzit
  · -- the restricted cocycle at `D_{q'}`, whose value at `d` is `z d`
    let D : Subgroup (↥L ≃ₐ[k] ↥L) := SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')
    let A' : Rep.{0} SSGRoute.PTExt.Coeff ↥D := Rep.res D.subtype A
    let zD : ↥(groupCohomology.cocycles₁ A') :=
      groupCohomology.mapCocycles₁ D.subtype (CategoryTheory.CategoryStruct.id A') z
    have hrestrict : SSGRoute.PTExt.extHRestrict D hL =
        SSGRoute.PTExt.eCoh 1 ↥D A' ((groupCohomology.H1π A').hom zD) :=
      Work.SSGRoute.E7cOmega.extHRestrict_eCoh_one (↥L ≃ₐ[k] ↥L) A D z
    -- the value of the restricted cocycle at `d` is `z d`
    have hzval : (zD : ↥D → A'.V) ⟨d, hdmem⟩ = z d := by
      show (groupCohomology.mapCocycles₁ D.subtype (CategoryTheory.CategoryStruct.id A') z
        : ↥D → A'.V) ⟨d, hdmem⟩ = z d
      rw [groupCohomology.coe_mapCocycles₁]
      rfl
    have hval : μ.hom ((zD : ↥D → M.V) ⟨d, hdmem⟩) ≠ 0 := by
      rw [hzval]
      exact hdval
    have hp := Work.SSGRoute.SSGStage.levelPair_eCoh_cocycles_ne_zero p k K Ω M hM w L q' hq' μ
      zD ⟨⟨d, hdmem⟩, hval⟩
    rw [hrestrict]
    exact hp

end CocycleDatum

/-- **The rank-one brick of `C6`.**  The detector for the permutation module
`Ind_N^{Gal(K/k)} 𝔽_p`, from the level input `Work.SSGRoute.E7cOmega.exists_level_detecting_functional`
(node `C6`'s arithmetic core) through the proved assembly
`Work.SSGRoute.E7cC.hcrux_of_coordDatum`. -/
theorem C6_rankOneBrick (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  classical
  haveI : N.FiniteIndex := inferInstance
  haveI : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  intro φ hφ
  exact Work.SSGRoute.E7cC.hcrux_of_coordDatum p k K Ω
    (permModule (p := p) (k := k) (K := K) N)
    (fun m => permModule_psmul (p := p) (k := k) (K := K) N m)
    w q hwq hpq
    (fun σ hσ m => permModule_inertia (p := p) (k := k) (K := K) N q hNI σ hσ m)
    φ hφ
    (fun μ hμ =>
      coordDatum_of_level_detecting_functional p k K Ω
        (permModule (p := p) (k := k) (K := K) N)
        (fun m => permModule_psmul (p := p) (k := k) (K := K) N m)
        w q hwq hpq
        (fun σ hσ m => permModule_inertia (p := p) (k := k) (K := K) N q hNI σ hσ m)
        μ hμ)

end

end Work.SSGRoute.PTdualControl
