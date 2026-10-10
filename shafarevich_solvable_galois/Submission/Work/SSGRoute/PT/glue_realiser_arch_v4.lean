import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.exists_transversal_places_wc
import Submission.Work.SSGRoute.PT.levelClassOf_add
import Submission.Work.SSGRoute.PT.liesOver_linked
import Submission.Work.SSGRoute.e9_local_decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design: `_lead_design/flags_2305/flags_2305.md` (SEAM-PLACE RESTATEMENT of the flags_1730
`glue_realiser_arch_v2`): `hpairArch` is now required only at the seam place
`u = mk (φc c |_L)` of each level `L` (binder `hus`), instead of at every `u | wc c` with
`D_u = ⟨res_L c⟩`.  The hypothesis is weaker, so the proof applies `hpairArch` only at
`u_c = mk (φc c |_L)`, discharging `hus` by `rfl`.

Helpers (proved, imported, not re-proved): `PT.decompK_linked`, `PT.liesOver_linked`,
`PT.wc_orbit_injective`, `PT.exists_transversal_places_wc`, `PT.levelClassOf_add`.
The finite part is `PT.glue_realiser_abstract` (v4 G, proved), run with the `C`-sum kept inside
`horth`.  The archimedean components `βc c (β c)` are given, so no realiser is needed there.

Bridge lemma of this file: `PT.pair_add_snd_zpowers_seam`, additivity of the archimedean pairing
`pair ⟨c⟩ (β c) ·` in its second variable, from the seam-place `hpairArch`.  It is what makes the
functional `Λ = Σ_{S₁} pair + Σ_C pair` of the finite part *linear* on the globally locally
constant `M'`-cocycles, which the coordinate splitting of `glue_realiser_abstract` needs.

Note: `PT.levelClassOf_add` is stated both here (in `PT/levelClassOf_add`) and in
`PT/glue_arch_own`; importing both modules into one file clashes on the declaration name.  This
file imports the former.
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory


/-! `glue_realiser_arch_v4` — copy of `glue_realiser_arch_v3`
(`Submission/Work/SSGRoute/PT/glue_realiser_arch_v2.lean`) with the (unused, and therefore
deletable) `hβg_unr` binder removed from the signature, so that the lemma is independent of the
dictionary's unramified *converse*.  The proof body is unchanged: `hβg_unr` is not referenced in it.
Built by the hub lane for `finiteS_converse_canonical_v8`. -/

namespace Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section PairAddZpSeam

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField ↥K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (↥K ≃ₐ[k] ↥K) T]
  [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (↥K ≃ₐ[k] ↥K) M]
  [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) M] [Finite M]

/-- **Additivity of the archimedean pairing in its second variable** (seam-place form of
`hpairArch`).  Two globally locally constant `M'`-cocycles `b, b'` factor simultaneously at one
level `L` (`PT.exists_level_factors_locConstOnTwo`, `H = ⊤`), and `b + b'` factors through
`b₀ + b₀'`; `hpairArch` at the *seam* place `u = mk (φc c |_L)` pins all three values, and
`levelClassOf (b₀ + b₀') = levelClassOf b₀ + levelClassOf b₀'`, `extHRestrict`, `levelPair`, `iota`
and `χ_L` being additive on the relevant (`p`-torsion) classes, gives the claim. -/
theorem pair_add_snd_zpowers_seam
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (wc : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K)
    (βc : ∀ c : (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (wc c)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (wc c)) 1)
    (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hseam : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x)) ∧
      wc c = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))))
    (hpairArch : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
          (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (wc c))
          (hus : u = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥L) Ω))))
          (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
          (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g),
          (∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) →
          pair (Subgroup.zpowers c) a b =
            χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u
              (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
                (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
                  (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)))))
    (c : (Ω ≃ₐ[k] Ω)) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hbc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b')
    (hlc : SSGRoute.IsLocConstOn ⊤ b) (hlc' : SSGRoute.IsLocConstOn ⊤ b') :
    pair (Subgroup.zpowers c) a (b + b') = pair (Subgroup.zpowers c) a b
      + pair (Subgroup.zpowers c) a b' := by
  classical
  -- ## a common finite normal level for `b` and `b'`
  obtain ⟨L, hLfin, hLnorm, hKL, b₀, b₀', hb₀, hb₀'⟩ :=
    exists_level_factors_locConstOnTwo k Ω K (⊤ : Subgroup (Ω ≃ₐ[k] Ω)) b b' hlc hlc'
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : IsGalois k L := inferInstance
  letI : NumberField ↥L := inferInstance
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## the twisted cocycle conditions
  have hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g := by
    intro g h
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) Ω g
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) Ω h
    have h1 := hbc σ trivial τ trivial
    rw [hb₀ (σ * τ) trivial, map_mul (SSGRoute.res k L) σ τ, hb₀ σ trivial,
      hb₀ τ trivial] at h1
    have hres : SSGRoute.res k K σ
        = SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L σ) :=
      (SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω) σ).symm
    rw [hres, add_comm] at h1
    exact h1
  have hψ' : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀' (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀' h + b₀' g := by
    intro g h
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) Ω g
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥L) Ω h
    have h1 := hbc' σ trivial τ trivial
    rw [hb₀' (σ * τ) trivial, map_mul (SSGRoute.res k L) σ τ, hb₀' σ trivial,
      hb₀' τ trivial] at h1
    have hres : SSGRoute.res k K σ
        = SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L σ) :=
      (SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω) σ).symm
    rw [hres, add_comm] at h1
    exact h1
  have hψsum : ∀ g h : ↥L ≃ₐ[k] ↥L,
      (b₀ + b₀') (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • (b₀ + b₀') h + (b₀ + b₀') g := by
    intro g h
    rw [Pi.add_apply, hψ g h, hψ' g h, Pi.add_apply, Pi.add_apply, smul_add]
    abel
  -- ## the seam place
  let u : NK.GlobalCFT.Place ↥L := NK.GlobalCFT.Place.ofInfinite
    (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥L) Ω)))
  have hseamc := hseam c hc2 hc1
  have hu : NK.GlobalCFT.Place.LiesOver u (wc c) := by
    rw [hseamc.2]
    exact liesOver_linked k Ω K L (φc c)
  -- ## cocycles on `⟨c⟩` and their representatives
  have hbcc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
    Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hbc
  have hbcc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' :=
    Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hbc'
  have hrep : ∀ σ ∈ Subgroup.zpowers c, b σ = b₀ (SSGRoute.res k L σ) :=
    fun σ _ => hb₀ σ trivial
  have hrep' : ∀ σ ∈ Subgroup.zpowers c, b' σ = b₀' (SSGRoute.res k L σ) :=
    fun σ _ => hb₀' σ trivial
  have hrepS : ∀ σ ∈ Subgroup.zpowers c, (b + b') σ = (b₀ + b₀') (SSGRoute.res k L σ) := by
    intro σ _
    rw [Pi.add_apply, hb₀ σ trivial, hb₀' σ trivial]
    rfl
  -- ## the three instances of `hpairArch` at the seam place, and the comparison of the values
  rw [hpairArch c hc2 hc1 a (b + b') ha L hKL u hu rfl (b₀ + b₀') hψsum hrepS,
    hpairArch c hc2 hc1 a b ha L hKL u hu rfl b₀ hψ hrep,
    hpairArch c hc2 hc1 a b' ha L hKL u hu rfl b₀' hψ' hrep']
  rw [show SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L (b₀ + b₀') hψsum)
      = SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)
        + SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ') from by
    rw [levelClassOf_add (p := p) (k := k) (Ω := Ω) (K := K) (L := L) (T := T) (M := M)
        hKL b₀ b₀' hψ hψ' hψsum,
      SSGRoute.PTExt.extHRestrict_add]]
  -- ## additivity of `levelPair`, of `iota` and of `χ`
  have hptor : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 :=
    fun x => nsmul_eq_zero_of_zmod p x
  have hJ : p • SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ) = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  have hJ' : p • SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ') = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  have hlp := Work.SSGRoute.levelPair_add_h (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
    (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ))
    (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ'))
  have hi := pt_iota_add (k := k) (L := ↥L) u
    (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)))
    (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ')))
  have hz1 : p • SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ)) = 0 :=
    (Work.SSGRoute.PT.levelPair_nsmul_snd (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) p (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ))).symm.trans
      ((congrArg (fun z => SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a) z) hJ).trans
        (Work.SSGRoute.levelPair_zero_h (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)))
  have hz2 : p • SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ')) = 0 :=
    (Work.SSGRoute.PT.levelPair_nsmul_snd (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) p (βc c a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀' hψ'))).symm.trans
      ((congrArg (fun z => SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a) z) hJ').trans
        (Work.SSGRoute.levelPair_zero_h (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)))
  refine (congrArg (fun z => χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u z)) hlp).trans ?_
  exact (congrArg (χ L hKL) hi).trans
    (hχadd L hKL _ _ (pt_iota_ptorsion p u _ hz1) (pt_iota_ptorsion p u _ hz2))

end PairAddZpSeam

/-- SEAM-PLACE RESTATEMENT (flags_2305).  Identical to `glue_realiser_arch_v2` except that
`hpairArch` is required only at the seam place `u = mk (φc c |_L)` of each level `L` (binder
`hus`), instead of at every `u | wc c` with `D_u = ⟨res_L c⟩`.  The hypothesis is weaker, so any
proof that applies `hpairArch` only at `u_c = mk (φc c |_L)` goes through with `hus := rfl` in place
of `decompK_linked`.  The G1⁺ hub can supply it without a `τ`-invariance argument (flags_2305.md).

Piece G⁺ of `finiteS_converse_canonical_v6`: the idèle gluing with the archimedean components
(restates `PT.glue_realiser_arch` with the v6 binders: `hC1`, the seam `φc`/`hseam`, and the
all-level `hpairArch`; the conclusion is unchanged).

Route.
* Finite part: `PT.glue_realiser_abstract` (v4 G, proved), run with the `C`-sum kept inside `horth`.
  `Λ(b) := Σ_{S₁} pair + Σ_C pair` is additive in `b` and kills the global cocycles vanishing on
  inertia outside `S₁`.  It factors through the local classes at `R \ S₁`, is split into local
  functionals, and is realised by unramified local cocycles (`hreal_unr`).
* Archimedean part: no realiser is needed, because the components `βc c (β c)` are given.
  `ext_idele_shapiro` over a transversal of ALL places of `K` that contains `R` and the `wc c`.
  Such a transversal exists because the `wc c` (`c ∈ C`) are in pairwise distinct `Gal(K/k)`-orbits
  (`wc_orbit_injective` applied to `hseam` and `hCdisj`; `hC1` makes `hseam` applicable), and none of
  them is finite.
* The last clause is the Shapiro vanishing off the chosen orbits. -/
theorem glue_realiser_arch_v4 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (hpair_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        pair (SSGRoute.decomp k A) a b = 0)
    (hreal_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
        (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          lam (b + b') = lam b + lam b') →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
        ∃ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
          ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            pair (SSGRoute.decomp k A) a b = lam b)
    (βg : ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        (SSGRoute.PTExt.unitsK k ↥K) 1)
    (hβg_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      βg (b + b') = βg b + βg b')
    (hβg_ker : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (βg b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b))
    (hβg_onto : ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
      SSGRoute.IsLocConstOn ⊤ b ∧ βg b = y)
    (hsq : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βl A hA b)
    (wc : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K)
    (βc : ∀ c : (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (wc c)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (wc c)) 1)
    (hwc : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        wc c ≠ NK.GlobalCFT.Place.ofFinite q) ∧
      (Subgroup.zpowers c).map (SSGRoute.res k K) = SSGRoute.PTExt.decompK (k := k) (wc c))
    (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hseam : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x)) ∧
      wc c = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))))
    (hβc_add : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
      βc c (b + b') = βc c b + βc c b')
    (hβc_ker : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      (βc c b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (hβc_onto : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc c b = y)
    (hβc_sq : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) (wc c)
        (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βc c b)
    (hpairArch : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
          (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (wc c))
          (hus : u = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥L) Ω))))
          (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
          (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g),
          (∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) →
          pair (Subgroup.zpowers c) a b =
            χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u
              (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
                (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
                  (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)))))
    (S₁ : Finset (ValuationSubring Ω)) (hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A)
    (hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B)
    (hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
    (hC1 : ∀ c ∈ C, c ≠ 1)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b +
        ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) :

    ∃ (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v),
      (∀ A ∈ S₁, A ∈ R) ∧
      (∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ∃ v ∈ R, SSGRoute.IsConjPlace k v B) ∧
      ∃ αe : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M,
        (∀ A ∈ S₁, αe A = α A) ∧
        (∀ v ∈ R, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v) (αe v) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k v) (αe v)) ∧
        (∀ v ∈ R, v ∉ S₁ → ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → αe v σ = 0) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R), pair (SSGRoute.decomp k v) (αe v) b)
            + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) ∧
        ∃ X : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) (SSGRoute.PTExt.idelesK k ↥K) 1,
          (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
            SSGRoute.PTExt.extLoc (k := k)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X =
            βl v (hRfin v hv) (αe v)) ∧
          (∀ c ∈ C, SSGRoute.PTExt.extLoc (k := k) (wc c) X = βc c (β c)) ∧
          (∀ w : NK.GlobalCFT.Place ↥K,
            (∀ (v : ValuationSubring Ω) (hv : v ∈ R) (σ : ↥K ≃ₐ[k] ↥K),
              σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) ≠ w) →
            (∀ c ∈ C, ∀ σ : ↥K ≃ₐ[k] ↥K, σ • wc c ≠ w) →
              SSGRoute.PTExt.extLoc (k := k) w X = 0) := by
  classical
  -- ## 1. the transversal `R` of the finite places, containing `S₁`
  obtain ⟨R, hS₁R, hRfin, hRdisj, hRcov⟩ := exists_transversal_finPlaces k Ω S₁ hS₁fin hS₁disj
  -- ## 2. the places of `R` outside `S₁` are good (unramified in `K`, not over `p`)
  have hRne : ∀ v ∈ R, v ∉ S₁ → ¬ SSGRoute.IsRamifiedIn k K v ∧ ¬ v.valuation (p : Ω) < 1 := by
    intro v hvR hvS
    constructor
    · intro hram
      obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram v (hRfin v hvR) (Or.inl hram)
      exact hvS (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj ▸ hA₀)
    · intro hval
      obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram v (hRfin v hvR) (Or.inr hval)
      exact hvS (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj ▸ hA₀)
  -- ## 3. the coefficient module, the global cocycles, and the local quotients
  let M' := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  let F := (Ω ≃ₐ[k] Ω) → M'
  let Z := Work.SSGRoute.lcCocycles p k Ω K M' ⊤
  let ı := {v : ValuationSubring Ω // v ∈ R ∧ v ∉ S₁}
  let Kv : ValuationSubring Ω → Submodule (ZMod p) F := fun v =>
    { carrier := {f : F | ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → f σ = 0}
      zero_mem' := fun σ _ => rfl
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_setOf_eq] at hf hg ⊢
        intro σ hσ
        rw [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
      smul_mem' := fun c {f} hf => by
        simp only [Set.mem_setOf_eq] at hf ⊢
        intro σ hσ
        rw [Pi.smul_apply, hf σ hσ, smul_zero] }
  let Ψ : ↥Z →ₗ[ZMod p] (∀ v : ı, F ⧸ Kv v.1) :=
    LinearMap.pi (fun v : ı => (Kv v.1).mkQ.comp Z.subtype)
  -- ## 4. monotonicity of the two predicates in the subgroup
  have hmono_loc : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : F), SSGRoute.IsLocConstOn ⊤ f →
      SSGRoute.IsLocConstOn H f := by
    intro H f hf
    obtain ⟨U, hUo, hU⟩ := hf
    exact ⟨U, hUo, fun g _ u hu _ => hU g trivial u hu trivial⟩
  have hmono_coc : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : F),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ f →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H f := by
    intro H f hf
    exact fun g _ h _ => hf g trivial h trivial
  -- ## 5. `Ψ` has finitely supported values
  have hsupp : ∀ x : ↥Z, {v : ı | Ψ x v ≠ 0}.Finite := by
    intro x
    have hxc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (x.1 : F) := x.2.1
    have hxl : SSGRoute.IsLocConstOn ⊤ (x.1 : F) := x.2.2
    obtain ⟨Sb, hSbfin, hSbdisj, hSbvanish⟩ :=
      vanishingInertia_finite k Ω K M' (x.1 : F) hxc hxl
    have hmem : ∀ v : ı, Ψ x v ≠ 0 → ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v.1 := by
      intro v hv
      by_contra hno
      push_neg at hno
      have hKv : (x.1 : F) ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → (x.1 : F) σ = 0
        exact fun σ hσ => hSbvanish v.1 (hRfin v.1 v.2.1) hno σ hσ
      have hzero : Ψ x v = 0 := by
        rw [show Ψ x v = (Kv v.1).mkQ (x.1 : F) from rfl, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hKv
      exact hv hzero
    let g : ↥{v : ı | Ψ x v ≠ 0} → ↥Sb :=
      fun v => ⟨Classical.choose (hmem v.1 v.2), (Classical.choose_spec (hmem v.1 v.2)).1⟩
    have hginj : Function.Injective g := by
      intro v w hvw
      have hv1 : SSGRoute.IsConjPlace k (Classical.choose (hmem v.1 v.2)) v.1.1 :=
        (Classical.choose_spec (hmem v.1 v.2)).2
      have hw1 : SSGRoute.IsConjPlace k (Classical.choose (hmem w.1 w.2)) w.1.1 :=
        (Classical.choose_spec (hmem w.1 w.2)).2
      have hab : Classical.choose (hmem v.1 v.2) = Classical.choose (hmem w.1 w.2) :=
        congrArg Subtype.val hvw
      have hconj : SSGRoute.IsConjPlace k v.1.1 w.1.1 := by
        obtain ⟨s1, hs1⟩ := hv1
        obtain ⟨s2, hs2⟩ := hw1
        refine ⟨s2 * s1⁻¹, ?_⟩
        calc (s2 * s1⁻¹) • v.1.1 = s2 • (s1⁻¹ • v.1.1) := mul_smul _ _ _
          _ = s2 • (s1⁻¹ • (s1 • Classical.choose (hmem v.1 v.2))) := by rw [hs1]
          _ = s2 • Classical.choose (hmem v.1 v.2) := by rw [inv_smul_smul]
          _ = s2 • Classical.choose (hmem w.1 w.2) := by rw [hab]
          _ = w.1.1 := hs2
      exact Subtype.ext (Subtype.ext (hRdisj v.1.1 v.1.2.1 w.1.1 w.1.2.1 hconj))
    haveI : Finite ↥Sb := Sb.finite_toSet.to_subtype
    exact Finite.of_injective g hginj
  -- ## 6. the functional `Λ = ∑_{S₁} pair (decomp k A) (α A) · + ∑_C pair ⟨c⟩ (β c) ·`
  have hpair_zero : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M), SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      pair (SSGRoute.decomp k A) a 0 = 0 := by
    intro A hA a ha
    have h0lc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (0 : F) :=
      ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩
    have h0c : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (0 : F) :=
      fun g _ h _ => by show (0 : M') = 0 + (SSGRoute.res k K) g • (0 : M'); rw [smul_zero, add_zero]
    have h := pair_add_snd_decomp p k Ω K ζ hζ hζK T hT χ hχadd M βl pair hpair A hA a 0 0
      ha h0lc h0lc h0c h0c
    rw [add_zero] at h
    have h2 : pair (SSGRoute.decomp k A) a 0 + 0
        = pair (SSGRoute.decomp k A) a 0 + pair (SSGRoute.decomp k A) a 0 := by
      rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hΛlin : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A) →
      ∃ LA : ↥Z →ₗ[ZMod p] ZMod p,
        ∀ x : ↥Z, LA x = pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro A hA hαA
    obtain ⟨LA, hLA⟩ := zmodLinearMap_of_addHom (p := p)
      { toFun := fun x : ↥Z => pair (SSGRoute.decomp k A) (α A) (x.1 : F)
        map_zero' := by
          show pair (SSGRoute.decomp k A) (α A) ((0 : ↥Z).1 : F) = 0
          rw [show ((0 : ↥Z).1 : F) = 0 from rfl]
          exact hpair_zero A hA (α A) hαA
        map_add' := by
          intro x y
          have hb : ∀ z : ↥Z, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (z.1 : F) :=
            fun z => hmono_coc _ _ z.2.1
          have hl : ∀ z : ↥Z, SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (z.1 : F) :=
            fun z => hmono_loc _ _ z.2.2
          have h := pair_add_snd_decomp p k Ω K ζ hζ hζK T hT χ hχadd M βl pair hpair A hA
            (α A) (x.1 : F) (y.1 : F) hαA (hl x) (hl y) (hb x) (hb y)
          rw [show (x.1 : F) + (y.1 : F) = ((x + y : ↥Z).1 : F) from rfl] at h
          exact h }
    exact ⟨LA, fun x => by rw [hLA x]; rfl⟩
  -- the `S₁`-part of `Λ`
  let LA : ValuationSubring Ω → ↥Z →ₗ[ZMod p] ZMod p := fun A =>
    if h : A ∈ S₁ then Classical.choose (hΛlin A (hS₁fin A h) (hα A h).2) else 0
  let Λ₀ : ↥Z →ₗ[ZMod p] ZMod p := ∑ A ∈ S₁, LA A
  have hLA : ∀ (A : ValuationSubring Ω) (hA : A ∈ S₁) (x : ↥Z),
      LA A x = pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro A hA x
    rw [show LA A = Classical.choose (hΛlin A (hS₁fin A hA) (hα A hA).2) from dif_pos hA]
    exact Classical.choose_spec (hΛlin A (hS₁fin A hA) (hα A hA).2) x
  have hΛ₀ : ∀ x : ↥Z, Λ₀ x = ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F) := by
    intro x
    have h1 : (∑ A ∈ S₁, LA A) x = ∑ A ∈ S₁, LA A x := LinearMap.sum_apply S₁ LA x
    simp only [Λ₀]
    rw [h1]
    exact Finset.sum_congr rfl fun A hA => hLA A hA x
  -- the `C`-part of `Λ`: additivity of the archimedean pairing
  have hpairC_zero : ∀ c ∈ C, pair (Subgroup.zpowers c) (β c) (0 : F) = 0 := by
    intro c hcC
    have h0coc : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (0 : F) := fun g _ h _ => by
      show (0 : M') = 0 + (SSGRoute.res k K) g • (0 : M'); rw [smul_zero, add_zero]
    have h0lc : SSGRoute.IsLocConstOn ⊤ (0 : F) := ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩
    have h := pair_add_snd_zpowers_seam p k Ω K T M χ hχadd pair wc βc φc hseam hpairArch
      c (hCinv c hcC) (hC1 c hcC) (β c) (hβ c hcC) 0 0 h0coc h0coc h0lc h0lc
    rw [add_zero] at h
    have h2 : pair (Subgroup.zpowers c) (β c) 0 + 0
        = pair (Subgroup.zpowers c) (β c) 0 + pair (Subgroup.zpowers c) (β c) 0 := by
      rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  obtain ⟨LT, hLT⟩ := zmodLinearMap_of_addHom (p := p)
    { toFun := fun x : ↥Z => ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) (x.1 : F)
      map_zero' := by
        refine Finset.sum_eq_zero fun c hc => ?_
        simpa using hpairC_zero c hc
      map_add' := by
        intro x y
        have hb : ∀ z : ↥Z, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ (z.1 : F) := fun z => z.2.1
        have hl : ∀ z : ↥Z, SSGRoute.IsLocConstOn ⊤ (z.1 : F) := fun z => z.2.2
        have h1 : (∑ c ∈ C, pair (Subgroup.zpowers c) (β c) ((x + y : ↥Z).1 : F))
            = ∑ c ∈ C, (pair (Subgroup.zpowers c) (β c) (x.1 : F)
                + pair (Subgroup.zpowers c) (β c) (y.1 : F)) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          exact pair_add_snd_zpowers_seam p k Ω K T M χ hχadd pair wc βc φc hseam hpairArch
            c (hCinv c hc) (hC1 c hc) (β c) (hβ c hc) (x.1 : F) (y.1 : F)
            (hb x) (hb y) (hl x) (hl y)
        rw [h1, Finset.sum_add_distrib] }
  -- the total functional `Λ`
  let Λ : ↥Z →ₗ[ZMod p] ZMod p := Λ₀ + LT
  have hΛ : ∀ x : ↥Z, Λ x
      = (∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F))
        + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) (x.1 : F) := by
    intro x
    have h1 : Λ x = (∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F)) + LT x := by
      show Λ₀ x + LT x
        = (∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F)) + LT x
      rw [hΛ₀ x]
    exact h1.trans (congrArg (fun z =>
      (∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) (x.1 : F)) + z) (hLT x))
  -- ## 7. `Λ` vanishes on the kernel of `Ψ`
  have hoff : ∀ (b : F), SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b →
      SSGRoute.IsLocConstOn ⊤ b →
      (∀ v ∈ R, v ∉ S₁ → ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → b σ = 0) →
      (∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b)
        + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0 := by
    intro b hbc hlc hbunr
    refine horth b hbc hlc ?_
    intro B hBfin hBnc σ hσI
    have hBram : ¬ SSGRoute.IsRamifiedIn k K B := by
      intro hram
      obtain ⟨A₀, hA₀, hconj⟩ := hS₁ram B hBfin (Or.inl hram)
      exact hBnc A₀ hA₀ hconj
    -- a representative `v ∈ R` of the class of `B`
    obtain ⟨v, hvR, τ, hτ⟩ := hRcov B hBfin
    have hvnotin : v ∉ S₁ := by
      intro hvS
      exact hBnc v hvS ⟨τ, hτ⟩
    have hvram : ¬ SSGRoute.IsRamifiedIn k K v := by
      intro hram
      obtain ⟨A₀, hA₀, hconj₂⟩ := hS₁ram v (hRfin v hvR) (Or.inl hram)
      exact hvnotin (hRdisj A₀ (hS₁R A₀ hA₀) v hvR hconj₂ ▸ hA₀)
    have hvanish : ∀ τ' : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v τ' → b τ' = 0 :=
      hbunr v hvR hvnotin
    have hBvanish : ∀ τ' : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B τ' → b τ' = 0 :=
      (inertiaVanishing_conj p k Ω K M' b hbc hvram hBram (σ := τ) hτ).mp hvanish
    exact hBvanish σ hσI
  have hΛker : ∀ x : ↥Z, Ψ x = 0 → Λ x = 0 := by
    intro x hx
    rw [hΛ x]
    refine hoff (x.1 : F) x.2.1 x.2.2 ?_
    intro v hvR hvS σ hσ
    have hvv : (x.1 : F) ∈ Kv v := by
      have h1 : Ψ x ⟨v, hvR, hvS⟩ = 0 := by rw [hx]; rfl
      rw [show Ψ x ⟨v, hvR, hvS⟩ = (Kv v).mkQ (x.1 : F) from rfl, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    exact (show ∀ τ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v τ → (x.1 : F) τ = 0 from hvv) σ hσ
  -- ## 8. split `-Λ` into local functionals
  have hkerΛ : ∀ x : ↥Z, Ψ x = 0 → (-Λ) x = 0 := by
    intro x hx
    rw [LinearMap.neg_apply, hΛker x hx, neg_zero]
  obtain ⟨ν, hν⟩ := exists_coordinate_splitting (p := p) (ı := ı)
    (Q := fun v : ı => F ⧸ Kv v.1) (X := ↥Z) Ψ hsupp (-Λ) hkerΛ
  let lam : ∀ v : ı, F →ₗ[ZMod p] ZMod p := fun v => (ν v).comp (Kv v.1).mkQ
  have hlam : ∀ (v : ı) (f : F), lam v f = ν v (Submodule.Quotient.mk f) := fun v f => rfl
  -- ## 9. realise the local functionals by unramified local cocycles
  have hres_one : ∀ (v : ValuationSubring Ω), ¬ SSGRoute.IsRamifiedIn k K v →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → SSGRoute.res k K σ = 1 := by
    intro v hv σ hσ
    have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker K
    have hmem : σ ∈ K.fixingSubgroup := by
      by_contra h
      exact hv ⟨σ, hσ, h⟩
    exact MonoidHom.mem_ker.mp (hker ▸ hmem)
  have hex : ∀ v : ı, ∃ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) a ∧
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → a σ = 0) ∧
      ∀ b : F, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) b →
        pair (SSGRoute.decomp k v.1) a b = lam v b := by
    intro v
    have hvram := (hRne v.1 v.2.1 v.2.2).1
    have hvval := (hRne v.1 v.2.1 v.2.2).2
    refine hreal_unr v.1 (hRfin v.1 v.2.1) hvval hvram (lam v) ?_ ?_ ?_
    · intro b b' _ _
      exact map_add (lam v) b b'
    · intro b hb
      obtain ⟨m, hm⟩ := hb
      rw [hlam]
      have hKv : b ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → b σ = 0
        intro σ hσ
        rw [hm σ hσ.1, hres_one v.1 hvram σ hσ, one_smul, sub_self]
      rw [show Submodule.Quotient.mk b = 0 from
        (Submodule.Quotient.mk_eq_zero (Kv v.1)).mpr hKv, map_zero]
    · intro b _ _ hb0
      rw [hlam]
      have hKv : b ∈ Kv v.1 := by
        show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → b σ = 0
        exact fun σ hσ => hb0 σ hσ
      rw [show Submodule.Quotient.mk b = 0 from
        (Submodule.Quotient.mk_eq_zero (Kv v.1)).mpr hKv, map_zero]
  let αnew : ∀ v : ı, (Ω ≃ₐ[k] Ω) → M := fun v => Classical.choose (hex v)
  have hαnew : ∀ v : ı,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) (αnew v) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) (αnew v) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v.1 σ → αnew v σ = 0) ∧
      ∀ b : F, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v.1) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k v.1) b →
        pair (SSGRoute.decomp k v.1) (αnew v) b = lam v b :=
    fun v => Classical.choose_spec (hex v)
  -- ## 10. the global local data `α'`
  let α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M := fun A =>
    if hS : A ∈ S₁ then α A
    else if hR : A ∈ R then αnew ⟨A, hR, hS⟩ else 0
  have hα'S₁ : ∀ A ∈ S₁, α' A = α A := by
    intro A hA
    rw [show α' A = if hS : A ∈ S₁ then α A else if hR : A ∈ R then αnew ⟨A, hR, hS⟩ else 0
      from rfl, dif_pos hA]
  have hα'cl : ∀ v ∈ R, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k v) (α' v) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k v) (α' v) := by
    intro v hvR
    by_cases hvS : v ∈ S₁
    · rw [show α' v = α v from hα'S₁ v hvS]
      exact hα v hvS
    · rw [show α' v = if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0
        from rfl, dif_neg hvS, dif_pos hvR]
      exact ⟨(hαnew ⟨v, hvR, hvS⟩).1, (hαnew ⟨v, hvR, hvS⟩).2.1⟩
  have hα'unr : ∀ v ∈ R, v ∉ S₁ → ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → α' v σ = 0 := by
    intro v hvR hvS σ hσ
    rw [show α' v = if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0
      from rfl, dif_neg hvS, dif_pos hvR]
    exact (hαnew ⟨v, hvR, hvS⟩).2.2.1 σ hσ
  -- ## 11. the sum over `R`, with the `C`-sum, vanishes
  have hsum : ∀ b : (Ω ≃ₐ[k] Ω) → M',
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R), pair (SSGRoute.decomp k v) (α' v) b)
        + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0 := by
    intro b hbc hlc
    let bz : ↥Z := ⟨b, hbc, hlc⟩
    obtain ⟨Sb, hSbfin, hSbdisj, hSbvanish⟩ := vanishingInertia_finite k Ω K M' b hbc hlc
    -- every element of `R` outside `S₁` where the summand does not vanish is conjugate to
    -- an element of the finite set `Sb`; there is at most one place of `R` per class
    have hfin_classes : {v : ValuationSubring Ω | v ∈ R ∧ ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v}.Finite := by
      let g : {v : ValuationSubring Ω // v ∈ R ∧ ∃ A ∈ Sb, SSGRoute.IsConjPlace k A v} → ↥Sb :=
        fun v => ⟨Classical.choose v.2.2, (Classical.choose_spec v.2.2).1⟩
      have hinj : Function.Injective g := by
        intro v w hvw
        have hv : SSGRoute.IsConjPlace k (Classical.choose v.2.2) v.1 :=
          (Classical.choose_spec v.2.2).2
        have hw : SSGRoute.IsConjPlace k (Classical.choose w.2.2) w.1 :=
          (Classical.choose_spec w.2.2).2
        have hab : Classical.choose v.2.2 = Classical.choose w.2.2 := congrArg Subtype.val hvw
        have hconj : SSGRoute.IsConjPlace k v.1 w.1 := by
          obtain ⟨s1, hs1⟩ := hv
          obtain ⟨s2, hs2⟩ := hw
          refine ⟨s2 * s1⁻¹, ?_⟩
          calc (s2 * s1⁻¹) • v.1 = s2 • (s1⁻¹ • v.1) := mul_smul _ _ _
            _ = s2 • (s1⁻¹ • (s1 • Classical.choose v.2.2)) := by rw [hs1]
            _ = s2 • Classical.choose v.2.2 := by rw [inv_smul_smul]
            _ = s2 • Classical.choose w.2.2 := by rw [hab]
            _ = w.1 := hs2
        exact Subtype.ext (hRdisj v.1 v.2.1 w.1 w.2.1 hconj)
      haveI : Finite ↥Sb := Sb.finite_toSet.to_subtype
      exact Finite.of_injective g hinj
    have hfinsupp : (↑R ∩ Function.support
        (fun v : ValuationSubring Ω => pair (SSGRoute.decomp k v) (α' v) b)).Finite := by
      refine Set.Finite.subset ((S₁.finite_toSet).union hfin_classes) ?_
      intro v hv
      obtain ⟨hvR, hvne⟩ := hv
      by_cases hvS : v ∈ S₁
      · exact Or.inl hvS
      · refine Or.inr ⟨hvR, ?_⟩
        by_contra hno
        push_neg at hno
        have hKv : b ∈ Kv v := by
          show ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → b σ = 0
          exact fun σ hσ => hSbvanish v (hRfin v hvR) hno σ hσ
        have hz : (Kv v).mkQ b = 0 := (Submodule.Quotient.mk_eq_zero (Kv v)).mpr hKv
        have hzero : pair (SSGRoute.decomp k v) (α' v) b = 0 := by
          rw [show α' v =
            (if hS : v ∈ S₁ then α v else if hR : v ∈ R then αnew ⟨v, hR, hS⟩ else 0) from rfl,
            dif_neg hvS, dif_pos hvR]
          rw [(hαnew ⟨v, hvR, hvS⟩).2.2.2 b (hmono_coc _ _ hbc) (hmono_loc _ _ hlc)]
          rw [show lam ⟨v, hvR, hvS⟩ b = ν ⟨v, hvR, hvS⟩ ((Kv v).mkQ b) from rfl, hz, map_zero]
        exact hvne hzero
    -- split the sum into the parts over `S₁` and over `R \ S₁`
    have hsets : (↑S₁ : Set (ValuationSubring Ω)) ∪ {v | v ∈ R ∧ v ∉ S₁} = R := by
      ext v
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact hS₁R v h
        · exact h
      · intro h
        by_cases hv : v ∈ S₁
        · exact Or.inl hv
        · exact Or.inr ⟨h, hv⟩
    have hdisj : Disjoint (↑S₁ : Set (ValuationSubring Ω)) {v | v ∈ R ∧ v ∉ S₁} := by
      rw [Set.disjoint_left]
      intro v hv hv'
      exact hv'.2 hv
    have hfinS₁ : ((↑S₁ : Set (ValuationSubring Ω)) ∩ Function.support
        (fun v => pair (SSGRoute.decomp k v) (α' v) b)).Finite :=
      S₁.finite_toSet.subset Set.inter_subset_left
    have hfinI : ({v | v ∈ R ∧ v ∉ S₁} ∩ Function.support
        (fun v => pair (SSGRoute.decomp k v) (α' v) b)).Finite :=
      hfinsupp.subset fun v hv => ⟨hv.1.1, hv.2⟩
    have hsplit : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ R),
          pair (SSGRoute.decomp k v) (α' v) b)
        = (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ (↑S₁ : Set (ValuationSubring Ω))),
              pair (SSGRoute.decomp k v) (α' v) b)
          + ∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ {v | v ∈ R ∧ v ∉ S₁}),
              pair (SSGRoute.decomp k v) (α' v) b := by
      rw [← finsum_mem_congr hsets (fun v _ => rfl)]
      exact finsum_mem_union' hdisj hfinS₁ hfinI
    -- the part over `S₁`, together with the `C`-sum, is `Λ`
    have hS₁part : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ (↑S₁ : Set (ValuationSubring Ω))),
          pair (SSGRoute.decomp k v) (α' v) b)
          + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = Λ bz := by
      rw [finsum_mem_eq_sum (fun v => pair (SSGRoute.decomp k v) (α' v) b) hfinS₁]
      have hsub : hfinS₁.toFinset ⊆ S₁ := fun v hv =>
        (Set.Finite.mem_toFinset hfinS₁).mp hv |>.1
      have hzero : ∀ x ∈ S₁, x ∉ hfinS₁.toFinset →
          pair (SSGRoute.decomp k x) (α' x) b = 0 := by
        intro x hx hxn
        by_contra hne
        exact hxn ((Set.Finite.mem_toFinset hfinS₁).mpr ⟨hx, Function.mem_support.mpr hne⟩)
      rw [Finset.sum_subset hsub hzero]
      rw [hΛ bz]
      exact congrArg (fun z => z + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) (bz : F))
        (Finset.sum_congr rfl fun A hA =>
          congrArg (fun z => pair (SSGRoute.decomp k A) z b) (hα'S₁ A hA))
    -- the part over `R \ S₁` is the sum of the local functionals
    have hIpart : (∑ᶠ (v : ValuationSubring Ω) (_ : v ∈ {v | v ∈ R ∧ v ∉ S₁}),
          pair (SSGRoute.decomp k v) (α' v) b) = ∑ᶠ (v : ı), ν v (Ψ bz v) := by
      rw [← finsum_set_coe_eq_finsum_mem (f := fun v : ValuationSubring Ω =>
        pair (SSGRoute.decomp k v) (α' v) b) {v | v ∈ R ∧ v ∉ S₁}]
      refine finsum_congr fun j => ?_
      have hα'j : α' j.1 = αnew j := by
        rw [show α' j.1 =
          (if hS : j.1 ∈ S₁ then α j.1 else if hR : j.1 ∈ R then αnew ⟨j.1, hR, hS⟩ else 0)
          from rfl, dif_neg j.2.2, dif_pos j.2.1]
      rw [hα'j, (hαnew j).2.2.2 b (hmono_coc _ _ hbc) (hmono_loc _ _ hlc)]
      rfl
    rw [hsplit, add_right_comm, hS₁part, hIpart, hν bz, LinearMap.neg_apply, add_neg_cancel]
  -- ## 12. the prescribed places of `K` are pairwise non-conjugate
  have hRnc : ∀ (v w : ValuationSubring Ω) (hv : v ∈ R) (hw : w ∈ R),
      (∃ σ : ↥K ≃ₐ[k] ↥K,
        σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) =
          NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K w (hRfin w hw))) → v = w := by
    intro v w hv hw hconj
    exact hRdisj v hv w hw (isConjPlace_of_finQ_conj k Ω K v w (hRfin v hv) (hRfin w hw) hconj)
  -- ## 13. the transversal `RK` of ALL places of `K`
  haveI : Finite T := by
    haveI : Module.Free (ZMod p) T := inferInstance
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
      rw [hT.1, Module.finrank_self]
    exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
      (LinearEquiv.injective _)
  haveI : Finite M' := Work.SSGRoute.PT.finite_dualMod_tensor p M T
  let qof : R → NK.GlobalCFT.Place ↥K := fun v =>
    NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2))
  obtain ⟨RK, hRKq, hRKw, hRKtrans⟩ :=
    exists_transversal_places_wc k Ω K R hRfin hRdisj wc φc hseam C hCinv hC1 hCdisj
  let Tpl : NK.GlobalCFT.Place ↥K → Type := fun q =>
    CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) q).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M'))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) q) 1
  let qK : R → ↥RK := fun v => ⟨qof v, hRKq v.1 v.2⟩
  let cK : ↥C → ↥RK := fun c => ⟨wc c.1, hRKw c.1 c.2⟩
  -- two `C`-involutions linked to the same place are equal
  have hwcinj : ∀ c ∈ C, ∀ c' ∈ C, wc c = wc c' → c = c' := by
    intro c hcC c' hc'C hcc'
    have hseamc := hseam c (hCinv c hcC) (hC1 c hcC)
    have hseamc' := hseam c' (hCinv c' hc'C) (hC1 c' hc'C)
    have hσ : (1 : ↥K ≃ₐ[k] ↥K) •
        NK.GlobalCFT.Place.ofInfinite
          (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))) =
        NK.GlobalCFT.Place.ofInfinite
          (NumberField.InfinitePlace.mk ((φc c').comp (algebraMap (↥K) Ω))) := by
      rw [one_smul, ← hseamc.2, hcc', hseamc'.2]
    obtain ⟨τ, hτ⟩ := wc_orbit_injective k Ω K c c' (hCinv c hcC) (hC1 c hcC)
      (hCinv c' hc'C) (hC1 c' hc'C) (φc c) (φc c') hseamc.1 hseamc'.1 1 hσ
    exact hCdisj c hcC c' hc'C ⟨τ, hτ⟩
  -- a `wc c` is never equal to a finite place of `R`
  have hfin_ne : ∀ c ∈ C, ∀ v : R, wc c ≠ qof v := by
    intro c hcC v hcv
    have hinf : (wc c).IsFinite := by
      rw [hcv]; exact NK.GlobalCFT.Place.isFinite_ofFinite _
    obtain ⟨q, hq⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hinf
    exact (hwc c (hCinv c hcC) (hC1 c hcC)).1 q hq
  -- the family of local `Ext` groups and the chosen family `a`
  have ha_ex : ∀ w : ↥RK, ∃ y : Tpl w.1,
      ((∃ v : R, qof v = w.1) → ∀ (v : R) (hv : qof v = w.1),
        y = Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1))) ∧
      ((∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w.1) →
        ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ C) (hw : wc c = w.1),
          y = Eq.mp (congrArg Tpl hw) (βc c (β c))) ∧
      ((¬ ∃ v : R, qof v = w.1) →
        (¬ ∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w.1) → y = 0) := by
    intro w
    by_cases h1 : ∃ v : R, qof v = w.1
    · obtain ⟨v, hv⟩ := h1
      refine ⟨Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1)), ?_, ?_, ?_⟩
      · intro _ v' hv'
        have hvv : v' = v := Subtype.ext (hRnc v'.1 v.1 v'.2 v.2 ⟨1, by
          rw [one_smul]
          exact hv'.trans hv.symm⟩)
        subst hvv
        rw [show hv' = hv from Subsingleton.elim _ _]
      · intro _ c hc hw
        exact (hfin_ne c hc v (hw.trans hv.symm)).elim
      · intro h2' _
        exact (h2' ⟨v, hv⟩).elim
    · by_cases h2 : ∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w.1
      · obtain ⟨c, hcC, hcw⟩ := h2
        refine ⟨Eq.mp (congrArg Tpl hcw) (βc c (β c)), ?_, ?_, ?_⟩
        · intro h1'; exact (h1 h1').elim
        · intro _ c' hc' hw'
          have hcc' : c' = c := hwcinj c' hc' c hcC (hw'.trans hcw.symm)
          subst hcc'
          rw [show hw' = hcw from Subsingleton.elim _ _]
        · intro _ h3'
          exact (h3' ⟨c, hcC, hcw⟩).elim
      · refine ⟨0, ?_, ?_, ?_⟩
        · intro h1'; exact (h1 h1').elim
        · intro h2' _ _ _; exact (h2 h2').elim
        · intro _ _; rfl
  let a : ∀ w : ↥RK, Tpl w.1 := fun w => Classical.choose (ha_ex w)
  have ha_v : ∀ (w : ↥RK) (v : R) (hv : qof v = w.1),
      a w = Eq.mp (congrArg Tpl hv) (βl v.1 (hRfin v.1 v.2) (α' v.1)) :=
    fun w v hv => (Classical.choose_spec (ha_ex w)).1 ⟨v, hv⟩ v hv
  have ha_c : ∀ (w : ↥RK) (c : Ω ≃ₐ[k] Ω) (hc : c ∈ C) (hw : wc c = w.1),
      a w = Eq.mp (congrArg Tpl hw) (βc c (β c)) :=
    fun w c hc hw => (Classical.choose_spec (ha_ex w)).2.1 ⟨c, hc, hw⟩ c hc hw
  have ha_zero : ∀ (w : ↥RK), (¬ ∃ v : R, qof v = w.1) →
      (¬ ∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w.1) → a w = 0 :=
    fun w h1 h2 => (Classical.choose_spec (ha_ex w)).2.2 h1 h2
  have ha_q : ∀ v : R, a (qK v) = βl v.1 (hRfin v.1 v.2) (α' v.1) := by
    intro v
    have hv : qof v = (qK v).1 := rfl
    rw [ha_v (qK v) v hv]
    exact eq_mp_congrArg_self (T := Tpl) hv _
  have ha_wc : ∀ c : ↥C, a (cK c) = βc c.1 (β c.1) := by
    intro c
    have hw : wc c.1 = (cK c).1 := rfl
    rw [ha_c (cK c) c.1 c.2 hw]
    exact eq_mp_congrArg_self (T := Tpl) hw _
  -- ## 14. the family `a` is unramified at all but finitely many places
  haveI : Finite ↥S₁ := S₁.finite_toSet.to_subtype
  haveI : Finite ↥C := C.finite_toSet.to_subtype
  have hbad : {w : ↥RK | ¬ SSGRoute.PTExt.IsUnramifiedExt w.1 (a w)}.Finite := by
    refine Set.Finite.subset
      ((Set.finite_range (fun v : ↥S₁ => qK ⟨v.1, hS₁R v.1 v.2⟩)).union
        (Set.finite_range (fun c : ↥C => cK c))) ?_
    intro w hw
    by_cases h1 : ∃ v : R, qof v = w.1
    · obtain ⟨v, hv⟩ := h1
      have hwv : w = qK v := Subtype.ext hv.symm
      by_cases hvS : v.1 ∈ S₁
      · exact Or.inl ⟨⟨v.1, hvS⟩, (congrArg qK (Subtype.ext rfl)).trans hwv.symm⟩
      · exfalso
        have hw' : ¬ SSGRoute.PTExt.IsUnramifiedExt w.1 (a w) := hw
        rw [hwv, ha_q v] at hw'
        exact hw' (hβl_unr v.1 (hRfin v.1 v.2) (hRne v.1 v.2 hvS).2 (hRne v.1 v.2 hvS).1
          (α' v.1) (hα'cl v.1 v.2).1 (hα'cl v.1 v.2).2 (hα'unr v.1 v.2 hvS))
    · by_cases h2 : ∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w.1
      · obtain ⟨c, hcC, hcw⟩ := h2
        exact Or.inr ⟨⟨c, hcC⟩, (Subtype.ext hcw.symm : w = cK ⟨c, hcC⟩).symm⟩
      · exfalso
        refine hw ?_
        rw [ha_zero w h1 h2]
        exact ⟨0, by rw [CategoryTheory.Abelian.Ext.zero_comp]⟩
  -- ## 15. the glued class `X`
  haveI : Finite ↥(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M') := inferInstanceAs (Finite M')
  obtain ⟨X, hX⟩ := (Work.SSGRoute.ext_idele_shapiro (k := k) (K := ↥K)
    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) M') 1 RK hRKtrans).2.2 a hbad
  refine ⟨R, hRfin, hS₁R, hRdisj, hRcov, α', hα'S₁, hα'cl, hα'unr, hsum, X, ?_, ?_, ?_⟩
  · -- the components at the places of `R`
    intro v hv
    have h1 : SSGRoute.PTExt.extLoc (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv))) X =
        a (qK ⟨v, hv⟩) := hX (qK ⟨v, hv⟩)
    rw [h1, ha_q ⟨v, hv⟩]
  · -- the components at the linked infinite places
    intro c hcC
    have h1 : SSGRoute.PTExt.extLoc (k := k) (wc c) X = a (cK ⟨c, hcC⟩) := hX (cK ⟨c, hcC⟩)
    rw [h1, ha_wc ⟨c, hcC⟩]
  · -- the Shapiro vanishing off the chosen orbits
    intro w hw hw'
    obtain ⟨w', hspec, -⟩ := hRKtrans w
    obtain ⟨σ, hσ⟩ := hspec
    have hw_eq : w = σ⁻¹ • w'.1 := by rw [← hσ, inv_smul_smul]
    have hw'not1 : ¬ ∃ v : R, qof v = w'.1 := by
      rintro ⟨v, hv⟩
      rw [← hv] at hw_eq
      exact hw v v.2 σ⁻¹ hw_eq.symm
    have hw'not2 : ¬ ∃ c : Ω ≃ₐ[k] Ω, c ∈ C ∧ wc c = w'.1 := by
      rintro ⟨c, hcC, hc⟩
      rw [← hc] at hw_eq
      exact hw' c hcC σ⁻¹ hw_eq.symm
    have hzero : SSGRoute.PTExt.extLoc (k := k) w'.1 X = 0 := by
      rw [hX w', ha_zero w' hw'not1 hw'not2]
    rw [hw_eq]
    exact Work.SSGRoute.e9c_extLoc_conj_zero X σ⁻¹ w'.1 hzero

end Work.SSGRoute.PT
