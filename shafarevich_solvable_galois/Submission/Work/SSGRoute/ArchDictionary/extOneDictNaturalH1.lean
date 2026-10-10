import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Module.Injective
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.dictNaturalDefs
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNatAux
import Submission.Work.SSGRoute.augSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The divisible-coefficient dictionary `Ext¹_G(M,N) ≃+ H¹(G, Hom_ℤ(M,N))`, natural in `M`

This file proves `Work.SSGRoute.ArchDictionary.extOneDictNaturalH1`: for a group `G` and a
`G`-module `N` whose underlying abelian group is divisible, the dictionary

  `e M : Ext¹_G(M,N) ≃+ H¹(G, Hom_ℤ(M,N))`

(where `Hom_ℤ(M,N)` carries the conjugation action, `Work.SSGRoute.homH1`) can be chosen to be a
*single* family of additive equivalences natural in the contravariant variable `M`.

The comparison is assembled from four natural factors, each a *canonical* map (no
`Classical.choice` in the maps themselves):

* `e1 M : Ext¹(M,N) ≃+ Q1 M`, the contravariant cokernel description attached to the canonical
  free presentation `0 → R → F → M → 0` of `M` (`CokerNat.cokerIso`);
* `cmp M : Q1 M ≃+ Q2 M`, the comparison of the two cokernels through the degree-`0` naturality
  `unitHomExtEquiv_symm_precomp` of the `Ext⁰(ℤ, Hom_ℤ(-,N)) ≃ Ext⁰(-,N)` dictionary;
* `e2 M : Ext¹(unitRep G, Hom_ℤ(M,N)) ≃+ Q2 M`, the covariant cokernel description attached to
  the dual presentation `0 → Hom_ℤ(M,N) → Hom_ℤ(F,N) → Hom_ℤ(R,N) → 0` (short exact because `N`
  is divisible, `homRepShortComplex_shortExact`; the `Ext¹` of the middle term vanishes by
  `ext_one_homRepFree_subsingleton`);
* `(gammaIso M)⁻¹ : Ext¹(unitRep G, Hom_ℤ(M,N)) ≃+ H¹(G, Hom_ℤ(M,N))`, the degree-`1` bridge
  `gammaHom` (`ExtH1Iso.lean`), whose naturality is `gammaHom_natural_coeff`.

Naturality of each factor is `CokerNat.cokerIso_natural`, `unitHomExtEquiv_symm_precomp`,
`CokerNat.cokerIsoCov_natural` and `gammaHom_natural_coeff` respectively; the assembly is then a
four-step rewrite.
-/

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

namespace Work.SSGRoute.ArchDictionary

namespace NatH1

noncomputable section

variable {G : Type} [Group G]

/-! ## The canonical presentation of `M` and the two cokernels -/

/-- The canonical (choice-free) two-term free presentation `0 → R M → F M → M → 0`. -/
abbrev pres (M : Rep.{0} Coeff G) : ShortComplex (Rep.{0} Coeff G) := SSGRoute.ses M

/-- The dual presentation `0 → Hom_ℤ(M,N) → Hom_ℤ(F M,N) → Hom_ℤ(R M,N) → 0`, written out
explicitly so that its `Xᵢ` are definitionally the internal `Hom`s. -/
abbrev dpres (N M : Rep.{0} Coeff G) : ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (homRepPre (pres M).X₃ (pres M).X₂ N (pres M).g)
    (homRepPre (pres M).X₂ (pres M).X₁ N (pres M).f)
    (by
      rw [homRepPre_comp (pres M).X₃ (pres M).X₂ (pres M).X₁ N (pres M).g (pres M).f,
        (pres M).zero, homRepPre_zero])

/-- The dual presentation is short exact when `N` is divisible. -/
theorem dpres_shortExact (N : Rep.{0} Coeff G) (hInj : Module.Injective Coeff N.V)
    (M : Rep.{0} Coeff G) : (dpres N M).ShortExact :=
  homRepShortComplex_shortExact G (pres M) (SSGRoute.ses_shortExact M) N hInj

/-- The cokernel `Hom_G(R M,N) / im(Hom_G(F M,N) → Hom_G(R M,N))`, the model of `Ext¹(M,N)`. -/
abbrev Q1 (N M : Rep.{0} Coeff G) : Type :=
  Abelian.Ext (pres M).X₁ N 0 ⧸ (CokerNat.preMap (pres M) N).range

/-- The cokernel `Ext⁰(ℤ,Hom_ℤ(R M,N)) / im(Ext⁰(ℤ,Hom_ℤ(F M,N)) → …)`, the model of
`Ext¹(ℤ,Hom_ℤ(M,N))`. -/
abbrev Q2 (N M : Rep.{0} Coeff G) : Type :=
  Abelian.Ext (unitRep G) (dpres N M).X₃ 0 ⧸
    (CokerNat.postMap (dpres N M) (unitRep G)).range

/-- **The contravariant cokernel description** `Ext¹(M,N) ≃+ Q1 M`. -/
noncomputable def e1 (N M : Rep.{0} Coeff G) : Abelian.Ext M N 1 ≃+ Q1 N M :=
  CokerNat.cokerIso (SSGRoute.ses_shortExact M) N

/-- The comparison `Q1 M →+ Q1 M'` induced by `u : M' ⟶ M`. -/
noncomputable def ind1 (N : Rep.{0} Coeff G) {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) :
    Q1 N M →+ Q1 N M' :=
  QuotientAddGroup.map (CokerNat.preMap (pres M) N).range (CokerNat.preMap (pres M') N).range
    ((Abelian.Ext.mk₀ (SSGRoute.sesMap u).τ₁).precomp N (zero_add 0))
    (CokerNat.preMap_range_le (SSGRoute.sesMap u) N)

/-- Computation rule for `ind1`. -/
lemma ind1_mk (N : Rep.{0} Coeff G) {M' M : Rep.{0} Coeff G} (u : M' ⟶ M)
    (a : Abelian.Ext (pres M).X₁ N 0) :
    ind1 N u (↑a : Q1 N M)
      = (↑((Abelian.Ext.mk₀ (SSGRoute.sesMap u).τ₁).precomp N (zero_add 0) a) : Q1 N M') :=
  QuotientAddGroup.map_mk' _ _ _ _ _

/-- **Naturality of the contravariant cokernel description.** -/
theorem e1_natural (N : Rep.{0} Coeff G) {M' M : Rep.{0} Coeff G} (u : M' ⟶ M)
    (x : Abelian.Ext M N 1) :
    e1 N M' ((Abelian.Ext.mk₀ u).comp x (zero_add 1)) = ind1 N u (e1 N M x) := by
  have h := CokerNat.cokerIso_natural (SSGRoute.ses_shortExact M') (SSGRoute.ses_shortExact M)
    (SSGRoute.sesMap u) N x
  rw [show (Abelian.Ext.mk₀ (SSGRoute.sesMap u).τ₃).precomp N (zero_add 1) x
      = (Abelian.Ext.mk₀ u).comp x (zero_add 1) from rfl] at h
  show CokerNat.cokerIso (SSGRoute.ses_shortExact M') N
        ((Abelian.Ext.mk₀ u).comp x (zero_add 1))
      = QuotientAddGroup.map (CokerNat.preMap (pres M) N).range (CokerNat.preMap (pres M') N).range
          ((Abelian.Ext.mk₀ (SSGRoute.sesMap u).τ₁).precomp N (zero_add 0))
          (CokerNat.preMap_range_le (SSGRoute.sesMap u) N)
          (CokerNat.cokerIso (SSGRoute.ses_shortExact M) N x)
  exact h

/-! ## The morphism of dual presentations -/

variable (N : Rep.{0} Coeff G)

/-- First commutation square of the comparison of the dual presentations. -/
lemma dualSESMap_comm₁₂ {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) :
    homRepPre M M' N u ≫ homRepPre M' (Rep.free Coeff G M'.V) N (freeCover M')
      = homRepPre M (Rep.free Coeff G M.V) N (freeCover M) ≫
          homRepPre (Rep.free Coeff G M.V) (Rep.free Coeff G M'.V) N (freeMap u) := by
  rw [homRepPre_comp, homRepPre_comp, SSGRoute.freeMap_freeCover_gen]

/-- Second commutation square of the comparison of the dual presentations. -/
lemma dualSESMap_comm₂₃ {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) :
    homRepPre (Rep.free Coeff G M.V) (Rep.free Coeff G M'.V) N (freeMap u) ≫
        homRepPre (Rep.free Coeff G M'.V) (Limits.kernel (freeCover M')) N
          (Limits.kernel.ι (freeCover M'))
      = homRepPre (Rep.free Coeff G M.V) (Limits.kernel (freeCover M)) N
            (Limits.kernel.ι (freeCover M)) ≫
          homRepPre (Limits.kernel (freeCover M)) (Limits.kernel (freeCover M')) N
            (SSGRoute.freeMapKernelGen u) := by
  rw [homRepPre_comp, homRepPre_comp, SSGRoute.freeMapKernelGen_ι]

/-- The morphism of dual presentations induced by `u : M' ⟶ M`. -/
noncomputable def dualSESMap {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) :
    dpres N M ⟶ dpres N M' :=
  ShortComplex.Hom.mk (homRepPre M M' N u)
    (homRepPre (Rep.free Coeff G M.V) (Rep.free Coeff G M'.V) N (freeMap u))
    (homRepPre (Limits.kernel (freeCover M)) (Limits.kernel (freeCover M'))
      N (SSGRoute.freeMapKernelGen u))
    (dualSESMap_comm₁₂ N u) (dualSESMap_comm₂₃ N u)

/-- **The covariant cokernel description** `Ext¹(ℤ, Hom_ℤ(M,N)) ≃+ Q2 M`. -/
noncomputable def e2 (hInj : Module.Injective Coeff N.V) (M : Rep.{0} Coeff G)
    [Subsingleton (Abelian.Ext (unitRep G) (dpres N M).X₂ 1)] :
    Abelian.Ext (unitRep G) (dpres N M).X₁ 1 ≃+ Q2 N M :=
  CokerNat.cokerIsoCov (dpres_shortExact N hInj M) (unitRep G)

/-- The comparison `Q2 M →+ Q2 M'` induced by `u : M' ⟶ M`. -/
noncomputable def ind2 {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) : Q2 N M →+ Q2 N M' :=
  QuotientAddGroup.map (CokerNat.postMap (dpres N M) (unitRep G)).range
    (CokerNat.postMap (dpres N M') (unitRep G)).range
    ((Abelian.Ext.mk₀ (homRepPre (pres M).X₁ (pres M').X₁ N
        (SSGRoute.freeMapKernelGen u))).postcomp (unitRep G) (zero_add 0))
    (CokerNat.postMap_range_le (dualSESMap N u) (unitRep G))

/-- Computation rule for `ind2`. -/
lemma ind2_mk {M' M : Rep.{0} Coeff G} (u : M' ⟶ M)
    (a : Abelian.Ext (unitRep G) (dpres N M).X₃ 0) :
    ind2 N u (↑a : Q2 N M)
      = (↑((Abelian.Ext.mk₀ (homRepPre (pres M).X₁ (pres M').X₁ N
          (SSGRoute.freeMapKernelGen u))).postcomp (unitRep G) (zero_add 0) a) : Q2 N M') :=
  QuotientAddGroup.map_mk' _ _ _ _ _

/-- **Naturality of the covariant cokernel description.** -/
theorem e2_symm_natural (hInj : Module.Injective Coeff N.V) {M' M : Rep.{0} Coeff G}
    (u : M' ⟶ M) [Subsingleton (Abelian.Ext (unitRep G) (dpres N M).X₂ 1)]
    [Subsingleton (Abelian.Ext (unitRep G) (dpres N M').X₂ 1)] (q : Q2 N M) :
    (e2 N hInj M').symm (ind2 N u q)
      = (Abelian.Ext.mk₀ (homRepPre M M' N u)).postcomp (unitRep G) (add_zero 1)
          ((e2 N hInj M).symm q) := by
  refine QuotientAddGroup.induction_on q fun a => ?_
  rw [ind2_mk]
  rw [show (e2 N hInj M').symm
        (↑((Abelian.Ext.mk₀ (homRepPre (pres M).X₁ (pres M').X₁ N
            (SSGRoute.freeMapKernelGen u))).postcomp (unitRep G) (zero_add 0) a) : Q2 N M')
      = CokerNat.connMapCov (dpres_shortExact N hInj M') (unitRep G)
          ((Abelian.Ext.mk₀ (homRepPre (pres M).X₁ (pres M').X₁ N
            (SSGRoute.freeMapKernelGen u))).postcomp (unitRep G) (zero_add 0) a) from
      CokerNat.cokerIsoCov_symm_mk (dpres_shortExact N hInj M') (unitRep G) _]
  rw [show (e2 N hInj M).symm (↑a : Q2 N M)
      = CokerNat.connMapCov (dpres_shortExact N hInj M) (unitRep G) a from
      CokerNat.cokerIsoCov_symm_mk (dpres_shortExact N hInj M) (unitRep G) a]
  exact (CokerNat.connMapCov_postcomp_natural (dpres_shortExact N hInj M)
    (dpres_shortExact N hInj M') (dualSESMap N u) (unitRep G) a).symm

/-! ## The comparison of the two cokernels -/

/-- The degree-`0` dictionary `Ext⁰(R M,N) ≃+ Ext⁰(ℤ, Hom_ℤ(R M,N))`. -/
noncomputable def cEq (M : Rep.{0} Coeff G) :
    Abelian.Ext (pres M).X₁ N 0 ≃+ Abelian.Ext (unitRep G) (dpres N M).X₃ 0 :=
  (unitHomExtEquiv (pres M).X₁ N).symm

/-- The degree-`0` dictionary on the middle terms, `Ext⁰(F M,N) ≃+ Ext⁰(ℤ, Hom_ℤ(F M,N))`. -/
noncomputable def cEq₂ (M : Rep.{0} Coeff G) :
    Abelian.Ext (pres M).X₂ N 0 ≃+ Abelian.Ext (unitRep G) (dpres N M).X₂ 0 :=
  (unitHomExtEquiv (pres M).X₂ N).symm

/-- The comparison of the two cokernels, on `AddMonoidHom`s. -/
noncomputable def cHom (M : Rep.{0} Coeff G) : Q1 N M →+ Q2 N M :=
  QuotientAddGroup.lift (CokerNat.preMap (pres M) N).range
    ((QuotientAddGroup.mk' (CokerNat.postMap (dpres N M) (unitRep G)).range).comp
      (cEq N M).toAddMonoidHom)
    (by
      intro a ha
      rw [AddMonoidHom.mem_ker]
      show (QuotientAddGroup.mk' (CokerNat.postMap (dpres N M) (unitRep G)).range)
          (cEq N M a) = 0
      refine (QuotientAddGroup.eq_zero_iff (cEq N M a)).mpr ?_
      obtain ⟨b, rfl⟩ := ha
      refine ⟨(cEq₂ N M) b, ?_⟩
      show CokerNat.postMap (dpres N M) (unitRep G) ((cEq₂ N M) b)
          = cEq N M ((CokerNat.preMap (pres M) N) b)
      rw [CokerNat.postMap_apply, CokerNat.preMap_apply]
      simp only [cEq, cEq₂]
      exact (unitHomExtEquiv_symm_precomp (pres M).X₂ (pres M).X₁ N (pres M).f b).symm)

/-- Computation rule for `cHom`. -/
lemma cHom_mk (M : Rep.{0} Coeff G) (a : Abelian.Ext (pres M).X₁ N 0) :
    cHom N M (↑a : Q1 N M) = (↑(cEq N M a) : Q2 N M) :=
  QuotientAddGroup.lift_mk' _ _ _

/-- Computation rule for `cHom`, in the `QuotientAddGroup.mk'` normalisation. -/
lemma cHom_mk' (M : Rep.{0} Coeff G) (a : Abelian.Ext (pres M).X₁ N 0) :
    cHom N M (QuotientAddGroup.mk' (CokerNat.preMap (pres M) N).range a)
      = QuotientAddGroup.mk' (CokerNat.postMap (dpres N M) (unitRep G)).range (cEq N M a) :=
  QuotientAddGroup.lift_mk' _ _ _

/-- The comparison of the two ranges: `cEq` carries the first cokernel onto the second. -/
lemma cHom_map_range (M : Rep.{0} Coeff G) :
    AddSubgroup.map (cEq N M).toAddMonoidHom (CokerNat.preMap (pres M) N).range
      = (CokerNat.postMap (dpres N M) (unitRep G)).range := by
  apply le_antisymm
  · intro y hy
    rw [AddSubgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := ha
    refine ⟨(cEq₂ N M) b, ?_⟩
    show CokerNat.postMap (dpres N M) (unitRep G) ((cEq₂ N M) b)
        = cEq N M ((CokerNat.preMap (pres M) N) b)
    rw [CokerNat.postMap_apply, CokerNat.preMap_apply]
    simp only [cEq, cEq₂]
    exact (unitHomExtEquiv_symm_precomp (pres M).X₂ (pres M).X₁ N (pres M).f b).symm
  · intro y hy
    rw [AddSubgroup.mem_map]
    obtain ⟨w, rfl⟩ := hy
    refine ⟨(CokerNat.preMap (pres M) N) ((unitHomExtEquiv (pres M).X₂ N) w), ⟨_, rfl⟩, ?_⟩
    have h := unitHomExtEquiv_symm_precomp (pres M).X₂ (pres M).X₁ N (pres M).f
      ((unitHomExtEquiv (pres M).X₂ N) w)
    rw [AddEquiv.symm_apply_apply] at h
    show cEq N M ((CokerNat.preMap (pres M) N) ((unitHomExtEquiv (pres M).X₂ N) w))
        = CokerNat.postMap (dpres N M) (unitRep G) w
    rw [CokerNat.postMap_apply, CokerNat.preMap_apply]
    simp only [cEq]
    exact h

/-- `cHom` is bijective. -/
theorem cHom_bijective (M : Rep.{0} Coeff G) : Function.Bijective (cHom N M) := by
  have hmap := cHom_map_range N M
  constructor
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (CokerNat.preMap (pres M) N).range x
    rw [AddMonoidHom.mem_ker, cHom_mk' N M a] at hx
    have hmem : cEq N M a ∈ (CokerNat.postMap (dpres N M) (unitRep G)).range :=
      (QuotientAddGroup.eq_zero_iff (cEq N M a)).mp hx
    have hmem' : cEq N M a ∈ AddSubgroup.map (cEq N M).toAddMonoidHom
        (CokerNat.preMap (pres M) N).range := by rw [hmap]; exact hmem
    rw [AddSubgroup.mem_map] at hmem'
    obtain ⟨a', ha', heq⟩ := hmem'
    rw [show a' = a from (cEq N M).injective heq] at ha'
    exact (QuotientAddGroup.eq_zero_iff a).mpr ha'
  · intro y
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective
      (CokerNat.postMap (dpres N M) (unitRep G)).range y
    refine ⟨(↑((cEq N M).symm b) : Q1 N M), ?_⟩
    rw [cHom_mk,
      show cEq N M ((cEq N M).symm b) = b from AddEquiv.apply_symm_apply (cEq N M) b]
    exact (QuotientAddGroup.mk'_apply _ b).symm

/-- **The comparison of the two cokernel models of `Ext¹`.** -/
noncomputable def cmp (M : Rep.{0} Coeff G) : Q1 N M ≃+ Q2 N M :=
  AddEquiv.ofBijective (cHom N M) (cHom_bijective N M)

/-- **Naturality of the comparison.** -/
theorem cmp_natural {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) (q : Q1 N M) :
    cmp N M' (ind1 N u q) = ind2 N u (cmp N M q) := by
  refine QuotientAddGroup.induction_on q fun a => ?_
  rw [ind1_mk,
    show cmp N M (↑a : Q1 N M) = (↑(cEq N M a) : Q2 N M) from cHom_mk N M a]
  rw [ind2_mk]
  show cHom N M'
      (↑((Abelian.Ext.mk₀ (SSGRoute.sesMap u).τ₁).precomp N (zero_add 0) a) : Q1 N M')
      = (↑((Abelian.Ext.mk₀ (homRepPre (pres M).X₁ (pres M').X₁ N
          (SSGRoute.freeMapKernelGen u))).postcomp (unitRep G) (zero_add 0) (cEq N M a)) : Q2 N M')
  rw [cHom_mk]
  congr 1
  simp only [cEq]
  exact unitHomExtEquiv_symm_precomp (pres M).X₁ (pres M').X₁ N
    (SSGRoute.freeMapKernelGen u) a

/-! ## The degree-one bridge `H¹(G, Hom_ℤ(M,N)) ≃+ Ext¹(ℤ, Hom_ℤ(M,N))` -/

/-- The degree-one bridge. -/
noncomputable def gammaIso (M : Rep.{0} Coeff G) :
    homH1 G M N ≃+ Abelian.Ext (unitRep G) (homRep M N) 1 :=
  AddEquiv.ofBijective
    (SSGRoute.ExtH1.gammaHom G (M.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G))
    ⟨SSGRoute.ExtH1.gammaHom_injective G (M.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G),
      SSGRoute.ExtH1.gammaHom_surjective G (M.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G)⟩

/-- Coefficient naturality of the bridge, in the direction needed here. -/
lemma gammaHom_nu4 {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) (y : homH1 G M N) :
    SSGRoute.ExtH1.gammaHom G (M'.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G)
        (homMapH1 G M M' N u y)
      = (Abelian.Ext.mk₀ (homRepPre M M' N u)).postcomp (unitRep G) (add_zero 1)
          (SSGRoute.ExtH1.gammaHom G (M.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G) y) :=
  SSGRoute.gammaHom_natural_coeff G (M.V →ₗ[Coeff] N.V) (M'.V →ₗ[Coeff] N.V)
    (SSGRoute.augSES_shortExact G) (homRepPre M M' N u).hom.toAddMonoidHom
    (homRepPre_isEquivariant M M' N u) (homRepPre M M' N u) (fun _ => rfl) y

/-- **Naturality of the bridge.** -/
theorem gammaIso_symm_natural {M' M : Rep.{0} Coeff G} (u : M' ⟶ M)
    (z : Abelian.Ext (unitRep G) (homRep M N) 1) :
    (gammaIso N M').symm ((Abelian.Ext.mk₀ (homRepPre M M' N u)).postcomp (unitRep G)
        (add_zero 1) z)
      = homMapH1 G M M' N u ((gammaIso N M).symm z) := by
  refine SSGRoute.ExtH1.gammaHom_injective G (M'.V →ₗ[Coeff] N.V)
    (SSGRoute.augSES_shortExact G) ?_
  rw [show SSGRoute.ExtH1.gammaHom G (M'.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G)
        ((gammaIso N M').symm ((Abelian.Ext.mk₀ (homRepPre M M' N u)).postcomp (unitRep G)
          (add_zero 1) z))
      = (Abelian.Ext.mk₀ (homRepPre M M' N u)).postcomp (unitRep G) (add_zero 1) z from
    AddEquiv.apply_symm_apply (gammaIso N M') _]
  rw [gammaHom_nu4 N u ((gammaIso N M).symm z)]
  rw [show SSGRoute.ExtH1.gammaHom G (M.V →ₗ[Coeff] N.V) (SSGRoute.augSES_shortExact G)
        ((gammaIso N M).symm z) = z from AddEquiv.apply_symm_apply (gammaIso N M) z]

/-! ## The natural family -/

/-- The dictionary `Ext¹(M,N) ≃+ H¹(G, Hom_ℤ(M,N))`, assembled from the four natural factors. -/
noncomputable def eOf (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    (M : Rep.{0} Coeff G) : Abelian.Ext M N 1 ≃+ homH1 G M N :=
  haveI : Subsingleton (Abelian.Ext (unitRep G) (dpres N M).X₂ 1) :=
    ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
  (e1 N M).trans ((cmp N M).trans ((e2 N hInj M).symm.trans (gammaIso N M).symm))

/-- **Naturality of the assembled dictionary.** -/
theorem eOf_natural (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) (x : Abelian.Ext M N 1) :
    eOf N hInj X hX M' ((Abelian.Ext.mk₀ u).comp x (zero_add 1))
      = homMapH1 G M M' N u (eOf N hInj X hX M x) := by
  haveI : Subsingleton (Abelian.Ext (unitRep G) (dpres N M).X₂ 1) :=
    ext_one_homRepFree_subsingleton G M.V N (X M) (hX M)
  haveI : Subsingleton (Abelian.Ext (unitRep G) (dpres N M').X₂ 1) :=
    ext_one_homRepFree_subsingleton G M'.V N (X M') (hX M')
  show (gammaIso N M').symm ((e2 N hInj M').symm (cmp N M'
        (e1 N M' ((Abelian.Ext.mk₀ u).comp x (zero_add 1)))))
      = homMapH1 G M M' N u ((gammaIso N M).symm ((e2 N hInj M).symm (cmp N M (e1 N M x))))
  rw [e1_natural, cmp_natural, e2_symm_natural, gammaIso_symm_natural]

end

end NatH1

theorem extOneDictNaturalH1 (G : Type) [Group G] (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hdiv : ∀ (n : ℕ), 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y) :
    ∃ e : ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff G),
        CategoryTheory.Abelian.Ext M N 1 ≃+ Work.SSGRoute.homH1 G M N,
      ∀ (M' M : Rep.{0} SSGRoute.PTExt.Coeff G) (u : M' ⟶ M)
        (x : CategoryTheory.Abelian.Ext M N 1),
        e M' ((CategoryTheory.Abelian.Ext.mk₀ u).comp x (zero_add 1))
          = Work.SSGRoute.homMapH1 G M M' N u (e M x) := by
  classical
  have hInj : Module.Injective SSGRoute.PTExt.Coeff N.V :=
    moduleInjective_coeff_of_divisible N.V hdiv
  let X : ∀ M : Rep.{0} SSGRoute.PTExt.Coeff G, Rep.{0} SSGRoute.PTExt.Coeff (⊥ : Subgroup G) :=
    fun M => Classical.choose (homRepFree_coind_iso G M.V N)
  let hX : ∀ M, Nonempty (homRep (Rep.free SSGRoute.PTExt.Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)) :=
    fun M => Classical.choose_spec (homRepFree_coind_iso G M.V N)
  exact ⟨fun M => NatH1.eOf N hInj X hX M, fun M' M u x => NatH1.eOf_natural N hInj X hX u x⟩

end Work.SSGRoute.ArchDictionary
