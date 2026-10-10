import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.rightDetect_sylowLevelStabIncl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## `local_duality_ext_detect_h`: the "right radical = 0" clause of E7b

The target of this file is the statement that, at a level `L ⊇ K`, a place `w' ∣ w` and a place
`w'` whose decomposition group `D_{w'}` has order divisible by `p`, every *nonzero* class
`h ∈ H¹(D_{w'}, M)` is detected by the Yoneda pairing against the classes living at the *fixed*
level `K`, i.e. against `Ext¹_{D_w}(M, K_wˣ)`.

This is the degree-`1`, `H¹`-slot companion of the on-disk `Work.SSGRoute.local_duality_ext` (E7b).

### What is proved here

`levelPair_coeff_naturality`: the level pairing is natural in the *coefficient module* `M` (the
contravariant variable of `Ext`): for a homomorphism of `G`-modules `π : M ⟶ M'`,
`levelPair f ι (π^* y) h = levelPair f ι y (π_* h)`.  This is the engine of every dévissage step:
it lets a detecting class defined for a quotient `M'` of `M` be pulled back to `M`.

### Status of the target and the precise obstruction (2026-09-27)

The statement is true in every case that can be computed:

* for the *trivial* module `M = 𝔽_p` the detection is exactly the norm criterion
  (`Work.SSGRoute.levelPair_trivial_eq_zero_iff_normB`): for `h ≠ 0` the kernel `N = ker h` has
  index `p` in `D_{w'}`, and the level pairing vanishes iff the tested unit `a` is an
  `N`-norm; the norm-image `N_{E'/k_v}(E'ˣ)` is a *proper* subgroup of `k_vˣ` by the norm index
  theorem (`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`), so some `a` is not
  a norm and detects `h`.  This is the base case of any dévissage.
* for `M` a direct sum of rank-one trivial modules the statement is additivity of the pairing
  (`levelPair_add`, `levelPair_zero`).
* for `M` induced from a subgroup (`M = 𝔽_p[D_w]`, `D_w = ℤ/2`, …) the detection is carried by
  Shapiro's lemma at the subgroup `N = ker (D_{w'} ↠ D_w)`; the `N`-level criterion is again the
  norm criterion for the *coefficient module* `L_{w'}ˣ` (available as
  `Work.SSGRoute.normCriterion_quotient`, whose hypothesis `H¹(N, ·) = 0` is Hilbert 90,
  `Work.SSGRoute.hilbert90_localUnitsRep`).
* at archimedean places the hypothesis `p ∣ |D_{w'}|` forces `p = 2` and `D_{w'} = ℤ/2`; the
  pairing `ℝˣ/ℝˣ² × H¹(ℤ/2, 𝔽₂) → Br(ℂ/ℝ) = ℤ/2` is nondegenerate (`DESIGN_FIX.md` §2).

The general case needs a dévissage of an arbitrary finite `p`-torsion `M` over `D_w`.  The
quotient step is available (`levelPair_coeff_naturality` above): if a *proper quotient* `M'` of `M`
still detects `h` (i.e. `π_* h ≠ 0` for `M ↠ M'`), then a detecting class for `M'` pulls back to
one for `M`.

The remaining case is `h` supported in the *Frattini* submodule `Φ(M) = ⋂ {maximal submodules}`
— equivalently, `h` dies in `H¹(D_{w'}, M/Φ(M))`.  Here the pullback of a detecting class for the
submodule `Φ(M) ⊆ M` need not exist, because the restriction maps
`Ext¹_{D_w}(M, A) → Ext¹_{D_w}(Φ(M), A)` (`A = K_wˣ`) are not surjective in general.  Deciding the
pushforward direction requires the level-wise local Tate duality for arbitrary finite torsion
coefficients, i.e. Milne, *Arithmetic Duality Theorems*, I.1.8 at `r = 0` for the coefficient module
`L_{w'}ˣ` — the chapter that is **absent from this workspace** (`PT/localTatePairing_deg02.lean`
records that the naive level-wise `Ext`-form of local duality is not available and that the correct
statement is the direct-limit form over the levels).  Equivalently: the statement is a consequence
of the *realisation* clause of `local_duality_ext` (clause (ii)) when that clause holds, but clause
(ii) itself fails at small levels, so it must be replaced by the weaker "right radical = 0" — which
is what this file asks for. -/

/-- **Naturality of the level pairing in the coefficient module.**  For a homomorphism of
`G`-modules `π : M ⟶ M'`, a class `y ∈ Ext^r_G(M', A)` and a class `h ∈ H^s(H, res_f M)`, the
pairing of the pullback `π^* y ∈ Ext^r_G(M, A)` with `h` equals the pairing of `y` with the
pushforward `π_* h ∈ H^s(H, res_f M')`.  In other words the level pairing
`levelPair f ι : Ext^r_G(M,A) × H^s(H, res_f M) → H^{s+r}(H, B)` is natural in the coefficient
module `M`. -/
theorem levelPair_coeff_naturality {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **The quotient step of the dévissage.**  If `π : M ⟶ M'` is a homomorphism of `D_w`-modules
and the class `h` pushed to `H¹(D_{w'}, res M')` is detected by a class `y` at the level `D_w`,
then `h` itself is detected by the pulled-back class `π^* y`. -/
theorem detect_of_quotient {G H : Type} [Group G] [Group H] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B)
    (y : Abelian.Ext.{0} M' A 1) (h : extH (Rep.res f M) 1)
    (hy : levelPair f ι y (h.comp (Abelian.Ext.mk₀ (Rep.resMap f π)) (add_zero 1)) ≠ 0) :
    ∃ y' : Abelian.Ext.{0} M A 1, levelPair f ι y' h ≠ 0 :=
  ⟨(Abelian.Ext.mk₀ π).comp y (zero_add 1),
    by rw [levelPair_coeff_naturality]; exact hy⟩

/-! ## The cyclic base case, assembled

At a level whose decomposition group `D_{w'}` is *cyclic of order `p`*, the norm criterion
`levelPair_trivial_eq_zero_iff_norm` reduces the detection of `h` to the single arithmetic
statement that the norm endomorphism of `L_{w'}ˣ` is not surjective onto the fixed units
`k_vˣ` (the norm index theorem, `normImage_at_level_proper` for `N = ⊥`).  We record the
assembly step here: *given* a `φ` whose value on `1` is outside the norm range, the
`pushClass`-class of `φ` detects `h`. -/

section BaseCase

variable (p : ℕ) [Fact p.Prime] (k K : Type)
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K] (w : NK.GlobalCFT.Place K)

/-- **Trivial-coefficient detection at a cyclic level of order `p`** (assembly form).  For a level
`L ⊇ K` whose decomposition group `D_{w'}` is cyclic of order `p`, any `φ : ℤ → K_wˣ` whose value
on `1` lies outside the norm endomorphism of `L_{w'}ˣ` yields a `y = pushClass_lde p K_wˣ φ` that
detects every nonzero class `h ∈ H¹(D_{w'}, 𝔽_p)`.

The remaining arithmetic input — the existence of such a `φ`, i.e. the properness of the norm
image `N_{E'/k_v}E'ˣ ⊊ k_vˣ` for the degree-`p` level `E' = L_{w'}` — is
`Work.SSGRoute.normImage_at_level_proper` (the norm index theorem in the local-units
vocabulary). -/
theorem detect_trivial_cyclic_of_norm_notMem
    (b : SSGRoute.Phi1.ExtGroupCohomologyBridge)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w')]
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (φ : unitRep (decompK (k := k) w) ⟶ localUnitsK (k := k) w)
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') = p)
    (hnot : (Rep.Hom.hom (((Rep.resFunctor f).map φ) ≫ ι) 1) ∉
      Set.range (Rep.Hom.hom (NK.HassePrinciple.localUnitsRep k L w').norm))
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))) 1) (hne : h ≠ 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  refine ⟨pushClass_lde p (localUnitsK (k := k) w) φ, fun hzero => hnot ?_⟩
  exact (levelPair_trivial_eq_zero_iff_norm b p k K w L w' hw' f ι φ hcyc hcard h hne).mp hzero

end BaseCase


/-! ## Assembly plan (node Y5 of the ssg6 E7b redesign)

The project lead's redesign (`requests/ssg6/DESIGN_E7B.md`, summarised in `E7B_STATUS.md` §2 and in
the docstring of `SSGRoute/decompK_restrict_surjective.lean`) makes this file node **Y5**: the
statement above is *unchanged* and is assembled from three top-level nodes, all of which are on
disk (currently in progress):

* **Y3** `Work.SSGRoute.levelPair_baseChange` (`SSGRoute/levelPair_baseChange.lean`): for
  `k ⊆ k' ⊆ K`, with `S := ((decompK (k := k') w).map (restrictScalarsHom k k')).comap
  (decompK (k := k) w).subtype` it gives `Nonempty (decompK (k := k') w ≃* S)`, an additive
  equivalence `eE` of the two `Ext¹`-groups, the equality of the `p`-torsion cardinalities at
  `H²`, and equivalences `eH`, `eB` intertwining the level pairings of the `k`-world (at the
  subgroup `S`) and the `k'`-world.
* **Y4** `Work.SSGRoute.local_detect_h_pgroup` (`SSGRoute/local_detect_h_pgroup.lean`):
  `RightDetect f ι N` for every finite `p`-torsion `N` and `hp : p ∣ |D_{w'}|`, whenever
  `IsPGroup p (decompK (k := k) w)`.
* **X5** `Work.SSGRoute.rightDetect_of_sylow` (`SSGRoute/rightDetect_of_sylow.lean`): Sylow descent
  — for `f : G ↠ D` and `S ≤ D` of index prime to `p`, right detection for `res_S M` on `S' ↠ S`
  gives right detection for `M` on `G ↠ D`, given the two `H²`-`p`-torsion cardinality facts.

The assembly (steps 1–4 of the lead's plan; `RightDetect f ι (Rep.res (decompK w).subtype M)` is
exactly the conclusion of the statement above):

1. `Sylow.nonempty (p := p) (G := decompK (k := k) w)` gives a Sylow `p`-subgroup `S`; set
   `k' := IntermediateField.fixedField (S.map (decompK (k := k) w).subtype)`.  Y3's `S` is this
   Sylow subgroup, by `IntermediateField.fixingSubgroup_fixedField` (`FiniteDimensional k K`).
2. `IsPGroup p (decompK (k := k') w)` holds (it is Y3's `S`, a Sylow `p`-subgroup), so Y4 at `k'`
   gives `RightDetect` in the `k'`-world at the level `L`.
3. Y3's `eE`, `eH`, `eB` transport that to `RightDetect` at the subgroup `S` in the `k`-world
   (the hypothesis `hdet` of X5).
4. X5 with `S =` the Sylow subgroup (`¬ p ∣ S.index`), `hf` from
   `Work.SSGRoute.decompK_restrict_surjective`, `hTG` from `Work.SSGRoute.local_pTorsion_card` at
   the level `L`, and `hTS` from Y3's `p`-torsion clause together with `local_pTorsion_card` at
   `k'`, yields `RightDetect f ι (Rep.res (decompK (k := k) w).subtype M)`, i.e. the statement.

`E7b(ii)` is then closed by the proved `Work.SSGRoute.local_duality_ext_realization_of_detection`. -/


/-! ## The Y5 assembly, step 1

The Sylow `p`-subgroup `S ≤ D_w` and the fixed field `k' = K^S` that the base-change node `Y3`
(`Work.SSGRoute.levelPair_baseChange`) is applied to: `levelPair_baseChange`'s `S` is
`((decompK (k := k') w).map (restrictScalarsHom k k')).comap (decompK (k := k) w).subtype`, and by
`IntermediateField.fixingSubgroup_fixedField` applied to the fixed field of
`S.map (decompK (k := k) w).subtype` this is the Sylow subgroup itself. -/

/-- **Step 1 of the Y5 assembly.**  There is a Sylow `p`-subgroup `S` of `D_w = decompK w` (whose
index is prime to `p`), and the fixed field `K^S` has `S.map .subtype` as its fixing subgroup. -/
theorem exists_sylow_fixedField_setup (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    ∃ S : Subgroup (decompK (k := k) w),
      IsPGroup p S ∧ ¬ p ∣ S.index ∧
      (IntermediateField.fixedField (S.map (decompK (k := k) w).subtype)).fixingSubgroup =
        S.map (decompK (k := k) w).subtype := by
  classical
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := decompK (k := k) w)
  refine ⟨(P : Subgroup (decompK (k := k) w)), P.isPGroup', Sylow.not_dvd_index P, ?_⟩
  exact IntermediateField.fixingSubgroup_fixedField _


/-- **The `k'`-world of the Y5 assembly (instances).**  For a subgroup `P ≤ Gal(K/k)` with fixed
field `k' = K^P`:

* `K/k'` is Galois — Mathlib's `IsGalois.tower_top_intermediateField`, which needs no normality of
  `P` (this is what makes the Sylow base change work: `S` is Sylow, hence in general *not* normal,
  so `IsGalois.of_fixedField_normal_subgroup` does not apply);
* `Gal(K/k')` is (the transport of) `P`, hence a `p`-group when `P` is, by
  `Work.SSGRoute.SylowIn.isPGroup_fixedField`;
* `k'` is a number field (a subfield of the number field `K` containing `k`). -/
theorem fixedField_world_instances (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (P : Subgroup (K ≃ₐ[k] K)) (hP : IsPGroup p P) :
    IsGalois ↥(IntermediateField.fixedField P) K ∧
      IsPGroup p (K ≃ₐ[↥(IntermediateField.fixedField P)] K) ∧
      NumberField ↥(IntermediateField.fixedField P) :=
  ⟨inferInstance, SylowIn.isPGroup_fixedField (P := P) hP, inferInstance⟩


/-- **The action on places only sees the underlying function.**  For a tower `k ⊆ k' ⊆ K` and
`σ : K ≃ₐ[k'] K`, forgetting the `k'`-linearity of `σ` does not change its action on the places of
`K`: both `SMul` instances act by pushing the place forward along the underlying function, so the
two sides are definitionally equal (the archimedean action is `w ↦ w ∘ σ⁻¹` and the nonarchimedean
one sends a prime to its image under the induced map of rings of integers, which is `σ` on
elements). -/
theorem place_smul_restrictScalarsHom (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k k'] [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' K] (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K) σ) • w = σ • w := by
  cases w <;> rfl

/-- **The decomposition group of `w` over the fixed field `K^P`.**  For a subgroup `P ≤ D_w`, the
image of the decomposition group of `w` in `Gal(K/K^P)` — viewed in `Gal(K/k)` by forgetting the
`K^P`-linearity — is exactly `P`:

* every `K^P`-automorphism of `K` is `K^P`-linear, hence its image in `Gal(K/k)` lies in the fixing
  subgroup of `K^P`, which is `P` (`IntermediateField.fixingSubgroup_fixedField`);
* conversely an element `x ∈ P ≤ D_w` fixes `w`, and the `K^P`-automorphism of `K` attached to `x`
  by `IntermediateField.fixingSubgroupEquiv` (which has the same underlying function as `x`) is in
  the decomposition group by `place_smul_restrictScalarsHom`. -/
theorem map_restrictScalarsHom_decompK_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K)) (hPD : P ≤ decompK (k := k) w) :
    (decompK (k := ↥(IntermediateField.fixedField P)) w).map
      (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P)) (A := K)) = P := by
  classical
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, -, rfl⟩
    have hmem : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
        (A := K) σ) ∈ (IntermediateField.fixedField P).fixingSubgroup :=
      ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)).symm σ).2
    rwa [IntermediateField.fixingSubgroup_fixedField P] at hmem
  · intro hx
    have hx' : x ∈ (IntermediateField.fixedField P).fixingSubgroup := by
      rwa [IntermediateField.fixingSubgroup_fixedField P]
    refine ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P)) ⟨x, hx'⟩, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      rw [← place_smul_restrictScalarsHom k ↥(IntermediateField.fixedField P) K]
      have hrst : (AlgEquiv.restrictScalarsHom (R := k) (S := ↥(IntermediateField.fixedField P))
          (A := K) ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField P))
            ⟨x, hx'⟩)) = x :=
        AlgEquiv.ext fun y => rfl
      rw [hrst]
      exact MulAction.mem_stabilizer_iff.mp (hPD hx)
    · exact AlgEquiv.ext fun y => rfl


/-- **The `k'`-world restriction map `f'` (Y5, step 2 setup).**  For a subgroup `P ≤ Gal(K/k)` with
fixed field `k' = K^P`, the restriction to `K` of a `k'`-automorphism of `L` stabilizing `w'` is the
`k'`-automorphism `galRes k' K L σ` of `K`, and it stabilizes the place `w` below `w'`.  This is
`Work.SSGRoute.decompK_restrict_exists` instantiated at the base field `k'`. -/
theorem exists_restrictionMap_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K)) :
    ∃ f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
        decompK (k := ↥(IntermediateField.fixedField P)) w,
      ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
          K ≃ₐ[↥(IntermediateField.fixedField P)] K)
        = galRes ↥(IntermediateField.fixedField P) K L
            (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L) := by
  haveI : IsGalois ↥(IntermediateField.fixedField P) L :=
    IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L
  exact decompK_restrict_exists ↥(IntermediateField.fixedField P) K L w w' hw'


/-- **The `k'`-world coefficient map `ι'` (Y5, step 2 setup).**  For a subgroup `P ≤ Gal(K/k)` with
fixed field `k' = K^P`, any restriction map `f'` with the `hf'` condition admits the canonical local
coefficient map `ι' : K_wˣ → L_{w'}ˣ` induced by `Place.localAlgebraMapUnits` — the `k'`-world
counterpart of the map `ι` of the target.  This is `Work.SSGRoute.localUnitsMap_exists` at `k := ↥k'`
(the one instance it needs beyond the tower data, `IsGalois ↥k' L`, being
`IsGalois.tower_top_of_isGalois`). -/
theorem exists_localUnitsMap_fixedField (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K))
    [IsGalois ↥(IntermediateField.fixedField P) L]
    (f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
        decompK (k := ↥(IntermediateField.fixedField P)) w)
    (hf' : ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
        K ≃ₐ[↥(IntermediateField.fixedField P)] K)
      = galRes ↥(IntermediateField.fixedField P) K L
          (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L)) :
    ∃ ι' : Rep.res f' (localUnitsK (k := ↥(IntermediateField.fixedField P)) w) ⟶
        NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w',
      ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι'.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) :=
  localUnitsMap_exists ↥(IntermediateField.fixedField P) K L w w' hw' f' hf'


/-- **`IsGalois` over a fixed field, at any upper level.**  For `K/k` Galois and any subgroup
`P ≤ Gal(K/k)`, the extension `L/K^P` is Galois for every `L ⊇ K` that is Galois over `k`.  This is
`IsGalois.tower_top_of_isGalois` applied to the nested base `k ⊆ ↥(K^P) ⊆ L`; registering it makes
the `[IsGalois ↥(K^P) L]` binder that the Y5 base change (and, more generally, `localUnitsRep` over
a fixed field) needs discharge automatically. -/
instance instIsGalois_fixedField_of_isGalois (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (P : Subgroup (K ≃ₐ[k] K)) : IsGalois ↥(IntermediateField.fixedField P) L :=
  IsGalois.tower_top_of_isGalois k (IntermediateField.fixedField P) L

/-- **The `k'`-world level data of the Y5 assembly.**  At a level `L ⊇ K`, `w' ∣ w` and the
`k`-world data `f`, `hf`, `ι`, `hι`, the `k'`-world data `f'`, `hf'`, `ι'`, `hι'` exist (via
`exists_restrictionMap_fixedField` and `exists_localUnitsMap_fixedField`); the `[IsGalois ↥k' L]`
instances are discharged by `instIsGalois_fixedField_of_isGalois`. -/
theorem fixedField_levelData (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (P : Subgroup (K ≃ₐ[k] K)) :
    ∃ (f' : MulAction.stabilizer (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w' →*
          decompK (k := ↥(IntermediateField.fixedField P)) w)
      (hf' : ∀ σ, ((f' σ : decompK (k := ↥(IntermediateField.fixedField P)) w) :
          K ≃ₐ[↥(IntermediateField.fixedField P)] K)
        = galRes ↥(IntermediateField.fixedField P) K L
            (σ : L ≃ₐ[↥(IntermediateField.fixedField P)] L))
      (ι' : Rep.res f' (localUnitsK (k := ↥(IntermediateField.fixedField P)) w) ⟶
          NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w')
      (hι' : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι'.hom (Additive.ofMul u)
          = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)),
      True := by
  obtain ⟨f', hf'⟩ := exists_restrictionMap_fixedField k K L w w' hw' P
  obtain ⟨ι', hι'⟩ := exists_localUnitsMap_fixedField k K L w w' hw' P f' hf'
  exact ⟨f', hf', ι', hι', trivial⟩


theorem local_duality_ext_detect_h (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) (hne : h ≠ 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      levelPair f ι y h ≠ 0 := by
  classical
  -- ## Step 1: the Sylow `p`-subgroup `S₀ ≤ D_w` and the subgroup `S = P.comap subtype`
  obtain ⟨S₀, hS₀group, hidxS₀, _hfixS₀⟩ := exists_sylow_fixedField_setup (p := p) k K w
  let P : Subgroup (K ≃ₐ[k] K) := S₀.map (decompK (k := k) w).subtype
  let S : Subgroup (decompK (k := k) w) := P.comap (decompK (k := k) w).subtype
  have hPgroup : IsPGroup p P := hS₀group.map (decompK (k := k) w).subtype
  have hPD : P ≤ decompK (k := k) w := by
    rintro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSeq : S = S₀ := by
    show (S₀.map (decompK (k := k) w).subtype).comap (decompK (k := k) w).subtype = S₀
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext (by simpa using hyx)
      rwa [← hxy]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSindex : ¬ p ∣ S.index := by rw [hSeq]; exact hidxS₀
  -- ## Step 2: the source group is `S.comap f` and `p` divides its order
  have hfsurj : Function.Surjective f := decompK_restrict_surjective k K w L w' hw' f hf
  have hpS : p ∣ Nat.card (S.comap f) := by
    have h1 : Nat.card (S.comap f) * (S.comap f).index
        = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w') := Subgroup.card_mul_index _
    have h2 : (S.comap f).index = S.index := Subgroup.index_comap_of_surjective S hfsurj
    have h3 : p ∣ Nat.card (S.comap f) * (S.comap f).index := by rw [h1]; exact hp
    rcases ((Fact.out : p.Prime).dvd_mul (m := Nat.card (S.comap f))
      (n := (S.comap f).index)).mp h3 with hh | hh
    · exact hh
    · exact absurd (h2 ▸ hh) hSindex
  -- ## Step 3: the same divisibility in the `k'`-world (Y4's hypothesis `hp`)
  have hp' : p ∣ Nat.card (MulAction.stabilizer
      (L ≃ₐ[↥(IntermediateField.fixedField P)] L) w') :=
    Nat.card_congr (stabInclEquivL k K L P w hPD w' hw' f hf).toEquiv ▸ hpS
  -- ## Step 4: the two Sylow-level inputs of X5
  have hTS : Nat.card {x : extH (Rep.res (S.comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')) 2 // p • x = 0} = p :=
    pTorsion_card_sylowLevel p k K w P hPD L w' hw' f hf hpS
  have hdet := rightDetect_sylowLevelStabIncl p k K w P hPgroup hPD M hM L w' hw' f hf ι hι hp'
  -- ## Step 5 (X5, Sylow descent) and the unpacking of `RightDetect` at `(h, hne)`
  exact rightDetect_of_sylow p f hfsurj S hSindex ι
    (local_pTorsion_card p k L w' hp) hTS (Rep.res (decompK (k := k) w).subtype M) hM hdet h hne

end Work.SSGRoute
