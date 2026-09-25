import Mathlib
import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.levelInclHom_mem_levelObstruction
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.exists_subgroup_levelGroup_equiv_sylow
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.BrauerHasse.Profinite

namespace NK.HassePrinciple

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open NK.BrauerHasse

section Aux

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Naturality of the level transition maps in the subgroup

For an inclusion `V ≤ U` of subgroups of `Gal(K'/K)`, the `H²`-level square expressing that
*inflation between levels* commutes with *restriction to the subgroup* is the contravariant
image of the corresponding square of quotient maps. -/

/-- The quotient maps induced by an inclusion of subgroups commute with the quotient maps
induced by the inclusion of levels. -/
lemma levelQuotHom_levelInclHom_comp {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (levelInclHom hV L).comp (levelQuotHom (U := V) h) =
      (levelQuotHom (U := U) h).comp (levelInclHom hV M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-- Level square for the inflation and the restriction to a subgroup. -/
lemma levelMap_levelInclHom {p : ℕ} {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    H2.map (levelInclHom hV L) ≫ levelMap p (U := V) h =
      levelMap p (U := U) h ≫ H2.map (levelInclHom hV M) := by
  have hsq := congrArg (fun f => H2.map (p := p) f)
    (levelQuotHom_levelInclHom_comp (U := U) (V := V) hV (L := L) (M := M) h)
  rw [H2.map_comp, H2.map_comp] at hsq
  simpa only [levelMap] using hsq

/-- Elementwise form of `levelMap_levelInclHom`. -/
lemma levelMap_levelInclHom_apply {p : ℕ} {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) (a : LevelH2 p U L) :
    (levelMap p (U := V) h) ((H2.map (levelInclHom hV L)).hom a) =
      (H2.map (levelInclHom hV M)).hom ((levelMap p (U := U) h) a) := by
  have hk := congrArg (fun (k : LevelH2 p U L ⟶ LevelH2 p V M) => k.hom a)
    (levelMap_levelInclHom (p := p) hV (L := L) (M := M) h)
  simpa [ModuleCat.comp_apply] using hk

/-- The corresponding square for the *local* level groups. -/
lemma localLevelQuotHom_localLevelInclHom_comp {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (localLevelInclHom hV A L).comp (localLevelQuotHom V A h) =
      (localLevelQuotHom U A h).comp (localLevelInclHom hV A M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-- Local level square for the local inflation and the inclusion of the local level groups. -/
lemma localLevelMap_localLevelInclHom {p : ℕ} {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    H2.map (localLevelInclHom hV A L) ≫ localLevelMap p V A h =
      localLevelMap p U A h ≫ H2.map (localLevelInclHom hV A M) := by
  have hsq := congrArg (fun f => H2.map (p := p) f)
    (localLevelQuotHom_localLevelInclHom_comp (U := U) (V := V) hV A (L := L) (M := M) h)
  rw [H2.map_comp, H2.map_comp] at hsq
  simpa only [localLevelMap] using hsq

/-- Elementwise form of `localLevelMap_localLevelInclHom`. -/
lemma localLevelMap_localLevelInclHom_apply {p : ℕ} {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M)
    (x : LocalLevelH2 p U A L) :
    (localLevelMap p V A h) ((H2.map (localLevelInclHom hV A L)).hom x) =
      (H2.map (localLevelInclHom hV A M)).hom ((localLevelMap p U A h) x) := by
  have hk := congrArg (fun (k : LocalLevelH2 p U A L ⟶ LocalLevelH2 p V A M) => k.hom x)
    (localLevelMap_localLevelInclHom (p := p) hV A (L := L) (M := M) h)
  simpa [ModuleCat.comp_apply] using hk

/-- **Local vanishing transfers to a subgroup.**  If a level class of `(U,L)` dies locally at every
place after inflation to a place-dependent larger level, then so does its restriction to any
subgroup `V ≤ U`. -/
lemma levelLocVanishing_levelInclHom {p : ℕ} {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L : FiniteGaloisIntermediateField K K'} {a : LevelH2 p U L}
    (ha : levelLocVanishing p U L a) :
    levelLocVanishing p V L ((H2.map (levelInclHom hV L)).hom a) := by
  intro A
  obtain ⟨M, hLM, hM⟩ := ha A
  refine ⟨M, hLM, ?_⟩
  rw [levelInclHom_locLevel_apply p hV A.1 L a]
  rw [localLevelMap_localLevelInclHom_apply (p := p) hV A.1 hLM]
  rw [hM, map_zero]

/-! ## The index of the restriction is stable under inflation -/

/-- Computation rule for the inflation on the quotient: it is the identity on representatives. -/
lemma levelQuotHom_apply_mk {U : Subgroup Gal(K'/K)} {L M : FiniteGaloisIntermediateField K K'}
    (h : L ≤ M) (u : ↥U) :
    levelQuotHom (U := U) h (↑u : LevelGroup U M) =
      (QuotientGroup.mk' (L.fixingSubgroup.subgroupOf U)) u := by
  rw [show levelQuotHom (U := U) h = QuotientGroup.map (M.fixingSubgroup.subgroupOf U)
    (L.fixingSubgroup.subgroupOf U) (MonoidHom.id ↥U) _ from rfl]
  rw [← QuotientGroup.mk'_apply, QuotientGroup.map_mk']
  rfl

/-- The quotient map between two levels is surjective. -/
lemma levelQuotHom_surjective {U : Subgroup Gal(K'/K)} {L M : FiniteGaloisIntermediateField K K'}
    (h : L ≤ M) : Function.Surjective (levelQuotHom (U := U) h) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H u => exact ⟨(↑u : LevelGroup U M), levelQuotHom_apply_mk (U := U) h u⟩

/-- **The range of the restriction at a bigger level is the preimage of its range at a smaller
level**, provided the smaller level's fixing group is contained in the subgroup.  This is the
group-theoretic statement behind the stability of the index of the restriction under inflation:
`V/(V ⊓ Gal(K'/M))` is the preimage in `U/(U ⊓ Gal(K'/M))` of `V/(V ⊓ Gal(K'/L))`. -/
lemma range_levelInclHom_eq_comap {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (hUV : L.fixingSubgroup.subgroupOf U ≤ V.subgroupOf U)
    {M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    MonoidHom.range (levelInclHom hV M) =
      (MonoidHom.range (levelInclHom hV L)).comap (levelQuotHom (U := U) h) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hx
      refine MonoidHom.mem_range.mpr ⟨levelQuotHom (U := V) h v, ?_⟩
      have hsq := congrArg (fun f => f v)
        (levelQuotHom_levelInclHom_comp (U := U) (V := V) hV h)
      simp only [MonoidHom.comp_apply] at hsq
      rw [hsq, hv]
    · intro hx
      rw [levelQuotHom_apply_mk (U := U) h u] at hx
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf V) v
      rw [levelInclHom, QuotientGroup.map_mk'] at hv
      rw [← QuotientGroup.mk'_apply] at hv
      obtain ⟨z, hz, hzu⟩ :=
        (QuotientGroup.mk'_eq_mk' (L.fixingSubgroup.subgroupOf U)).mp hv
      have hwV : Subgroup.inclusion hV w ∈ V.subgroupOf U := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
        exact w.2
      have hzV : z ∈ V.subgroupOf U := hUV hz
      have huV : u ∈ V.subgroupOf U := by
        rw [← hzu]
        exact mul_mem hwV hzV
      refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk' _ ⟨u, ?_⟩, ?_⟩
      · rwa [Subgroup.mem_subgroupOf] at huV
      · rw [levelInclHom, QuotientGroup.map_mk']
        rw [← QuotientGroup.mk'_apply]
        congr 1

/-- **The index of the restriction is stable under inflation.**  If the fixing group of the
smaller level is contained in the subgroup, then the index of `V/(V ⊓ Gal(K'/L))` in
`U/(U ⊓ Gal(K'/L))` equals the index of `V/(V ⊓ Gal(K'/M))` in `U/(U ⊓ Gal(K'/M))`. -/
lemma index_range_levelInclHom_eq {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (hUV : L.fixingSubgroup.subgroupOf U ≤ V.subgroupOf U)
    {M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (MonoidHom.range (levelInclHom hV M)).index = (MonoidHom.range (levelInclHom hV L)).index := by
  rw [range_levelInclHom_eq_comap hV L hUV h,
    Subgroup.index_comap_of_surjective _ (levelQuotHom_surjective (U := U) h)]

/-! ## The Sylow preimage -/

/-- **The preimage in `U` of a Sylow `p`-subgroup of the level group.**  Besides the properties
proved in `exists_subgroup_levelGroup_equiv_sylow`, this `V` contains the fixing group
`U ⊓ Gal(K'/L)`, which is what makes the index of the restriction stable under inflation
(`index_range_levelInclHom_eq`). -/
theorem exists_subgroup_levelGroup_sylow_preimage {p : ℕ} [Fact p.Prime]
    (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (Q : Sylow p (LevelGroup U L)) :
    ∃ (V : Subgroup Gal(K'/K)) (hV : V ≤ U),
      L.fixingSubgroup.subgroupOf U ≤ V.subgroupOf U ∧
      MonoidHom.range (levelInclHom hV L) = Q.toSubgroup ∧
      IsPGroup p (LevelGroup V L) := by
  let φ : ↥U →* LevelGroup U L := QuotientGroup.mk' (L.fixingSubgroup.subgroupOf U)
  let W : Subgroup ↥U := Q.toSubgroup.comap φ
  let V : Subgroup Gal(K'/K) := W.map U.subtype
  have hV : V ≤ U := Subgroup.map_subtype_le W
  have hW : V.subgroupOf U = W := by
    simp only [V, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective W
  have hNL : L.fixingSubgroup.subgroupOf U ≤ V.subgroupOf U := by
    rw [hW]
    intro u hu
    refine Subgroup.mem_comap.mpr ?_
    have hphi : φ u = 1 := by
      have hker : u ∈ φ.ker := by
        rw [show φ.ker = L.fixingSubgroup.subgroupOf U from QuotientGroup.ker_mk' _]
        exact hu
      exact MonoidHom.mem_ker.mp hker
    rw [hphi]
    exact Q.toSubgroup.one_mem
  have hrange : MonoidHom.range (levelInclHom hV L) = Q.toSubgroup := by
    have hχ : MonoidHom.range (levelInclHom hV L) = (φ.comp (Subgroup.inclusion hV)).range := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf V) z
        exact ⟨v, by rw [levelInclHom, QuotientGroup.map_mk']; rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨QuotientGroup.mk' _ v, by rw [levelInclHom, QuotientGroup.map_mk']; rfl⟩
    rw [hχ, MonoidHom.range_comp, Subgroup.inclusion_range, hW, Subgroup.map_comap_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), top_inf_eq]
  refine ⟨V, hV, hNL, hrange, ?_⟩
  let f : LevelGroup V L →* ↥Q.toSubgroup :=
    MonoidHom.codRestrict (levelInclHom hV L) Q.toSubgroup
      (fun x => by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact levelInclHom_injective hV L (Subtype.ext_iff.mp hab)
    · intro q
      have hq : (q : LevelGroup U L) ∈ MonoidHom.range (levelInclHom hV L) := by
        rw [hrange]
        exact q.2
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hq
      exact ⟨x, Subtype.ext hx⟩
  exact IsPGroup.of_equiv Q.isPGroup' (MulEquiv.ofBijective f hf).symm

end Aux

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The `p`-primary Hasse principle in its level-wise form implies it at all levels.**

If the level-wise Hasse principle holds at the levels whose level group
`V/(V ⊓ Gal(K'/L))` is a `p`-group — that is, at such a level every class which dies locally at
every place (in the colimit sense, `levelLocVanishing`) is zero in the colimit — then it holds at
every level, i.e. `LevelForm p K K' κ κ'` holds.

This is the Sylow reduction in the *colimit* form.  Proof sketch: given a level class `a` at `(U,L)`
with `levelLocVanishing`, let `Q` be a Sylow `p`-subgroup of the finite level group
`Γ = U/(U ⊓ Gal(K'/L))` and `V ≤ U` its preimage (`exists_subgroup_levelGroup_equiv_sylow`); then
`LevelGroup V L ≃* Q`, the index of `V` in `U` is prime to `p` (so that, at every level `M ≥ L`, the
restriction `H2.map (levelInclHom hV M)` is injective by
`H2_map_injective_of_coprime_index`), and the local vanishing of `a` transfers to the restriction of
`a` to `(V,L)` (naturality of the localisation in the subgroup,
`levelInclHom_locLevel_apply`, plus naturality of the *local* inflation).  The `p`-primary
hypothesis then gives `ofLevel L (res a) = 0` in `H²(V, Z/p)`, hence (by the description of equality
in the filtered colimit, `ofLevel_eq_iff`) `levelMap_{L→M} (res a) = 0` for some `M ≥ L`;
functoriality of the inflation in the subgroup identifies this with
`res (levelMap_{L→M} a) = 0`, and injectivity of `res` at the level `M` gives
`levelMap_{L→M} a = 0`, i.e. `ofLevel L a = 0` in `H²(U, Z/p)`. -/
theorem levelForm_of_pgroupLevel {p : ℕ} (hp : p.Prime)
    (h : ∀ (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K'),
      IsPGroup p (LevelGroup V L) → ∀ a : LevelH2 p V L, levelLocVanishing p V L a →
        H2Profinite.ofLevel L a = 0) :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro U _hU _hκ L a ha
  -- A Sylow `p`-subgroup `Q` of the finite level group and its preimage `V ≤ U` in `U`.
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := LevelGroup U L)
  obtain ⟨V, hV, hUV, hrange, hP⟩ := exists_subgroup_levelGroup_sylow_preimage (K := K) (K' := K')
    U L Q
  -- The local vanishing of `a` transfers to the restriction of `a` to `(V,L)`.
  have hvan : levelLocVanishing p V L ((H2.map (levelInclHom hV L)).hom a) :=
    levelLocVanishing_levelInclHom hV ha
  -- The `p`-primary hypothesis kills the class of the restriction in the colimit.
  have hzeroV : H2Profinite.ofLevel L ((H2.map (levelInclHom hV L)).hom a) = 0 := h V L hP _ hvan
  -- Hence it dies at some finite level `M ≥ L`.
  obtain ⟨M, hLM, _h₂, he⟩ := (ofLevel_eq_iff (p := p) (U := V) (L := L)
    (L' := ⊥) ((H2.map (levelInclHom hV L)).hom a) (0 : LevelH2 p V ⊥)).mp
      (hzeroV.trans
        (ofLevel_zero (p := p) (U := V) (⊥ : FiniteGaloisIntermediateField K K')).symm)
  -- The inflation of the restriction is the restriction of the inflation.
  have hkey : (H2.map (levelInclHom hV M)).hom ((levelMap p (U := U) hLM) a) = 0 := by
    have h1 : (levelMap p (U := V) hLM) ((H2.map (levelInclHom hV L)).hom a) = 0 := by
      rw [he, map_zero]
    rwa [levelMap_levelInclHom_apply (p := p) hV hLM a] at h1
  -- The index of the restriction at the level `M` equals `[Γ : Q]`, which is prime to `p`.
  have hcop : Nat.Coprime (Subgroup.index (MonoidHom.range (levelInclHom hV M))) p := by
    rw [index_range_levelInclHom_eq hV L hUV hLM, hrange, Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr Q.not_dvd_index
  -- Restriction to the subgroup of prime-to-`p` index is injective.
  have hzM : (levelMap p (U := U) hLM) a = 0 :=
    H2_map_injective_of_coprime_index (p := p) (levelInclHom hV M)
      (levelInclHom_injective hV M) hcop (hkey.trans (map_zero _).symm)
  calc H2Profinite.ofLevel L a
      = H2Profinite.ofLevel M ((levelMap p (U := U) hLM) a) :=
        (H2Profinite.ofLevel_levelMap (p := p) (U := U) hLM a).symm
    _ = H2Profinite.ofLevel M (0 : LevelH2 p U M) := by rw [hzM]
    _ = 0 := ofLevel_zero (p := p) (U := U) M

end NK.HassePrinciple
