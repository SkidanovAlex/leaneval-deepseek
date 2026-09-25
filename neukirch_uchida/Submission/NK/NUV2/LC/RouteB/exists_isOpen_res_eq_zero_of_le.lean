import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.BrauerHasse.ofLevel_eq_iff
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NUV2/LC/RouteB/DESIGN_containment_v3.md first (the orchestrator's redesign of decompContainment_B; your lemma is one node). Never use the circular le_stabSubgroup_of_localType, SurjTwo/HasseTwo/ABHNSurjectivity shapes. hFC and hKC are PROVED (NK.CFTLib.fundamentalClassElement, NK.NUV2.kernelCondition_all).

# exists_isOpen_res_eq_zero_of_le (helper S5, formal; only Branch L needs it)

**Target file** `RouteB/exists_isOpen_res_eq_zero_of_le.lean`. Imports: `Submission.NK.NUV2.LC.RouteB.Defs`,
`Submission.NK.BrauerHasse.ofLevel_eq_iff`, `Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist`.

This is L1b (`exists_isOpen_le_res_eq_zero`, `RouteB/res_eq_zero_of_isOpen_le.lean`) **without**
`IsOpen W`, which the local groups `U ⊓ D_A` never satisfy.

**Proof.** Write `y = ofLevel L a`. Since `res y = ofLevel L (H2.map (levelInclHom hVW L) a) = 0`,
`ofLevel_eq_iff` gives some `M ≥ L` with `H2.map (levelInclHom hVW M) (levelMap a) = 0`. Put
`N := V ⊔ M.fixingSubgroup`, which is open. Then `levelInclHom : LevelGroup V M → LevelGroup (W ⊓ N) M` is
bijective:
- surjective: every element of `W ∩ V·G_M` is `v·g` with `v ∈ V` and `g ∈ G_M`;
- injective: `V ∩ G_M = V ∩ (W ⊓ N) ∩ G_M`.

So `res_{W→W⊓N}` of the level-`M` class is zero too. Use `levelInclHom_surjective_of_le_sup_fixingSubgroup`
from the same file, and `H2_map_mulEquiv_ne_zero` / `H2_map_ne_zero_of_bijective`
(`RouteB/onePlaceLevelClassesNaive.lean`).

**Sanity check.** If `V = W`, take `N = ⊤`.
-/

namespace NK.NUV2.LC.RouteB

open CategoryTheory

set_option maxHeartbeats 1600000

/-- **Surjectivity of the level inclusion.**  If every element of `U` can be written as `v · n` with
`v ∈ V` and `n ∈ Gal(K'/L)`, then the quotient map `V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))` is
surjective.  (Local copy of the helper of the same name in
`Submission/Work/NUV2/LC/RouteB/res_eq_zero_of_isOpen_le.lean`, to keep this module
self-contained.) -/
private lemma levelInclHom_surj_aux {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (hU : U ≤ V ⊔ L.fixingSubgroup) :
    Function.Surjective (NK.BrauerHasse.levelInclHom h L) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨v, hv, n, hn, hvn⟩ := Subgroup.mem_sup_of_normal_right.mp (hU u.2)
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_⟩
    rw [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    show v⁻¹ * (u : Gal(K'/K)) ∈ L.fixingSubgroup
    rw [← hvn]
    have h2 : v⁻¹ * (v * n) = n := by group
    rw [h2]
    exact hn

/-- Continuity of `H²(·, Z/p)` for an arbitrary (not necessarily open) ambient subgroup `W`: if the
restriction of `y ∈ H²(W)` to `V ≤ W` vanishes, it already vanishes on `W ⊓ N` for some open
`N ⊇ V`.  (Proof: represent `y` at a level, kill the restriction at a level `M`, take
`N := V ⊔ Gal(K'/M)`; the level groups of `V` and `W ⊓ N` at `M` coincide.) -/
theorem exists_isOpen_res_eq_zero_of_le (p : ℕ) [NeZero p] {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] {V W : Subgroup Gal(K'/K)}
    (hVW : V ≤ W) (y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p W)
    (hy : NK.LocalDecomposition.H2Profinite.res p hVW y = 0) :
    ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧ V ≤ N ∧
      NK.LocalDecomposition.H2Profinite.res p (inf_le_left : W ⊓ N ≤ W) y = 0 := by
  obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective y
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel] at hy
  obtain ⟨M, hLM, hz⟩ :=
    (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p) (U := V)
      ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hVW L)).hom a)).mp hy
  rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p hVW hLM a] at hz
  refine ⟨V ⊔ M.fixingSubgroup, ?_, le_sup_left, ?_⟩
  · exact Subgroup.isOpen_mono le_sup_right
      (IntermediateField.fixingSubgroup_isOpen (M : IntermediateField K K'))
  · rw [NK.LocalDecomposition.H2Profinite.res_ofLevel]
    refine (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p)
      (U := W ⊓ (V ⊔ M.fixingSubgroup))
      ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom
        (inf_le_left : W ⊓ (V ⊔ M.fixingSubgroup) ≤ W) L)).hom a)).mpr
      ⟨M, hLM, ?_⟩
    rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p
      (inf_le_left : W ⊓ (V ⊔ M.fixingSubgroup) ≤ W) hLM a]
    -- The level group of `V` is a common quotient of the level groups of `W ⊓ N` and of `V`.
    have h₁ : V ≤ W ⊓ (V ⊔ M.fixingSubgroup) := le_inf hVW le_sup_left
    have hsurj : Function.Surjective (NK.BrauerHasse.levelInclHom h₁ M) :=
      levelInclHom_surj_aux h₁ M inf_le_right
    have hhom : NK.BrauerHasse.levelInclHom (U := W) (V := V) hVW M =
        (NK.BrauerHasse.levelInclHom
            (inf_le_left : W ⊓ (V ⊔ M.fixingSubgroup) ≤ W) M).comp
          (NK.BrauerHasse.levelInclHom h₁ M) := by
      rw [NK.NUV2.LC.OddTwist.levelInclHom_comp p h₁
        (inf_le_left : W ⊓ (V ⊔ M.fixingSubgroup) ≤ W) M]
    have hinj := NK.HassePrinciple.h2Map_injective_of_bijective (p := p)
      (NK.BrauerHasse.levelInclHom h₁ M)
      ⟨NK.HassePrinciple.levelInclHom_injective h₁ M, hsurj⟩
    have hz' := hz
    rw [hhom, NK.BrauerHasse.H2.map_comp, ModuleCat.comp_apply] at hz'
    exact hinj (by simpa using hz')

end NK.NUV2.LC.RouteB
