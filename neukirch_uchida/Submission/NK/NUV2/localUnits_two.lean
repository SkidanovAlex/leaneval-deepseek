import Mathlib
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.NUV2.PrincipalUnitBall
import Submission.NK.NUV2.LocalUnitsAux
import Submission.NK.NUV2.BallCoverAux
import Submission.NK.NUV2.unitCover_two

/-!
# The `ℤ_2`-rank of the local units at a place above `2`: `NK.NUV2.localUnits_two`

**The target.**  `NK.RankTheoryDeep.LocalUnitDualRankInput.{0} 2`, the local unit structure at
the places `q | 2` consumed by the idèle-side rank computation of CoNF (10.3.20): for a number
field `K` and a finite prime `q` of `K` of residue characteristic `2`,

`rank_{ℤ_2} Hom_cts(𝒪_qˣ, ℤ_2) ≤ e(q|2) · f(q|2)`.

**The proof.**  The bound is attained (`𝒪_qˣ ≅ μ_{q-1} × (1+𝔪)`, `1+𝔪 ≅ ℤ_2^{ef}`), and the route
here is the elementary one through the `2`-adic exponential and logarithm of
`Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq`:

1. `NK.NUV2.ballCover_two`: the additive ball `𝔪^M` is covered by `e·f` elements modulo `2`
   (the layer `𝔪^M/𝔪^{M+e} ≅ 𝓞/𝔪^e` is `(ℤ/2)^{ef}`);
2. `NK.NUV2.unitCover_two`: pushing this through `exp` — an isomorphism between the additive
   ball and the principal-unit ball `1 + 𝔪^{M'}` — covers the principal-unit ball by `e·f` elements
   modulo *squares*;
3. `NK.NUV2.LocalUnitsAux.rank_dual_le_of_cover_subtype`: a cover modulo `ℓ`-th powers bounds the
   `ℤ_ℓ`-rank of the continuous dual by the number of generators (the `ℓ`-th powers contribute only
   a factor `ℓ`);
4. `NK.NUV2.LocalUnitsAux.rank_dual_le_of_finiteIndex`: a finite-index subgroup has the same
   rank, and `1 + 𝔪^{M'}` has finite index in `𝒪_qˣ`
   (`NK.NUV2.principalUnitBall_finiteIndex`).

The passage between the units of the completed ring of integers and the local units
`𝒪_qˣ = NK.GlobalCFT.Place.localUnits K (ofFinite q)` is the canonical isomorphism
`Submonoid.unitsEquivUnitsType`, under which the cover and the finite index transport.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField WithZero

namespace NK.NUV2

open IsDedekindDomain

/-- **The `ℤ_2`-rank of the local units at a place of residue characteristic `2` is at most the
local degree.** -/
theorem localUnits_two : NK.RankTheoryDeep.LocalUnitDualRankInput.{0} 2 := by
  intro K _ _ q hlies
  -- the additive cover of `𝔪^M` by `e·f` elements modulo `2`
  obtain ⟨b, hb, hcov⟩ := BallCoverAux.ballCover_two' q hlies 1
  -- pushing it through `exp` covers the principal-unit ball by `e·f` elements modulo squares
  obtain ⟨M', hle, hM'1, b', hb', hcov'⟩ := unitCover_two K q hlies b 1 le_rfl hb hcov
  -- the principal-unit ball `1 + 𝔪^{M'}` of `𝓞_{K_q}ˣ`
  set U : Subgroup (q.adicCompletionIntegers K)ˣ := principalUnitBall K q M' with hU
  have hUfin : U.FiniteIndex := by
    rw [hU]; exact principalUnitBall_finiteIndex K q M'
  have hb'U : ∀ i, b' i ∈ U := by
    intro i
    rw [hU]
    exact (mem_principalUnitBall_iff_val q M' (b' i)).mpr (hb' i)
  -- the canonical isomorphism `𝒪_qˣ ≃ (𝓞_{K_q})ˣ`
  let e : ↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q)) ≃*
      (q.adicCompletionIntegers K)ˣ :=
    Submonoid.unitsEquivUnitsType (q.adicCompletionIntegers K).toSubmonoid
  -- the same subgroup inside the local units
  set U' : Subgroup ↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q)) :=
    U.comap e.toMonoidHom with hU'def
  have hU'fin : U'.FiniteIndex := by
    refine Subgroup.FiniteIndex.mk ?_
    rw [hU'def, Subgroup.index_comap_of_surjective U (f := e.toMonoidHom) e.surjective]
    exact Subgroup.FiniteIndex.index_ne_zero (H := U)
  -- the generators, transported to the local units
  set g : Fin (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) →
      ↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q)) :=
    fun i => e.symm (b' i) with hgdef
  have hg : ∀ i, g i ∈ U' := by
    intro i
    rw [hgdef, hU'def, Subgroup.mem_comap]
    rw [show e.toMonoidHom (e.symm (b' i)) = b' i from MulEquiv.apply_symm_apply e (b' i)]
    exact hb'U i
  -- the cover of `U'` modulo squares, transported along the isomorphism
  have hcover : ∀ a ∈ U', ∃ z ∈ Subgroup.closure (Set.range g), ∃ w ∈ U', a = z * w ^ 2 := by
    intro a ha
    have ha' : e a ∈ U := by rwa [hU'def, Subgroup.mem_comap] at ha
    obtain ⟨z, hz, w, hw, hzw⟩ :=
      hcov' (e a) ((mem_principalUnitBall_iff_val q M' (e a)).mp (by rw [← hU]; exact ha'))
    have hwU : w ∈ U := (mem_principalUnitBall_iff_val q M' w).mpr hw
    refine ⟨e.symm z, ?_, e.symm w, ?_, ?_⟩
    · have h1 : e.symm z ∈ Subgroup.map e.symm.toMonoidHom (Subgroup.closure (Set.range b')) :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [MonoidHom.map_closure] at h1
      have himg : (e.symm.toMonoidHom '' Set.range b' : Set _) =
          Set.range (fun i => e.symm (b' i)) := by
        ext y
        constructor
        · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩; exact ⟨b' i, ⟨i, rfl⟩, rfl⟩
      rw [himg] at h1
      rw [hgdef]
      exact h1
    · rw [hU'def, Subgroup.mem_comap]
      rw [show e.toMonoidHom (e.symm w) = w from MulEquiv.apply_symm_apply e w]
      exact hwU
    · refine e.injective ?_
      rw [map_mul, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hzw
  show Module.rank (PadicInt 2)
      (NK.Reconstruct.Dual ↥(NK.GlobalCFT.Place.localUnits K
        (NK.GlobalCFT.Place.ofFinite q)) 2) ≤
    ((q.asIdeal.ramificationIdx ℤ : Cardinal) * (q.asIdeal.inertiaDeg ℤ : Cardinal))
  calc Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual ↥(NK.GlobalCFT.Place.localUnits K
          (NK.GlobalCFT.Place.ofFinite q)) 2)
      ≤ Module.rank (PadicInt 2) (NK.Reconstruct.Dual ↥U' 2) :=
        LocalUnitsAux.rank_dual_le_of_finiteIndex U'
    _ ≤ ((q.asIdeal.ramificationIdx ℤ : Cardinal) * (q.asIdeal.inertiaDeg ℤ : Cardinal)) := by
        have := LocalUnitsAux.rank_dual_le_of_cover_subtype U' g hg hcover
        simpa [Nat.cast_mul] using this

end NK.NUV2
