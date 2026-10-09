import Mathlib
import Submission.NK.NUV2.LC.normGroupDeterminesLevel
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.Work.HilbertSymbolGeneral.canonicalAPI
import Submission.Work.HilbertSymbolGeneral.hilbertSymbol_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity (the projector formula) of the `p = 2` Hilbert symbol

For a tower of fields `F ⊆ E ⊆ F'` with `F'` a separable closure of `F` and of `E`, the Hilbert
symbol of the `p = 2` local chapter satisfies the *projector (transitivity) formula*

  `(x, a)_E = (N_{E/F} x, a)_F`     (`x ∈ Eˣ`, `a ∈ Fˣ`).

This is the local input of Schmidt–Wingberg's p. 16 computation (the `p = 2` "dichotomy"): the
product of the local symbols over the primes dividing the anti-invariant element `X = z - σz`
collapses because `N_{K_P/L_𝔭}(X) = -X²` turns `(X, a)_{K_P}` into `(-1, a)_{L_𝔭} = 1`.

## Mathematical content

Both sides are `Multiplicative (ZMod 2)`-valued, so it suffices to identify the "`= 1`" sets.  By
the norm criterion (`hilbertSymbol_eq_one_iff_normGroup`) these are the norm groups

  `A_E = N_{E(√a)/E} E(√a)ˣ ≤ Eˣ`,   `A_F = N_{F(√a)/F} F(√a)ˣ ≤ Fˣ`.

* `A_E ⊆ N_{E/F}^{-1} A_F`: **norm transitivity** (`normGroup_trans`, `normGroup_le_of_tower`);
  norms from `E(√a)` to `F` factor through `F(√a)` because `F ⊆ F(√a) ⊆ E(√a)`.
* `N_{E/F}^{-1} A_F ⊆ A_E`: the **index count**.  `A_E` has index `[E(√a) : E] ≤ 2` in `Eˣ`
  (norm index theorem at the level `E`, from `R'`), and `N_{E/F}^{-1} A_F` has index
  `[N : N ∩ A_F] ≤ [Fˣ : A_F] = [F(√a) : F] ≤ 2` (norm index theorem at `F`, from `R`).  Two
  subgroups of index `≤ 2`, one inside the other, coincide unless the larger one is everything;
  the remaining case `N_{E/F} Eˣ ⊆ A_F` forces `N_{E/F} Eˣ = A_F` (indices `[Fˣ : N] = [E : F]`
  and `[Fˣ : A_F] ≤ 2`), and then `normGroup_injective R` identifies the levels `E` and `F(√a)`,
  so that `a` is a square in `E` and `A_E = Eˣ` — the contradiction.

The bottom field `E` of the tower is presented as the level `E₀ ≤ F^ab` that it is
(`E = NK.LocalReciprocity.levelMap E₀`), so that the norm index theorem and the injectivity of
`L ↦ N_{L/F} Lˣ` apply to it without transport.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped Classical

namespace Work.SSGRoute.ZConstruction

open NK.LocalArtin

section LevelSub

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

/-- A level of `F^{ab}` (an intermediate field of `maxAbelianSubext F F'`) viewed as a subfield of
`F'`. -/
abbrev levelSub (E₀ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')) :
    IntermediateField F F' :=
  NK.LocalReciprocity.levelMap E₀

end LevelSub

section GroupIndex

variable {G H : Type*} [Group G] [Group H]

/-- The index of the preimage of a subgroup under a homomorphism is at most the index of the
subgroup (the index of a finite-index subgroup can only decrease under pull-back along the induced
injection of quotients). -/
theorem Subgroup.index_comap_le (φ : G →* H) (A : Subgroup H) (hA : A.index ≠ 0) :
    (A.comap φ).index ≤ A.index := by
  rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right A]
  exact Subgroup.relIndex_le_of_le_right (H := A) (K := φ.range) (L := ⊤) le_top
    (by rwa [Subgroup.relIndex_top_right])

/-- Two subgroups, one contained in the other, with the same finite index, are equal. -/
theorem Subgroup.eq_of_le_of_index_eq {A B : Subgroup G} (hAB : A ≤ B) (hB : B.index ≠ 0)
    (h : A.index = B.index) : A = B := by
  refine le_antisymm hAB ?_
  rw [← Subgroup.relIndex_eq_one]
  have hmul := Subgroup.relIndex_mul_index hAB
  rw [h] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hB) (by rw [hmul, one_mul])

end GroupIndex

section Main

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F'] [NeZero (2 : F)]

variable (E₀ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
variable [FiniteDimensional F E₀] [Normal F E₀]

variable [NeZero (2 : ↥(levelSub E₀))] [IsSepClosure ↥(levelSub E₀) F']

/-- **Key inclusion**: a norm from `E(√a)` down to `E` is, after `N_{E/F}`, a norm from `F(√a)`
down to `F` — the transitivity of the norm group across the tower `F ⊆ F(√a) ⊆ E(√a)`. -/
theorem normGroup_quadLevel_le_comap (R : ReciprocityMap F F')
    (y : F') (a : Fˣ) (hyF : y * y = algebraMap F F' (a : F))
    (b : ↥(levelSub E₀)) (hb : b = algebraMap F ↥(levelSub E₀) (a : F))
    (hyE : y * y = algebraMap ↥(levelSub E₀) F' b) :
    NK.LocalReciprocity.normGroup ↥(levelSub E₀) ↥(NK.NUV2.LC.quadLevel y b hyE) ≤
      (NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF)).comap
        (Units.map (Algebra.norm F : ↥(levelSub E₀) →* F)) := by
  set L₂ : IntermediateField ↥(levelSub E₀) F' :=
    NK.LocalReciprocity.levelMap (NK.NUV2.LC.quadLevel y b hyE) with hL₂
  set L₁ : IntermediateField F F' :=
    NK.LocalReciprocity.levelMap (NK.NUV2.LC.quadLevel y (a : F) hyF) with hL₁
  -- the element `y` lies in the `E`-side level
  have hyL₂ : y ∈ (L₂ : Set F') := by
    refine NK.LocalReciprocity.mem_levelMap.mpr
      ⟨NK.NUV2.LC.quadRoot y b hyE, ?_⟩
    rw [NK.LocalReciprocity.levelIncl_apply, NK.NUV2.LC.quadRoot_coe]
  -- the `F`-side level is contained in the `E`-side level
  have hle : L₁ ≤ L₂.restrictScalars F := by
    intro x hx
    rw [hL₁, NK.LocalReciprocity.levelMap] at hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hquad : NK.NUV2.LC.quadLevel y (a : F) hyF ≤
        (L₂.restrictScalars F).comap
          (IntermediateField.val (NK.LocalReciprocity.maxAbelianSubext F F')) := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hyL₂
    exact hquad hz
  -- the algebra structures of the tower `F ⊆ ↥L₁ ⊆ ↥L₂`
  letI : Algebra ↥L₁ ↥L₂ := (RingHom.toAlgebra
    { toFun := fun x => ⟨(x : F'), hle x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl })
  letI : Algebra F ↥L₂ := ((algebraMap ↥L₁ ↥L₂).comp (algebraMap F ↥L₁)).toAlgebra
  haveI : IsScalarTower F ↥L₁ ↥L₂ :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI : IsScalarTower F ↥(levelSub E₀) ↥L₂ :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  have hL₂norm : NK.LocalReciprocity.normGroup ↥(levelSub E₀)
      ↥(NK.NUV2.LC.quadLevel y b hyE) = NK.LocalReciprocity.normGroup ↥(levelSub E₀) ↥L₂ := by
    rw [hL₂]
    exact NK.LocalReciprocity.normGroup_levelMap _
  have hL₁norm : NK.LocalReciprocity.normGroup F
      ↥(NK.NUV2.LC.quadLevel y (a : F) hyF) = NK.LocalReciprocity.normGroup F ↥L₁ := by
    rw [hL₁]
    exact NK.LocalReciprocity.normGroup_levelMap _
  intro x hx
  rw [Subgroup.mem_comap]
  have hx' : x ∈ NK.LocalReciprocity.normGroup ↥(levelSub E₀) ↥L₂ := by
    rw [← hL₂norm]
    exact hx
  have hmap : (Units.map (Algebra.norm F : ↥(levelSub E₀) →* F)) x ∈
      NK.LocalReciprocity.normGroup F ↥L₂ := by
    rw [NK.LocalReciprocity.normGroup_trans (F := F) (E := ↥(levelSub E₀)) (M := ↥L₂)]
    exact ⟨x, hx', rfl⟩
  have hle₂ : NK.LocalReciprocity.normGroup F ↥L₂ ≤ NK.LocalReciprocity.normGroup F ↥L₁ :=
    NK.LocalReciprocity.normGroup_le_of_tower (F := F) (E := ↥L₁) (M := ↥L₂)
  rw [hL₁norm]
  exact hle₂ hmap

/-- **The index of `A_E` is `[E(√a) : E]`** (the norm index theorem at the level `E`). -/
theorem index_normGroup_quadLevel_E (R' : ReciprocityMap ↥(levelSub E₀) F')
    (y : F') (b : ↥(levelSub E₀))
    (hyE : y * y = algebraMap ↥(levelSub E₀) F' b) :
    (NK.LocalReciprocity.normGroup ↥(levelSub E₀) ↥(NK.NUV2.LC.quadLevel y b hyE)).index =
      Module.finrank ↥(levelSub E₀) ↥(NK.NUV2.LC.quadLevel y b hyE) := by
  haveI := NK.NUV2.LC.quadLevel_finiteDimensional (F := ↥(levelSub E₀)) (F' := F') y b hyE
  haveI := NK.NUV2.LC.quadLevel_normal (F := ↥(levelSub E₀)) (F' := F') y b hyE
  exact NK.NUV2.LC.index_normGroup_eq_finrank R' (NK.NUV2.LC.quadLevel y b hyE)

/-- **The index of `A_F` is `[F(√a) : F]`** (the norm index theorem at `F`). -/
theorem index_normGroup_quadLevel_F (R : ReciprocityMap F F')
    (y : F') (a : Fˣ) (hyF : y * y = algebraMap F F' (a : F)) :
    (NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF)).index =
      Module.finrank F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF) := by
  haveI := NK.NUV2.LC.quadLevel_finiteDimensional (F := F) (F' := F') y (a : F) hyF
  haveI := NK.NUV2.LC.quadLevel_normal (F := F) (F' := F') y (a : F) hyF
  exact NK.NUV2.LC.index_normGroup_eq_finrank R (NK.NUV2.LC.quadLevel y (a : F) hyF)

/-- **The index of `N_{E/F} Eˣ` is `[E : F]`** (the norm index theorem at the level `E₀`). -/
theorem index_normGroup_level (R : ReciprocityMap F F') :
    (NK.LocalReciprocity.normGroup F ↥(levelSub E₀)).index = Module.finrank F ↥E₀ := by
  rw [← NK.LocalReciprocity.normGroup_levelMap E₀]
  exact NK.NUV2.LC.index_normGroup_eq_finrank R E₀

/-- **The degenerate case**: if every norm from `E` is a norm from `F(√a)`, then `a` is a square in
`E`.  (The two norm groups are those of the levels `E/F` and `F(√a)/F` of `F^{ab}`; if
`N_{E/F} Eˣ ≤ N_{F(√a)/F} F(√a)ˣ` then `E = E ⊔ F(√a)` by `normGroup_injective`, so
`F(√a) ≤ E`.) -/
theorem isSquare_of_normGroup_le (R : ReciprocityMap F F')
    (y : F') (a : Fˣ) (hyF : y * y = algebraMap F F' (a : F))
    (h : NK.LocalReciprocity.normGroup F ↥(levelSub E₀) ≤
      NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF)) :
    ∃ c : ↥(levelSub E₀), c * c = algebraMap F ↥(levelSub E₀) (a : F) := by
  haveI := NK.NUV2.LC.quadLevel_finiteDimensional (F := F) (F' := F') y (a : F) hyF
  haveI := NK.NUV2.LC.quadLevel_normal (F := F) (F' := F') y (a : F) hyF
  have h' : NK.LocalReciprocity.normGroup F ↥E₀ ≤
      NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF) := by
    rw [NK.LocalReciprocity.normGroup_levelMap E₀]
    exact h
  -- the maximal abelian subextension comparison
  have hsup : E₀ ⊔ NK.NUV2.LC.quadLevel y (a : F) hyF = E₀ := by
    refine NK.NUV2.LC.normGroup_injective R _ _ ?_
    rw [NK.NUV2.LC.normGroup_eq_comap_fixingSubgroup R
        (E₀ ⊔ NK.NUV2.LC.quadLevel y (a : F) hyF),
      IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf,
      ← NK.NUV2.LC.normGroup_eq_comap_fixingSubgroup R E₀,
      ← NK.NUV2.LC.normGroup_eq_comap_fixingSubgroup R
        (NK.NUV2.LC.quadLevel y (a : F) hyF)]
    exact inf_eq_left.mpr h'
  have hQle : NK.NUV2.LC.quadLevel y (a : F) hyF ≤ E₀ := sup_eq_left.mp hsup
  -- `y` lies in the level `E = levelMap E₀`
  have hyQ : y ∈ (NK.LocalReciprocity.levelMap (NK.NUV2.LC.quadLevel y (a : F) hyF) : Set F') := by
    refine NK.LocalReciprocity.mem_levelMap.mpr ⟨NK.NUV2.LC.quadRoot y (a : F) hyF, ?_⟩
    rw [NK.LocalReciprocity.levelIncl_apply, NK.NUV2.LC.quadRoot_coe]
  have hyE : y ∈ (levelSub E₀ : Set F') := NK.LocalReciprocity.levelMap_mono hQle hyQ
  refine ⟨⟨y, hyE⟩, ?_⟩
  exact Subtype.ext hyF

/-- **The value of the "`= 1`" predicates agree for one and the same square root `y` of `a`:**

  `(X, a)_E = 1 ↔ (N_{E/F} X, a)_F = 1`. -/
theorem hilbertSymbol_eq_one_iff_of_level (R : ReciprocityMap F F')
    (R' : ReciprocityMap ↥(levelSub E₀) F')
    (X : (↥(levelSub E₀))ˣ) (a : Fˣ)
    (y : F') (hyF : y * y = algebraMap F F' (a : F))
    (hyE : y * y = algebraMap ↥(levelSub E₀) F'
      (algebraMap F ↥(levelSub E₀) (a : F))) :
    NK.NUV2.LC.hilbertSymbol R' X (Units.map (algebraMap F ↥(levelSub E₀)) a) = 1 ↔
      NK.NUV2.LC.hilbertSymbol R (Units.map (Algebra.norm F) X) a = 1 := by
  haveI hfd := NK.NUV2.LC.quadLevel_finiteDimensional (F := ↥(levelSub E₀)) (F' := F') y
    (algebraMap F ↥(levelSub E₀) (a : F)) hyE
  haveI hnr := NK.NUV2.LC.quadLevel_normal (F := ↥(levelSub E₀)) (F' := F') y
    (algebraMap F ↥(levelSub E₀) (a : F)) hyE
  haveI hfdF := NK.NUV2.LC.quadLevel_finiteDimensional (F := F) (F' := F') y (a : F) hyF
  haveI hnrF := NK.NUV2.LC.quadLevel_normal (F := F) (F' := F') y (a : F) hyF
  -- unfold both symbols at the common square root `y`
  have hL : NK.NUV2.LC.hilbertSymbol R' X (Units.map (algebraMap F ↥(levelSub E₀)) a) =
      NK.NUV2.LC.hilbertSymbolAt R' y (algebraMap F ↥(levelSub E₀) (a : F)) hyE X := by
    rw [NK.NUV2.LC.hilbertSymbol]
    exact NK.NUV2.LC.hilbertSymbolAt_independent R' (NK.NUV2.LC.sqroot_mul_self _) hyE X
  have hR : NK.NUV2.LC.hilbertSymbol R (Units.map (Algebra.norm F) X) a =
      NK.NUV2.LC.hilbertSymbolAt R y (a : F) hyF (Units.map (Algebra.norm F) X) := by
    rw [NK.NUV2.LC.hilbertSymbol]
    exact NK.NUV2.LC.hilbertSymbolAt_independent R (NK.NUV2.LC.sqroot_mul_self _) hyF _
  rw [hL, hR, NK.NUV2.LC.hilbertSymbolAt_eq_one_iff, NK.NUV2.LC.hilbertSymbolAt_eq_one_iff]
  -- the two norm groups
  set AE : Subgroup (↥(levelSub E₀))ˣ :=
    NK.LocalReciprocity.normGroup ↥(levelSub E₀)
      ↥(NK.NUV2.LC.quadLevel y (algebraMap F ↥(levelSub E₀) (a : F)) hyE) with hAE
  set AF : Subgroup Fˣ :=
    NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF) with hAF
  set Φ : (↥(levelSub E₀))ˣ →* Fˣ :=
    Units.map (Algebra.norm F : ↥(levelSub E₀) →* F) with hΦ
  have hAE_le : AE ≤ AF.comap Φ := by
    rw [hAE, hAF, hΦ]
    exact normGroup_quadLevel_le_comap (E₀ := E₀) R y a hyF _ rfl hyE
  have hAEindex : AE.index = Module.finrank ↥(levelSub E₀)
      ↥(NK.NUV2.LC.quadLevel y (algebraMap F ↥(levelSub E₀) (a : F)) hyE) := by
    rw [hAE]
    exact index_normGroup_quadLevel_E (E₀ := E₀) R' y _ hyE
  have hAEle2 : AE.index ≤ 2 := by
    rw [hAEindex]
    exact NK.NUV2.LC.quadLevel_finrank_le_two _ _ _
  have hAEpos : 0 < AE.index := by
    rw [hAEindex]
    exact Module.finrank_pos
  have hAFindex : AF.index = Module.finrank F ↥(NK.NUV2.LC.quadLevel y (a : F) hyF) := by
    rw [hAF]
    exact index_normGroup_quadLevel_F R y a hyF
  have hAFne : AF.index ≠ 0 := by
    rw [hAFindex]
    exact ne_of_gt Module.finrank_pos
  have hBEle : (AF.comap Φ).index ≤ AF.index := Subgroup.index_comap_le Φ AF hAFne
  have hBEle2 : (AF.comap Φ).index ≤ 2 :=
    le_trans hBEle (le_trans (le_of_eq hAFindex) (NK.NUV2.LC.quadLevel_finrank_le_two _ _ _))
  have hBEne : (AF.comap Φ).index ≠ 0 := by
    intro h0
    have hdvd := Subgroup.index_dvd_of_le hAE_le
    rw [h0] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    simp only [zero_mul] at hk
    omega
  constructor
  · intro hx
    exact Subgroup.mem_comap.mp (hAE_le hx)
  · intro hx
    by_cases hBE1 : (AF.comap Φ).index ≤ 1
    · -- every norm from `E` is a norm from `F(√a)`: `a` is a square in `E`, so `AE = ⊤`
      have hBEtop : AF.comap Φ = ⊤ := by
        rw [← Subgroup.index_eq_one]
        omega
      have hbad : NK.LocalReciprocity.normGroup F ↥(levelSub E₀) ≤ AF := by
        intro x hx'
        rw [NK.LocalReciprocity.normGroup_eq_range] at hx'
        obtain ⟨x', rfl⟩ := hx'
        exact Subgroup.mem_comap.mp (hBEtop ▸ Subgroup.mem_top x')
      obtain ⟨c, hc⟩ := isSquare_of_normGroup_le (E₀ := E₀) R y a hyF hbad
      have hbot : NK.NUV2.LC.quadLevel y (algebraMap F ↥(levelSub E₀) (a : F)) hyE = ⊥ :=
        NK.NUV2.LC.quadLevel_eq_bot_of_isSquare y _ hyE ⟨c, hc⟩
      have hAEtop : AE = ⊤ := by
        rw [hAE, hbot]
        exact Work.HilbertSymbolGeneral.normGroup_bot_eq_top
      rw [hAEtop]
      exact Subgroup.mem_top X
    · have hBE2 : (AF.comap Φ).index = 2 := by omega
      by_cases hAE2 : AE.index = 2
      · have hEq : AE = AF.comap Φ :=
          Subgroup.eq_of_le_of_index_eq hAE_le (by omega) (by omega)
        rw [hEq]
        exact hx
      · have hAEtop : AE = ⊤ := by
          rw [← Subgroup.index_eq_one]
          omega
        rw [hAEtop]
        exact Subgroup.mem_top X

/-- **The projector (transitivity) formula for the `p = 2` Hilbert symbol**: for a finite abelian
level `E/F` of `F^{ab}` and `x ∈ Eˣ`, `a ∈ Fˣ`,

  `(x, a)_E = (N_{E/F} x, a)_F`. -/
theorem hilbertSymbol_transitivity
    (R : ReciprocityMap F F') (R' : ReciprocityMap ↥(levelSub E₀) F')
    (X : (↥(levelSub E₀))ˣ) (a : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R' X
        (Units.map (algebraMap F ↥(levelSub E₀)) a) =
      NK.NUV2.LC.hilbertSymbol R (Units.map (Algebra.norm F) X) a := by
  refine Work.HilbertSymbolGeneral.eq_of_eq_one_iff_eq_one ?_
  exact hilbertSymbol_eq_one_iff_of_level (E₀ := E₀) R R' X a
    (NK.NUV2.LC.sqroot (F := F) (F' := F') a)
    (NK.NUV2.LC.sqroot_mul_self (F := F) (F' := F') a)
    (by
      rw [← IsScalarTower.algebraMap_apply F ↥(levelSub E₀) F' (a : F)]
      exact NK.NUV2.LC.sqroot_mul_self (F := F) (F' := F') a)

end Main

section Quadratic

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F'] [NeZero (2 : F)]

/-- **The projector (transitivity) formula in the quadratic case**, the form in which the p. 16
dichotomy consumes it: for `E = F(√d) ⊆ F'` (`δ² = d`) and `x ∈ Eˣ`, `a ∈ Fˣ`,

  `(x, a)_E = (N_{E/F} x, a)_F`.

*Instantiation at a local extension `K_P/L_𝔭`.*  Present `K_P` as `L_𝔭(√d)` inside a common
separable closure `F'` of `L_𝔭`: pick a non-square `d : L_𝔭` with `K_P ≅ L_𝔭(√d)` (`K_P/L_𝔭` is
quadratic), a square root `δ : F'` of `d` — then `E := ↥(levelSub (quadLevel δ d hδ))` is `L_𝔭(√d)`
as a subfield of `F'` and `NK.LocalReciprocity.levelEquiv` gives the `L_𝔭`-algebra isomorphism with
`K_P` along which the two sides are transported.  The hypothesis `IsSepClosure ↥(levelSub (quadLevel
δ d hδ)) F'` says that `F'` is a separable closure of the quadratic field as well — immediate from
`L_𝔭 ⊆ K_P ⊆ F'` and the separability of `K_P/L_𝔭`. -/
theorem hilbertSymbol_transitivity_quadratic
    (δ : F') (d : F) (hδ : δ * δ = algebraMap F F' d)
    [FiniteDimensional F ↥(NK.NUV2.LC.quadLevel δ d hδ)]
    [Normal F ↥(NK.NUV2.LC.quadLevel δ d hδ)]
    [NeZero (2 : ↥(levelSub (NK.NUV2.LC.quadLevel δ d hδ)))]
    [IsSepClosure ↥(levelSub (NK.NUV2.LC.quadLevel δ d hδ)) F']
    (R : ReciprocityMap F F')
    (R' : ReciprocityMap ↥(levelSub (NK.NUV2.LC.quadLevel δ d hδ)) F')
    (X : (↥(levelSub (NK.NUV2.LC.quadLevel δ d hδ)))ˣ) (a : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R' X
        (Units.map (algebraMap F ↥(levelSub (NK.NUV2.LC.quadLevel δ d hδ))) a) =
      NK.NUV2.LC.hilbertSymbol R (Units.map (Algebra.norm F) X) a :=
  hilbertSymbol_transitivity (E₀ := NK.NUV2.LC.quadLevel δ d hδ) R R' X a

end Quadratic

end Work.SSGRoute.ZConstruction
