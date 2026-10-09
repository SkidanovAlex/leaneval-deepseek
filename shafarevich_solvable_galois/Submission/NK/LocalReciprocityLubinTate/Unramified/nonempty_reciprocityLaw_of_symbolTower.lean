import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormCorrespondence
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocity law from a Lubin–Tate symbol tower

`NK.LocalReciprocityLubinTate.LubinTateSymbolTower` records the canonical Artin symbols of the
Lubin–Tate levels `E_{m,n}` of a tower over `F` (the unramified parameter being an arbitrary
divisibility chain `a`): a homomorphism `T.symbol m n : Fˣ →* Gal(E_{m,n}/F)` at every level,
surjective with kernel the norm group `N_{E_{m,n}/F} E_{m,n}ˣ`, compatible with restriction, and
with the levels nested (`T.mono`).

This file shows that this data — together with

* `NormInKernel`: the symbols annihilate norms at every subfield `L ≤ E_{m,n}` of a tower level,
* `NormIndex`: `[Fˣ : N_{L/F} Lˣ] = [L : F]` at every finite abelian level,
* the covering hypothesis: every finite abelian level of `F^{ab}` is contained in a tower level,

produces the reciprocity law `NK.LocalCFT.ReciprocityLaw F F'`.  The proof is the norm index
argument:

* restricting the level symbol at a tower level `E_{m,n} ⊇ L` to `L` gives a surjection
  `Fˣ ↠ Gal(L/F)` (a restriction of a surjection, `AlgEquiv.restrictNormalHom_surjective`);
* by `NormInKernel` its kernel contains `N_{L/F} Lˣ`, and both have index `[L : F]`
  (`NormIndex`, resp. surjectivity together with `Nat.card Gal(L/F) = [L : F]`), so they are equal
  and the level symbol descends to an isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`;
* the compatibility of the level symbols under restriction (`T.symbol_compat`) is inherited by the
  restrictions, after passing to a common refining tower level (`symbol_restrict_eq`); this is
  exactly the `compat` field of the reciprocity law.

## A remark on the hypotheses

The norm-subgroup correspondence `NormCorrespondence F F'` (`hcorr`) is *not* used by this
reduction: the reciprocity isomorphisms are pinned down by the norm index theorem `NormIndex`
(counting), the annihilation of norms `NormInKernel`, and the covering hypothesis.  The hypothesis
is nevertheless kept, because it is part of the interface supplied by the caller; the statement is
strictly stronger than needed.

## Implementation notes

`NK.LocalCFT.levelRestrictLe` is not directly usable at the *tower* levels, because the
`Normal` instance of a tower level is a *term* (`T.normal m n`) and not an instance; the wrapper
`restrictGalHom L E h` (`= levelRestrictLe h` by `rfl`) takes the instance arguments as variables
so that the tower levels can be named in statements.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

namespace NK.LocalReciprocityLubinTate.Unramified

open NK.LocalReciprocityLubinTate

universe u v

namespace SymbolTower

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Restriction of an `F`-automorphism of the larger level `E` to the normal sublevel `L ≤ E`.

This is definitionally `NK.LocalCFT.levelRestrictLe`, but its type does not mention the
`Normal`-instance on `E` as a type class argument, so that it can be used for the Lubin–Tate levels
`E = T.level m n`, whose normality is the term `T.normal m n`. -/
noncomputable def restrictGalHom
    (L E : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] [Normal F E] (h : L ≤ E) :
    (↥E ≃ₐ[F] ↥E) →* (↥L ≃ₐ[F] ↥L) := by
  letI : Algebra ↥L ↥E := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L ↥E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L

/-- `restrictGalHom` is literally the restriction map `NK.LocalCFT.levelRestrictLe`. -/
theorem restrictGalHom_eq_levelRestrictLe
    (L E : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] [Normal F E] (h : L ≤ E) :
    restrictGalHom L E h = NK.LocalCFT.levelRestrictLe h := rfl

/-- The value of the restricted automorphism, read in the ambient field. -/
theorem restrictGalHom_apply
    (L E : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] [Normal F E] (h : L ≤ E) (σ : ↥E ≃ₐ[F] ↥E) (y : ↥L) :
    ((restrictGalHom L E h σ) y).1 = (σ ⟨y.1, h y.2⟩).1 := by
  letI : Algebra ↥L ↥E := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L ↥E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  unfold restrictGalHom
  rw [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply]
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ ↥L y)

/-- The value of the restriction between two levels of `F^{ab}`, read in the ambient field. -/
theorem levelRestrictLe_apply_val
    {L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    [Normal F L₁] [Normal F L₂] (h : L₂ ≤ L₁) (σ : ↥L₁ ≃ₐ[F] ↥L₁) (y : ↥L₂) :
    ((NK.LocalCFT.levelRestrictLe h σ) y).1 = (σ ⟨y.1, h y.2⟩).1 := by
  rw [← restrictGalHom_eq_levelRestrictLe L₂ L₁ h]
  exact restrictGalHom_apply L₂ L₁ h σ y

/-- Restriction of Galois groups between normal levels is surjective. -/
theorem restrictGalHom_surjective
    (L E : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] [Normal F E] (h : L ≤ E) :
    Function.Surjective (restrictGalHom L E h) := by
  intro σ
  letI : Algebra ↥L ↥E := RingHom.toAlgebra (Subsemiring.inclusion h)
  haveI : IsScalarTower F ↥L ↥E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L) (E := ↥E) σ
  exact ⟨τ, hτ⟩

/-- The covering hypothesis: every finite abelian level of `F^{ab}` is contained in a Lubin–Tate
level of the tower `T`. -/
def LevelCovered {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) : Prop :=
  ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), ∃ m n : ℕ, L ≤ T.level m n

/-- The propositional content of the choice of a tower level containing `L`. -/
theorem towerIndexAux {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    ∃ p : ℕ × ℕ, L ≤ T.level p.1 p.2 := by
  obtain ⟨m, n, hmn⟩ := hcov L hcomm
  exact ⟨(m, n), hmn⟩

/-- A chosen pair of tower indices `(m, n)` with `L ≤ T.level m n`. -/
noncomputable def towerIndex {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) : ℕ × ℕ :=
  Classical.choose (towerIndexAux T hcov L hcomm)

/-- The first chosen tower index. -/
noncomputable def towerM {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) : ℕ :=
  (towerIndex T hcov L hcomm).1

/-- The second chosen tower index. -/
noncomputable def towerN {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) : ℕ :=
  (towerIndex T hcov L hcomm).2

theorem towerIndex_spec {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    L ≤ T.level (towerM T hcov L hcomm) (towerN T hcov L hcomm) :=
  Classical.choose_spec (towerIndexAux T hcov L hcomm)

/-- The compatibility of the tower symbols, transported to the field `F^{ab}`: the symbol at a
smaller level is the restriction of the symbol at a larger level. -/
theorem symbol_cast {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (x : Fˣ) (y : ↥(T.level m n)) :
    ((T.symbol m n x) y).1 = ((T.symbol M N x) ⟨y.1, T.mono hm hn y.2⟩).1 := by
  have h := T.symbol_compat hm hn x y
  exact (congrArg Subtype.val h).symm

/-- Two level symbols agree on a point lying in the intersection of the two levels. -/
theorem symbol_restrict_eq {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) {m n m' n' : ℕ} (x : Fˣ)
    (y : NK.LocalReciprocity.maxAbelianSubext F F')
    (hm : y ∈ T.level m n) (hm' : y ∈ T.level m' n') :
    ((T.symbol m n x) ⟨y, hm⟩).1 = ((T.symbol m' n' x) ⟨y, hm'⟩).1 := by
  calc ((T.symbol m n x) ⟨y, hm⟩).1
      = ((T.symbol (max m m') (max n n') x)
          ⟨y, T.mono (le_max_left m m') (le_max_left n n') hm⟩).1 :=
        symbol_cast T (le_max_left m m') (le_max_left n n') x ⟨y, hm⟩
    _ = ((T.symbol (max m m') (max n n') x)
          ⟨y, T.mono (le_max_right m m') (le_max_right n n') hm'⟩).1 :=
        congrArg (fun z => ((T.symbol (max m m') (max n n') x) z).1) (Subtype.ext rfl)
    _ = ((T.symbol m' n' x) ⟨y, hm'⟩).1 :=
        (symbol_cast T (le_max_right m m') (le_max_right n n') x ⟨y, hm'⟩).symm

/-! ### The level symbol -/

/-- The Artin symbol at the finite abelian level `L`, obtained by restricting the tower symbol at a
level `E_{m,n} ≥ L`. -/
noncomputable def levelSymbol {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    Fˣ →* (↥L ≃ₐ[F] ↥L) := by
  haveI : Normal F (T.level (towerM T hcov L hcomm) (towerN T hcov L hcomm)) :=
    T.normal _ _
  exact (restrictGalHom L _ (towerIndex_spec T hcov L hcomm)).comp
    (T.symbol (towerM T hcov L hcomm) (towerN T hcov L hcomm))

theorem levelSymbol_apply {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) (x : Fˣ) (y : ↥L) :
    ((levelSymbol T hcov L hcomm x) y).1
      = ((T.symbol (towerM T hcov L hcomm) (towerN T hcov L hcomm) x)
          ⟨y.1, (towerIndex_spec T hcov L hcomm) y.2⟩).1 := by
  haveI : Normal F (T.level (towerM T hcov L hcomm) (towerN T hcov L hcomm)) :=
    T.normal _ _
  change (((restrictGalHom L (T.level (towerM T hcov L hcomm) (towerN T hcov L hcomm))
      (towerIndex_spec T hcov L hcomm))
      (T.symbol (towerM T hcov L hcomm) (towerN T hcov L hcomm) x)) y).1
    = ((T.symbol (towerM T hcov L hcomm) (towerN T hcov L hcomm) x)
        ⟨y.1, (towerIndex_spec T hcov L hcomm) y.2⟩).1
  exact restrictGalHom_apply L _ _ _ y

theorem levelSymbol_surjective {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    Function.Surjective (levelSymbol T hcov L hcomm) := by
  haveI : Normal F (T.level (towerM T hcov L hcomm) (towerN T hcov L hcomm)) :=
    T.normal _ _
  intro g
  obtain ⟨σ, hσ⟩ := restrictGalHom_surjective L _ (towerIndex_spec T hcov L hcomm) g
  obtain ⟨x, hx⟩ := T.symbol_surjective (towerM T hcov L hcomm) (towerN T hcov L hcomm) σ
  refine ⟨x, ?_⟩
  show (restrictGalHom L _ (towerIndex_spec T hcov L hcomm))
    (T.symbol (towerM T hcov L hcomm) (towerN T hcov L hcomm) x) = g
  rw [hx, hσ]

/-- **Norms are killed by the level symbol**: the kernel of the Artin symbol at `L` contains the
norm group `N_{L/F} Lˣ`. -/
theorem normGroup_le_ker_levelSymbol {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T) {x : Fˣ}
    (hx : x ∈ NK.LocalReciprocity.normGroup F ↥L) :
    x ∈ MonoidHom.ker (levelSymbol T hcov L hcomm) := by
  rw [MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  rw [levelSymbol_apply, AlgEquiv.one_apply]
  exact congrArg (Subtype.val) (hnk (towerM T hcov L hcomm) (towerN T hcov L hcomm) L hcomm
    (towerIndex_spec T hcov L hcomm) x hx y)

/-- **The kernel of the level symbol is the norm group**: the reverse inclusion follows from the
norm index theorem, both sides having index `[L : F]`. -/
theorem ker_levelSymbol {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T)
    (hidx : NK.LocalArtin.NormIndex F F') :
    MonoidHom.ker (levelSymbol T hcov L hcomm) = NK.LocalReciprocity.normGroup F ↥L := by
  have hle : NK.LocalReciprocity.normGroup F ↥L ≤ MonoidHom.ker (levelSymbol T hcov L hcomm) :=
    fun x hx => normGroup_le_ker_levelSymbol T hcov L hcomm hnk hx
  refine le_antisymm ?_ hle
  have hker : (MonoidHom.ker (levelSymbol T hcov L hcomm)).index =
      (NK.LocalReciprocity.normGroup F ↥L).index := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (levelSymbol_surjective T hcov L hcomm),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank F ↥L, ← hidx L]
  have hpos : 0 < (NK.LocalReciprocity.normGroup F ↥L).index := by
    rw [hidx L]; exact Module.finrank_pos
  have hkerpos : 0 < (MonoidHom.ker (levelSymbol T hcov L hcomm)).index := by
    rw [hker]; exact hpos
  have hrel : (NK.LocalReciprocity.normGroup F ↥L).relIndex
      (MonoidHom.ker (levelSymbol T hcov L hcomm)) = 1 := by
    refine Nat.mul_right_cancel hkerpos ?_
    rw [one_mul, Subgroup.relIndex_mul_index hle, hker]
  exact Subgroup.relIndex_eq_one.mp hrel

/-! ### The reciprocity isomorphism at a level -/

/-- The level symbol, descended to the quotient by the norm group.  This is the inverse of the
reciprocity isomorphism at the level `L`. -/
noncomputable def levelHom {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T) :
    (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) →* (↥L ≃ₐ[F] ↥L) :=
  QuotientGroup.lift (NK.LocalReciprocity.normGroup F ↥L) (levelSymbol T hcov L hcomm)
    (fun x hx => normGroup_le_ker_levelSymbol T hcov L hcomm hnk hx)

theorem levelHom_mk {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T) (x : Fˣ) :
    levelHom T hcov L hcomm hnk (QuotientGroup.mk x) = levelSymbol T hcov L hcomm x :=
  QuotientGroup.lift_mk' _ _ x

theorem levelHom_surjective {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T) :
    Function.Surjective (levelHom T hcov L hcomm hnk) := by
  intro g
  obtain ⟨x, hx⟩ := levelSymbol_surjective T hcov L hcomm g
  exact ⟨QuotientGroup.mk x, by rw [levelHom_mk]; exact hx⟩

theorem levelHom_injective {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T)
    (hidx : NK.LocalArtin.NormIndex F F') :
    Function.Injective (levelHom T hcov L hcomm hnk) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := NK.LocalReciprocity.normGroup F ↥L) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := NK.LocalReciprocity.normGroup F ↥L) b
  rw [levelHom_mk, levelHom_mk] at hab
  have hmem : x * y⁻¹ ∈ MonoidHom.ker (levelSymbol T hcov L hcomm) := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [ker_levelSymbol T hcov L hcomm hnk hidx] at hmem
  exact (QuotientGroup.eq).mpr (by simpa [mul_comm] using inv_mem hmem)

/-- The reciprocity isomorphism at a finite abelian level, induced by the level symbol. -/
noncomputable def levelEquiv {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T)
    (hidx : NK.LocalArtin.NormIndex F F') :
    (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* (↥L ≃ₐ[F] ↥L) :=
  MulEquiv.ofBijective (levelHom T hcov L hcomm hnk)
    ⟨levelHom_injective T hcov L hcomm hnk hidx, levelHom_surjective T hcov L hcomm hnk⟩

theorem levelEquiv_mk {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ)
    (hnk : NormInKernel F F' π a q T)
    (hidx : NK.LocalArtin.NormIndex F F') (x : Fˣ) :
    levelEquiv T hcov L hcomm hnk hidx (QuotientGroup.mk x) =
      levelSymbol T hcov L hcomm x :=
  levelHom_mk T hcov L hcomm hnk x

/-- **Compatibility of the level isomorphisms**: the isomorphisms at two nested levels are
compatible with the quotient map induced by the inclusion of the norm groups. -/
theorem levelEquiv_compat {π : Fˣ} {a : ℕ → ℕ} {q : ℕ}
    (T : LubinTateSymbolTower F F' π a (higherUnits F) q) (hcov : LevelCovered T)
    (hnk : NormInKernel F F' π a q T)
    (hidx : NK.LocalArtin.NormIndex F F')
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    (h₁ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (h₂ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ) (h : L₂ ≤ L₁) (x : Fˣ) :
    NK.LocalCFT.levelRestrictLe h (levelEquiv T hcov L₁ h₁ hnk hidx (QuotientGroup.mk x)) =
      levelEquiv T hcov L₂ h₂ hnk hidx
        (QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
          (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ)
          (NK.LocalCFT.normGroup_le_of_le h) (QuotientGroup.mk x)) := by
  have hmap : QuotientGroup.map (NK.LocalReciprocity.normGroup F ↥L₁)
      (NK.LocalReciprocity.normGroup F ↥L₂) (MonoidHom.id Fˣ)
      (NK.LocalCFT.normGroup_le_of_le h) (QuotientGroup.mk x) = QuotientGroup.mk x :=
    QuotientGroup.map_mk _ _ _ _ x
  rw [hmap, levelEquiv_mk, levelEquiv_mk]
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  rw [levelRestrictLe_apply_val, levelSymbol_apply, levelSymbol_apply]
  exact symbol_restrict_eq T x y.1 _ _

end SymbolTower

theorem nonempty_reciprocityLaw_of_symbolTower {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {a : ℕ → ℕ}
    (T : NK.LocalReciprocityLubinTate.LubinTateSymbolTower F F' π a
      (NK.LocalReciprocityLubinTate.higherUnits F) (NK.LocalReciprocityLubinTate.residueCard F))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence F F')
    (hidx : NK.LocalArtin.NormIndex F F')
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel F F' π a
      (NK.LocalReciprocityLubinTate.residueCard F) T)
    (hcover : ∀ (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      [FiniteDimensional F L] [Normal F L]
      (_ : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ), ∃ m n : ℕ, L ≤ T.level m n) :
    Nonempty (NK.LocalCFT.ReciprocityLaw F F') := by
  have hcov : SymbolTower.LevelCovered T := hcover
  exact ⟨{ levelEquiv := fun L _ _ hcomm =>
              SymbolTower.levelEquiv T hcov L hcomm hnk hidx
           compat := fun L₁ L₂ _ _ _ _ h₁ h₂ h x =>
              SymbolTower.levelEquiv_compat T hcov hnk hidx L₁ L₂ h₁ h₂ h x }⟩

end NK.LocalReciprocityLubinTate.Unramified
