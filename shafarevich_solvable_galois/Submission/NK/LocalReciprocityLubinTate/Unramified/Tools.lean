import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTLevel_commutative
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_sup_higherUnits
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.Unramified.exists_unramified_level_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Tools for the assembly of the Lubin–Tate tower

This file collects the technical lemmas that the *assembly* of the Lubin–Tate tower
(`NK.LocalReciprocityLubinTate.Unramified.TowerAssembly`) consumes:

1. `exists_intermediateField_algEquiv_of_isSepClosed` — a finite Galois level of a fixed algebraic
   closure of `F` can be realised, up to `F`-isomorphism, inside *any* separably closed extension
   `F'`.  This is how the levels `K_n = F(Λ_n)` — naturally constructed inside
   `AlgebraicClosure F` — are transported into the separable closure `F'` of the boundary theorem.
2. `restrictLevel` and its API — a finite normal level `L ≤ F'` contained in `F^{ab}` is viewed as a
   level of `F^{ab}` itself (`IntermediateField F (maxAbelianSubext F F')`), with the same norm
   group, and with the Galois-theoretic properties transported along the canonical
   `F`-isomorphism.
3. `inf_sup_zpowers_pow_eq` — the arithmetic identity

   `(⟨π^{m+1}⟩ · U⁰) ⊓ (⟨π⟩ · U^{n+1}) = ⟨π^{m+1}⟩ · U^{n+1}`

   for a uniformiser `π` and the higher unit filtration `U`, i.e. the intersection formula for the
   norm groups of the unramified and the Lubin–Tate level.
4. `exists_irreducible_natCast_of_isUniformizer` — a uniformiser of `F` is (the image of) an
   irreducible element of the ring of integers `𝒪[F]`, so that the degree and commutativity
   theorems about `LTLevel` (which are stated for an irreducible element of `𝒪[F]`) apply to it.
5. `finrank_LTLevel_eq_of_isUniformizer` — the degree `[F(Λ_n) : F] = (q-1) q^{n-1}` for a
   uniformiser given as a unit of `F`.

## Conventions

`U^n = higherUnits F n = 1 + 𝔪[F]^n ≤ Fˣ` is the higher unit filtration of `Basic.lean`, and
`higherUnits F 0 = 𝒪[F]ˣ` is the group of units of the ring of integers.
-/

open scoped ValuativeRel

set_option linter.unusedVariables false

namespace NK.LocalReciprocityLubinTate.Unramified

universe u v

noncomputable section

/-! ## 1. Realising a finite Galois level inside a separably closed extension -/

/-- **A finite Galois level of `AlgebraicClosure F` embeds into any separably closed extension of
`F`, and the inverse image of the image is a level with the same norm group.**

The embedding is `IsSepClosed.lift`, available because `↥L/F` is finite and separable. -/
theorem exists_intermediateField_algEquiv_of_isSepClosed {F : Type u} [Field F]
    {F' : Type v} [Field F'] [Algebra F F'] [IsSepClosed F']
    (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    [Algebra.IsSeparable F ↥L] :
    ∃ L' : IntermediateField F F', Nonempty (↥L ≃ₐ[F] ↥L') := by
  refine ⟨IntermediateField.map (IsSepClosed.lift (K := F) (L := ↥L) (M := F')) ⊤,
    ⟨(IntermediateField.topEquiv (F := F) (E := ↥L)).symm.trans
      (IntermediateField.equivMap (F := F) (E := ↥L) (K := F') ⊤
        (IsSepClosed.lift (K := F) (L := ↥L) (M := F')))⟩⟩

/-! ## 2. Levels of `F'` contained in `F^{ab}`, as levels of `F^{ab}` -/

section Restrict

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']

/-- **A finite normal level of `F'` contained in `F^{ab}`, viewed as a level of `F^{ab}`.**  For a
subextension `L ≤ F'` with `L ≤ F^{ab} = maxAbelianSubext F F'`, this is `L` regarded as an
intermediate field of `F^{ab}`; it is the pullback of `L` along `F^{ab} ↪ F'`. -/
def restrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') :
    IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F') :=
  L.comap (NK.LocalReciprocity.maxAbelianSubext F F').val

theorem mem_restrictLevel {L : IntermediateField F F'}
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F')
    {x : NK.LocalReciprocity.maxAbelianSubext F F'} :
    x ∈ restrictLevel L hL ↔ (x : F') ∈ L := Iff.rfl

/-- **The canonical `F`-isomorphism `L ≃ₐ[F] F^{ab} ⊇ L`** for a level `L ≤ F^{ab}`. -/
def restrictLevelEquiv (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') :
    ↥L ≃ₐ[F] ↥(restrictLevel L hL) where
  toFun x := ⟨⟨(x : F'), hL x.2⟩, x.2⟩
  invFun y := ⟨(y : F'), y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)
  map_mul' x y := Subtype.ext (Subtype.ext rfl)
  map_add' x y := Subtype.ext (Subtype.ext rfl)
  commutes' c := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem restrictLevelEquiv_apply_coe (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') (x : ↥L) :
    ((restrictLevelEquiv L hL x : ↥(restrictLevel L hL)) :
      NK.LocalReciprocity.maxAbelianSubext F F') = (x : F') := rfl

/-- **The norm group is unchanged** by restricting a level of `F^{ab}` to `F^{ab}`. -/
theorem normGroup_restrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') :
    NK.LocalReciprocity.normGroup F ↥(restrictLevel L hL) =
      NK.LocalReciprocity.normGroup F ↥L :=
  (NK.LocalReciprocity.normGroup_eq_of_algEquiv (restrictLevelEquiv L hL)).symm

instance instFiniteDimensionalRestrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') [FiniteDimensional F ↥L] :
    FiniteDimensional F ↥(restrictLevel L hL) :=
  FiniteDimensional.of_surjective (restrictLevelEquiv L hL).toLinearMap
    (restrictLevelEquiv L hL).surjective

instance instNormalRestrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') [Normal F ↥L] :
    Normal F ↥(restrictLevel L hL) :=
  Normal.of_algEquiv (restrictLevelEquiv L hL)

instance instIsGaloisRestrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F') [IsGalois F ↥L] :
    IsGalois F ↥(restrictLevel L hL) :=
  IsGalois.of_algEquiv (restrictLevelEquiv L hL)

/-- Commutativity of the Galois group transfers to the restricted level. -/
theorem commutative_restrictLevel (L : IntermediateField F F')
    (hL : L ≤ NK.LocalReciprocity.maxAbelianSubext F F')
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    ∀ σ τ : ↥(restrictLevel L hL) ≃ₐ[F] ↥(restrictLevel L hL), σ * τ = τ * σ := by
  intro σ τ
  apply (AlgEquiv.autCongr (restrictLevelEquiv L hL).symm).injective
  rw [map_mul, map_mul]
  exact hcomm _ _

end Restrict

/-! ## 3. The arithmetic identity for the norm groups of a compositum -/

section Units

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem higherUnits_zero (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    NK.LocalReciprocityLubinTate.higherUnits F 0 =
      (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range := by
  rw [NK.LocalReciprocityLubinTate.higherUnits, NK.LocalReciprocityLubinTate.principalUnits_zero,
    NK.LocalReciprocityLubinTate.Units.unitsIncl, MonoidHom.range_eq_map]

/-- **The arithmetic identity** `(⟨π^{m+1}⟩ · U⁰) ⊓ (⟨π⟩ · U^{n+1}) = ⟨π^{m+1}⟩ · U^{n+1}`.

This is the intersection formula for the norm groups of the unramified level of degree `m+1`
(`⟨π^{m+1}⟩ · U⁰`) and the `(n+1)`-st Lubin–Tate level (`⟨π⟩ · U^{n+1}`). -/
theorem inf_sup_zpowers_pow_eq (π : Fˣ) (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F))
    (m n : ℕ) :
    (Subgroup.zpowers (π ^ (m + 1)) ⊔ NK.LocalReciprocityLubinTate.higherUnits F 0)
        ⊓ (Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F (n + 1))
      = Subgroup.zpowers (π ^ (m + 1)) ⊔
          NK.LocalReciprocityLubinTate.higherUnits F (n + 1) := by
  set A : Subgroup Fˣ := Subgroup.zpowers (π ^ (m + 1)) with hA
  set Z : Subgroup Fˣ := Subgroup.zpowers π with hZ
  set D : Subgroup Fˣ := NK.LocalReciprocityLubinTate.higherUnits F 0 with hD
  set B : Subgroup Fˣ := NK.LocalReciprocityLubinTate.higherUnits F (n + 1) with hB
  have hAZ : A ≤ Z :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), by rw [zpow_natCast]⟩)
  have hBD : B ≤ D :=
    NK.LocalReciprocityLubinTate.higherUnits_antitone F (Nat.zero_le (n + 1))
  have hDinf : Z ⊓ D = ⊥ := by
    rw [hZ, hD, higherUnits_zero]
    exact NK.LocalReciprocityLubinTate.Units.inf_zpowers_range F π hπ
  refine le_antisymm ?_
    (le_inf (sup_le le_sup_left (hBD.trans le_sup_right))
      (sup_le (hAZ.trans le_sup_left) le_sup_right))
  rintro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [Subgroup.mem_sup] at hy2
  obtain ⟨a, ha, b, hb, hab⟩ := hy2
  rw [Subgroup.mem_sup] at hy1
  obtain ⟨c, hc, d, hd, hcd⟩ := hy1
  rw [Subgroup.mem_zpowers_iff] at ha hc
  obtain ⟨j, hj⟩ := ha
  obtain ⟨k, hk⟩ := hc
  have hbD : b ∈ (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range := by
    rw [← higherUnits_zero F]
    exact hBD hb
  have hdD : d ∈ (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range := by
    rw [← higherUnits_zero F]
    exact hd
  have hb'' : b = a⁻¹ * y := by rw [← hab]; group
  have hb' : b = (π ^ j)⁻¹ * y := by rw [hb'', ← hj]
  have hd'' : d = c⁻¹ * y := by rw [← hcd]; group
  have hd' : d = (π ^ (((m + 1 : ℕ) : ℤ) * k))⁻¹ * y := by rw [hd'', ← hk, ← zpow_natCast, ← zpow_mul]
  have hmem : π ^ (j - ((m + 1 : ℕ) : ℤ) * k) ∈ Z ⊓ D := by
    constructor
    · exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩
    · rw [hD, higherUnits_zero]
      have hkey : π ^ (j - ((m + 1 : ℕ) : ℤ) * k) = d * b⁻¹ := by
        have hL : π ^ (j - ((m + 1 : ℕ) : ℤ) * k)
            = π ^ j * (π ^ (((m + 1 : ℕ) : ℤ) * k))⁻¹ := by
          rw [sub_eq_add_neg, zpow_add, ← zpow_neg]
        rw [hL, hb', hd', mul_inv_rev, inv_inv]
        group
      rw [hkey]
      exact Subgroup.mul_mem _ hdD (Subgroup.inv_mem _ hbD)
  rw [hDinf] at hmem
  have hone : π ^ (j - ((m + 1 : ℕ) : ℤ) * k) = 1 := Subgroup.mem_bot.mp hmem
  have hjk : j = ((m + 1 : ℕ) : ℤ) * k := by
    have h1 : (NK.LocalReciprocityLubinTate.Units.valUnits F π) ^
        (j - ((m + 1 : ℕ) : ℤ) * k) = 1 := by
      rw [← map_zpow, hone, map_one]
    have h2 := (NK.LocalReciprocityLubinTate.Units.zpow_valUnits_pi_eq_one_iff F π hπ
      (j - ((m + 1 : ℕ) : ℤ) * k)).mp h1
    linarith
  have ha' : a = (π ^ (m + 1)) ^ k := by
    rw [← hj, hjk, zpow_mul, zpow_natCast]
  refine Subgroup.mem_sup.mpr ⟨(π ^ (m + 1)) ^ k, ?_, b, hb, ?_⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  · rw [← hab, ha']

end Units

/-! ## 4. A uniformiser is an irreducible element of the ring of integers -/

section Irreducible

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **A uniformiser of `F` is (the coerced image of) an irreducible element of `𝒪[F]`.**

`Valuation.IsUniformizer.val_lt_one` makes `π` integral, and
`Valuation.IsUniformizer.is_generator` says that the integral element generates the maximal ideal;
in the discrete valuation ring `𝒪[F]` this is equivalent to irreducibility. -/
theorem exists_irreducible_natCast_of_isUniformizer (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F)) :
    ∃ P : ↥(ValuativeRel.valuation F).integer, Irreducible P ∧ (P : F) = (π : F) := by
  let P : ↥(ValuativeRel.valuation F).integer :=
    ⟨(π : F), le_of_lt (Valuation.IsUniformizer.val_lt_one hπ)⟩
  have hgen : IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer = Ideal.span {P} :=
    Valuation.IsUniformizer.is_generator (v := ValuativeRel.valuation F) hπ
  exact ⟨P, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal P
    (fun h => Valuation.IsUniformizer.ne_zero hπ (Subtype.ext_iff.mp h)) hgen, rfl⟩

/-! ## 5. The classical Lubin–Tate theorems for a uniformiser given as a unit of `F` -/

section LTLevels

variable (F : Type u) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The degree of the Lubin–Tate level**, for a uniformiser given as a unit of `F`:
`[F(Λ_n) : F] = (q - 1) q^{n-1}` for `n ≥ 1` and `q = residueCard F`. -/
theorem finrank_LTLevel_eq_of_isUniformizer (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F)) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank F ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n)
      = (NK.LocalReciprocityLubinTate.residueCard F - 1)
        * NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) := by
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F π hπ
  rw [← hPcoe]
  exact NK.LocalReciprocityLubinTate.finrank_LTLevel_eq (F := F) P hPirr n hn

/-- **The Lubin–Tate level is an abelian extension**, for a uniformiser given as a unit of `F`. -/
theorem LTLevel_commutative_of_isUniformizer (π : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F)) (n : ℕ) (hn : 1 ≤ n) :
    ∀ σ τ : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
      ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n), σ * τ = τ * σ := by
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F π hπ
  rw [← hPcoe]
  exact NK.LocalReciprocityLubinTate.LubinTate.LTLevel_commutative (F := F) P hPirr n hn

end LTLevels
