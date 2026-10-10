import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_quotient_zpowers_pow_sup_higherUnits_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the `l`-th power class group of a nonarchimedean local field

`NK.LocalAnabelian.KummerGroup l F = Fˣ ⧸ (Fˣ)^l` is the `l`-Kummer class group of a field `F`.
For a nonarchimedean local field of characteristic zero it is finite: this is the arithmetic input
of Kummer theory for local fields (the source of the finiteness of the Kummer dual of the Galois
group), and it is proved here from the Lubin–Tate chapter of the workspace.

## The argument

Let `l` be prime and `F` a nonarchimedean local field of characteristic zero, with ring of
integers `𝒪[F]`, maximal ideal `𝔪[F]`, residue cardinality `q = #𝓀[F]` and a uniformiser `π`.

1. **A higher unit group lies in the `l`-th powers.**  Newton's method for the `l`-th power map on
   `1 + 𝔪[F]` (`NK.LocalReciprocityLubinTate.Units.exists_pow_eq_of_mem_maximalIdeal_pow`) produces
   `n` such that every `y ∈ 𝔪[F]^n` is `(1+x)^l - 1` with `x ∈ 𝔪[F]`; hence every `1 + y ∈ U^n` is
   an `l`-th power:  `higherUnits F n ≤ (Fˣ)^l`.
2. **The Lubin–Tate quotient is finite of known order.**  For a uniformiser `π`,
   `NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen` computes
   `Nat.card (Fˣ ⧸ (⟨π^l⟩ ⊔ U^n)) = l · (q - 1) · q^{n-1}`; as `l ≠ 0` and `q ≥ 2` the right hand
   side is nonzero, so the quotient is finite.
3. **Conclusion.**  Both `⟨π^l⟩` and `U^n` lie in `(Fˣ)^l`, so the quotient map
   `Fˣ ⧸ (⟨π^l⟩ ⊔ U^n)  ⟶  Fˣ ⧸ (Fˣ)^l` (`QuotientGroup.map`) is surjective, and `Finite` descends
   along a surjection.

## Main result

* `Work.SSGRoute.finite_powClass_localField`
-/

open scoped ValuativeRel

set_option linter.style.haveILetI false

namespace Work.SSGRoute

universe u

/-- **Existence of a uniformiser, as a unit.**  The ring of integers `𝒪[F]` of a nonarchimedean
local field is a discrete valuation ring, so it has an irreducible element `ϖ`
(`IsDiscreteValuationRing.exists_irreducible`); its maximal ideal is then `(ϖ)`
(`Irreducible.maximalIdeal_eq`), which makes `ϖ` a uniformiser of `F`
(`Valuation.isUniformizer_of_maximalIdeal_eq_span`).  Being a uniformiser it is nonzero, so it is a
unit of `F`. -/
lemma exists_uniformizer_unit (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    ∃ π : Fˣ, NK.LocalReciprocityLubinTate.IsUniformizer F (π : F) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(ValuativeRel.valuation F).integer
  have hspan : IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer = Ideal.span {ϖ} :=
    Irreducible.maximalIdeal_eq hϖ
  have hπ₀ : Valuation.IsUniformizer (ValuativeRel.valuation F) (ϖ : F) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span (ValuativeRel.valuation F) hspan
  exact ⟨Units.mk0 (ϖ : F) (Valuation.IsUniformizer.ne_zero hπ₀), hπ₀⟩

/-- **The residue cardinality of a nonarchimedean local field is at least `2`.**  The residue field
`𝓀[F]` is finite (because `F` is a local field) and a field, hence nontrivial. -/
lemma two_le_residueCard (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F := by
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  rw [NK.LocalReciprocityLubinTate.residueCard, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **The `l`-th power class group of a non-archimedean local field of characteristic zero is
finite.**  `KummerGroup l F = Fˣ ⧸ (Fˣ)^l`.

Suggested route (all ingredients are in the workspace):
* `NK.LocalReciprocityLubinTate.Units.exists_pow_eq_of_mem_maximalIdeal_pow F l hl.one_le` gives
  `n` with `𝓂[F]^n` inside the image of the `l`-th power map on `𝓞[F]`, i.e. `higherUnits F n ≤ (Fˣ)^l`
  (every `y ∈ 𝔪^n` is `(1+x)^l - 1` with `x ∈ 𝔪`, so `1+y = (1+x)^l` is an `l`-th power);
* `NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen F π hπ l n _ _`
  (for a uniformiser `π`, obtainable from `ValuativeRel.IsNontrivial.exists_lt_one` and
  `ValuativeRel.valuation_surjective`) computes
  `Nat.card (Fˣ ⧸ (Subgroup.zpowers (π ^ l) ⊔ higherUnits F n)) = l * (residueCard F - 1) * residueCard F ^ (n-1)`;
* `Subgroup.zpowers (π^l) ≤ (Fˣ)^l` and `higherUnits F n ≤ (Fˣ)^l`, so `Fˣ ⧸ (Fˣ)^l` is a quotient of
  the finite group `Fˣ ⧸ (Subgroup.zpowers (π^l) ⊔ higherUnits F n)`; conclude by
  `Finite.of_surjective` along `QuotientGroup.map`.
(Bump `n` to `n+1` with `higherUnits_antitone` if `n = 0`.) -/
theorem finite_powClass_localField (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (l : ℕ) (hl : l.Prime) :
    Finite (NK.LocalAnabelian.KummerGroup l F) := by
  classical
  have hl1 : 1 ≤ l := hl.one_le
  -- Step 1: some higher unit group is contained in the `l`-th powers.
  obtain ⟨n, hn⟩ :=
    NK.LocalReciprocityLubinTate.Units.exists_pow_eq_of_mem_maximalIdeal_pow F l hl1
  have hUn₀ : NK.LocalReciprocityLubinTate.higherUnits F n ≤
      NK.LocalAnabelian.powSubgroup l F := by
    intro u hu
    rw [NK.LocalReciprocityLubinTate.higherUnits, Subgroup.mem_map] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff] at hv
    obtain ⟨x, hx, hxpow⟩ := hn ((v : ↥𝒪[F]) - 1) hv
    have hxunit : IsUnit (1 + x : ↥𝒪[F]) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h1 : (1 : ↥𝒪[F]) ∈ 𝓂[F] := by
        have hsub : (1 + x) - x = 1 := by ring
        rw [← hsub]
        exact sub_mem hmem hx
      exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[F]).ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
    let w : (↥𝒪[F])ˣ := hxunit.unit
    have hw : w ^ l = v := by
      apply Units.ext
      show ((w ^ l : (↥𝒪[F])ˣ) : ↥𝒪[F]) = (v : ↥𝒪[F])
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec hxunit]
      convert hxpow using 2
      ring
    rw [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range]
    refine ⟨NK.LocalReciprocityLubinTate.Units.unitsIncl F w, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hw]
    exact hvu
  -- Step 2: the Lubin–Tate quotient `Fˣ ⧸ (⟨π^l⟩ · U^{n+1})` is finite.
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit F
  let A : Subgroup Fˣ :=
    Subgroup.zpowers (π ^ l) ⊔ NK.LocalReciprocityLubinTate.higherUnits F (n + 1)
  let B : Subgroup Fˣ := NK.LocalAnabelian.powSubgroup l F
  have hUn : NK.LocalReciprocityLubinTate.higherUnits F (n + 1) ≤ B :=
    le_trans (NK.LocalReciprocityLubinTate.higherUnits_antitone F (Nat.le_succ n)) hUn₀
  have hmem : π ^ l ∈ B := by
    change π ^ l ∈ NK.LocalAnabelian.powSubgroup l F
    rw [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range]
    exact ⟨π, by rw [powMonoidHom_apply]⟩
  have hzp : Subgroup.zpowers (π ^ l) ≤ B := Subgroup.zpowers_le.mpr hmem
  have hAB : A ≤ B := sup_le hzp hUn
  have hcard : Nat.card (Fˣ ⧸ A) =
      l * (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (n + 1 - 1) :=
    NK.LocalReciprocityLubinTate.natCard_quotient_zpowers_pow_sup_higherUnits_gen F π hπ l
      (n + 1) hl1 (by omega)
  have hne : Nat.card (Fˣ ⧸ A) ≠ 0 := by
    rw [hcard]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero hl.ne_zero (by have := two_le_residueCard F; omega))
      (pow_ne_zero _ (by have := two_le_residueCard F; omega))
  haveI : Finite (Fˣ ⧸ A) := Nat.finite_of_card_ne_zero hne
  -- Step 3: descend finiteness along the surjection `Fˣ ⧸ A → Fˣ ⧸ (Fˣ)^l`.
  have hfin : A ≤ Subgroup.comap (MonoidHom.id Fˣ) B := by
    rw [Subgroup.comap_id]
    exact hAB
  have hsurj : Function.Surjective (QuotientGroup.map A B (MonoidHom.id Fˣ) hfin) :=
    QuotientGroup.map_surjective_of_surjective A B (MonoidHom.id Fˣ)
      (QuotientGroup.mk'_surjective B) hfin
  exact Finite.of_surjective (QuotientGroup.map A B (MonoidHom.id Fˣ) hfin) hsurj

end Work.SSGRoute
