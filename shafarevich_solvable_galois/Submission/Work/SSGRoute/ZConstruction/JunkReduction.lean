import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataAux
import Submission.Work.SSGRoute.ZConstruction.AuxExistsGapInduction
import Submission.Work.SSGRoute.ZConstruction.AuxExistsUnmixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Case C reduced to a purely algebraic gate: the *proper-junk variant* of the datum

`Work.SSGRoute.z_data_general_of_auxGap_and_caseC`
(`ZConstruction/AuxExistsGapInduction.lean`) leaves the node reduced to the one-dimensional gate
`MupGate`, the per-datum auxiliary gate `AuxExistsGap`, and the **Case C** gate: the `z`-data for
datata whose prescribed `cs(S)`-local data *and* whose junk ramification both span the coefficient
module.  This file shows that Case C is a consequence of a much more elementary statement, which
mentions neither transfers nor cyclicity:

> **Proper-junk variant.**  Every `ZHyp` datum `y` has a *variant* `y'` which is again a `ZHyp`
> datum, agrees with `y` on the local groups of the places conjugate into `S` (the only part of the
> datum that the node's conclusion sees, see §1 below), and whose *junk span is proper*:
> `junkSpan K Λ S y' ≠ ⊤`.

Indeed, such a variant can be fed to the Case A step of the induction
(`Work.SSGRoute.z_data_of_spanning_of_auxGap`, which needs exactly `csData K S y' = ⊤` and
`junkSpan K Λ S y' ≠ ⊤`), and the resulting witness works for `y` as well, because the node's
conclusion mentions the datum only through its values on those local groups (§1).

## 1. The conclusion depends on the datum only on the `cs(S)`-local groups

Clause 3 of `Work.SSGRoute.HasZData K Λ S y z` is the only clause mentioning `y`:
`z σ = y σ` for `σ` in the decomposition group (inside `G_K`) of a place conjugate into `S`.
Consequently `HasZData K Λ S y z` follows from `HasZData K Λ S y' z` as soon as `y` and `y'` agree
there (`hasZData_of_agrees_on_csGroups`), and `csData K S y' = csData K S y`
(`csData_congr`).  Hence the node's obligation is a statement about the *restriction of the datum to
the `cs(S)`-local groups*, i.e. about a **class of data**, and one is free to replace `y` by any
`ZHyp` variant with the same restriction.

## 2. What remains

`Work.SSGRoute.z_data_general_of_auxGap_and_junkVariant` (this file) proves the `z`-data from

* `MupGate` (the one-dimensional gate),
* `AuxExistsGap` (the per-datum auxiliary-class gate, which is *derivable* from the pairing gate and
  the Poitou--Tate-matched realisation gate),
* the **variant gate** `JunkVariantGate`: every `ZHyp` datum at every `(Λ,S)` has a proper-junk
  variant.

The variant gate is a statement about the *ramification of data* alone; the natural way to produce a
variant is to add an *admissible shift* `δ` (additive, locally constant, vanishing on the `cs(S)`-local
groups, on the involutions and on the non-`Λ`-split inertia), since such a shift preserves `ZHyp`
(`ZHyp.add`) and the restriction to the `cs(S)`-local groups; the variant gate is then the assertion
that one can choose `δ` so that the sum `y + δ` has proper junk span.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The `z`-data transports along a datum which agrees on the `cs(S)`-local groups.**  The
conclusion mentions the datum only in its third clause (`z σ = y σ` on the local groups of the
places conjugate into `S`), so it is insensitive to `y` away from those groups. -/
theorem hasZData_of_agrees_on_csGroups {K Λ : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [AddCommGroup E] {y y' : (Ω ≃ₐ[k] Ω) → E}
    {z : (Ω ≃ₐ[k] Ω) → E}
    (h : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = y σ)
    (hz : HasZData K Λ S y' z) : HasZData K Λ S y z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
  exact ⟨h1, h2,
    (fun B hB hconj σ hσK hσd => by rw [h3 B hB hconj σ hσK hσd, h B hB hconj σ hσK hσd]),
    h4, h5, h6⟩

/-- **`csData` only depends on the restriction of the datum to the `cs(S)`-local groups.** -/
theorem csData_congr {K : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] {y y' : (Ω ≃ₐ[k] Ω) → E}
    (h : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = y σ) :
    csData (p := p) K S y' = csData (p := p) K S y := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨B, hB, hconj, σ, hσK, hσd, rfl⟩
    rw [h B hB hconj σ hσK hσd]
    exact mem_csData (p := p) hB hconj hσK hσd
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨B, hB, hconj, σ, hσK, hσd, rfl⟩
    rw [← h B hB hconj σ hσK hσd]
    exact mem_csData (p := p) hB hconj hσK hσd

/-- **`ZHyp` is closed under addition**: every clause of `ZHyp` is either an additivity statement
(the crossed-cocycle condition, preserved under sums because the `G_K`-action on the coefficient
module is trivial) or of the form "the value at a specific `σ` is `0`". -/
theorem ZHyp.sum {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] {y₁ y₂ : (Ω ≃ₐ[k] Ω) → E}
    (h₁ : ZHyp (p := p) K Λ S y₁) (h₂ : ZHyp (p := p) K Λ S y₂) :
    ZHyp (p := p) K Λ S (fun σ => y₁ σ + y₂ σ) where
  add g hg h hh := by rw [h₁.add g hg h hh, h₂.add g hg h hh]; abel
  locconst := by
    obtain ⟨U₁, hU₁o, hU₁⟩ := h₁.locconst
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂.locconst
    refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
    · simpa using hU₁o.inter hU₂o
    · intro g hg u hu huK
      show y₁ (g * u) + y₂ (g * u) = y₁ g + y₂ g
      rw [hU₁ g hg u hu.1 huK, hU₂ g hg u hu.2 huK]
  hyS B hB hnot hsp σ hσ hσI := by
    rw [h₁.hyS B hB hnot hsp σ hσ hσI, h₂.hyS B hB hnot hsp σ hσ hσI, add_zero]
  hyT B hB hconj σ hσ hσI := by
    rw [h₁.hyT B hB hconj σ hσ hσI, h₂.hyT B hB hconj σ hσ hσI, add_zero]
  hy0 B hB hconj hcase σ hσ hσd := by
    rw [h₁.hy0 B hB hconj hcase σ hσ hσd, h₂.hy0 B hB hconj hcase σ hσ hσd, add_zero]
  hyinf c hc h2 := by rw [h₁.hyinf c hc h2, h₂.hyinf c hc h2, add_zero]

/-- **The proper-junk variant gate** at `(Λ,S)`: every `ZHyp` datum has a `ZHyp` variant, agreeing
with it on the `cs(S)`-local groups, whose junk span is proper.

By §1 the node's conclusion is insensitive to the datum outside those local groups, so this is a
statement about the *ramification of data* alone; by §2 it discharges Case C. -/
def JunkVariantGate (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] (y : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  ∃ y' : (Ω ≃ₐ[k] Ω) → E,
    ZHyp (p := p) K Λ S y' ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = y σ) ∧
    ZConstruction.junkSpan K Λ S y' ≠ ⊤

/-- **The proper-junk variant gate from an admissible shift with proper junk span.**  If `δ` is a
`ZHyp` datum whose sum with `y` has proper junk span and which vanishes on the `cs(S)`-local groups,
then `y + δ` is a proper-junk variant of `y`. -/
theorem junkVariantGate_of_add {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] {y δ : (Ω ≃ₐ[k] Ω) → E}
    (hδ : ZHyp (p := p) K Λ S δ) (hy : ZHyp (p := p) K Λ S y)
    (hvan : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → δ σ = 0)
    (hjun : ZConstruction.junkSpan K Λ S (fun σ => y σ + δ σ) ≠ ⊤) :
    JunkVariantGate (p := p) K Λ S y :=
  ⟨fun σ => y σ + δ σ, ZHyp.sum hy hδ,
    (fun B hB hconj σ hσK hσd => by
      show y σ + δ σ = y σ
      rw [hvan B hB hconj σ hσK hσd, add_zero]), hjun⟩

/-- **The `z`-data from the one-dimensional gate, the per-datum auxiliary-class gate and the
proper-junk variant gate.**

This is `Work.SSGRoute.z_data_general_of_auxGap_and_caseC` with the Case C gate replaced by
`JunkVariantGate`: in the Case C branch (`csData K S y = ⊤` and `junkSpan K Λ S y = ⊤`) the variant
`y'` of the datum is fed to the Case A step and the resulting witness is transported back to `y`. -/
theorem z_data_general_of_auxGap_and_junkVariant {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hmup : MupGate (p := p) K)
    (haux : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
      ZConstruction.AuxExistsGap (p := p) K Λ S)
    (hvar : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → JunkVariantGate (p := p) K Λ S y) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb
  have key : ∀ (m : ℕ), ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E],
      Module.finrank (ZMod p) E = m → ∀ (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro E _instE _instM _instF hfin y hy
      by_cases hdim : Module.finrank (ZMod p) E ≤ 1
      · exact hmup Λ S hAmb E hdim y hy
      · push_neg at hdim
        by_cases hsp : csData (p := p) K S y = ⊤
        · by_cases hjun : ZConstruction.junkSpan K Λ S y = ⊤
          · -- Case C: replace the datum by its proper-junk variant
            obtain ⟨y', hy'hyp, hy'agree, hy'jun⟩ := hvar Λ S hAmb E y hy
            have hsp' : csData (p := p) K S y' = ⊤ := by
              rw [csData_congr (p := p) hy'agree]; exact hsp
            obtain ⟨z', hz'⟩ :=
              z_data_of_spanning_of_auxGap (p := p) (K := K) (Λ := Λ) (S := S) (E := E)
                hAmb hmup (haux Λ S hAmb.hSfin)
                (fun E' _ _ _ hlt y'' hy'' =>
                  ih (Module.finrank (ZMod p) E') (by rw [← hfin]; exact hlt) E' rfl y'' hy'')
                y' hy'hyp hsp' hdim hy'jun
            exact ⟨z', hasZData_of_agrees_on_csGroups hy'agree hz'⟩
          · -- Case A
            refine z_data_of_spanning_of_auxGap hAmb hmup (haux Λ S hAmb.hSfin) ?_ y hy hsp hdim hjun
            intro E' _ _ _ hlt y' hy'
            exact ih (Module.finrank (ZMod p) E') (by rw [← hfin]; exact hlt) E' rfl y' hy'
        · -- Case B: the peeling step
          haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
          obtain ⟨C, hc⟩ := Submodule.exists_isCompl (csData (p := p) K S y)
          have hlt : Module.finrank (ZMod p) ↥(csData (p := p) K S y) <
              Module.finrank (ZMod p) E := Submodule.finrank_lt hsp
          have hltm : Module.finrank (ZMod p) ↥(csData (p := p) K S y) < m := by
            rw [← hfin]; exact hlt
          have hy' : ZHyp (p := p) K Λ S
              (fun σ => (csData (p := p) K S y).projectionOnto C hc (y σ)) :=
            ZHyp.mapAdd (f := ((csData (p := p) K S y).projectionOnto C hc).toAddMonoidHom) hy
          obtain ⟨z', hz'⟩ := ih _ hltm ↥(csData (p := p) K S y) rfl _ hy'
          have hmap := hasZData_map (A := ↥(csData (p := p) K S y)) (B := E)
            (f := (Submodule.subtype (csData (p := p) K S y)).toAddMonoidHom)
            (fun _ _ h => Subtype.ext h) hz'
          refine ⟨fun σ => (z' σ : E), hasZData_of_fixes_data
            (π := (Submodule.subtype (csData (p := p) K S y)).comp
              ((csData (p := p) K S y).projectionOnto C hc)) ?_ hmap⟩
          intro B hB hconj σ hσK hσd
          have hmem : y σ ∈ csData (p := p) K S y := mem_csData (p := p) (K := K) hB hconj hσK hσd
          show ((Submodule.subtype (csData (p := p) K S y)).comp
            ((csData (p := p) K S y).projectionOnto C hc)) (y σ) = y σ
          rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left _ hmem]
          rfl
  intro E _instE _instM _instF y hy
  exact key (Module.finrank (ZMod p) E) E rfl y hy

end Work.SSGRoute
