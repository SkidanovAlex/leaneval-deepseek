import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZRealV2.RealisationV2Own
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The auxiliary `z`-data from Grünwald-with-escape (the re-pointed realisation gate)

`Submission/Work/SSGRoute/ZSplit/Bridge.lean` derives the auxiliary `z`-data of Schmidt–Wingberg §4
from the realisation input `IsRealisationInput` — the Poitou–Tate degree-one realisation, which
allows an *arbitrary* auxiliary field `Λ₀ ⊇ Λ` with no unramifiedness at the prescribed set `S`, and
is therefore (as recorded in `_NOTE_STEP4_DESIGN.md` §3) very likely over-strong: the orthogonality
against the characters of `Λ₀` that ramify at `S` fails in general.

This module derives the *same* conclusion from `Work.SSGRoute.z_realisation_of_grunwald` (Z1), the
pairing-free relative Grünwald theorem with escape, which is now proved.  The realisation Z1 supplies
lives over the compositum `Λ ⊔ L₂` of the escape field `Λ` and the auxiliary field `L₂` (the paper's
`K̃`), and it carries — as `hL₂` — the hypothesis that `L₂` be unramified at the places of `S`.
Consequently the interface changes in the ways recorded in the paper's §4:

* the escape field is no longer arbitrary: it is `Λ ⊔ L₂` (`hΛL₂` below);
* the prescribed set `S` is contained in the auxiliary set `S₀` (`hSsub`), and the *new* places
  `S₀ ∖ S` are split in `Λ` (`hnew`) — the defining property of the paper's `T'`;
* `S₀` covers the ramification of `Λ` and of `L₂` (`hS₀ramΛ`, `hS₀ramL₂`), not only that of `Λ₀`.

The one-dimensional gate is taken as an explicit hypothesis `hgate` (it is
`Work.SSGRoute.IsMupZData p k Ω K` specialised to the coefficient module `ZMod p`), so that this
module does not depend on the `ZSplit`/`ZConstruction` assembly files — note that
`Submission/Work/SSGRoute/ZSplit/Assembly.lean` currently fails to compile (its
`z_data_general_of_mup_and_aux` is already declared in
`Submission/Work/SSGRoute/ZConstruction/ZDataAux.lean`), which also makes `ZSplit/Bridge.lean`
unbuildable at present. -/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The escape field of a realisation may be lowered.**  If `Λ' ≤ Λ` then every place that is
split in `Λ` is split in `Λ'` (splitting is harder for bigger fields), so the unramifiedness clause
of `IsYRealisation p K Λ …` is stronger than the one of `IsYRealisation p K Λ' …`.  (The auxiliary
set `S₀` may be changed in neither direction: its two clauses move oppositely.) -/
theorem IsYRealisation.mono_escape_v2 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ Λ' : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {yt : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f yt) (hΛ : Λ' ≤ Λ) :
    IsYRealisation p K Λ' T S₀ f yt := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6⟩
  intro B hB hBnot hns σ hσG hσI
  refine h5 B hB hBnot ?_ σ hσG hσI
  intro hsplit
  exact hns (le_trans hsplit (IntermediateField.fixingSubgroup_le hΛ))

/-- **The realisation of the auxiliary `z`-data from Grünwald-with-escape.**

This is the conclusion of `Work.SSGRoute.IsAuxiliaryZData` with the interface changes described in
the module docstring: the escape field is `Λ₀ = Λ ⊔ L₂`, the prescribed set satisfies `S ⊆ S₀`, its
new places `S₀ ∖ S` are split in `Λ`, and `S₀` covers the ramification of `Λ` and of `L₂`.

The hypothesis `hgate` is the one-dimensional case of the `z`-construction for the coefficient
module `ZMod p` at an arbitrary pair `(Λ, S)` (this is `Work.SSGRoute.IsMupZData p k Ω K`
specialised to `ZMod p`). -/
theorem isAuxiliaryZData_of_grunwald_v2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (hgate : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
        ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, IsFinPlace k A) →
      (∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B) →
      ∀ (y : (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
      IsLocConstOn K.fixingSubgroup y →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) →
      ∃ z, IsZData p K Λ S y z) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
      ∀ (Λ₀ : IntermediateField k Ω) [FiniteDimensional k Λ₀] [IsGalois k Λ₀],
      Λ ≤ Λ₀ → K ≤ Λ₀ →
      ∀ (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L], L ≤ Λ₀ →
      ∀ (S₀ : Finset (ValuationSubring Ω)),
      (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
        ∃ A ∈ S₀, IsConjPlace k A B) →
      (∀ A ∈ S₀, IsFinPlace k A) →
      (∀ A ∈ S₀, ∀ B ∈ S₀, IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B) →
      ∀ (S : Finset (ValuationSubring Ω)),
      (∀ A ∈ S, IsFinPlace k A) →
      S ⊆ S₀ →
      (∀ A ∈ S₀, A ∉ S → IsSplitIn k Λ A) →
      ∀ (L₂ : IntermediateField k Ω) [FiniteDimensional k L₂] [IsGalois k L₂],
      K ≤ L₂ → Λ ⊔ L₂ = Λ₀ →
      (∀ σ ∈ K.fixingSubgroup, σ ^ p ∈ L₂.fixingSubgroup) →
      (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
        σ * τ * σ⁻¹ * τ⁻¹ ∈ L₂.fixingSubgroup) →
      (∀ A ∈ S, ∀ σ ∈ K.fixingSubgroup, IsInertia k A σ → σ ∈ L₂.fixingSubgroup) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k Λ B →
        ∃ A ∈ S₀, IsConjPlace k A B) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L₂ B →
        ∃ A ∈ S₀, IsConjPlace k A B) →
      ∀ (ν : (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h) →
      IsLocConstOn K.fixingSubgroup ν →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
        ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ν σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0) →
      ∃ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ A : ValuationSubring Ω, (∃ A' ∈ S, IsConjPlace k A' A) → f A = ν) ∧
        ∃ yt zF, IsYRealisation p K Λ₀ S S₀ f yt ∧ IsZData p K Λ₀ S₀ yt zF := by
  intro Λ instΛf instΛg hKΛ Λ₀ instΛ₀f instΛ₀g hΛΛ₀ hKΛ₀ L instLf instLn hLΛ₀ S₀ hS₀ramL
    hS₀fin hS₀disj hS₀ramΛ₀ S hSfin hSsub hnew L₂ instL₂f instL₂g hKL₂ hΛL₂ hL₂exp hL₂comm hL₂
    hS₀ramΛ hS₀ramL₂
    ν hadd hloc hνS hνT hν0 hνinf
  -- the auxiliary set covers the ramification of `Λ` and `L₂` as well, so it covers the
  -- covering hypothesis of Grünwald with escape
  have hS₀cov : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨ IsRamifiedIn k Λ B ∨ IsRamifiedIn k L₂ B) →
      ∃ A ∈ S₀, IsConjPlace k A B := by
    intro B hB hc
    rcases hc with h | h | h
    · exact hS₀ramΛ₀ B hB (Or.inr h)
    · exact hS₀ramΛ B hB h
    · exact hS₀ramL₂ B hB h
  -- Z1: Grünwald with escape realises the datum over `Λ ⊔ L₂ = Λ₀`
  obtain ⟨yt, hyt0⟩ := z_realisation_of_grunwald_v2_own p k Ω K ζ hζ hζK hKimag Λ L₂ hKΛ hKL₂
    S S₀ hSsub hS₀fin hS₀disj hS₀cov hnew hL₂ hL₂exp hL₂comm ν
    (fun g hg h hh => hadd g hg h hh) hloc hνS hνT
  rw [hΛL₂] at hyt0
  -- a place conjugate to a place of `S` is a finite place
  have hfinplace : ∀ (A B : ValuationSubring Ω), IsFinPlace k A → IsConjPlace k A B →
      IsFinPlace k B := by
    intro A B hA hAB
    obtain ⟨σ', hσ'⟩ := hAB
    rw [← hσ']
    exact (isFinPlace_smul_iff A σ').mpr hA
  -- the prescribed datum is unramified at the places of `S`
  have hfunr : ∀ B : ValuationSubring Ω, (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → (fun _ => ν) B σ = 0 := by
    intro B hB σ hσG hσI
    obtain ⟨A, hA, hAB⟩ := hB
    exact hνT B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ σ hσG hσI
  -- and it vanishes on the local groups of the places of `S` over `p` or not split in `K`
  have hvanish : ∀ B : ValuationSubring Ω, (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → (fun _ => ν) B σ = 0 := by
    intro B hB hd σ hσG hσD
    obtain ⟨A, hA, hAB⟩ := hB
    exact hν0 B (hfinplace A B (hSfin A hA) hAB) ⟨A, hA, hAB⟩ hd σ hσG hσD
  -- hence the hypotheses of the one-dimensional statement for `yt`
  obtain ⟨hyS', hyT', hy0', hyinf'⟩ :=
    IsYRealisation.zStatementHypotheses p hyt0 hfunr hvanish
  -- `yt` is additive on `G_K`
  have hytadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, yt (g * h) = yt g + yt h := by
    intro g hg h hh
    have hres : res k K g = 1 := (res_eq_one_iff_mem_fixingSubgroup (K := K) g).mpr hg
    have hc := hyt0.1 g hg h hh
    rwa [hres, one_smul] at hc
  -- and the one-dimensional `z`-data for `yt` at the auxiliary pair
  obtain ⟨zF, hzF⟩ := hgate Λ₀ hKΛ₀ S₀ hS₀fin hS₀disj hS₀ramΛ₀ yt hytadd hyt0.2.1 hyS' hyT' hy0' hyinf'
  exact ⟨fun _ => ν, fun A hA => rfl, yt, zF, hyt0, hzF⟩

end Work.SSGRoute
