import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.ShaCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation conditions of `Z¹_loc`/`Z²_loc` as a function of the place set

The workspace's Tate–Shafarevich groups are defined by imposing the local condition — "the cocycle is
a coboundary at that place" — at **every** finite place (and at every involution, for the real
places):

`Sha1 p k Ω K M = Z¹_loc ⧸ B¹`,  `Z¹_loc = {φ : cocycle ∧ locconst ∧ ∀ A finite place, φ|D_A = 0 ∧ ∀ σ² = 1, φ|⟨σ⟩ = 0}`

(`Work.SSGRoute.ShaCocycles`), and similarly `Sha2 = Z²_loc ⧸ B²`.

Milne's Poitou–Tate duality (I.4.10(a), and its cofinite-`S` form I.4.20(a)) is stated for a *set*
`S` of places, with exactly the conditions at the places of `S`.  This file introduces the
`S`-parametrised versions `Z1locOn S`, `Z2locOn S` — the same conditions, imposed only at the finite
places lying in `S` (the involution conditions are kept, `ℚ`-independent of `S`, since they are
finitely many) — and proves the obvious identification

`Z¹_loc = Z1locOn Set.univ = ⨅ S, Z1locOn S`

(and the same in degree `2`), together with antitonicity in `S`.  This is the vocabulary in which
the *limit step* of the bridge (`PTCore/pt_pairing_limit.lean`) is applied: the `S`-duality gives
`#(Z1locOn S ⧸ B¹) = #(Z2locOn S ⧸ B²)` for each cofinite `S`, and the limit over the downward
directed family `S ↦ Z1locOn S` produces the all-places statement.

Nothing here is arithmetic: it is the place-set bookkeeping of the two localisation conditions.
-/

namespace Work.SSGRoute.PTCore

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **`Z¹_loc` with the finite-place conditions imposed only at the places of `S`.**

The cocycle condition, the local-constancy condition and the involution (`σ ^ 2 = 1`) conditions are
kept for every `S` (they involve finitely many conjugacy classes of places); the finite-place
condition `φ ∈ B¹(decomp k A)` is imposed exactly at the finite places `A ∈ S`.  With `S = Set.univ`
this is literally `Z1loc`. -/
def Z1locOn (S : Set (ValuationSubring Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {φ | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ φ ∧ SSGRoute.IsLocConstOn ⊤ φ ∧
    (∀ A : ValuationSubring Ω, A ∈ S → SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) φ) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers σ) φ)}
  zero_mem' := ⟨isCocycleOn_zero, isLocConstOn_zero, fun _ _ _ => isCoboundaryOn_zero,
    fun _ _ => isCoboundaryOn_zero⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨isCocycleOn_add hf1 hg1, isLocConstOn_add hf2 hg2,
      fun A hAS hA => isCoboundaryOn_add (hf3 A hAS hA) (hg3 A hAS hA),
      fun σ hσ => isCoboundaryOn_add (hf4 σ hσ) (hg4 σ hσ)⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3, hf4⟩
    exact ⟨isCocycleOn_smul hf1 a, isLocConstOn_smul hf2 a,
      fun A hAS hA => isCoboundaryOn_smul (hf3 A hAS hA) a,
      fun σ hσ => isCoboundaryOn_smul (hf4 σ hσ) a⟩

/-- **`Z²_loc` with the finite-place conditions imposed only at the places of `S`.**  The mirror of
`Z1locOn` in degree `2` (the involution conditions are again kept for every `S`). -/
def Z2locOn (S : Set (ValuationSubring Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | SSGRoute.IsCocycle2 (SSGRoute.res k K) c ∧ SSGRoute.IsLocConst2 c ∧
    (∀ A : ValuationSubring Ω, A ∈ S → SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c)}
  zero_mem' := ⟨isCocycle2_zero, isLocConst2_zero, fun _ _ _ => isCoboundary2On_zero,
    fun _ _ => isCoboundary2On_zero⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨isCocycle2_add hf1 hg1, isLocConst2_add hf2 hg2,
      fun A hAS hA => isCoboundary2On_add (hf3 A hAS hA) (hg3 A hAS hA),
      fun σ hσ => isCoboundary2On_add (hf4 σ hσ) (hg4 σ hσ)⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3, hf4⟩
    exact ⟨isCocycle2_smul hf1 a, isLocConst2_smul hf2 a,
      fun A hAS hA => isCoboundary2On_smul (hf3 A hAS hA) a,
      fun σ hσ => isCoboundary2On_smul (hf4 σ hσ) a⟩

/-- **`Z1locOn` is antitone in the place set**: fewer prescribed places means fewer conditions. -/
theorem Z1locOn_antitone : Antitone (Z1locOn p k Ω K M) := by
  intro S T hST φ hφ
  exact ⟨hφ.1, hφ.2.1, fun A hA hAf => hφ.2.2.1 A (hST hA) hAf, hφ.2.2.2⟩

/-- **`Z2locOn` is antitone in the place set.** -/
theorem Z2locOn_antitone : Antitone (Z2locOn p k Ω K M) := by
  intro S T hST c hc
  exact ⟨hc.1, hc.2.1, fun A hA hAf => hc.2.2.1 A (hST hA) hAf, hc.2.2.2⟩

/-- **`Z1locOn Set.univ` is `Z1loc`**: imposing the finite-place condition at every place of `univ`
is imposing it at every finite place. -/
theorem Z1locOn_univ : Z1locOn p k Ω K M Set.univ = Z1loc p k Ω K M := by
  ext φ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun A hA => h3 A trivial hA, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun A _ hA => h3 A hA, h4⟩

/-- **`Z2locOn Set.univ` is `Z2loc`.** -/
theorem Z2locOn_univ : Z2locOn p k Ω K M Set.univ = Z2loc p k Ω K M := by
  ext c
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun A hA => h3 A trivial hA, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun A _ hA => h3 A hA, h4⟩

/-- **`Z¹_loc` is the intersection of the `S`-parametrised versions over all place sets.**  Since
`Set.univ` is the largest set, `Z1locOn Set.univ` is a lower bound of the family and hence the
infimum. -/
theorem Z1loc_eq_iInf_Z1locOn :
    Z1loc p k Ω K M = ⨅ S : Set (ValuationSubring Ω), Z1locOn p k Ω K M S := by
  rw [← Z1locOn_univ p k Ω K M]
  refine le_antisymm (le_iInf fun S => Z1locOn_antitone p k Ω K M (Set.subset_univ S)) ?_
  exact iInf_le _ Set.univ

/-- **`Z²_loc` is the intersection of the `S`-parametrised versions over all place sets.** -/
theorem Z2loc_eq_iInf_Z2locOn :
    Z2loc p k Ω K M = ⨅ S : Set (ValuationSubring Ω), Z2locOn p k Ω K M S := by
  rw [← Z2locOn_univ p k Ω K M]
  refine le_antisymm (le_iInf fun S => Z2locOn_antitone p k Ω K M (Set.subset_univ S)) ?_
  exact iInf_le _ Set.univ

/-- **`Ш¹` with the local conditions imposed only at the places of `S`**: the quotient of
`Z1locOn S` by the global coboundaries, exactly as `Sha1` is the quotient of `Z1loc`.  For
`S = Set.univ` this is the workspace's `Sha1`; for a cofinite `S` it is the group appearing on the
`S`-side of Milne's duality (I.4.10(a) / I.4.20(a)). -/
abbrev Sha1On (S : Set (ValuationSubring Ω)) : Type :=
  ↥(Z1locOn p k Ω K M S) ⧸ (B1top p k Ω K M).comap (Z1locOn p k Ω K M S).subtype

/-- **`Ш²` with the local conditions imposed only at the places of `S`.** -/
abbrev Sha2On (S : Set (ValuationSubring Ω)) : Type :=
  ↥(Z2locOn p k Ω K M S) ⧸ (B2top p k Ω K M).comap (Z2locOn p k Ω K M S).subtype

/-- The global `1`-coboundaries lie in `Z1locOn S` for every `S`: a coboundary is a cocycle, is
locally constant, and is (locally) a coboundary at every place.  This is what makes the quotient
`Sha1On S` a genuine *subquotient* of `Z1top ⧸ B1top = H¹`, and hence lets the two place-set
families be compared. -/
theorem B1top_le_Z1locOn [NumberField k] [IsAlgClosure k Ω] [FiniteDimensional k K]
    [IsGalois k K] (S : Set (ValuationSubring Ω)) :
    B1top p k Ω K M ≤ Z1locOn p k Ω K M S := by
  intro φ hφ
  have hlc : φ ∈ Work.SSGRoute.lcCocycles p k Ω K M ⊤ :=
    Work.SSGRoute.coboundaries_le_lcCocycles (p := p) (k := k) (Ω := Ω) K M ⊤ hφ
  exact ⟨hlc.1, hlc.2,
    fun A _ _ => isCoboundaryOn_mono le_top hφ,
    fun σ _ => isCoboundaryOn_mono le_top hφ⟩

end Work.SSGRoute.PTCore
