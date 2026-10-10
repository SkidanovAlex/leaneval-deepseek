import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

/-- **E9's exactness leg: the exact segment of the class formation, with `E1`'s witness as the
interface.**

The design (`DESIGN_PT.md` E9, §3's assembly; `DESIGN_EXT.md` §2-3; `DESIGN_FIX2.md` §2-3) derives the
middle exactness of the Poitou–Tate sequence from the long exact sequence of `Ext_G(E', ·)` on the
class formation `0 → Kˣ → 𝕀_K → C_K → 0` (`sesK`), composed with the two bridges `E1`
(`H¹(k,E) ≅ Ext¹_G(E',Kˣ)`) and `E2` (idèle Shapiro).  This statement is the *formal* exactness half,
in the vocabulary of `SSGRoute.PTDefs`, with the *witness* `β` of `E1` — together with its three
clauses — taken as an interface rather than re-derived.  Only the *surjectivity* clause is used in the
proof; the other two are carried so that a caller holding `ext_h1_bridge`'s witness can plug it in
verbatim.

The three conjuncts are the three exactness statements of the segment

`H¹(k,E) --β--> Ext¹_G(E',Kˣ) --extToIdeles--> Ext¹_G(E',𝕀_K) --extToClasses--> Ext¹_G(E',C_K)
  --extDelta--> Ext²_G(E',Kˣ) --extToIdeles--> Ext²_G(E',𝕀_K)`:

* (i) **exactness at `Ext¹_G(E', 𝕀_K)`** — a class of `Ext¹_G(E',𝕀_K)` is killed by the class map
  `𝕀_K → C_K` iff it is the idèle-image `extToIdeles (β b)` of a class coming from `H¹(k,E)`:
  `ker(extToClasses) = range(extToIdeles ∘ β)`.  Reading local components with `extLoc` (and using
  E2's clause (i), which makes the description of a class by its localisations faithful) this *is*
  `im(H¹(k,E) → P¹(E)) = ker(P¹(E) → Ext¹_G(E',C_K))`, the first equality of the design's assembly
  bullet 2, and hence the input of the middle exactness `im(loc) = ann(loc)` that the counting
  identity `Work.SSGRoute.PT.pt_counting_identity_h1` consumes.
* (ii) **exactness at `Ext¹_G(E', C_K)`**: `extDelta y = 0 ↔ ∃ z, extToClasses z = y`.
* (iii) **exactness at `Ext²_G(E', Kˣ)`**: `(∃ z, extDelta z = y) ↔ extToIdeles y = 0`.

*Level-freeness.*  Note that the statement has no `∀ L ⊇ K` clause with fixed local data: `β` is a
map on *level-free* cochains `G_k → E`, and the three exactness statements concern the single level
`K`.  This is deliberate — the level-uniform shape is exactly the defect that
`PT/localTatePairing_deg02.lean` documents and that made the filed `E8` node unrepairable.

*Proof route — the three conjuncts are verbatim Mathlib.*  With `hS : sesK.ShortExact` (from
`NK.HassePrinciple.ideleShortComplex_shortExact k K`) and `X := modRep (K ≃ₐ[k] K)
(DualMod p (E ⊗[ZMod p] T))`, the primed exactness lemmas of `Mathlib.CategoryTheory.Abelian.Ext`
(derived from `covariant_sequence_exact₂'` / `_exact₃'` / `_exact₁'`) apply directly, because
`extToIdeles = ·.comp (mk₀ S.f)`, `extToClasses = ·.comp (mk₀ S.g)` and `extDelta = ·.comp hS.extClass`:
* (i) `covariant_sequence_exact₂' X hS 1` gives `ker extToClasses = range extToIdeles`; then
  `hβ_surj` upgrades `range extToIdeles` to `range (extToIdeles ∘ β)`.  The easy inclusion
  (`extToClasses (extToIdeles y) = 0`, needed for the `←` direction) is
  `ShortComplex.ShortExact.comp_extClass` + `S.f ≫ S.g = 0` (hand-proved form:
  `Work.SSGRoute.PTExt.extToClasses_extToIdeles`, `PT/pt_pairing_ext.lean`).
* (ii) `covariant_sequence_exact₃' X hS 1 2` (note `hS.extClass.postcomp` *is* `extDelta`, so there
  is no sign gap).
* (iii) `covariant_sequence_exact₁' X hS 1 2`.

Do **not** add `Sha2Lib/pt_core_assembly` or `PTdualControl/extExact` to the imports: Mathlib alone
suffices, and those lanes are being edited (one of them currently fails to build).

*Why this node is worth having.*  It converts the design's "exact segment" into a single citable
statement in the `PTDefs` vocabulary with the `E1` interface pinned, i.e. it is the input of the
middle-exactness step for the counting identity, and it fixes the degrees (`1`, `2`) and the
directions (`extToIdeles`, `extToClasses`, `extDelta`) once and for all. -/
theorem pt_extSegment_exact
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (β : ((Ω ≃ₐ[k] Ω) → E) →
        Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
          (unitsK k K) 1)
    (hβ_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
        β (b + b') = β b + β b')
    (hβ_ker : ∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b))
    (hβ_surj : ∀ y : Abelian.Ext (modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 1,
        ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
          SSGRoute.IsLocConstOn ⊤ b ∧ β b = y) :
    (∀ y : Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
        (idelesK k K) 1,
        extToClasses y = 0 ↔
          ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
            SSGRoute.IsLocConstOn ⊤ b ∧ extToIdeles (β b) = y) ∧
    (∀ y : Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
        (classesK k K) 1,
        extDelta y = 0 ↔
          ∃ z : Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
            (idelesK k K) 1, extToClasses z = y) ∧
    (∀ y : Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
        (unitsK k K) 2,
        (∃ z : Abelian.Ext (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)))
            (classesK k K) 1, extDelta z = y) ↔
          extToIdeles y = 0) := by
  have hS : (sesK k K).ShortExact := NK.HassePrinciple.ideleShortComplex_shortExact k K
  let X := modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
  refine ⟨?_, ?_, ?_⟩
  · -- (i) exactness at `Ext¹_G(E', 𝕀_K)`
    intro y
    have hex := Abelian.Ext.covariant_sequence_exact₂' X hS 1
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    have hiff : extToClasses y = 0 ↔
        ∃ x : Abelian.Ext.{0} X (unitsK k K) 1, extToIdeles x = y := by
      exact hex y
    rw [hiff]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨b, hbc, hbl, hb⟩ := hβ_surj x
      exact ⟨b, hbc, hbl, by rw [hb, hx]⟩
    · rintro ⟨b, -, -, hb⟩
      exact ⟨β b, hb⟩
  · -- (ii) exactness at `Ext¹_G(E', C_K)`
    intro y
    have hex := Abelian.Ext.covariant_sequence_exact₃' X hS 1 2 (by norm_num)
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    have hiff : extDelta y = 0 ↔
        ∃ z : Abelian.Ext.{0} X (idelesK k K) 1, extToClasses z = y := by
      exact hex y
    exact hiff
  · -- (iii) exactness at `Ext²_G(E', Kˣ)`
    intro y
    have hex := Abelian.Ext.covariant_sequence_exact₁' X hS 1 2 (by norm_num)
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    have hiff : extToIdeles y = 0 ↔
        ∃ z : Abelian.Ext.{0} X (classesK k K) 1, extDelta z = y := by
      exact hex y
    exact hiff.symm

end Work.SSGRoute.PT
