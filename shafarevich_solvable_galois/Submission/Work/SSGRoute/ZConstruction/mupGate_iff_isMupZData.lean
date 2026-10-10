import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.ZVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two spellings of the one-dimensional gate agree

The workspace carries the one-dimensional (`A = μ_p`) case of Schmidt--Wingberg's `z`-data in two
spellings:

* `Work.SSGRoute.MupGate (p := p) K` (`ZConstruction/ZDataReduction.lean`), stated for coefficient
  modules carrying only `AddCommGroup`, `Module (ZMod p)` and `Finite`, with the ambient hypotheses
  bundled in the structure `Work.SSGRoute.ZAmbient` (which also carries a primitive `p`-th root of
  unity `ζ ∈ K`), and with the hypotheses on the datum `y` bundled as `Work.SSGRoute.ZHyp`; and
* `Work.SSGRoute.IsMupZData p k Ω K` (`ZVocab.lean`), the form of the `ZSplit` lane, stated for
  coefficient modules carrying in addition the two `Gal(K|k)`-action instances
  `DistribMulAction (K ≃ₐ[k] K) E` and `SMulCommClass (K ≃ₐ[k] K) (ZMod p) E`, with the ambient and
  datum hypotheses unbundled, and concluding in the predicate `Work.SSGRoute.IsZData` rather than in
  `Work.SSGRoute.HasZData`.

The two predicates are *the same statement*:

* the two extra action instances do not occur in the body of `IsZData` / `HasZData` (whose six
  clauses mention only `+` on the coefficient module), and the two predicates `IsZData` and
  `HasZData` have the same body by definition (`isZData_iff_hasZData'` below);
* in the direction `MupGate → IsMupZData` the ambient hypotheses are simply repackaged, the missing
  `ζ, hζ, hζK` being exactly the data the theorem is handed;
* in the direction `IsMupZData → MupGate` the extra action instances are manufactured by the
  *trivial* action, exactly as in `Work.SSGRoute.mupGate_of_cores`.

Consequently the arithmetic content of the two gates is identical, and a consumer may pass between
the two spellings without touching the mathematics (in particular
`Work.SSGRoute.isMupZData_of_workspace` and `Work.SSGRoute.mupGate_of_cores` prove the same thing).
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- `Work.SSGRoute.IsZData` and `Work.SSGRoute.HasZData` spell out the same six clauses of
Schmidt--Wingberg's Theorem 13; `IsZData` merely carries the two (unused) `Gal(K|k)`-action
instances on the coefficient module.  (A local copy of
`Work.SSGRoute.isZData_iff_hasZData`, kept here so that this file does not depend on the
`ZSplit`/`ZMove` lane.) -/
theorem isZData_iff_hasZData' {K Λ : IntermediateField k Ω} {E : Type} [AddCommGroup E]
    [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {S : Finset (ValuationSubring Ω)} {y z : (Ω ≃ₐ[k] Ω) → E} :
    Work.SSGRoute.IsZData p K Λ S y z ↔ Work.SSGRoute.HasZData K Λ S y z :=
  ⟨fun h => h, fun h => h⟩

theorem mupGate_iff_isMupZData (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.MupGate (p := p) K ↔ Work.SSGRoute.IsMupZData p k Ω K := by
  constructor
  · -- `MupGate → IsMupZData`: repackage the ambient hypotheses (supplying `ζ, hζ, hζK`) and the
    -- datum hypotheses, then translate `HasZData` into `IsZData`.
    intro hM E instE instMod instAct instSMC instFin hdim Λ instΛf instΛg hKΛ S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf
    obtain ⟨z, hz⟩ := hM Λ S ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E hdim y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
    exact ⟨z, isZData_iff_hasZData'.mpr hz⟩
  · -- `IsMupZData → MupGate`: the two extra action instances are supplied by the trivial action,
    -- which the bodies of `IsZData` / `HasZData` do not see.
    intro hμ Λ instΛf instΛg S hAmb E instE instMod instFin hdim y hy
    obtain ⟨hKΛ, ζa, hζa, hζKa, hSfin, hSdisj, hSram⟩ := hAmb
    letI : DistribMulAction (K ≃ₐ[k] K) E :=
      { smul := fun _ x => x
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_zero := fun _ => rfl
        smul_add := fun _ _ _ => rfl }
    haveI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E := ⟨fun _ _ _ => rfl⟩
    obtain ⟨z, hz⟩ := hμ E hdim Λ hKΛ S hSfin hSdisj hSram y hy.add hy.locconst hy.hyS hy.hyT
      hy.hy0 hy.hyinf
    exact ⟨z, isZData_iff_hasZData'.mp hz⟩

end Work.SSGRoute.ZConstruction
