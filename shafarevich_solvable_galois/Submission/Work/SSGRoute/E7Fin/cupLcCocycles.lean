/-
# The `2`-cochains behind the cup pairing are locally constant cocycles

Two structural facts used by the `inv ∘ cup` construction of the local pairing (`G1`):

* the locally constant `2`-coboundaries of a coefficient module are locally constant `2`-cocycles
  (`coboundaries2_le_lcCocycles2`), the degree-`2` analogue of the proved
  `Work.SSGRoute.coboundaries_le_lcCocycles`;
* the naive cup product `evCupFun a b` of two locally constant `1`-cocycles is a locally constant
  `2`-cocycle (`evCupFun_mem_lcCocycles2`), i.e. it is a class in the local `H² = H2loc`.

With these, any `inv : Subgroup → 2-cochains → 𝔽_p` that kills the `2`-coboundaries (property
`hinv_cob` of the `G1` assembly) *factors through* the local `H²`, and the pairing
`pairOfInvH inv M H a b = inv H (evCupFun a b)` is defined on `H²(H, DualMod p T)`; this is the
formal content behind the `invQ` construction of `Submission/Work/SSGRoute/HRec/HrDefs.lean`.

The proof of `IsLocConst2On` for `d¹b` is the one of `Work.PTCore.isLocConst2On_d1c` (the witness
is the normal core of the local-constancy witness intersected with `K.fixingSubgroup`); for the cup
product no normal core is needed, because the only place the argument `u` is moved past is the
`res k K g • …` factor, so intersecting with `(res k K).ker` suffices.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.E7Fin.cupPairing
import Submission.Work.SSGRoute.evCupFun_isCocycle2On
import Submission.Work.PTCore.nform_props
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **Every locally constant `2`-coboundary on `H` is a locally constant `2`-cocycle on `H`.**
(Submodule inclusion `coboundaries2 ≤ lcCocycles2`; the cocycle identity holds for `d¹b` with no
hypotheses, and local constancy is `Work.PTCore.isLocConst2On_d1c`.) -/
theorem coboundaries2_le_lcCocycles2
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    coboundaries2 p k Ω K N H ≤ lcCocycles2 p k Ω K N H := by
  intro c hc
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨?_, ?_⟩
  · intro g hg h hh l hl
    have h1 : c h l = Work.PTCore.d1c (p := p) (K := K) N b h l := hbc h hh l hl
    have h2 : c (g * h) l = Work.PTCore.d1c (p := p) (K := K) N b (g * h) l :=
      hbc (g * h) (mul_mem hg hh) l hl
    have h3 : c g (h * l) = Work.PTCore.d1c (p := p) (K := K) N b g (h * l) :=
      hbc g hg (h * l) (mul_mem hh hl)
    have h4 : c g h = Work.PTCore.d1c (p := p) (K := K) N b g h := hbc g hg h hh
    have hcoc := Work.PTCore.d1c_isCocycle2On (p := p) (K := K) (M := N) H b g hg h hh l hl
    simpa only [h1, h2, h3, h4, Work.PTCore.d1c_apply] using hcoc
  · have hlc := Work.PTCore.isLocConst2On_d1c (p := p) (K := K) (M := N) H b hb
    obtain ⟨W, hWo, hW⟩ := hlc
    refine ⟨W, hWo, ?_⟩
    intro g hg h hh u hu v hv huH hvH
    have h1 : c (g * u) (h * v) =
        Work.PTCore.d1c (p := p) (K := K) N b (g * u) (h * v) :=
      hbc (g * u) (mul_mem hg huH) (h * v) (mul_mem hh hvH)
    have h2 : c g h = Work.PTCore.d1c (p := p) (K := K) N b g h := hbc g hg h hh
    rw [h1, h2]
    exact hW g hg h hh u hu v hv huH hvH

namespace E7Fin

variable (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **The cup product of two locally constant `1`-cocycles is a locally constant `2`-cocycle**, i.e.
an element of `lcCocycles2` with coefficients in `DualMod p T ≅ μ_p`.  The cocycle half is the proved
`evCupFun_isCocycle2On`; the local-constancy half uses the witness
`U_a ⊓ U_b ⊓ (res k K).ker` (the `ker` absorbs the `res k K g`-twist). -/
theorem evCupFun_mem_lcCocycles2
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) :
    evCupFun p k Ω K T M a b ∈ lcCocycles2 p k Ω K (DualMod p T) H := by
  obtain ⟨U1, hU1o, hU1⟩ := ha.2
  obtain ⟨U2, hU2o, hU2⟩ := hb.2
  refine ⟨?_, ?_⟩
  · exact SSGRoute.evCupFun_isCocycle2On p k Ω K T M H a b ha.1 hb.1
  · refine ⟨U1 ⊓ U2 ⊓ K.fixingSubgroup, ?_, ?_⟩
    · rw [Subgroup.coe_inf, Subgroup.coe_inf]
      exact (hU1o.inter hU2o).inter (IntermediateField.fixingSubgroup_isOpen K)
    · intro g hg h hh u hu v hv huH hvH
      have hu1 : SSGRoute.res k K u = 1 := by
        rw [← MonoidHom.mem_ker, show (SSGRoute.res k K).ker = K.fixingSubgroup from
          IntermediateField.restrictNormalHom_ker (E := K)]
        exact hu.2
      have hgu : a (g * u) = a g := hU1 g hg u hu.1.1 huH
      have hhv : b (h * v) = b h := hU2 h hh v hv.1.2 hvH
      rw [evCupFun_apply, evCupFun_apply, hgu, hhv, map_mul, hu1, mul_one]

end E7Fin

end Work.SSGRoute
