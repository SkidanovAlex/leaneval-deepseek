import Mathlib
import Submission.Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `↥(asFieldL D g)` is Galois over the twist field `↥(asTwistFieldTrue D g τ σS)`

The twisted Artin–Schreier action `σ' = asTwistAction D τ σS` preserves `L(E) = asFieldL D g`
(`ASTwistData.hpres`) and satisfies `σ'⁵ = 1` there (`ASTwistData.h5L`), while being nontrivial
(`ASTwistData.hneL`).  Hence its restriction `A'` to `↥L(E)` is a ring automorphism of order `5`.

By Artin's theorem (`IsGalois.of_fixed_field`) the extension `↥L(E) / ↥(FixedPoints A')` is Galois,
where `FixedPoints A'` is the fixed subfield of the cyclic group `⟨A'⟩` inside `↥L(E)`.  The
colleague lemma `Work.MotV5.RigAS.fixedField_subfield_restrict_eq` identifies this fixed subfield
with the restriction to `↥L(E)` of `asTwistFieldTrue D g τ σS = L(E)^{⟨σ'⟩}`, i.e. with the
subfield of `↥L(E)` consisting of the elements lying in `asTwistFieldTrue D g τ σS`.  The identity
on the ambient field `K̄(E)` is therefore a ring isomorphism from that fixed subfield onto
`↥(asTwistFieldTrue D g τ σS)`, and `IsGalois.of_equiv_equiv` transports the Galois property along
this isomorphism and along the (definitional) identity `↥L(E) ≃+* ↥(extendScalars _)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.MotV5.RigAS.GaloisTrue

open IntermediateField

theorem galois (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    IsGalois ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      ↥(IntermediateField.extendScalars (Work.MotV5.asTwistFieldTrue_le_asFieldL D g τ σS)) := by
  classical
  -- `L = asFieldL D g` and `T = asTwistFieldTrue D g τ σS`, with `T ≤ L`
  let L : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) := Work.MotV5.asFieldL D g
  let T : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) := Work.MotV5.asTwistFieldTrue D g τ σS
  have hTL : T ≤ L := inf_le_right
  -- the twisted action and its restriction to `L`
  let A : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D := Work.MotV5.asTwistAction D τ σS
  have hpres : ∀ x ∈ L, A x ∈ L := h.hpres
  have h5 : ∀ x ∈ L, (A ^ 5) x = x := h.h5L
  let A' : ↥L ≃+* ↥L := Work.MotV5.RigAS.restrictRingEquiv L A hpres h5
  have hA'5 : A' ^ 5 = 1 := Work.MotV5.RigAS.restrictRingEquiv_pow_five_eq_one L A hpres h5
  haveI hfin : Finite ↥(Subgroup.zpowers A') :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hA'5⟩)
  -- the fixed field of `⟨A'⟩` inside `↥L` agrees with `↥T` (as subfields of `↥L`)
  let S : Subfield ↥L := FixedPoints.subfield (Subgroup.zpowers A') ↥L
  have hS_eq : S = (IntermediateField.restrict (F := T) (E := L) hTL).toSubfield :=
    Work.MotV5.RigAS.fixedField_subfield_restrict_eq L A hpres h5
  -- Artin: `↥L` is Galois over the fixed field `↥S`
  haveI hGal : IsGalois ↥S ↥L := IsGalois.of_fixed_field ↥L ↥(Subgroup.zpowers A')
  -- the identity on the ambient field identifies `↥S` with `↥T`
  have hS_mem : ∀ x : ↥L, x ∈ S ↔ (x : Work.MotV.Om D) ∈ T := by
    intro x
    rw [hS_eq]
    exact IntermediateField.mem_restrict hTL x
  have hmem : ∀ s : ↥S, (s.1 : Work.MotV.Om D) ∈ T := fun s => (hS_mem s.1).mp s.2
  let fHom : ↥S →+* ↥T :=
    { toFun := fun s => ⟨(s.1 : Work.MotV.Om D), hmem s⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hinj : Function.Injective fHom := by
    intro a b hab
    have h1 : (a : ↥L) = (b : ↥L) :=
      Subtype.ext (congrArg (fun y : ↥T => (y : Work.MotV.Om D)) hab)
    exact Subtype.ext h1
  have hsurj : Function.Surjective fHom := by
    intro y
    have hyL : (y : Work.MotV.Om D) ∈ L := hTL y.2
    refine ⟨⟨⟨(y : Work.MotV.Om D), hyL⟩, ?_⟩, ?_⟩
    · exact (hS_mem ⟨(y : Work.MotV.Om D), hyL⟩).mpr y.2
    · rfl
  let f : ↥S ≃+* ↥T := RingEquiv.ofBijective fHom ⟨hinj, hsurj⟩
  -- the (definitional) identity `↥L ≃+* ↥(extendScalars hTL)`
  let LE : IntermediateField ↥T (Work.MotV.Om D) := IntermediateField.extendScalars hTL
  let gg : ↥L ≃+* ↥LE := RingEquiv.refl ↥L
  have hcomp : (algebraMap ↥T ↥LE).comp f.toRingHom
      = gg.toRingHom.comp (algebraMap ↥S ↥L) := by
    ext s
    rfl
  exact IsGalois.of_equiv_equiv (f := f) (g := gg) hcomp

end Work.MotV5.RigAS.GaloisTrue
