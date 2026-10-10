import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.SSGRoute.LTDDefs.H3loc.Defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The extension by `0` off `H` of a continuous `3`-coboundary of `↥H` is a local `3`-coboundary

This is the exact degree-`3` analogue of
`Work.SSGRoute.LTDDefs.H2loc.extendFun2_mem_coboundaries2`: the extension `extendFun3 H c` of a
*continuous* `3`-coboundary `c` of the profinite group `↥H` (an element of `Work.SSGRoute.B3 ↥H`,
i.e. `d²` of a locally constant `2`-cochain of `↥H`) is a local `3`-coboundary on `H`, i.e. lies in
`Work.SSGRoute.coboundaries3 p k Ω K M H`.

The proof is the degree-`3` transcription of the degree-`2` argument:

* `c ∈ B3 ↥H` unwinds (`Work.SSGRoute.mem_B3_iff`) to a locally constant `b : ↥H × ↥H → M` with
  `d² b = c`;
* `b` is uniformly locally constant by an open subgroup `U ≤ G_k` (the pair form
  `exists_openSubgroup_pair_mul_eq_of_isLocallyConstant` of uniform local constancy on the
  profinite group `↥H`, using closedness of `H`), so that `extendFun2 H b` satisfies the local
  constancy condition `IsLocConst2On` demanded by `IsCoboundary3On`;
* for `g, h, l ∈ H` all of `g * h`, `h * l` stay in `H`, and the two differentials `d²` agree —
  `dCochain2` acts through `res k K`, which is identified with the action of `↥H` by `hcompat`.

## Note on the spelling of the finiteness hypothesis

The statement as it was requested writes the hypothesis on `K` as `[FinitDimensional k K]`; the
intended (and Mathlib) name is `FiniteDimensional`.  To keep the statement *verbatim* as
requested, the alias `FinitDimensional` is introduced below as an abbreviation for
`FiniteDimensional` (it unfolds to it definitionally, so the statement is the intended one, and
callers passing a `FiniteDimensional` instance are unaffected).
-/

/-- Alias for `FiniteDimensional`, so that the statement below reads verbatim as requested. -/
abbrev FinitDimensional (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop :=
  FiniteDimensional k K

namespace Work.SSGRoute.LTDDefs.H3bridge

theorem extendFun3_mem_coboundaries3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FinitDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : ↥H × ↥H × ↥H → M} (hc : c ∈ Work.SSGRoute.Z3 (M := M) ↥H)
    (hb : c ∈ Work.SSGRoute.B3 (M := M) ↥H) :
    Work.SSGRoute.LTDDefs.H3loc.extendFun3 H c ∈ Work.SSGRoute.coboundaries3 p k Ω K M H := by
  rw [Work.SSGRoute.mem_B3_iff] at hb
  obtain ⟨b, hbloc, hbeq⟩ := hb
  obtain ⟨U, hUo, hU⟩ :=
    Work.SSGRoute.exists_openSubgroup_pair_mul_eq_of_isLocallyConstant k Ω H hH hbloc
  refine (Work.SSGRoute.mem_coboundaries3 p k Ω K M H _).mpr ⟨Work.SSGRoute.extendFun2 H b,
    ⟨U, hUo, ?_⟩, ?_⟩
  · -- Local constancy of `extendFun2 H b` on `H × H`.
    intro g hg h hh u hu v hv huH hvH
    have hgu : g * u ∈ H := H.mul_mem hg huH
    have hhv : h * v ∈ H := H.mul_mem hh hvH
    rw [Work.SSGRoute.extendFun2_apply H b hgu hhv,
      Work.SSGRoute.extendFun2_apply H b hg hh]
    have h1 := hU ⟨g, hg⟩ ⟨h, hh⟩ u v huH hvH hu hv
    have e1 : (⟨g * u, hgu⟩ : ↥H) = ⟨g, hg⟩ * ⟨u, huH⟩ := Subtype.ext rfl
    have e2 : (⟨h * v, hhv⟩ : ↥H) = ⟨h, hh⟩ * ⟨v, hvH⟩ := Subtype.ext rfl
    rw [e1, e2]
    exact h1
  · -- The `d²` identity: `extendFun3 H c = d² (extendFun2 H b)` on `H`.
    intro g hg h hh l hl
    have hgh : g * h ∈ H := H.mul_mem hg hh
    have hhl : h * l ∈ H := H.mul_mem hh hl
    rw [Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hg hh hl,
      Work.SSGRoute.dCochain2_apply,
      Work.SSGRoute.extendFun2_apply H b hh hl,
      Work.SSGRoute.extendFun2_apply H b hgh hl,
      Work.SSGRoute.extendFun2_apply H b hg hhl,
      Work.SSGRoute.extendFun2_apply H b hg hh]
    rw [← hbeq, Work.GroupCohomology.d2_apply]
    have e1 : (⟨g, hg⟩ : ↥H) • b (⟨h, hh⟩, ⟨l, hl⟩)
        = SSGRoute.res k K g • b (⟨h, hh⟩, ⟨l, hl⟩) := hcompat ⟨g, hg⟩ _
    have e2 : (⟨g, hg⟩ * ⟨h, hh⟩ : ↥H) = ⟨g * h, hgh⟩ := Subtype.ext rfl
    have e3 : (⟨h, hh⟩ * ⟨l, hl⟩ : ↥H) = ⟨h * l, hhl⟩ := Subtype.ext rfl
    rw [e1, e2, e3]

end Work.SSGRoute.LTDDefs.H3bridge
