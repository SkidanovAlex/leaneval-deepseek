import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.PT.H2RowAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The restricted module of locally constant `1`-cocycles on `I`

The submodule `lcCocycles p k Ω K M I` of *all* functions `G_k → M` is infinite-dimensional: the
cocycle and local-constancy conditions only constrain the values on `I`, so the values off `I` are
free.  All the constructions of the inverse transgression only ever evaluate cocycles at elements
of `I`; the correct ambient module is therefore the module `Zr` of functions `↥I → M` that are
locally constant `1`-cocycles *on `I`*.

This file provides `Zr`, the conjugation action of `C = closure (zpowers σ)` on it, and the
comparison maps with the class group `H1loc(I,M) = lcCocycles I ⧸ coboundaries`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The restriction of a function on `G_k` to `I`. -/
def resI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : ((Ω ≃ₐ[k] Ω) → M) →ₗ[ZMod p] (↥I → M) where
  toFun f := fun i => f (i : Ω ≃ₐ[k] Ω)
  map_add' f g := rfl
  map_smul' c f := rfl

/-- The extension of a function on `I` by zero. -/
def ext0 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : (↥I → M) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → M) where
  toFun f := fun x => if h : x ∈ I then f ⟨x, h⟩ else 0
  map_add' f g := by
    funext x
    by_cases h : x ∈ I <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : x ∈ I <;> simp [h]

@[simp] lemma ext0_apply_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥I → M) {x : Ω ≃ₐ[k] Ω} (hx : x ∈ I) :
    ext0 p k Ω K M I f x = f ⟨x, hx⟩ := by
  simp [ext0, hx]

@[simp] lemma ext0_apply_not_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥I → M) {x : Ω ≃ₐ[k] Ω} (hx : x ∉ I) :
    ext0 p k Ω K M I f x = 0 := by
  simp [ext0, hx]

/-- The cocycle condition on `I` for a function on `↥I`. -/
def IsCocycleI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥I → M) : Prop :=
  ∀ g h : ↥I, f (g * h) = f g + SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • f h

/-- Local constancy on `I` for a function on `↥I`. -/
def IsLocConstI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥I → M) : Prop :=
  ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ g : ↥I, ∀ u : ↥I, (u : Ω ≃ₐ[k] Ω) ∈ U → f (g * u) = f g

/-- The module of locally constant `1`-cocycles on `I` (as functions on `↥I`). -/
def Zr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) (↥I → M) where
  carrier := {f | IsCocycleI p k Ω K M I f ∧ IsLocConstI p k Ω K M I f}
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · intro g h; simp
    · exact ⟨⊤, isOpen_univ, fun g u _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro x y
      simp only [Pi.add_apply, hf1 x y, hg1 x y, smul_add]
      abel
    · obtain ⟨U, hUo, hU⟩ := hf2
      obtain ⟨V, hVo, hV⟩ := hg2
      refine ⟨U ⊓ V, ?_, fun g u hu => ?_⟩
      · rw [Subgroup.coe_inf]; exact hUo.inter hVo
      · have h1 : (u : Ω ≃ₐ[k] Ω) ∈ U := (Subgroup.mem_inf.mp hu).1
        have h2 : (u : Ω ≃ₐ[k] Ω) ∈ V := (Subgroup.mem_inf.mp hu).2
        simp only [Pi.add_apply, hU g u h1, hV g u h2]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨?_, ?_⟩
    · intro x y
      simp only [Pi.smul_apply, hf1 x y, smul_add]
      rw [smul_comm (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) c (f y)]
    · obtain ⟨U, hUo, hU⟩ := hf2
      exact ⟨U, hUo, fun g u hu => by simp only [Pi.smul_apply, hU g u hu]⟩

@[simp] lemma mem_Zr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥I → M) :
    f ∈ Zr p k Ω K M I ↔ IsCocycleI p k Ω K M I f ∧ IsLocConstI p k Ω K M I f := Iff.rfl

/-- The restriction of a locally constant `1`-cocycle on `I` (as a function on `G_k`) is one (as
a function on `↥I`). -/
lemma resI_mem_Zr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ SSGRoute.lcCocycles p k Ω K M I) :
    resI p k Ω K M I f ∈ Zr p k Ω K M I := by
  obtain ⟨hcoc, hloc⟩ := hf
  obtain ⟨U, hUo, hU⟩ := hloc
  refine ⟨fun g h => ?_, ⟨U, hUo, fun g u hu => ?_⟩⟩
  · exact hcoc g g.2 h h.2
  · exact hU g g.2 (u : Ω ≃ₐ[k] Ω) hu u.2

/-- Extending a locally constant `1`-cocycle on `↥I` by zero gives a locally constant
`1`-cocycle on `I` in the sense of functions on `G_k`. -/
lemma ext0_mem_lcCocycles (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) {f : ↥I → M} (hf : f ∈ Zr p k Ω K M I) :
    ext0 p k Ω K M I f ∈ SSGRoute.lcCocycles p k Ω K M I := by
  obtain ⟨hcoc, hloc⟩ := hf
  obtain ⟨U, hUo, hU⟩ := hloc
  refine ⟨fun g hg h hh => ?_, ⟨U, hUo, fun g hg u hu huI => ?_⟩⟩
  · rw [ext0_apply_mem p k Ω K M I f (I.mul_mem hg hh), ext0_apply_mem p k Ω K M I f hg,
      ext0_apply_mem p k Ω K M I f hh]
    exact hcoc ⟨g, hg⟩ ⟨h, hh⟩
  · rw [ext0_apply_mem p k Ω K M I f (I.mul_mem hg huI), ext0_apply_mem p k Ω K M I f hg]
    exact hU ⟨g, hg⟩ ⟨u, huI⟩ hu

/-- Pointwise agreement on `I` gives equality of classes in `H¹_loc(I,M)`. -/
lemma toClass_eq_of_eqOn_I (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) {f f' : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ SSGRoute.lcCocycles p k Ω K M I) (hf' : f' ∈ SSGRoute.lcCocycles p k Ω K M I)
    (h : ∀ n ∈ I, f n = f' n) :
    SSGRoute.toClass p k Ω K M I f = SSGRoute.toClass p k Ω K M I f' := by
  have hsub : f - f' ∈ SSGRoute.lcCocycles p k Ω K M I := Submodule.sub_mem _ hf hf'
  have hcob : f - f' ∈ SSGRoute.coboundaries p k Ω K M I :=
    ⟨0, fun n hn => by rw [Pi.sub_apply, h n hn, sub_self]; simp⟩
  have hzero : SSGRoute.toClass p k Ω K M I (f - f') = 0 :=
    (SSGRoute.toClass_eq_zero_iff p k Ω K M I hsub).mpr hcob
  have hsplit : f = f' + (f - f') := by
    ext x; simp
  rw [hsplit, SSGRoute.toClass_add p k Ω K M I hf' hsub, hzero, add_zero]

end

end Work.SSGRoute.HSRow
