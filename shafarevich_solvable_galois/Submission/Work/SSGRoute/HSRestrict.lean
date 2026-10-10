import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.HSConj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of locally constant `1`-cocycles to a subgroup

For `I ≤ D = decomp k A` the assignment "restrict a locally constant `1`-cocycle on `D` to `I`"
descends to a `𝔽_p`-linear map `res1 : H¹_loc(D,M) → H¹_loc(I,M)`, computing on representatives
by `res1 (toClass_D f) = toClass_I f`.
-/

open scoped Pointwise
open Classical

set_option linter.unusedSectionVars false

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (A : ValuationSubring Ω)

/-- A locally constant `1`-cocycle on `D = decomp k A` restricts to a locally constant
`1`-cocycle on any subgroup `I ≤ D`. -/
def restrictCocycle1 (hI : I ≤ SSGRoute.decomp k A) :
    ↥(lcCocycles p k Ω K M (SSGRoute.decomp k A)) →ₗ[ZMod p]
      ↥(lcCocycles p k Ω K M I) where
  toFun f := ⟨f.1, ⟨fun g hg h hh => f.2.1 g (hI hg) h (hI hh),
    f.2.2.choose, f.2.2.choose_spec.1,
    fun g hg u hu huI => f.2.2.choose_spec.2 g (hI hg) u hu (hI huI)⟩⟩
  map_add' f g := Subtype.ext rfl
  map_smul' c f := Subtype.ext rfl

@[simp] lemma restrictCocycle1_coe (hI : I ≤ SSGRoute.decomp k A)
    (f : ↥(lcCocycles p k Ω K M (SSGRoute.decomp k A))) :
    (restrictCocycle1 p k Ω K M I A hI f : (Ω ≃ₐ[k] Ω) → M) = f.1 := rfl

/-- A `1`-coboundary on `D` restricts to a `1`-coboundary on `I`. -/
lemma cobQ_le_comap_restrict (hI : I ≤ SSGRoute.decomp k A) :
    cobQ p k Ω K M (SSGRoute.decomp k A) ≤
      Submodule.comap (restrictCocycle1 p k Ω K M I A hI) (cobQ p k Ω K M I) := by
  intro x hx
  rw [cobQ, Submodule.mem_comap] at hx
  rw [Submodule.mem_comap]
  show x.1 ∈ coboundaries p k Ω K M I
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun g hg => hm g (hI hg)⟩

/-- **The restriction map** `H¹_loc(D,M) → H¹_loc(I,M)`. -/
noncomputable def res1 (hI : I ≤ SSGRoute.decomp k A) :
    H1loc p k Ω K M (SSGRoute.decomp k A) →ₗ[ZMod p] H1loc p k Ω K M I :=
  Submodule.mapQ (cobQ p k Ω K M (SSGRoute.decomp k A)) (cobQ p k Ω K M I)
    (restrictCocycle1 p k Ω K M I A hI) (cobQ_le_comap_restrict p k Ω K M I A hI)

lemma res1_toClass (hI : I ≤ SSGRoute.decomp k A)
    (f : (Ω ≃ₐ[k] Ω) → M) (hf : f ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A)) :
    res1 p k Ω K M I A hI (toClass p k Ω K M (SSGRoute.decomp k A) f)
      = toClass p k Ω K M I f := by
  have h1 : toClass p k Ω K M (SSGRoute.decomp k A) f
      = Submodule.mkQ (cobQ p k Ω K M (SSGRoute.decomp k A)) ⟨f, hf⟩ := by
    rw [toClass, dif_pos hf]
  have hflc : f ∈ lcCocycles p k Ω K M I :=
    (restrictCocycle1 p k Ω K M I A hI ⟨f, hf⟩).2
  have h2 : toClass p k Ω K M I f = Submodule.mkQ (cobQ p k Ω K M I) ⟨f, hflc⟩ := by
    rw [toClass, dif_pos hflc]
  rw [h1, h2, Submodule.mkQ_apply]
  show (Submodule.mapQ (cobQ p k Ω K M (SSGRoute.decomp k A)) (cobQ p k Ω K M I)
      (restrictCocycle1 p k Ω K M I A hI) (cobQ_le_comap_restrict p k Ω K M I A hI))
      (Submodule.Quotient.mk ⟨f, hf⟩) = Submodule.Quotient.mk ⟨f, hflc⟩
  rw [Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

end

end Work.SSGRoute
