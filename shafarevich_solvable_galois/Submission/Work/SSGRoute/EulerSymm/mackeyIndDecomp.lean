import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.EulerSymm.indCyclicSubModel
import Submission.Work.SSGRoute.artinInduced
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Mackey decomposition of `Res_{D_A}(Ind_C^G N)`

For `G = Gal(K/k)`, `C ≤ G`, a finite `𝔽_p[C]`-module `N`, and `D_A = decomp k A`, the restriction
of `Ind_C^G N` to `D_A` (with `δ • f = res(δ) • f`) is the internal direct sum of the submodules
supported on the double cosets `G_A · g · C` (`G_A = res(D_A)`); the summand attached to `g` is
`Ind_{D_d(g)}^{D_A}(gN)`, with `D_d(g) = D_A ⊓ comap (res k K) (g C g⁻¹)` and `gN` the module `N`
with the conjugated `g C g⁻¹`-action pulled back along `res`.

Items 2–3 of `NOTE_indCyclic_route.md` §6.
-/

open scoped TensorProduct
open Classical

namespace Work.SSGRoute.EulerSymm

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `G_A = res(D_A) ⊆ G`, the image of the **decomposition group** `D_A = decomp k A`.  (Note
`(res k K).range` alone is all of `G`, since `res` is surjective on `Gal(Ω/k)`.) -/
abbrev imageRes (A : ValuationSubring Ω) : Subgroup (K ≃ₐ[k] K) :=
  (SSGRoute.decomp k A).map (SSGRoute.res k K)

/-- The double coset `G_A · g · C ⊆ G`. -/
def doubleCosetSet (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K) :
    Set (K ≃ₐ[k] K) :=
  {x | ∃ a ∈ imageRes k Ω K A, ∃ c ∈ C, x = a * g * c}

/-- `D_d(g) = D_A ⊓ comap (res k K) (g C g⁻¹)`; `res` maps it onto `G_A ∩ g C g⁻¹`. -/
def Dd (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K) :
    Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓
    Subgroup.comap (SSGRoute.res k K) (C.map (MulEquiv.toMonoidHom (MulAut.conj g)))

variable {k Ω K}

/-- `res k K` restricted to `D_d(g)`, landing in `g C g⁻¹`. -/
def DdToConj (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K) :
    ↥(Dd k Ω K A C g) →* ↥(C.map (MulEquiv.toMonoidHom (MulAut.conj g))) where
  toFun δ := ⟨SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω), δ.2.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' δ ε := Subtype.ext (map_mul _ _ _)

/-- The isomorphism `↥C ≃* ↥(g C g⁻¹)`, `c ↦ g c g⁻¹`. -/
def conjSubgroupIso (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K) :
    ↥C ≃* ↥(C.map (MulEquiv.toMonoidHom (MulAut.conj g))) :=
  Subgroup.equivMapOfInjective C (MulEquiv.toMonoidHom (MulAut.conj g))
    (MulAut.conj g).injective

/-- The homomorphism `↥(D_d g) →* ↥C`, `δ ↦ g⁻¹ (res δ) g`. -/
def DdToC (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K) :
    ↥(Dd k Ω K A C g) →* ↥C :=
  (conjSubgroupIso C g).symm.toMonoidHom.comp (DdToConj A C g)

/-- The `↥(D_d g)`-module `gN`. -/
def twistAction (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (g : K ≃ₐ[k] K) (N : Type) [AddCommGroup N] [DistribMulAction ↥C N] :
    DistribMulAction ↥(Dd k Ω K A C g) N :=
  DistribMulAction.compHom N (DdToC A C g)

attribute [instance] twistAction

/-- The `𝔽_p`-action on `gN` commutes with the twisted action. -/
instance twistSMulComm (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K))
    (g : K ≃ₐ[k] K) (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction ↥C N]
    [SMulCommClass ↥C (ZMod p) N] :
    SMulCommClass ↥(Dd k Ω K A C g) (ZMod p) N where
  smul_comm δ c n := smul_comm (DdToC A C g δ) c n

/-- The Euler characteristic at `D_d(g)` with the twisted coefficient `gN`. -/
def chiTwist (A : ValuationSubring Ω) (C : Subgroup (K ≃ₐ[k] K)) (g : K ≃ₐ[k] K)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction ↥C N]
    [SMulCommClass ↥C (ZMod p) N] : ℤ :=
  chiSubH p k Ω (Dd k Ω K A C g) N


/-- A `Gal(K/k)`-module is a module for any subgroup, by restriction. -/
instance restrictDistribMulAction (C : Subgroup (K ≃ₐ[k] K)) (T : Type) [AddCommGroup T]
    [DistribMulAction (K ≃ₐ[k] K) T] : DistribMulAction ↥C T :=
  DistribMulAction.compHom T C.subtype

/-- The restricted `𝔽_p`-action commutes with the restricted group action. -/
instance restrictSMulCommClass (C : Subgroup (K ≃ₐ[k] K)) (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] :
    SMulCommClass ↥C (ZMod p) T where
  smul_comm c r t := smul_comm (c : K ≃ₐ[k] K) r t

end

end Work.SSGRoute.EulerSymm
