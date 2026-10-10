import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.CokerF
import Submission.Work.SSGRoute.HSRow.CokerZr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugation action on `Zr`, the class map, and the `2`-cochain `Fz`
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


/-- The conjugation of `i ∈ I` by `γ ∈ C`, as an element of `↥I`. -/
def conjI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (i : ↥I) : ↥I :=
  ⟨(γ : Ω ≃ₐ[k] Ω)⁻¹ * (i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω),
    conj_inv_mem p k Ω K M I σ H γ (i : Ω ≃ₐ[k] Ω) i.2⟩

@[simp] lemma conjI_coe (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (i : ↥I) :
    ((conjI p k Ω K M I σ H γ i : ↥I) : Ω ≃ₐ[k] Ω)
      = (γ : Ω ≃ₐ[k] Ω)⁻¹ * (i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω) := rfl

lemma conjI_mul (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (g h : ↥I) :
    conjI p k Ω K M I σ H γ (g * h)
      = conjI p k Ω K M I σ H γ g * conjI p k Ω K M I σ H γ h := by
  refine Subtype.ext ?_
  show (γ : Ω ≃ₐ[k] Ω)⁻¹ * ((g * h : ↥I) : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)
    = (γ : Ω ≃ₐ[k] Ω)⁻¹ * (g : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)
      * ((γ : Ω ≃ₐ[k] Ω)⁻¹ * (h : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω))
  rw [Subgroup.coe_mul]
  group

/-- The conjugation action of `γ ∈ C` on the locally constant `1`-cocycles on `↥I`. -/
def twR (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) : ↥(Zr p k Ω K M I) →ₗ[ZMod p] ↥(Zr p k Ω K M I) where
  toFun f :=
    ⟨fun i => SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • (f : ↥I → M) (conjI p k Ω K M I σ H γ i), ⟨by
        intro g h
        have h1 : (f : ↥I → M) (conjI p k Ω K M I σ H γ (g * h))
            = (f : ↥I → M) (conjI p k Ω K M I σ H γ g
                * conjI p k Ω K M I σ H γ h) :=
          congrArg (fun x : ↥I => (f : ↥I → M) x) (conjI_mul p k Ω K M I σ H γ g h)
        show SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
              • (f : ↥I → M) (conjI p k Ω K M I σ H γ (g * h))
            = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
                • (f : ↥I → M) (conjI p k Ω K M I σ H γ g)
              + SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)
                • (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
                    • (f : ↥I → M) (conjI p k Ω K M I σ H γ h))
        rw [h1, (f.2.1) (conjI p k Ω K M I σ H γ g) (conjI p k Ω K M I σ H γ h), smul_add]
        congr 1
        rw [← mul_smul, ← mul_smul]
        congr 1
        rw [conjI_coe]
        simp only [map_mul, map_inv]
        group, by
        obtain ⟨U, hUo, hU⟩ := f.2.2
        haveI hUfin : U.FiniteIndex := by
          rw [Subgroup.finiteIndex_iff_finite_quotient]
          exact Subgroup.quotient_finite_of_isOpen U hUo
        refine ⟨Subgroup.normalCore U, ?_, ?_⟩
        · have hUc : IsClosed (U : Set (Ω ≃ₐ[k] Ω)) :=
            Subgroup.isClosed_of_isOpen U hUo
          have hUnc : IsClosed ((Subgroup.normalCore U : Subgroup (Ω ≃ₐ[k] Ω)) :
              Set (Ω ≃ₐ[k] Ω)) := Subgroup.normalCore_isClosed U hUc
          exact Subgroup.isOpen_of_isClosed_of_finiteIndex (Subgroup.normalCore U) hUnc
        · intro g u hu
          haveI hNnorm : (Subgroup.normalCore U).Normal := inferInstance
          have hcu : (γ : Ω ≃ₐ[k] Ω)⁻¹ * (u : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω) ∈
              Subgroup.normalCore U := by
            have h := hNnorm.conj_mem (u : Ω ≃ₐ[k] Ω) hu (γ : Ω ≃ₐ[k] Ω)⁻¹
            simpa using h
          have h1 : (f : ↥I → M) (conjI p k Ω K M I σ H γ (g * u))
              = (f : ↥I → M) (conjI p k Ω K M I σ H γ g
                  * conjI p k Ω K M I σ H γ u) :=
            congrArg (fun x : ↥I => (f : ↥I → M) x) (conjI_mul p k Ω K M I σ H γ g u)
          show SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
              • (f : ↥I → M) (conjI p k Ω K M I σ H γ (g * u))
            = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
              • (f : ↥I → M) (conjI p k Ω K M I σ H γ g)
          rw [h1, hU (conjI p k Ω K M I σ H γ g) (conjI p k Ω K M I σ H γ u)
            (Subgroup.normalCore_le U hcu)]⟩⟩
  map_add' f g := Subtype.ext (funext fun i => by
    show SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • ((f : ↥I → M) + (g : ↥I → M)) (conjI p k Ω K M I σ H γ i)
      = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • (f : ↥I → M) (conjI p k Ω K M I σ H γ i)
        + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • (g : ↥I → M) (conjI p k Ω K M I σ H γ i)
    rw [Pi.add_apply, smul_add])
  map_smul' c f := Subtype.ext (funext fun i => by
    show SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • (c • (f : ↥I → M)) (conjI p k Ω K M I σ H γ i)
      = c • (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • (f : ↥I → M) (conjI p k Ω K M I σ H γ i))
    rw [Pi.smul_apply, smul_comm])

@[simp] lemma twR_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (f : ↥(Zr p k Ω K M I)) (i : ↥I) :
    (twR p k Ω K M I σ H γ f : ↥I → M) i
      = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
        • (f : ↥I → M) (conjI p k Ω K M I σ H γ i) := rfl

lemma twR_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) (f : ↥(Zr p k Ω K M I)) :
    twR p k Ω K M I σ H γ (twR p k Ω K M I σ H δ f)
      = twR p k Ω K M I σ H (γ * δ) f := by
  have key : ∀ i : ↥I, conjI p k Ω K M I σ H δ (conjI p k Ω K M I σ H γ i)
      = conjI p k Ω K M I σ H (γ * δ) i := by
    intro i
    refine Subtype.ext ?_
    rw [conjI_coe, conjI_coe, conjI_coe, Subgroup.coe_mul]
    group
  refine Subtype.ext (funext fun i => ?_)
  rw [twR_apply, twR_apply, twR_apply, Subgroup.coe_mul, map_mul, mul_smul, key]

lemma conjI_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) (i : ↥I) :
    conjI p k Ω K M I σ H 1 i = i := by
  refine Subtype.ext ?_
  rw [conjI_coe]
  simp

lemma twR_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    twR p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) = LinearMap.id := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun i => ?_)
  rw [twR_apply, conjI_one, OneMemClass.coe_one, map_one, one_smul]
  rfl

/-- The class of `F ∈ Zr` in `H¹_loc(I,M)`: the class of its extension by zero. -/
def cl (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : ↥(Zr p k Ω K M I) →ₗ[ZMod p]
      Work.SSGRoute.H1loc p k Ω K M I :=
  (Submodule.mkQ (Submodule.comap (SSGRoute.lcCocycles p k Ω K M I).subtype
      (SSGRoute.coboundaries p k Ω K M I))).comp
    (((ext0 p k Ω K M I).comp (Zr p k Ω K M I).subtype).codRestrict
      (SSGRoute.lcCocycles p k Ω K M I)
      (fun f => ext0_mem_lcCocycles p k Ω K M I f.2))

lemma cl_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥(Zr p k Ω K M I)) :
    cl p k Ω K M I f = SSGRoute.toClass p k Ω K M I
      (ext0 p k Ω K M I (f : ↥I → M)) := by
  rw [cl, LinearMap.comp_apply, Submodule.mkQ_apply, SSGRoute.toClass,
    dif_pos (ext0_mem_lcCocycles p k Ω K M I f.2)]
  rfl

/-- The `Zr`-element attached to a locally constant `1`-cocycle on `I`. -/
def resZr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (β : ↥(SSGRoute.lcCocycles p k Ω K M I)) :
    ↥(Zr p k Ω K M I) :=
  ⟨resI p k Ω K M I (β : (Ω ≃ₐ[k] Ω) → M), resI_mem_Zr p k Ω K M I β.2⟩

@[simp] lemma resZr_coe (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (β : ↥(SSGRoute.lcCocycles p k Ω K M I)) (i : ↥I) :
    (resZr p k Ω K M I β : ↥I → M) i = (β : (Ω ≃ₐ[k] Ω) → M) (i : Ω ≃ₐ[k] Ω) := rfl

lemma cl_resZr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (β : ↥(SSGRoute.lcCocycles p k Ω K M I)) :
    cl p k Ω K M I (resZr p k Ω K M I β)
      = SSGRoute.toClass p k Ω K M I (β : (Ω ≃ₐ[k] Ω) → M) := by
  rw [cl_apply]
  exact toClass_eq_of_eqOn_I p k Ω K M I (ext0_mem_lcCocycles p k Ω K M I
      (resZr p k Ω K M I β).2) β.2
    (fun n hn => by rw [ext0_apply_mem p k Ω K M I _ hn]; rfl)

/-- The submodule of "coboundaries" in `Zr`: the kernel of the class map. -/
def Br (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ↥(Zr p k Ω K M I) :=
  LinearMap.ker (cl p k Ω K M I)

lemma mem_Br (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥(Zr p k Ω K M I)) :
    f ∈ Br p k Ω K M I ↔ cl p k Ω K M I f = 0 := Iff.rfl

end

end Work.SSGRoute.HSRow
