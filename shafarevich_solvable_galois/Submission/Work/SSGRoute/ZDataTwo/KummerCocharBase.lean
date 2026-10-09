import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic_over_K
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.grunwald_setup
import Submission.Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit
import Submission.Work.SSGRoute.exists_kummerChar_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer-cochain bridge (base definitions)

`Work.SSGRoute.kummerCochar` is the global Kummer character of `b ∈ Kˣ`, transported from
`Gal(Ω/↥K)` to `G_K = K.fixingSubgroup` by `IntermediateField.fixingSubgroupEquiv` and extended by
`0` off `G_K`.  This module collects the definition, its elementary properties (additivity, local
constancy, multiplicativity in the element, invisibility of squares), the local Kummer dictionary
in the cochain language, and the node-shaped wrapper `Work.SSGRoute.nodeKummerCochar`, so that the
files stating the Schmidt–Wingberg §4 arithmetic core (and the node's assembly) share them.
-/

open scoped Pointwise

namespace Work.SSGRoute

section KummerBridge

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

open _root_.SSGRoute

/-- The global Kummer cochain of `b ∈ Kˣ`: the Kummer character of `b` on `G_K`, extended by `0`
off `G_K`. -/
noncomputable def kummerCochar (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) : (Ω ≃ₐ[k] Ω) → ZMod 2 := by
  classical
  exact fun σ => if h : σ ∈ K.fixingSubgroup then
    Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ b
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0

lemma kummerCochar_apply (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCochar K ζ hζ b σ =
      Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ b
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
  simp only [kummerCochar, dif_pos hσ]

lemma kummerCochar_of_not_mem (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∉ K.fixingSubgroup) : kummerCochar K ζ hζ b σ = 0 := by
  simp only [kummerCochar, dif_neg hσ]

/-- The Kummer cochain of `b` is additive on `G_K`. -/
lemma kummerCochar_add (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) :
    ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      kummerCochar K ζ hζ b (g * h) = kummerCochar K ζ hζ b g + kummerCochar K ζ hζ b h := by
  intro g hg h hh
  have hgh : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
  rw [kummerCochar_apply K ζ hζ b hgh, kummerCochar_apply K ζ hζ b hg,
    kummerCochar_apply K ζ hζ b hh]
  have key : (⟨g * h, hgh⟩ : ↥(K.fixingSubgroup)) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
  rw [key, map_mul (IntermediateField.fixingSubgroupEquiv K),
    Work.SSGRoute.kummerChar_mul_apply]

/-- The Kummer cochain of `b` is locally constant on `G_K`. -/
lemma kummerCochar_locConst (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) :
    SSGRoute.IsLocConstOn K.fixingSubgroup (kummerCochar K ζ hζ b) := by
  haveI hfdL : FiniteDimensional k
      ↥(IntermediateField.adjoin k
        {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b}) :=
    IntermediateField.adjoin.finiteDimensional (K := k)
      (x := Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b)
      ((Algebra.IsAlgebraic.isIntegral (K := k) (A := Ω)).isIntegral _)
  refine ⟨K.fixingSubgroup ⊓ (IntermediateField.adjoin k
      {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b}).fixingSubgroup, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen K).inter
      (IntermediateField.fixingSubgroup_isOpen _)
  · intro gg hg u hu huH
    obtain ⟨huK, huL⟩ := Subgroup.mem_inf.mp hu
    have hgu : gg * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huK
    rw [kummerCochar_apply K ζ hζ b hgu, kummerCochar_apply K ζ hζ b hg]
    have key : (⟨gg * u, hgu⟩ : ↥(K.fixingSubgroup)) = ⟨gg, hg⟩ * ⟨u, huK⟩ := Subtype.ext rfl
    rw [key, map_mul (IntermediateField.fixingSubgroupEquiv K),
      Work.SSGRoute.kummerChar_mul_apply]
    have hfix : ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω)
          ((Work.SSGRoute.kummerSqrt (Ω := Ω) b : Ωˣ) : Ω) =
        ((Work.SSGRoute.kummerSqrt (Ω := Ω) b : Ωˣ) : Ω) := by
      have hmem : Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b ∈ (IntermediateField.adjoin k
          {Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b} : IntermediateField k Ω) :=
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      have hfixu : (u : Ω ≃ₐ[k] Ω) (Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b) =
          Work.SSGRoute.kummerSqrtVal (K := ↥K) (Ω := Ω) b :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp huL _ hmem
      have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω) =
          ⇑(u : Ω ≃ₐ[k] Ω) := by ext x; rfl
      exact (congrFun hcoe ((Work.SSGRoute.kummerSqrt (Ω := Ω) b : Ωˣ) : Ω)).trans
        (by simpa only [Work.SSGRoute.kummerSqrt, Units.val_mk0] using hfixu)
    have hzero : Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ b
        ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) = 0 :=
      Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq 2 hζ b (Work.SSGRoute.kummerSqrt (Ω := Ω) b)
        (Work.SSGRoute.kummerSqrt_pow (Ω := Ω) b) _ hfix
    rw [hzero, add_zero]

/-- **The local Kummer dictionary in the node's vocabulary.**  The Kummer cochain of `b` vanishes
on the local group `decomp k A ⊓ G_K` of a finite place `A` if and only if `b` is a local `2`-power
at the prime `𝔭` of `K` below `A`.  This transports
`Work.SSGRoute.local_kummer_dictionary_two` along `grunwaldSetupDecompEquiv`. -/
theorem kummerCochar_eq_zero_iff_localPowClass (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    ((∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, kummerCochar K ζ hζ b σ = 0) ↔
      NK.UchidaKummer.localPowClass ↥K 2 𝔭 b = 1) := by
  have hdict := Work.SSGRoute.local_kummer_dictionary_two k Ω K ζ hζ A hA 𝔭 h𝔭 b
  constructor
  · intro h
    rw [← hdict]
    intro τ hτ
    set x : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      (grunwaldSetupDecompEquiv k Ω K A).symm ⟨τ, hτ⟩ with hx
    have hxK : (x : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp x.2).2
    have h1 : Work.SSGRoute.kummerChar (Ω := Ω) ζ hζ b
        ((IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), hxK⟩) = 0 := by
      have h0 := h (x : Ω ≃ₐ[k] Ω) x.2
      rwa [kummerCochar_apply K ζ hζ b hxK] at h0
    have h3 : ((IntermediateField.fixingSubgroupEquiv K)
          ⟨(x : Ω ≃ₐ[k] Ω), hxK⟩ : Ω ≃ₐ[↥K] Ω) = τ := by
      have h4 := (grunwaldSetupDecompEquiv k Ω K A).apply_symm_apply ⟨τ, hτ⟩
      exact congrArg Subtype.val h4
    rwa [h3] at h1
  · intro h σ hσ
    rw [kummerCochar_apply K ζ hζ b (Subgroup.mem_inf.mp hσ).2]
    exact (hdict.mpr h) _ (grunwaldSetupDecompEquiv k Ω K A ⟨σ, hσ⟩).2


/-- The Kummer cochain is multiplicative in the element (the Kummer character of a product is the
sum of the Kummer characters). -/
lemma kummerCochar_mul (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (a b : (↥K)ˣ) :
    kummerCochar K ζ hζ (a * b) = kummerCochar K ζ hζ a + kummerCochar K ζ hζ b := by
  classical
  funext σ
  by_cases hσ : σ ∈ K.fixingSubgroup
  · rw [kummerCochar_apply K ζ hζ (a * b) hσ, Work.SSGRoute.kummerChar_mul]
    simp only [Pi.add_apply]
    rw [kummerCochar_apply K ζ hζ a hσ, kummerCochar_apply K ζ hζ b hσ]
  · rw [kummerCochar_of_not_mem K ζ hζ (a * b) hσ]
    simp only [Pi.add_apply, kummerCochar_of_not_mem K ζ hζ a hσ,
      kummerCochar_of_not_mem K ζ hζ b hσ, zero_add]

/-- `x + x = 0` in `ZMod 2`. -/
lemma zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, h2, zero_mul]


/-- A square factor is invisible to the Kummer cochain (`char(c²) = 2·char(c) = 0` in `𝔽₂`). -/
lemma kummerCochar_sq (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (c : (↥K)ˣ) : kummerCochar K ζ hζ (c ^ 2) = 0 := by
  rw [pow_two, kummerCochar_mul]
  funext σ
  exact zmodTwo_add_self _

/-- **Conjunct (5) of the node, from an arithmetic hypothesis on `b`.**  If `b = c² u` with `u` a
unit at every finite place `A` at which `u` is required to be a unit (`A ∤ 2`), then the Kummer
cochain of `b` kills the inertia of `A`. -/
theorem kummerCochar_eq_zero_of_isInertia_of_sq_mul_unit (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (h2 : ¬ A.valuation (2 : Ω) < 1)
    (c u : (↥K)ˣ) (hu : A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup)
    (hσI : SSGRoute.IsInertia (k := ↥K) A
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)) :
    kummerCochar K ζ hζ (c ^ 2 * u) σ = 0 := by
  have hzero := Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit k Ω K ζ hζ A hA h2 u hu
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) hσI
  rw [kummerCochar_mul]
  simp only [Pi.add_apply, kummerCochar_sq K ζ hζ c, Pi.zero_apply, zero_add]
  rw [kummerCochar_apply K ζ hζ u hσ, hzero]


/-- **`y` is (on `G_K`) a Kummer cochain.**  This is the Kummer correspondence
`Work.SSGRoute.exists_kummerChar_of_additive_locConst`, transported to the cochain
`kummerCochar`: under the node's hypotheses (additivity and local constancy on `G_K`) the data `y`
is the Kummer cochain of some `h ∈ Kˣ`, so hypothesis (i) of the Kummer core is automatic. -/
theorem exists_kummerCochar_of_node_data (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y) :
    ∃ h : (↥K)ˣ, ∀ σ ∈ K.fixingSubgroup, y σ = kummerCochar K ζ hζ h σ := by
  obtain ⟨h, hh⟩ := Work.SSGRoute.exists_kummerChar_of_additive_locConst k Ω K ζ hζ y hy hyc
  refine ⟨h, fun σ hσ => ?_⟩
  rw [kummerCochar_apply K ζ hζ h hσ]
  exact hh σ hσ

end KummerBridge

section NodeCochar

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- A primitive `2`-nd root of unity in `Ω` lying in `K` is primitive in `K`. -/
lemma isPrimitiveRoot_subtype_of_mem {K : IntermediateField k Ω} {ζ : Ω} (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ 2) : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
    (algebraMap ↥K Ω).injective

end NodeCochar

section NodeCochar2

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

/-- The Kummer cochain of `b`, with the root of unity taken in `Ω`. -/
noncomputable def nodeKummerCochar (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) : (Ω ≃ₐ[k] Ω) → ZMod 2 :=
  kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b

end NodeCochar2

section NodeCochar3

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

lemma nodeKummerCochar_add (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) :
    ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      nodeKummerCochar K ζ hζK hζ b (g * h) =
        nodeKummerCochar K ζ hζK hζ b g + nodeKummerCochar K ζ hζK hζ b h :=
  kummerCochar_add K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b

lemma nodeKummerCochar_locConst (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2) (b : (↥K)ˣ) :
    SSGRoute.IsLocConstOn K.fixingSubgroup (nodeKummerCochar K ζ hζK hζ b) :=
  kummerCochar_locConst K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b

end NodeCochar3

end Work.SSGRoute
