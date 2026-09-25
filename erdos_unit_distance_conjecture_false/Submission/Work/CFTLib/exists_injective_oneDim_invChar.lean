import Mathlib
import Submission.Work.CFTLib.splitSetOf_density
import Submission.Work.CFTLib.splitSet_determines_field
import Submission.Work.CFTLib.splitSet_eq_imp_proportional
import Submission.Work.CFTLib.InvCharSetup
import Submission.Work.CFTLib.card_oneDim_submodules
import Submission.Work.CFTLib.InvCharCrux
import Submission.Work.CFTLib.InvCharCrux.fixingSubgroup_normal_of_classField
import Submission.Work.CFTLib.ClassGroupTransport.exists_classGroup_mulEquiv
import Submission.Work.CFTLib.PGroupConjTrivial.commutator_mem_of_isPGroup
import Submission.Work.CFTLib.PGroupConjTrivial.card_quotient_fixingSubgroup
import Submission.Work.CFTLib.PGroupConjTrivial.exists_char_ker_eq_fixingSubgroup

namespace Work.CFTLib

open NumberField CategoryTheory
open scoped Classical

/-- The additive character module `Hom(Cl(𝓞 K), 𝔽_p)`. -/
abbrev CharHom (p : ℕ) (K : Type*) [Field K] [NumberField K] : Type _ :=
  AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p)

/-- The subgroup `N = ker (restrictNormalHom K) = Gal(K'/K) ≤ Gal(K'/F)`. -/
noncomputable abbrev Nker (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] [Normal F K] : Subgroup (K' ≃ₐ[F] K') :=
  (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker

/-- The type of one-dimensional subspaces. -/
abbrev OneDim (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :=
  {S : Submodule (ZMod p) V // Module.finrank (ZMod p) S = 1}

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
  [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
  [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
  [IsGalois F K']
  (p : ℕ) [Fact p.Prime]
  (hHCF : CFTLib.PClassFieldArtin)
  (hmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
      [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[K] L) →
      CFTLib.IsUnramified K L → Nonempty (L →ₐ[K] K'))

/-- The class-field image in `K'` of a nonzero invariant character `χ`, chosen once and for all
from `Work.CFTLib.InvCharCrux.exists_classFieldImage`. -/
noncomputable def clsField (χ : clInvariantChar F K p) (hχ : χ ≠ 0) : IntermediateField K K' :=
  Classical.choose (InvCharCrux.exists_classFieldImage p hHCF hmax χ hχ)

theorem clsField_spec (χ : clInvariantChar F K p) (hχ : χ ≠ 0) :
    FiniteDimensional K ↥(clsField p hHCF hmax χ hχ) ∧
    NumberField ↥(clsField p hHCF hmax χ hχ) ∧
    IsGalois K ↥(clsField p hHCF hmax χ hχ) ∧
    Module.finrank K ↥(clsField p hHCF hmax χ hχ) = p ∧
    Work.Tower.IsUnramifiedExtensionForallPrimes K ↥(clsField p hHCF hmax χ hχ) ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(clsField p hHCF hmax χ hχ)) = 1 ↔
        (χ : CharHom p K) (Additive.ofMul (primeCls v)) = 0) :=
  Classical.choose_spec (InvCharCrux.exists_classFieldImage p hHCF hmax χ hχ)

/-! ## One-dimensional subspaces and their chosen generators -/

theorem exists_mem_ne_zero_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (S : Submodule (ZMod p) V) (hS : Module.finrank (ZMod p) S = 1) : ∃ χ ∈ S, χ ≠ 0 := by
  have hne : S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot (ZMod p) V] at hS
    exact one_ne_zero hS.symm
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

/-- A chosen nonzero element of a one-dimensional subspace. -/
noncomputable def chrOf (S : OneDim p (clInvariantChar F K p)) : clInvariantChar F K p :=
  Classical.choose (exists_mem_ne_zero_of_finrank_eq_one (p := p)
    (V := clInvariantChar F K p) (S := S.1) (hS := S.2))

theorem chrOf_mem (S : OneDim p (clInvariantChar F K p)) : chrOf p S ∈ S.1 := by
  unfold chrOf
  exact (Classical.choose_spec (exists_mem_ne_zero_of_finrank_eq_one (p := p)
    (V := clInvariantChar F K p) (S := S.1) (hS := S.2))).1

theorem chrOf_ne_zero (S : OneDim p (clInvariantChar F K p)) : chrOf p S ≠ 0 := by
  unfold chrOf
  exact (Classical.choose_spec (exists_mem_ne_zero_of_finrank_eq_one (p := p)
    (V := clInvariantChar F K p) (S := S.1) (hS := S.2))).2

/-- The chosen generator of `S` is `Gal(K/F)`-invariant. -/
theorem chrOf_invariant (S : OneDim p (clInvariantChar F K p)) (g : K ≃ₐ[F] K)
    (c : ClassGroup (𝓞 K)) :
    (chrOf p S : CharHom p K) (Additive.ofMul (clEquiv F K g c)) =
      (chrOf p S : CharHom p K) (Additive.ofMul c) :=
  (chrOf p S).2 g c


/-! ## The class field and its fixing subgroup attached to a one-dimensional subspace -/

/-- The class field of the chosen generator of `S`, inside `K'`. -/
noncomputable def MOf (S : OneDim p (clInvariantChar F K p)) : IntermediateField K K' :=
  clsField p hHCF hmax (chrOf p S) (chrOf_ne_zero p S)

theorem MOf_spec (S : OneDim p (clInvariantChar F K p)) :
    FiniteDimensional K ↥(MOf p hHCF hmax S) ∧
    NumberField ↥(MOf p hHCF hmax S) ∧
    IsGalois K ↥(MOf p hHCF hmax S) ∧
    Module.finrank K ↥(MOf p hHCF hmax S) = p ∧
    Work.Tower.IsUnramifiedExtensionForallPrimes K ↥(MOf p hHCF hmax S) ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(MOf p hHCF hmax S)) = 1 ↔
        (chrOf p S : CharHom p K) (Additive.ofMul (primeCls v)) = 0) := by
  unfold MOf
  exact clsField_spec p hHCF hmax (chrOf p S) (chrOf_ne_zero p S)

theorem MOf_finiteDimensional (S : OneDim p (clInvariantChar F K p)) :
    FiniteDimensional K ↥(MOf p hHCF hmax S) := (MOf_spec p hHCF hmax S).1

theorem MOf_numberField (S : OneDim p (clInvariantChar F K p)) :
    NumberField ↥(MOf p hHCF hmax S) := (MOf_spec p hHCF hmax S).2.1

theorem MOf_isGalois (S : OneDim p (clInvariantChar F K p)) :
    IsGalois K ↥(MOf p hHCF hmax S) := (MOf_spec p hHCF hmax S).2.2.1

theorem MOf_finrank (S : OneDim p (clInvariantChar F K p)) :
    Module.finrank K ↥(MOf p hHCF hmax S) = p := (MOf_spec p hHCF hmax S).2.2.2.1

theorem MOf_unramified (S : OneDim p (clInvariantChar F K p)) :
    Work.Tower.IsUnramifiedExtensionForallPrimes K ↥(MOf p hHCF hmax S) :=
  (MOf_spec p hHCF hmax S).2.2.2.2.1

theorem MOf_law (S : OneDim p (clInvariantChar F K p))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(MOf p hHCF hmax S)) = 1 ↔
      (chrOf p S : CharHom p K) (Additive.ofMul (primeCls v)) = 0 :=
  (MOf_spec p hHCF hmax S).2.2.2.2.2 v

/-- The fixing subgroup of the class field, inside `Gal(K'/F)`. -/
noncomputable def HOf (S : OneDim p (clInvariantChar F K p)) : Subgroup (K' ≃ₐ[F] K') :=
  (IntermediateField.restrictScalars F (MOf p hHCF hmax S)).fixingSubgroup

theorem HOf_le (S : OneDim p (clInvariantChar F K p)) : HOf p hHCF hmax S ≤ Nker F K K' := by
  intro g hg
  rw [Nker, MonoidHom.mem_ker]
  have hfix : ∀ x ∈ (MOf p hHCF hmax S : Set K'), g x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ g).mp hg
  change g.restrictNormal K = 1
  apply AlgEquiv.ext
  intro x
  apply (algebraMap K K').injective
  rw [AlgEquiv.restrictNormal_commutes g K x, AlgEquiv.one_apply]
  exact hfix _ ((MOf p hHCF hmax S).algebraMap_mem x)

theorem HOf_normal (S : OneDim p (clInvariantChar F K p)) : (HOf p hHCF hmax S).Normal := by
  haveI hfd := MOf_finiteDimensional p hHCF hmax S
  haveI hgal := MOf_isGalois p hHCF hmax S
  refine InvCharCrux.fixingSubgroup_normal_of_classField (F := F) (K := K) (K' := K') p
    (MOf p hHCF hmax S) (InvCharCrux.toMulChar p (chrOf p S)) ?_ ?_ ?_ ?_
  · exact InvCharCrux.toMulChar_ne_one p _ (chrOf_ne_zero p S)
  · intro v
    rw [InvCharCrux.toMulChar_eq_one_iff]
    exact MOf_law p hHCF hmax S v
  · exact MOf_unramified p hHCF hmax S
  · intro h c
    show InvCharCrux.toMulChar p (chrOf p S) (clEquiv F K h c) =
      InvCharCrux.toMulChar p (chrOf p S) c
    rw [InvCharCrux.toMulChar_apply, InvCharCrux.toMulChar_apply]
    exact congrArg Multiplicative.ofAdd (chrOf_invariant p S h c)


/-! ## The invariant character attached to a one-dimensional subspace -/

theorem multiplicative_toAdd_eq_zero_iff {α : Type*} [AddGroup α] (x : Multiplicative α) :
    x.toAdd = 0 ↔ x = 1 :=
  ⟨fun h => Multiplicative.toAdd.injective (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

/-- A surjective character `N →* Multiplicative (ZMod p)` with kernel the fixing subgroup of the
class field of `S`. -/
noncomputable def phiOf (S : OneDim p (clInvariantChar F K p)) :
    Nker F K K' →* Multiplicative (ZMod p) := by
  haveI hfd := MOf_finiteDimensional p hHCF hmax S
  haveI hgal := MOf_isGalois p hHCF hmax S
  exact Classical.choose (PGroupConjTrivial.exists_char_ker_eq_fixingSubgroup (F := F) (K := K)
    (K' := K') p (MOf p hHCF hmax S) (MOf_finrank p hHCF hmax S))

theorem phiOf_spec (S : OneDim p (clInvariantChar F K p)) :
    (phiOf p hHCF hmax S).ker = (HOf p hHCF hmax S).subgroupOf (Nker F K K') ∧
    Function.Surjective (phiOf p hHCF hmax S) := by
  haveI hfd := MOf_finiteDimensional p hHCF hmax S
  haveI hgal := MOf_isGalois p hHCF hmax S
  exact Classical.choose_spec (PGroupConjTrivial.exists_char_ker_eq_fixingSubgroup (F := F) (K := K)
    (K' := K') p (MOf p hHCF hmax S) (MOf_finrank p hHCF hmax S))

theorem phiOf_ker (S : OneDim p (clInvariantChar F K p)) :
    (phiOf p hHCF hmax S).ker = (HOf p hHCF hmax S).subgroupOf (Nker F K K') :=
  (phiOf_spec p hHCF hmax S).1

theorem phiOf_surjective (S : OneDim p (clInvariantChar F K p)) :
    Function.Surjective (phiOf p hHCF hmax S) := (phiOf_spec p hHCF hmax S).2

theorem psiOf_mem (hG' : IsPGroup p (K' ≃ₐ[F] K')) (S : OneDim p (clInvariantChar F K p)) :
    MonoidHom.toAdditive (phiOf p hHCF hmax S) ∈ invCharSubmodule p (Nker F K K') := by
  intro g n
  haveI hHn := HOf_normal p hHCF hmax S
  haveI hfd := MOf_finiteDimensional p hHCF hmax S
  haveI hgal := MOf_isGalois p hHCF hmax S
  have hcard := PGroupConjTrivial.card_quotient_fixingSubgroup (F := F) (K := K) (K' := K') p
    (MOf p hHCF hmax S) (MOf_finrank p hHCF hmax S)
  have hcom := PGroupConjTrivial.commutator_mem_of_isPGroup (G := K' ≃ₐ[F] K') (p := p) hG'
    (Nker F K K') (HOf p hHCF hmax S) (HOf_le p hHCF hmax S) hcard g n
  have key : ∀ (Q : g⁻¹ * (n : K' ≃ₐ[F] K') * g ∈ Nker F K K'),
      (MonoidHom.toAdditive (phiOf p hHCF hmax S))
        (Additive.ofMul (⟨g⁻¹ * (n : K' ≃ₐ[F] K') * g, Q⟩ : Nker F K K'))
        = (MonoidHom.toAdditive (phiOf p hHCF hmax S)) (Additive.ofMul n) := by
    intro Q
    let c : Nker F K K' :=
      ⟨g⁻¹ * (n : K' ≃ₐ[F] K') * g * (n : K' ≃ₐ[F] K')⁻¹,
        (Nker F K K').mul_mem Q ((Nker F K K').inv_mem n.2)⟩
    have hc : c ∈ (phiOf p hHCF hmax S).ker := by
      rw [phiOf_ker p hHCF hmax S, Subgroup.mem_subgroupOf]
      exact hcom
    have heq : (⟨g⁻¹ * (n : K' ≃ₐ[F] K') * g, Q⟩ : Nker F K K') = c * n := by
      apply Subtype.ext
      change g⁻¹ * (n : K' ≃ₐ[F] K') * g
        = (g⁻¹ * (n : K' ≃ₐ[F] K') * g * (n : K' ≃ₐ[F] K')⁻¹) * (n : K' ≃ₐ[F] K')
      group
    show ((phiOf p hHCF hmax S) (⟨g⁻¹ * (n : K' ≃ₐ[F] K') * g, Q⟩ : Nker F K K')).toAdd
      = ((phiOf p hHCF hmax S) n).toAdd
    exact congrArg Multiplicative.toAdd
      (by rw [heq, map_mul, MonoidHom.mem_ker.mp hc, one_mul])
  exact key _

/-- The character of `N` attached to `S`, as an element of `invCharSubmodule p N`. -/
noncomputable def psiOf (hG' : IsPGroup p (K' ≃ₐ[F] K')) (S : OneDim p (clInvariantChar F K p)) :
    invCharSubmodule p (Nker F K K') :=
  ⟨MonoidHom.toAdditive (phiOf p hHCF hmax S), psiOf_mem p hHCF hmax hG' S⟩

theorem psiOf_kernel (hG' : IsPGroup p (K' ≃ₐ[F] K')) (S : OneDim p (clInvariantChar F K p))
    (x : Nker F K K') :
    (psiOf p hHCF hmax hG' S : Additive (Nker F K K') →+ ZMod p) (Additive.ofMul x) = 0 ↔
      (x : K' ≃ₐ[F] K') ∈ HOf p hHCF hmax S := by
  unfold psiOf
  show ((phiOf p hHCF hmax S) x).toAdd = 0 ↔ (x : K' ≃ₐ[F] K') ∈ HOf p hHCF hmax S
  rw [multiplicative_toAdd_eq_zero_iff, ← MonoidHom.mem_ker, phiOf_ker p hHCF hmax S,
    Subgroup.mem_subgroupOf]

theorem psiOf_ne_zero (hG' : IsPGroup p (K' ≃ₐ[F] K')) (S : OneDim p (clInvariantChar F K p)) :
    psiOf p hHCF hmax hG' S ≠ 0 := by
  intro h
  have hφ1 : phiOf p hHCF hmax S = 1 := by
    ext n
    show (phiOf p hHCF hmax S) n = 1
    rw [← multiplicative_toAdd_eq_zero_iff]
    have h2 : ((psiOf p hHCF hmax hG' S : Additive (Nker F K K') →+ ZMod p)
        (Additive.ofMul n)) = 0 := by
      rw [h]; simp
    exact h2
  obtain ⟨n, hn⟩ := phiOf_surjective p hHCF hmax S (Multiplicative.ofAdd (1 : ZMod p))
  rw [hφ1] at hn
  have h01 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective (by simpa using hn.symm)
  exact one_ne_zero h01


/-- The map on one-dimensional subspaces. -/
noncomputable def fOf (hG' : IsPGroup p (K' ≃ₐ[F] K')) :
    OneDim p (clInvariantChar F K p) → OneDim p (invCharSubmodule p (Nker F K K')) :=
  fun S => ⟨Submodule.span (ZMod p) {psiOf p hHCF hmax hG' S},
    finrank_span_singleton (K := ZMod p) (V := invCharSubmodule p (Nker F K K'))
      (psiOf_ne_zero p hHCF hmax hG' S)⟩

set_option maxHeartbeats 3000000 in
theorem fOf_injective (hG' : IsPGroup p (K' ≃ₐ[F] K')) :
    Function.Injective (fOf (F := F) (K := K) (K' := K') p hHCF hmax hG' :
      OneDim p (clInvariantChar F K p) → OneDim p (invCharSubmodule p (Nker F K K'))) := by
  intro S S' hSS'
  have hspan : Submodule.span (ZMod p) {psiOf p hHCF hmax hG' S}
      = Submodule.span (ZMod p) {psiOf p hHCF hmax hG' S'} := by
    have h := congrArg Subtype.val hSS'
    simpa only [fOf] using h
  have hmem : psiOf p hHCF hmax hG' S' ∈
      Submodule.span (ZMod p) {psiOf p hHCF hmax hG' S} := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hmem
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hu
    exact psiOf_ne_zero p hHCF hmax hG' S' hu.symm
  have hvalFun : ∀ y : Nker F K K',
      (psiOf p hHCF hmax hG' S' : Additive (Nker F K K') →+ ZMod p) (Additive.ofMul y)
        = u • ((psiOf p hHCF hmax hG' S : Additive (Nker F K K') →+ ZMod p)
          (Additive.ofMul y)) := by
    intro y
    have hcong := congrArg (fun f : Additive (Nker F K K') →+ ZMod p => f (Additive.ofMul y))
      (congrArg Subtype.val hu)
    simpa using hcong.symm
  have hH : (IntermediateField.restrictScalars F (MOf p hHCF hmax S)).fixingSubgroup
      = (IntermediateField.restrictScalars F (MOf p hHCF hmax S')).fixingSubgroup := by
    show HOf p hHCF hmax S = HOf p hHCF hmax S'
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ Nker F K K' := HOf_le p hHCF hmax S hx
      have h1 : (psiOf p hHCF hmax hG' S : Additive (Nker F K K') →+ ZMod p)
          (Additive.ofMul (⟨x, hxN⟩ : Nker F K K')) = 0 :=
        (psiOf_kernel p hHCF hmax hG' S ⟨x, hxN⟩).mpr hx
      have h2 : (psiOf p hHCF hmax hG' S' : Additive (Nker F K K') →+ ZMod p)
          (Additive.ofMul (⟨x, hxN⟩ : Nker F K K')) = 0 := by
        rw [hvalFun ⟨x, hxN⟩, h1, smul_zero]
      exact (psiOf_kernel p hHCF hmax hG' S' ⟨x, hxN⟩).mp h2
    · intro x hx
      have hxN : x ∈ Nker F K K' := HOf_le p hHCF hmax S' hx
      have h1 : (psiOf p hHCF hmax hG' S' : Additive (Nker F K K') →+ ZMod p)
          (Additive.ofMul (⟨x, hxN⟩ : Nker F K K')) = 0 :=
        (psiOf_kernel p hHCF hmax hG' S' ⟨x, hxN⟩).mpr hx
      have h2 : (psiOf p hHCF hmax hG' S : Additive (Nker F K K') →+ ZMod p)
          (Additive.ofMul (⟨x, hxN⟩ : Nker F K K')) = 0 := by
        rw [hvalFun ⟨x, hxN⟩] at h1
        exact (smul_eq_zero.mp h1).resolve_left hu_ne
      exact (psiOf_kernel p hHCF hmax hG' S ⟨x, hxN⟩).mp h2
  have hM : MOf p hHCF hmax S = MOf p hHCF hmax S' := by
    apply IntermediateField.restrictScalars_injective F
    rw [← IsGalois.fixedField_fixingSubgroup
        (IntermediateField.restrictScalars F (MOf p hHCF hmax S)),
      ← IsGalois.fixedField_fixingSubgroup
        (IntermediateField.restrictScalars F (MOf p hHCF hmax S')), hH]
  haveI hfdS := MOf_finiteDimensional p hHCF hmax S
  haveI hnfS := MOf_numberField p hHCF hmax S
  haveI hgalS := MOf_isGalois p hHCF hmax S
  have hCF : ∀ (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)), χ ≠ 1 →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L),
        IsGalois K L ∧ Module.finrank K L = p ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 ↔
            χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1) := by
    intro χ hχ
    obtain ⟨L, hF, hNF, hAlg, hFD, hgal, hfr, _hunr, hlaw⟩ := hHCF K p χ hχ
    exact ⟨L, hF, hNF, hAlg, hFD, hgal, hfr, fun v => hlaw v⟩
  have hlaw1 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(MOf p hHCF hmax S)) = 1 ↔
        InvCharCrux.toMulChar p (chrOf p S) (primeCls v) = 1) := by
    intro v
    rw [InvCharCrux.toMulChar_eq_one_iff]
    exact MOf_law p hHCF hmax S v
  have hlaw2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(MOf p hHCF hmax S)) = 1 ↔
        InvCharCrux.toMulChar p (chrOf p S') (primeCls v) = 1) := by
    intro v
    rw [hM, InvCharCrux.toMulChar_eq_one_iff]
    exact MOf_law p hHCF hmax S' v
  obtain ⟨a, ha⟩ := splitSet_eq_imp_proportional p hCF
    (InvCharCrux.toMulChar_ne_one p _ (chrOf_ne_zero p S))
    (InvCharCrux.toMulChar_ne_one p _ (chrOf_ne_zero p S'))
    (MOf_finrank p hHCF hmax S) (MOf_finrank p hHCF hmax S) hlaw1 hlaw2 rfl
  have hprop : chrOf p S = (a : ZMod p) • chrOf p S' := by
    apply Subtype.ext
    ext x
    have hh := congrArg Multiplicative.toAdd (ha (Additive.toMul x))
    rw [toAdd_pow] at hh
    show (chrOf p S : CharHom p K) (Additive.ofMul (Additive.toMul x))
      = (a : ZMod p) • ((chrOf p S' : CharHom p K) (Additive.ofMul (Additive.toMul x)))
    rw [nsmul_eq_mul] at hh
    rw [smul_eq_mul]
    exact hh
  have ha_ne : (a : ZMod p) ≠ 0 := by
    intro h0
    have hz : chrOf p S = 0 := by rw [hprop, h0, zero_smul]
    exact chrOf_ne_zero p S hz
  have hprop' : chrOf p S' = (a : ZMod p)⁻¹ • chrOf p S := by
    rw [hprop, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]
  have hS : S.1 = Submodule.span (ZMod p) {chrOf p S} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (K := ZMod p) (V := clInvariantChar F K p)
      (S := S.1) (w := chrOf p S) S.2 (chrOf_mem p S) (chrOf_ne_zero p S)
  have hS' : S'.1 = Submodule.span (ZMod p) {chrOf p S'} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (K := ZMod p) (V := clInvariantChar F K p)
      (S := S'.1) (w := chrOf p S') S'.2 (chrOf_mem p S') (chrOf_ne_zero p S')
  have hspanEq : Submodule.span (ZMod p) {chrOf p S} = Submodule.span (ZMod p) {chrOf p S'} := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff, hprop]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (chrOf p S')))
    · rw [Submodule.span_le, Set.singleton_subset_iff, hprop']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (chrOf p S)))
  apply Subtype.ext
  rw [hS, hS', hspanEq]

/-- **The crux injection for `invChar_le_invCharSubmodule`** (with the `p`-group hypothesis on
`Gal(K'/F)`, which the caller supplies).

There is an injection from the type of one-dimensional subspaces of `clInvariantChar F K p` into the
type of one-dimensional subspaces of `invCharSubmodule p N`,
`N = ker (restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K))`.

Construction: for a nonzero `χ ∈ clInvariantChar F K p`, view it as a multiplicative character
`Cl(𝓞 K) →* Multiplicative (ZMod p)`, take its class field `L` (given by `hHCF`), embed `L` into
`K'` over `K` (given by `hmax`) with image `L₀ ≤ K'`, and map `χ` to the character of `N` with
kernel `Gal(K'/L₀) ≤ N`.

## Why this works

* `χ ∈ clInvariantChar` is `G := Gal(K/F)`-invariant, so for `g ∈ G'` the conjugate `g L₀` is again
  a class field of `χ`, hence has the same split set as `L₀`; both are finite Galois over `K` inside
  `K'`, so `splitSet_determines_field` gives `g L₀ = L₀`.  Thus `L₀` is `G'`-stable and
  `H := Gal(K'/L₀) ◁ G'`.
* `N/H ≅ Gal(L₀/K) ≅ ℤ/p`, and **any** character `φ : N → ℤ/p` with kernel `H` is automatically
  `G'`-invariant: the conjugation action of `G'` on `N/H` factors through `G = G'/N` (an element of
  `N` acts trivially since `N/H` is abelian), and `G` is a quotient of the `p`-group `G'` (using
  the hypothesis `hG'`), while `Aut(ℤ/p)` has order `p - 1`; since `gcd(p, p-1) = 1` the action is
  trivial.  No Artin equivariance is needed.
* Well-definedness on one-dimensional subspaces uses `splitSet_determines_field`; injectivity uses
  `splitSet_eq_imp_proportional` (equal class fields ⟹ equal split sets ⟹ `χ, χ'` proportional).

(Existing helper work: `Work.CFTLib.InvCharCrux.exists_classFieldImage` produces `L₀ ≤ K'` from
`hHCF` and `hmax`; `Work.CFTLib.InvCharCrux.fixingSubgroup_normal_of_classField` gives the
normality of `Gal(K'/L₀)`.) -/
theorem exists_injective_oneDim_invChar (hHCF : CFTLib.PClassFieldArtin)
    {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (p : ℕ) [Fact p.Prime] (hG' : IsPGroup p (K' ≃ₐ[F] K'))
    (hmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
      [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[K] L) →
      CFTLib.IsUnramified K L → Nonempty (L →ₐ[K] K')) :
    ∃ f : {S : Submodule (ZMod p) (Work.CFTLib.clInvariantChar F K p) //
              Module.finrank (ZMod p) S = 1} →
            {S : Submodule (ZMod p) (Work.CFTLib.invCharSubmodule p
                (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) //
              Module.finrank (ZMod p) S = 1},
      Function.Injective f :=
  ⟨fOf (F := F) (K := K) (K' := K') p hHCF hmax hG', fOf_injective (F := F) (K := K) (K' := K') p hHCF hmax hG'⟩

end Work.CFTLib
