import Mathlib
import Submission.Work.CFTLib.splitSetOf_density
import Submission.Work.CFTLib.splitsCompletelySet
import Submission.Work.CFTLib.dirichletDensity_utils
import Submission.Work.CFTLib.finite_sdiff_inertiaDegIn_splitsCompletelySet
import Submission.Work.CFTLib.hasDirichletDensity_splitsCompletelySet
import Submission.Work.Tower.Unramified.compositum_splits_completely_alt
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

namespace Work.CFTLib

open NumberField

/-! ### Auxiliary lemmas about completely split primes -/

/-- The compositum of two Galois intermediate fields (of a common extension) is Galois. -/
theorem isGalois_sup {K A : Type*} [Field K] [Field A] [Algebra K A]
    (L₁ L₂ : IntermediateField K A) [IsGalois K ↥L₁] [IsGalois K ↥L₂] :
    IsGalois K ↥(L₁ ⊔ L₂) := by
  have hsup : (L₁ ⊔ L₂ : IntermediateField K A) = ⨆ i : Bool, (if i then L₁ else L₂) := by
    rw [iSup_bool_eq]; simp
  haveI hN : ∀ i : Bool, Normal K ↥(if i then L₁ else L₂) := by
    intro i; cases i <;> simp <;> infer_instance
  haveI hS : ∀ i : Bool, Algebra.IsSeparable K ↥(if i then L₁ else L₂) := by
    intro i; cases i <;> simp <;> infer_instance
  haveI hNorm : Normal K ↥(L₁ ⊔ L₂) :=
    hsup ▸ IntermediateField.normal_iSup K A (fun i : Bool => if i then L₁ else L₂)
  haveI hSep : Algebra.IsSeparable K ↥(L₁ ⊔ L₂) :=
    hsup ▸ IntermediateField.isSeparable_iSup K A (t := fun i : Bool => if i then L₁ else L₂)
  infer_instance

/-- Two sets of primes of a number field with the same Dirichlet density have equal density
values. -/
theorem eq_of_hasDirichletDensity {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ₁ δ₂ : ℝ}
    (h₁ : NumberField.Set.HasDirichletDensity S δ₁)
    (h₂ : NumberField.Set.HasDirichletDensity S δ₂) : δ₁ = δ₂ :=
  h₁.dirichletDensity_eq.symm.trans h₂.dirichletDensity_eq

/-- The primes splitting completely in a compositum `L₁ ⊔ L₂` are exactly those splitting
completely in both `L₁` and `L₂` (complete splitting ascends to, and descends from, the
compositum). -/
theorem splitsCompletelySet_sup_eq_inter {K A : Type*} [Field K] [NumberField K] [Field A]
    [NumberField A] [Algebra K A] (L₁ L₂ : IntermediateField K A) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] :
    splitsCompletelySet (L₁ ⊔ L₂) = splitsCompletelySet L₁ ∩ splitsCompletelySet L₂ := by
  haveI hfd : FiniteDimensional K ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  ext v
  simp only [Set.mem_inter_iff, mem_splitsCompletelySet]
  constructor
  · intro hv
    exact ⟨Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom v.asIdeal
        (IntermediateField.inclusion le_sup_left) hv,
      Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom v.asIdeal
        (IntermediateField.inclusion le_sup_right) hv⟩
  · rintro ⟨h₁, h₂⟩
    exact Work.Tower.Unramified.compositum_splits_completely_alt h₁ h₂

/-! ### The main theorem -/

/-- Two finite Galois subextensions of a common field whose sets of primes of inertia degree `1`
coincide are equal.

(The `f = 1` primes of the compositum `L₁ ⊔ L₂` need only agree with `S(L₁) ∩ S(L₂)` outside the
(finite) set of primes ramifying in the compositum, using
`splitSetOf_density` and `hasDirichletDensity_of_symmDiff_finite`.  Density then forces
`[L₁ ⊔ L₂ : K] = [L₁ : K]`.) -/
theorem splitSet_determines_field {K A : Type} [Field K] [NumberField K] [Field A] [NumberField A]
    [Algebra K A] (L₁ L₂ : IntermediateField K A) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsGalois K ↥L₁] [IsGalois K ↥L₂] [NumberField ↥L₁]
    [NumberField ↥L₂]
    (h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
            Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L₁) = 1} =
         {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
            Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L₂) = 1}) :
    L₁ = L₂ := by
  classical
  haveI hfdM : FiniteDimensional K ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  haveI hgalM : IsGalois K ↥(L₁ ⊔ L₂) := isGalois_sup L₁ L₂
  -- pointwise form of the hypothesis on the inertia-degree-one sets
  have hmem : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L₁) = 1) ↔
        (Ideal.inertiaDegIn v.asIdeal (𝓞 ↥L₂) = 1) := by
    intro v
    simpa using Set.ext_iff.mp h v
  -- the densities of the completely split sets
  have hd1 := hasDirichletDensity_splitsCompletelySet L₁
  have hd2 := hasDirichletDensity_splitsCompletelySet L₂
  have hdM := hasDirichletDensity_splitsCompletelySet (L₁ ⊔ L₂)
  have hsplit := splitsCompletelySet_sup_eq_inter L₁ L₂
  -- density of the split set of the compositum, computed *via* `L₁`
  have hdM1 : NumberField.Set.HasDirichletDensity (splitsCompletelySet (L₁ ⊔ L₂))
      (1 / (Module.finrank K ↥L₁ : ℝ)) := by
    refine NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite ?_ ?_ hd1
    · rw [hsplit]
      refine (finite_sdiff_inertiaDegIn_splitsCompletelySet L₂).subset ?_
      rintro v ⟨hv1, hvnot⟩
      have hv2 : v ∉ splitsCompletelySet L₂ := fun h2 => hvnot ⟨hv1, h2⟩
      exact ⟨(hmem v).mp (inertiaDegIn_eq_one_of_splitsCompletelyIn L₁ hv1), hv2⟩
    · rw [hsplit]
      exact Set.Finite.subset Set.finite_empty
        (by rintro v ⟨⟨h1, -⟩, h2⟩; exact h2 h1)
  -- density of the split set of the compositum, computed *via* `L₂`
  have hdM2 : NumberField.Set.HasDirichletDensity (splitsCompletelySet (L₁ ⊔ L₂))
      (1 / (Module.finrank K ↥L₂ : ℝ)) := by
    refine NK.BauerGeneral.hasDirichletDensity_of_symmDiff_finite ?_ ?_ hd2
    · rw [hsplit]
      refine (finite_sdiff_inertiaDegIn_splitsCompletelySet L₁).subset ?_
      rintro v ⟨hv2, hvnot⟩
      have hv1 : v ∉ splitsCompletelySet L₁ := fun h1 => hvnot ⟨h1, hv2⟩
      exact ⟨(hmem v).mpr (inertiaDegIn_eq_one_of_splitsCompletelyIn L₂ hv2), hv1⟩
    · rw [hsplit]
      exact Set.Finite.subset Set.finite_empty
        (by rintro v ⟨⟨-, h2⟩, h1⟩; exact h1 h2)
  -- comparing the two densities forces the degrees to agree
  have hfr1 : Module.finrank K ↥L₁ = Module.finrank K ↥(L₁ ⊔ L₂) := by
    have h1 : (1 : ℝ) / (Module.finrank K ↥L₁ : ℝ) =
        (1 : ℝ) / (Module.finrank K ↥(L₁ ⊔ L₂) : ℝ) :=
      eq_of_hasDirichletDensity hdM1 hdM
    exact Nat.cast_injective (inv_inj.mp (by simpa only [one_div] using h1))
  have hfr2 : Module.finrank K ↥L₂ = Module.finrank K ↥(L₁ ⊔ L₂) := by
    have h1 : (1 : ℝ) / (Module.finrank K ↥L₂ : ℝ) =
        (1 : ℝ) / (Module.finrank K ↥(L₁ ⊔ L₂) : ℝ) :=
      eq_of_hasDirichletDensity hdM2 hdM
    exact Nat.cast_injective (inv_inj.mp (by simpa only [one_div] using h1))
  have hLM1 : L₁ = L₁ ⊔ L₂ := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hfr1
  have hLM2 : L₂ = L₁ ⊔ L₂ := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hfr2
  exact hLM1.trans hLM2.symm

end Work.CFTLib
