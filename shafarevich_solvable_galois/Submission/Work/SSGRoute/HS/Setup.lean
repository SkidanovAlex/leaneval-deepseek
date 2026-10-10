import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.LTDDefs.H2locAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The semidirect decomposition `D_A = I · C` of a decomposition group

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois subextension,
`A` a place of `Ω`, `D = decomp k A` its decomposition group, `I ≤ D` a subgroup normalised by
`D`, `σ ∈ D` of infinite order and `C = closure (zpowers σ)` the procyclic closed subgroup it
generates.  Assume `D ≤ I ⊔ C` and `I ⊓ C = ⊥`.  Then `D = I · C` and the decomposition
`d = i * γ` (`i ∈ I`, `γ ∈ C`) is unique, so `D` is the semidirect product `I ⋊ C` with
`C ≅ Ẑ`.

This file builds that structure (`ip`, `proj`, and their basic calculus), which is the group-theoretic
input of the Hochschild–Serre two-row decomposition for a decomposition group.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HS

noncomputable section

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The decomposition group `D_A = decomp k A` is closed in the Krull topology. -/
theorem isClosed_decomp (A : ValuationSubring Ω) :
    IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A

/-- `C = closure (zpowers σ) ≤ D` when `σ ∈ D` and `D` is closed. -/
theorem CC_le_DD (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A) :
    Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
  Subgroup.topologicalClosure_minimal _
    (Subgroup.zpowers_le.mpr hσ) (isClosed_decomp A)

/-- **Existence of the factorisation `d = i * γ`** for `d ∈ D`, given `D ≤ I ⊔ C`. -/
theorem exists_factor (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hC : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    {d : Ω ≃ₐ[k] Ω} (hd : d ∈ SSGRoute.decomp k A) :
    ∃ i ∈ I, ∃ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ), i * γ = d := by
  let S : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {x | ∃ i ∈ I, ∃ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ),
        i * γ = x}
      one_mem' := ⟨1, I.one_mem, 1, (Subgroup.topologicalClosure _).one_mem, by rw [one_mul]⟩
      mul_mem' := by
        rintro x y ⟨i₁, hi₁, γ₁, hγ₁, rfl⟩ ⟨i₂, hi₂, γ₂, hγ₂, rfl⟩
        exact ⟨i₁ * (γ₁ * i₂ * γ₁⁻¹), I.mul_mem hi₁ (hnorm γ₁ (hC hγ₁) i₂ hi₂),
          γ₁ * γ₂, (Subgroup.topologicalClosure _).mul_mem hγ₁ hγ₂, by group⟩
      inv_mem' := by
        rintro x ⟨i, hi, γ, hγ, rfl⟩
        refine ⟨γ⁻¹ * i⁻¹ * γ, ?_, γ⁻¹, (Subgroup.topologicalClosure _).inv_mem hγ, by group⟩
        have h := hnorm γ⁻¹ (hC ((Subgroup.topologicalClosure _).inv_mem hγ)) i⁻¹ (I.inv_mem hi)
        simpa [mul_assoc] using h }
  have hle : I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, (Subgroup.topologicalClosure _).one_mem, by rw [mul_one]⟩)
      (fun x hx => ⟨1, I.one_mem, x, hx, by rw [one_mul]⟩)
  exact hle (hsup hd)

/-- **Uniqueness of the factorisation `d = i * γ`**, given `I ⊓ C = ⊥`. -/
theorem factor_unique (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    {i₁ i₂ : Ω ≃ₐ[k] Ω} (hi₁ : i₁ ∈ I) (hi₂ : i₂ ∈ I)
    {γ₁ γ₂ : Ω ≃ₐ[k] Ω} (hγ₁ : γ₁ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hγ₂ : γ₂ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (heq : i₁ * γ₁ = i₂ * γ₂) : i₁ = i₂ ∧ γ₁ = γ₂ := by
  have hkey : i₂⁻¹ * i₁ = γ₂ * γ₁⁻¹ := by
    calc i₂⁻¹ * i₁ = i₂⁻¹ * (i₁ * γ₁) * γ₁⁻¹ := by group
      _ = i₂⁻¹ * (i₂ * γ₂) * γ₁⁻¹ := by rw [heq]
      _ = γ₂ * γ₁⁻¹ := by group
  have hmem : i₂⁻¹ * i₁ ∈ I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) :=
    Subgroup.mem_inf.mpr ⟨I.mul_mem (I.inv_mem hi₂) hi₁, by
      rw [hkey]
      exact (Subgroup.topologicalClosure _).mul_mem hγ₂
        ((Subgroup.topologicalClosure _).inv_mem hγ₁)⟩
  have h1 : i₂⁻¹ * i₁ = 1 := Subgroup.mem_bot.mp (le_of_eq hinf hmem)
  have hi : i₁ = i₂ := by
    calc i₁ = i₂ * (i₂⁻¹ * i₁) := by group
      _ = i₂ * 1 := by rw [h1]
      _ = i₂ := by rw [mul_one]
  refine ⟨hi, ?_⟩
  rw [hi] at heq
  exact mul_left_cancel heq

section Proj

variable (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
variable (hI : I ≤ SSGRoute.decomp k A)
variable (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
variable (hC : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A)
variable (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))

/-- The `I`-component of `d ∈ D` (depends on a choice, determined up to nothing by uniqueness). -/
def ip (d : ↥(SSGRoute.decomp k A)) : ↥I :=
  ⟨(exists_factor A I σ hI hnorm hC hsup d.2).choose,
    (exists_factor A I σ hI hnorm hC hsup d.2).choose_spec.1⟩

/-- The `C`-component of `d ∈ D` (the projection `D → C ≅ D/I`). -/
def proj (d : ↥(SSGRoute.decomp k A)) : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
  ⟨(exists_factor A I σ hI hnorm hC hsup d.2).choose_spec.2.choose,
    (exists_factor A I σ hI hnorm hC hsup d.2).choose_spec.2.choose_spec.1⟩

theorem ip_mul_proj (d : ↥(SSGRoute.decomp k A)) :
    (ip A I σ hI hnorm hC hsup d).1 * (proj A I σ hI hnorm hC hsup d).1 = d.1 :=
  (exists_factor A I σ hI hnorm hC hsup d.2).choose_spec.2.choose_spec.2

/-- **`proj` is a group homomorphism `D → C`.** -/
theorem proj_mul (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (d₁ d₂ : ↥(SSGRoute.decomp k A)) :
    proj A I σ hI hnorm hC hsup (d₁ * d₂) =
      proj A I σ hI hnorm hC hsup d₁ * proj A I σ hI hnorm hC hsup d₂ := by
  have h1 := ip_mul_proj A I σ hI hnorm hC hsup (d₁ * d₂)
  have h2 := ip_mul_proj A I σ hI hnorm hC hsup d₁
  have h3 := ip_mul_proj A I σ hI hnorm hC hsup d₂
  have hmemI : (proj A I σ hI hnorm hC hsup d₁).1 * (ip A I σ hI hnorm hC hsup d₂).1 *
      ((proj A I σ hI hnorm hC hsup d₁).1)⁻¹ ∈ I :=
    hnorm _ (hC (proj A I σ hI hnorm hC hsup d₁).2) _
      (ip A I σ hI hnorm hC hsup d₂).2
  have heq : (ip A I σ hI hnorm hC hsup d₁).1 *
        ((proj A I σ hI hnorm hC hsup d₁).1 * (ip A I σ hI hnorm hC hsup d₂).1 *
          ((proj A I σ hI hnorm hC hsup d₁).1)⁻¹) *
        ((proj A I σ hI hnorm hC hsup d₁).1 * (proj A I σ hI hnorm hC hsup d₂).1) =
      (ip A I σ hI hnorm hC hsup (d₁ * d₂)).1 *
        (proj A I σ hI hnorm hC hsup (d₁ * d₂)).1 := by
    rw [h1, Subgroup.coe_mul, ← h2, ← h3]
    group
  obtain ⟨-, hγ⟩ := factor_unique A I σ hinf
    (I.mul_mem (ip A I σ hI hnorm hC hsup d₁).2 hmemI)
    (ip A I σ hI hnorm hC hsup (d₁ * d₂)).2
    (proj A I σ hI hnorm hC hsup d₁ * proj A I σ hI hnorm hC hsup d₂).2
    (proj A I σ hI hnorm hC hsup (d₁ * d₂)).2 heq
  exact Subtype.ext hγ.symm

end Proj

end

end Work.SSGRoute.HS
