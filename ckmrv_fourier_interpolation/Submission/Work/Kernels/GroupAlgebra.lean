/-
# The group algebra `R = ℂ[SL(2,ℤ)]` acting on `ℍ → ℂ` by slash operators

This file sets up the group algebra `R = ℂ[SL(2,ℤ)]` of CKMRV Section 3.3 together with its
action on functions `ℍ → ℂ` by linear combinations of slash operators,

  `slash k r F = ∑_γ c_γ · (F ∣[k] γ)`,   `r = ∑_γ c_γ γ ∈ R`,

the right ideals

  `𝓘   = (T-I)² R + S (T-I)² R`,
  `𝓘₊  = (S+I) R + (T-I)² R`,   `𝓘₋ = (S-I) R + (T-I)² R`,
  `𝓘̃₊ = (T - 2I + T⁻¹ - 2S) R + (I - STS) R`,
  `𝓘̃₋ = (T - 2I + T⁻¹ + 2S) R + (I + STS) R`

of CKMRV (3.9), realized as `ℂ`-submodules of `R`, and the spaces
`Ann_k(J, 𝒫) = {F ∈ 𝒫 : (F ∣[k] r) = 0 for all r ∈ J}` that they cut out.

Since the weight `d/2` is even for `d = 8, 24`, `-I` acts trivially and the action factors
through the group algebra of `PSL(2,ℤ)`.

The right ideals are realized as `Work.Kernels.span2 g₀ g₁ = g₀ R + g₁ R ⊆ R`.
-/
import Mathlib
import Submission.Work.Kernels.Slash

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- The group algebra `R = ℂ[SL(2,ℤ)]` of CKMRV Section 3.3. -/
abbrev R : Type := MonoidAlgebra ℂ (SL(2,ℤ))

/-- The element `T = !![1,1;0,1]` of `R`. -/
abbrev R_T : R := MonoidAlgebra.single ModularGroup.T 1

/-- The element `S = !![0,-1;1,0]` of `R`. -/
abbrev R_S : R := MonoidAlgebra.single ModularGroup.S 1

/-- The weight-`k` action of `r ∈ R` on functions `ℍ → ℂ` by linear combinations of slash
operators: `slash k r F = ∑_γ c_γ · (F ∣[k] γ)`. -/
noncomputable def slash (k : ℤ) (r : R) (F : ℍ → ℂ) : ℍ → ℂ :=
  Finsupp.sum r.coeff fun γ c => c • (F ∣[k] γ)

@[simp]
lemma slash_zero (k : ℤ) (F : ℍ → ℂ) : slash k 0 F = 0 := by
  simp [slash, MonoidAlgebra.coeff_zero]

@[simp]
lemma slash_single (k : ℤ) (γ : SL(2,ℤ)) (c : ℂ) (F : ℍ → ℂ) :
    slash k (MonoidAlgebra.single γ c) F = c • (F ∣[k] γ) := by
  simp [slash, MonoidAlgebra.coeff_single]

lemma slash_add (k : ℤ) (r s : R) (F : ℍ → ℂ) :
    slash k (r + s) F = slash k r F + slash k s F := by
  simp only [slash, MonoidAlgebra.coeff_add]
  rw [Finsupp.sum_add_index]
  · intro a ha
    simp
  · intro a ha b₁ b₂
    exact add_smul b₁ b₂ (F ∣[k] a)

@[simp]
lemma slash_one (k : ℤ) (F : ℍ → ℂ) : slash k (1 : R) F = F := by
  rw [MonoidAlgebra.one_def, slash_single, SlashAction.slash_one]
  simp

lemma slash_sum {ι : Type*} (k : ℤ) (s : Finset ι) (r : ι → R) (F : ℍ → ℂ) :
    slash k (∑ i ∈ s, r i) F = ∑ i ∈ s, slash k (r i) F := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, slash_add, ih]

/-! ## Right ideals of `R` -/

/-- The right ideal `g₀ R + g₁ R` of `R`, as a `ℂ`-submodule. -/
noncomputable def span2 (g₀ g₁ : R) : Submodule ℂ R where
  carrier := {r : R | ∃ a b : R, r = g₀ * a + g₁ * b}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, b₁, hx⟩ ⟨a₂, b₂, hy⟩
    exact ⟨a₁ + a₂, b₁ + b₂, by rw [hx, hy]; noncomm_ring⟩
  smul_mem' := by
    rintro c x ⟨a, b, hx⟩
    exact ⟨c • a, c • b, by rw [hx, smul_add, ← mul_smul_comm, ← mul_smul_comm]⟩

lemma mem_span2 {g₀ g₁ r : R} : r ∈ span2 g₀ g₁ ↔ ∃ a b : R, r = g₀ * a + g₁ * b :=
  Iff.rfl

/-- `𝓘 = (T-I)² R + S (T-I)² R`. -/
noncomputable def IdealI : Submodule ℂ R := span2 ((R_T - 1) ^ 2) (R_S * (R_T - 1) ^ 2)

/-- `𝓘₊ = (S+I) R + (T-I)² R`. -/
noncomputable def IdealIp : Submodule ℂ R := span2 (R_S + 1) ((R_T - 1) ^ 2)

/-- `𝓘₋ = (S-I) R + (T-I)² R`. -/
noncomputable def IdealIm : Submodule ℂ R := span2 (R_S - 1) ((R_T - 1) ^ 2)

/-- The element `T⁻¹` of `R`. -/
abbrev R_Tinv : R := MonoidAlgebra.single (ModularGroup.T)⁻¹ 1

/-- `𝓘̃₊ = (T - 2I + T⁻¹ - 2S) R + (I - STS) R`. -/
noncomputable def IdealTp : Submodule ℂ R :=
  span2 (R_T - 2 * 1 + R_Tinv - 2 * R_S) (1 - R_S * R_T * R_S)

/-- `𝓘̃₋ = (T - 2I + T⁻¹ + 2S) R + (I + STS) R`. -/
noncomputable def IdealTm : Submodule ℂ R :=
  span2 (R_T - 2 * 1 + R_Tinv + 2 * R_S) (1 + R_S * R_T * R_S)

/-- `𝓘 ⊆ 𝓘₊`, using `S(T-I)² = (S+I)(T-I)² - (T-I)²`. -/
lemma IdealI_le_IdealIp : IdealI ≤ IdealIp := by
  rintro r ⟨a, b, rfl⟩
  refine ⟨(R_T - 1) ^ 2 * b, a - b, ?_⟩
  noncomm_ring

/-- `𝓘 ⊆ 𝓘₋`, using `S(T-I)² = (S-I)(T-I)² + (T-I)²`. -/
lemma IdealI_le_IdealIm : IdealI ≤ IdealIm := by
  rintro r ⟨a, b, rfl⟩
  refine ⟨(R_T - 1) ^ 2 * b, a + b, ?_⟩
  noncomm_ring

/-- The space `Ann_k(J, 𝒫)` of CKMRV Section 4.2: functions in `𝒫` annihilated by the
right ideal `J` under the weight-`k` action. -/
def Ann (k : ℤ) (J : Submodule ℂ R) : Set (ℍ → ℂ) :=
  {F | InP F ∧ ∀ r ∈ J, slash k r F = 0}

lemma Ann.mono {k : ℤ} {J J' : Submodule ℂ R} (h : J ≤ J') :
    Ann k J' ⊆ Ann k J :=
  fun _ hF => ⟨hF.1, fun r hr => hF.2 r (h hr)⟩

end Work.Kernels
