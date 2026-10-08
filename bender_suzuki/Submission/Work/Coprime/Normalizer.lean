/-
Area A3 (coprime action): how the pointwise action of `A` on `Subgroup G` interacts with
`Subgroup.normalizer` and `Subgroup.centralizer`.

The main consequences (`FT.IsInvariant.normalizer`, `FT.IsInvariant.centralizer`) are that the
normalizer and the centralizer of an `A`-invariant subgroup are again `A`-invariant; this is the
form in which the coprime action is used together with the Frattini argument downstream.
-/
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped Pointwise

namespace FT

variable {A : Type*} {G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

/-- The pointwise action on subgroups commutes with taking normalizers:
`a • N_G(H) = N_G(a • H)`. -/
theorem smul_normalizer (a : A) (H : Subgroup G) :
    a • Subgroup.normalizer (H : Set G) = Subgroup.normalizer ((a • H : Subgroup G) : Set G) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := H),
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := H)]
    have hconj : a⁻¹ • (x * y * x⁻¹) = (a⁻¹ • x) * (a⁻¹ • y) * (a⁻¹ • x)⁻¹ := by
      rw [smul_mul', smul_mul', smul_inv']
    rw [hconj]
    exact hx (a⁻¹ • y)
  · intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have hconj : a⁻¹ • (x * (a • y) * x⁻¹) = (a⁻¹ • x) * y * (a⁻¹ • x)⁻¹ := by
      rw [smul_mul', smul_mul', smul_inv', inv_smul_smul]
    have h1 := hx (a • y)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := H), inv_smul_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := H), hconj] at h1
    exact h1

/-- The normalizer of an `A`-invariant subgroup is `A`-invariant. -/
instance IsInvariant.normalizer (H : Subgroup G) [IsInvariant A H] :
    IsInvariant A (Subgroup.normalizer (H : Set G)) :=
  ⟨fun a => by
    rw [smul_normalizer a H, (inferInstance : IsInvariant A H).smul_eq_self a]⟩

/-- The pointwise action on subgroups commutes with taking centralizers:
`a • C_G(S) = C_G(a • S)`. -/
theorem smul_centralizer (a : A) (S : Set G) :
    a • Subgroup.centralizer S = Subgroup.centralizer (a • S) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨c, hc, rfl⟩
    have hc' : ∀ g ∈ S, g * c = c * g := Subgroup.mem_centralizer_iff.mp hc
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro y ⟨z, hz, rfl⟩
    have h2 := congrArg (fun w : G => a • w) (hc' z hz)
    simp only [smul_mul'] at h2
    exact h2
  · rintro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hx' : ∀ g ∈ (a • S : Set G), g * x = x * g := Subgroup.mem_centralizer_iff.mp hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    have h2 := congrArg (fun w : G => a⁻¹ • w) (hx' (a • z) ⟨z, hz, rfl⟩)
    simp only [smul_mul', inv_smul_smul] at h2
    exact h2

/-- Subgroup-level form of `FT.smul_centralizer`. -/
theorem smul_centralizer_subgroup (a : A) (H : Subgroup G) :
    a • Subgroup.centralizer (H : Set G) = Subgroup.centralizer (a • H : Subgroup G) := by
  rw [smul_centralizer a (H : Set G), Subgroup.coe_pointwise_smul]

/-- The centralizer of an `A`-invariant subgroup is `A`-invariant. -/
instance IsInvariant.centralizer (H : Subgroup G) [IsInvariant A H] :
    IsInvariant A (Subgroup.centralizer (H : Set G)) :=
  ⟨fun a => by
    rw [smul_centralizer_subgroup a H, (inferInstance : IsInvariant A H).smul_eq_self a]⟩

end FT
