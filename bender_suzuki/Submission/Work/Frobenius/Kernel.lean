import Mathlib
import Submission.Work.Frobenius.ThetaIrr
import Submission.Work.Frobenius.Column
import Submission.Work.Frobenius.Basic.card_frobeniusKernel
import Submission.Work.Frobenius.Basic.normalizer_eq_of_isFrobeniusComplement
import Submission.Work.Frobenius.Kernel.eq_one_of_character_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Frobenius kernel as a subgroup

Given a Frobenius complement `H ≤ G` we obtain the Frobenius kernel by intersecting the kernels
of the representations with characters `θ*`, `θ ∈ Irr H`, `θ ≠ 1` (`kernelSubgroup`), and prove
that this intersection is a normal complement of `H` with carrier `frobeniusKernel H`.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise MonoidAlgebra

namespace Work.Frobenius

variable {G : Type*} [Group G] [Fintype G]

section LocalFintype

local instance instFintypeSubgroupKernel (H : Subgroup G) : Fintype H := Fintype.ofFinite H

variable {H : Subgroup G}

/-- The bundled irreducible representation of `G` with character `θ*`. -/
noncomputable def thetaStarRep (hH : IsFrobeniusComplement H)
    (θ : {θ : H → ℂ // θ ∈ Irr H ∧ θ ≠ 1}) : IrrRep G :=
  Classical.choose (mem_Irr_iff.mp (thetaStar_mem_Irr hH θ.2.1 θ.2.2))

theorem thetaStarRep_character (hH : IsFrobeniusComplement H)
    (θ : {θ : H → ℂ // θ ∈ Irr H ∧ θ ≠ 1}) :
    (thetaStarRep hH θ).ρ.character = thetaStar H θ.1 :=
  Classical.choose_spec (mem_Irr_iff.mp (thetaStar_mem_Irr hH θ.2.1 θ.2.2))

/-- The Frobenius kernel associated with the complement `H`, as a subgroup: the intersection of
the kernels of the representations with characters `θ*`, `θ ∈ Irr H`, `θ ≠ 1`. -/
noncomputable def kernelSubgroup (hH : IsFrobeniusComplement H) : Subgroup G :=
  ⨅ θ : {θ : H → ℂ // θ ∈ Irr H ∧ θ ≠ 1}, (thetaStarRep hH θ).ρ.ker

theorem mem_kernelSubgroup_iff {hH : IsFrobeniusComplement H} {x : G} :
    x ∈ kernelSubgroup hH ↔
      ∀ θ : {θ : H → ℂ // θ ∈ Irr H ∧ θ ≠ 1}, x ∈ (thetaStarRep hH θ).ρ.ker :=
  Subgroup.mem_iInf

theorem one_mem_kernelSubgroup (hH : IsFrobeniusComplement H) :
    (1 : G) ∈ kernelSubgroup hH := by
  rw [mem_kernelSubgroup_iff]
  intro θ
  exact MonoidHom.mem_ker.mpr (map_one _)

theorem kernelSubgroup_normal (hH : IsFrobeniusComplement H) : (kernelSubgroup hH).Normal := by
  rw [kernelSubgroup]
  exact Subgroup.normal_iInf_normal fun θ => MonoidHom.normal_ker _

/-- The induced class function of a function on `H` vanishes off the conjugates of `H`. -/
theorem indFun_eq_zero_of_not_conj {f : H → ℂ} {x : G}
    (h : ∀ g : G, g⁻¹ * x * g ∉ H) : indFun H f x = 0 := by
  simp only [indFun]
  rw [Finset.sum_eq_zero]
  · simp
  · intro y _
    by_cases hy : y * x * y⁻¹ ∈ H
    · exact absurd hy (by simpa [mul_assoc] using h y⁻¹)
    · simp [hy]

theorem thetaStar_apply_of_not_conj {θ : H → ℂ} {x : G}
    (h : ∀ g : G, g⁻¹ * x * g ∉ H) : thetaStar H θ x = θ 1 := by
  rw [thetaStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, indFun_eq_zero_of_not_conj h]
  simp

/-- `θ*` at a nontrivial element of `H` takes the value `θ h`. -/
theorem thetaStar_apply_of_mem_complement (hH : IsFrobeniusComplement H) {θ : H → ℂ}
    (hθ : IsClassFun θ) {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) :
    thetaStar H θ h = θ ⟨h, hh⟩ := by
  have hcf : IsClassFun (θ - (θ 1) • (1 : H → ℂ)) :=
    hθ.sub (IsClassFun.smul (θ 1) (isClassFun_const 1))
  rw [thetaStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Induction.indFun_apply_of_mem_complement (f := θ - (θ 1) • (1 : H → ℂ)) hH hcf hh hh1]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  ring

/-- The Frobenius kernel (as a set) is contained in `kernelSubgroup`. -/
theorem frobeniusKernel_subset_kernelSubgroup (hH : IsFrobeniusComplement H) :
    frobeniusKernel H ⊆ kernelSubgroup hH := by
  intro x hx
  rw [mem_frobeniusKernel_iff] at hx
  rcases hx with rfl | hx
  · exact one_mem_kernelSubgroup hH
  · change x ∈ kernelSubgroup hH
    rw [mem_kernelSubgroup_iff]
    intro θ
    refine Kernel.eq_one_of_character_eq (thetaStarRep hH θ) ?_
    rw [thetaStarRep_character hH θ, thetaStar_apply_of_not_conj hx, thetaStar_apply_one]

/-- `kernelSubgroup` meets the complement trivially. -/
theorem inf_kernelSubgroup_complement (hH : IsFrobeniusComplement H) :
    kernelSubgroup hH ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxH⟩ := Subgroup.mem_inf.mp hx
  by_contra hx1
  obtain ⟨θ, hθ, hθ1, hθx⟩ :=
    exists_irr_ne_one_apply_ne_apply_one (H := H) (x := (⟨x, hxH⟩ : H)) (by simpa using hx1)
  have hxker : x ∈ (thetaStarRep hH ⟨θ, hθ, hθ1⟩).ρ.ker :=
    (mem_kernelSubgroup_iff.mp hxK) ⟨θ, hθ, hθ1⟩
  have hval : (thetaStarRep hH ⟨θ, hθ, hθ1⟩).ρ.character x
      = (thetaStarRep hH ⟨θ, hθ, hθ1⟩).ρ.character 1 := by
    have hxρ : (thetaStarRep hH ⟨θ, hθ, hθ1⟩).ρ x = 1 := MonoidHom.mem_ker.mp hxker
    simp only [Representation.character, hxρ, map_one]
  rw [thetaStarRep_character hH ⟨θ, hθ, hθ1⟩,
    thetaStar_apply_of_mem_complement hH (irr_isClassFun hθ) hxH hx1, thetaStar_apply_one] at hval
  exact hθx hval

/-- The cardinality of `kernelSubgroup` is at least the index of `H`. -/
theorem index_le_card_kernelSubgroup (hH : IsFrobeniusComplement H) :
    H.index ≤ Nat.card (kernelSubgroup hH) := by
  rw [← Basic.card_frobeniusKernel hH]
  refine Nat.card_le_card_of_injective
    (fun x : (frobeniusKernel H : Set G) => (⟨x.1, frobeniusKernel_subset_kernelSubgroup hH x.2⟩ :
      kernelSubgroup hH)) ?_
  intro a b hab
  have h1 : (a : G) = (b : G) := by
    have := congrArg (fun z : ↥(kernelSubgroup hH) => (z : G)) hab
    simpa using this
  exact Subtype.ext h1

/-- If two subgroups meet trivially, the product of their orders is at most the order of `G`. -/
theorem card_mul_card_le_of_inf_eq_bot {K L : Subgroup G} (h : K ⊓ L = ⊥) :
    Nat.card K * Nat.card L ≤ Nat.card G := by
  have hinj : Function.Injective (fun p : K × L => (p.1 : G) * (p.2 : G)) := by
    rintro ⟨k₁, l₁⟩ ⟨k₂, l₂⟩ heq
    have heq' : (k₁ : G) * (l₁ : G) = (k₂ : G) * (l₂ : G) := by simpa using heq
    have hker : (k₂ : G)⁻¹ * k₁ = 1 := by
      have hmem : (k₂ : G)⁻¹ * k₁ ∈ K ⊓ L := by
        refine ⟨K.mul_mem (K.inv_mem k₂.2) k₁.2, ?_⟩
        have h2 : (k₂ : G)⁻¹ * k₁ = l₂ * (l₁ : G)⁻¹ := by
          have := congrArg (fun z => (k₂ : G)⁻¹ * z * (l₁ : G)⁻¹) heq'
          simpa [mul_assoc] using this
        rw [h2]; exact L.mul_mem l₂.2 (L.inv_mem l₁.2)
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hk : (k₁ : G) = k₂ := by
      have := congrArg (fun z => (k₂ : G) * z) hker
      simpa [mul_assoc] using this
    have hl : (l₁ : G) = l₂ := by
      have h2 := heq'
      rw [← hk] at h2
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hk) (Subtype.ext hl)
  have := Nat.card_le_card_of_injective (fun p : K × L => (p.1 : G) * (p.2 : G)) hinj
  rwa [Nat.card_prod] at this

/-- The cardinality of `kernelSubgroup` is exactly the index of `H`. -/
theorem card_kernelSubgroup (hH : IsFrobeniusComplement H) :
    Nat.card (kernelSubgroup hH) = H.index := by
  refine le_antisymm ?_ (index_le_card_kernelSubgroup hH)
  have hle := card_mul_card_le_of_inf_eq_bot (inf_kernelSubgroup_complement hH)
  rw [← Subgroup.index_mul_card H] at hle
  exact Nat.le_of_mul_le_mul_right hle Nat.card_pos

/-- `kernelSubgroup` is exactly the Frobenius kernel. -/
theorem kernelSubgroup_eq_frobeniusKernel (hH : IsFrobeniusComplement H) :
    ((kernelSubgroup hH : Subgroup G) : Set G) = frobeniusKernel H := by
  refine Set.Subset.antisymm ?_ (frobeniusKernel_subset_kernelSubgroup hH)
  intro x hx
  rw [mem_frobeniusKernel_iff]
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · refine Or.inr fun g hg => ?_
    -- x = g⁻¹ h g with h ∈ H would give h ∈ K ∩ H = 1
    have hyK : g⁻¹ * x * g ∈ kernelSubgroup hH := by
      simpa using (kernelSubgroup_normal hH).conj_mem x hx g⁻¹
    have hybot : g⁻¹ * x * g ∈ (⊥ : Subgroup G) := by
      rw [← inf_kernelSubgroup_complement hH]
      exact Subgroup.mem_inf.mpr ⟨hyK, hg⟩
    have hy1 : g⁻¹ * x * g = 1 := Subgroup.mem_bot.mp hybot
    exact hx1 (by rw [show x = g * (g⁻¹ * x * g) * g⁻¹ from by group, hy1]; group)

/-- `kernelSubgroup` is a complement of `H`. -/
theorem isComplement'_kernelSubgroup (hH : IsFrobeniusComplement H) :
    IsComplement' (kernelSubgroup hH) H := by
  rw [isComplement'_iff]
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [card_kernelSubgroup hH, Subgroup.index_mul_card]
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [inf_kernelSubgroup_complement hH] at hx
    exact hx

end LocalFintype

end Work.Frobenius
