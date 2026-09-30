import Mathlib
import Submission.Work.BW.ker_orth
import Submission.Work.BW.ker_c_eq_span_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- If `c : Fin (r-1) → Fin r → ℚ` is a `ℚ`-independent family of vectors orthogonal to a
nonzero integral vector `B`, and `σ` enumerates the coordinates where `B` may be nonzero (`B`
vanishes off `range σ`), then the family `c m ∘ σ` spans exactly the orthogonal complement of
`B ∘ σ` inside `ℚ^{N'}`. -/
lemma span_comp_eq_ker {r N' : ℕ} (σ : Fin N' → Fin r) (hσ : Function.Injective σ)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (B : Fin r → ℤ) (hB : B ≠ 0) (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0)
    (hBZ : ∀ k : Fin r, k ∉ Set.range σ → B k = 0) :
    Submodule.span ℚ (Set.range (fun m : Fin (r - 1) => fun j : Fin N' => c m (σ j)))
      = LinearMap.ker
          ((∑ j : Fin N', (B (σ j) : ℚ) • LinearMap.proj j) : (Fin N' → ℚ) →ₗ[ℚ] ℚ) := by
  classical
  let F : (Fin r → ℚ) →ₗ[ℚ] ℚ := ∑ i : Fin r, (B i : ℚ) • LinearMap.proj i
  let Fσ : (Fin N' → ℚ) →ₗ[ℚ] ℚ := ∑ j : Fin N', (B (σ j) : ℚ) • LinearMap.proj j
  let ρ : (Fin r → ℚ) →ₗ[ℚ] (Fin N' → ℚ) :=
    { toFun := fun u => fun j => u (σ j)
      map_add' := by intro u w; rfl
      map_smul' := by intro a u; rfl }
  have hF_apply : ∀ u : Fin r → ℚ, F u = ∑ i, (B i : ℚ) * u i := by
    intro u
    simp only [F, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hFσ_apply : ∀ v : Fin N' → ℚ, Fσ v = ∑ j, (B (σ j) : ℚ) * v j := by
    intro v
    simp only [Fσ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  -- The sum identity rewriting the `Fin r` sum as a sum over `σ`.
  have hsum_id : ∀ u : Fin r → ℚ,
      (∑ j : Fin N', (B (σ j) : ℚ) * u (σ j)) = ∑ i : Fin r, (B i : ℚ) * u i := by
    intro u
    rw [← Finset.sum_image (f := fun i : Fin r => (B i : ℚ) * u i) (g := σ) (s := Finset.univ)
          (hσ.injOn)]
    rw [Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)) (fun x _ hx => by
          have hx' : x ∉ Set.range σ := by
            intro hr
            obtain ⟨a, ha⟩ := hr
            exact hx (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
          simp [hBZ x hx'])]
  -- Key: `Fσ ∘ ρ = F`.
  have hcomp : Fσ.comp ρ = F := by
    apply LinearMap.ext
    intro u
    show Fσ (ρ u) = F u
    rw [hFσ_apply, hF_apply]
    exact hsum_id u
  -- The kernel of `F` is the span of `c`.
  have hker : LinearMap.ker F = Submodule.span ℚ (Set.range c) := by
    apply le_antisymm
    · intro u hu
      by_contra huc
      obtain ⟨w, hw, huw⟩ := ker_orth c u huc
      obtain ⟨t, ht⟩ := ker_c_eq_span_B c hc B hB hcB w hw
      apply huw
      rw [ht]
      have hu0 : F u = 0 := LinearMap.mem_ker.mp hu
      have hu_sum : (∑ i : Fin r, u i * (B i : ℚ)) = 0 := by
        rw [show (∑ i : Fin r, u i * (B i : ℚ)) = F u from by
              rw [hF_apply]; exact Finset.sum_congr rfl (fun i _ => by ring)]
        exact hu0
      calc (∑ i : Fin r, u i * (t * (B i : ℚ)))
          = t * (∑ i : Fin r, u i * (B i : ℚ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = 0 := by rw [hu_sum, mul_zero]
    · rw [Submodule.span_le]
      rintro u ⟨m, rfl⟩
      apply LinearMap.mem_ker.mpr
      rw [hF_apply]
      rw [show (∑ i : Fin r, (B i : ℚ) * c m i) = ∑ i : Fin r, c m i * (B i : ℚ) from
            Finset.sum_congr rfl (fun i _ => by ring)]
      exact hcB m
  -- The goal's LHS is the image of `span (range c)` under `ρ`.
  have hmap : Submodule.span ℚ (Set.range (fun m : Fin (r - 1) => fun j : Fin N' => c m (σ j)))
      = Submodule.map ρ (Submodule.span ℚ (Set.range c)) := by
    rw [Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨c m, ⟨m, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
  change Submodule.span ℚ (Set.range (fun m : Fin (r - 1) => fun j : Fin N' => c m (σ j)))
      = LinearMap.ker Fσ
  rw [hmap, ← hker]
  apply le_antisymm
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := hw
    apply LinearMap.mem_ker.mpr
    rw [show Fσ (ρ u) = F u from congrArg (fun g : (Fin r → ℚ) →ₗ[ℚ] ℚ => g u) hcomp]
    exact LinearMap.mem_ker.mp hu
  · intro v hv
    have hρu : ρ (Function.extend σ v 0) = v := by
      funext j
      exact hσ.extend_apply v 0 j
    refine ⟨Function.extend σ v 0, ?_, hρu⟩
    apply LinearMap.mem_ker.mpr
    rw [show F (Function.extend σ v 0) = Fσ (ρ (Function.extend σ v 0)) from
          (congrArg (fun g : (Fin r → ℚ) →ₗ[ℚ] ℚ => g (Function.extend σ v 0)) hcomp).symm]
    rw [hρu]
    exact LinearMap.mem_ker.mp hv

end Work.BW
