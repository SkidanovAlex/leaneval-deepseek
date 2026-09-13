import Mathlib
import Submission.Grassmann.Injective

/-!
# Duality of the Grassmann graph: `Gr k ℓ ≅ Gr k (k - ℓ)`

The standard (dot-product) bilinear form on `𝔽₂ᵏ` is nondegenerate and symmetric, so
`L ↦ L^⊥` is an order-reversing involution on subspaces of `𝔽₂ᵏ` with
`dim L^⊥ = k - dim L`.  Since `(L₁ ⊓ L₂)^⊥ = L₁^⊥ ⊔ L₂^⊥`, the orthocomplement map sends
`ℓ`-subspaces to `(k-ℓ)`-subspaces and preserves the intersection dimension in the
appropriate sense; hence it induces a **graph isomorphism** `Gr k ℓ ≃g Gr k (k - ℓ)`.

Consequences: every statement about `Gr k ℓ` (spectral gap, level decomposition, the
sub-Grassmannian density structure `SubGr`) transfers to `Gr k (k-ℓ)`, so it suffices to
treat the case `2ℓ ≤ k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k ℓ : ℕ}

/-! ## 1. The standard bilinear form on `𝔽₂ᵏ` -/

/-- The standard dot-product bilinear form on `𝔽₂ᵏ`. -/
def dotBilin (k : ℕ) : LinearMap.BilinForm 𝔽₂ (Fin k → 𝔽₂) :=
  Matrix.toBilin' (1 : Matrix (Fin k) (Fin k) 𝔽₂)

lemma dotBilin_apply (x y : Fin k → 𝔽₂) :
    dotBilin k x y = ∑ i, x i * y i := by
  rw [dotBilin, Matrix.toBilin'_apply]
  simp [Matrix.one_apply]

lemma dotBilin_isRefl : (dotBilin k).IsRefl := by
  intro x y h
  have h' : (dotBilin k) y x = (dotBilin k) x y := by
    rw [dotBilin_apply, dotBilin_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [h', h]

lemma dotBilin_nondegenerate : (dotBilin k).Nondegenerate := by
  rw [dotBilin]
  refine Matrix.Nondegenerate.toBilin' ?_
  refine Matrix.nondegenerate_of_det_ne_zero ?_
  simp

/-- The orthogonal complement of a subspace of `𝔽₂ᵏ` for the standard form. -/
def ortho (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) : Submodule 𝔽₂ (Fin k → 𝔽₂) :=
  (dotBilin k).orthogonal L

lemma mem_ortho {v : Fin k → 𝔽₂} {L : Submodule 𝔽₂ (Fin k → 𝔽₂)} :
    v ∈ ortho L ↔ ∀ w ∈ L, ∑ i, v i * w i = 0 := by
  rw [ortho, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [dotBilin_apply]
  constructor
  · intro h w hw
    have := h w hw
    have hswap : (∑ i, v i * w i : 𝔽₂) = ∑ i, w i * v i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hswap]; exact this
  · intro h w hw
    have := h w hw
    have hswap : (∑ i, w i * v i : 𝔽₂) = ∑ i, v i * w i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hswap]; exact this

lemma ortho_ortho (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) : ortho (ortho L) = L :=
  LinearMap.BilinForm.orthogonal_orthogonal dotBilin_nondegenerate dotBilin_isRefl L

lemma ortho_mono {L L' : Submodule 𝔽₂ (Fin k → 𝔽₂)} (h : L ≤ L') : ortho L' ≤ ortho L :=
  LinearMap.BilinForm.orthogonal_le h

lemma le_ortho_iff {L L' : Submodule 𝔽₂ (Fin k → 𝔽₂)} : ortho L' ≤ ortho L ↔ L ≤ L' := by
  constructor
  · intro h
    have := ortho_mono h
    rwa [ortho_ortho, ortho_ortho] at this
  · exact ortho_mono

lemma finrank_ortho (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Module.finrank 𝔽₂ (ortho L) = k - Module.finrank 𝔽₂ L := by
  rw [ortho, LinearMap.BilinForm.finrank_orthogonal dotBilin_nondegenerate, finrank_fin_fun]

lemma ortho_sup (L L' : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    ortho (L ⊔ L') = ortho L ⊓ ortho L' := by
  refine le_antisymm ?_ ?_
  · exact le_inf (ortho_mono le_sup_left) (ortho_mono le_sup_right)
  · intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    simp only [mem_ortho] at hv1 hv2 ⊢
    intro w hw
    rw [Submodule.mem_sup] at hw
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    have h1 := hv1 x hx
    have h2 := hv2 y hy
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]

lemma ortho_inf (L L' : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    ortho (L ⊓ L') = ortho L ⊔ ortho L' := by
  have h : ortho (ortho L ⊔ ortho L') = L ⊓ L' := by
    rw [ortho_sup, ortho_ortho, ortho_ortho]
  rw [← h, ortho_ortho]

lemma finrank_ortho_inf (L L' : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Module.finrank 𝔽₂ ↥(ortho L ⊓ ortho L') + Module.finrank 𝔽₂ ↥(L ⊔ L') = k := by
  have h := finrank_ortho (L ⊔ L')
  rw [ortho_sup] at h
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq L L'
  have h3 : Module.finrank 𝔽₂ L ≤ k := by
    have := Submodule.finrank_le L; rwa [finrank_fin_fun] at this
  have h4 : Module.finrank 𝔽₂ L' ≤ k := by
    have := Submodule.finrank_le L'; rwa [finrank_fin_fun] at this
  have h5 : Module.finrank 𝔽₂ ↥(L ⊔ L') ≤ k := by
    have := Submodule.finrank_le (L ⊔ L'); rwa [finrank_fin_fun] at this
  omega
/-! ## 2. The orthocomplement map on vertices and the graph isomorphism -/

/-- The number of `(k-ℓ)`-subspaces of `ortho (L ⊓ L')` etc.: the dimension of the
orthogonal complement of the intersection. -/
lemma finrank_ortho_inf_eq (L L' : GrVertex k ℓ) (hℓ : ℓ ≤ k) :
    Module.finrank 𝔽₂ ↥(ortho L.1 ⊓ ortho L'.1) =
      k - ℓ - (ℓ - Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1)) := by
  have h1 := finrank_ortho_inf L.1 L'.1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq L.1 L'.1
  rw [L.2, L'.2] at h2
  have h3 : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) ≤ ℓ := by
    have := Submodule.finrank_mono (inf_le_left : L.1 ⊓ L'.1 ≤ L.1)
    rwa [L.2] at this
  have h4 : Module.finrank 𝔽₂ ↥(L.1 ⊔ L'.1) ≤ k := by
    have := Submodule.finrank_le (L.1 ⊔ L'.1); rwa [finrank_fin_fun] at this
  omega

/-- The orthocomplement map, as a bijection of vertices `GrVertex k ℓ ≃ GrVertex k (k-ℓ)`. -/
def orthoEquiv (k ℓ : ℕ) (hℓ : ℓ ≤ k) : GrVertex k ℓ ≃ GrVertex k (k - ℓ) where
  toFun L := ⟨ortho L.1, by rw [finrank_ortho, L.2]⟩
  invFun M := ⟨ortho M.1, by
    rw [finrank_ortho, M.2]
    omega⟩
  left_inv L := Subtype.ext (ortho_ortho L.1)
  right_inv M := Subtype.ext (ortho_ortho M.1)

lemma orthoEquiv_apply (hℓ : ℓ ≤ k) (L : GrVertex k ℓ) :
    (orthoEquiv k ℓ hℓ L).1 = ortho L.1 := rfl

/-- **Orthocomplementation preserves the distance** `grDist L L' = ℓ - dim (L ⊓ L')`. -/
lemma grDist_ortho (hℓ : ℓ ≤ k) (L L' : GrVertex k ℓ) :
    grDist (orthoEquiv k ℓ hℓ L) (orthoEquiv k ℓ hℓ L') = grDist L L' := by
  rw [grDist, grDist, orthoEquiv_apply, orthoEquiv_apply]
  have h1 := finrank_ortho_inf L.1 L'.1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq L.1 L'.1
  rw [L.2, L'.2] at h2
  have h3 : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) ≤ ℓ := by
    have := Submodule.finrank_mono (inf_le_left : L.1 ⊓ L'.1 ≤ L.1)
    rwa [L.2] at this
  have h4 : Module.finrank 𝔽₂ ↥(L.1 ⊔ L'.1) ≤ k := by
    have := Submodule.finrank_le (L.1 ⊔ L'.1); rwa [finrank_fin_fun] at this
  omega

/-- **The orthocomplement map preserves adjacency.** -/
theorem adj_orthoEquiv (hℓ : ℓ ≤ k) (h1 : 1 ≤ ℓ) (L L' : GrVertex k ℓ) :
    (Gr k (k - ℓ)).Adj (orthoEquiv k ℓ hℓ L) (orthoEquiv k ℓ hℓ L') ↔
      (Gr k ℓ).Adj L L' := by
  rcases eq_or_lt_of_le hℓ with heq | hlt
  · have hk : k - ℓ = 0 := by omega
    have huniq0 : ∀ A B : GrVertex k (k - ℓ), A = B := fun A B => Subtype.ext (by
      have hA : Module.finrank 𝔽₂ A.1 = 0 := A.2.trans hk
      have hB : Module.finrank 𝔽₂ B.1 = 0 := B.2.trans hk
      rw [Submodule.finrank_eq_zero.mp hA, Submodule.finrank_eq_zero.mp hB])
    have hLtop : L.1 = ⊤ :=
      Submodule.eq_top_of_finrank_eq (K := 𝔽₂) (by rw [finrank_fin_fun]; exact heq ▸ L.2)
    have hL'top : L'.1 = ⊤ :=
      Submodule.eq_top_of_finrank_eq (K := 𝔽₂) (by rw [finrank_fin_fun]; exact heq ▸ L'.2)
    have hfalse1 : ¬ (Gr k (k - ℓ)).Adj (orthoEquiv k ℓ hℓ L) (orthoEquiv k ℓ hℓ L') := by
      intro h
      rw [Gr, SimpleGraph.fromRel_adj] at h
      exact h.1 (huniq0 _ _)
    have hfalse2 : ¬ (Gr k ℓ).Adj L L' := by
      intro h
      rw [Gr, SimpleGraph.fromRel_adj] at h
      exact h.1 (Subtype.ext (by rw [hLtop, hL'top]))
    exact ⟨fun h => absurd h hfalse1, fun h => absurd h hfalse2⟩
  · have h2 : 1 ≤ k - ℓ := by omega
    rw [adj_iff_grDist_eq_one _ _ h2, adj_iff_grDist_eq_one _ _ h1, grDist_ortho]

/-- **The Grassmann graphs in complementary dimensions are isomorphic:**
`Gr k ℓ ≃g Gr k (k - ℓ)` via orthocomplementation (for `1 ≤ ℓ ≤ k`). -/
def orthoIso (k ℓ : ℕ) (hℓ : ℓ ≤ k) (h1 : 1 ≤ ℓ) : Gr k ℓ ≃g Gr k (k - ℓ) where
  toEquiv := orthoEquiv k ℓ hℓ
  map_rel_iff' := fun {L L'} => adj_orthoEquiv hℓ h1 L L'

end

end F2
end Submission.Grassmann
