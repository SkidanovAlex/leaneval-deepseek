import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HPgram
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# Covolume is multiplicative on orthogonal direct sums

`Work.HP.detL L` is the covolume (in the real span) of an integral lattice
`L ⊆ ℤ^ι`, defined as the square root of the determinant of the Gram matrix of a
`ℤ`-basis of `L` (the basis produced by `Submodule.basisOfPid`).

The main result `detL_sup_orthogonal` states that if `L₁ ⊓ L₂ = ⊥` and the lattices
are orthogonal with respect to the standard Euclidean inner product
`⟨x,y⟩ = ∑ i, x i * y i`, then

  `detL (L₁ ⊔ L₂) = detL L₁ * detL L₂`

(this is the classical fact that covolumes multiply across an orthogonal direct sum).

The proof builds an explicit `ℤ`-basis of `L₁ ⊔ L₂` indexed by `Fin k₁ ⊕ Fin k₂`
by combining bases of `L₁` and `L₂`; that the two pieces are independent is exactly
`L₁ ⊓ L₂ = ⊥`, and orthogonality makes the Gram matrix block diagonal, so its
determinant is the product of the two Gram determinants.  `detL` is basis-independent
(`Work.HP.Lat.detL_basis_gram`), so we may use this adapted basis.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Work.HP.FM

theorem detL_sup_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L₁ L₂ : Submodule ℤ (ι → ℤ)) (hdisj : L₁ ⊓ L₂ = ⊥)
    (horth : ∀ x ∈ L₁, ∀ y ∈ L₂, ∑ i, x i * y i = 0) :
    Work.HP.detL (L₁ ⊔ L₂) = Work.HP.detL L₁ * Work.HP.detL L₂ := by
  classical
  -- Bases of `L₁` and `L₂`, viewed as families of ambient integer vectors.
  obtain ⟨k₁, b₁⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L₁
  obtain ⟨k₂, b₂⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L₂
  let v₁ : Fin k₁ → ι → ℤ := fun i => (b₁ i : ι → ℤ)
  let v₂ : Fin k₂ → ι → ℤ := fun j => (b₂ j : ι → ℤ)
  -- Each family spans the corresponding lattice.
  have hspan₁ : Submodule.span ℤ (Set.range v₁) = L₁ := by
    have h2 : Submodule.map L₁.subtype ⊤ = L₁ := by
      rw [Submodule.map_top]; exact Submodule.range_subtype L₁
    have hr : Set.range v₁ = L₁.subtype '' Set.range b₁ := by
      change Set.range (L₁.subtype ∘ b₁) = L₁.subtype '' Set.range b₁
      rw [Set.range_comp]
    rw [hr, Submodule.span_image L₁.subtype, Module.Basis.span_eq, h2]
  have hspan₂ : Submodule.span ℤ (Set.range v₂) = L₂ := by
    have h2 : Submodule.map L₂.subtype ⊤ = L₂ := by
      rw [Submodule.map_top]; exact Submodule.range_subtype L₂
    have hr : Set.range v₂ = L₂.subtype '' Set.range b₂ := by
      change Set.range (L₂.subtype ∘ b₂) = L₂.subtype '' Set.range b₂
      rw [Set.range_comp]
    rw [hr, Submodule.span_image L₂.subtype, Module.Basis.span_eq, h2]
  -- Each family is `ℤ`-linearly independent.
  have hv₁ : LinearIndependent ℤ v₁ :=
    b₁.linearIndependent.map' L₁.subtype (Submodule.ker_subtype L₁)
  have hv₂ : LinearIndependent ℤ v₂ :=
    b₂.linearIndependent.map' L₂.subtype (Submodule.ker_subtype L₂)
  have hmem₁ : ∀ i, v₁ i ∈ L₁ := fun i => (b₁ i).2
  have hmem₂ : ∀ j, v₂ j ∈ L₂ := fun j => (b₂ j).2
  -- `L₁ ⊓ L₂ = ⊥` says the two spans are disjoint, so the union is independent.
  have hdj : Disjoint (Submodule.span ℤ (Set.range v₁)) (Submodule.span ℤ (Set.range v₂)) := by
    rw [hspan₁, hspan₂, disjoint_iff]; exact hdisj
  have hli : LinearIndependent ℤ (Sum.elim v₁ v₂) := LinearIndependent.sum_type hv₁ hv₂ hdj
  -- ... and it spans `L₁ ⊔ L₂`.
  have hspan_sup : Submodule.span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspan₁, hspan₂]
  -- The resulting adapted basis of `L₁ ⊔ L₂`.
  let bsup : Module.Basis (Fin k₁ ⊕ Fin k₂) ℤ ↥(L₁ ⊔ L₂) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan_sup)
  have hbsup : ∀ k, ((bsup k : ↥(L₁ ⊔ L₂)) : ι → ℤ) = Sum.elim v₁ v₂ k := by
    intro k
    simp [bsup, Module.Basis.map_apply]
  -- The Gram matrices of the two factors over `ℝ`.
  let G₁ : Matrix (Fin k₁) (Fin k₁) ℝ :=
    Matrix.of fun i j => ∑ x, ((v₁ i) x : ℝ) * ((v₁ j) x : ℝ)
  let G₂ : Matrix (Fin k₂) (Fin k₂) ℝ :=
    Matrix.of fun i j => ∑ x, ((v₂ i) x : ℝ) * ((v₂ j) x : ℝ)
  -- The Gram matrix of `bsup` is block diagonal, with the two diagonal blocks `G₁`, `G₂`.
  have hgram : (Matrix.of fun i j : Fin k₁ ⊕ Fin k₂ =>
        ∑ x, (((bsup i : ↥(L₁ ⊔ L₂)) : ι → ℤ) x : ℝ) *
             (((bsup j : ↥(L₁ ⊔ L₂)) : ι → ℤ) x : ℝ))
      = Matrix.fromBlocks G₁ 0 0 G₂ := by
    ext i j
    rw [Matrix.of_apply, hbsup i, hbsup j]
    cases i with
    | inl a =>
      cases j with
      | inl b => simp [G₁, Matrix.fromBlocks, Sum.elim]
      | inr b =>
        have h0 : ∑ x, v₁ a x * v₂ b x = 0 := horth (v₁ a) (hmem₁ a) (v₂ b) (hmem₂ b)
        have hcast : ∑ x, ((v₁ a x : ℤ) : ℝ) * ((v₂ b x : ℤ) : ℝ)
            = ((∑ x, v₁ a x * v₂ b x : ℤ) : ℝ) := by
          rw [Int.cast_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [Int.cast_mul]
        simp only [Matrix.fromBlocks, Matrix.zero_apply, Matrix.of_apply,
          Sum.elim_inl, Sum.elim_inr]
        rw [hcast, h0, Int.cast_zero]
    | inr a =>
      cases j with
      | inl b =>
        have h0 : ∑ x, v₂ a x * v₁ b x = 0 := by
          rw [Finset.sum_congr rfl (fun x _ => mul_comm _ _)]
          exact horth (v₁ b) (hmem₁ b) (v₂ a) (hmem₂ a)
        have hcast : ∑ x, ((v₂ a x : ℤ) : ℝ) * ((v₁ b x : ℤ) : ℝ)
            = ((∑ x, v₂ a x * v₁ b x : ℤ) : ℝ) := by
          rw [Int.cast_sum]
          exact Finset.sum_congr rfl fun x _ => by rw [Int.cast_mul]
        simp only [Matrix.fromBlocks, Matrix.zero_apply, Matrix.of_apply,
          Sum.elim_inl, Sum.elim_inr]
        rw [hcast, h0, Int.cast_zero]
      | inr b => simp [G₂, Matrix.fromBlocks, Sum.elim]
  -- `detL` of the sum is the square root of the determinant of this adapted Gram matrix.
  have hdet := Work.HP.Lat.detL_basis_gram (L₁ ⊔ L₂) bsup
  rw [hgram, Matrix.det_fromBlocks_zero₁₂] at hdet
  -- `detL` of each factor is the square root of the corresponding Gram determinant.
  have h₁ : Work.HP.detL L₁ = Real.sqrt G₁.det := by
    rw [Work.HP.Lat.detL_basis_gram L₁ b₁]
  have h₂ : Work.HP.detL L₂ = Real.sqrt G₂.det := by
    rw [Work.HP.Lat.detL_basis_gram L₂ b₂]
  have hG₁_nonneg : 0 ≤ G₁.det := Work.HP.gramMat_det_nonneg k₁ L₁ b₁
  rw [hdet, h₁, h₂, Real.sqrt_mul hG₁_nonneg]

end Work.HP.FM
