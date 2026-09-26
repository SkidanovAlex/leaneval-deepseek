import Mathlib

/-!
# `finrank span ≤ t` iff all `(t+1)`-minors vanish

For a family `A : Fin N → (Fin M → ℝ)` of vectors in `ℝ^M`, the dimension of the span of the
family is at most `t` if and only if every `(t+1) × (t+1)` minor of the matrix whose rows are the
vectors `A i` vanishes.

The proof is the classical "rank = largest order of a nonvanishing minor" argument:

* (⇒) if the span has dimension `≤ t`, any `t+1` rows are linearly dependent, hence every
  `(t+1) × (t+1)` submatrix has dependent rows and vanishing determinant.  Equivalently, a
  nonvanishing minor exhibits `t+1` linearly independent rows via `Matrix.rank_submatrix_le` and
  `Matrix.rank_of_det_ne_zero`.
* (⇐) if the rank is `≥ t+1`, extract a linearly independent subfamily of `t+1` rows
  (`exists_linearIndependent'`) and then a nonvanishing `(t+1) × (t+1)` minor from a linearly
  independent family.  The latter is
  `Work.Drive.exists_minor_det_ne_zero_of_linearIndependent`: the coordinate functionals span the
  dual of the span `V` of the family (`Subspace.dualRestrict_surjective` together with the fact
  that the coordinate projections are the dual basis of `Pi.basisFun`), so an independent
  subfamily of them is a basis of `V*`; evaluating that basis on the independent family gives an
  invertible square matrix, whose determinant is the required nonvanishing minor.
-/

open Submodule Module

namespace Work.Drive

/-- **Nonvanishing minor from a linearly independent family of vectors.**
If `f : Fin k → (Fin M → ℝ)` is linearly independent, then some `k × k` minor of the matrix
whose rows are the vectors `f i` is nonzero. -/
theorem exists_minor_det_ne_zero_of_linearIndependent {k M : ℕ} (f : Fin k → (Fin M → ℝ))
    (hf : LinearIndependent ℝ f) :
    ∃ b : Fin k → Fin M, (Matrix.of (fun i j => f i (b j))).det ≠ 0 := by
  classical
  let V : Submodule ℝ (Fin M → ℝ) := Submodule.span ℝ (Set.range f)
  let g : Fin k → V := fun i => ⟨f i, by
    show f i ∈ Submodule.span ℝ (Set.range f)
    exact Submodule.subset_span ⟨i, rfl⟩⟩
  have hg_li : LinearIndependent ℝ g := by
    apply LinearIndependent.of_comp V.subtype
    show LinearIndependent ℝ (fun i => f i)
    exact hf
  have hg_span : Submodule.span ℝ (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have key : ∀ (x : Fin M → ℝ) (hx : x ∈ V),
        (⟨x, hx⟩ : V) ∈ Submodule.span ℝ (Set.range g) := by
      intro x hx
      induction hx using span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
      | smul c a ha iha => exact Submodule.smul_mem _ c iha
    exact key y.val y.property
  let φ : Fin M → (V →ₗ[ℝ] ℝ) := fun j => (LinearMap.proj j).comp V.subtype
  -- The restrictions of the coordinate functionals span the dual of `V`.
  have hφspan : Submodule.span ℝ (Set.range φ) = ⊤ := by
    have hproj_eq : (fun j : Fin M => (LinearMap.proj j : (Fin M → ℝ) →ₗ[ℝ] ℝ)) =
        (Pi.basisFun ℝ (Fin M)).dualBasis := by
      funext j
      apply LinearMap.ext
      intro x
      rw [Module.Basis.dualBasis_apply, Pi.basisFun_repr]
      exact LinearMap.proj_apply j x
    have hproj_span : Submodule.span ℝ
        (Set.range (fun j : Fin M => (LinearMap.proj j : (Fin M → ℝ) →ₗ[ℝ] ℝ))) = ⊤ := by
      rw [hproj_eq, Module.Basis.span_eq]
    have hφ_eq : φ = (fun j : Fin M => Submodule.dualRestrict V
        ((fun j : Fin M => (LinearMap.proj j : (Fin M → ℝ) →ₗ[ℝ] ℝ)) j)) := by
      funext j
      rfl
    rw [hφ_eq, Set.range_comp', ← Submodule.map_span, hproj_span, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr Subspace.dualRestrict_surjective
  -- Extract a basis of `V*` among the restrictions of coordinate functionals.
  obtain ⟨κ, b', hb'inj, hspan', hli'⟩ := exists_linearIndependent' ℝ φ
  haveI : Fintype κ := Fintype.ofInjective b' hb'inj
  have hfinV : Module.finrank ℝ V = k := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hf
    rw [Fintype.card_fin] at h1
    rw [h1]
    rfl
  have hcard : Fintype.card κ = k := by
    have h2 := linearIndependent_iff_card_eq_finrank_span.mp hli'
    rw [h2]
    show Set.finrank ℝ (Set.range (φ ∘ b')) = k
    rw [Set.finrank, hspan', hφspan]
    rw [finrank_top, Subspace.dual_finrank_eq, hfinV]
  -- Reindex along `κ ≃ Fin k`.
  let e : κ ≃ Fin k := (Fintype.equivFin κ).trans (finCongr hcard)
  let b : Fin k → Fin M := b' ∘ e.symm
  have hspanb : Submodule.span ℝ (Set.range (fun l : Fin k => φ (b l))) = ⊤ := by
    have hr : Set.range (fun l : Fin k => φ (b l)) = Set.range (φ ∘ b') := by
      change Set.range ((φ ∘ b') ∘ ⇑e.symm) = Set.range (φ ∘ b')
      simp
    rw [hr, hspan', hφspan]
  have hlib : LinearIndependent ℝ (fun l : Fin k => φ (b l)) := by
    have h' : (fun l : Fin k => φ (b l)) = (φ ∘ b') ∘ ⇑e.symm := by
      ext l; rfl
    rw [h']
    exact hli'.comp e.symm e.symm.injective
  -- The evaluation map at `g` of this basis of the dual is injective.
  let Ψ : V →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi (fun l : Fin k => φ (b l))
  have hΨ_apply : ∀ u : V, Ψ u = fun l => φ (b l) u := fun u => rfl
  have hker : Ψ.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    funext j
    show (u : Fin M → ℝ) j = 0
    have hmem : φ j ∈ Submodule.span ℝ (Set.range (fun l : Fin k => φ (b l))) := by
      rw [hspanb]; exact Submodule.mem_top
    have hle : Submodule.span ℝ (Set.range (fun l : Fin k => φ (b l))) ≤
        LinearMap.ker (LinearMap.applyₗ u) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have h1 := congrFun hu l
      simp only [hΨ_apply, Pi.zero_apply] at h1
      simpa using h1
    have h2 := hle hmem
    rw [LinearMap.mem_ker] at h2
    simpa [φ, LinearMap.comp_apply, LinearMap.proj_apply] using h2
  have hcol_li : LinearIndependent ℝ (fun i : Fin k => (fun l => φ (b l) (g i))) := by
    have hm := LinearIndependent.map' hg_li Ψ hker
    have hEq : (fun i : Fin k => (fun l => φ (b l) (g i))) = ⇑Ψ ∘ g := by
      funext i l
      rfl
    rw [hEq]
    exact hm
  -- The square matrix `φ (b l) (g i)` is invertible.
  have hdet : (Matrix.of (fun l i : Fin k => φ (b l) (g i))).det ≠ 0 := by
    rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_col_iff]
    exact hcol_li
  refine ⟨b, ?_⟩
  have heq : Matrix.of (fun i j : Fin k => f i (b j)) =
      (Matrix.of (fun l i : Fin k => φ (b l) (g i))).transpose := by
    ext i l
    show f i (b l) = φ (b l) (g i)
    rfl
  rw [heq, Matrix.det_transpose]
  exact hdet

/-- The rank of a matrix is at most `t` if and only if all its `(t+1) × (t+1)` minors vanish. -/
theorem matrix_rank_le_iff_minors_eq_zero {N M t : ℕ} (ht : t + 1 ≤ N)
    (A : Matrix (Fin N) (Fin M) ℝ) :
    A.rank ≤ t ↔ ∀ (a : Fin (t + 1) → Fin N) (b : Fin (t + 1) → Fin M),
      (A.submatrix a b).det = 0 := by
  classical
  constructor
  · intro h a b
    by_contra hdet
    have h1 : (A.submatrix a b).rank ≤ A.rank := Matrix.rank_submatrix_le A a b
    have h2 := Matrix.rank_of_det_ne_zero hdet
    rw [h2, Fintype.card_fin] at h1
    omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hrank : t + 1 ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by
      rw [← Matrix.rank_eq_finrank_span_row A]
      omega
    obtain ⟨κ, a', ha'inj, hspanκ, hliκ⟩ := exists_linearIndependent' ℝ A.row
    haveI : Fintype κ := Fintype.ofInjective a' ha'inj
    have hcardκ : Fintype.card κ = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by
      have h2 := linearIndependent_iff_card_eq_finrank_span.mp hliκ
      rw [h2, Set.finrank, hspanκ]
    have hle : t + 1 ≤ Fintype.card κ := by omega
    let emb : Fin (t + 1) → κ := (Fintype.equivFin κ).symm ∘ Fin.castLE hle
    have hemb_inj : Function.Injective emb :=
      (Fintype.equivFin κ).symm.injective.comp (Fin.castLE_injective hle)
    let a : Fin (t + 1) → Fin N := a' ∘ emb
    have hli_a : LinearIndependent ℝ (A.row ∘ a) := hliκ.comp emb hemb_inj
    obtain ⟨b, hb⟩ := exists_minor_det_ne_zero_of_linearIndependent (A.row ∘ a) hli_a
    exact hb (h a b)

theorem finrank_span_le_iff_minors_eq_zero {N M t : ℕ} (ht : t + 1 ≤ N)
    (A : Fin N → (Fin M → ℝ)) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range A)) ≤ t ↔
      ∀ (a : Fin (t + 1) → Fin N) (b : Fin (t + 1) → Fin M),
        (Matrix.of (fun i j : Fin (t + 1) => A (a i) (b j))).det = 0 := by
  have h := matrix_rank_le_iff_minors_eq_zero ht (Matrix.of A)
  rw [Matrix.rank_eq_finrank_span_row] at h
  exact h

end Work.Drive
