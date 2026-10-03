import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnKeyRank
import Submission.Work.ORVonNeumann.Rep.vnAssembly
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnCyclicTrace
import Submission.Work.ORVonNeumann.Rep.vnMatOpEquivariant
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl
import Submission.Work.ORVonNeumann.Rep.vnHdimMono
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnMatOpOne
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagDefs
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagKernel
import Submission.Work.ORVonNeumann.Rep.vnBlockUpperKerInf

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### The diagonal right regular action on `HSum` -/

theorem diagOp_mul (n : ℕ) (g h : G) :
    (diagOp (G := G) n g).comp (diagOp (G := G) n h) = diagOp (G := G) n (g * h) := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  rw [ContinuousLinearMap.comp_apply, hcoord_diagOp_apply, hcoord_diagOp_apply, hcoord_diagOp_apply,
    rightRegOp_mul_apply]

theorem diagOp_inv (n : ℕ) (g : G) :
    (diagOp (G := G) n g).comp (diagOp (G := G) n g⁻¹) = 1 := by
  rw [diagOp_mul, mul_inv_cancel]
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  rw [hcoord_diagOp_apply, rightRegOp_one_apply, one_apply_eq_self]

theorem diagOp_adjoint (n : ℕ) (g : G) :
    ContinuousLinearMap.adjoint (diagOp (G := G) n g) = diagOp (G := G) n g⁻¹ := by
  rw [eq_comm]
  refine (ContinuousLinearMap.eq_adjoint_iff (diagOp (G := G) n g⁻¹) (diagOp (G := G) n g)).mpr ?_
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoord_apply (G := G) n i ((diagOp (G := G) n g⁻¹) x),
    ← hcoord_apply (G := G) n i ((diagOp (G := G) n g) y)]
  rw [hcoord_diagOp_apply, hcoord_diagOp_apply]
  rw [← rightRegOp_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  simp only [hcoord_apply]

/-- The star projection onto an equivariant subspace is equivariant. -/
theorem equivariant_starProjection {n : ℕ} {K : Submodule ℂ (HSum (G := G) n)}
    [K.HasOrthogonalProjection] (hK : ∀ g, ∀ x ∈ K, diagOp (G := G) n g x ∈ K) :
    Equivariant (G := G) K.starProjection := by
  intro g
  apply ContinuousLinearMap.ext
  intro x
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := K) (u := diagOp (G := G) n g x) (v := diagOp (G := G) n g (K.starProjection x)) ?_ ?_
  · exact hK g _ (Submodule.starProjection_apply_mem K x)
  · intro w hw
    rw [← map_sub, inner_eq_zero_symm,
      ← ContinuousLinearMap.adjoint_inner_left (A := diagOp (G := G) n g)
        (x := x - K.starProjection x) (y := w), diagOp_adjoint]
    exact (Submodule.mem_orthogonal K (x - K.starProjection x)).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _ (hK g⁻¹ w hw)

/-- The kernel of an equivariant operator is equivariant. -/
theorem equivariant_ker {m n : ℕ} {Z : HSum (G := G) m →L[ℂ] HSum (G := G) n}
    (hZ : Equivariant (G := G) Z) (g : G) (x : HSum (G := G) m) (hx : Z x = 0) :
    Z (diagOp (G := G) m g x) = 0 := by
  have h := congrArg (fun (f : HSum (G := G) m →L[ℂ] HSum (G := G) n) => f x) (hZ g)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, hx, map_zero]

/-- The retraction onto the second block is equivariant. -/
theorem vnBAK_equivariant_retR (a b : ℕ) :
    Equivariant (G := G) (retR (G := G) a b) := by
  intro g
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro k
  simp only [ContinuousLinearMap.comp_apply]
  simp only [vnBd_hcoord_retR, hcoord_diagOp_apply]

/-! ### Rank–nullity for equivariant operators -/

/-- For an equivariant operator on `HSum a`, the von Neumann dimensions of the kernel and of the
orthogonal complement of the kernel of the adjoint add up to `a` (rank–nullity, obtained from
`vnKeyRank` via `matOfEquiv`). -/
theorem rankNullity_equivariant {a : ℕ} {g : HSum (G := G) a →L[ℂ] HSum (G := G) a}
    (hg : Equivariant (G := G) g) :
    hdim (G := G) g.ker + hdim (G := G) (ContinuousLinearMap.adjoint g).kerᗮ = a := by
  have hY : matOp (G := G) (matOfEquiv (G := G) g hg) = g := matOp_matOfEquiv (G := G) g hg
  have hkey : hdim (G := G) (matOp (G := G) (matOfEquiv (G := G) g hg)).ker
      = hdim (G := G) (ContinuousLinearMap.adjoint
          (matOp (G := G) (matOfEquiv (G := G) g hg))).ker := by
    have h := vnKeyRank (G := G) (matOfEquiv (G := G) g hg)
    linarith [h]
  rw [hY] at hkey
  have hcomp := vnHdimCompl (G := G) (K := (ContinuousLinearMap.adjoint g).ker)
  linarith [hkey, hcomp]

/-- **The index identity (rank–nullity) for an equivariant operator between `HSum`s**:
`hdim (ker X) = hdim (ker X†) + m - n` for `X : HSum m → HSum n` equivariant.  This is
`vnKeyRank` transported across `matOfEquiv` (available in the rectangular form). -/
theorem vnBAK_index_equivariant {m n : ℕ} (X : HSum (G := G) m →L[ℂ] HSum (G := G) n)
    (hX : Equivariant (G := G) X) :
    hdim (G := G) X.ker
      = hdim (G := G) (ContinuousLinearMap.adjoint X).ker + (m : ℝ) - (n : ℝ) := by
  have hY : matOp (G := G) (matOfEquiv (G := G) X hX) = X := matOp_matOfEquiv (G := G) X hX
  have h := vnKeyRank (G := G) (matOfEquiv (G := G) X hX)
  rw [hY] at h
  linarith

/-- The kernel of the identity matrix operator on `HSum k` has von Neumann dimension `0`. -/
theorem vnBAK_hdim_ker_matOp_one (k : ℕ) :
    hdim (G := G)
      ((matOp (G := G) (1 : Matrix (Fin k) (Fin k) (↥(groupVonNeumann G)))).ker) = 0 := by
  have hbot : (matOp (G := G) (1 : Matrix (Fin k) (Fin k) (↥(groupVonNeumann G)))).ker
      = (⊥ : Submodule ℂ (HSum (G := G) k)) := by
    rw [vnMatOpOne]
    ext x
    simp
  exact (hdim_congr (G := G) hbot).trans (hdim_bot (G := G) k)

/-- A subspace with an orthogonal projection is closed. -/
theorem vnBAK_isClosed_of_hasOrthogonalProjection {N : ℕ}
    {K : Submodule ℂ (HSum (G := G) N)} [K.HasOrthogonalProjection] :
    IsClosed (K : Set (HSum (G := G) N)) := by
  rw [← Submodule.orthogonal_orthogonal (K := K)]
  exact Submodule.isClosed_orthogonal _

/-- A closed subspace has an orthogonal projection. -/
theorem vnBAK_hasOrthogonalProjection_of_isClosed {N : ℕ}
    {K : Submodule ℂ (HSum (G := G) N)} (h : IsClosed (K : Set (HSum (G := G) N))) :
    K.HasOrthogonalProjection := by
  haveI : IsClosed (K : Set (HSum (G := G) N)) := h
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace K

/-! ### Additivity of `hdim` for the kernel of the projection to a quotient

For a closed equivariant subspace `M` and an equivariant operator `π`, the map
`π ∘ P_M : HSum N → HSum a` has kernel `Mᗮ ⊔ (M ⊓ π.ker)` and adjoint with kernel of
orthogonal complement `cl (π M)`; the index identity for `π ∘ P_M` and `vnHdimCompl` then give
the exact-sequence additivity `hdim M = hdim (M ⊓ π.ker) + hdim (cl (π M))`. -/

/-- **The orthogonal projection onto `S.ker` for `S = π ∘ P_M`** splits as the sum of the
projections onto `Mᗮ` and onto `M ⊓ π.ker`. -/
theorem vnBAK_starProjection_ker_comp {N a : ℕ}
    (M : Submodule ℂ (HSum (G := G) N)) [M.HasOrthogonalProjection]
    (hM : Equivariant (G := G) M.starProjection)
    (π : HSum (G := G) N →L[ℂ] HSum (G := G) a) (hπ : Equivariant (G := G) π)
    [(M ⊓ π.ker).HasOrthogonalProjection] (x : HSum (G := G) N) :
    (π.comp M.starProjection).ker.starProjection x
      = Mᗮ.starProjection x + (M ⊓ π.ker).starProjection x := by
  have hS : Equivariant (G := G) (π.comp M.starProjection) := hM.comp hπ
  have hMorth : Submodule.IsOrtho M Mᗮ := Submodule.le_orthogonal_orthogonal M
  have hkerS : (π.comp M.starProjection).ker = Mᗮ ⊔ (M ⊓ π.ker) := by
    ext y
    rw [Submodule.mem_sup]
    constructor
    · intro hy
      have hy0 : π (M.starProjection y) = 0 := by
        exact LinearMap.mem_ker.mp hy
      exact ⟨y - M.starProjection y, Submodule.sub_starProjection_mem_orthogonal y,
        M.starProjection y, ⟨Submodule.starProjection_apply_mem M y, hy0⟩,
        sub_add_cancel y (M.starProjection y)⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      change π (M.starProjection (u + v)) = 0
      have hu0 : M.starProjection u = 0 := by
        rw [← Submodule.ker_starProjection] at hu
        exact LinearMap.mem_ker.mp hu
      have hv1 : M.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv.1
      have hv2 : π v = 0 := LinearMap.mem_ker.mp hv.2
      rw [map_add, map_add, hu0, map_zero, zero_add, hv1, hv2]
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (K := (π.comp M.starProjection).ker) ?_ ?_
  · rw [hkerS]
    exact Submodule.add_mem_sup (Submodule.starProjection_apply_mem _ _)
      (Submodule.starProjection_apply_mem _ _)
  · have hone : x - (Mᗮ.starProjection x + (M ⊓ π.ker).starProjection x) ∈ (Mᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      have h1 : inner ℂ x u = inner ℂ (Mᗮ.starProjection x) u := by
        have h := (Submodule.mem_orthogonal' (K := Mᗮ) (x - Mᗮ.starProjection x)).mp
          (Submodule.sub_starProjection_mem_orthogonal x) u hu
        rw [inner_sub_left, sub_eq_zero] at h
        exact h
      have h2 : inner ℂ ((M ⊓ π.ker).starProjection x) u = 0 :=
        Submodule.IsOrtho.inner_eq hMorth
          (Submodule.starProjection_apply_mem (M ⊓ π.ker) x).1 hu
      rw [inner_sub_left, inner_add_left, h1, h2]
      ring
    have htwo : x - (Mᗮ.starProjection x + (M ⊓ π.ker).starProjection x)
        ∈ (M ⊓ π.ker)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro v hv
      have h1 : inner ℂ x v = inner ℂ ((M ⊓ π.ker).starProjection x) v := by
        have h := (Submodule.mem_orthogonal' (K := M ⊓ π.ker)
          (x - (M ⊓ π.ker).starProjection x)).mp
          (Submodule.sub_starProjection_mem_orthogonal x) v hv
        rw [inner_sub_left, sub_eq_zero] at h
        exact h
      have h2 : inner ℂ (Mᗮ.starProjection x) v = 0 :=
        Submodule.IsOrtho.inner_eq hMorth.symm
          (Submodule.starProjection_apply_mem Mᗮ x) hv.1
      rw [inner_sub_left, inner_add_left, h1, h2]
      ring
    rw [hkerS, ← Submodule.inf_orthogonal]
    exact ⟨hone, htwo⟩

/-- **Slot: the exact-sequence additivity of the von Neumann dimension.** -/
theorem vnBAK_hdim_ker_inf_range {N a : ℕ}
    (M : Submodule ℂ (HSum (G := G) N)) [M.HasOrthogonalProjection]
    (hM : Equivariant (G := G) M.starProjection)
    (π : HSum (G := G) N →L[ℂ] HSum (G := G) a) (hπ : Equivariant (G := G) π)
    [(M ⊓ π.ker).HasOrthogonalProjection] :
    hdim (G := G) M = hdim (G := G) (M ⊓ π.ker)
      + hdim (G := G) ((M.map π.toLinearMap).topologicalClosure) := by
  have hS : Equivariant (G := G) (π.comp M.starProjection) := hM.comp hπ
  have hMorth : Submodule.IsOrtho M Mᗮ := Submodule.le_orthogonal_orthogonal M
  have horthTL : Submodule.IsOrtho Mᗮ (M ⊓ π.ker) :=
    Submodule.IsOrtho.mono_right inf_le_left hMorth.symm
  -- (i) the dimension of the kernel of `S = π ∘ P_M`
  have h1 : hdim (G := G) (π.comp M.starProjection).ker
      = hdim (G := G) Mᗮ + hdim (G := G) (M ⊓ π.ker) := by
    rw [hdim_apply, hdim_apply, hdim_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vnBAK_starProjection_ker_comp (G := G) M hM π hπ]
    simp only [sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (Mᗮ.starProjection (hdelta (G := G) N i))
      ((M ⊓ π.ker).starProjection (hdelta (G := G) N i))
      (Submodule.IsOrtho.inner_eq horthTL (Submodule.starProjection_apply_mem Mᗮ _)
        (Submodule.starProjection_apply_mem (M ⊓ π.ker) _))
  -- (ii) the index identity for `S`
  have h2 : hdim (G := G) (π.comp M.starProjection).ker
      = hdim (G := G) (ContinuousLinearMap.adjoint (π.comp M.starProjection)).ker
        + (N : ℝ) - (a : ℝ) := vnBAK_index_equivariant (G := G) _ hS
  -- (iii) the kernel of the adjoint of `S`
  have hrange : (π.comp M.starProjection).range = M.map π.toLinearMap := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨M.starProjection z, Submodule.starProjection_apply_mem M z, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, by
        change π (M.starProjection m) = π m
        rw [Submodule.starProjection_eq_self_iff.mpr hm]⟩
  have horth : ((ContinuousLinearMap.adjoint (π.comp M.starProjection)).ker)ᗮ
      = (M.map π.toLinearMap).topologicalClosure := by
    rw [ContinuousLinearMap.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint]
    exact congrArg Submodule.topologicalClosure hrange
  have h3 : hdim (G := G) (ContinuousLinearMap.adjoint (π.comp M.starProjection)).ker
      = (a : ℝ) - hdim (G := G) ((M.map π.toLinearMap).topologicalClosure) := by
    have hcomp := vnHdimCompl (G := G)
      (K := (ContinuousLinearMap.adjoint (π.comp M.starProjection)).ker)
    have hcc : hdim (G := G)
        ((ContinuousLinearMap.adjoint (π.comp M.starProjection)).ker)ᗮ
        = hdim (G := G) ((M.map π.toLinearMap).topologicalClosure) :=
      hdim_congr (G := G) horth
    linarith
  -- (iv) the dimension of `M`
  have h4 : hdim (G := G) M + hdim (G := G) Mᗮ = (N : ℝ) :=
    vnHdimCompl (G := G) (K := M)
  linarith

/-! ### The block structure of `blockUpper` -/

theorem vnBU_apply_inl_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (j' : Fin m) :
    (Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inl j))
      (finSumFinEquiv (Sum.inl j')) = A j j' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem vnBU_apply_inl_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (k' : Fin q) :
    (Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inl j))
      (finSumFinEquiv (Sum.inr k')) = C j k' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem vnBU_apply_inr_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (j' : Fin m) :
    (Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inr k))
      (finSumFinEquiv (Sum.inl j')) = 0 := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem vnBU_apply_inr_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (k' : Fin q) :
    (Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inr k))
      (finSumFinEquiv (Sum.inr k')) = B k k' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem vnBU_retR {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retR (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockUpper A C B) w)
      = matOp (G := G) B (retR (G := G) m q w) := by
  apply hsum_ext
  intro k
  rw [vnBd_hcoord_retR, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retR (G := G)]
  have hzero : (∑ j' : Fin m,
        ((Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inr k))
          (finSumFinEquiv (Sum.inl j')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w)) = 0 := by
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [vnBU_apply_inr_inl]
    simp
  have hright : (∑ k' : Fin q,
        ((Work.ORVonNeumann.blockUpper A C B) (finSumFinEquiv (Sum.inr k))
          (finSumFinEquiv (Sum.inr k')) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w))
      = ∑ k' : Fin q, ((B k k' : ↥(groupVonNeumann G)) : boundedEnd G)
            (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w) := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vnBU_apply_inr_inr]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hzero, zero_add, hright]

theorem vnBU_retL {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retL (G := G) n p (matOp (G := G) (Work.ORVonNeumann.blockUpper A C B) w)
      = matOp (G := G) A (retL (G := G) m q w) + matOp (G := G) C (retR (G := G) m q w) := by
  apply hsum_ext
  intro j
  rw [vnBd_hcoord_retL, map_add, hcoord_matOp_apply, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retL (G := G), vnBd_hcoord_retR (G := G)]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [vnBU_apply_inl_inl]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vnBU_apply_inl_inr]

/-! ### The kernel form of the block upper triangular inequality -/

/-- **The kernel form**: for a block upper triangular operator, the von Neumann dimension of the
kernel is at most the sum of the dimensions of the kernels of the two diagonal blocks.

This is the exact-sequence additivity `vnBAK_hdim_ker_inf_range` applied to
`M = ker (matOp [[A,C],[0,B]])` and the second coordinate retraction `π = retR m q`: the
intersection is `ker (matOp (blockDiag A 1))`, whose dimension is `hdim (ker (matOp A))` by
`vnBlockDiagKernel`, and the closure of the image is contained in `ker (matOp B)` by the
coordinate computation `vnBU_retR`. -/
theorem vnBAK_kernel_le {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) :
    hdim (G := G) ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker)
      ≤ hdim (G := G) ((matOp (G := G) A).ker) + hdim (G := G) ((matOp (G := G) B).ker) := by
  have hTeq : Equivariant (G := G) (matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)) :=
    vnMatOpEquivariant (G := G) (Work.ORVonNeumann.blockUpper A C B)
  have hretReq : Equivariant (G := G) (retR (G := G) m q) := vnBAK_equivariant_retR (G := G) m q
  have hM : Equivariant (G := G)
      ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker.starProjection) := by
    refine equivariant_starProjection (G := G) ?_
    intro g x hx
    exact equivariant_ker (G := G) hTeq g x hx
  haveI hTker : ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker).HasOrthogonalProjection :=
    vnBAK_hasOrthogonalProjection_of_isClosed (G := G)
      ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).isClosed_ker)
  haveI hAker : ((matOp (G := G) A).ker).HasOrthogonalProjection :=
    vnBAK_hasOrthogonalProjection_of_isClosed (G := G) ((matOp (G := G) A).isClosed_ker)
  haveI hBker : ((matOp (G := G) B).ker).HasOrthogonalProjection :=
    vnBAK_hasOrthogonalProjection_of_isClosed (G := G) ((matOp (G := G) B).isClosed_ker)
  haveI hInf : (((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker)
      ⊓ (retR (G := G) m q).ker).HasOrthogonalProjection := by
    haveI hcl : IsClosed ((((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker)
        ⊓ (retR (G := G) m q).ker : Submodule ℂ (HSum (G := G) (m + q))) :
          Set (HSum (G := G) (m + q))) :=
      ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).isClosed_ker).inter
        ((retR (G := G) m q).isClosed_ker)
    exact Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have hadd := vnBAK_hdim_ker_inf_range (G := G)
    ((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker) hM (retR (G := G) m q) hretReq
  have hK1 : hdim (G := G) (((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker)
        ⊓ (retR (G := G) m q).ker)
      = hdim (G := G) ((matOp (G := G) (Work.ORVonNeumann.blockDiag A
          (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G))))).ker) :=
    hdim_congr (G := G) (vnBlockUpperKerInf (G := G) A C B)
  have hK2 : hdim (G := G) ((matOp (G := G) (Work.ORVonNeumann.blockDiag A
        (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G))))).ker)
      = hdim (G := G) ((matOp (G := G) A).ker)
        + hdim (G := G) ((matOp (G := G)
            (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G)))).ker) :=
    vnBlockDiagKernel (G := G) A (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G)))
  have hK3 : hdim (G := G) ((matOp (G := G)
        (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G)))).ker) = 0 :=
    vnBAK_hdim_ker_matOp_one (G := G) q
  have hmono : hdim (G := G)
      ((((matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker).map
        (retR (G := G) m q).toLinearMap).topologicalClosure)
      ≤ hdim (G := G) ((matOp (G := G) B).ker) := by
    apply vnHdimMono (G := G)
    apply Submodule.topologicalClosure_minimal
    · intro z hz
      rw [Submodule.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hw0 : matOp (G := G) (Work.ORVonNeumann.blockUpper A C B) w = 0 :=
        LinearMap.mem_ker.mp hw
      have hret := vnBU_retR (G := G) A C B w
      rw [hw0, map_zero] at hret
      exact LinearMap.mem_ker.mpr hret.symm
    · exact (matOp (G := G) B).isClosed_ker
  linarith

/-! ### The adjoint form -/

theorem vnBlockUpperAdjointKernel {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) (C : Matrix (Fin n) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))) (B : Matrix (Fin p) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.hdim ((ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) (Work.ORVonNeumann.blockUpper A C B))).ker) ≤ Work.ORVonNeumann.Rep.hdim ((ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) A)).ker) + Work.ORVonNeumann.Rep.hdim ((ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) B)).ker) := by
  have hker := vnBAK_kernel_le (G := G) A C B
  have hTeq : Equivariant (G := G) (matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)) :=
    vnMatOpEquivariant (G := G) (Work.ORVonNeumann.blockUpper A C B)
  have hAeq : Equivariant (G := G) (matOp (G := G) A) := vnMatOpEquivariant (G := G) A
  have hBeq : Equivariant (G := G) (matOp (G := G) B) := vnMatOpEquivariant (G := G) B
  have hTidx := vnBAK_index_equivariant (G := G)
    (matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)) hTeq
  have hAidx := vnBAK_index_equivariant (G := G) (matOp (G := G) A) hAeq
  have hBidx := vnBAK_index_equivariant (G := G) (matOp (G := G) B) hBeq
  push_cast at hTidx hAidx hBidx ⊢
  linarith

end Work.ORVonNeumann.Rep
