import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

def golodShafarevich_gradedPart (K ι : Type*) [Field K] (n : ℕ) :
    Submodule K (FreeAlgebra K ι) :=
  Submodule.span K {x | ∃ w : FreeMonoid ι,
    (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}

def golodShafarevich_twoSidedIdeal (K ι σ : Type*) [Field K]
    (rel : σ → FreeAlgebra K ι) : Submodule K (FreeAlgebra K ι) :=
  Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
    x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}

lemma golodShafarevich_basisFreeMonoid_one {K ι : Type*} [Field K] :
    FreeAlgebra.basisFreeMonoid K ι (1 : FreeMonoid ι) = 1 := by
  unfold FreeAlgebra.basisFreeMonoid
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv (R := K))).symm
      (Finsupp.single (1 : FreeMonoid ι) 1) = 1
  rw [LinearEquiv.symm_trans_apply]
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

lemma golodShafarevich_basisFreeMonoid_of {K ι : Type*} [Field K] (i : ι) :
    FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) = FreeAlgebra.ι K i := by
  unfold FreeAlgebra.basisFreeMonoid
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv (R := K))).symm
      (Finsupp.single (FreeMonoid.of i) 1) = FreeAlgebra.ι K i
  rw [LinearEquiv.symm_trans_apply]
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

lemma golodShafarevich_basisFreeMonoid_mul {K ι : Type*} [Field K] (u v : FreeMonoid ι) :
    FreeAlgebra.basisFreeMonoid K ι (u * v) =
      FreeAlgebra.basisFreeMonoid K ι u * FreeAlgebra.basisFreeMonoid K ι v := by
  unfold FreeAlgebra.basisFreeMonoid
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv (R := K))).symm
      (Finsupp.single (u * v) 1) =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv (R := K))).symm (Finsupp.single u 1) *
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans
      (MonoidAlgebra.coeffLinearEquiv (R := K))).symm (Finsupp.single v 1)
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply]
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]

lemma golodShafarevich_algebraMapInv_ι_eq_zero {K ι : Type*} [Field K] (i : ι) :
    algebraMapInv (FreeAlgebra.ι K i) = (0 : K) := by
  simp [algebraMapInv, lift_ι_apply]

lemma golodShafarevich_algebraMapInv_basis_of_ne_one {K ι : Type*} [Field K]
    (w : FreeMonoid ι) (hw : w ≠ 1) :
    algebraMapInv (FreeAlgebra.basisFreeMonoid K ι w) = 0 := by
  induction w using FreeMonoid.recOn with
  | one => exact (hw rfl).elim
  | of_mul x xs ih =>
      rw [golodShafarevich_basisFreeMonoid_mul (FreeMonoid.of x) xs,
        golodShafarevich_basisFreeMonoid_of, map_mul,
        golodShafarevich_algebraMapInv_ι_eq_zero, zero_mul]

lemma golodShafarevich_algebraMapInv_basis_of_length_pos {K ι : Type*} [Field K]
    (w : FreeMonoid ι) (h : 0 < (FreeMonoid.toList w).length) :
    algebraMapInv (FreeAlgebra.basisFreeMonoid K ι w) = 0 := by
  apply golodShafarevich_algebraMapInv_basis_of_ne_one
  intro hw
  have hlen : (FreeMonoid.toList w).length = 0 := by simp [hw]
  omega

lemma golodShafarevich_algebraMapInv_eq_zero_of_mem_gradedPart
    {K ι : Type*} [Field K] {d : ℕ} {x : FreeAlgebra K ι}
    (hd : 2 ≤ d) (hx : x ∈ golodShafarevich_gradedPart K ι d) :
    algebraMapInv x = 0 := by
  refine Submodule.span_induction (p := fun x _ => algebraMapInv x = 0) ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with ⟨w, hlen, rfl⟩
    have hlenpos : 0 < (FreeMonoid.toList w).length := by omega
    exact golodShafarevich_algebraMapInv_basis_of_length_pos w hlenpos
  · simp
  · intro x y hx hy hx0 hy0
    rw [map_add, hx0, hy0, add_zero]
  · intro a x hx hx0
    rw [map_smul, hx0, smul_zero]

lemma golodShafarevich_twoSidedIdeal_le_ker_aug {K ι σ : Type*} [Field K]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r)) :
    golodShafarevich_twoSidedIdeal K ι σ rel ≤
      LinearMap.ker (algebraMapInv : FreeAlgebra K ι →ₐ[K] K).toLinearMap := by
  rw [golodShafarevich_twoSidedIdeal, Submodule.span_le]
  intro x hx
  rcases hx with ⟨r, v, w, rfl⟩
  have hrel0 : algebraMapInv (rel r) = 0 :=
    golodShafarevich_algebraMapInv_eq_zero_of_mem_gradedPart (hdeg r) (hhom r)
  change algebraMapInv (FreeAlgebra.basisFreeMonoid K ι v * rel r *
    FreeAlgebra.basisFreeMonoid K ι w) = 0
  rw [map_mul, map_mul, hrel0, mul_zero, zero_mul]

lemma golodShafarevich_one_not_mem_twoSidedIdeal {K ι σ : Type*} [Field K]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r)) :
    (1 : FreeAlgebra K ι) ∉ golodShafarevich_twoSidedIdeal K ι σ rel := by
  intro h1
  have hle := golodShafarevich_twoSidedIdeal_le_ker_aug degRel rel hdeg hhom
  have hmemker : (1 : FreeAlgebra K ι) ∈
      LinearMap.ker (algebraMapInv : FreeAlgebra K ι →ₐ[K] K).toLinearMap := hle h1
  have hone : algebraMapInv (1 : FreeAlgebra K ι) = (1 : K) := by simp [algebraMapInv]
  have hzero : (1 : K) = 0 := by
    rw [← hone]
    exact hmemker
  exact zero_ne_one hzero.symm

lemma golodShafarevich_gradedPart_zero_eq_span_one {K ι : Type*} [Field K] :
    golodShafarevich_gradedPart K ι 0 = K ∙ (1 : FreeAlgebra K ι) := by
  apply le_antisymm
  · rw [golodShafarevich_gradedPart, Submodule.span_le]
    intro x hx
    rcases hx with ⟨w, hlen, rfl⟩
    have hlist : FreeMonoid.toList w = [] := List.eq_nil_of_length_eq_zero hlen
    have hw : w = 1 := by
      apply FreeMonoid.toList.injective
      simpa [FreeMonoid.toList_one] using hlist
    rw [hw, golodShafarevich_basisFreeMonoid_one]
    exact Submodule.mem_span_singleton_self _
  · rw [Submodule.span_singleton_le_iff_mem, golodShafarevich_gradedPart]
    apply Submodule.subset_span
    refine ⟨1, ?_, golodShafarevich_basisFreeMonoid_one.symm⟩
    simp

theorem golod_shafarevich_degree_zero_finrank
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      degreeSubmodule (degRel r)) :
    let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
      Submodule.span K {x | ∃ w : FreeMonoid ι,
        (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
    let twoSidedSpan : (σ → FreeAlgebra K ι) → Submodule K (FreeAlgebra K ι) := fun rel =>
      Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
        x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}
    Module.finrank K
      (Submodule.map (Submodule.mkQ (twoSidedSpan rel)) (degreeSubmodule 0)) = 1 := by
  dsimp
  change Module.finrank K
    (Submodule.map (Submodule.mkQ (golodShafarevich_twoSidedIdeal K ι σ rel))
      (golodShafarevich_gradedPart K ι 0)) = 1
  rw [golodShafarevich_gradedPart_zero_eq_span_one]
  rw [Submodule.map_span]
  have h1not : (1 : FreeAlgebra K ι) ∉ golodShafarevich_twoSidedIdeal K ι σ rel := by
    exact golodShafarevich_one_not_mem_twoSidedIdeal degRel rel hdeg (by
      intro r
      exact hhom r)
  have hne : Submodule.Quotient.mk (p := golodShafarevich_twoSidedIdeal K ι σ rel)
      (1 : FreeAlgebra K ι) ≠ 0 := by
    intro hq
    rw [Submodule.Quotient.mk_eq_zero] at hq
    exact h1not hq
  rw [Set.image_singleton]
  change Module.finrank K
    (K ∙ (Submodule.Quotient.mk (p := golodShafarevich_twoSidedIdeal K ι σ rel)
      (1 : FreeAlgebra K ι))) = 1
  exact finrank_span_singleton hne

end Commons.Algebra.FreeAlgebra