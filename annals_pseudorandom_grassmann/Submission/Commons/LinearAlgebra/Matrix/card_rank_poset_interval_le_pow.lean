import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Submission.Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_iff

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Matrix

open Module

/-- If `Y.rank = Y'.rank + (Y - Y').rank` then `ker Y ≤ ker Y'`. -/
theorem rank_poset_ker_le {K : Type*} [Field K] {n m : ℕ}
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank) :
    LinearMap.ker Y.mulVecLin ≤ LinearMap.ker Y'.mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  simp only [Matrix.mulVecLin_apply] at hv ⊢
  have hcond := (rank_poset_iff Y' Y).mp h
  have hmem : Y.mulVec v ∈ LinearMap.range Y'.mulVecLin := by
    rw [hv]; exact Submodule.zero_mem _
  rw [hcond.2 v hmem, hv]

/-- The descended map `U = range Y → range Y'`. -/
noncomputable def rank_poset_lift {K : Type*} [Field K] {n m : ℕ}
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank) :
    (LinearMap.range Y.mulVecLin) →ₗ[K] (Fin n → K) :=
  (Submodule.liftQ (LinearMap.ker Y.mulVecLin) Y'.mulVecLin (rank_poset_ker_le Y Y' h)).comp
    (LinearMap.quotKerEquivRange Y.mulVecLin).symm.toLinearMap

/-- The descended map `U → range Y'` evaluated on `Y.mulVecLin w`. -/
theorem rank_poset_lift_apply {K : Type*} [Field K] {n m : ℕ}
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank)
    (w : Fin m → K) :
    rank_poset_lift Y Y' h ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩ = Y'.mulVecLin w := by
  simp only [rank_poset_lift, LinearMap.comp_apply, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply, LinearEquiv.coe_toLinearMap]

/-- The descended map `U → range Y` lands in `U = range Y`. -/
theorem rank_poset_lift_mem_range {K : Type*} [Field K] {n m : ℕ}
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank) :
    ∀ x : LinearMap.range Y.mulVecLin,
      rank_poset_lift Y Y' h x ∈ LinearMap.range Y.mulVecLin := by
  intro x
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp x.2
  have hx : x = ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩ := Subtype.ext hw.symm
  rw [hx, rank_poset_lift_apply]
  exact ((rank_poset_iff Y' Y).mp h).1 (LinearMap.mem_range_self _ w)

/-- The endomorphism of `U = range Y.mulVecLin` induced by a matrix `Y'` below `Y` in the rank
poset. -/
noncomputable def rank_poset_to_end {K : Type*} [Field K] (n m : ℕ)
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank) :
    (LinearMap.range Y.mulVecLin →ₗ[K] LinearMap.range Y.mulVecLin) :=
  LinearMap.codRestrict _ (rank_poset_lift Y Y' h) (rank_poset_lift_mem_range Y Y' h)

theorem rank_poset_to_end_apply {K : Type*} [Field K] {n m : ℕ}
    (Y Y' : Matrix (Fin n) (Fin m) K) (h : Y.rank = Y'.rank + (Y - Y').rank)
    (w : Fin m → K) :
    ((rank_poset_to_end n m Y Y' h) ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩ : Fin n → K)
      = Y'.mulVecLin w := by
  rw [rank_poset_to_end, LinearMap.codRestrict_apply, rank_poset_lift_apply]

/-- General field version of the cardinality bound for the rank-poset interval. -/
theorem card_rank_poset_interval_le_pow_general {K : Type*} [Field K] [Fintype K]
    (n m : ℕ) (Y : Matrix (Fin n) (Fin m) K) :
    Nat.card {Y' : Matrix (Fin n) (Fin m) K // Y.rank = Y'.rank + (Y - Y').rank}
      ≤ Nat.card K ^ (Y.rank * Y.rank) := by
  classical
  set U : Submodule K (Fin n → K) := LinearMap.range Y.mulVecLin with hU
  have hfr : Module.finrank K U = Y.rank := by rw [hU]; rfl
  haveI : Finite (U →ₗ[K] U) :=
    Finite.of_injective (fun f : U →ₗ[K] U => (f : U → U)) DFunLike.coe_injective
  let Φ : {Y' : Matrix (Fin n) (Fin m) K // Y.rank = Y'.rank + (Y - Y').rank} → (U →ₗ[K] U) :=
    fun Y' => rank_poset_to_end n m Y Y'.1 Y'.2
  have hΦ : Function.Injective Φ := by
    intro Y'₁ Y'₂ hEq
    apply Subtype.ext
    have hfun : Y'₁.1.mulVecLin = Y'₂.1.mulVecLin := by
      apply LinearMap.ext
      intro w
      have h1 : ((Φ Y'₁) ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩ : Fin n → K)
          = Y'₁.1.mulVecLin w :=
        rank_poset_to_end_apply Y Y'₁.1 Y'₁.2 w
      have h2 : ((Φ Y'₂) ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩ : Fin n → K)
          = Y'₂.1.mulVecLin w :=
        rank_poset_to_end_apply Y Y'₂.1 Y'₂.2 w
      have hcong := congrArg (fun f : U →ₗ[K] U =>
        ((f ⟨Y.mulVecLin w, LinearMap.mem_range_self _ w⟩) : Fin n → K)) hEq
      rw [h1, h2] at hcong
      exact hcong
    ext i j
    have hc := congrArg (fun f : (Fin m → K) →ₗ[K] (Fin n → K) => f (Pi.single j 1) i) hfun
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at hc
    exact hc
  have hb : Basis (Fin (Module.finrank K U)) K U := Module.finBasis K U
  have hinj : Function.Injective (fun f : U →ₗ[K] U => (fun i => f (hb i))) := by
    intro f g hfg
    exact Basis.ext hb (fun i => congrFun hfg i)
  have hcard : Nat.card (U →ₗ[K] U) ≤ Nat.card K ^ (Y.rank * Y.rank) := by
    calc Nat.card (U →ₗ[K] U)
        ≤ Nat.card (Fin (Module.finrank K U) → U) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card U ^ (Module.finrank K U) := by rw [Nat.card_fun, Nat.card_fin]
      _ = (Nat.card K ^ Module.finrank K U) ^ Module.finrank K U := by
            rw [Module.natCard_eq_pow_finrank (K := K) (V := U)]
      _ = Nat.card K ^ (Module.finrank K U * Module.finrank K U) := by rw [pow_mul]
      _ = Nat.card K ^ (Y.rank * Y.rank) := by rw [hfr]
  calc Nat.card {Y' : Matrix (Fin n) (Fin m) K // Y.rank = Y'.rank + (Y - Y').rank}
      ≤ Nat.card (U →ₗ[K] U) := Nat.card_le_card_of_injective Φ hΦ
    _ ≤ Nat.card K ^ (Y.rank * Y.rank) := hcard

theorem card_rank_poset_interval_le_pow (n m : ℕ) (Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    Nat.card {Y' : Matrix (Fin n) (Fin m) (ZMod 2) // Y.rank = Y'.rank + (Y - Y').rank}
      ≤ 2 ^ (Y.rank * Y.rank) := by
  have h := card_rank_poset_interval_le_pow_general (K := ZMod 2) n m Y
  rwa [Nat.card_zmod] at h

end Commons.LinearAlgebra.Matrix