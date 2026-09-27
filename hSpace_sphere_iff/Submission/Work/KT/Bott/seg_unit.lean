import Mathlib
import Submission.Work.KT.Bott.LauDefs
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one

/-!
# `Work.KT.Bott.seg_unit` — matrices near a unit, and the straight-line segment to them

Let `u` be an invertible matrix over `C(X, ℂ)` (`X` compact) with two-sided inverse `A`, and let `V`
be any matrix with `mNorm n (u - V) * mNorm n A < 1`.  Then `V` is invertible, and so is the
straight-line segment `(1 - t) u + t V` in the matrix ring over `C(X × [0,1], ℂ)`.

This is the "nearby unit and its straight-line homotopy" input of the Laurent approximation
`Work.KT.Bott.laurent_approx` (see `NOTES_seg_unit.md`): the segment is the homotopy `H` exhibiting
the invertible matrix `V` as homotopic to `u` through invertible matrices.

The argument, in two steps:

* **Abstract step** (any complete commutative normed ring `R`).  With `hu := Units.mk u A h1 h2`
  one has the identity
  `(1 - c) • u + c • V = u * (1 - c • (A * (u - V)))`
  (`u * A = 1` collapses the middle factor), the perturbation `c • (A * (u - V))` has
  `mNorm ≤ ‖c‖ * mNorm A * mNorm (u - V)` by submultiplicativity and `mNorm_smul_le`, and this is
  `< 1` when `‖c‖ ≤ 1` and `mNorm (u - V) * mNorm A < 1`.  So `1 - c • (A * (u - V))` is a unit by
  the Neumann series (`Work.KT.isUnit_one_sub_of_matNorm_lt_one`) and hence so is the product.
  The case `c = 1` of this identity reads `V = u * (1 - A * (u - V))`, giving `IsUnit V`.

* **Transport step.**  Apply the abstract step over `R = C(X × [0,1], ℂ)` to the pullbacks
  `u.map φ`, `V.map φ`, `A.map φ` along the ring homomorphism `φ : C(X, ℂ) →+* C(X × [0,1], ℂ)`
  induced by the projection `X × [0,1] → X`, with `c = LauDefs.tC X` the parameter `t`.  The norm
  bounds `mNorm (u.map φ - V.map φ) ≤ mNorm (u - V)` and `mNorm (A.map φ) ≤ mNorm A` hold by
  `LauDefs.mNorm_map_le` (a pullback along a projection does not increase the sup norm), the step
  function has `‖tC X‖ ≤ 1`, and `seg u V = (1 - tC X) • u.map φ + tC X • V.map φ` by definition.
-/

namespace Work.KT.Bott

open Matrix

noncomputable section

/-- **A matrix close to an invertible matrix is invertible** (Neumann series).  If `u * A = 1` and
`A * u = 1` (so `u` is a unit with inverse `A`) and `mNorm n (u - V) * mNorm n A < 1`, then `V` is a
unit: indeed `V = u * (1 - A * (u - V))` is a unit times a Neumann-series unit. -/
lemma isUnit_of_mNorm_sub_mul_lt_one {R : Type*} [NormedRing R] [CompleteSpace R] {n : ℕ}
    {u V A : Matrix (Fin n) (Fin n) R} (h1 : u * A = 1) (h2 : A * u = 1)
    (h : LauDefs.mNorm n (u - V) * LauDefs.mNorm n A < 1) : IsUnit V := by
  have hu : IsUnit u := ⟨Units.mk u A h1 h2, rfl⟩
  have hne : LauDefs.mNorm n (A * (u - V)) < 1 := by
    calc LauDefs.mNorm n (A * (u - V))
        ≤ LauDefs.mNorm n A * LauDefs.mNorm n (u - V) := LauDefs.mNorm_mul_le n _ _
      _ = LauDefs.mNorm n (u - V) * LauDefs.mNorm n A := mul_comm _ _
      _ < 1 := h
  have hprod : IsUnit (u * (1 - A * (u - V))) :=
    hu.mul (isUnit_one_sub_of_matNorm_lt_one _ hne)
  have heq : u * (1 - A * (u - V)) = V := by
    rw [mul_sub, mul_one, ← mul_assoc, h1, one_mul, sub_sub_cancel]
  rwa [heq] at hprod

/-- **The convex combination `(1 - c) • u + c • V` of two nearby matrices is invertible.**  If `u` is
a unit with inverse `A` (i.e. `u * A = 1` and `A * u = 1`), `mNorm n (u - V) * mNorm n A < 1` and
`‖c‖ ≤ 1`, then `(1 - c) • u + c • V` is a unit: it equals `u * (1 - c • (A * (u - V)))`, a unit
times a Neumann-series unit. -/
lemma isUnit_one_sub_smul {R : Type*} [NormedCommRing R] [CompleteSpace R] {n : ℕ}
    {u V A : Matrix (Fin n) (Fin n) R} (h1 : u * A = 1) (h2 : A * u = 1)
    (h : LauDefs.mNorm n (u - V) * LauDefs.mNorm n A < 1) (c : R) (hc : ‖c‖ ≤ 1) :
    IsUnit ((1 - c) • u + c • V) := by
  have hu : IsUnit u := ⟨Units.mk u A h1 h2, rfl⟩
  have hc' : ‖c‖₊ ≤ 1 := by rw [← NNReal.coe_le_coe]; simpa using hc
  have hne : LauDefs.mNorm n (c • (A * (u - V))) < 1 := by
    calc LauDefs.mNorm n (c • (A * (u - V)))
        ≤ ‖c‖₊ * LauDefs.mNorm n (A * (u - V)) := LauDefs.mNorm_smul_le n c _
      _ ≤ ‖c‖₊ * (LauDefs.mNorm n A * LauDefs.mNorm n (u - V)) :=
          mul_le_mul_of_nonneg_left (LauDefs.mNorm_mul_le n _ _) (by positivity)
      _ ≤ 1 * (LauDefs.mNorm n A * LauDefs.mNorm n (u - V)) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = LauDefs.mNorm n (u - V) * LauDefs.mNorm n A := by ring
      _ < 1 := h
  have hprod : IsUnit (u * (1 - c • (A * (u - V)))) :=
    hu.mul (isUnit_one_sub_of_matNorm_lt_one _ hne)
  have heq : u * (1 - c • (A * (u - V))) = (1 - c) • u + c • V := by
    rw [mul_sub, mul_one, Matrix.mul_smul, ← mul_assoc, h1, one_mul, smul_sub, sub_smul, one_smul]
    abel
  rwa [heq] at hprod

theorem seg_unit {X : Type} [TopologicalSpace X] [CompactSpace X] (n : ℕ)
    (u V A : Matrix (Fin n) (Fin n) C(X, ℂ))
    (h1 : u * A = 1) (h2 : A * u = 1)
    (h : LauDefs.mNorm n (u - V) * LauDefs.mNorm n A < 1) :
    IsUnit V ∧ IsUnit (LauDefs.seg u V) := by
  refine ⟨isUnit_of_mNorm_sub_mul_lt_one h1 h2 h, ?_⟩
  -- pullback along the projection `X × [0,1] → X`
  let φ : C(X, ℂ) →+* C(X × unitInterval, ℂ) :=
    { toFun := fun f => f.comp (ContinuousMap.fst : C(X × unitInterval, X))
      map_one' := by ext p; rfl
      map_mul' := by intro a b; ext p; rfl
      map_zero' := by ext p; rfl
      map_add' := by intro a b; ext p; rfl }
  have hφ : ∀ a : C(X, ℂ), ‖φ a‖ ≤ ‖a‖ := by
    intro a
    rw [ContinuousMap.norm_le (φ a) (norm_nonneg a)]
    intro p
    simpa [φ] using ContinuousMap.norm_coe_le_norm a p.1
  have h1' : u.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul (f := φ), h1]
    exact Matrix.map_one (φ : C(X, ℂ) → C(X × unitInterval, ℂ)) (map_zero φ) (map_one φ)
  have h2' : A.map φ * u.map φ = 1 := by
    rw [← Matrix.map_mul (f := φ), h2]
    exact Matrix.map_one (φ : C(X, ℂ) → C(X × unitInterval, ℂ)) (map_zero φ) (map_one φ)
  -- the perturbation is still small after pulling back
  have h' : LauDefs.mNorm n (u.map φ - V.map φ) * LauDefs.mNorm n (A.map φ) < 1 := by
    have hA : LauDefs.mNorm n (A.map φ) ≤ LauDefs.mNorm n A := LauDefs.mNorm_map_le n φ hφ A
    have hUV : LauDefs.mNorm n (u.map φ - V.map φ) ≤ LauDefs.mNorm n (u - V) := by
      rw [← Matrix.map_sub (φ : C(X, ℂ) → C(X × unitInterval, ℂ))
        (fun a b => map_sub φ a b) u V]
      exact LauDefs.mNorm_map_le n φ hφ (u - V)
    exact lt_of_le_of_lt (mul_le_mul hUV hA (by positivity) (by positivity)) h
  have hc : ‖(LauDefs.tC X : C(X × unitInterval, ℂ))‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro p
    have ht : ‖LauDefs.tC X p‖ = |((p.2 : unitInterval) : ℝ)| := by
      rw [LauDefs.tC_apply]; exact RCLike.norm_ofReal _
    rw [ht, abs_of_nonneg p.2.2.1]
    exact p.2.2.2
  have hmain : IsUnit ((1 - LauDefs.tC X) • u.map φ + LauDefs.tC X • V.map φ) :=
    isUnit_one_sub_smul h1' h2' h' (LauDefs.tC X) hc
  have heq : LauDefs.seg u V = (1 - LauDefs.tC X) • u.map φ + LauDefs.tC X • V.map φ := by
    ext i j p
    simp [LauDefs.seg, φ, Matrix.map_apply, ContinuousMap.comp_apply]
  rwa [heq]

end

end Work.KT.Bott
