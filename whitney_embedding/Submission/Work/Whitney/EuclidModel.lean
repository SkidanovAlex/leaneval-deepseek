import Mathlib
import Submission.Work.Whitney.LocalModel

/-!
# Transporting the cut-off local model to `EuclideanSpace ℝ (Fin n)`

`Work.Whitney.inclModel n` and the cut-off models `β` of `Submission/Work/Whitney/LocalModel.lean`
live on the product `(Fin n → ℝ) × (Fin n → ℝ)` of *function* spaces (carrying the sup norm),
whereas the tubular parametrisation `H` of `Work.Whitney.exists_tubular_param` lives on
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` (carrying the `L²` norm).  This file provides
the translation between the two worlds:

* `Work.Whitney.euclidOfLp`, `Work.Whitney.lpOfEuclid` — the linear isomorphisms (not isometries!)
  `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` given by `WithLp.ofLp` / `WithLp.toLp`;
* `Work.Whitney.pairToE`, `Work.Whitney.pairOfE` — their componentwise versions on pairs;
* `Work.Whitney.scaledModel n lam β` — `x ↦ (1/lam) • β (lam • x)`, the *scaling* of a model `β`,
  which keeps its double point pair but moves it to `a/lam`, `b/lam` and shrinks the support;
* `Work.Whitney.euclidModel n lam β` — the transported and scaled model
  `u ↦ pairToE (scaledModel n lam β (euclidOfLp n u))`, a map `EuclideanSpace ℝ (Fin n) → ℝⁿ × ℝⁿ`.

The point of the scaling: the bounds that a model `β` satisfies in the sup norm on `(Fin n → ℝ)`
(`‖β x - inclModel x‖ ≤ δ`, `β x = inclModel x` for `‖x‖ ≥ R`) translate into the same bounds in
the `L²` norm *only* after dividing by `√n`; taking `lam = √n` restores the constants `δ` and `R` in
the `L²` world (`norm_lpOfEuclid_le` is the norm comparison `‖toLp x‖ ≤ √n ‖x‖`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- The underlying-function map `EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)` (`WithLp.ofLp`),
as a continuous linear map. -/
noncomputable def euclidOfLp (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ)).toContinuousLinearMap

/-- The inverse of `euclidOfLp` (`WithLp.toLp`), as a continuous linear map. -/
noncomputable def lpOfEuclid (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ)).symm.toContinuousLinearMap

@[simp] theorem euclidOfLp_apply (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    euclidOfLp n u = u.ofLp := rfl

@[simp] theorem lpOfEuclid_apply (n : ℕ) (x : Fin n → ℝ) :
    (lpOfEuclid n x : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 x := rfl

@[simp] theorem euclidOfLp_lpOfEuclid (n : ℕ) (x : Fin n → ℝ) :
    euclidOfLp n (lpOfEuclid n x) = x := WithLp.ofLp_toLp 2 x

@[simp] theorem lpOfEuclid_euclidOfLp (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    lpOfEuclid n (euclidOfLp n u) = u := WithLp.toLp_ofLp 2 u

theorem euclidOfLp_comp_lpOfEuclid (n : ℕ) :
    euclidOfLp n ∘L lpOfEuclid n = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  ext x; simp

theorem lpOfEuclid_comp_euclidOfLp (n : ℕ) :
    lpOfEuclid n ∘L euclidOfLp n = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext x; simp

/-- The componentwise transport `(x, y) ↦ (toLp x, toLp y)` on pairs. -/
noncomputable def pairToE (n : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ]
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  ((lpOfEuclid n).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))).prod
    ((lpOfEuclid n).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)))

/-- The inverse of `pairToE`. -/
noncomputable def pairOfE (n : ℕ) : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
    ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ((euclidOfLp n).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))).prod
    ((euclidOfLp n).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))))

@[simp] theorem pairToE_apply (n : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    pairToE n z = (lpOfEuclid n z.1, lpOfEuclid n z.2) := rfl

@[simp] theorem pairOfE_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    pairOfE n z = (euclidOfLp n z.1, euclidOfLp n z.2) := rfl

@[simp] theorem pairOfE_pairToE (n : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    pairOfE n (pairToE n z) = z := by
  obtain ⟨x, y⟩ := z
  simp

@[simp] theorem pairToE_pairOfE (n : ℕ) (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    pairToE n (pairOfE n z) = z := by
  obtain ⟨x, y⟩ := z
  simp

theorem euclidOfLp_injective (n : ℕ) : Function.Injective (euclidOfLp n) :=
  fun a b h => by simpa using congrArg (lpOfEuclid n) h

theorem lpOfEuclid_injective (n : ℕ) : Function.Injective (lpOfEuclid n) :=
  fun a b h => by simpa using congrArg (euclidOfLp n) h

theorem pairToE_injective (n : ℕ) : Function.Injective (pairToE n) :=
  fun a b h => by simpa using congrArg (pairOfE n) h

theorem pairOfE_injective (n : ℕ) : Function.Injective (pairOfE n) :=
  fun a b h => by simpa using congrArg (pairToE n) h

theorem pairToE_surjective (n : ℕ) : Function.Surjective (pairToE n) :=
  fun z => ⟨pairOfE n z, by simp⟩

theorem pairToE_range (n : ℕ) : (pairToE n).range = ⊤ :=
  LinearMap.range_eq_top.mpr (pairToE_surjective n)

theorem lpOfEuclid_range (n : ℕ) : (lpOfEuclid n).range = ⊤ :=
  LinearMap.range_eq_top.mpr (fun z => ⟨euclidOfLp n z, by simp⟩)

theorem pairOfE_comp_pairToE (n : ℕ) :
    pairOfE n ∘L pairToE n = ContinuousLinearMap.id ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ContinuousLinearMap.ext fun z => by simp

theorem pairToE_comp_pairOfE (n : ℕ) :
    pairToE n ∘L pairOfE n = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  ContinuousLinearMap.ext fun z => by simp

/-- **Norm comparison**: the `L²` norm of `WithLp.toLp x` is at most `√n` times the sup norm of
`x`.  (This is the only place where the mismatch between the two worlds is quantified.) -/
theorem norm_lpOfEuclid_le (n : ℕ) (x : Fin n → ℝ) :
    ‖lpOfEuclid n x‖ ≤ Real.sqrt n * ‖x‖ := by
  have hcoe : lpOfEuclid n x = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) := rfl
  rw [hcoe, EuclideanSpace.norm_eq]
  have h1 : ∀ i : Fin n, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i‖ ≤ ‖x‖ := by
    intro i
    have h : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i = x i := rfl
    rw [h]
    exact norm_le_pi_norm x i
  have h2 : ∑ i : Fin n, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i‖ ^ 2
      ≤ ∑ _i : Fin n, ‖x‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h1 i) 2
  have h3 : ∑ _i : Fin n, ‖x‖ ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin n, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i‖ ^ 2)
      ≤ Real.sqrt ((n : ℝ) * ‖x‖ ^ 2) := by rw [← h3]; exact Real.sqrt_le_sqrt h2
    _ = Real.sqrt n * ‖x‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg x)]

/-- The componentwise norm comparison for pairs. -/
theorem norm_pairToE_le (n : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖pairToE n z‖ ≤ Real.sqrt n * ‖z‖ := by
  obtain ⟨x, y⟩ := z
  refine max_le ?_ ?_
  · exact (norm_lpOfEuclid_le n x).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (x, y)) (Real.sqrt_nonneg n))
  · exact (norm_lpOfEuclid_le n y).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le ((x, y) : (Fin n → ℝ) × (Fin n → ℝ)))
        (Real.sqrt_nonneg n))

/-- Cancellation of a scalar and its inverse, in the exact shape in which it occurs below. -/
theorem smul_one_div_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (lam : ℝ) (hlam : lam ≠ 0)
    (x : E) : lam • ((1 / lam) • x) = x := by
  rw [smul_smul]
  have h : lam * (1 / lam) = 1 := by field_simp
  rw [h, one_smul]

/-- Cancellation of the inverse of a scalar with the scalar. -/
theorem one_div_smul_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (lam : ℝ) (hlam : lam ≠ 0)
    (x : E) : (1 / lam) • (lam • x) = x := by
  rw [smul_smul]
  have h : 1 / lam * lam = 1 := by field_simp
  rw [h, one_smul]

/-- **The scaled model** `x ↦ (1/lam) • β (lam • x)`. -/
noncomputable def scaledModel (n : ℕ) (lam : ℝ) (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun x => (1 / lam) • β (lam • x)

/-- **The transported and scaled model**, a map `EuclideanSpace ℝ (Fin n) → ℝⁿ × ℝⁿ`, which is the
form in which a cut-off local model can be glued into a chart representation by a tubular
parametrisation `H` on `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
noncomputable def euclidModel (n : ℕ) (lam : ℝ)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  fun u => pairToE n (scaledModel n lam β (euclidOfLp n u))

/-- The image of the double point of `β` under the transport and scaling, in the `L²` world. -/
noncomputable def scaledPt (n : ℕ) (lam : ℝ) (a : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  lpOfEuclid n ((1 / lam) • a)

@[simp] theorem scaledModel_apply (n : ℕ) (lam : ℝ)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (x : Fin n → ℝ) :
    scaledModel n lam β x = (1 / lam) • β (lam • x) := rfl

@[simp] theorem euclidModel_apply (n : ℕ) (lam : ℝ)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (u : EuclideanSpace ℝ (Fin n)) :
    euclidModel n lam β u = pairToE n (scaledModel n lam β (euclidOfLp n u)) := rfl

theorem euclidModel_eq_comp (n : ℕ) (lam : ℝ)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) :
    euclidModel n lam β = pairToE n ∘ scaledModel n lam β ∘ euclidOfLp n := rfl

@[simp] theorem scaledPt_eq (n : ℕ) (lam : ℝ) (a : Fin n → ℝ) :
    scaledPt n lam a = (1 / lam) • lpOfEuclid n a := by
  simp [scaledPt]

end Work.Whitney
