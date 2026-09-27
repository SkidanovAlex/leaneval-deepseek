import Mathlib
import Submission.Work.Whitney.LocalModel

/-!
# Auxiliary linear algebra for the transversality of Whitney's local model

This file packages the explicit linear maps appearing in the derivative of Whitney's local
model `model n : ℝⁿ → ℝⁿ × ℝⁿ` (see `Submission/Work/Whitney/LocalModel.lean`) at the two
preimages of the double point, `±e₀`, together with the resulting "two sheets" endomorphism
and the proof that its determinant is nonzero.

Writing `X n = Fin n → ℝ`:

* `sheetE0 n` is the linear map `v ↦ (fun i => if i = 0 then -(1/2) * v 0 else (1/2) * v i)`;
  it is the second component of `fderiv ℝ (model n) (e0 n)`.
* `sheetNegE0 n` is `v ↦ (fun i => if i = 0 then (1/2) * v 0 else -(1/2) * v i)`;
  it is the second component of `fderiv ℝ (model n) (-(e0 n))`.
* `C n` is the "two sheets" endomorphism `(u, v) ↦ (u + v, sheetE0 u + sheetNegE0 v)` of
  `X n × X n`, i.e. the `coprod` of the two derivatives of the model.
* `invC n` is an explicit inverse of `C n`, from which `LinearMap.det (C n) ≠ 0` follows.

The two facts about `fderiv` of the model are proved separately
(`Work.Whitney.model_fderiv_e0`, `Work.Whitney.model_fderiv_neg_e0`).
-/

namespace Work.Whitney

open Set Filter Topology

/-- The second component of the derivative of Whitney's model at `e₀`:
`v ↦ (fun i => if i = 0 then -(1/2) * v 0 else (1/2) * v i)`. -/
noncomputable def sheetE0 (n : ℕ) [NeZero n] : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => (if i = 0 then (-(1/2):ℝ) else (1/2)) • LinearMap.proj i

/-- The second component of the derivative of Whitney's model at `-e₀`:
`v ↦ (fun i => if i = 0 then (1/2) * v 0 else -(1/2) * v i)`. -/
noncomputable def sheetNegE0 (n : ℕ) [NeZero n] : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => (if i = 0 then (1/2:ℝ) else -(1/2)) • LinearMap.proj i

/-- The inverse of `sheetE0 n`: `v ↦ (fun i => if i = 0 then -2 * v 0 else 2 * v i)`. -/
noncomputable def sheetInvE0 (n : ℕ) [NeZero n] : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => (if i = 0 then (-2:ℝ) else 2) • LinearMap.proj i

/-- The "two sheets" endomorphism of Whitney's model at its self-intersection:
`(u, v) ↦ (u + v, sheetE0 u + sheetNegE0 v)`. -/
noncomputable def C (n : ℕ) [NeZero n] :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
    (sheetE0 n ∘ₗ LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) +
      sheetNegE0 n ∘ₗ LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

/-- An explicit inverse of `C n`. -/
noncomputable def invC (n : ℕ) [NeZero n] :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ((1/2:ℝ) • (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) +
      sheetInvE0 n ∘ₗ LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))).prod
    ((1/2:ℝ) • (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) -
      sheetInvE0 n ∘ₗ LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)))

/-- `sheetInvE0 n` is a right inverse of `sheetE0 n`. -/
lemma sheetE0_comp_sheetInvE0 (n : ℕ) [NeZero n] :
    sheetE0 n ∘ₗ sheetInvE0 n = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LinearMap.comp_apply, sheetE0, sheetInvE0, LinearMap.pi_apply,
    LinearMap.smul_apply, LinearMap.proj_apply]
  split_ifs <;> simp

/-- `sheetNegE0 n + sheetE0 n = 0`. -/
lemma sheetNegE0_add_sheetE0 (n : ℕ) [NeZero n] : sheetNegE0 n + sheetE0 n = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Pi.add_apply, LinearMap.add_apply, sheetNegE0, sheetE0,
    LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  split_ifs <;> simp

/-- `sheetNegE0 n ∘ sheetInvE0 n = -1`. -/
lemma sheetNegE0_comp_sheetInvE0 (n : ℕ) [NeZero n] :
    sheetNegE0 n ∘ₗ sheetInvE0 n = -1 := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LinearMap.comp_apply, sheetNegE0, sheetInvE0, LinearMap.pi_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, LinearMap.neg_apply]
  split_ifs <;> simp

/-- The two sheets endomorphism, unfolded. -/
lemma C_apply (n : ℕ) [NeZero n] (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    C n p = (p.1 + p.2, sheetE0 n p.1 + sheetNegE0 n p.2) := by
  simp [C, LinearMap.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply]

/-- The explicit inverse, unfolded. -/
lemma invC_apply (n : ℕ) [NeZero n] (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    invC n p = ((1/2:ℝ) • (p.1 + sheetInvE0 n p.2),
      (1/2:ℝ) • (p.1 - sheetInvE0 n p.2)) := by
  simp [invC, LinearMap.prod_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

/-- `invC n` is a right inverse of `C n`. -/
lemma C_comp_invC (n : ℕ) [NeZero n] : C n ∘ₗ invC n = 1 := by
  apply LinearMap.ext
  intro p
  have hp : (1 : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ]
      ((Fin n → ℝ) × (Fin n → ℝ))) p = p := rfl
  rw [LinearMap.comp_apply, C_apply, invC_apply, hp]
  apply Prod.ext
  · funext i
    simp only [sheetE0, sheetNegE0, sheetInvE0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    split_ifs <;> ring
  · funext i
    simp only [sheetE0, sheetNegE0, sheetInvE0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, Pi.neg_apply]
    split_ifs <;> ring

/-- The two sheets endomorphism of Whitney's model at its self-intersection is invertible:
its determinant is nonzero. -/
theorem det_C_ne_zero (n : ℕ) [NeZero n] : LinearMap.det (C n) ≠ 0 := by
  intro h0
  have h := LinearMap.det_comp (C n) (invC n)
  rw [C_comp_invC] at h
  rw [show (1 : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ]
      ((Fin n → ℝ) × (Fin n → ℝ))) = LinearMap.id from rfl, LinearMap.det_id] at h
  rw [h0, zero_mul] at h
  exact one_ne_zero h

end Work.Whitney
