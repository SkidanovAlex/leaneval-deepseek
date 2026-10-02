import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate padding `ℝ^{k+8} ↪ ℝ^{k+m}` (`8 ≤ m`) as an isometry, with its adjoint

For `8 ≤ m` the coordinate inclusion `ℝ^{k+8} → ℝ^{k+m}` — the map that keeps the first `k+8`
coordinates and puts `0` in the remaining `m - 8` — is a linear isometry `pad`, and its Hilbert
adjoint `pad†` is the coordinate projection onto the first `k+8` coordinates.  This file builds
that pair explicitly and records the four properties the Pontryagin–Thom chapter needs:

* `pad† ∘ pad = id` (the inclusion is a section of the projection),
* `pad† = proj` and `proj† = pad` (they are mutually adjoint),
* `pad` preserves the norm,
* the coordinate formula `(pad x) (Fin.castLE h j) = x j`.

The construction: the underlying linear map `padLin` is written down coordinate-wise, and the
isometry property is obtained from `LinearMap.isometryOfOrthonormal` by testing it on the standard
orthonormal basis `EuclideanSpace.basisFun` (on which it is just a reindexing by the injective
`Fin.castLE`).  The adjoint is then *defined* to be `pad.adjoint`, so the two adjointness
statements and the section property are instances of `adjoint_adjoint` and
`LinearIsometry.adjoint_comp_self`.
-/

namespace Work.PTGeometric

set_option maxHeartbeats 800000

open scoped BigOperators

/-- **The coordinate inclusion `ℝ^{k+8} → ℝ^{k+m}`**, as a linear map: the first `k + 8`
coordinates are kept, the remaining `m - 8` are put to zero.  (For `m < 8` this is not the
statement one wants, and is not used.) -/
noncomputable def padLin (k m : ℕ) :
    EuclideanSpace ℝ (Fin (k+8)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k+m)) where
  toFun x := WithLp.toLp 2 (fun j => if h : (j : ℕ) < k + 8 then x.ofLp ⟨j, h⟩ else 0)
  map_add' x y := by
    ext j
    by_cases h : (j : ℕ) < k + 8 <;> simp [h]
  map_smul' c x := by
    ext j
    by_cases h : (j : ℕ) < k + 8 <;> simp [h]

/-- Bookkeeping: for `j : Fin (k+m)` whose value is `< k + 8`, the corresponding element of
`Fin (k+8)` agrees with `Fin.castLE` exactly on the *value* condition. -/
lemma fin_castLE_eq {k m : ℕ} {h : k+8 ≤ k+m} {j : Fin (k+m)} {i : Fin (k+8)}
    (hj : (j:ℕ) < k+8) : (⟨(j:ℕ), hj⟩ : Fin (k+8)) = i ↔ j = Fin.castLE h i := by
  constructor
  · intro hij; exact Fin.ext (by rw [Fin.val_castLE]; exact congrArg Fin.val hij)
  · intro hji
    have h2 : (j:ℕ) = (i:ℕ) := by rw [hji, Fin.val_castLE]
    exact Fin.ext (by simpa using h2)

/-- The coordinate inclusion sends the standard basis vector `single i 1` to the standard basis
vector `single (castLE h i) 1`. -/
lemma padLin_single (k m : ℕ) (h : k + 8 ≤ k + m) (i : Fin (k + 8)) :
    padLin k m (EuclideanSpace.single i 1) = EuclideanSpace.single (Fin.castLE h i) 1 := by
  ext j
  simp only [padLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.single_apply]
  by_cases hj : (j : ℕ) < k + 8
  · rw [dif_pos hj]
    by_cases hji : (⟨↑j, hj⟩ : Fin (k+8)) = i
    · rw [if_pos hji, if_pos ((fin_castLE_eq hj).mp hji)]
    · rw [if_neg hji, if_neg (fun hc => hji ((fin_castLE_eq hj).mpr hc))]
  · have hne : ¬ (j = Fin.castLE h i) :=
      fun hji => hj (by rw [hji, Fin.val_castLE]; exact i.isLt)
    rw [dif_neg hj, if_neg hne]

/-- **The coordinate inclusion as a linear isometry.**  It is obtained from
`LinearMap.isometryOfOrthonormal`: on the standard orthonormal basis it is the reindexing by the
injective `Fin.castLE`. -/
noncomputable def padLI (k m : ℕ) (hm : 8 ≤ m) :
    EuclideanSpace ℝ (Fin (k+8)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+m)) := by
  have hle : k + 8 ≤ k + m := by omega
  let v : Module.Basis (Fin (k+8)) ℝ (EuclideanSpace ℝ (Fin (k+8))) :=
    (EuclideanSpace.basisFun (Fin (k+8)) ℝ).toBasis
  have hv1 : ∀ i : Fin (k+8), v i = EuclideanSpace.single i 1 := by
    intro i
    rw [show ⇑v = ⇑(EuclideanSpace.basisFun (Fin (k+8)) ℝ) from OrthonormalBasis.coe_toBasis _]
    exact EuclideanSpace.basisFun_apply _ _ i
  have hv : Orthonormal ℝ ⇑v := by
    rw [show ⇑v = ⇑(EuclideanSpace.basisFun (Fin (k+8)) ℝ) from OrthonormalBasis.coe_toBasis _]
    exact (EuclideanSpace.basisFun _ _).orthonormal
  have hf : Orthonormal ℝ (padLin k m ∘ ⇑v) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Function.comp_apply, hv1, padLin_single k m hle]
    rw [← EuclideanSpace.basisFun_apply (Fin (k+m)) ℝ (Fin.castLE hle i),
        EuclideanSpace.basisFun_inner, PiLp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : ¬ (Fin.castLE hle i = Fin.castLE hle j) :=
        fun hc => hij (Fin.castLE_injective hle hc)
      rw [if_neg hne, if_neg hij]
  exact (padLin k m).isometryOfOrthonormal hv hf

/-- `padLI` is the coordinate inclusion as a function. -/
lemma padLI_apply (k m : ℕ) (hm : 8 ≤ m) (x : EuclideanSpace ℝ (Fin (k+8))) :
    (padLI k m hm) x = padLin k m x := rfl

/-- **The coordinate padding and its adjoint.**  For `8 ≤ m` there are continuous linear maps
`pad : ℝ^{k+8} → ℝ^{k+m}` (the coordinate inclusion) and `proj : ℝ^{k+m} → ℝ^{k+8}` (the
coordinate projection), which are mutually adjoint, compose to the identity, and satisfy the
coordinate formula `(pad x) (Fin.castLE h j) = x j`. -/
theorem exists_padAmb (k m : ℕ) (hm : 8 ≤ m) :
    ∃ (pad : EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (k + m)))
      (proj : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))),
      proj.comp pad = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k + 8))) ∧
      pad.adjoint = proj ∧ proj.adjoint = pad ∧
      (∀ x : EuclideanSpace ℝ (Fin (k + 8)), ‖pad x‖ = ‖x‖) ∧
      (∀ (x : EuclideanSpace ℝ (Fin (k + 8))) (j : Fin (k + 8)),
        (pad x).ofLp (Fin.castLE (by omega) j) = x.ofLp j) := by
  refine ⟨(padLI k m hm).toContinuousLinearMap, (padLI k m hm).toContinuousLinearMap.adjoint,
    ?_, rfl, ?_, ?_, ?_⟩
  · exact LinearIsometry.adjoint_comp_self (padLI k m hm)
  · simp [ContinuousLinearMap.adjoint_adjoint]
  · intro x
    exact (padLI k m hm).norm_map x
  · intro x j
    rw [show ((padLI k m hm).toContinuousLinearMap) x = padLin k m x from padLI_apply k m hm x]
    simp only [padLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [dif_pos (by rw [Fin.val_castLE]; exact j.isLt)]
    simp only [Fin.val_castLE, Fin.eta]

end Work.PTGeometric
