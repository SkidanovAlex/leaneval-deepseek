import Mathlib
import Submission.Commons.Data.Matrix.upperTriangular_of_det_ne_zero

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

/-- **Straightening a rational flag to the standard flag by a unimodular map.**
Given ℝ-linearly independent integer vectors `v 0, …, v (N-1)` in `ℤ^N`, there is an invertible
`ℝ`-linear map `U` that preserves `ℤ^N` bijectively (unimodular, `|det U| = 1`) and sends the
`i`-dimensional span of `v 0, …, v (i-1)` onto the standard coordinate subspace
`span {e_0, …, e_{i-1}}` for every `i ≤ N`.

Suggested proof: for each `i` the subspace `Lᵢ := span ℝ (v 0, …, v (i-1))` is defined over `ℚ`
(spanned by integer vectors).  A rational subspace `L ⊆ ℝ^N` contains a `ℤ`-basis of the lattice
`L ∩ ℤ^N`; choose `c_0, …, c_{N-1} ∈ ℤ^N` greedily so that `c_0,…,c_{i-1}` is a `ℤ`-basis of
`Lᵢ ∩ ℤ^N` (equivalently, extend a `ℤ`-basis of `Lᵢ ∩ ℤ^N` to `Lᵢ₊₁ ∩ ℤ^N`, possible because
`Lᵢ ⊆ Lᵢ₊₁` are rational).  Then `c` is a `ℤ`-basis of `ℤ^N`, and the map `U` with `U cᵢ = eᵢ`
is unimodular and does the job. -/
theorem exists_unimodular_flag (N : ℕ) (v : Fin N → (Fin N → ℤ))
    (hv : LinearIndependent ℝ (fun i => fun k => (v i k : ℝ))) :
    ∃ U : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ),
      (∀ x : Fin N → ℤ, ∃ y : Fin N → ℤ, U (fun k => (x k : ℝ)) = fun k => (y k : ℝ)) ∧
      (∀ y : Fin N → ℤ, ∃ x : Fin N → ℤ, U (fun k => (x k : ℝ)) = fun k => (y k : ℝ)) ∧
      |LinearMap.det U| = 1 ∧
      (∀ (i : ℕ) (hi : i ≤ N),
        U '' (Submodule.span ℝ (Set.range (fun j : Fin i => fun k => (v (Fin.castLE hi j) k : ℝ))))
          = Submodule.span ℝ (Set.range (fun j : Fin i =>
              (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ)))) := by
  classical
  -- The integer matrix whose columns are the vectors `v c`.
  let A : Matrix (Fin N) (Fin N) ℤ := Matrix.of (fun r c => v c r)
  have hA_apply : ∀ r c, A r c = v c r := fun r c => rfl
  -- Its determinant is nonzero (the columns are ℝ-linearly independent).
  have hAdet : A.det ≠ 0 := by
    have hcol : (A.map (Int.castRingHom ℝ)).col = (fun i : Fin N => fun k => (v i k : ℝ)) := by
      funext i k
      simp [A, Matrix.col]
    have hLI : LinearIndependent ℝ (A.map (Int.castRingHom ℝ)).col := by
      rw [hcol]; exact hv
    have hns : (A.map (Int.castRingHom ℝ)).Nonsingular := Matrix.linearIndependent_col_iff.mp hLI
    have hdetR : (A.map (Int.castRingHom ℝ)).det ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp hns
    have hmap : (A.det : ℝ) = (A.map (Int.castRingHom ℝ)).det :=
      RingHom.map_det (Int.castRingHom ℝ) A
    have hcast : (A.det : ℝ) ≠ 0 := by rw [hmap]; exact hdetR
    exact fun h => hcast (by rw [h]; simp)
  -- Hermite/row reduction: a unimodular integer `U` with `U * A` upper triangular.
  obtain ⟨U, hUunit, hUtri⟩ := Commons.Data.Matrix.upperTriangular_of_det_ne_zero A hAdet
  have hUtri_v : ∀ (i j : Fin N), j < i → (U.mulVec (v j)) i = 0 := by
    intro i j hij
    simpa [A] using hUtri i j hij
  let Uℝ : Matrix (Fin N) (Fin N) ℝ := U.map (Int.castRingHom ℝ)
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' Uℝ
  have hf_apply : ∀ x : Fin N → ℝ, f x = Uℝ.mulVec x := fun x => Matrix.toLin'_apply Uℝ x
  -- An integer inverse for `U`.
  obtain ⟨u, hu⟩ : ∃ u : ℤˣ, (↑u : ℤ) = U.det := hUunit
  let W : Matrix (Fin N) (Fin N) ℤ := (↑u⁻¹ : ℤ) • U.adjugate
  have hUW : U * W = 1 := by
    have hs : (↑u⁻¹ : ℤ) * (↑u : ℤ) = 1 := Units.inv_mul u
    change U * ((↑u⁻¹ : ℤ) • U.adjugate) = 1
    rw [Matrix.mul_smul, Matrix.mul_adjugate, ← hu, smul_smul, hs, one_smul]
  have hUWℝ : Uℝ * (W.map (Int.castRingHom ℝ)) = 1 := by
    have h1 : Uℝ * (W.map (Int.castRingHom ℝ)) = (U * W).map (Int.castRingHom ℝ) := by
      rw [Matrix.map_mul]
    rw [h1, hUW]
    ext i j
    simp [Matrix.one_apply]
  have hdetℝ : Uℝ.det ≠ 0 := by
    have hh : Uℝ.det = (U.det : ℝ) := (RingHom.map_det (Int.castRingHom ℝ) U).symm
    rw [hh, ← hu]
    exact_mod_cast (Units.ne_zero u : (↑u : ℤ) ≠ 0)
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hmv : Uℝ.mulVec x = Uℝ.mulVec y := by
      rw [← hf_apply x, ← hf_apply y]; exact hxy
    exact Matrix.mulVec_injective_of_det_ne_zero hdetℝ hmv
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · -- integrality, forward
    intro x
    refine ⟨U.mulVec x, ?_⟩
    rw [hf_apply]
    funext k
    simpa [Uℝ, Function.comp_def] using (RingHom.map_mulVec (Int.castRingHom ℝ) U x k).symm
  · -- integrality, backward
    intro y
    refine ⟨W.mulVec y, ?_⟩
    rw [hf_apply]
    have h1 : Uℝ.mulVec (fun k => ((W.mulVec y) k : ℝ)) = fun k => ((U.mulVec (W.mulVec y)) k : ℝ) := by
      funext k
      simpa [Uℝ, Function.comp_def] using (RingHom.map_mulVec (Int.castRingHom ℝ) U (W.mulVec y) k).symm
    rw [h1]
    have h2 : U.mulVec (W.mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, hUW, Matrix.one_mulVec]
    rw [h2]
  · -- determinant
    have h1 : LinearMap.det f = (U.det : ℝ) := by
      change LinearMap.det (Matrix.toLin' Uℝ) = (U.det : ℝ)
      rw [LinearMap.det_toLin']
      exact (RingHom.map_det (Int.castRingHom ℝ) U).symm
    rw [h1, ← hu]
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  · -- flag
    have hfv : ∀ j : Fin N, f (fun k => (v j k : ℝ)) = fun k => ((U.mulVec (v j)) k : ℝ) := by
      intro j
      rw [hf_apply]
      funext k
      simpa [Uℝ, Function.comp_def] using (RingHom.map_mulVec (Int.castRingHom ℝ) U (v j) k).symm
    have hzero : ∀ (j k : Fin N), j < k → (U.mulVec (v j)) k = 0 := fun j k hjk => hUtri_v k j hjk
    have hRHS_eq : ∀ (i : ℕ) (hi : i ≤ N),
        Submodule.span ℝ (Set.range (fun j : Fin i =>
            (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ)))
          = Pi.spanSubset ℝ (Set.range (Fin.castLE hi)) := by
      intro i hi
      rw [Pi.spanSubset]
      congr 1
      rw [← Set.range_comp]
      congr 1
      funext j
      exact (Pi.basisFun_apply ℝ (Fin N) (Fin.castLE hi j)).symm
    have hmem : ∀ (i : ℕ) (hi : i ≤ N) (j : Fin i),
        f (fun k => (v (Fin.castLE hi j) k : ℝ)) ∈
          Submodule.span ℝ (Set.range (fun j : Fin i =>
            (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ))) := by
      intro i hi j
      rw [hRHS_eq i hi, Pi.mem_spanSubset_iff]
      intro k hk
      have hkj : (Fin.castLE hi j) < k := by
        have hk' : i ≤ k.val := by
          by_contra hlt
          rw [not_le] at hlt
          exact hk ⟨⟨k.val, hlt⟩, by apply Fin.ext; simp [Fin.castLE]⟩
        refine Fin.lt_def.mpr ?_
        rw [Fin.val_castLE]
        omega
      rw [hfv (Fin.castLE hi j)]
      simp [hzero (Fin.castLE hi j) k hkj]
    intro i hi
    have hle : Submodule.map f (Submodule.span ℝ (Set.range (fun j : Fin i => fun k => (v (Fin.castLE hi j) k : ℝ))))
        ≤ Submodule.span ℝ (Set.range (fun j : Fin i =>
            (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ))) := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro y ⟨x, ⟨j, rfl⟩, rfl⟩
      exact hmem i hi j
    have hfinL : Module.finrank ℝ (Submodule.map f (Submodule.span ℝ (Set.range (fun j : Fin i => fun k => (v (Fin.castLE hi j) k : ℝ))))) = i := by
      rw [Submodule.map_span, ← Set.range_comp]
      rw [finrank_span_eq_card]
      · simp
      · exact (hv.comp (Fin.castLE hi) (Fin.castLE_injective hi)).map' f (LinearMap.ker_eq_bot.mpr hfinj)
    have hfinR : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : Fin i =>
          (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ)))) = i := by
      rw [finrank_span_eq_card]
      · simp
      · exact (Pi.linearIndependent_single_one (Fin N) ℝ).comp (Fin.castLE hi) (Fin.castLE_injective hi)
    have heq : Submodule.map f (Submodule.span ℝ (Set.range (fun j : Fin i => fun k => (v (Fin.castLE hi j) k : ℝ))))
        = Submodule.span ℝ (Set.range (fun j : Fin i =>
            (Pi.single (Fin.castLE hi j) (1:ℝ) : Fin N → ℝ))) :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hfinR, hfinL])
    rw [← Submodule.map_coe f (Submodule.span ℝ (Set.range (fun j : Fin i => fun k => (v (Fin.castLE hi j) k : ℝ))))]
    rw [heq]

end Commons.GeometryOfNumbers.SuccessiveMinima
