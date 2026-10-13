import Mathlib
import Submission.Work.WilC4aRW.Defs
import Submission.Work.WilC4aRW.LinEquiv.exists_pi_equiv
import Submission.Work.WilC4aRW.LinEquiv.shear_complexIncl
import Submission.Work.WilC4aRW.LinEquiv.reindex_complexIncl

set_option autoImplicit false

noncomputable section

namespace Work.WilC4aRW.LinEquiv

open Work.WilC4aRW

/-! ## A "shear" linear equivalence

For `w : Fin (n+1) → K` and an index `j` with `w j ≠ 0`, the map
`x ↦ x + (x j) • (w - e_j)` (where `e_j = Pi.single j 1`) is a `K`-linear
equivalence -- its matrix is the identity with column `j` replaced by `w`, so its
determinant is `w j` -- and it sends the basis vector `e_j` to `w`.  This is the
elementary coordinate change that moves a non-zero vector to a basis vector. -/
theorem exists_shear_linearEquiv {K : Type*} [Field K] {n : ℕ} (w : Fin (n + 1) → K)
    (j : Fin (n + 1)) (hj : w j ≠ 0) :
    ∃ T : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K),
      (∀ x, T x = x + (x j) • (w - Pi.single j 1)) ∧ T (Pi.single j 1) = w := by
  let e : Fin (n + 1) → K := Pi.single j 1
  have hneg : e - w = -(w - e) := by rw [neg_sub]
  have hcoeff : ∀ (x : Fin (n + 1) → K), (x + (x j) • (w - e)) j = (x j) * (w j) := by
    intro x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e, Pi.single_eq_same]
    ring
  have hcoeff' : ∀ (y : Fin (n + 1) → K),
      (y + ((y j) * (w j)⁻¹) • (e - w)) j = (y j) * (w j)⁻¹ := by
    intro y
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e, Pi.single_eq_same]
    field_simp
    ring
  refine ⟨{ toFun := fun x => x + (x j) • (w - e)
            invFun := fun y => y + ((y j) * (w j)⁻¹) • (e - w)
            left_inv := by
              intro x
              show (x + (x j) • (w - e)) + (((x + (x j) • (w - e)) j) * (w j)⁻¹) • (e - w)
                = x
              rw [hcoeff x, mul_assoc, mul_inv_cancel₀ hj, mul_one, hneg, smul_neg]
              abel
            right_inv := by
              intro y
              show (y + ((y j) * (w j)⁻¹) • (e - w))
                + (((y + ((y j) * (w j)⁻¹) • (e - w)) j)) • (w - e) = y
              rw [hcoeff' y, hneg, smul_neg]
              abel
            map_add' := by
              intro x y
              ext i
              simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
              ring
            map_smul' := by
              intro c x
              ext i
              simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
                RingHom.id_apply]
              ring }, ?_, ?_⟩
  · intro x
    show x + (x j) • (w - e) = x + (x j) • (w - Pi.single j 1)
    simp only [e]
  · show e + (e j) • (w - e) = w
    rw [show e j = 1 from Pi.single_eq_same j 1, one_smul]
    abel

/-! ## Elementary index bookkeeping -/

/-- A non-zero vector of `Fin (n+1) → ℝ` has a non-zero coordinate. -/
lemma exists_coord_ne_zero {n : ℕ} (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) : ∃ j, v j ≠ 0 := by
  by_contra h
  refine hv (funext fun i => ?_)
  simpa using not_not.mp (not_exists.mp h i)

/-- The basic property of the transposition `Fin.last n ↔ j`. -/
lemma swap_last_apply_iff {n : ℕ} (j i : Fin (n + 1)) :
    (Equiv.swap (Fin.last n) j) i = Fin.last n ↔ i = j := by
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-! ## The coordinate change -/

/-- Given a non-zero vector `v` of `ℝ^{n+1}`, there is a real linear automorphism
`L` sending the standard basis vector `e_{n+1} = (0,…,0,1)` to `v`, together with
its complexification: a `ℂ`-linear automorphism `Lc` of `ℂ^{n+1}` which intertwines
the coordinatewise inclusion `ℝ^{n+1} ↪ ℂ^{n+1}` and also sends `e_{n+1}` to `v`. -/
theorem exists_coordinate_change {n : ℕ} (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) :
    ∃ L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ),
      L (Pi.single (Fin.last n) (1 : ℝ)) = v ∧
      ∃ Lc : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ),
        (∀ x : Fin (n + 1) → ℝ,
          Lc (Work.WilC4aRW.cplxIncl x) = Work.WilC4aRW.cplxIncl (L x)) ∧
        Lc (Pi.single (Fin.last n) (1 : ℂ)) = Work.WilC4aRW.cplxIncl v := by
  obtain ⟨j, hj⟩ := exists_coord_ne_zero v hv
  -- the transposition of the last coordinate with a coordinate where `v` is non-zero
  obtain ⟨P, hP⟩ := exists_pi_equiv (K := ℝ) (Equiv.swap (Fin.last n) j)
  obtain ⟨Pc, hPc⟩ := exists_pi_equiv (K := ℂ) (Equiv.swap (Fin.last n) j)
  -- the shears sending `e_j` to `v`, over `ℝ` and over `ℂ`
  obtain ⟨T, hT, hTj⟩ := exists_shear_linearEquiv (K := ℝ) v j hj
  have hjC : (cplxIncl v) j ≠ 0 := by
    show ((v j : ℝ) : ℂ) ≠ 0
    exact_mod_cast hj
  obtain ⟨Tc, hTc, hTcj⟩ := exists_shear_linearEquiv (K := ℂ) (cplxIncl v) j hjC
  have hPe : P (Pi.single (Fin.last n) (1 : ℝ)) = Pi.single j 1 := by
    ext i
    rw [hP]
    by_cases h : i = j
    · rw [h, Equiv.swap_apply_right]
      simp
    · have h' : (Equiv.swap (Fin.last n) j) i ≠ Fin.last n :=
        fun hh => h ((swap_last_apply_iff j i).mp hh)
      rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]
  have hPcE : Pc (Pi.single (Fin.last n) (1 : ℂ)) = Pi.single j 1 := by
    have h1 := reindex_complexIncl (Equiv.swap (Fin.last n) j) P hP Pc hPc
      (Pi.single (Fin.last n) (1 : ℝ))
    rw [cplxIncl_single, hPe, cplxIncl_single] at h1
    simpa using h1
  refine ⟨(P.trans T).toContinuousLinearEquiv, ?_, (Pc.trans Tc).toContinuousLinearEquiv,
    ?_, ?_⟩
  · simp only [LinearEquiv.coe_toContinuousLinearEquiv']
    rw [LinearEquiv.trans_apply, hPe, hTj]
  · intro x
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply]
    rw [reindex_complexIncl (Equiv.swap (Fin.last n) j) P hP Pc hPc x]
    exact shear_complexIncl v j T hT Tc hTc (P x)
  · simp only [LinearEquiv.coe_toContinuousLinearEquiv']
    rw [LinearEquiv.trans_apply, hPcE, hTcj]

end Work.WilC4aRW.LinEquiv
